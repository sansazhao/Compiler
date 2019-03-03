#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "liveness.h"
#include "color.h"
#include "table.h"

#define K 15

// main operations
static void Build(G_graph ig);
static void MakeWorklist(G_graph ig);
static void Simplify();
static void DecrementDegree(G_node m);
static void EnableMoves(G_nodeList nodes);
static void Coalesce();
static void AddWorkList(G_node u);
static bool OK(G_node t, G_node r);
static bool Conservative(G_node u, G_node v);	//briggs
static void Combine(G_node u, G_node v);
static void Freeze();
static void FreezeMoves(G_node u);
static void SelectSpill();
static void AssignColors(G_graph ig);
static void AddEdge(G_node u, G_node v);

// helper
static Live_moveList NodeMoves(G_node n);
static G_nodeList Adjacent(G_node n);
static G_node GetAlias(G_node n);
static int GetColor(Temp_temp temp);
static bool Precolored(G_node n);
static bool MoveRelated(G_node n);
static bool InMoveList(Live_moveList a, G_node src, G_node dst);
static Live_moveList SubMoveList(Live_moveList a, Live_moveList b);
static Live_moveList UnionMoveList(Live_moveList a, Live_moveList b);
static G_nodeList UnionNodeList(G_nodeList u, G_nodeList v);
static G_nodeList SubNodeList(G_nodeList u, G_nodeList v);
static G_nodeList UnionNode(G_node u, G_nodeList v);

// static variables
static G_table degreeTab;
static G_table colorTab;
static G_table aliasTab;

static G_nodeList simplifyWorklist;
static G_nodeList freezeWorklist;
static G_nodeList spillWorklist;

static G_nodeList spilledNodes;
static G_nodeList coalescedNodes;
static G_nodeList coloredNodes;
static G_nodeList selectStack;
static Live_moveList coalescedMoves;
static Live_moveList constrainedMoves;
static Live_moveList frozenMoves;
static Live_moveList worklistMoves;
static Live_moveList activeMoves;

static char *PrecoloredRegs[17] = {"none", "%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi", "%rbp", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "%rsp"};

struct COL_result COL_color(G_graph ig, Temp_map initial, Temp_tempList regs, Live_moveList moves){
	simplifyWorklist = NULL;	
	freezeWorklist = NULL;
	spillWorklist = NULL;
	spilledNodes = NULL;
	coalescedNodes = NULL;
	coloredNodes = NULL;
	selectStack = NULL;
	coalescedMoves = NULL;
	constrainedMoves = NULL;
	frozenMoves = NULL;
	worklistMoves = moves;
	activeMoves = NULL;

	degreeTab = G_empty();
	colorTab = G_empty();
	aliasTab = G_empty();

	Build(ig);

	MakeWorklist(ig);

	while(simplifyWorklist || worklistMoves || freezeWorklist || spillWorklist){
		if(simplifyWorklist)
			Simplify();
		else if(worklistMoves)
			Coalesce();
		else if(freezeWorklist)
			Freeze();
		else if(spillWorklist)
			SelectSpill();
	}

	AssignColors(ig);
	//coloring 
	Temp_map coloring = Temp_empty();
	for (G_nodeList nodes = G_nodes(ig); nodes; nodes = nodes->tail){
		int c = G_look_int(colorTab, GetAlias(nodes->head));
		Temp_enter(coloring, Live_gtemp(nodes->head), PrecoloredRegs[c]);
	}
	//spill
	Temp_tempList spills = NULL;
    for (; spilledNodes; spilledNodes = spilledNodes->tail) {
        Temp_temp temp = G_nodeInfo(spilledNodes->head);
        spills = Temp_TempList(temp, spills);
    }

	struct COL_result ret;
	ret.coloring = coloring;
	ret.spills = spills;
	return ret;
}

//build conflict graph and tables
static void Build(G_graph ig){
	for (G_nodeList nodes = G_nodes(ig); nodes; nodes = nodes->tail){
		int d = 0;
		for (G_nodeList nl = G_succ(nodes->head); nl; nl = nl->tail)
			d++;
		G_enter_int(degreeTab, nodes->head, d);		//degree

		Temp_temp temp = Live_gtemp(nodes->head);
		int color = GetColor(temp);
		G_enter_int(colorTab, nodes->head, color);	//color

		G_node *alias = checked_malloc(sizeof(G_node));
		*alias = nodes->head;
		G_enter(aliasTab, nodes->head, alias);		//node
	}
}

static void AddEdge(G_node u, G_node v){
	if(!G_inNodeList(u, G_adj(v)) && u != v){
		if(!Precolored(u)){
			(*(int *)G_look(degreeTab, u))++;
			G_addEdge(u, v);		//adjList[u] <- adj(u) U adj(v)
		}
		if(!Precolored(v)){
			(*(int *)G_look(degreeTab, v))++;
			G_addEdge(v, u);		
		}
	}
}

static void MakeWorklist(G_graph g){
	for(G_nodeList nodes = G_nodes(g); nodes; nodes = nodes->tail){
		int degree = G_look_int(degreeTab, nodes->head);
		int color = G_look_int(colorTab, nodes->head);

		if(color != 0)	//is Precolored
			continue;
		if(degree >= K)	//union wait pack
			spillWorklist = UnionNode(nodes->head, spillWorklist);
		else if(MoveRelated(nodes->head))
			freezeWorklist = UnionNode(nodes->head, freezeWorklist);
		else
			simplifyWorklist = UnionNode(nodes->head, simplifyWorklist);
	}
}

static G_nodeList Adjacent(G_node n){
	return SubNodeList(G_succ(n), UnionNodeList(selectStack, coalescedNodes));
}

// n in activemoves U worklistmoves
static Live_moveList NodeMoves(G_node n){
	Live_moveList moves = NULL;
	G_node m = GetAlias(n);
	for(Live_moveList p = UnionMoveList(activeMoves, worklistMoves); p; p = p->tail)
		if(GetAlias(p->src) == m || GetAlias(p->dst) == m)
			moves = Live_MoveList(p->src, p->dst, moves);
	return moves;	
}

static bool MoveRelated(G_node n){
	return (NodeMoves(n) != NULL);
}

static int GetColor(Temp_temp temp){
	Temp_tempList regs = F_regs();
    for(int idx = 0; idx < K+1; idx++, regs = regs->tail){
		if(regs->head == temp)
			return idx+1;
    }
	return 0;
}

static void Simplify(){
	G_node n = simplifyWorklist->head;
	simplifyWorklist = simplifyWorklist->tail;	//sub head
	selectStack = G_NodeList(n, selectStack);	//push n to select
	for(G_nodeList nodes = Adjacent(n); nodes; nodes = nodes->tail)
		DecrementDegree(nodes->head);
}

static void DecrementDegree(G_node m){
	int c = G_look_int(colorTab, m);
	if(c)	//Precolored
		return;

	int d = G_look_int(degreeTab, m);
	G_enter_int(degreeTab, m, --d);

	if(d == K - 1){
		EnableMoves(UnionNode(m, Adjacent(m)));
		spillWorklist = SubNodeList(spillWorklist, G_NodeList(m, NULL));
		if (MoveRelated(m))
			freezeWorklist = UnionNode(m, freezeWorklist);
		else
			simplifyWorklist = UnionNode(m, simplifyWorklist);
	}
}

static void EnableMoves(G_nodeList nodes){
	for(G_node n = nodes->head; nodes; nodes = nodes->tail){
		for(Live_moveList m = NodeMoves(n); m; m = m->tail){
			if(InMoveList(activeMoves, m->src, m->dst)){
				activeMoves = SubMoveList(activeMoves, Live_MoveList(m->src, m->dst, NULL));
				worklistMoves = UnionMoveList(m, worklistMoves);
			}
		}
	}
}

static void Coalesce(){
	G_node u, v;
	G_node x = worklistMoves->src;
	G_node y = worklistMoves->dst;
	Live_moveList m = Live_MoveList(x, y, NULL);

	// guarantee at least one is 0 color.   bind v to u.
	if (Precolored(GetAlias(y))){
		u = GetAlias(y);
		v = GetAlias(x);
	}
	else{
		u = GetAlias(x);
		v = GetAlias(y);
	}
	
	worklistMoves = worklistMoves->tail;
	if(u == v){
		coalescedMoves = UnionMoveList(m, coalescedMoves);
		AddWorkList(u);
	}
	else if(Precolored(v) || G_inNodeList(u, G_adj(v))){
		constrainedMoves = UnionMoveList(m, constrainedMoves);
		AddWorkList(u);
		AddWorkList(v);
	}
	else if(Precolored(u) && (OK(v, u))){
		coalescedMoves = UnionMoveList(m, coalescedMoves);
		Combine(u, v);
		AddWorkList(u);
	}
	else if(!Precolored(u) && Conservative(u, v)){
		coalescedMoves = UnionMoveList(m, coalescedMoves);
		Combine(u, v);
		AddWorkList(u);
	}
	else{
		activeMoves = UnionMoveList(m, activeMoves);
	}
}

static void AddWorkList(G_node u){
	if(!Precolored(u) && !MoveRelated(u) && G_look_int(degreeTab, u) < K){
		freezeWorklist = SubNodeList(freezeWorklist, G_NodeList(u, NULL));
		simplifyWorklist = UnionNode(u, simplifyWorklist);
	}
}

// used when coalesce precolord 
static bool OK(G_node t, G_node r){
	for(G_nodeList p = Adjacent(t); p; p = p->tail){
		if(!(G_look_int(degreeTab, p->head) < K 
		|| Precolored(p->head) || G_inNodeList(p->head, G_adj(r)))){
			return FALSE;
		}
	}
	return TRUE;
}

//can fix arg nodes
static bool Conservative(G_node u, G_node v){
	G_nodeList nodes = UnionNodeList(Adjacent(u), Adjacent(v));
	int k = 0;
	for(; nodes; nodes = nodes->tail){
		G_node n = nodes->head;
		if(G_look_int(degreeTab, n) >= K){
			k++;
		}
	}
	return (k < K);
}

static G_node GetAlias(G_node n){
	if(G_inNodeList(n, coalescedNodes)){
		G_node *a = G_look(aliasTab, n);
		return GetAlias(*a);
	}
	return n;
}

//  v -> u
static void Combine(G_node u, G_node v){
	if (G_inNodeList(v, freezeWorklist))
		freezeWorklist = SubNodeList(freezeWorklist, G_NodeList(v, NULL));
	else
		spillWorklist = SubNodeList(spillWorklist, G_NodeList(v, NULL));
	coalescedNodes = UnionNode(v, coalescedNodes);
	*(G_node *)G_look(aliasTab, v) = u;

	for (G_nodeList t = Adjacent(v); t; t = t->tail){
		AddEdge(t->head, u);
		DecrementDegree(t->head);
	}

	int d = G_look_int(degreeTab, u);
	if (d >= K && G_inNodeList(u, freezeWorklist)){
		freezeWorklist = SubNodeList(freezeWorklist, G_NodeList(u, NULL));
		spillWorklist = UnionNode(u, spillWorklist);
	}
}

static void Freeze(){
	G_node u = freezeWorklist->head;
	freezeWorklist = freezeWorklist->tail;
	simplifyWorklist = UnionNode(u, simplifyWorklist);
	FreezeMoves(u);
}

static void FreezeMoves(G_node u){
	for (Live_moveList m = NodeMoves(u); m; m = m->tail){
		G_node x = m->src;
		G_node y = m->dst;
		G_node v;
		if (GetAlias(y) == GetAlias(u))
			v = GetAlias(x);
		else
			v = GetAlias(y);
		activeMoves = SubMoveList(activeMoves, Live_MoveList(x, y, NULL));
		frozenMoves = UnionMoveList(m, frozenMoves);
		if(NodeMoves(v) == NULL && G_look_int(degreeTab, v) < K){
			freezeWorklist = SubNodeList(freezeWorklist, G_NodeList(v, NULL));
			simplifyWorklist = UnionNode(v, simplifyWorklist);
		}
	}
}

static void SelectSpill(){
	G_node m;
	int max = 0;
	for(G_nodeList p = spillWorklist; p; p = p->tail){
		Temp_temp t = G_nodeInfo(p->head);
		int degree = G_look_int(degreeTab, p->head);
		if(degree > max){	//选择活动范围大的
			max = degree;
			m = p->head;
		}
	}
	spillWorklist = SubNodeList(spillWorklist, G_NodeList(m, NULL));
	simplifyWorklist = UnionNode(m, simplifyWorklist);
	FreezeMoves(m);
}

static void AssignColors(G_graph ig){
	int okColors[K+1];
	while(selectStack){
		G_node n = selectStack->head;		// n = pop(stack)
		selectStack = selectStack->tail;
		for(int i = 1; i < K + 1; i++){
			okColors[i] = 1;		//rsp can't be used
		}

		for(G_nodeList adjs = G_succ(n); adjs; adjs = adjs->tail){
			G_node w = GetAlias(adjs->head);	//succ的颜色都标0
		 	int c = G_look_int(colorTab, w);
			okColors[c] = 0;	//color is used
		}
		
		int i;
		bool spill = TRUE;
		for(i = 1; i < K + 1; i++){
			if(okColors[i]){
				spill = FALSE;	//该点分配为i
				break;
			}
		}
		if(spill){		//okcolor == {}
			printf("assign spill %d\n",i);
			spilledNodes = UnionNode(n, spilledNodes);
		}
		else{	
			coloredNodes = UnionNode(n, coloredNodes);
			G_enter_int(colorTab, n, i);
		}
	}

	// color coalesced nodes: color[n] <= color[GetAlias(n)]
	for (G_nodeList n = coalescedNodes; n; n = n->tail){
		G_enter_int(colorTab, n->head, G_look_int(colorTab, GetAlias(n->head)));
	}
}

static bool Precolored(G_node n){
	return G_look_int(colorTab, n);
}

static G_nodeList UnionNode(G_node u, G_nodeList v){
	G_nodeList res = G_NodeList(u, NULL);
	return UnionNodeList(res, v);
}

static G_nodeList SubNodeList(G_nodeList u, G_nodeList v){
	G_nodeList res = NULL;
	for (G_nodeList nodes = u; nodes; nodes = nodes->tail)
		if (!G_inNodeList(nodes->head, v))
			res = G_NodeList(nodes->head, res);
	return res;
}

static G_nodeList UnionNodeList(G_nodeList u, G_nodeList v){
	G_nodeList res = u;
	for (G_nodeList nodes = v; nodes; nodes = nodes->tail)
		if (!G_inNodeList(nodes->head, u))
			res = G_NodeList(nodes->head, res);
	return res;
}

static Live_moveList UnionMoveList(Live_moveList a, Live_moveList b){
	Live_moveList l = a;
	for(Live_moveList p = b; p; p = p->tail)
		if(!InMoveList(a, p->src, p->dst))
			l = Live_MoveList(p->src, p->dst, l);
	return l;
}

static Live_moveList SubMoveList(Live_moveList a, Live_moveList b){
	Live_moveList l = NULL;
	for(Live_moveList p = a; p; p = p->tail)
		if(!InMoveList(b, p->src, p->dst))
			l = Live_MoveList(p->src, p->dst, l);
	return l;
}

static bool InMoveList(Live_moveList l, G_node src, G_node dst){
	for(; l; l = l->tail)
		if(l->src == src && l->dst == dst)
			return TRUE;
	return FALSE;
}
