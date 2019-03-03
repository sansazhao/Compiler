#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "liveness.h"
#include "table.h"

/* 用一个数据结构来记住每一个节点有哪些出口活跃的临时变量有所帮助
* 已知一个流图结点n, 在此结点活跃的临时变掀集合可通过查看全局表liveMap 得知。
*/

static bool inTempList(Temp_tempList a, Temp_temp t);

static void enterTab(G_table t, G_node flowNode, Temp_tempList temps){
	*(Temp_tempList*)G_look(t, flowNode) = temps;
}

static Temp_tempList lookTab(G_table t, G_node flownode){
	return *(Temp_tempList *)G_look(t, flownode);
}

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail) {
	Live_moveList lm = (Live_moveList) checked_malloc(sizeof(*lm));
	lm->src = src;
	lm->dst = dst;
	lm->tail = tail;
	return lm;
}

//指出n表示的临时变量，让节点的info域指向temp
Temp_temp Live_gtemp(G_node n) {
	return (Temp_temp)G_nodeInfo(n);
}

static Temp_tempList unionTempList(Temp_tempList a, Temp_tempList b) {
	Temp_tempList res = a;
	for (; b; b = b->tail) {
		if (!inTempList(a, b->head)) {
			res = Temp_TempList(b->head, res);
		}
	}
	return res;
}

static Temp_tempList subTempList(Temp_tempList a, Temp_tempList b) {
	Temp_tempList res = NULL;
	for (; a; a = a->tail) {
		if (!inTempList(b, a->head)) {
			res = Temp_TempList(a->head, res);
		}
	}
	return res;
}

static bool isEqual(Temp_tempList a, Temp_tempList b) {
	Temp_tempList p = a;
	for (; p; p = p->tail) 
		if (!inTempList(b, p->head))
			return FALSE;
	p = b;
	for (; p; p = p->tail) 
		if (!inTempList(a, p->head)) 
			return FALSE;
	return TRUE;
}

static bool inTempList(Temp_tempList a, Temp_temp t) {
	for (; a; a = a->tail)
		if (a->head == t) 
			return TRUE;
	return FALSE;
}

static bool inMoveList(Live_moveList a, G_node src, G_node dst) {
	for (; a; a = a->tail) 
		if (a->src == src && a->dst == dst) 
			return TRUE;
	return FALSE;
}

static G_node tempToNode(TAB_table tab, Temp_temp t, G_graph g){
	G_node n = TAB_look(tab, t);
	if (!n){
		n = G_Node(g, t);
		TAB_enter(tab, t, n);
	}
	return n;
}

//conflict graph
struct Live_graph Live_liveness(G_graph flow) {
	struct Live_graph lg;
	lg.graph = G_Graph();
	lg.moves = NULL;

	G_table inTab = G_empty();
	G_table outTab = G_empty();
	
	for (G_nodeList nodes = G_nodes(flow); nodes; nodes = nodes->tail) {
		G_enter(inTab, nodes->head, checked_malloc(sizeof(Temp_tempList)));
		G_enter(outTab, nodes->head, checked_malloc(sizeof(Temp_tempList)));
	}

	//liveness analysis
	bool end = FALSE;
	while(!end){	
		end = TRUE;
		G_node n;
		for(G_nodeList nodes = G_nodes(flow); nodes; nodes = nodes->tail) {
			n = nodes->head;
			Temp_tempList in_old = lookTab(inTab, n);
			Temp_tempList out_old = lookTab(outTab, n);
 
			Temp_tempList in = NULL, out = NULL;
			// out[n] <- union in[succ[n]]
			for(G_nodeList succs = G_succ(n); succs; succs = succs->tail) {
				Temp_tempList in_succ = lookTab(inTab, succs->head);
				out = unionTempList(out, in_succ);
			}
			// in[n] <- use[n] U (out[n] - def[n]) */
			in = unionTempList(FG_use(n), subTempList(out, FG_def(n)));
			
			if(!isEqual(in_old, in) || !isEqual(out_old, out)) {
				end = FALSE;
			}
			enterTab(inTab, n, in);
            enterTab(outTab, n, out);
		}
	}
	TAB_table temp_to_node = TAB_empty();

	// add precolored registers
	for (Temp_tempList temps = F_regs(); temps; temps = temps->tail) {
		G_node tempNode = G_Node(lg.graph, temps->head);
		TAB_enter(temp_to_node, temps->head, tempNode);
	}
	for (Temp_tempList temps = F_regs(); temps; temps = temps->tail) {
		for (Temp_tempList next = temps->tail; next; next = next->tail) {
			G_node a = TAB_look(temp_to_node, temps->head);
			G_node b = TAB_look(temp_to_node, next->head);
			G_addEdge(a, b);
			G_addEdge(b, a);
		}
	}

	// add conflict edge
	for (G_nodeList nodes = G_nodes(flow); nodes; nodes = nodes->tail) {
		G_node n = nodes->head;
		for (Temp_tempList def = FG_def(n); def; def = def->tail) {	
			G_node a = tempToNode(temp_to_node, def->head, lg.graph);
			for(Temp_tempList out = lookTab(outTab, n); out; out = out->tail) {
				if(out->head == def->head) 
					continue;
				G_node b = tempToNode(temp_to_node, out->head, lg.graph);
				if(!G_inNodeList(a, G_adj(b)) && (!FG_isMove(n) || !inTempList(FG_use(n), out->head))) {
					G_addEdge(a, b);
					G_addEdge(b, a);
				}
			}
			// add movelist
			if (!FG_isMove(n))
				continue;
			for (Temp_tempList out = FG_use(n); out; out = out->tail) {
				if (out->head == F_FP() || out->head == def->head)
					continue;
				G_node b = tempToNode(temp_to_node, out->head, lg.graph);
				if (!inMoveList(lg.moves, b, a)) {
					lg.moves = Live_MoveList(b, a, lg.moves);
				}
			}
		}
	}
	return lg;
}