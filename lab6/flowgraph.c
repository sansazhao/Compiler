#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "errormsg.h"
#include "table.h"

Temp_tempList FG_def(G_node n) {
	AS_instr inst = (AS_instr)G_nodeInfo(n);
	switch(inst->kind) {
		case I_OPER:
			return inst->u.OPER.dst;
		case I_MOVE:
			return inst->u.MOVE.dst;
	}
	return NULL;
}

Temp_tempList FG_use(G_node n) {
	AS_instr inst = (AS_instr)G_nodeInfo(n);
	switch(inst->kind) {
		case I_OPER:
			return inst->u.OPER.src;
		case I_MOVE:
			return inst->u.MOVE.src;
	}
	return NULL;
}

//是否是move指令
bool FG_isMove(G_node n) {
	AS_instr inst = (AS_instr)G_nodeInfo(n);
	return inst->kind == I_MOVE;
}

G_graph FG_AssemFlowGraph(AS_instrList il, F_frame f) {
	G_graph g = G_Graph();
	G_node prev = NULL;

	TAB_table label_table = TAB_empty();
	
	for(AS_instrList l = il; l; l = l->tail){
		AS_instr inst = l->head;
		G_node b = G_Node(g, inst);
		if(prev)
			G_addEdge(prev, b);
		if(inst->kind == I_OPER && 	//may bug?
				!strncmp("jmp", inst->u.OPER.assem, 3))
			prev = NULL;
		else
			prev = b;
		if(inst->kind == I_LABEL)
			TAB_enter(label_table, inst->u.LABEL.label, b);
	}

	//add jumpto labels
	for(G_nodeList nodes = G_nodes(g); nodes; nodes = nodes->tail) {
		AS_instr inst = (AS_instr)G_nodeInfo(nodes->head);
		if(inst->kind == I_OPER && inst->u.OPER.jumps) {
			Temp_labelList jmps = inst->u.OPER.jumps->labels;
			for(; jmps; jmps = jmps->tail) {
				G_node dst = TAB_look(label_table, jmps->head);
				if(dst)
					G_addEdge(nodes->head, dst);
			}
		}
	}

	return g;
}
