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
#include "regalloc.h"
#include "table.h"
#include "flowgraph.h"
#include <string.h>


#define MAXLINE 100

static char* fp_inst[1000];
static int num;
static int offset[1000];
static const int wordSize = 8;

static bool hasTemp(Temp_tempList list, Temp_temp temp){
    for(; list; list = list->tail)
        if(list->head == temp)
            return 1;
    return 0;
}

static void replaceTemp(Temp_tempList list, Temp_temp old, Temp_temp now){
    for(; list; list = list->tail)
        if(list->head == old)
            list->head = now;
}

AS_instrList RewriteProgram(F_frame f, AS_instrList il, Temp_tempList spills) {
    AS_instrList result = il;
    for (; spills; spills = spills->tail){
        Temp_temp spill = spills->head;
        f->local++;

        AS_instrList instrs = result;
        for (; instrs; instrs = instrs->tail){
            AS_instr cur = instrs->head;
			//save the spills
            if(cur->kind == I_OPER || cur->kind == I_MOVE){
                if(hasTemp(cur->u.OPER.dst, spill)){ 	//dst should spill 
                    Temp_temp r = Temp_newtemp();
                    replaceTemp(cur->u.OPER.dst, spill, r); 

                    char *inst = checked_malloc(MAXLINE*(sizeof(char)));
					fp_inst[num] = inst;
					offset[num++] = f->local * wordSize;
					sprintf(inst, "movq `s0, %s(%%rsp)", Temp_labelstring(f->label));
					AS_instr store = AS_Oper(inst, NULL, Temp_TempList(r, NULL), NULL);
                    instrs->tail = AS_InstrList(store, instrs->tail);
                } 
				else if(hasTemp(cur->u.OPER.src, spill)){	//src should spill
                    Temp_temp r = Temp_newtemp();
                    replaceTemp(cur->u.OPER.src, spill, r);  

                    char *inst = checked_malloc(MAXLINE*(sizeof(char)));
					fp_inst[num] = inst;
					offset[num++] = - f->local * wordSize;
					sprintf(inst, "movq %s(%%rsp), `d0", Temp_labelstring(f->label));
					AS_instr load = AS_Oper(inst, Temp_TempList(r, NULL), NULL, NULL);
                    instrs->head = load;
                    instrs->tail = AS_InstrList(cur, instrs->tail);
                }
            }
        }
    }
    return result;
}

struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
	G_graph flowGraph;
	struct Live_graph liveGraph;
	struct COL_result color;
	num = 0;
	while(1){
		flowGraph = FG_AssemFlowGraph(il, f);
		liveGraph = Live_liveness(flowGraph);
		color = COL_color(liveGraph.graph, F_tempMap, NULL, liveGraph.moves);		
		if(color.spills == NULL)
			break;
		il = RewriteProgram(f, il, color.spills);
	}

	int fs = f->local * wordSize;
	for(int i = 0; i < num; i++){	//sp + fs - k
		if(offset[i] > 0)
			sprintf(fp_inst[i], "movq `s0, %d(%%rsp)", fs - offset[i]);
		else
			sprintf(fp_inst[i], "movq %d(%%rsp), `d0", fs + offset[i]);
	}

	struct RA_result ret;
	ret.coloring = color.coloring;
	ret.il = il;
	return ret;
}
