#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "tree.h"
#include "frame.h"

/*Lab5: Your implementation here.*/

//varibales
struct F_access_ {
	enum {inFrame, inReg} kind;
	union {
		int offset; //inFrame
		Temp_temp reg; //inReg
	} u;
};

struct F_frame_{
	Temp_label name;
	F_accessList formals;	//static link 
	F_accessList locals;
	int offset;

};

const int wordSize = 8;

static F_access InFrame(int offset){
	F_access access = checked_malloc(sizeof(struct F_access_));
	access->kind = inFrame;
	access->u.offset = offset;
	return access;
}

static F_access InReg(Temp_temp reg){
	F_access access = checked_malloc(sizeof(struct F_access_));
	access->kind = inReg;
	access->u.reg = reg;
	return access;
}

F_frag F_StringFrag(Temp_label label, string str) {
	F_frag frag = checked_malloc(sizeof(*frag)); 
	frag->kind = F_stringFrag;
	frag->u.stringg.label = label;
	frag->u.stringg.str = str;
	return frag;                                      
}                                                     
                                                      
F_frag F_ProcFrag(T_stm body, F_frame frame) {  
	F_frag frag = checked_malloc(sizeof(*frag)); 
	frag->kind = F_procFrag;
	frag->u.proc.body = body;
	frag->u.proc.frame = frame;      
	return frag;                                      
}                                                     

//片段：栈帧和函数体     
F_fragList F_FragList(F_frag head, F_fragList tail) {
	F_fragList fragList = checked_malloc(sizeof(*fragList)); 
	fragList->head = head;
	fragList->tail = tail;
	return fragList;                                      
}                                                     

F_frame F_newFrame(Temp_label name, U_boolList formals){
	F_frame  f = checked_malloc(sizeof(*f));
	f->name = name;
	f->locals = NULL;
	f->offset = 0;
	F_accessList head = malloc(sizeof(struct F_accessList_)); 
    F_accessList tail = head;	
	int offset = 8;
	while(formals){//head f8 f12 f16 ...
		if (formals->head != TRUE) {
            printf("Frame: formal parameter should be passed in stack.\n");
        }
		tail->tail = F_AccessList(InFrame(offset), NULL);
		offset += wordSize;
		tail = tail->tail;
		formals = formals->tail;
	}
	f->formals = head->tail;
	return f;	
}

F_access F_allocLocal(F_frame f, bool escape){
	F_access access;
	if(escape){//frame
		access = InFrame(f->offset);
		f->offset += wordSize;
	}
	else{//reg
		access = InReg(Temp_newtemp());
	}
	return access;
}

Temp_label F_name(F_frame f){
	return f->name;
}

F_accessList F_formals(F_frame f){
	return f->formals;
}

F_accessList F_AccessList(F_access head, F_accessList tail){
	F_accessList accessList = malloc(sizeof(*accessList)); 
	accessList->head = head;
	accessList->tail = tail;
	return accessList; 
}


Temp_temp F_FP(void){
	return Temp_newtemp();
}

Temp_temp F_RV(void){//rax
	return Temp_newtemp();
}

T_exp F_Exp(F_access acc, T_exp framePtr){
	switch(acc->kind){
		case inFrame:
			return T_Mem(T_Binop(T_plus, T_Const(acc->u.offset), framePtr));
		case inReg:
			return T_Temp(acc->u.reg);
		default:
			assert(0);
	}
}

T_stm F_procEntryExitl(F_frame frame, T_stm stm){
	return stm;
}

T_exp F_externalCall(string s, T_expList args){
	return T_Call(T_Name(Temp_namedlabel(s)), args);
}