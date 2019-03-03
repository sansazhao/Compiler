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
#define L Temp_TempList

static const int wordSize = 8;	//64bit

/* function implementation */
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

F_accessList F_AccessList(F_access head, F_accessList tail) {
	F_accessList l = checked_malloc(sizeof(*l));
	l->head = head;
	l->tail = tail;
	return l;
}

F_frame F_newFrame(Temp_label name, U_boolList formals) {
	F_frame f = checked_malloc(sizeof(*f));
	f->label = name;		
	f->local = 0;

	F_accessList head = NULL, tail = NULL;
	int reg_cnt = 0, spill = 0;

	for (U_boolList p = formals; p; p = p->tail) {
		F_access acc = NULL;
		if(p->head && reg_cnt < 6){// head->current, bool escape
			printf("f: %dth, local: %d \n", reg_cnt, f->local + 1);
			f->local++;
			acc = InFrame(-(f->local)*wordSize);
			reg_cnt++;
		}
		else if(!p->head){
			printf("reg: %dth \n", reg_cnt);
			acc = InReg(Temp_newtemp());
		}	 
		else
			acc = InFrame((spill++)*wordSize);

		if(head){
			tail->tail = F_AccessList(acc, NULL);
			tail = tail->tail;
		} 
		else{
			head = F_AccessList(acc, NULL);
			tail = head;
		}
	}
	printf("END: %s \n\n", Temp_labelstring(name));
	f->formals = head;

	return f;
}

Temp_label F_name(F_frame f) {
	return f->label;
}

F_accessList F_formals(F_frame f) {
	return f->formals;
}

F_access F_allocLocal(F_frame f, bool escape) {
	if(escape){ //escape -> frame
		f->local++;
		return InFrame(-(f->local)*wordSize);
	}
	else //reg
		return InReg(Temp_newtemp());
}

T_exp F_Exp(F_access acc, T_exp fp) {
	if (acc->kind == inReg)
		return T_Temp(acc->u.reg);
	else
		return T_Mem(T_Binop(T_plus, T_Const(acc->u.offset), fp));
}

T_exp F_externalCall(string s, T_expList args) {
	return T_Call(T_Name(Temp_namedlabel(s)), args);
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

F_fragList F_FragList(F_frag head, F_fragList tail) {
	F_fragList fl = checked_malloc(sizeof(*fl));
	fl->head = head;
	fl->tail = tail;
	return fl;
}                                             

//liveness analysis
AS_instrList F_procEntryExit2(AS_instrList body){
	static Temp_tempList returnSink = NULL;
	if (!returnSink)  
		returnSink = L(F_RSP(), F_callee_save());
    return AS_splice(body, 
			AS_InstrList(AS_Oper("ret", NULL, returnSink, NULL), NULL));
}

AS_proc F_procEntryExit3(F_frame f, AS_instrList il){
  	int fs = f->local*8;
	AS_proc proc = checked_malloc(sizeof(*proc));
  	char *prolog = checked_malloc(100 * sizeof(char));
	sprintf(prolog, "subq $%d, %%rsp\n", fs);
  	proc->prolog = prolog;

  	char *epilog = checked_malloc(100 * sizeof(char));
	sprintf(epilog, "addq $%d, %%rsp\nret\n", fs);
 	proc->epilog = epilog;

  	proc->body = il;
}

#define newtemp {static Temp_temp t = NULL;if (!t)t = Temp_newtemp();return t;}
Temp_temp F_FP() newtemp

Temp_temp F_RAX() newtemp
Temp_temp F_RBX() newtemp
Temp_temp F_RCX() newtemp
Temp_temp F_RDX() newtemp
Temp_temp F_RSI() newtemp
Temp_temp F_RDI() newtemp
Temp_temp F_RBP() newtemp
Temp_temp F_RSP() newtemp
Temp_temp F_R8() newtemp
Temp_temp F_R9() newtemp
Temp_temp F_R10() newtemp
Temp_temp F_R11() newtemp
Temp_temp F_R12() newtemp
Temp_temp F_R13() newtemp
Temp_temp F_R14() newtemp
Temp_temp F_R15() newtemp

Temp_tempList F_regs(){
	return L(F_RAX(), L(F_RBX(), L(F_RCX(), L(F_RDX(), L(F_RSI(), L(F_RDI(), L(F_RBP(),  
	 		L(F_R8(), L(F_R9(), L(F_R10(), L(F_R11(), L(F_R12(), L(F_R13(), L(F_R14(), L(F_R15(), 
			L(F_RSP(), NULL))))))))))))))));	
}

Temp_tempList F_argregs(){
	return L(F_RDI(), L(F_RSI(), L(F_RDX(), 
			L(F_RCX(), L(F_R8(), L(F_R9(), NULL))))));
}

Temp_tempList F_caller_save(){
	return L(F_RAX(), L(F_R10(), L(F_R11(), F_argregs())));
}

Temp_tempList F_callee_save(){
	return L(F_RBX(), L(F_RBP(), L(F_R12(), 
			L(F_R13(), L(F_R14(), L(F_R15(), NULL))))));
}

void F_initTempMap(){
	F_tempMap = Temp_empty();
	Temp_enter(F_tempMap, F_RAX(), "%rax");
	Temp_enter(F_tempMap, F_RSP(), "%rsp");
	Temp_enter(F_tempMap, F_RDI(), "%rdi");
	Temp_enter(F_tempMap, F_RSI(), "%rsi");
	Temp_enter(F_tempMap, F_RDX(), "%rdx");
	Temp_enter(F_tempMap, F_RCX(), "%rcx");
	Temp_enter(F_tempMap, F_R8(), "%r8");
	Temp_enter(F_tempMap, F_R9(), "%r9");
	Temp_enter(F_tempMap, F_R10(), "%r10");
	Temp_enter(F_tempMap, F_R11(), "%r11");
	Temp_enter(F_tempMap, F_RBX(), "%rbx");
	Temp_enter(F_tempMap, F_RBP(), "%rbp");
	Temp_enter(F_tempMap, F_R12(), "%r12");
	Temp_enter(F_tempMap, F_R13(), "%r13");
	Temp_enter(F_tempMap, F_R14(), "%r14");
	Temp_enter(F_tempMap, F_R15(), "%r15");
}