#include <stdio.h>
#include "util.h"
#include "table.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "printtree.h"
#include "frame.h"
#include "translate.h"

const int wordSize = 8;
static Tr_level outer = NULL;

//LAB5: you can modify anything you want.

struct Tr_access_ {
	Tr_level level;
	F_access access;
};

typedef struct patchList_ *patchList;
struct patchList_ {
	Temp_label *head; 
	patchList tail;
};

struct Cx {
	patchList trues; 
	patchList falses; 
	T_stm stm;
};

struct Tr_exp_ {
	enum {Tr_ex, Tr_nx, Tr_cx} kind;
	union {T_exp ex; T_stm nx; struct Cx cx; } u;
};

struct Tr_level_ {
	F_frame frame;
	Tr_level parent;
};

static Tr_access Tr_Access(Tr_level level, F_access access);
static Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail);
static Tr_accessList makeFormalList(Tr_level l);  

static patchList PatchList(Temp_label *head, patchList tail);
static patchList doPatch(patchList tList, Temp_label label);
static patchList joinPatch(patchList first, patchList second);

static Tr_exp Tr_Ex(T_exp ex);
static Tr_exp Tr_Nx(T_stm nx);
static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm);

static T_exp unEx(Tr_exp e);
static T_stm unNx(Tr_exp e);
static struct Cx unCx(Tr_exp e);

static T_exp staticLink(Tr_level l, Tr_level g);	//trace static link from l to g


Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail) {
	Tr_expList l = checked_malloc(sizeof(*l));
	l->head = head;
	l->tail = tail;
	return l;
}

Tr_level Tr_outermost(void) {
	if (!outer)
		outer = Tr_newLevel(NULL, Temp_newlabel(), NULL);
	return outer;
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals) {
	Tr_level l = checked_malloc(sizeof(*l));
	l->parent = parent;
	l->frame = F_newFrame(name, U_BoolList(TRUE, formals));	//true-static link
	return l;
}


static Tr_accessList makeTrAccessList(F_accessList list, Tr_level l){
	if(!list)
		return NULL;
	Tr_access access = Tr_Access(l, list->head);
	return Tr_AccessList(access, makeTrAccessList(list->tail, l));
}

Tr_accessList Tr_formals(Tr_level level) {
	return makeTrAccessList(F_formals(level->frame), level);
}

Tr_access Tr_allocLocal(Tr_level level, bool escape) {
	return Tr_Access(level, F_allocLocal(level->frame, escape));
}

static F_fragList fragList;
static F_fragList frag_tail;

F_fragList Tr_getResult() {
	return fragList->tail;
}

static void Tr_addFrag(F_frag frag){
	frag_tail->tail = F_FragList(frag, NULL);
	frag_tail = frag_tail->tail;
}

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals) {
	F_frag frag = F_ProcFrag(T_Move(T_Temp(F_RAX()), unEx(body)), level->frame);
	Tr_addFrag(frag);
}

Tr_exp Tr_null() {
	return Tr_Ex(T_Const(0));
}

//Tr exp
Tr_exp Tr_simpleVar(Tr_access acc, Tr_level l){
	T_exp t_exp = F_Exp(acc->access, staticLink(l, acc->level));
    return Tr_Ex(t_exp);
}

Tr_exp Tr_fieldVar(Tr_exp ptr, int index){
	return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(ptr), T_Const(wordSize*index))));
}

//array
Tr_exp Tr_subscriptVar(Tr_exp base, Tr_exp index) {
	assert(base && index);
	return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(base), T_Binop(
						T_mul, unEx(index), T_Const(wordSize)))));
}

Tr_exp Tr_intExp(int val) {
	printf("i : %d\n",val);
	return Tr_Ex(T_Const(val));
}

Tr_exp Tr_stringExp(string str){
	printf("s : %s\n", str);
	Temp_label label = Temp_newlabel();
	F_frag frag = F_StringFrag(label, str);
	Tr_addFrag(frag);
	return Tr_Ex(T_Name(label));
}

static T_expList unExpList(Tr_expList tr){
    if (tr == NULL)
        return NULL;
    return T_ExpList(tr->head->u.ex, unExpList(tr->tail));
}

Tr_exp Tr_callExp(Temp_label fun, Tr_expList args, Tr_level caller, Tr_level callee){
	T_expList t_args = unExpList(args);
	if(!caller->parent){
		return Tr_Ex(F_externalCall(Temp_labelstring(fun), t_args));
	}	
	t_args = T_ExpList(staticLink(callee, caller->parent), t_args);
	return Tr_Ex(T_Call(T_Name(fun), t_args));
}

Tr_exp Tr_arithExp(A_oper oper, Tr_exp left, Tr_exp right) {
	T_binOp op;
	switch (oper) {
		case A_plusOp:		
			op = T_plus; break;
		case A_minusOp:		
			op = T_minus; break;
		case A_timesOp:		
			op = T_mul;	break;
		case A_divideOp:	
			op = T_div; break;
		default:	
			assert(0);
	}
	return Tr_Ex(T_Binop(op, unEx(left), unEx(right)));	
}

Tr_exp Tr_relExp(A_oper oper, Tr_exp left, Tr_exp right) {
	T_relOp op;
	switch (oper) {
		case A_eqOp:	
			op = T_eq;	break;
		case A_neqOp:	
			op = T_ne;	break;
		case A_ltOp:	
			op = T_lt;	break;
		case A_leOp:	
			op = T_le;	break;
		case A_gtOp:	
			op = T_gt;	break;
		case A_geOp:	
			op = T_ge;	break;
		default:	
			assert(0);
	}
	T_stm stm = T_Cjump(op, unEx(left), unEx(right), NULL, NULL);
	patchList trues = PatchList(&stm->u.CJUMP.true, NULL);
	patchList falses = PatchList(&stm->u.CJUMP.false, NULL);
	return Tr_Cx(trues, falses, stm);
}

Tr_exp Tr_stringCompareExp(A_oper oper, Tr_exp left, Tr_exp right) {
	T_exp ans = F_externalCall(String("stringEqual"), 
								T_ExpList(unEx(left), T_ExpList(unEx(right), NULL)));
	if (oper == A_eqOp)
		return Tr_Ex(ans);
	else	//not equal
		return Tr_Ex(T_Binop(T_minus, T_Const(1), ans));	
}

Tr_exp Tr_funcDec(Tr_exp body, Tr_level lv) {
	return Tr_Nx(T_Move(T_Temp(F_RAX()), unEx(body)));
}

Tr_exp Tr_arrayExp(Tr_exp size, Tr_exp init) {
	return Tr_Ex(F_externalCall(String("initArray"), 
								 T_ExpList(unEx(size), 
								 T_ExpList(unEx(init), NULL))));
}

Tr_exp Tr_recordExp(Tr_expList l) {
	int n = 0;
	Tr_expList it = l;
	while(it){
		n++;
		it = it->tail;
	}
	Temp_temp r = Temp_newtemp();
	T_stm alloc = T_Move(T_Temp(r), F_externalCall(String("malloc"), T_ExpList(T_Const(n*wordSize), NULL)));
	int i = n - 1;
	T_stm seq = T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Const(i-- * wordSize))),  unEx(l->head));

	for (l = l->tail; l; l = l->tail, i--) {
		seq = T_Seq(T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Const(i*wordSize))),  unEx(l->head)), seq); 
	}
	return Tr_Ex(T_Eseq(T_Seq(alloc, seq), T_Temp(r)));
}

// ESEQ
Tr_exp Tr_seqExp(Tr_expList l) {
	T_exp seq = unEx(l->head);
	Tr_expList el;
	for(el = l->tail; el; el = el->tail) 
		seq = T_Eseq(unNx(el->head), seq);
	return Tr_Ex(seq);
}

Tr_exp Tr_ifExp(Tr_exp test, Tr_exp then, Tr_exp elsee) {
	struct Cx cx = unCx(test);
	Temp_label t = Temp_newlabel();//if == true then
	Temp_label f = Temp_newlabel();//if == false
	doPatch(cx.trues, t);
	doPatch(cx.falses, f);
	if(!elsee){//if - then:  cx -> label t -> then -> label f 
		T_stm then_stm = T_Seq(T_Label(t), unNx(then));
		T_stm seq = T_Seq(cx.stm, T_Seq(then_stm, T_Label(f)));	
		return Tr_Nx(seq);
	}
	else{//if then else
		Temp_temp r = Temp_newtemp();
		Temp_label joinLabel = Temp_newlabel();
		T_exp joinJump = T_Eseq(T_Label(joinLabel), T_Temp(r));//汇合点
		if (then->kind == Tr_nx || elsee->kind == Tr_nx) { 
			return Tr_Nx(T_Seq(cx.stm,
						  T_Seq(T_Label(t),
						   T_Seq(unNx(then),
						    T_Seq(T_Jump(T_Name(joinLabel), Temp_LabelList(joinLabel, NULL)),
							 T_Seq(T_Label(f),
							  T_Seq(unNx(elsee),
									T_Label(joinLabel))))))));
		} 
		//then: label t -> move then to result -> jmp join 
		T_stm then_stm = T_Seq(T_Move(T_Temp(r), unEx(then)),
                           T_Jump(T_Name(joinLabel), Temp_LabelList(joinLabel, NULL)));
    	then_stm = T_Seq(T_Label(t), then_stm);	

		//else: label f -> move else to result -> jmp join
		T_stm else_stm = T_Seq(T_Move(T_Temp(r), unEx(elsee)),
                           T_Jump(T_Name(joinLabel), Temp_LabelList(joinLabel, NULL)));
		else_stm = T_Seq(T_Label(f), else_stm);
		T_exp ex = T_Eseq(T_Seq(cx.stm, T_Seq(then_stm, else_stm)), joinJump);
		return Tr_Ex(ex);
	}
}

//lab6 -- fix bug: donelabel.name = null 
Tr_exp Tr_whileExp(Tr_exp test, Tr_exp body, Temp_label done) {
	struct Cx cx = unCx(test);
	Temp_label testLabel = Temp_newlabel();
	Temp_label bodyLabel = Temp_newlabel();
	doPatch(cx.trues, bodyLabel);
	doPatch(cx.falses, done);
	T_stm stm = T_Seq(T_Label(testLabel),
				T_Seq(cx.stm,		//true body;false done
				T_Seq(T_Label(bodyLabel),
				T_Seq(unNx(body),
				T_Seq(T_Jump(T_Name(testLabel), Temp_LabelList(testLabel, NULL)),
					  T_Label(done))))));
	return Tr_Nx(stm);
}

Tr_exp Tr_forExp(Tr_level l, Tr_access loop, Tr_exp lo, Tr_exp hi, Tr_exp body, Temp_label done) {
	T_exp i = F_Exp(loop->access, T_Temp(F_FP()));
	T_exp limit = T_Temp(Temp_newtemp());
	T_stm init_stm = T_Seq(T_Move(i, unEx(lo)), T_Move(limit, unEx(hi)));
    Temp_label bodyLabel = Temp_newlabel(), addLabel = Temp_newlabel();

	T_stm stm = T_Seq(init_stm, 
				T_Seq(T_Cjump(T_le, i, limit, bodyLabel, done),	//  <= body
				T_Seq(T_Label(bodyLabel),
				T_Seq(unNx(body),
				T_Seq(T_Cjump(T_eq, i, limit, done, addLabel),
				T_Seq(T_Label(addLabel),
				T_Seq(T_Move(i, T_Binop(T_plus, i, T_Const(1))),
				T_Seq(T_Jump(T_Name(bodyLabel), Temp_LabelList(bodyLabel, NULL)),
					  T_Label(done)))))))));
	return Tr_Nx(stm);
}

Tr_exp Tr_breakExp(Temp_label done){
	return Tr_Nx(T_Jump(T_Name(done), Temp_LabelList(done, NULL)));
}

static Tr_access Tr_Access(Tr_level level, F_access access) {
	Tr_access a = checked_malloc(sizeof(*a));
	a->level = level;
	a->access = access;
	return a;
}

static Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail) {
	Tr_accessList l = checked_malloc(sizeof(*l));
	l->head = head;
	l->tail = tail;
	return l; 
}

static patchList PatchList(Temp_label *head, patchList tail) {
	patchList l = checked_malloc(sizeof(*l));
	l->head = head;
	l->tail = tail;
	return l;
}

static patchList doPatch(patchList tList, Temp_label label) {
	for (; tList; tList = tList->tail)
		*(tList->head) = label;
}

static patchList joinPatch(patchList first, patchList second) {
	if (!first)	
		return second;
	for (; first->tail; first = first->tail);
	first->tail = second;
	return first;
}

static Tr_exp Tr_Ex(T_exp ex) {
	Tr_exp e = checked_malloc(sizeof(*e));
	e->kind = Tr_ex;
	e->u.ex = ex;
	return e;
}

static Tr_exp Tr_Nx(T_stm nx) {
	Tr_exp e = checked_malloc(sizeof(*e));
	e->kind = Tr_nx;
	e->u.nx = nx;
	return e;
}

static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm) {
	Tr_exp e = checked_malloc(sizeof(*e));
	e->kind = Tr_cx;
	e->u.cx.trues = trues;
	e->u.cx.falses = falses;
	e->u.cx.stm = stm;
	return e;
}

static T_exp unEx(Tr_exp e) {
	switch(e->kind) {
		case Tr_ex:
			return e->u.ex;
		case Tr_cx: {
			Temp_temp r = Temp_newtemp();
			Temp_label t = Temp_newlabel(), f = Temp_newlabel();
			doPatch(e->u.cx.trues, t);
			doPatch(e->u.cx.falses, f);
			return T_Eseq(T_Move(T_Temp(r), T_Const(1)),
						  T_Eseq(e->u.cx.stm,
								 T_Eseq(T_Label(f),
										T_Eseq(T_Move(T_Temp(r), T_Const(0)),
											   T_Eseq(T_Label(t),T_Temp(r))))));
		}
		case Tr_nx:
			return T_Eseq(e->u.nx, T_Const(0));
		default:
			assert(0) ; /*can't get here */
	}
}

static T_stm unNx(Tr_exp e) {
	switch (e->kind) { 
		case Tr_ex:
			return T_Exp(e->u.ex);
		case Tr_nx:
			return e->u.nx;
		case Tr_cx: {
			Temp_label label = Temp_newlabel();
            doPatch(e->u.cx.trues, label);
            doPatch(e->u.cx.falses, label);
            return T_Seq(e->u.cx.stm, T_Label(label));
		}
	}
	assert(0);
}

static struct Cx unCx(Tr_exp e) {
	switch(e->kind) {
		case Tr_cx:
			return e->u.cx;
		case Tr_ex: {
			struct Cx cx;
			if(e->u.ex->kind == T_CONST){		//specially treat CONST
				if(e->u.ex->u.CONST == 0){		//false
					cx.stm = T_Jump(T_Name(NULL),Temp_LabelList(NULL, NULL));
					cx.trues = PatchList(&cx.stm->u.JUMP.exp->u.NAME,
                            	PatchList(&cx.stm->u.JUMP.jumps->head, NULL));	
					cx.falses = NULL;
				}
				else{							//true
					cx.stm = T_Cjump(T_ne, e->u.ex, T_Const(0), NULL, NULL);
					cx.trues = NULL;
					cx.falses = PatchList(&cx.stm->u.JUMP.exp->u.NAME,
                                PatchList(&cx.stm->u.JUMP.jumps->head, NULL));
				}
				return cx;
			}
			cx.stm = T_Cjump(T_ne, e->u.ex, T_Const(0), NULL, NULL);
			cx.trues = PatchList(&cx.stm->u.CJUMP.true, NULL);
			cx.falses = PatchList(&cx.stm->u.CJUMP.false, NULL);
			return cx;
		}
		default:
			assert(0);
	}
}

static T_exp staticLink(Tr_level cur, Tr_level target){
	T_exp link = T_Temp(F_FP());
	while(cur && cur != target){
		F_access ac = F_formals(cur->frame)->head;
		link = F_Exp(ac, link);
		cur = cur->parent;
	}
	return link;
}

void Tr_init(){
	fragList = F_FragList(NULL, NULL);
	frag_tail = fragList;
}

Tr_exp Tr_assignExp(Tr_exp left, Tr_exp right) {
	return Tr_Nx(T_Move(unEx(left), unEx(right)));
}

static Tr_accessList makeFormalList(Tr_level l) {
	Tr_accessList head = NULL, tail = NULL;
	F_accessList ptr = F_formals(l->frame);
	for (; ptr; ptr = ptr->tail) {
		Tr_access ac = Tr_Access(l, ptr->head);
		if (head) {
			tail->tail = Tr_AccessList(ac, NULL);
			tail = tail->tail;
		} else {
			head = Tr_AccessList(ac, NULL);
			tail = head;
		}
	}
	return head;
}
