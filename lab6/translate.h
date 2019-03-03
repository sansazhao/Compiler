#ifndef TRANSLATE_H
#define TRANSLATE_H

#include "util.h"
#include "absyn.h"
#include "temp.h"
#include "frame.h"

/* Lab5: your code below */

typedef struct Tr_exp_ *Tr_exp;

typedef struct Tr_expList_ *Tr_expList;

struct Tr_expList_ {
	Tr_exp head;
	Tr_expList tail;	
};

typedef struct Tr_access_ *Tr_access;

typedef struct Tr_accessList_ *Tr_accessList;

struct Tr_accessList_ {
	Tr_access head;
	Tr_accessList tail;	
};

typedef struct Tr_level_ *Tr_level;

//frame
Tr_access Tr_allocLocal(Tr_level level, bool escape);
Tr_accessList Tr_formals(Tr_level level);
Tr_level Tr_outermost(void);
Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals);
void Tr_procEntryExit(Tr_level level, Tr_exp body,Tr_accessList formals);
void Tr_init();
// IR tree exp
Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail);
Tr_exp Tr_simpleVar(Tr_access access, Tr_level level);
Tr_exp Tr_fieldVar(Tr_exp ptr, int index);
Tr_exp Tr_subscriptVar(Tr_exp ptr, Tr_exp index); 
Tr_exp Tr_null();
Tr_exp Tr_intExp(int value);
Tr_exp Tr_stringExp(string str);
Tr_exp Tr_callExp(Temp_label fun, Tr_expList args, Tr_level caller, Tr_level callee);
Tr_exp Tr_arithExp(A_oper oper, Tr_exp left, Tr_exp right);
Tr_exp Tr_relExp(A_oper oper, Tr_exp left, Tr_exp right);
Tr_exp Tr_recordExp(Tr_expList fields);
Tr_exp Tr_arrayExp(Tr_exp size_exp, Tr_exp init_exp);
Tr_exp Tr_seqExp(Tr_expList l);
Tr_exp Tr_assignExp(Tr_exp lvalue, Tr_exp value);
Tr_exp Tr_ifExp(Tr_exp test, Tr_exp then, Tr_exp elsee);
Tr_exp Tr_whileExp(Tr_exp test, Tr_exp body, Temp_label done);
Tr_exp Tr_forExp(Tr_level level, Tr_access loop_var_access, Tr_exp lo, Tr_exp hi, Tr_exp body, Temp_label done);
Tr_exp Tr_breakExp(Temp_label done);
Tr_exp Tr_funcDec(Tr_exp body, Tr_level lv);
F_fragList Tr_getResult(void);	//fraglist
Tr_exp Tr_stringCompareExp(A_oper oper, Tr_exp left, Tr_exp right);



#endif
