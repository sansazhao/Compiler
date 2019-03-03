
/*Lab5: This header file is not complete. Please finish it with more definition.*/

#ifndef FRAME_H
#define FRAME_H

#include "tree.h"
#include "assem.h"

typedef struct F_access_ *F_access;

struct F_access_ {
	enum {inFrame, inReg} kind;
	union {
		int offset; //inFrame
		Temp_temp reg; //inReg
	} u;
};

typedef struct F_accessList_ *F_accessList;

// the frame->access->head is static link, tail -> others
struct F_accessList_ {F_access head; F_accessList tail;};

/* temp */
F_accessList F_AccessList(F_access head, F_accessList tail);

typedef struct F_frame_ *F_frame;

struct F_frame_ {
	F_accessList formals;
	int local;
	Temp_label label;
};

// extern const int wordSize;

F_frame F_newFrame(Temp_label name, U_boolList formals);

Temp_label F_name(F_frame f);
F_accessList F_formals(F_frame f);
F_access F_allocLocal(F_frame f, bool escape);

T_exp F_Exp(F_access acc, T_exp framePtr);

T_exp F_externalCall(string s, T_expList args);

/* declaration for fragments */
typedef struct F_frag_ *F_frag;
struct F_frag_ {enum {F_stringFrag, F_procFrag} kind;
			union {
				struct {Temp_label label; string str;} stringg;
				struct {T_stm body; F_frame frame;} proc;
			} u;
};

F_frag F_StringFrag(Temp_label label, string str);
F_frag F_ProcFrag(T_stm body, F_frame frame);

typedef struct F_fragList_ *F_fragList;
struct F_fragList_ 
{
	F_frag head; 
	F_fragList tail;
};

F_fragList F_FragList(F_frag head, F_fragList tail);

AS_proc F_procEntryExit3(F_frame frame, AS_instrList il);

Temp_temp F_FP();

Temp_temp F_RAX();
Temp_temp F_RDX();
Temp_temp F_RSP();

Temp_map F_tempMap;
Temp_tempList F_regs();
Temp_tempList F_specialregs();
Temp_tempList F_argregs();
Temp_tempList F_caller_save();
Temp_tempList F_callee_save();
void F_initTempMap();

#endif
