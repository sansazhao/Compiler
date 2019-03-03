#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "errormsg.h"
#include "tree.h"
#include "assem.h"
#include "frame.h"
#include "codegen.h"
#include "table.h"

#define MAXLINE 100
#define L Temp_TempList

static AS_instrList iList, last;
static F_frame frame;           //a stamp for munchexp 
static const int wordSize = 8;

static int munchArgs(int i, T_expList args);
static Temp_temp munchExp(T_exp e);
static void  munchStm(T_stm stm);

static Temp_temp ith_arg(int i){
    Temp_tempList six_regs = F_argregs();
    for(int idx = 0; idx < i; idx++)
        six_regs = six_regs->tail;
    return six_regs->head;
}

static void emit(AS_instr inst){
    if(last)
        last = last->tail = AS_InstrList(inst, NULL);
    else
        last  = iList = AS_InstrList(inst, NULL);
}

AS_instrList F_codegen(F_frame f, T_stmList stmList) {
    iList = last = AS_InstrList(NULL, NULL);
    frame = f;  //save static frame

    // move callee_save -> tmp
    Temp_tempList callee = F_callee_save();
    Temp_tempList bak, tmp; 
    bak = tmp = L(Temp_newtemp(), NULL);
    for(; callee; tmp = tmp->tail = L(Temp_newtemp(), NULL), callee = callee->tail)
        emit(AS_Move("movq `s0, `d0", L(tmp->head, NULL), L(callee->head, NULL)));
    
    // put args to according frame access/regs
    F_accessList formals = F_formals(f);
    int frame_index = 0;
    for(int reg_num = 0; reg_num < 6 && formals; reg_num++){
        Temp_temp reg = ith_arg(reg_num);
        if(formals->head->kind == inFrame){
            /* delete fp: fp -> rsp + fs
            *   move rsp -> d
            *   d += fs
            *   move reg -> -8(d), -16(d)...
            */
            Temp_temp d = Temp_newtemp();
            emit(AS_Oper("movq `s0, `d0", L(d, NULL), L(F_RSP(), NULL), NULL));
            char *inst = checked_malloc(MAXLINE * sizeof(char));
            sprintf(inst, "addq $%s_framesize, `d0", Temp_labelstring(F_name(f)));
            emit(AS_Oper(inst, L(d, NULL), NULL, NULL));
            inst = checked_malloc(MAXLINE * sizeof(char));
            frame_index++;
            sprintf(inst, "movq `s0, %d(`d0)", -(frame_index) * wordSize);
            emit(AS_Oper(inst, L(d, NULL), L(reg, NULL), NULL));
        }
        else
            emit(AS_Move("movq `s0, `d0", L(formals->head->u.reg, NULL), L(reg, NULL)));
        formals = formals->tail;
    }

    for(T_stmList sl = stmList; sl; sl = sl->tail){
        munchStm(sl->head);
    }

    // restore tmp -> callee_save
    callee = F_callee_save();
    tmp = bak;
    for(; callee; tmp = tmp->tail, callee = callee->tail)
        emit(AS_Move("movq `s0, `d0", L(callee->head, NULL), L(tmp->head, NULL)));
    return iList->tail;
}

static int munchArgs(int i, T_expList args){
    if(!args)return 0;
    int push = 0;
    if(i < 6){   //to regs
        Temp_temp dst = ith_arg(i);
        emit(AS_Move("movq `s0, `d0", L(dst, NULL), L(munchExp(args->head), NULL)));
        munchArgs(i+1, args->tail); //i+1
    }
    else{ //push rest args
        push = 1 + munchArgs(i+1, args->tail);
        emit(AS_Oper("pushq `s0", NULL, L(munchExp(args->head), NULL), NULL));
    }
    return push;
}

static Temp_temp munchExp(T_exp e){
    Temp_temp d = Temp_newtemp();
    char *inst = checked_malloc(MAXLINE * sizeof(char));
    switch(e->kind){
        case T_BINOP:{
			Temp_temp left = munchExp(e->u.BINOP.left);
			Temp_temp right = munchExp(e->u.BINOP.right);
            string op;
            switch(e->u.BINOP.op){ 
                case T_plus: op = "addq `s0, `d0"; break;
                case T_minus: op = "subq `s0, `d0"; break;
                case T_mul: op = "imulq `s0, `d0"; break;
                case T_div: {
                    Temp_temp left = munchExp(e->u.BINOP.left);
                    Temp_temp right = munchExp(e->u.BINOP.right);
                    emit(AS_Move("movq `s0, `d0", L(F_RAX(), NULL), L(left, NULL)));
                    emit(AS_Oper("cqto", L(F_RDX(), L(F_RAX(), NULL)), L(F_RAX(), NULL), NULL));
                    emit(AS_Oper("idivq `s0", L(F_RDX(), L(F_RAX(), NULL)), L(right, NULL), NULL));
                    emit(AS_Move("movq `s0, `d0", L(d, NULL), L(F_RAX(), NULL)));
                    return d;
                }
                case T_and:     case T_or:      case T_lshift: 
                case T_rshift:  case T_arshift: case T_xor:
                    assert(0);
            }
            emit(AS_Move("movq `s0, `d0", L(d, NULL), L(left, NULL)));
			emit(AS_Oper(op, L(d, NULL), L(right, L(d, NULL)), NULL));
			return d;
        }
        case T_MEM:{
            // fp = sp + (fs + const k)
            if(e->u.MEM->kind == T_BINOP && e->u.MEM->u.BINOP.right->u.TEMP == F_FP()){
                sprintf(inst, "movq %s_framesize + %d(`s0), `d0", Temp_labelstring(F_name(frame)), e->u.MEM->u.BINOP.left->u.CONST);
                emit(AS_Oper(inst, L(d, NULL), L(F_RSP(), NULL), NULL));
            }
            else if(e->u.MEM->kind == T_BINOP && e->u.MEM->u.BINOP.left->kind == T_CONST){
                sprintf(inst, "movq %d(`s0), `d0", e->u.MEM->u.BINOP.left->u.CONST);
                emit(AS_Oper(inst, L(d, NULL), L(munchExp(e->u.MEM->u.BINOP.right), NULL), NULL));
            }
            else
                emit(AS_Oper("movq (`s0), `d0", L(d, NULL), 
                                                L(munchExp(e->u.MEM), NULL), NULL));
		    return d;
        }
        case T_TEMP:{
            if (e->u.TEMP == F_FP()){   //return sp + fs
                sprintf(inst, "addq $%s_framesize, `d0", Temp_labelstring(F_name(frame)));
                emit(AS_Oper("movq `s0, `d0", L(d, NULL), L(F_RSP(), NULL), NULL));
                emit(AS_Oper(inst, L(d, NULL), NULL, NULL));
            }
            else
                d = e->u.TEMP;
            return d;
        }
        case T_NAME:{
		    sprintf(inst, "movq $%s, `d0", Temp_labelstring(e->u.NAME));
		    emit(AS_Oper(inst, L(d, NULL), NULL, NULL));
            return d;
        }
        case T_CONST:{
		    sprintf(inst, "movq $%d, `d0", e->u.CONST);
		    emit(AS_Oper(inst, L(d, NULL), NULL, NULL));
            return d;
        }
        case T_CALL:{
            Temp_label func = e->u.CALL.fun->u.NAME;
            int push_num = munchArgs(0, e->u.CALL.args);
            Temp_tempList call_defs = Temp_TempList(F_RAX(), F_caller_save());   //rax & caller_save regs
	        sprintf(inst, "call %s", Temp_labelstring(func));
	        emit(AS_Oper(inst, call_defs, NULL, NULL));

            // pop stack
            if(push_num > 0){
                inst = checked_malloc(MAXLINE * sizeof(char));
	            sprintf(inst, "addq $%d, %%rsp\n", push_num * wordSize);
                emit(AS_Oper(inst, NULL, NULL, NULL));
            }
            // move rax -> dst
	        emit(AS_Move("movq `s0, `d0", L(d, NULL), L(F_RAX(), NULL)));
            return d;
        }
        case T_ESEQ:
            assert(0);
    }
}

static void  munchStm(T_stm stm){
    switch(stm->kind){
        case T_LABEL:
            emit(AS_Label(Temp_labelstring(stm->u.LABEL),stm->u.LABEL));
            return;
        case T_JUMP:
            emit(AS_Oper("jmp `j0", NULL, NULL, AS_Targets(stm->u.JUMP.jumps)));
            return;
        case T_CJUMP:{
            Temp_temp left = munchExp(stm->u.CJUMP.left);
            Temp_temp right = munchExp(stm->u.CJUMP.right);
            emit(AS_Oper("cmp `s1, `s0", NULL, L(left, L(right, NULL)), AS_Targets(NULL)));
            string inst;
            switch(stm->u.CJUMP.op){
                case T_eq:inst = "je `j0";break;
                case T_ne:inst = "jne `j0";break;
                case T_lt:inst = "jl `j0";break;
                case T_gt:inst = "jg `j0";break;
                case T_le:inst = "jle `j0";break;
                case T_ge:inst = "jge `j0";break;
                case T_ult:inst = "jb `j0";break;
                case T_ule:inst = "jbe `j0";break;
                case T_ugt:inst = "ja `j0";break;
                case T_uge:inst = "jae `j0";break;
            }
            emit(AS_Oper(inst, NULL, NULL, AS_Targets(Temp_LabelList(stm->u.CJUMP.true, NULL))));
            return;
        }
        case T_MOVE:{
            T_exp dst = stm->u.MOVE.dst, src = stm->u.MOVE.src;
            if (dst->kind == T_MEM){
                if (dst->u.MEM->kind == T_BINOP){
                    string inst = checked_malloc(MAXLINE * sizeof(char));
                    if (dst->u.MEM->u.BINOP.right->kind == T_CONST){
                        T_exp e1 = dst->u.MEM->u.BINOP.left, e2 = src;
                        // movq src -> i(left)
                        sprintf(inst, "movq `s0, %d(`s1)", dst->u.MEM->u.BINOP.right->u.CONST);
                        emit(AS_Oper(inst, NULL, L(munchExp(e2), L(munchExp(e1), NULL)), NULL));
                        return;
                    }
                    else if (dst->u.MEM->u.BINOP.left->kind == T_CONST){
                        T_exp e1 = dst->u.MEM->u.BINOP.right, e2 = src;
                        // movq src -> i(right)
                        sprintf(inst, "movq `s0, %d(`s1)", dst->u.MEM->u.BINOP.left->u.CONST);
                        emit(AS_Oper(inst, NULL, L(munchExp(e2), L(munchExp(e1), NULL)), NULL));
                        return;
                    }
                    else{
			            emit(AS_Oper("movq `s0, (`s1)", NULL, L(munchExp(src), L(munchExp(dst->u.MEM), NULL)), NULL));
                        return;
                    }
                }
                else if (src->kind == T_MEM);
                else{
                    emit(AS_Oper("movq `s0, (`s1)", NULL, L(munchExp(src), 
                                                L(munchExp(dst->u.MEM), NULL)), NULL));
                    return;
                }
            }
            else if(dst->kind == T_TEMP){
			    emit(AS_Move("movq `s0, `d0", L(munchExp(dst), NULL), L(munchExp(src), NULL)));
                return;
            }
        }
        case T_EXP:
            munchExp(stm->u.EXP);
            return;
        case T_SEQ:
            return;
    }
}

