#include <stdio.h>
#include <string.h>
#include "prog1.h"

typedef struct table *Table_;
struct table {
    string id;
    int value;
    Table_ tail;
};

struct IntAndTable{
    int i;
    Table_ t;
};

int maxargs(A_stm stm);
struct IntAndTable interpExp(A_exp e, Table_ t);

Table_ Table(string id, int value, struct table *tail){
    Table_ t = checked_malloc(sizeof(*t));
    t->id = id;
    t->value = value;
    t->tail = tail;
    return t;
}

int maxargsExp(A_exp exp){
    switch(exp->kind){
        case A_idExp:case A_numExp:
            return 1;
        case A_opExp:{
            int n1 = maxargsExp(exp->u.op.left);
            int n2 = maxargsExp(exp->u.op.right);
            return n1 > n2 ? n1 : n2;
        }
        case A_eseqExp:{
            int n1 = maxargs(exp->u.eseq.stm);
            int n2 = maxargsExp(exp->u.eseq.exp);
            return n1 > n2 ? n1 : n2;
        }
        default:
            return 0;
    }
}

int maxargsExpList(A_expList exps){
    switch(exps->kind){
        case A_pairExpList:{
            int n1 = maxargsExp(exps->u.pair.head);
            int n2 = maxargsExpList(exps->u.pair.tail);
            return n1 > n2 ? n1 : n2;
        }
        case A_lastExpList:
            return maxargsExp(exps->u.last);
        default:
            return 0;
    }
}

int argsExpList(A_expList exps){
    if(exps->kind == A_pairExpList)
        return 1 + argsExpList(exps->u.pair.tail);
    return 1;
}

int maxargs(A_stm stm){
    switch(stm->kind){
        case A_assignStm:
            return maxargsExp(stm->u.assign.exp);
        case A_compoundStm:{
            int n1 = maxargs(stm->u.compound.stm1);
            int n2 = maxargs(stm->u.compound.stm2);
            return n1 > n2 ? n1 : n2;
        }
        case A_printStm:{
            int args = argsExpList(stm->u.print.exps);
            int max = maxargsExpList(stm->u.print.exps);
            return args > max ? args : max;
        }
        default:
            return 0;
    }
}

Table_ update(Table_ t, string key, int i){
    return Table(key,i,t);
}

int lookup(Table_ t, string key){
    if(strcmp(t->id, key) == 0)
        return t->value;
    else
        return lookup(t->tail, key);
}

Table_ printExpList(A_expList exps, Table_ t){
    if(exps->kind == A_pairExpList){
        struct IntAndTable it = interpExp(exps->u.pair.head, t);
        printf("%d ",it.i);
        return printExpList(exps->u.pair.tail, it.t);
    }
    else{
        struct IntAndTable it = interpExp(exps->u.last, t);
        printf("%d\n",it.i);
        return it.t;
    }
}

Table_ interpStm(A_stm s, Table_ t){
    switch(s->kind){
        case A_assignStm:{
            struct IntAndTable right = interpExp(s->u.assign.exp, t);
            return update(right.t, s->u.assign.id, right.i);
        }
        case A_compoundStm:
            return interpStm(s->u.compound.stm2, interpStm(s->u.compound.stm1, t));
        case A_printStm:
            return printExpList(s->u.print.exps, t);
        default:
            return t;
    }
}

struct IntAndTable IntAndTable(int i, Table_ t){
    struct IntAndTable it;
    it.i = i;
    it.t = t;
    return it;
}

struct IntAndTable interpExp(A_exp e, Table_ t){
    switch(e->kind){
        case A_idExp:
            return IntAndTable(lookup(t, e->u.id), t);
        case A_numExp:
            return IntAndTable(e->u.num, t);
        case A_opExp: {
            struct IntAndTable left = interpExp(e->u.op.left, t);
            struct IntAndTable right = interpExp(e->u.op.right, left.t);
            switch(e->u.op.oper){
                case A_plus:
                    return IntAndTable(left.i + right.i, right.t);
                case A_minus:
                    return IntAndTable(left.i - right.i, right.t);
                case A_times:
                    return IntAndTable(left.i * right.i, right.t);
                case A_div:
                    return IntAndTable(left.i / right.i, right.t);
            }
        }   
        case A_eseqExp:default:
            return interpExp(e->u.eseq.exp, interpStm(e->u.eseq.stm,t));
    }
}

void interp(A_stm stm)
{
    interpStm(stm, NULL);
}
