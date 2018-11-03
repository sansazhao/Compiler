#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "helper.h"
#include "env.h"
#include "semant.h"

/*Lab4: Your implementation of lab4*/


typedef void* Tr_exp;
struct expty 
{
	Tr_exp exp; 
	Ty_ty ty;
};

//In Lab4, the first argument exp should always be **NULL**.
struct expty expTy(Tr_exp exp, Ty_ty ty)
{
	struct expty e;

	e.exp = exp;
	e.ty = ty;

	return e;
}

Ty_ty type(Ty_ty t_name){
	if(t_name->kind == Ty_name)
		return type(t_name->u.name.ty);
	return t_name;
}

struct expty transExp (S_table venv, S_table tenv, A_exp a){
    switch (a->kind) {
		case A_opExp:{
			A_oper oper = a->u.op.oper;
			struct expty left = transExp(venv,tenv,a->u.op.left);
			struct expty right = transExp(venv,tenv,a->u.op.right);
			if(oper == A_plusOp || oper == A_minusOp 
			|| oper == A_timesOp || oper == A_divideOp) {
				if(left.ty->kind != Ty_int)
				EM_error(a->u.op.left->pos, "integer required");
				if(right.ty->kind != Ty_int)
				EM_error(a->u.op.right->pos, "integer required");
				return expTy(NULL, Ty_Int());
			}
			else{//eq neq lt le gt ge
				if(type(left.ty) != type(right.ty))
				EM_error(a->u.op.left->pos, "same kind required");
				return expTy(NULL, Ty_Int());
			}
		}
		case A_letExp:{
			struct expty exp;
			A_decList d;
			S_beginScope(venv);
			S_beginScope(tenv);
			for(d = a->u.let.decs; d; d = d->tail)
				transDec(venv, tenv, d->head);
			exp = transExp(venv, tenv, a->u.let.body);
			S_endScop(tenv);  
			S_endScop(venv);
			return exp;
    	}
		case A_varExp:
			return transVar(venv, tenv, a->u.var);
		case A_nilExp:
			return expTy(NULL, Ty_Nil());
		case A_intExp:
			return expTy(NULL, Ty_Int());
		case A_stringExp:
			return expTy(NULL, Ty_String());
		case A_callExp:{
			E_enventry x = S_look(venv, a->u.call.func);
			if(x && x->kind == E_funEntry){//check formals
				Ty_tyList expect = x->u.fun.formals;
				A_expList actual = a->u.call.args;
				while(expect && actual){
					struct expty exp_arg = transExp(venv, tenv, actual->head);
					if(type(exp_arg.ty)->kind != type(expect->head)->kind)
						EM_error(actual->head->pos, "wrong arg type %s", S_name(a->u.call.args));
					expect = expect->tail;
					actual = actual->tail;
				}
				if(expect || actual)
					EM_error(actual->head->pos, "less or more arg %s", S_name(a->u.call.args));
				return expTy(NULL, actual_ty(x->u.fun.result));
			}
			else{
				EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
				return expTy(NULL, Ty_Int());
			}
		}
		case A_recordExp:{
			Ty_ty ty = S_look(venv, a->u.record.typ);
			ty = type(ty);
			if(!ty)
				EM_error(a->pos, "undefined record  %s", S_name(a->u.record.typ));
			if(ty->kind != Ty_record)
				EM_error(a->pos, "not record  %s", S_name(a->u.record.typ));
			A_efieldList actual = a->u.record.fields;
			A_fieldList expect = ty->u.record;
			while(actual && expect){
				if(actual->head->name != expect->head->name)
					EM_error(a->pos, "record name doesn't exist %s", S_name(a->u.record.typ));
				struct expty exp_rec = transExp(venv, tenv, actual->head->exp);
				if(type(exp_rec.ty) != type(expect->head->typ))
					EM_error(a->pos, "wrong arg type %s", S_name(a->u.record.typ));
				expect = expect->tail;
				actual = actual->tail;
			}
			if(expect || actual)
				EM_error(a->pos, "less or more field %s", S_name(a->u.record.typ));
			return expTy(NULL, ty);
		}
		case A_seqExp:
		case A_assignExp:
		case A_ifExp:{
			struct expty test = transExp(venv, tenv, a->u.iff.test);
			if(type(test.ty)->kind != Ty_int)
				EM_error(a->pos, "test part of if should be int %s", S_name(a->u.iff.test));
			struct expty then = transExp(venv, tenv, a->u.iff.then);
			struct expty elsee = transExp(venv, tenv, a->u.iff.elsee);
			return expTy(NULL, then.ty);
		}
		case A_forExp:
		case A_whileExp:
		case A_breakExp:
		case A_arrayExp:
		default: break;
	}
}

struct expty transVar (S_table venv, S_table tenv, A_var v){
    switch (v->kind) {
		case A_simpleVar:{
			E_enventry x = S_look(venv, v->u.simple) ;
			if(x && x->kind == E_varEntry) 
				return expTy(NULL, actual_ty(x->u.var.ty));
			else{
				EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
				return expTy(NULL, Ty_Int());
			}
		}
		case A_fieldVar:{
		}
		case A_subscriptVar:{
		}
		break;
	}
}

void transDec (S_table venv, S_table tenv, A_dec d){
    switch(d->kind){
		case A_varDec:{
			struct expty e = transExp(venv, tenv, d->u.var.init);
			S_enter(venv, d->u.var.var, E_VarEntry(e.ty));
		}
		case A_typeDec:{
			S_enter(tenv, d->u.type->head->name, transTy(tenv, d->u.type->head->ty));
		}
		case A_functionDec:{
			A_fundec f = d->u.function->head;
			Ty_ty resultTy = S_look(tenv, f->result);
			Ty_tyList formalTys = makeFromalTyList(tenv, f->params);
			S_enter(venv, f->name, E_FunEntry(formalTys, resultTy));
			S_beginScope(venv); 
			{   A_fieldList l;
				Ty_tyList t_name;
				for(l=f->params, t_name=formalTys; l; l=l->tail, t_name=t_name->tail)
					S_enter(venv, l->head->name, E_VarEntry(t_name->head));
			}
			transExp(venv, tenv, d->u.function->head->body);
			S_endScope(venv);
		}
		break;
    }
}



