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
#include "translate.h"

static Temp_label breakLabel;	//record the last breaklabel instead of reference

struct expty {
	Tr_exp exp; 
	Ty_ty ty;
};

struct expty expTy(Tr_exp exp, Ty_ty ty){
	struct expty e;
	e.exp = exp;
	e.ty = ty;
	return e;
}

static struct expty transVar(Tr_level level, S_table venv, S_table tenv, A_var v);
static struct expty transExp(Tr_level level, S_table venv, S_table tenv, A_exp a);
static Tr_exp transDec(Tr_level level, S_table venv, S_table tenv, A_dec d);
static Ty_ty transTy(S_table tenv, A_ty a);


Ty_fieldList makeFieldList(S_table tenv, A_fieldList a) {
	if (!a)
		return NULL;
	Ty_ty t = S_look(tenv, a->head->typ);
	if (!t) {
		EM_error(a->head->pos, "undefined type %s", S_name(a->head->typ));
		t = Ty_Int();
	}
	return Ty_FieldList(Ty_Field(a->head->name, t), makeFieldList(tenv, a->tail));
}

Ty_tyList makeTyList(S_table tenv, A_fieldList fields) {
	if(!fields)
		return NULL;
	Ty_ty ty = 	S_look(tenv, fields->head->typ);
	if(!ty){
		EM_error(fields->head->pos, "undefined type %s", S_name(fields->head->typ));
		ty = Ty_Int();
	}
	return Ty_TyList(ty, makeTyList(tenv, fields->tail));
}

U_boolList makeFormalList(A_fieldList params) {
	if(!params){
        return NULL;
    }
    return U_BoolList(params->head->escape, makeFormalList(params->tail));
}

Ty_ty actual_ty(Ty_ty t) {
	if (!t)
		return NULL;
	while (t && t->kind == Ty_name)
		t = t->u.name.ty;
	return t;
}

// entrance
F_fragList SEM_transProg(A_exp exp) {
	Tr_init();
	Tr_level mainLevel = Tr_newLevel(Tr_outermost(), Temp_namedlabel("tigermain"), NULL);
	E_enventry entry = E_FunEntry(mainLevel, Temp_newlabel(), NULL, Ty_Void());
	struct expty body = transExp(mainLevel, E_base_venv(), E_base_tenv(), exp);
	
	Tr_procEntryExit(entry->u.fun.level, body.exp, NULL);
	return Tr_getResult();
}

struct expty transExp(Tr_level tlevel, S_table venv, S_table tenv, A_exp a) {
	switch (a->kind) {
		case A_varExp: 
			return transVar(tlevel, venv, tenv, a->u.var);	
		case A_nilExp: 
			return expTy(Tr_null(), Ty_Nil());	
		case A_intExp: 
			return expTy(Tr_intExp(a->u.intt), Ty_Int());	
		case A_stringExp: 
			return expTy(Tr_stringExp(a->u.stringg), Ty_String());	
		case A_callExp: {
			E_enventry x = S_look(venv, a->u.call.func);
			printf("call: %s\n",S_name(x->u.fun.label));
			if(x && x->kind == E_funEntry){   //check formals
				Ty_tyList expect = x->u.fun.formals;
				A_expList actual = a->u.call.args;
				Tr_expList list = NULL, t = NULL;
				while(expect && actual){
					struct expty exp_arg = transExp(tlevel, venv, tenv, actual->head);
					if(actual_ty(exp_arg.ty)->kind != actual_ty(expect->head)->kind
						&& !(actual_ty(expect->head)->kind == Ty_record
							 && actual_ty(exp_arg.ty)->kind == Ty_nil))
						EM_error(actual->head->pos, "para type mismatch");
					expect = expect->tail;
					actual = actual->tail;
					if(list){
						t->tail = Tr_ExpList(exp_arg.exp, NULL);
						t = t->tail;
					}
					else{
						list = Tr_ExpList(exp_arg.exp, NULL);
						t = list;
					}
				}
				if(expect || actual)
					EM_error(actual->head->pos, "too many params in function %s", S_name(a->u.call.func));
				Tr_exp tr_exp = Tr_callExp(x->u.fun.label, list, x->u.fun.level, tlevel);
				// return expTy(tr_exp, actual_ty(x->u.fun.result));
				return expTy(tr_exp, x->u.fun.result);

			}
			else{
				EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
				return expTy(NULL, Ty_Int());
			}
		}
		case A_opExp: {
			A_oper oper = a->u.op.oper;
			struct expty left = transExp(tlevel, venv, tenv, a->u.op.left);
			struct expty right = transExp(tlevel, venv, tenv, a->u.op.right);
			if(oper == A_plusOp || oper == A_minusOp 
			|| oper == A_timesOp || oper == A_divideOp) {
				if(actual_ty(left.ty)->kind != Ty_int){
					EM_error(a->u.op.left->pos, "integer required");
					return expTy(Tr_null(), Ty_Int());
				}
				if(actual_ty(right.ty)->kind != Ty_int){
					EM_error(a->u.op.right->pos, "integer required");
					return expTy(Tr_null(), Ty_Int());
				}
				//IR
				return expTy(Tr_arithExp(oper, left.exp, right.exp), Ty_Int());
			}
			else if(oper == A_neqOp || oper == A_eqOp){//eq neq
				if(actual_ty(left.ty) != actual_ty(right.ty)
					 && !(actual_ty(left.ty)->kind == Ty_record && actual_ty(right.ty)->kind == Ty_nil)){
					EM_error(a->pos, "same type required");
					return expTy(Tr_null(), Ty_Int());
				}
				if(left.ty->kind == Ty_string || right.ty->kind == Ty_string)
					return expTy(Tr_stringCompareExp(oper, left.exp, right.exp), Ty_Int());
				else
					return expTy(Tr_relExp(oper, left.exp, right.exp), Ty_Int());
			}
			else{//lt le gt ge
				if(actual_ty(left.ty) != actual_ty(right.ty)
					 && !(actual_ty(left.ty)->kind == Ty_record && actual_ty(right.ty)->kind == Ty_nil)){
					EM_error(a->pos, "same type required");
					return expTy(Tr_null(), Ty_Int());
				}
				//IR
				return expTy(Tr_relExp(oper, left.exp, right.exp), Ty_Int());
			}
		} 
		case A_recordExp: {
			Ty_ty ty = S_look(tenv, a->u.record.typ);
			ty = actual_ty(ty);
			if(!ty){
				EM_error(a->pos, "undefined type %s", S_name(a->u.record.typ));
				return expTy(Tr_null(), Ty_Int());
			}
			if(ty->kind != Ty_record)
				EM_error(a->pos, "not record  %s", S_name(a->u.record.typ));
			A_efieldList actual = a->u.record.fields;
			Ty_fieldList expect = ty->u.record;
			Tr_expList fields = NULL;	//do not use Tr_Explist(NULL, NULL)to init
			while(actual && expect){
				if(actual->head->name != expect->head->name){
					EM_error(a->pos, "record name doesn't exist %s", S_name(a->u.record.typ));
					continue;
				}
				struct expty exp_rec = transExp(tlevel, venv, tenv, actual->head->exp);
				if(actual_ty(exp_rec.ty) != actual_ty(expect->head->ty)
					&& !(actual_ty(expect->head->ty)->kind == Ty_record
							 && actual_ty(exp_rec.ty)->kind == Ty_nil))
					EM_error(a->pos, "para type mismatch");
				expect = expect->tail;
				actual = actual->tail;
				fields = Tr_ExpList(exp_rec.exp, fields);
			}
			if(expect || actual)
				EM_error(a->pos, "less or more field %s", S_name(a->u.record.typ));
				return expTy(Tr_recordExp(fields), ty);
		}
		case A_seqExp: {
			A_expList seq = a->u.seq;
			if (seq == NULL)
				return expTy(Tr_null(), Ty_Void());
			struct expty ty;
			Tr_expList tl = NULL;
			while(seq){
				ty = transExp(tlevel, venv, tenv, seq->head);
				tl = Tr_ExpList(ty.exp, tl);
				seq = seq->tail;
			}
			return expTy(Tr_seqExp(tl), ty.ty);
		}
		case A_assignExp: {
			struct expty var = transVar(tlevel, venv, tenv, a->u.assign.var);
			struct expty exp = transExp(tlevel, venv, tenv, a->u.assign.exp);
			E_enventry x = S_look(venv, a->u.assign.var->u.simple);
			if(x && x->readonly == 1)
				EM_error(a->pos, "loop variable can't be assigned");
			if(actual_ty(var.ty) != actual_ty(exp.ty)
			 && !(actual_ty(var.ty)->kind == Ty_record && actual_ty(exp.ty)->kind == Ty_nil))
				EM_error(a->pos, "unmatched assign exp");
			return expTy(Tr_assignExp(var.exp, exp.exp), Ty_Void());
		}
		case A_ifExp: {
			struct expty test = transExp(tlevel, venv, tenv, a->u.iff.test);
			struct expty then = transExp(tlevel, venv, tenv, a->u.iff.then);
			struct expty elsee;
			if(a->u.iff.elsee){
				elsee = transExp(tlevel, venv, tenv, a->u.iff.elsee);
				// if(!elsee.ty || elsee.ty->kind == Ty_nil)
				// 	return expTy(Tr_ifExp(test.exp, then.exp, NULL), then.ty);
				// if(!then.ty);
				// else if(actual_ty(then.ty) != actual_ty(elsee.ty)
				// && !(actual_ty(then.ty)->kind == Ty_record && actual_ty(elsee.ty)->kind == Ty_nil))
				// 	EM_error(a->u.iff.then->pos, "then exp and else exp type mismatch");
				return expTy(Tr_ifExp(test.exp, then.exp, elsee.exp), then.ty);
			}
			return expTy(Tr_ifExp(test.exp, then.exp, NULL), Ty_Void());
		
		}
		case A_whileExp: {
			// printf("whileexp\n");
			struct expty t = transExp(tlevel, venv, tenv, get_whileexp_test(a));	
			Temp_label done = Temp_newlabel();
			breakLabel = done;
			struct expty b = transExp(tlevel,venv, tenv, get_whileexp_body(a));	
			if (t.ty->kind != Ty_int)
				EM_error(a->pos, "while-exp was not an integer");
			if (b.ty->kind != Ty_void)
				EM_error(a->pos, "while body must produce no value");
			return expTy(Tr_whileExp(t.exp, b.exp, done), Ty_Void());
		
		}
		case A_forExp: {
			struct expty lo = transExp(tlevel, venv, tenv, get_forexp_lo(a));
			struct expty hi = transExp(tlevel, venv, tenv, get_forexp_hi(a));
			if(actual_ty(lo.ty)->kind != Ty_int)
				EM_error(a->pos, "for exp's range type is not integer");
			if(actual_ty(hi.ty)->kind != Ty_int)
				EM_error(a->pos, "for exp's range type is not integer");
			S_beginScope(venv);
			Tr_access acc = Tr_allocLocal(tlevel, a->u.forr.escape);
			S_enter(venv, a->u.forr.var, E_ROVarEntry(acc, Ty_Int()));
			Temp_label done = Temp_newlabel();
			breakLabel = done;
			struct expty body = transExp(tlevel, venv, tenv, a->u.forr.body);
			S_endScope(venv);
			if (body.ty->kind != Ty_void)
				EM_error(a->pos, "body exp shouldn't return a value");
			return expTy(Tr_forExp(tlevel, acc, lo.exp, hi.exp, body.exp, done), Ty_Void());
		}
		case A_breakExp: {
			return expTy(Tr_breakExp(breakLabel), Ty_Void());
		}
		case A_letExp: {
			S_beginScope(venv);
			S_beginScope(tenv);
			struct expty exp;
			A_decList d;
			Tr_exp t_exp;
			Tr_expList el = NULL;
			for(d = a->u.let.decs; d; d = d->tail){
				t_exp = transDec(tlevel, venv, tenv, d->head);
				el = Tr_ExpList(t_exp, el);
			}
			exp = transExp(tlevel, venv, tenv, a->u.let.body);
			el = Tr_ExpList(exp.exp, el);
			S_endScope(tenv);  
			S_endScope(venv);
			return expTy(Tr_seqExp(el), exp.ty);
		}
		case A_arrayExp: {
			Ty_ty t = actual_ty(S_look(tenv, get_arrayexp_typ(a)));
			if (!t) {
				EM_error(a->pos, "undefined type %s", S_name(get_arrayexp_typ(a)));
				return expTy(Tr_null(), Ty_Int());
			}
			if(t->kind != Ty_array) {
				EM_error(a->pos, "'%s' was not a array type", S_name(get_arrayexp_typ(a)));
				return expTy(Tr_null(), Ty_Int());
			}
			struct expty size = transExp(tlevel, venv, tenv, get_arrayexp_size(a));	
			struct expty init = transExp(tlevel, venv, tenv, get_arrayexp_init(a));	
			if (size.ty->kind != Ty_int)
				EM_error(a->pos, "array size was not an integer value");
			if (actual_ty(t->u.array) != actual_ty(init.ty))
				EM_error(a->pos, "array init type mismatch");
			return expTy(Tr_arrayExp(size.exp, init.exp), t);
		}
	}
}


struct expty transVar(Tr_level tlevel, S_table venv, S_table tenv, A_var v) {
	switch (v->kind) {
		case A_simpleVar: {
			E_enventry x = S_look(venv, v->u.simple);
			printf("%s\n", S_name(v->u.simple));
			if(x && x->kind == E_varEntry){ 
				Tr_exp tr_exp = Tr_simpleVar(x->u.var.access, tlevel);
				return expTy(tr_exp, actual_ty(x->u.var.ty));
			}
			else{
				EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
				return expTy(Tr_null(), Ty_Int());
			}
		}
		case A_fieldVar: {
			struct expty var = transVar(tlevel, venv, tenv, v->u.field.var);
			if(var.ty->kind != Ty_record){
				EM_error(v->pos, "not a record type");
				return expTy(Tr_null(), Ty_Int());
			}
			Ty_fieldList fields = var.ty->u.record;
			int index = 0;
			while(fields != NULL && fields->head->name != v->u.field.sym){
				fields = fields->tail;
				index++;
			}
			if(!fields){
				EM_error(v->pos,"field %s doesn't exist", S_name(v->u.field.sym));
				return expTy(Tr_null(), Ty_Int());
			}
			//IR
			Tr_exp tr_exp = Tr_fieldVar(var.exp, index);
			return expTy(tr_exp, actual_ty(fields->head->ty));
		}
		case A_subscriptVar: {
			struct expty var = transVar(tlevel, venv, tenv, v->u.subscript.var);
			struct expty exp = transExp(tlevel, venv, tenv, v->u.subscript.exp);
			if(var.ty->kind != Ty_array){
				EM_error(v->pos, "array type required");
				return expTy(Tr_null(), Ty_Int());
			}
			if(exp.ty->kind != Ty_int){
				EM_error(v->pos, "subscriptvar 22");
				return expTy(Tr_null(), Ty_Int());
			}
			//IR
			Tr_exp tr_exp = Tr_subscriptVar(var.exp, exp.exp);
			return expTy(tr_exp, actual_ty(var.ty->u.array));
		}
	}
}

Tr_exp transDec(Tr_level tlevel, S_table venv, S_table tenv, A_dec d) {
	switch (d->kind) {
		case A_varDec: {
			struct expty e = transExp(tlevel, venv, tenv, d->u.var.init);
			Tr_access acc = Tr_allocLocal(tlevel, d->u.var.escape);
			if(d->u.var.typ){
				Ty_ty type = S_look(tenv, d->u.var.typ);
				if(!type){
					EM_error(d->u.var.init->pos, "type not exist %s", S_name(d->u.var.typ));
				}
				if(actual_ty(type) != actual_ty(e.ty)
				 	&& !(actual_ty(type)->kind == Ty_record 
					 		&& actual_ty(e.ty)->kind == Ty_nil)) {
					EM_error(d->u.var.init->pos, "type mismatch");
				}
				S_enter(venv, d->u.var.var, E_VarEntry(acc, type));
			}
			else{
				if(actual_ty(e.ty)->kind == Ty_nil)
					EM_error(d->u.var.init->pos, "init should not be nil without type specified");
				S_enter(venv, d->u.var.var, E_VarEntry(acc, e.ty));
			}
			printf("vardec %s\n",S_name(d->u.var.var));
			return Tr_assignExp(Tr_simpleVar(acc, tlevel), e.exp);
		}

		case A_typeDec: {
			A_nametyList l;
			A_nametyList types 	= d->u.type;
			while(types){	
				if(S_look(tenv, types->head->name));
					// EM_error(d->pos, "two types have the same name");
				else{
					S_enter(tenv, types->head->name, Ty_Name(types->head->name, NULL));
					printf("type dec %s\n",S_name(types->head->name));
				}
				types = types->tail;	
			}
			
			types = d->u.type;
			while(types){	//put binding
				Ty_ty ty = S_look(tenv, types->head->name);
				if(!ty)
					continue;
				ty->u.name.ty = transTy(tenv, types->head->ty);
				types = types->tail;
			}

			types = d->u.type;
			while(types){	//cycle
				Ty_ty ty = S_look(tenv, types->head->name);
				Ty_ty temp = ty->u.name.ty;
				for(; temp->kind == Ty_name && temp; temp = temp->u.name.ty){
					if(temp == ty){
						EM_error(d->pos, "illegal type cycle");
						ty->u.name.ty = Ty_Int();
						break;
					}
				}
				types = types->tail;
			}
			return Tr_null();
		}
		case A_functionDec: {
			A_fundecList fs = d->u.function;
			while(fs){
				if(S_look(venv, fs->head->name)){	//function name
					// EM_error(d->pos,"two functions have the same name");
					fs = fs->tail;
					continue;
				}
				Ty_ty resultTy;
				if(fs->head->result){	//function result
					resultTy = S_look(tenv, fs->head->result);
					if (!resultTy){
						EM_error(fs->head->pos, "undefined result %s", S_name(fs->head->result));
						resultTy = Ty_Int();
					}
				}
				else{
					resultTy = Ty_Void();
				}

				//new level	
				Temp_label fun = Temp_newlabel();
				Tr_level newLevel = Tr_newLevel(tlevel, fun, makeFormalList(fs->head->params));
				Ty_tyList formalTys = makeTyList(tenv, fs->head->params);
				S_enter(venv, fs->head->name, E_FunEntry(newLevel, fun, formalTys, resultTy));
				fs = fs->tail;
			}
			fs = d->u.function;
			while(fs){ //only scan the second time can check the body
				E_enventry entry = S_look(venv, fs->head->name);
				Tr_accessList formals = Tr_formals(entry->u.fun.level)->tail;
				S_beginScope(venv); 
				A_fieldList params = fs->head->params;
				
				//add params 
				for(; params; params = params->tail, formals = formals->tail){
					Ty_ty type = S_look(tenv, params->head->typ);
					S_enter(venv, params->head->name, E_VarEntry(formals->head, type));
					printf("func arg: %s\n",S_name(params->head->name));
				}
				//trans body
				struct expty body = transExp(entry->u.fun.level, venv, tenv, fs->head->body);
				E_enventry x = S_look(venv, fs->head->name);
				if(!body.ty);
				else if(x->u.fun.result->kind == Ty_void && 
					body.ty->kind != Ty_void)
					EM_error(fs->head->pos,"procedure returns value");

				Tr_procEntryExit(entry->u.fun.level, body.exp, formals);
				S_endScope(venv);
				fs = fs->tail;
			}
			return Tr_null();
		}
	}
}

Ty_ty transTy(S_table tenv, A_ty a) {
	switch(a->kind){
	case A_nameTy:{
		Ty_ty ty = S_look(tenv, a->u.name);
		if(!ty){
			EM_error(a->pos,"undefined nameTy %s",S_name(a->u.name));
			return Ty_Int();
		}
		return Ty_Name(a->u.name, ty);
	}
	case A_recordTy:{
		return Ty_Record(makeFieldList(tenv, a->u.record));
	}
	case A_arrayTy:{
		Ty_ty ty = S_look(tenv, a->u.array);
		if(!ty){
			EM_error(a->pos,"undefined arrayTy %s",S_name(a->u.array));
			return Ty_Array(Ty_Int());
		}
		return Ty_Array(S_look(tenv, get_ty_array(a)));
	}
	default:
		return NULL;
	}
}

