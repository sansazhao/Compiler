#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "env.h"
#include "semant.h"
#include "helper.h"
#include "translate.h"

/*Lab5: Your implementation of lab5.*/

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

Ty_ty actual_ty(Ty_ty ty){
	while(ty && ty->kind == Ty_name)
		ty = ty->u.name.ty;
	return ty;
}

struct expty transExp (S_table venv, S_table tenv, A_exp a, Tr_level l, Temp_label breakLabel){
    switch (a->kind) {
		case A_opExp:{
			A_oper oper = a->u.op.oper;
			struct expty left = transExp(venv, tenv, a->u.op.left, l, breakLabel);
			struct expty right = transExp(venv, tenv, a->u.op.right, l ,breakLabel);
			if(oper == A_plusOp || oper == A_minusOp 
			|| oper == A_timesOp || oper == A_divideOp) {
				if(actual_ty(left.ty)->kind != Ty_int){
					EM_error(a->u.op.left->pos, "integer required");
					return expTy(NULL, Ty_Int());
				}
				if(actual_ty(right.ty)->kind != Ty_int){
					EM_error(a->u.op.right->pos, "integer required");
					return expTy(NULL, Ty_Int());
				}
				//IR
				return expTy(Tr_arithExp(oper, left.exp, right.exp), Ty_Int());
			}
			else{//eq neq lt le gt ge
				if(actual_ty(left.ty) != actual_ty(right.ty)){
					EM_error(a->pos, "same type required");
					return expTy(NULL, Ty_Int());
				}
				//IR
				return expTy(Tr_relExp(oper, left.exp, right.exp), Ty_Int());
			}
		}
		case A_letExp:{
			printf("let\n");
			S_beginScope(venv);
			S_beginScope(tenv);
			struct expty exp;
			A_decList d;
			for(d = a->u.let.decs; d; d = d->tail)
				transDec(venv, tenv, d->head, l, breakLabel);
			exp = transExp(venv, tenv, a->u.let.body, l, breakLabel);
			S_endScope(tenv);  
			S_endScope(venv);
			return exp;	
    	}
		case A_varExp:
			return transVar(venv, tenv, a->u.var, l, breakLabel);
		case A_nilExp:
			return expTy(Tr_nil(), Ty_Nil());
		case A_intExp:
			return expTy(Tr_int(a->u.intt), Ty_Int());
		case A_stringExp:
			return expTy(Tr_string(a->u.stringg), Ty_String());
		case A_breakExp:
			return expTy(Tr_breakExp(breakLabel), Ty_Void());
		case A_callExp:{
			E_enventry x = S_look(venv, a->u.call.func);
			if(x && x->kind == E_funEntry){   //check formals
				Ty_tyList expect = x->u.fun.formals;
				A_expList actual = a->u.call.args;
				Tr_expList list = Tr_ExpList(NULL, NULL), t = list;
				while(expect && actual){
					struct expty exp_arg = transExp(venv, tenv, actual->head, l, breakLabel);
					if(actual_ty(exp_arg.ty)->kind != actual_ty(expect->head)->kind)
						EM_error(actual->head->pos, "para type mismatch");
					expect = expect->tail;
					actual = actual->tail;
					t->tail = Tr_ExpList(exp_arg.exp, NULL);
					t = t->tail;
				}
				if(expect || actual)
					EM_error(actual->head->pos, "too many params in function %s", S_name(a->u.call.func));
				//fun args caller callee
				Tr_exp tr_exp = Tr_callExp(x->u.fun.label, list->tail, x->u.fun.level, l);
				return expTy(tr_exp, actual_ty(x->u.fun.result));
			}
			else{
				EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
				return expTy(NULL, Ty_Int());
			}
		}
		case A_recordExp:{
			printf("record\n");
			Ty_ty ty = S_look(tenv, a->u.record.typ);
			ty = actual_ty(ty);
			if(!ty){
				EM_error(a->pos, "undefined type %s", S_name(a->u.record.typ));
				return expTy(NULL, Ty_Int());
			}
			if(ty->kind != Ty_record)
				EM_error(a->pos, "not record  %s", S_name(a->u.record.typ));
			A_efieldList actual = a->u.record.fields;
			Ty_fieldList expect = ty->u.record;
			Tr_expList fields = Tr_ExpList(NULL, NULL), t = fields;
			while(actual && expect){
				if(actual->head->name != expect->head->name)
					EM_error(a->pos, "record name doesn't exist %s", S_name(a->u.record.typ));
				struct expty exp_rec = transExp(venv, tenv, actual->head->exp, l ,breakLabel);
				if(actual_ty(exp_rec.ty) != actual_ty(expect->head->ty))
					EM_error(a->pos, "para type mismatch");
				expect = expect->tail;
				actual = actual->tail;
				t->tail = Tr_ExpList(exp_rec.exp, NULL);
				t = t->tail;
			}
			if(expect || actual)
				EM_error(a->pos, "less or more field %s", S_name(a->u.record.typ));
			return expTy(Tr_recordExp(fields->tail), ty);
		}
		case A_arrayExp:{
			// printf("arrayExp\n");
			Ty_ty ty = S_look(tenv, a->u.array.typ);
			ty = actual_ty(ty);
			if(!ty)
				EM_error(a->pos, "undefined array  %s", S_name(a->u.array.typ));
			if(ty->kind != Ty_array)
				EM_error(a->pos, "not array  %s", S_name(a->u.array.typ));
			struct expty size = transExp(venv, tenv, a->u.array.size, l, breakLabel);
			if(actual_ty(size.ty)->kind != Ty_int)
				EM_error(a->pos, "size of array should be int %s", S_name(a->u.array.typ));
			struct expty init = transExp(venv, tenv, a->u.array.init, l, breakLabel);
			if(actual_ty(init.ty) != actual_ty(ty->u.array))
				EM_error(a->pos, "type mismatch");
			return expTy(Tr_arrayExp(size.exp, init.exp), ty);
		}
		case A_seqExp:{
			// printf("seqExp\n");
			A_expList seq = a->u.seq;
			struct expty ty;
			Tr_exp eseq = Tr_nil();
			Ty_ty type = Ty_Void();
			while(seq){
				// printf("seqExp1\n");
				ty = transExp(venv, tenv, seq->head, l, breakLabel);
				// printf("seqExp2\n");
				eseq = Tr_eseq(eseq, ty.exp);
				type = ty.ty;
				seq = seq->tail;
				// printf("seqExp3\n");
			}
			return expTy(eseq, type);
		}
		case A_assignExp:{
			// printf("assignExp");
			if(a->u.assign.var->kind == A_simpleVar){
				E_enventry x = S_look(venv, a->u.assign.var->u.simple);
				if(x && x->readonly == 1)
					EM_error(a->pos, "loop variable can't be assigned");
			}
			struct expty var = transVar(venv, tenv, a->u.assign.var, l, breakLabel);
			struct expty exp = transExp(venv, tenv, a->u.assign.exp, l, breakLabel);
			if(actual_ty(var.ty) != actual_ty(exp.ty))
				EM_error(a->pos, "unmatched assign exp");
			return expTy(Tr_assignExp(var.exp, exp.exp), Ty_Void());
		}
		case A_ifExp:{
			struct expty test = transExp(venv, tenv, a->u.iff.test, l, breakLabel);
			// if(actual_ty(test.ty)->kind != Ty_int)
			// 	EM_error(a->pos, "");
			struct expty then = transExp(venv, tenv, a->u.iff.then, l, breakLabel);
			if(actual_ty(then.ty)->kind != Ty_void)
				EM_error(a->pos, "if-then exp's body must produce no value");
			struct expty elsee;
			if(a->u.iff.elsee){
				elsee = transExp(venv, tenv, a->u.iff.elsee, l, breakLabel);
				if(actual_ty(then.ty) != actual_ty(elsee.ty))
					EM_error(a->u.iff.then->pos, "then exp and else exp type mismatch");
			}
			return expTy(Tr_ifExp(test.exp, then.exp, elsee.exp), then.ty);
		}
		case A_forExp:{
			struct expty lo = transExp(venv, tenv, a->u.forr.lo, l, breakLabel);
			struct expty hi = transExp(venv, tenv, a->u.forr.hi, l, breakLabel);
			if(actual_ty(lo.ty)->kind != Ty_int)
				EM_error(a->pos, "for exp's range type is not integer");
			if(actual_ty(hi.ty)->kind != Ty_int)
				EM_error(a->pos, "for exp's range type is not integer");
			S_beginScope(venv);
			Tr_access acc = Tr_allocLocal(l, a->u.forr.escape);
			S_enter(venv, a->u.forr.var, E_ROVarEntry(acc, Ty_Int()));
			struct expty body = transExp(venv, tenv, a->u.forr.body, l, breakLabel);
			S_endScope(venv);
			if(actual_ty(body.ty)->kind != Ty_void)
				EM_error(a->pos, "the body of for should be void ");
			Temp_label done = Temp_newlabel();
			return expTy(Tr_forExp(l, acc, lo.exp, hi.exp, body.exp, done), Ty_Void());
		}
		case A_whileExp:{
			struct expty test = transExp(venv, tenv, a->u.whilee.test, l, breakLabel);
			if(actual_ty(test.ty)->kind != Ty_int)
				EM_error(a->pos, "test part of while should be int");
			struct expty body = transExp(venv, tenv, a->u.whilee.body, l, breakLabel);
			if(actual_ty(body.ty)->kind != Ty_void)
				EM_error(a->pos, "while body must produce no value");
			
			Temp_label done = Temp_newlabel();
			return expTy(Tr_whileExp(test.exp, body.exp, done), Ty_Void());
		}
		default:
			assert(0); 
			break;
	}
}

struct expty transVar (S_table venv, S_table tenv, A_var v, Tr_level l, Temp_label breakLabel){
    switch (v->kind) {
		case A_simpleVar:{
			E_enventry x = S_look(venv, v->u.simple);
			if(x && x->kind == E_varEntry){ 
				//IR
				Tr_exp tr_exp = Tr_simpleVar(x->u.var.access, l);
				return expTy(tr_exp, actual_ty(x->u.var.ty));
			}
			else{
				EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
				return expTy(NULL, Ty_Int());
			}
		}
		case A_fieldVar:{//record a:b
			struct expty var = transVar(venv, tenv, v->u.field.var, l, breakLabel);
			if(var.ty->kind != Ty_record){
				EM_error(v->pos, "not a record type");
				return expTy(NULL, Ty_Int());
			}
			Ty_fieldList fields = var.ty->u.record;
			int index = 0;
			while(fields != NULL && fields->head->name != v->u.field.sym){
				fields = fields->tail;
				index++;
			}
			if(!fields){
				EM_error(v->pos,"field %s doesn't exist", S_name(v->u.field.sym));
				return expTy(NULL, Ty_Int());
			}
			//IR
			Tr_exp tr_exp = Tr_fieldVar(var.exp, index);
			return expTy(tr_exp, actual_ty(fields->head->ty));
		}
		case A_subscriptVar:{//array a,b,c
			struct expty var = transVar(venv, tenv, v->u.subscript.var, l, breakLabel);
			struct expty exp = transExp(venv, tenv, v->u.subscript.exp, l, breakLabel);
			if(var.ty->kind != Ty_array){
				EM_error(v->pos, "array type required");
				return expTy(NULL, Ty_Int());
			}
			if(exp.ty->kind != Ty_int){
				EM_error(v->pos, "subscriptvar 22");
				return expTy(NULL, Ty_Int());
			}
			//IR
			Tr_exp tr_exp = Tr_subscriptVar(var.exp, exp.exp);
			return expTy(tr_exp, actual_ty(var.ty->u.array));

		}
		default:
			break;
	}
}

Ty_tyList makeFormalTyList(S_table tenv, A_fieldList fields){
	if(!fields)
		return NULL;
	Ty_ty ty = 	S_look(tenv, fields->head->typ);
	return Ty_TyList(ty, makeFormalTyList(tenv, fields->tail));
}

U_boolList makeFormalList(A_fieldList params) {
    if (!params) {
        return NULL;
    }
    return U_BoolList(params->head->escape, makeFormalList(params->tail));
}

Tr_exp transDec (S_table venv, S_table tenv, A_dec d, Tr_level l, Temp_label breakLabel){
    switch(d->kind){
		case A_varDec:{
			struct expty e = transExp(venv, tenv, d->u.var.init, l, breakLabel);
			Tr_access acc = Tr_allocLocal(l, d->u.var.escape);
			if(d->u.var.typ){
				Ty_ty type = S_look(tenv, d->u.var.typ);
				if(!type){
					EM_error(d->u.var.init->pos, "type not exist %s", S_name(d->u.var.typ));
				}
				if(actual_ty(type) != actual_ty(e.ty)) {
					EM_error(d->u.var.init->pos, "type mismatch");
				}
				// printf("var dec1 %s\n",S_name(d->u.var.var));
				S_enter(venv, d->u.var.var, E_VarEntry(acc, type));
			}
			else{
				if (actual_ty(e.ty)->kind == Ty_nil)
					EM_error(d->u.var.init->pos, "init should not be nil without type specified");
				// printf("var dec2 %s\n",S_name(d->u.var.var));
				S_enter(venv, d->u.var.var, E_VarEntry(acc, e.ty));
				// printf("vardec 1\n");
			}
			return Tr_assignExp(Tr_simpleVar(acc, l), e.exp);
		}
		case A_typeDec:{
			// printf("type dec\n");
			A_nametyList types 	= d->u.type;
			while(types){	
				if(S_look(tenv, types->head->name)){
					EM_error(d->pos, "two types have the same name");
				}
				else{
					S_enter(tenv, types->head->name, Ty_Name(types->head->name, NULL));
					// printf("type dec %s\n",S_name(types->head->name));
				}
				types = types->tail;	
			}

			// // add type declarations to table
            // types = d->u.type;
            // while (types) {
            //     S_enter(tenv, types->head->name, Ty_Name(types->head->name, NULL));
            //     types = types->tail;
            // }
			
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
				for(; temp->kind == Ty_name && temp->u.name.ty; temp = temp->u.name.ty){
					if(temp == ty){
						EM_error(d->pos, "illegal type cycle");
						ty->u.name.ty = Ty_Int();
						break;
					}
				}
				types = types->tail;
			}
			return Tr_nil();
		}

		/* 调用Tr newlevel为每个函数创建新的嵌套层，trnewlevel 调用fnewframe建立新栈帧
		 * semant将这个嵌套层保护在该函数的FunEntry中，被调用时返回给translate
		 */
		case A_functionDec:{
			A_fundecList fs = d->u.function;
			while(fs){
				if(S_look(venv, fs->head->name)){
					EM_error(d->pos,"two functions have the same name");
					fs = fs->tail;
					continue;
				}
				Ty_ty resultTy;
				if(fs->head->result){
					resultTy = S_look(tenv, fs->head->result);
					if (!resultTy){
						EM_error(fs->head->pos, "undefined result %s", S_name(fs->head->result));
						resultTy = Ty_Void();
					}
				}
				else{
					resultTy = Ty_Void();
				}

				//new level	
				Temp_label fun = Temp_newlabel();
				Tr_level newLevel = Tr_newLevel(l, fun, makeFormalList(fs->head->params));
				Ty_tyList formalTys = makeFormalTyList(tenv, fs->head->params);
				S_enter(venv, fs->head->name, E_FunEntry(newLevel, fun, formalTys, resultTy));
				fs = fs->tail;
			}
			fs = d->u.function;
			while(fs){ //only scan the second time can check the body
				E_enventry entry = S_look(venv, fs->head->name);
				Tr_accessList formals = Tr_formals(entry->u.fun.level);
				S_beginScope(venv); 
				// Ty_tyList formalTys = makeFormalTyList(tenv, fs->head->params);
				A_fieldList params = fs->head->params;
				
				//add params 
				for(; params; params = params->tail, formals = formals->tail){
					Ty_ty type = S_look(tenv, params->head->typ);
					S_enter(venv, params->head->name, E_VarEntry(formals->head, type));
				}
				//trans body
				struct expty body = transExp(venv, tenv, fs->head->body, l, breakLabel);
				E_enventry x = S_look(venv, fs->head->name);
				if(actual_ty(x->u.fun.result)->kind == Ty_void && 
					actual_ty(body.ty)->kind != Ty_void)
					EM_error(fs->head->pos,"procedure returns value");
				S_endScope(venv);

				Tr_procEntryExit(entry->u.fun.level, body.exp, formals);
				
				fs = fs->tail;
			}
			return Tr_nil();
		}
		default:
			break;
    }
}

Ty_fieldList makeFieldList(S_table tenv, A_fieldList fields){
	A_field field = fields->head;
	Ty_ty ty = S_look(tenv, field->typ);
	if(!ty)
		EM_error(field->pos,"undefined type %s",S_name(field->typ));
	Ty_field head = Ty_Field(field->name, ty);
	if(fields->tail)
		return Ty_FieldList(head, makeFieldList(tenv, fields->tail));
	else
		return Ty_FieldList(head, NULL);
}

Ty_ty transTy(S_table tenv, A_ty a){
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
				return Ty_Int();
			}
			return Ty_Array(ty);
		}
		default:
			return NULL;
	}
}

F_fragList SEM_transProg(A_exp exp){
	//TODO LAB5: do not forget to add the main frame
	Temp_label main = Temp_newlabel();
	Tr_level mainLevel = Tr_newLevel(Tr_outermost(), main, NULL);
	E_enventry entry = E_FunEntry(mainLevel, main, NULL, Ty_Void());
	struct expty body = transExp(E_base_venv(), E_base_tenv(), exp, mainLevel, NULL);
	Tr_procEntryExit(entry->u.fun.level, body.exp, NULL);
	return Tr_getResult();
}

