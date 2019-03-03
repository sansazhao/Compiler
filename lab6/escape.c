#include <stdio.h>
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "escape.h"
#include "table.h"


static void traverseExp(S_table env, int depth, A_exp e);
static void traverseDec(S_table env, int depth, A_dec d);
static void traverseVar(S_table env, int depth, A_var v);

void Esc_findEscape(A_exp exp) {
	S_table env = S_empty();
	traverseExp(env, 0, exp);
}

static escapeEntry EscapeEntry(int depth, bool *escape){
	escapeEntry ee = checked_malloc(sizeof(*ee));
	ee->depth = depth;
	ee->escape = escape;
	return ee;
}

static void traverseExp(S_table env, int depth, A_exp e){
	switch(e->kind){
		case A_varExp:
			traverseVar(env, depth, e->u.var);
			return;
		case A_callExp:{
			A_expList el = e->u.call.args;
			for(; el; el = el->tail)
				traverseExp(env, depth, el->head);
			return;
		}
		case A_opExp:
			traverseExp(env, depth, e->u.op.left);
			traverseExp(env, depth, e->u.op.right);
			return;
		case A_recordExp:{
			A_efieldList efl = e->u.record.fields;
			for (; efl; efl = efl->tail)
				traverseExp(env, depth, efl->head->exp);
			return;
		}
		case A_seqExp:{
			A_expList el = e->u.seq;
			for (; el; el = el->tail)
				traverseExp(env, depth, el->head);
			return;
		}
		case A_assignExp:
			traverseVar(env, depth, e->u.assign.var);
			traverseExp(env, depth, e->u.assign.exp);
			return;
		case A_ifExp:
			traverseExp(env, depth, e->u.iff.test);
			traverseExp(env, depth, e->u.iff.then);
			if (e->u.iff.elsee) 
				traverseExp(env, depth, e->u.iff.elsee);
			return;
		case A_whileExp:
			traverseExp(env, depth, e->u.whilee.test);
			traverseExp(env, depth, e->u.whilee.body);
			return;
		case A_forExp:{
			e->u.forr.escape = FALSE;
			S_enter(env, e->u.forr.var, EscapeEntry(depth, &(e->u.forr.escape)));
			traverseExp(env, depth, e->u.forr.lo);
			traverseExp(env, depth, e->u.forr.hi);
			S_beginScope(env);
			traverseExp(env, depth, e->u.forr.body);
			S_endScope(env);
			return;
		}
		case A_letExp:{
			S_beginScope(env);
			A_decList lt = e->u.let.decs;
			for (; lt; lt = lt->tail)
				traverseDec(env, depth, lt->head);
			traverseExp(env, depth, e->u.let.body);
			S_endScope(env);
			return;
		}
		case A_arrayExp:
			traverseExp(env, depth, e->u.array.size);
			traverseExp(env, depth, e->u.array.init);
			return;
		default:
			return;
	}
}

static void traverseDec(S_table env, int depth, A_dec d){
	switch(d->kind){
		case A_varDec:
			traverseExp(env, depth, d->u.var.init);
			d->u.var.escape = FALSE;
			S_enter(env, d->u.var.var, EscapeEntry(depth, &(d->u.var.escape)));
			return;
		case A_typeDec:
			return;
		case A_functionDec:{
			A_fundecList fl = d->u.function;
			for(; fl; fl = fl->tail){
				A_fundec fun = fl->head;
				A_fieldList params = fun->params;
				S_beginScope(env);
				for (; params; params = params->tail){
					params->head->escape = FALSE;
					S_enter(env, params->head->name, EscapeEntry(depth+1, &(params->head->escape)));
				}
				traverseExp(env, depth+1, fun->body);
				S_endScope(env);
			}
			return;
		}
	}
	return;
}

static void traverseVar(S_table env, int depth, A_var v){
	switch(v->kind){
		case A_simpleVar: {
			escapeEntry entry = S_look(env, v->u.simple);
			if (entry->depth < depth)	
				*(entry->escape) = TRUE;
			return;
		}
		case A_fieldVar:
			traverseVar(env, depth, v->u.field.var);
			return;
		case A_subscriptVar:
			traverseVar(env, depth, v->u.subscript.var);
			traverseExp(env, depth, v->u.subscript.exp);
			return;
	}
	assert(0);
}
