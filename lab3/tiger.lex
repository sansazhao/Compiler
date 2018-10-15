%{
/* Lab2 Attention: You are only allowed to add code in this file and start at Line 26.*/
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "y.tab.h"
#include "errormsg.h"

int charPos=1;

int yywrap(void)
{
 charPos=1;
 return 1;
}

void adjust(void)
{
 EM_tokPos=charPos;
 charPos+=yyleng;
}

/*
* Please don't modify the lines above.
* You can add C declarations of your own below.
*/

#define MAXSIZE  2048
int comment = 0;
int len = 0;
char *str = NULL;
/* @function: getstr
 * @input: a string literal
 * @output: the string value for the input which has all the escape sequences 
 * translated into their meaning.
 */
char *getstr(const char *str)
{
    return NULL;
}

/*  @function:initStr
 *  malloc the space and initialize the variables to get ready to read string
 */
void initStr(){
    str = (char *)malloc(MAXSIZE);
    str[0] = '\0';
    len = 0;
}

/*  @function:endStr
 *  free the space
 */
void endStr(){
    free(str);
    str = NULL;
}
%}
  /* Lex Definitions */

  /* Use COMMENT to handle comments
   * Use STR to handle string 
   */
%Start COMMENT STR 
%%
  /* Regular Expressions and Actions */
<COMMENT>"/*" {adjust();++comment;BEGIN COMMENT;}
<COMMENT>"*/" {
    adjust();
    comment--;
    if(comment == 0)
        BEGIN INITIAL;
    if(comment < 0){
        comment = 0;
        EM_error(EM_tokPos,"error comment");
        BEGIN INITIAL;
    } 
}
<COMMENT>"\n" {adjust();EM_newline();continue;}
<COMMENT>. {adjust();}
<INITIAL>"/*" {adjust();++comment;BEGIN COMMENT;}
<INITIAL>","  {adjust();return COMMA;}
<INITIAL>":"  {adjust();return COLON;}
<INITIAL>";"  {adjust();return SEMICOLON;}
<INITIAL>"("  {adjust();return LPAREN;}
<INITIAL>")"  {adjust();return RPAREN;}
<INITIAL>"["  {adjust();return LBRACK;}
<INITIAL>"]"  {adjust();return RBRACK;}
<INITIAL>"{"  {adjust();return LBRACE;}
<INITIAL>"}"  {adjust();return RBRACE;}
<INITIAL>"."  {adjust();return DOT;}
<INITIAL>"+"  {adjust();return PLUS;}
<INITIAL>"-"  {adjust();return MINUS;}
<INITIAL>"*"  {adjust();return TIMES;}
<INITIAL>"/"  {adjust();return DIVIDE;}
<INITIAL>"="  {adjust();return EQ;}
<INITIAL>"<>" {adjust();return NEQ;}
<INITIAL>"<"  {adjust();return LT;}
<INITIAL>"<=" {adjust();return LE;}
<INITIAL>">"  {adjust();return GT;}
<INITIAL>">=" {adjust();return GE;}
<INITIAL>"&"  {adjust();return AND;}
<INITIAL>"|"  {adjust();return OR;}
<INITIAL>":=" {adjust();return ASSIGN;}
<INITIAL>array {adjust();return ARRAY;}
<INITIAL>if    {adjust();return IF;}
<INITIAL>then  {adjust();return THEN;}
<INITIAL>else  {adjust();return ELSE;}
<INITIAL>while {adjust();return WHILE;}
<INITIAL>for   {adjust();return FOR;}
<INITIAL>to    {adjust();return TO;}
<INITIAL>do    {adjust();return DO;}
<INITIAL>let   {adjust();return LET;}
<INITIAL>in    {adjust();return IN;}
<INITIAL>end   {adjust();return END;}
<INITIAL>of    {adjust();return OF;}
<INITIAL>break {adjust();return BREAK;}
<INITIAL>nil   {adjust();return NIL;}
<INITIAL>function {adjust();return FUNCTION;}
<INITIAL>var    {adjust();return VAR;}
<INITIAL>type   {adjust();return TYPE;}

<INITIAL>[a-zA-Z_][a-zA-Z0-9_]* {adjust();yylval.sval = String(yytext);return ID;}
<INITIAL>[0-9]* {adjust();yylval.ival = atoi(yytext);return INT;}
<INITIAL>"\n" {adjust(); EM_newline(); continue;}
<INITIAL>[\ \t]* {adjust();continue;}
    /* Entry of STR */
<INITIAL>\" {adjust();initStr();BEGIN STR;}
<INITIAL><<EOF>>    {return 0;}
    /* none matches, print error info  */
<INITIAL>. {adjust();EM_error(EM_tokPos, "error initial");}
    /* STR: handle strings */
<STR>\" {
    charPos += yyleng;
    str[len] = '\0';
    yylval.sval = String(str);
    if(len == 0)//return (null)
        yylval.sval = NULL;
    endStr();
    BEGIN INITIAL;
    return STRING;
}
    /* handle \ddd \^C */
<STR>\\[0-9]{1,3}  {charPos += yyleng;str[len++] = atoi(yytext + 1);}
<STR>\\^[A-Z\[\]\^\_\\] {charPos += yyleng;str[len++] = yytext[2] - 'A' + 1;}
    /* handle \n, \t, \\, \, real \n, \", \...\ */
<STR>\\n {charPos += yyleng;str[len++] = '\n';}
<STR>\\t {charPos += yyleng;str[len++] = '\t';}
<STR>\\\\  {charPos += yyleng;str[len++] = '\\';} 
<STR>\\  {charPos += yyleng;str[len++] = '\\';}
<STR>\n {charPos += yyleng;EM_newline();str[len++] = '\n';}
<STR>\\\" {charPos += yyleng;str[len++] = '"';}
<STR>\\[\n \t\f]+\\ {charPos += yyleng;}
<STR>. {charPos += yyleng;str[len++] = yytext[0];}
