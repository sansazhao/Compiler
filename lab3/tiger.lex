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
int len, total;
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
    total = MAXSIZE;
    str[0] = '\0';
    len = 0;
}

void add(char c){
    if (len + 1 == total) {
        str = realloc(str, total + MAXSIZE);
        if (!str) {
            printf("Add:remalloc error!\n");
            exit(1);
        }
        total += MAXSIZE;
    }
    str[len++] = c;
    str[len] = '\0';

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
<COMMENT>{
    "/*" {adjust();++comment;BEGIN COMMENT;}
    "*/" {
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
    "\n" {adjust();EM_newline();continue;}
    . {adjust();}
}

<INITIAL>{
    "/*" {adjust();++comment;BEGIN COMMENT;}
    ","  {adjust();return COMMA;}
    ":"  {adjust();return COLON;}
    ";"  {adjust();return SEMICOLON;}
    "("  {adjust();return LPAREN;}
    ")"  {adjust();return RPAREN;}
    "["  {adjust();return LBRACK;}
    "]"  {adjust();return RBRACK;}
    "{"  {adjust();return LBRACE;}
    "}"  {adjust();return RBRACE;}
    "."  {adjust();return DOT;}
    "+"  {adjust();return PLUS;}
    "-"  {adjust();return MINUS;}
    "*"  {adjust();return TIMES;}
    "/"  {adjust();return DIVIDE;}
    "="  {adjust();return EQ;}
    "<>" {adjust();return NEQ;}
    "<"  {adjust();return LT;}
    "<=" {adjust();return LE;}
    ">"  {adjust();return GT;}
    ">=" {adjust();return GE;}
    "&"  {adjust();return AND;}
    "|"  {adjust();return OR;}
    ":=" {adjust();return ASSIGN;}
    array {adjust();return ARRAY;}
    if    {adjust();return IF;}
    then  {adjust();return THEN;}
    else  {adjust();return ELSE;}
    while {adjust();return WHILE;}
    for   {adjust();return FOR;}
    to    {adjust();return TO;}
    do    {adjust();return DO;}
    let   {adjust();return LET;}
    in    {adjust();return IN;}
    end   {adjust();return END;}
    of    {adjust();return OF;}
    break {adjust();return BREAK;}
    nil   {adjust();return NIL;}
    function {adjust();return FUNCTION;}
    var    {adjust();return VAR;}
    type   {adjust();return TYPE;}

    [a-zA-Z_][a-zA-Z0-9_]* {adjust();yylval.sval = String(yytext);return ID;}
    [0-9]*  {adjust();yylval.ival = atoi(yytext);return INT;}
    "\n"    {adjust(); EM_newline(); continue;}
    [\ \t]* {adjust(); continue;}

    \"        {adjust();initStr();BEGIN STR;}
    <<EOF>>   {return 0;}
    .         {adjust();EM_error(EM_tokPos, "error initial");}
}

    /* STR: handle strings */
<STR>{
    \" {
        charPos += yyleng;
        str[len] = '\0';
        yylval.sval = String(str);
        if(len == 0)//return (null)
            yylval.sval = "";
        endStr();
        BEGIN INITIAL;
        return STRING;
    }
        /* handle \ddd \^C */
    \\[0-9]{1,3}       {charPos += yyleng, add(atoi(yytext + 1));}
    \\^[A-Z\[\]\^\_\\] {charPos += yyleng, add(yytext[2] - 'A' + 1);}
        /* handle \n, \t, \\, \, real \n, \", \...\ */
    \\n   {charPos += yyleng, add('\n');}
    \\t   {charPos += yyleng, add('\t');}
    \\\\  {charPos += yyleng, add('\\');} 
    \\    {charPos += yyleng, add('\\');}
    \n    {charPos += yyleng;EM_newline(), add('\n');}
    \\\"  {charPos += yyleng, add('"');}
    \\[\n \t\f]+\\ {charPos += yyleng;}
    .     {charPos += yyleng, add(yytext[0]);}
}