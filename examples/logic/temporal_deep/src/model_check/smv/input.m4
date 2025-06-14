%{
#include <node.h>
#include <y.tab.h>
%}
%a	15000
%o	25000
%%
[ \n\t]                 ;
"--".*\n                ;
"#".*\n                 sscanf(yytext,"# %d",&yylineno);
"ASYNC"                 return(ASYNC);
"MODULE"                return(MODULE);
"process"               return(PROCESS);
"DEFINE"                return(DEFINE);
"VAR"                   return(VAR);
"CONSTANT"              return(CONSTANT);
"INIT"                  return(INIT);
"TRANS"                 return(TRANS);
"INVAR"                 return(INVAR);
"FORMAT"                return(FORMAT);
"SPEC"                  return(SPEC);
"PRINT"                 return(PRINT);
"hide"                  return(HIDE);
"expose"                return(EXPOSE);
ifdef(`TIMING',
"COMPUTE"               return(COMPUTE);)
"FAIRNESS"              return(FAIRNESS);
"ISA"                   return(ISA);
"ASSIGN"                return(ASSIGN);
"INPUT"                 return(INPUT);
"OUTPUT"                return(OUTPUT);
"IMPLEMENTS"            return(IMPLEMENTS);
"GOTO"                  return(GOTO);
"LET"                   return(LET);
"STEP"                  return(STEP);
"EVAL"                  return(EVAL);
"RESET"                 return(RESET);
"array"                 return(ARRAY);
"of"                    return(OF);
"boolean"               return(BOOLEAN);
"EX"                    return(EX);
"AX"                    return(AX);
"EF"                    return(EF);
"AF"                    return(AF);
"EG"                    return(EG);
"AG"                    return(AG);
"E"                     return(E);
"A"                     return(A);
"U"                     return(UNTIL);
"BU"                    return(BUNTIL);
"EBF"                   return(EBF);
"ABF"                   return(ABF);
"EBG"                   return(EBG);
"ABG"                   return(ABG);
ifdef(`TIMING',
"MIN"                   return(MIN);
"MAX"                   return(MAX);)
"("                     return(LP);
")"                     return(RP);
"["                     return(LB);
"]"                     return(RB);
"{"                     return(LCB);
"}"                     return(RCB);
"FALSE"                 {
				yylval.node = new_node(FALSEEXP,NIL,NIL);
				return(FALSEEXP);
			}
"TRUE"                  {
				yylval.node = new_node(TRUEEXP,NIL,NIL);
				return(TRUEEXP);
			}
"apropos"               return(APROPOS);
"case"                  return(CASE);
"esac"                  return(ESAC);
":="                    return(EQDEF);
"+"                     return(PLUS);
"-"                     return(MINUS);
"*"                     return(TIMES);
"/"                     return(DIVIDE);
"mod"                   return(MOD);
"="                     return(EQUAL);
"!="                    return(NOTEQUAL);
"<="                    return(LE);
">="                    return(GE);
"<"                     return(LT);
">"                     return(GT);
"next"                  return(NEXT);
"init"                  return(SMALLINIT);
"sigma"                 return(SIGMA);
"self"                  return(SELF);
"union"                 return(UNION);
"in"                    return(SETIN);
"notin"                 return(SETNOTIN);
".."                    return(TWODOTS);
"."                     return(DOT);
"->"                    return(IMPLIES);
"<->"                   return(IFF);
"|"                     return(OR);
"&"                     return(AND);
"!"                     return(NOT);
[A-Za-z_][A-Za-z0-9_\$#-]*  { 
                             yylval.node = new_node(ATOM,
                                                     find_string(yytext),NIL);
                             return(ATOM);
                           }
[0-9]+                  {
                          int i;
                          sscanf(yytext,"%d",&i);
                          yylval.node = new_node(NUMBER,i,NIL);
                          return(NUMBER);
                        }
\"[^\"]*\"              {
                          yylval.node = new_node(QUOTE,
                                                  find_string(yytext),NIL);
                             return(QUOTE);
                        }
","                     return(COMMA);
":"                     return(COLON);
";"                     return(SEMI);
.			;/* rpterr("illegal character"); */
%%

