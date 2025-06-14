#include <stdio.h>
#include <sys/types.h>
#include <sys/times.h>
#include <storage.h>
#include <string.h>
#include <node.h>
#include <hash.h>
#include <bdd.h>
#include <assoc.h>
#include <y.tab.h>
#include <setjmp.h>
#ifdef SMV_SIGNALS
#include <signal.h>
#endif
#include <time.h>
#ifndef CLK_TCK
# define CLK_TCK 60
#endif

/* Functions */

void init_eval();
void signal_handler();
void open_input();
void close_input();
void undefined();
void redefining();
void circular();
void toomanyvars();
void start_err();
void finish_err();
int my_setjmp();
void cancel_my_setjmp();
void my_exit();
void print_usage();
void rpterr();
void catastrophe();
void push_atom();
void pop_atom();
void yyerror();
int yywrap();
void indent();
void indent_node();
