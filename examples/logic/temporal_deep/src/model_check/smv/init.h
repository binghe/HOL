#include <stdio.h>
#include <sys/types.h>
#include <sys/times.h>
#include "str.h"
#include "y.tab.h"
#include <setjmp.h>
#ifdef SMV_SIGNALS
#include <signal.h>
#endif
#include <time.h>
#ifndef CLK_TCK
# define CLK_TCK 60
#endif

/* Functions */

void init_eval(void);
void signal_handler(int sig);
void open_input(char *filename);
void close_input(void);
void undefined(node_ptr s);
void redefining(node_ptr s);
void circular(node_ptr s);
void toomanyvars(node_ptr s);
void start_err(void);
void finish_err(void);
int my_setjmp(void);
void cancel_my_setjmp(void);
void my_exit(int n);
void print_usage(void);
void rpterr(const char* format, ...);
void catastrophe(const char* format, ...);
void push_atom(node_ptr s);
void pop_atom(void);
void yyerror(char *s);
int yywrap(void);
void indent(FILE *stream);
void indent_node(FILE *stream, char *s1, node_ptr n, char *s2);
