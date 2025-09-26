#include <stdio.h>

typedef union {
  int inttype;
  struct node *nodetype;
  struct string *strtype;
  struct bdd *bddtype;
} value;

typedef struct node{
  struct node *link;
  short int type,lineno;
  value left,right;
} node_rec,*node_ptr;

#define NIL ((node_ptr)0)
#define FAILURE_NODE ((node_ptr)(-1))
#define ATOM_MAX_LENGTH 256

node_ptr new_node(int type, node_ptr left, node_ptr right);
node_ptr find_node(int type, node_ptr left, node_ptr right);
void init_node(void);
void free_node(node_ptr a);
void print_node(FILE *stream, node_ptr n);
int print_node_atcol(FILE *stream, node_ptr n, int col);
void fprint_node(FILE *ff, node_ptr n);
int sprint_node(char *str, int size, node_ptr n);

node_ptr subst_node(node_ptr n);
node_ptr map(node_ptr (*f)(), node_ptr l);
node_ptr key_node(node_ptr n);
int list_length(node_ptr l);
int member(node_ptr x, node_ptr l);
void free_list(node_ptr a);
node_ptr cons(node_ptr x, node_ptr y);
node_ptr car(node_ptr x);
node_ptr cdr(node_ptr x);
node_ptr append(node_ptr x, node_ptr y);
node_ptr reverse(node_ptr x);
node_ptr list_minus(node_ptr l1, node_ptr l2);
node_ptr unify_node(node_ptr n1, node_ptr n2, node_ptr sl);

void walk(void (*f)(), node_ptr l);
