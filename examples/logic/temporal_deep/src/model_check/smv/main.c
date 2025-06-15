#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "storage.h"
#include "hash.h"
#include "node.h"
#include "symbols.h"
#include "assoc.h"
#include "init.h"

int yyparse (void);

/* Global variables */

extern int KEYTABLESIZE, APPLY_CACHE_SIZE, MINI_CACHE_SIZE;

extern int heuristics,verbose,option_print_reachable,
  option_forward_search,option_round_robin,
  option_incremental,option_restrict_trans, option_interactive,
  option_AG_only, option_conj_part, option_changes_only;
extern int option_print_node_length;
extern int option_print_width;
extern int interactive_mode;
extern int conj_part_limit;
extern double fudge_factor;
extern char *output_order_file,*input_order_file;
extern char *input_file;
extern char *myname;
extern hash_ptr seq_hash;
extern char* addrstart;
extern char *option_dump_reachable;

extern node_ptr parse_tree;
#ifdef REORDER
extern int reorder;
extern int reorder_bits;
extern int reorder_size;
extern int reorder_maxsize;
extern int reorder_minsize;
extern float reorder_factor;
#endif
#ifdef OTHER_SIMP
extern int option_othersimp;
extern int option_gc_factor;
extern int option_gc_limit;
extern int option_early;
extern int option_checktrans;
extern int option_drip;
extern int option_output_often;
#endif

#ifdef SMV_SIGNALS
/* Quit after outputting the order file with -quit option (default),
   but don't quit with -noquit. */
extern int option_quit;
/* Whether to write a pid file */
extern int option_pid;
#endif

extern node_ptr atom_stack;

extern jmp_buf longjmp_buf;
extern int longjmp_on_err;

#ifdef SERGEYDEBUG
extern unsigned apply_cache_access_count;
extern unsigned apply_cache_hit_count;
#endif

extern int option_final_reorder;
extern int indent_size;

/* The main function - the only function in this file */

int main(argc,argv)
int argc;
char **argv;
{
  extern int yylineno;
#ifdef SMV_SIGNALS
  int i;

  /* Catch all the signals we can catch, except for segfaults.
     Core dumps are useful for debugging. 
     Also, stopping and resuming seems like a good idea. */
  for(i = 0 ; i < 32 ; i++)
    if((i != SIGSEGV) && (i != SIGCONT) && (i != SIGTSTP))
      signal(i, signal_handler);
#endif
  init_storage();
  addrstart = (char *) sbrk(0);
  argc--;
  myname = *(argv++);
  while(argc){
    if(argc == 1 && (**argv) != '-'){
      open_input(*(argv++));
      argc--;
      continue;
    }
    if(strcmp(*argv,"-rr")==0){
      argv++;
      argc--;
      option_round_robin = 1;
      continue;
    }
    if(strcmp(*argv,"-nopid")==0){
      argv++;
      argc--;
      option_pid = 0;
      continue;
    }
    if(strcmp(*argv,"-r")==0){
      argv++;
      argc--;
      option_print_reachable = 1;
      continue;
    }
    if(strcmp(*argv,"-f")==0){ /* This is the default now */
      argv++;
      argc--;
      option_forward_search = 1;
      continue;
    }
    if(strcmp(*argv,"-nof")==0){
      argv++;
      argc--;
      option_forward_search = 0;
      continue;
    }
    if(strcmp(*argv,"-inc")==0){
      argv++;
      argc--;
      option_incremental = 1;
      continue;
    }
    if(strcmp(*argv,"-int")==0){
      argv++;
      argc--;
      option_interactive = 1;
      setlinebuf(stdout);
      continue;
    }
    if(strcmp(*argv,"-AG")==0){
      argv++;
      argc--;
      option_AG_only = 1;
      continue;
    }
    if(strcmp(*argv,"-h")==0){
      heuristics = 1;
      argv++;
      argc--;
      continue;
    }
#ifdef REORDER
    if(strcmp(*argv, "-reorder") == 0) {
      argv++;
      argc--;
      reorder = 1;
      option_quit = 0;
      continue;
    }
#endif
#ifdef OTHER_SIMP
    if(strcmp(*argv, "-early") == 0) {
      argv++;
      argc--;
      option_early = 1;
      continue;
    }
    if(strcmp(*argv, "-noearly") == 0) {
      argv++;
      argc--;
      option_early = 0;
      continue;
    }
    if(strcmp(*argv, "-final-reorder") == 0) {
      argv++;
      argc--;
      option_final_reorder = 1;
      continue;
    }
    if(strcmp(*argv, "-no-final-reorder") == 0) {
      argv++;
      argc--;
      option_final_reorder = 0;
      continue;
    }
    if(strcmp(*argv, "-checktrans") == 0) {
      argv++;
      argc--;
      option_checktrans = 1;
      continue;
    }
    if(strcmp(*argv, "-nochecktrans") == 0) {
      argv++;
      argc--;
      option_checktrans = 0;
      continue;
    }
    if(strcmp(*argv, "-drip") == 0) {
      argv++;
      argc--;
      option_drip = 1;
      continue;
    }
    if(strcmp(*argv, "-l") == 0 || strcmp(*argv, "-long") == 0) { 
      argv++;
      argc--;
      option_changes_only = 0;
      continue;
    }
#endif /* OTHER_SIMP */
#ifdef VERSION
    if(strcmp(*argv, "-version") == 0) {
      argv++;
      argc--;
      printf(VERSION);printf("\n");
      return(0);
    }
#endif
#ifdef SMV_SIGNALS
    if(strcmp(*argv, "-quit") == 0) {
      argv++;
      argc--;
      option_quit = 1;
      continue;
    }
    if(strcmp(*argv, "-noquit") == 0) {
      argv++;
      argc--;
      option_quit = 0;
      continue;
    }
#endif
    if(argc<2)rpterr("command line error");
    if(strcmp(*argv,"-v")==0){
      argv++;
      sscanf(*(argv++),"%d",&verbose);
      setlinebuf(stdout);
    }
#ifdef OTHER_SIMP
    else if((strcmp(*argv, "-simp") == 0)
	    || (strcmp(*argv, "-othersimp") == 0)) {
      argv++;
      sscanf(*(argv++),"%d",&option_othersimp);
      if(option_othersimp < 0 || option_othersimp > 2) {
	fprintf(stderr,"Error: -othersimp %d: must be 0, 1 or 2\n", option_othersimp);
	exit(1);
      }
    }
    else if(strcmp(*argv, "-gcfactor") == 0) {
      argv++;
      sscanf(*(argv++),"%d",&option_gc_factor);
    }
    else if(strcmp(*argv, "-gclimit") == 0) {
      argv++;
      sscanf(*(argv++),"%d",&option_gc_limit);
    }
    else if(strcmp(*argv,"-oo")==0){
      argv++;
      output_order_file = *(argv++);
      option_output_often = 1;
    }
#endif
    else if(strcmp(*argv,"-i")==0){
      argv++;
      input_order_file = *(argv++);
    }
    else if(strcmp(*argv,"-o")==0){
      argv++;
      output_order_file = *(argv++);
    }
    else if(strcmp(*argv,"-dumpspace")==0){
      argv++;
      option_dump_reachable = *(argv++);
    }
    else if(strcmp(*argv,"-cols")==0){
      argv++;
      sscanf(*(argv++),"%d",&option_print_node_length);
    }
    else if(strcmp(*argv,"-width")==0){
      argv++;
      sscanf(*(argv++),"%d",&option_print_width);
    }
    else if(strcmp(*argv,"-k")==0){
      argv++;
      sscanf(*(argv++),"%d",&KEYTABLESIZE);
    }
    else if(strcmp(*argv,"-c")==0){
      argv++;
      sscanf(*(argv++),"%d",&APPLY_CACHE_SIZE);
    }
    else if(strcmp(*argv,"-m")==0){
      argv++;
      sscanf(*(argv++),"%d",&MINI_CACHE_SIZE);
    }
    else if(strcmp(*argv,"-cp")==0){
      argv++;
      sscanf(*(argv++),"%d",&conj_part_limit);
      option_conj_part = 1;
    }
#ifdef REORDER
    else if(strcmp(*argv, "-reorderbits") == 0) {
      argv++;
      sscanf(*(argv++),"%d",&reorder_bits);
      reorder_bits *= 2;
    }
    else if(strcmp(*argv, "-reordersize") == 0) {
      argv++;
      sscanf(*(argv++),"%d",&reorder_size);
    }
    else if(strcmp(*argv, "-reordermaxsize") == 0) {
      argv++;
      sscanf(*(argv++),"%d",&reorder_maxsize);
    }
    else if(strcmp(*argv, "-reorderminsize") == 0) {
      argv++;
      sscanf(*(argv++),"%d",&reorder_minsize);
    }
    else if(strcmp(*argv, "-reorderfactor") == 0) {
      argv++;
      sscanf(*(argv++),"%f",&reorder_factor);
    }
#endif
    else rpterr("undefined: %s",*argv);
    argc -= 2;
  }
#ifdef OTHER_SIMP
  /* Compute the actual amount of memory left for bdds */
  option_gc_limit -= (KEYTABLESIZE*sizeof(bdd_ptr)
		      + APPLY_CACHE_SIZE*sizeof(apply_rec))/(1024*1024);
#endif
#ifdef SMV_SIGNALS
  if(option_pid){ 
    FILE *ff = fopen(".smv-pid","w");
    if(ff != NULL) {
      fprintf(ff,"%d",getpid());
      fclose(ff);
    }
#endif
  }
  if(verbose){
    fprintf(stderr,"Key table size: %d\n",KEYTABLESIZE);
    fprintf(stderr,"Apply cache size: %d\n",APPLY_CACHE_SIZE);
    fprintf(stderr,"Variable ordering heuristics: ");
    if(heuristics)fprintf(stderr,"ON, factor = %g\n",fudge_factor);
    else fprintf(stderr,"OFF\n");
#ifdef OTHER_SIMP
    fprintf(stderr,"GC factor: %d, memory limit (adjusted): %dMB (%d BDD nodes)\n",
	    option_gc_factor,option_gc_limit,option_gc_limit*BDDS_IN_MB);
    fprintf(stderr,"Reordering: ");
    if(reorder) fprintf(stderr,"ON, "); else fprintf(stderr,"OFF, "); 
    fprintf(stderr,"Factor: %f\n",reorder_factor);
    if(option_early && option_AG_only && option_forward_search)
      fprintf(stderr,"Using early evaluation of AG specs\n");
    fprintf(stderr,"Simplification algorithm: ");
    if(option_othersimp==0)fprintf(stderr,"memory efficient (0)\n");
    else if(option_othersimp==1)fprintf(stderr,"time efficient (1)\n");
    else fprintf(stderr,"both (2) \n");
#endif
  }
  if(MINI_CACHE_SIZE > APPLY_CACHE_SIZE)
    rpterr("mini-cache-size (%d) is larger than the cache-size (%d)",
	   MINI_CACHE_SIZE, APPLY_CACHE_SIZE);
  init_string();
  init_assoc();
  init_node();
  init_bdd();
  init_eval();
  
  if(verbose){fprintf(stderr,"Parsing..."); fflush(stderr);}
  if(yyparse())my_exit(1);
  if(verbose)fprintf(stderr,"done.\n");
  
  close_input();

  build_symbols();
  my_exit(0);
}
