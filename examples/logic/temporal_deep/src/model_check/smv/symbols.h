node_ptr find_atom(node_ptr a);
void check_spec(node_ptr the_spec);
void eval_command(node_ptr exp);
void trans_command(node_ptr n);
void init_command(node_ptr n);
void fair_command(node_ptr n);
void reset_command(void);
#ifdef TIMING
void compute_bound(node_ptr the_spec);
#endif
void goto_state(node_ptr s);
void assign_command(node_ptr var, node_ptr val);
void single_step(void);
void build_symbols(void);
void type_error(node_ptr n);
void output_order(void);
