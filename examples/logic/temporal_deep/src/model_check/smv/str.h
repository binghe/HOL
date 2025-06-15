typedef struct string{
  struct assoc *link;
  char *text;
} string_rec,*string_ptr;

string_ptr find_string(char *x);
void init_string(void);
