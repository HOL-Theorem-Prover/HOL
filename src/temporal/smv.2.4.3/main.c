#include <stdio.h>
#include <sys/types.h>
#include <sys/times.h>
#include <storage.h>
#include <node.h>
#include <hash.h>
#include <bdd.h>
#include <assoc.h>
#include <grammar.tab.h>
#include <setjmp.h>
#include <unistd.h> /* for changing stderr to stdout */

#include <time.h>
#ifndef CLK_TCK
# define CLK_TCK 60
#endif

void init_eval(){}

int KEYTABLESIZE=16381, APPLY_CACHE_SIZE=16381, MINI_CACHE_SIZE=16381;
int heuristics = 0,verbose = 0,option_print_reachable=0,
  option_forward_search = 0,option_round_robin = 0,
  option_incremental = 0,option_restrict_trans = 0, option_interactive = 0,
  option_AG_only = 0, option_conj_part = 0;
int interactive_mode = 0;
int conj_part_limit = 0;
double fudge_factor;
char *output_order_file = 0,*input_order_file = 0;
static char *input_file = "stdin";
static char *myname = "smv";
static hash_ptr seq_hash;
static char* addrstart;

extern node_ptr parse_tree;

main(argc,argv)
int argc;
char **argv;
{
  extern int yylineno;
  dup2(1,2);	/* changing stderr to stdout */
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
    if(strcmp(*argv,"-r")==0){
      argv++;
      argc--;
      option_print_reachable = 1;
      continue;
    }
    if(strcmp(*argv,"-f")==0){
      argv++;
      argc--;
      option_forward_search = 1;
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
    if(argc<2)rpterr("command line error");
    if(strcmp(*argv,"-v")==0){
      argv++;
      sscanf(*(argv++),"%d",&verbose);
      setlinebuf(stdout);
      setlinebuf(stderr);
    }
    else if(strcmp(*argv,"-i")==0){
      argv++;
      input_order_file = *(argv++);
    }
    else if(strcmp(*argv,"-o")==0){
      argv++;
      output_order_file = *(argv++);
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
    else rpterr("undefined: %s",*argv);
    argc -= 2;
  }
  if(verbose){
    fprintf(stderr,"Key table size: %d\n",KEYTABLESIZE);
    fprintf(stderr,"Apply cache size: %d\n",APPLY_CACHE_SIZE);
    fprintf(stderr,"Variable ordering heuristics: ");
    if(heuristics)fprintf(stderr,"ON, factor = %g\n",fudge_factor);
    else fprintf(stderr,"OFF\n");
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

open_input(filename)
char *filename;
{
  extern int yylineno;
  extern FILE *yyin;
  input_file = filename;
  if(!(yyin = fopen(filename,"r")))
    rpterr("cannot open %s for input",filename);
  yylineno = 1;
}

close_input()
{
  extern int yylineno;
  input_file = 0;
  yylineno = 0;
}

static node_ptr atom_stack=0;

undefined(s)
node_ptr s;
{
  start_err();
  print_node(stderr,s);
  fprintf(stderr," undefined");
  finish_err();
}

redefining(s)
node_ptr s;
{
  start_err();
  fprintf(stderr,"redefining ");
  print_node(stderr,s);
  finish_err();
}

circular(s)
node_ptr s;
{
  start_err();
  fprintf(stderr,"recursively defined: ");
  print_node(stderr,s);
  finish_err();
}

toomanyvars(s)
node_ptr s;
{
  start_err();
  fprintf(stderr,"too many variables");
  finish_err();
}

start_err()
{
  extern int yylineno;
  fprintf(stderr,"\n");
  if(input_file)fprintf(stderr,"file %s: ",input_file);
  if(yylineno)fprintf(stderr,"line %d: ",yylineno);
}

jmp_buf longjmp_buf;
int longjmp_on_err = 0;
finish_err()
{
  fprintf(stderr,"\n");
  while(atom_stack){
    node_ptr s = car(atom_stack);
    atom_stack = cdr(atom_stack);
    fprintf(stderr,"in definition of ");
    print_node(stderr,s);
    if(s->lineno)
      fprintf(stderr," at line %d",s->lineno);
    fprintf(stderr,"\n");
  }
  if(longjmp_on_err)longjmp(longjmp_buf,1);
  my_exit(1);
}

int my_setjmp()
{
  int v;
  longjmp_on_err = 1;
  v = setjmp(longjmp_buf);
  if(v)
    longjmp_on_err = 0;
  return(v);
}

void cancel_my_setjmp()
{
    longjmp_on_err = 0;
}  
  

my_exit(n)
int n;
{
  if(verbose)fprintf(stderr,"%s: exit(%d)\n ",myname,n);
  exit(n);
}
  
print_usage()
{
  struct tms buffer;
  printf("\nresources used:\n");
  times(&buffer);
  printf("user time: %g s, system time: %g s\n",
	 buffer.tms_utime/(double)CLK_TCK,
	 buffer.tms_stime/(double)CLK_TCK);
  printf("BDD nodes allocated: %d\n",get_bdd_nodes_allocated());
  printf("Bytes allocated: %d\n",(unsigned)((char *)sbrk(0)-addrstart));
}

/*VARARGS1*/
rpterr(s,a1,a2,a3,a4)
char *s,*a1,*a2,*a3,*a4;
{
  start_err();
  fprintf(stderr,s,a1,a2,a3,a4);
  finish_err();
}

/*VARARGS1*/
void catastrophe(s,a1,a2,a3,a4)
char *s,*a1,*a2,*a3,*a4;
{
  fprintf(stderr,"Oh Shit!\ninternal error: ");
  fprintf(stderr,s,a1,a2,a3,a4);
  fprintf(stderr,"\nPlease report this error to mcmillan@cs.cmu.edu\n");
  fprintf(stderr,"Send a copy of this output and your input.\n");
  fprintf(stderr,"Goodbye cruel world...\n");
  my_exit(1);
}

push_atom(s)
node_ptr s;
{
  atom_stack = cons(s,atom_stack);
}

pop_atom()
{
  node_ptr temp;
  if(!atom_stack)catastrophe("pop_atom: stack empty");
  temp = cdr(atom_stack);
  free_node(atom_stack);
  atom_stack = temp;
}

yyerror(s)
char *s;
{
    extern yytext;
    start_err();
    fprintf(stderr,"at token \"%s\": %s\n",&yytext,s);
    if(!interactive_mode)finish_err();
}

yywrap()
{
  return(1);
}

int indent_size = 0;
void indent(stream)
FILE *stream;
{
  int i;
  for(i=0;i<indent_size;i++)fprintf(stream,"  ");
}

void indent_node(stream,s1,n,s2)
FILE *stream;
char *s1,*s2;
node_ptr n;
{
  indent(stream);
  fprintf(stream,"%s",s1);
  print_node(stream,n);
  fprintf(stream,"%s",s2);
}
