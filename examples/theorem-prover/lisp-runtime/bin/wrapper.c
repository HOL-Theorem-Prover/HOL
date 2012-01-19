#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <time.h>
#include "wrapper.h"

void jit_exec(long *);


/* global variables */

#ifdef DEBUG
long gc_count = 0;
long *exp_stack;
long *heap1;
long *heap2;
char *symtable;
char *code_heap;
long original_stack_size;
long original_code_heap_size;
time_t prev_print;
#endif

/* functions which can be called from within the verified code */

void print_str (char* str, long i, long e, long wsp) {
  printf("%s",str);
#ifdef DEBUG
  if ((int)str[0] == 10) {
    if (i == e) {
      printf(";  heap: 1.00000  ");
    } else {
      printf(";  heap: 0.%05ld  ", i * 100000 / e);
    }
    time(&prev_print);
    printf("stack: %ld  GCs: %ld  consts: %ld  code: %ldkB  time: %s",
           original_stack_size - wsp, gc_count, exp_stack[18+8],
           (original_code_heap_size - exp_stack[18+3]) / 1024, ctime(&prev_print));
  }
#endif
}

long read_line_counter = 0;
char read_line_buffer[1024*1024];
char* read_line() {
  read_line_counter++;
  printf("> ");
  if (fgets (read_line_buffer, 1024*1024, stdin) == NULL) {
    printf("\n");
    return "";
  }
  return read_line_buffer;
}

/* long gc_started = 0; */
void print_stats (long state, long i, long e) {
#ifdef DEBUG
  if (state == 1) { gc_count++; } else {}
#endif
  /*
  time_t now; time(&now);
  if (state == 1) {
    gc_started = now; printf("GC: ");
  } else {
    printf("lasted %ld seconds, heap usage %02f %s  --- %s", now - gc_started, ((float)i)/((float)e) * 100.0, "%", ctime(&now));
  }
  */
}

void report_error(long bp, long sp, long error) {
  printf("ERROR: ");
  switch (error) {
    case  0: printf("Not enough heap space.\n\n"); break;
    case  1: printf("Not enough stack space.\n\n"); break;
    case  2: printf("Arithmetic overflow.\n\n"); break;
    case  3: printf("Not enough space in code heap.\n\n"); break;
    case  4: printf("Runtime error caused by 'error' function.\n\n"); break;
    case  5: printf("Syntax error.\n\n"); break;
    case  6: printf("Encountered a symbol longer than 255 characters.\n\n"); break;
    case  7: printf("Not enough space in symbol table.\n\n"); break;
    case  8: printf("Illformed abbreviation.\n\n"); break;
    case  9: printf("Encountered a number larger than 1,073,741,823.\n\n"); break;
    case 10: printf("Unexpected end of input stream.\n\n"); break;
    case 11: printf("An undefined function was called.\n\n"); break;
    case 12: printf("Not enough space for new constant.\n\n"); break;
  default: printf("Unknown error (%d).\n\n",(int)error); break;
  }
  exit(EXIT_SUCCESS);
}


/* a function which allocates memory with EXEC enabled */

char * alloc_executable(size_t len) { /* len = number of bytes */
  /* Local variables */
  size_t page_size = getpagesize();
  /* Round up so that len is a multiple of getpagesize() */
  if (len % page_size) {
    len &= ~(page_size-1);
    len += page_size;
  }
  /* Open a file for use as scratch memory */
  int fd = 0, ret = 0;
  void *pa = MAP_FAILED;
  char template[] = "/tmp/alloc_executable_XXXXXX";
  fd = mkstemp(template);
  if (fd < 0) return pa;
  unlink(template);
  ret = ftruncate(fd, len);
  if (ret < 0) return pa;
  /* Do the allocation */
  return mmap(NULL, len, PROT_READ|PROT_WRITE|PROT_EXEC, MAP_PRIVATE, fd, 0);
}


/* main function */

int main(int argc, char** argv) {

  printf("Jitawa -- test version (built %s)\n", NOW);

  setvbuf(stdout, NULL, _IONBF, 0); // this line makes sure stdout is not buffered

#ifndef DEBUG
  long gc_count = 0;
  long *exp_stack;
  long *heap1;
  long *heap2;
  char *symtable;
  char *code_heap;
  long original_stack_size;
  long original_code_heap_size;
  time_t prev_print;
#endif

  char* settings = "default";
  long heap_size = 1;             // million cons-cells that fit into the heap
  long stack_size = 1;            // million expressions that fit into the stack
  long const_table_size = 1;      // thousand expressions that fit into the const table
  long symtable_size = 64;        // kilo roughly speaking the number of characters
  long abbrev_array_length = 10;  // number of cells in abbrev-speed-up array
  long code_heap_size = 1;        // megabytes
  long generation_size = 0;       // million cons-cells that fit into the first generation heap

  if (1 < argc) {
    if (strcmp(argv[1],"large") == 0) {
      heap_size = 1500;
      generation_size = 700;
      stack_size = 600;
      const_table_size = 1024;
      symtable_size = 1024;
      abbrev_array_length = 550000000;
      code_heap_size = 500;
      settings = argv[1];
    }
  }
  printf("Using %s settings: heap[%ldMcons], stack[%ldMcons], symtable[%ldkB], code[%ldMB]\n",settings,heap_size,stack_size,symtable_size,code_heap_size);

  heap_size        *= 1024 * 1024;
  generation_size  *= 1024 * 1024;
  stack_size       *= 1024 * 1024;
  const_table_size *= 1024;
  symtable_size    *= 1024;
  code_heap_size   *= 1024 * 1024;

  if (generation_size == 0) {
    generation_size = heap_size / 4;
  }

  exp_stack = malloc(4 * stack_size + 256 + 4 * const_table_size + 32);
  heap1 = malloc(8 * heap_size);
  heap2 = malloc(8 * heap_size);
  symtable = malloc(symtable_size);
  code_heap = alloc_executable(code_heap_size);
  if (exp_stack == NULL) { printf("Unable to allocate stack of size %ld.\n", stack_size); exit(EXIT_FAILURE); }
  if (heap1 == NULL) { printf("Unable to allocate heap(1) of size %ld.\n", heap_size); exit(EXIT_FAILURE); }
  if (heap2 == NULL) { printf("Unable to allocate heap(2) of size %ld.\n", heap_size); exit(EXIT_FAILURE); }
  if (symtable == NULL) { printf("Unable to allocate symbol table of size %ld.\n", symtable_size); exit(EXIT_FAILURE); }
  if (code_heap == NULL) { printf("Unable to allocate code heap of size %ld.\n", code_heap_size); exit(EXIT_FAILURE); }

  /* initialising the state based on lisp_init_def and zLISP_INTI_def */
  read_line_buffer[0] = 0;
  // main init state
  exp_stack[0]  = (long)heap1;
  exp_stack[1]  = (long)heap2;
  exp_stack[2]  = (long)heap_size;
  exp_stack[3]  = (long)stack_size;
  exp_stack[4]  = (long)symtable;
  exp_stack[5]  = (long)symtable_size;
  exp_stack[6]  = (long)0;
  exp_stack[7]  = (long)(*report_error);
  // cs starts at exp_stack[8]
  exp_stack[8]  = (long)print_str;
  exp_stack[9]  = (long)read_line;
  exp_stack[10] = (long)print_stats;
  exp_stack[11] = (long)abbrev_array_length;
  exp_stack[12] = (long)code_heap;
  exp_stack[13] = (long)code_heap_size;
  exp_stack[14] = (long)0;
  exp_stack[15] = (long)0;
  exp_stack[16] = (long)0;
  exp_stack[17] = (long)0;
  // ds starts at exp_stack[8]
  exp_stack[18] = (long)read_line_buffer;
  exp_stack[18+5] = (long)generation_size;
  exp_stack[18+7] = (long)const_table_size;
  original_stack_size = (long)stack_size;
  original_code_heap_size = (long)code_heap_size;

  jit_exec(exp_stack);

  printf("\n");
  exit(EXIT_SUCCESS);
}


