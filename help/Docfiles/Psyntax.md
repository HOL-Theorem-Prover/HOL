## `Psyntax` {#Psyntax}


```
Psyntax : Psyntax_sig
```



A structure that provides a tuple-style environment for term manipulation.


Each function in the `Psyntax` structure has a corresponding “record
version" in the `Rsyntax` structure, and vice versa. One can flip-flop
between the two structures by opening one and then the other. One can
also use long identifiers in order to use both syntaxes at once.

### Failure

Never fails.

### Example

The following shows how to open the `Psyntax` structure and the
functions that subsequently become available in the top level
environment. Documentation for each of these functions is available
online.
    
       - open Psyntax;
    
This command results in the following functions entering the top-level
name-space.  Term creation functions:
    
       val mk_var = fn : string * hol_type -> term
       val mk_const = fn : string * hol_type -> term
       val mk_comb = fn : term * term -> term
       val mk_abs = fn : term * term -> term
       val mk_primed_var = fn : string * hol_type -> term
       val mk_eq = fn : term * term -> term
       val mk_imp = fn : term * term -> term
       val mk_select = fn : term * term -> term
       val mk_forall = fn : term * term -> term
       val mk_exists = fn : term * term -> term
       val mk_conj = fn : term * term -> term
       val mk_disj = fn : term * term -> term
       val mk_cond = fn : term * term * term -> term
       val mk_let = fn : term * term -> term
    
Term “destructor” functions (i.e., those functions that pull a term
apart, and reveal some of its internal structure):
    
       val dest_var = fn : term -> string * hol_type
       val dest_const = fn : term -> string * hol_type
       val dest_comb = fn : term -> term * term
       val dest_abs = fn : term -> term * term
       val dest_eq = fn : term -> term * term
       val dest_imp = fn : term -> term * term
       val dest_select = fn : term -> term * term
       val dest_forall = fn : term -> term * term
       val dest_exists = fn : term -> term * term
       val dest_conj = fn : term -> term * term
       val dest_disj = fn : term -> term * term
       val dest_cond = fn : term -> term * term * term
       val dest_let = fn : term -> term * term
    
The `lambda` datatype for taking terms apart, which is the range of the
`dest_term` function.
    
       datatype lambda =
          VAR of string * hol_type
        | CONST of {Name : string, Thy : string, Ty : hol_type}
        | COMB of term * term
        | LAMB of term * term
       val dest_term : term -> lambda
    

### See also

[`Rsyntax`](#Rsyntax)

