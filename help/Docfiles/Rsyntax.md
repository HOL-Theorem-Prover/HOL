## `Rsyntax` {#Rsyntax}


```
Rsyntax
```



A structure that restores a record-style environment for term manipulation.


If one has opened the `Psyntax` structure, one can open the Rsyntax
structure to get record-style functions back.

Each function in the `Rsyntax` structure has a corresponding function
in the Psyntax structure, and vice versa. One can flip-flop between
the two structures by opening one and then the other. One can also use
long identifiers in order to use both syntaxes at once.

### Failure

Never fails.

### Example

The following shows how to open the Rsyntax structure and the
functions that subsequently become available in the top level
environment. Documentation for each of these functions is available
online.
    
       - open Rsyntax;
       open Rsyntax
       val INST = fn : term subst -> thm -> thm
       val INST_TYPE = fn : hol_type subst -> thm -> thm
       val INST_TY_TERM = fn : term subst * hol_type subst -> thm -> thm
       val SUBST = fn : {thm:thm, var:term} list -> term -> thm -> thm
       val SUBST_CONV = fn : {thm:thm, var:term} list -> term -> term -> thm
       val define_new_type_bijections = fn
         : {ABS:string, REP:string, name:string, tyax:thm} -> thm
       val dest_abs = fn : term -> {Body:term, Bvar:term}
       val dest_comb = fn : term -> {Rand:term, Rator:term}
       val dest_cond = fn : term -> {cond:term, larm:term, rarm:term}
       val dest_conj = fn : term -> {conj1:term, conj2:term}
       val dest_cons = fn : term -> {hd:term, tl:term}
       val dest_const = fn : term -> {Name:string, Ty:hol_type}
       val dest_disj = fn : term -> {disj1:term, disj2:term}
       val dest_eq = fn : term -> {lhs:term, rhs:term}
       val dest_exists = fn : term -> {Body:term, Bvar:term}
       val dest_forall = fn : term -> {Body:term, Bvar:term}
       val dest_imp = fn : term -> {ant:term, conseq:term}
       val dest_let = fn : term -> {arg:term, func:term}
       val dest_list = fn : term -> {els:term list, ty:hol_type}
       val dest_pabs = fn : term -> {body:term, varstruct:term}
       val dest_pair = fn : term -> {fst:term, snd:term}
       val dest_select = fn : term -> {Body:term, Bvar:term}
       val dest_type = fn : hol_type -> {Args:hol_type list, Tyop:string}
       val dest_var = fn : term -> {Name:string, Ty:hol_type}
       val inst = fn : hol_type subst -> term -> term
       val match_term = fn : term -> term -> term subst * hol_type subst
       val match_type = fn : hol_type -> hol_type -> hol_type subst
       val mk_abs = fn : {Body:term, Bvar:term} -> term
       val mk_comb = fn : {Rand:term, Rator:term} -> term
       val mk_cond = fn : {cond:term, larm:term, rarm:term} -> term
       val mk_conj = fn : {conj1:term, conj2:term} -> term
       val mk_cons = fn : {hd:term, tl:term} -> term
       val mk_const = fn : {Name:string, Ty:hol_type} -> term
       val mk_disj = fn : {disj1:term, disj2:term} -> term
       val mk_eq = fn : {lhs:term, rhs:term} -> term
       val mk_exists = fn : {Body:term, Bvar:term} -> term
       val mk_forall = fn : {Body:term, Bvar:term} -> term
       val mk_imp = fn : {ant:term, conseq:term} -> term
       val mk_let = fn : {arg:term, func:term} -> term
       val mk_list = fn : {els:term list, ty:hol_type} -> term
       val mk_pabs = fn : {body:term, varstruct:term} -> term
       val mk_pair = fn : {fst:term, snd:term} -> term
       val mk_primed_var = fn : {Name:string, Ty:hol_type} -> term
       val mk_select = fn : {Body:term, Bvar:term} -> term
       val mk_type = fn : {Args:hol_type list, Tyop:string} -> hol_type
       val mk_var = fn : {Name:string, Ty:hol_type} -> term
       val new_binder = fn : {Name:string, Ty:hol_type} -> unit
       val new_constant = fn : {Name:string, Ty:hol_type} -> unit
       val new_infix = fn : {Name:string, Prec:int, Ty:hol_type} -> unit
       val new_recursive_definition = fn
         : {def:term, fixity:fixity, name:string, rec_axiom:thm} -> thm
       val new_specification = fn
         : {consts:{const_name:string, fixity:fixity} list,
            name:string, sat_thm:thm}
           -> thm
       val new_type = fn : {Arity:int, Name:string} -> unit
       val new_type_definition = fn
         : {inhab_thm:thm, name:string, pred:term} -> thm
       val subst = fn : term subst -> term -> term
       val subst_occs = fn : int list list -> term subst -> term -> term
       val type_subst = fn : hol_type subst -> hol_type -> hol_type
    



### See also

[`Psyntax`](#Psyntax)

