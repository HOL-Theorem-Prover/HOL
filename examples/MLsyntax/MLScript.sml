(*---------------------------------------------------------------------------*
 * This example defines the abstract syntax for a simple ML-like language,   *
 * and a simple mutually-recursive function for computing the variables      *
 * in a program.  It exercises the type definition package on a mutually     *
 * recursive concrete type.                                                  *
 *                                                                           *
 * The example is also a demonstration of how Holmake works. Just invoke     *
 *                                                                           *
 *     Holmake                                                               *
 *                                                                           *
 * and wait. When Holmake is done, a compiled theory corresponding to this   *
 * file is found in MLSyntaxTheory.u{i,o}. It can be loaded into an          *
 * interactive session by                                                    *
 *                                                                           *
 *    load "MLTheory";                                                       *
 *                                                                           *
 * Loading the theory can take a little while - about 5 seconds on my        *
 * machine.                                                                  *
 *                                                                           *
 * If you are working interactively, i.e., you don't want to pay any         *
 * attention to this Holmake stuff, do the following:                        *
 *                                                                           *
    app load ["bossLib", "stringTheory", "setTheory"];
 *                                                                           *
 * and then proceed with cut-and-paste.                                      *
 *                                                                           *
 *                                                                           *
 *                                                                           *
 *              GRAMMAR                                                      *
 *             ---------                                                     *
 *                                                                           *
 *     atexp ::= <var>                                                       *
 *             | "let" <dec> "in" <exp> "end"                                *
 *                                                                           *
 *     exp   ::= <atexp>                                                     *
 *             | <exp> <atexp>                                               *
 *             | "fn" <match>                                                *
 *                                                                           *
 *     match ::= <rule>                                                      *
 *             | <rule> "|" <match>                                          *
 *                                                                           *
 *      rule ::= <pat> "=>" <exp>                                            *
 *                                                                           *
 *       dec ::= "val" <valbind>                                             *
 *             | "local" <dec> "in" <dec> "end"                              *
 *             | <dec> ";" <dec>                                             *
 *                                                                           *
 *   valbind ::= <pat> "=" <exp>                                             *
 *             | <pat> "=" <exp> "and" <valbind>                             *
 *             | "valrec" <valbind>                                          *
 *                                                                           *
 *     pat   ::= "_"  (* wildcard *)                                         *
 *             | <var>                                                       *
 *                                                                           *
 *---------------------------------------------------------------------------*)


structure MLScript =
struct

open bossLib Theory Parse ;

local open stringTheory pred_setTheory   (* Make strings and sets be present *)
in end;

val _ = new_theory "ML";


(*---------------------------------------------------------------------------
    Define the type of variables.
 ---------------------------------------------------------------------------*)

val _ = Hol_datatype `var = VAR of string`;


(*---------------------------------------------------------------------------
    Define the datatype of ML syntax trees.
 ---------------------------------------------------------------------------*)

val _ = Hol_datatype
        `atexp = var_exp of var
               | let_exp of dec => exp ;

           exp = aexp    of atexp
               | app_exp of exp => atexp
               | fn_exp  of match ;

         match = match  of rule
               | matchl of rule => match ;

          rule = rule of pat => exp ;

           dec = val_dec   of valbind
               | local_dec of dec => dec
               | seq_dec   of dec => dec ;

       valbind = bind  of pat => exp
               | bindl of pat => exp => valbind
               | rec_bind of valbind ;

           pat = wild_pat
               | var_pat of var`;


(*---------------------------------------------------------------------------
      A simple collection of functions for finding the variables
      in a program.
 ----------------------------------------------------------------------------*)

val Vars_def =
 Define
   `(atexpV (var_exp v)      = {v}) /\
    (atexpV (let_exp d e)    = (decV d) UNION (expV e))
     /\
    (expV (aexp a)           = atexpV a) /\
    (expV (app_exp e a)      = (expV e) UNION (atexpV a)) /\
    (expV (fn_exp m)         = matchV m)
     /\
    (matchV (match r)        = ruleV r) /\
    (matchV (matchl r mrst)  = (ruleV r) UNION (matchV mrst))
     /\
    (ruleV (rule p e)        = (patV p) UNION (expV e))
     /\
    (decV (val_dec b)        = valbindV b) /\
    (decV (local_dec d1 d2)  = (decV d1) UNION (decV d2)) /\
    (decV (seq_dec d1 d2)    = (decV d1) UNION (decV d2))
     /\
    (valbindV (bind p e)     = (patV p) UNION (expV e)) /\
    (valbindV (bindl p e vb) = (patV p) UNION (expV e) UNION (valbindV vb)) /\
    (valbindV (rec_bind vb)  = (valbindV vb))
     /\
    (patV wild_pat           = {}) /\
    (patV (var_pat v)        = {v})`;

val _ = export_theory();

end;
