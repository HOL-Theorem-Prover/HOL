(*---------------------------------------------------------------------------

     This example defines the abstract syntax for a simple ML-like language,
     and a simple mutually-recursive function for computing the variables 
     in a program. 

 ---------------------------------------------------------------------------*)

app load ["mutualLib", "stringLib", "setTheory"];


(* variables *)

val var_Axiom = 
   Define_type.define_type
    {name="var_Axiom",
     fixities = [Prefix], type_spec =`var = VAR of string`};

val var_ty = Type`:var`;


(*--------------------------GRAMMAR----------------------------------------

       atexp ::= <var> 
               | let <dec> in <exp> end
    
       exp   ::= <atexp>
               | <exp> <atexp>
               | fn <match>
    
       match ::= <rule>
               | <rule> "|" <match>
    
        rule ::= <pat> => <exp>
                
         dec ::= val <valbind>
               | local <dec> in <dec> end
               | <dec> ; <dec>
    
     valbind ::= <pat> = <exp>
               | <pat> = <exp> and <valbind>
               | valrec <valbind>
    
       pat   ::=  _  (* wildcard *)
               | <var>

 -------------------------------------------------------------------------*)


val {Cases_Thm, Constructors_Distinct_Thm,
     Constructors_One_One_Thm, New_Ty_Existence_Thm,
     New_Ty_Induct_Thm, New_Ty_Uniqueness_Thm}
  =  
     time (mutualLib.define_type [])

        `atexp = var_exp of var
               | let_exp of dec => exp ;

           exp = aexp of atexp
               | app_exp of exp => atexp
               | fn_exp of match ;

         match = match of rule
               | match_list of rule => match ;

          rule = rule of pat => exp ;

           dec = val_dec of valbind
               | local_dec of dec => dec
               | seq_dec of dec => dec ;

       valbind = bind of pat => exp
               | bind_list of pat => exp => valbind
               | rec_bind of valbind ;
 
           pat = wild_pat
               | var_pat of var`;


(*---------------------------------------------------------------------------
    A simple function for finding the variables in a program
 --------------------------------------------------------------------------- *)

val vars_thm = mutualLib.define_mutual_functions
{name = "vars_thm", rec_axiom = New_Ty_Existence_Thm, fixities = NONE,
 def =
(--`(atexpV (var_exp v)   = {v}) /\
    (atexpV (let_exp d e) = (decV d) UNION (expV e))
     /\
    (expV (aexp a)        = atexpV a) /\
    (expV (app_exp e a)   = (expV e) UNION (atexpV a)) /\
    (expV (fn_exp m)      = matchV m)
     /\
    (matchV (match r)           = ruleV r) /\
    (matchV (match_list r mrst) = (ruleV r) UNION (matchV mrst))
     /\
    (ruleV (rule p e)           = (patV p) UNION (expV e))
     /\
    (decV (val_dec b)       = valbindV b) /\
    (decV (local_dec d1 d2) = (decV d1) UNION (decV d2)) /\
    (decV (seq_dec d1 d2)   = (decV d1) UNION (decV d2))
     /\
    (valbindV (bind p e)           = (patV p) UNION (expV e)) /\
    (valbindV (bind_list p e brst) = (patV p) UNION (expV e) 
                                     UNION (valbindV brst)) /\
    (valbindV (rec_bind vb) = (valbindV vb))
     /\
    (patV wild_pat     = {}) /\
    (patV (var_pat v) = {v})`--)};


(*---------------------------------------------------------------------------

    Warning! 

   One has to exercise a little discipline with variable names in
   quotations that define mutually recursive functions. Type inference
   will attempt to unify the types of variables in different
   clauses. This is OK, provided that, as in the example above, all
   occurrences of "d" are to have type `:dec` (for instance). However,
   if one tries to have the clauses

      (matchV (match_list r rst) = (ruleV r) UNION (matchV rst))

   and

    (valbindV (bind_list p e rst) = (patV p) UNION (expV e) 
                                             UNION (valbindV rst))

   appear in the same mutually recursive function definition, type
   inference will attempt to make the types of both "rst" be the
   same. This will fail, since the first is supposed to have the type
   `:match` and the second `:valbind`.

   This is _not_ a bug in type inference, but a shortcoming in the form
   that an input term may have; something should be done to allow the
   restriction of scope of variables in the term that specifies the
   function (like allowing quantification for each conjunct).

 ---------------------------------------------------------------------------*)
