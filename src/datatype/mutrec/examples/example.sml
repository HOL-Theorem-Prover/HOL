(*---------------------------------------------------------------------------
 * This example defines the abstract syntax for a simple ML-like language,
 *  and a simple mutually-recursive function for computing the variables
 *  in a program.
 *---------------------------------------------------------------------------*)

app load ["mutrecLib", "stringTheory", "setTheory"];


(*---------------------------------------------------------------------------
 * First, we define a type of variables.
 *---------------------------------------------------------------------------*)

val var_Axiom =
  Define_type.define_type
     {name="var_Axiom",
      fixities = [Term.Prefix],
      type_spec =`var = VAR of string`};

val var_ty = Parse.Type`:var`;


(*------------GRAMMAR---------------------------------------------------------

       atexp ::= <var>
               | let <dec> in <exp> end

       exp   ::= <atexp>
               | <exp> <atexp>
               | fn <match>

       match ::= <rule>
               | <rule> "|" <match>

       rule ::= <pat> => <exp>

       dec   ::= val <valbind>
               | local <dec> in <dec> end
               | <dec> ; <dec>

     valbind ::= <pat> = <exp>
               | <pat> = <exp> and <valbind>
               | valrec <valbind>

       pat   ::= _  (* wildcard *)
               | <var>

 *------------------------------------------------------------------------*)

local open TypeInfo
in
val syntax_spec =
[{type_name = "atexp",
  constructors =
      [{name = "var_exp", arg_info = [existing var_ty]},
       {name = "let_exp", arg_info = [being_defined "dec",
                                      being_defined "exp"]}]},
 {type_name = "exp",
  constructors =
      [{name = "aexp", arg_info = [being_defined "atexp"]},
       {name = "app_exp", arg_info = [being_defined "exp",
				     being_defined "atexp"]},
       {name = "fn_exp", arg_info = [being_defined "match"]}]},
 {type_name = "match",
  constructors =
      [{name = "match", arg_info = [being_defined "rule"]},
       {name = "match_list", arg_info = [being_defined "rule",
                                         being_defined "match"]}]},
 {type_name = "rule",
  constructors =
      [{name = "rule", arg_info = [being_defined "pat",
                                   being_defined "exp"]}]},
 {type_name = "dec",
  constructors =
      [{name = "val_dec", arg_info = [being_defined "valbind"]},
       {name = "local_dec", arg_info = [being_defined "dec",
                                        being_defined "dec"]},
       {name = "seq_dec", arg_info = [being_defined "dec",
                                      being_defined "dec"]}]},
 {type_name = "valbind",
  constructors =
      [{name = "bind", arg_info = [being_defined "pat",
                                   being_defined "exp"]},
       {name = "bind_list", arg_info = [being_defined "pat",
                                        being_defined "exp",
                                        being_defined "valbind"]},
       {name = "rec_bind", arg_info = [being_defined "valbind"]}]},
 {type_name = "pat",
  constructors =
      [{name = "wild_pat", arg_info = []},
       {name = "var_pat", arg_info = [existing var_ty]}]}]
end;


(*---------------------------------------------------------------------------
 * Now define the type!
 *---------------------------------------------------------------------------*)
val {Cases = syntax_cases,
     Constructors_Distinct = syntax_constructors_distinct,
     Constructors_One_One = syntax_constructors_one_one,
     New_Ty_Existence = syntax_existence_thm,
     New_Ty_Uniqueness = syntax_uniqueness_thm,
     New_Ty_Induct = syntax_induction_thm,
     Argument_Extraction_Defs}
 = Lib.time
     mutrecLib.define_type syntax_spec;


(*---------------------------------------------------------------------------
 * A simple function for finding the variables in an expression of
 * the defined syntax.
 *---------------------------------------------------------------------------*)

val vars_thm = mutrecLib.define_mutual_functions
{name = "vars_thm", rec_axiom = syntax_existence_thm, fixities = NONE,
 def = Parse.Term

   `(atexpV (var_exp v) = {v}) /\
    (atexpV (let_exp d e) = (decV d) UNION (expV e))
     /\
    (expV (aexp a) = atexpV a) /\
    (expV (app_exp e a) = (expV e) UNION (atexpV a)) /\
    (expV (fn_exp m) = matchV m)
     /\
    (matchV (match r) = ruleV r) /\
    (matchV (match_list r mrst) = (ruleV r) UNION (matchV mrst))
     /\
    (ruleV (rule p e) = (patV p) UNION (expV e))
     /\
    (decV (val_dec b) = valbindV b) /\
    (decV (local_dec d1 d2) = (decV d1) UNION (decV d2)) /\
    (decV (seq_dec d1 d2) = (decV d1) UNION (decV d2))
     /\
    (valbindV (bind p e) = (patV p) UNION (expV e)) /\
    (valbindV (bind_list p e brst) = (patV p) UNION (expV e)
                                     UNION (valbindV brst)) /\
    (valbindV (rec_bind vb) = (valbindV vb))
     /\
    (patV wild_pat = {}) /\
    (patV (var_pat v) = {v})`};


(* Warning!

One has to exercise a little discipline with variable names in
quotations that define mutually recursive functions. Type inference will
attempt to unify the types of variables in different clauses. This is
OK, provided that, as in the example above, all occurrences of "d" are
to have type `:dec` (for instance). However, if one tries to have the
clauses

  (matchV (match_list r rst) = (ruleV r) UNION (matchV rst))

and

  (valbindV (bind_list p e rst) = (patV p) UNION (expV e) UNION (valbindV rst))

appear in the same mutually recursive function definition, type
inference will attempt to make the types of both "rst" be the same. This
will fail, since the first is supposed to have the type `:match` and the
second `:valbind`.

This is _not_ a bug in type inference, but a shortcoming in the form that
an input term may have; something should be done to allow the
restriction of scope of variables in the term that specifies the
function (like allowing quantification for each conjunct).
*)
