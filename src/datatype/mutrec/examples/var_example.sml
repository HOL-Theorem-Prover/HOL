(* This example is basically the same as the one in example.sml, except
   that the type for variables is left as a type variable.
*)

new_theory "var_ex";
load_library_in_place (find_library "mutrec");

val var_ty = (==`:'var`==)

structure Ast  =
struct
structure TypeInfo = TypeInfo
open TypeInfo
val mut_rec_ty_spec =
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
       {name = "var_pat", arg_info = [existing var_ty]}]}];


    val New_Ty_Existence_Thm_Name = "syntax_existence_thm"
    val New_Ty_Induct_Thm_Name = "syntax_induction_thm"
    val New_Ty_Uniqueness_Thm_Name = "syntax_uniqueness_thm"
    val Constructors_Distinct_Thm_Name = "syntax_constructors_distinct"
    val Constructors_One_One_Thm_Name = "syntax_constructors_one_one"
    val Cases_Thm_Name = "syntax_cases"


end; (* struct *)


(* Prove the defining theorems for the type *)
structure GramDef = MutRecTypeFunc (Ast);

(* Just so that the constant "UNION" is defined. To actually work with sets,
   one would want to load in the "set" library.
*)
val _ = new_parent "set";
(* A simple function for finding the variables in a program *)

val vars_thm = define_mutual_functions
{name = "vars_thm", rec_axiom = syntax_existence_thm, fixities = NONE,
 def =
(--`(atexpV (var_exp (v:'var)) = {v}) /\
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
    (patV (var_pat v) = {v})`--)};
