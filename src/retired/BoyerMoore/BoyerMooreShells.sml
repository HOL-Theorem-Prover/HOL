(****************************************************************************)
(* FILE          : shells.sml                                               *)
(* DESCRIPTION   : Vague approximation in ML to the Boyer-Moore `shell'     *)
(*                 principle.                                               *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 8th May 1991                                             *)
(*                                                                          *)
(* TRANSLATED BY : R.J.Boulton                                              *)
(* DATE          : 2nd October 1995                                         *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 18th November 1995                                       *)
(****************************************************************************)

structure BoyerMooreShells =
struct

local

open HolKernel Parse basicHol90Lib Abbrev Prim_rec_Compat Psyntax;
open Define_type;
infix ##;

fun failwith function =
   raise HOL_ERR {origin_structure = "BoyerMooreShells",
                  origin_function = function,
                  message = ""};

in

(*--------------------------------------------------------------------------*)
(* ML datatype for holding information about a recursive logical type.      *)
(*--------------------------------------------------------------------------*)

type constructor_info =
   string *               (* Constructor name   *)
   hol_type list *        (* Argument types     *)
   (string * thm) list;   (* Accessor functions *)

type shell_info =
   {arg_types : hol_type list,     (* Argument types for type constructor *)
    constructors :
       constructor_info list,      (* Constructors for the type           *)
    axiom : thm,                   (* Type axiom                          *)
    induct : thm,                  (* Induction theorem                   *)
    cases : thm,                   (* Cases theorem                       *)
    distinct : thm list,           (* Constructors distinct               *)
    one_one : thm list,            (* Constructors one-one                *)
    struct_conv : conv -> conv};   (* Structure simplification conversion *)

datatype shell = Shell of string * shell_info;

(*--------------------------------------------------------------------------*)
(* Reference variable holding the currently defined system shells.          *)
(*--------------------------------------------------------------------------*)

val system_shells = ref ([] : shell list);

(*--------------------------------------------------------------------------*)
(* Function to find the details of a named shell from a list of shells.     *)
(*--------------------------------------------------------------------------*)

fun shell_info [] name = failwith "shell_info"
  | shell_info ((Shell (sh_name,info))::shells) name =
   if (sh_name = name)
   then info
   else shell_info shells name;

(*--------------------------------------------------------------------------*)
(* Function to find the details of a named shell from the shells currently  *)
(* defined in the system.                                                   *)
(*--------------------------------------------------------------------------*)

fun sys_shell_info name = shell_info (!system_shells) name;

(*--------------------------------------------------------------------------*)
(* Function to extract details of a named constructor from shell            *)
(* information.                                                             *)
(*--------------------------------------------------------------------------*)

fun shell_constructor name (info : shell_info) =
   let fun shell_constructor' name [] = failwith "shell_constructor"
         | shell_constructor' name
              ((con_name,arg_types,accessors)::constructors) =
          if (con_name = name)
          then (arg_types,accessors)
          else shell_constructor' name constructors
   in  shell_constructor' name (#constructors info)
   end;

(*--------------------------------------------------------------------------*)
(* Functions to extract the argument types and the accessor functions for a *)
(* particular constructor. The source is a set of shell information.        *)
(*--------------------------------------------------------------------------*)

fun shell_constructor_arg_types name info = #1 (shell_constructor name info)
and shell_constructor_accessors name info = #2 (shell_constructor name info);

(*--------------------------------------------------------------------------*)
(* shells : unit -> string list                                             *)
(*                                                                          *)
(* Function to compute the names of the currently defined system shells.    *)
(*--------------------------------------------------------------------------*)

fun shells () =
   let fun shells' [] = []
         | shells' ((Shell (name,_))::shl) = name::(shells' shl)
   in  shells' (!system_shells)
   end;

(*--------------------------------------------------------------------------*)
(* all_constructors : unit -> string list                                   *)
(*                                                                          *)
(* Returns a list of all the shell constructors (and bottom values)         *)
(* available in the system.                                                 *)
(*--------------------------------------------------------------------------*)

fun all_constructors () =
   flatten (map (map #1 o #constructors o sys_shell_info) (shells ()));

(*--------------------------------------------------------------------------*)
(* all_accessors : unit -> string list                                      *)
(*                                                                          *)
(* Returns a list of all the shell accessors available in the system.       *)
(*--------------------------------------------------------------------------*)

fun all_accessors () =
   flatten
      (map (flatten o map (map #1 o #3) o #constructors o sys_shell_info)
          (shells ()));

(*--------------------------------------------------------------------------*)
(* `Shell' for natural numbers.                                             *)
(*--------------------------------------------------------------------------*)

val num_shell =
   let val axiom = prim_recTheory.num_Axiom
       and induct = numTheory.INDUCTION
       and cases = arithmeticTheory.num_CASES
       and distinct = [arithmeticTheory.SUC_NOT]
       and one_one = [prim_recTheory.INV_SUC_EQ]
       and PRE = prim_recTheory.PRE
   in  Shell
          ("num",
           {arg_types = [],
            constructors =
               [("0",[],[]),("SUC",[(==`:num`==)],[("PRE",CONJUNCT2 PRE)])],
            axiom = axiom,
            induct = induct,
            cases = cases,
            distinct = distinct,
            one_one = one_one,
            struct_conv = BoyerMooreStructEqual.ONE_STEP_RECTY_EQ_CONV
                             (induct,distinct,one_one)})
   end;

(*--------------------------------------------------------------------------*)
(* `Shell' for lists.                                                       *)
(*--------------------------------------------------------------------------*)

val list_shell =
   let val axiom = listTheory.list_Axiom
       and induct = listTheory.list_INDUCT
       and cases = listTheory.list_CASES
       and distinct = [listTheory.NOT_NIL_CONS]
       and one_one = [listTheory.CONS_11]
       and HD = listTheory.HD
       and TL = listTheory.TL
   in  Shell
          ("list",
           {arg_types = [(==`:'a`==)],
            constructors =
               [("NIL",[],[]),
                ("CONS",
                 [(==`:'a`==),(==`:('a)list`==)],[("HD",HD),("TL",TL)])],
            axiom = axiom,
            induct = induct,
            cases = cases,
            distinct = distinct,
            one_one = one_one,
            struct_conv = BoyerMooreStructEqual.ONE_STEP_RECTY_EQ_CONV
                             (induct,distinct,one_one)})
   end;

(*--------------------------------------------------------------------------*)
(* Set-up the system shell to reflect the basic HOL system.                 *)
(*--------------------------------------------------------------------------*)

val _ = system_shells := [list_shell,num_shell];

(*--------------------------------------------------------------------------*)
(* define_shell : {name : string,                                           *)
(*                 type_spec : term frag list,                              *)
(*                 fixities : fixity list,                                  *)
(*                 accessors : (string * string list) list} -> unit         *)
(*                                                                          *)
(* Function for defining a new HOL type together with accessor functions,   *)
(* and making a new Boyer-Moore shell from these definitions. If the type   *)
(* already exists the function attempts to load the corresponding theorems  *)
(* from the current theory hierarchy and use them to make the shell.        *)
(*                                                                          *)
(* The first three fields of the argument correspond to those taken by      *)
(* `define_type' and the fourth defines the accessor functions. This is a   *)
(* list of constructor names each with names of accessors. The function     *)
(* assumes that there are no accessors for a constructor that doesn't       *)
(* appear in the list, so it is not necessary to include an entry for a     *)
(* nullary constructor. For other constructors there must be one accessor   *)
(* name for each argument and they should be given in the correct order.    *)
(* The function ignores any item in the list with a constructor name that   *)
(* does not belong to the type.                                             *)
(*                                                                          *)
(* The constructor and accessor names must all be distinct and must not be  *)
(* the names of existing constants.                                         *)
(*                                                                          *)
(* Example:                                                                 *)
(*                                                                          *)
(*    define_shell                                                          *)
(*       {name = "sexp",                                                    *)
(*        type_spec = `sexp = Nil | Atom of 'a | Cons of sexp => sexp`,     *)
(*        fixities = [Prefix,Prefix,Prefix],                                *)
(*        accessors = [("Atom",["Tok"]),("Cons",["Car","Cdr"])]};           *)
(*                                                                          *)
(* This results in the following theorems being stored in the current       *)
(* theory (or these are the theorems the function would expect to find in   *)
(* the theory hierarchy if the type already exists):                        *)
(*                                                                          *)
(*    sexp               (type axiom)                                       *)
(*    sexp_Induct        (induction theorem)                                *)
(*    sexp_one_one       (injectivity of constructors)                      *)
(*    sexp_distinct      (distinctness of constructors)                     *)
(*    sexp_cases         (cases theorem)                                    *)
(*                                                                          *)
(* The following definitions for the accessor functions are also stored:    *)
(*                                                                          *)
(*    Tok                |- !x. Tok (Atom x) = x                            *)
(*    Car                |- !s1 s2. Car (Cons s1 s2) = s1                   *)
(*    Cdr                |- !s1 s2. Cdr (Cons s1 s2) = s2                   *)
(*                                                                          *)
(* In certain cases the distinctness or injectivity theorems may not exist, *)
(* when nothing is saved for them.                                          *)
(*                                                                          *)
(* Finally, a new Boyer-Moore shell is added based on the definitions and   *)
(* theorems.                                                                *)
(*--------------------------------------------------------------------------*)
(* Altered for hol98 *)
fun define_shell {name,type_spec,fixities,accessors} =
   let
(*     fun find_theory s =
          let fun f s [] = failwith "find_theory"
                | f s (thy::thys) =
                 if can (theorem thy) s
                 then thy
                 else f s thys
          in  f s (current_theory () :: ancestry "-")
          end
*)
  fun find_theory s = failwith "define_shell.find_theory"
       fun mk_def_eq (name,comb,arg) =
          let val ty = mk_type ("fun",[type_of comb,type_of arg])
          in  mk_eq (mk_comb (Rsyntax.mk_var {Name = name,Ty = ty},comb),arg)
          end
       fun define_accessor axiom (name,tm) =
          (name,Rsyntax.new_recursive_definition
                   {name = name,rec_axiom = axiom,def = tm})
       fun define_accessors axiom (comb,specs) =
          map (fn (name,arg) =>
                  define_accessor axiom (name,mk_def_eq (name,comb,arg)))
             specs
   in
   if (mem name (shells ()))
   then failwith "define_shell -- shell already exists"
   else
   let val defined = is_type name
   (* NEW for HOL98 *)
       val _ = if defined
               then failwith ("define_shell -- type already defined!")
               else ();
       val theory =
          if defined
          then (find_theory name handle HOL_ERR _ =>
                failwith ("define_shell -- no axiom found for type " ^ name))
          else current_theory ()
       val name_Axiom =
          if defined
          then failwith "define_shell" (* theorem theory name *)
          else define_type
                  {name = name,fixities = fixities,type_spec = type_spec}
       val name_Induct =
          if defined
          then failwith "define_shell" (* theorem theory (name ^ "_Induct") *)
          else save_thm (name ^ "_Induct",prove_induction_thm name_Axiom)
       and name_one_ones =
          if defined
          then failwith "define_shell"
           (* (CONJUNCTS (theorem theory (name ^ "_one_one"))
                handle e => if (can prove_constructors_one_one name_Axiom)
                            then raise e
                            else [])
           *)
          else ((CONJUNCTS o save_thm)
                   ((name ^ "_one_one"),prove_constructors_one_one name_Axiom)
                handle HOL_ERR _ => [])
       and name_distincts =
          if defined
          then failwith "define_shell"
            (* (CONJUNCTS (theorem theory (name ^ "_distinct"))
                handle e => if (can prove_constructors_distinct name_Axiom)
                            then raise e
                            else [])
            *)
          else ((CONJUNCTS o save_thm)
                   (name ^ "_distinct",prove_constructors_distinct name_Axiom)
                handle HOL_ERR _ => [])
       val name_cases =
          if defined
          then failwith "define_shell" (* theorem theory (name ^ "_cases") *)
          else save_thm (name ^ "_cases",prove_cases_thm name_Induct)
       val ty = (type_of o #1 o dest_forall o concl) name_cases
       val ty_args = #Args (Rsyntax.dest_type ty)
       val cases = (strip_disj o #2 o dest_forall o concl) name_cases
       val combs = map (rhs o #2 o strip_exists) cases
       val constrs_and_args =
          map (((#Name o Rsyntax.dest_const) ## I) o strip_comb) combs
       val (constrs,arg_types) =
          split (map (I ## map type_of) constrs_and_args)
       val acc_specs =
          map (fn (c,args) =>
                  (combine (assoc c accessors handle NOT_FOUND => [],args)
                   handle HOL_ERR _ =>
                   failwith
                      ("define_shell -- " ^
                       "incorrect number of accessors for constructor " ^ c)))
             constrs_and_args
       val acc_defs =
          if defined
          then failwith "define_shell"
             (* map (map ((fn acc => (acc,definition theory acc)) o #1))
                  acc_specs *)
          else map (define_accessors name_Axiom) (combine (combs,acc_specs))
       val name_shell =
          Shell (name,
                 {arg_types = ty_args,
                  constructors =
                     map (fn (n,(t,a)) => (n,t,a))
                        (combine (constrs,combine (arg_types,acc_defs))),
                  axiom = name_Axiom,induct = name_Induct,cases = name_cases,
                  distinct = name_distincts,one_one = name_one_ones,
                  struct_conv = BoyerMooreStructEqual.ONE_STEP_RECTY_EQ_CONV
                                   (name_Induct,name_distincts,name_one_ones)})
   in  system_shells := name_shell::(!system_shells)
   end
   end;

end;

end; (* BoyerMooreShells *)
