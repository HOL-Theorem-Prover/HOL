(****************************************************************************)
(* FILE          : environment.sml                                          *)
(* DESCRIPTION   : Environment of definitions and pre-proved theorems for   *)
(*                 use in automation.                                       *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 8th May 1991                                             *)
(*                                                                          *)
(* TRANSLATED BY : R.J.Boulton                                              *)
(* DATE          : 3rd October 1995                                         *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 4th October 1995                                         *)
(****************************************************************************)

structure BoyerMooreEnvironment =
struct

local

open HolKernel Parse basicHol90Lib Psyntax BoyerMooreSupport;;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;


fun failwith function =
   raise HOL_ERR {origin_structure = "BoyerMooreEnvironment",
                  origin_function = function,
                  message = ""};

in

(*--------------------------------------------------------------------------*)
(* Reference variable to hold the defining theorems for operators currently *)
(* defined within the system. Each definition is stored as a triple. The    *)
(* first component is the name of the operator. The second is the number of *)
(* the recursive argument. If the operator is not defined recursively, this *)
(* number is zero. The third component is a list of pairs of type           *)
(* constructor names and the theorems that define the behaviour of the      *)
(* operator for each constructor. If the operator is not recursive, the     *)
(* constructor names are empty (null) strings.                              *)
(*--------------------------------------------------------------------------*)

val system_defs = ref ([] : (string * (int * (string * thm) list)) list);

(*--------------------------------------------------------------------------*)
(* new_def : thm -> unit                                                    *)
(*                                                                          *)
(* Make a new definition available. Checks that theorem has no hypotheses,  *)
(* then splits it into conjuncts. The variables for each conjunct are       *)
(* specialised and then the conjuncts are made into equations.              *)
(*                                                                          *)
(* For each equation, a triple is obtained, consisting of the name of the   *)
(* function on the LHS, the number of the recursive argument, and the name  *)
(* of the constructor used in that argument. This process fails if the LHS  *)
(* is not an application of a constant (possibly to zero arguments), or if  *)
(* more than one of the arguments is anything other than a variable. The    *)
(* argument that is not a variable must be an application of a constructor. *)
(* If the function is not recursive, the argument number returned is zero.  *)
(*                                                                          *)
(* Having obtained a triple for each equation, a check is made that the     *)
(* first two components are the same for each equation. Then, the equations *)
(* are saved together with constructor names for each, and the name of the  *)
(* operator being defined, and the number of the recursive argument.        *)
(*--------------------------------------------------------------------------*)

fun new_def th =
   let fun make_into_eqn th =
          let val tm = concl th
          in  if (is_eq tm) then th
              else if (is_neg tm) then EQF_INTRO th
              else EQT_INTRO th
          end
       and get_constructor th =
          let val tm = lhs (concl th)
              val (f,args) = strip_comb tm
              val name = #Name (Rsyntax.dest_const f)
              val bools = number_list (map is_var args)
              val i = itlist (fn (b,i) => fn n =>
                                 if ((not b) andalso (n = 0))
                                 then i
                                 else if b then n else failwith "") bools 0
          in  if (i = 0)
              then ((name,i),"")
              else ((name,i),
                    #Name (Rsyntax.dest_const (#1 (strip_comb (el i args)))))
          end
       val tm = case (dest_thm th) of ([],tm) => tm | _ => failwith ""
       val ths = CONJ_LIST (length (conj_list tm)) th
       val ths' = map SPEC_ALL ths
       val eqs = map make_into_eqn ths'
       val constructs = map get_constructor eqs
       val (xl,yl) = (mk_set ## I) (split constructs)
       val (name,i) = if (length xl = 1) then (hd xl) else failwith ""
   in  system_defs := (name,(i,combine (yl,eqs)))::(!system_defs)
   end
   handle HOL_ERR _ => failwith "new_def";

(*--------------------------------------------------------------------------*)
(* defs : unit -> thm list list                                             *)
(*                                                                          *)
(* Returns a list of lists of theorems currently being used as definitions. *)
(* Each list in the list is for one operator.                               *)
(*--------------------------------------------------------------------------*)

fun defs () = map ((map #2) o #2 o #2) (!system_defs);

(*--------------------------------------------------------------------------*)
(* get_def : string -> (string * (int * (string * thm) list))               *)
(*                                                                          *)
(* Function to obtain the definition information of a named operator.       *)
(*--------------------------------------------------------------------------*)

fun get_def name =
   (name,assoc name (!system_defs)) handle NOT_FOUND => failwith "get_def";

(*--------------------------------------------------------------------------*)
(* Reference variable for a list of theorems currently proved in the        *)
(* system. These theorems are available to the automatic proof procedures   *)
(* for use as rewrite rules. The elements of the list are actually pairs of *)
(* theorems. The first theorem is that specified by the user. The second is *)
(* an equivalent theorem in a standard form.                                *)
(*--------------------------------------------------------------------------*)

val system_rewrites = ref ([] : (thm * thm) list);

(*--------------------------------------------------------------------------*)
(* CONJ_IMP_IMP_IMP = |- x /\ y ==> z = x ==> y ==> z                       *)
(*--------------------------------------------------------------------------*)

val CONJ_IMP_IMP_IMP =
   prove
      ((--`((x /\ y) ==> z) = (x ==> (y ==> z))`--),
       BOOL_CASES_TAC (--`x:bool`--) THEN
       BOOL_CASES_TAC (--`y:bool`--) THEN
       BOOL_CASES_TAC (--`z:bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* CONJ_UNDISCH : thm -> thm                                                *)
(*                                                                          *)
(* Undischarges the conjuncts of the antecedant of an implication.          *)
(* e.g. |- x /\ (y /\ z) /\ w ==> x  --->  x, y /\ z, w |- x                *)
(*                                                                          *)
(* Has to check for negations, because UNDISCH processes them when we don't *)
(* want it to.                                                              *)
(*--------------------------------------------------------------------------*)

fun CONJ_UNDISCH th =
   let val th' = CONV_RULE (REWR_CONV CONJ_IMP_IMP_IMP) th
       val th'' = UNDISCH th'
   in  CONJ_UNDISCH th''
   end
   handle HOL_ERR _ =>
   (if not (is_neg (concl th)) then UNDISCH th else failwith "")
   handle HOL_ERR _ => failwith "CONJ_UNDISCH";

(*--------------------------------------------------------------------------*)
(* new_rewrite_rule : thm -> unit                                           *)
(*                                                                          *)
(* Make a new rewrite rule available. Checks that the theorem has no        *)
(* hypotheses. The theorem is saved together with an equivalent theorem in  *)
(* a standard form. Theorems are fully generalized, then specialized with   *)
(* unique variable names (genvars), and then standardized as follows:       *)
(*                                                                          *)
(*    |- (h1 /\ ... /\ hn) ==> (l = r)  --->  h1, ..., hn |- l = r          *)
(*    |- (h1 /\ ... /\ hn) ==> ~b       --->  h1, ..., hn |- b = F          *)
(*    |- (h1 /\ ... /\ hn) ==> b        --->  h1, ..., hn |- b = T          *)
(*    |- l = r                          --->  |- l = r                      *)
(*    |- ~b                             --->  |- b = F                      *)
(*    |- b                              --->  |- b = T                      *)
(*                                                                          *)
(* A conjunction of rules may be given. The function will treat each        *)
(* conjunct in the theorem as a separate rule.                              *)
(*--------------------------------------------------------------------------*)

fun new_rewrite_rule th =
   (if (is_conj (concl th))
    then (map new_rewrite_rule (CONJUNCTS th); ())
    else let val tm = case (dest_thm th) of ([],tm) => tm | _ => failwith ""
             val th' = GSPEC (GEN_ALL th)
             val th'' = CONJ_UNDISCH th' handle HOL_ERR _ => th'
             val tm'' = concl th''
             val th''' =
                if (is_eq tm'') then th''
                else if (is_neg tm'') then EQF_INTRO th''
                else EQT_INTRO th''
         in  system_rewrites := (th,th''')::(!system_rewrites)
         end)
   handle HOL_ERR _ => failwith "new_rewrite_rule";

(*--------------------------------------------------------------------------*)
(* rewrite_rules : unit -> thm list                                         *)
(*                                                                          *)
(* Returns the list of theorems currently being used as rewrites, in the    *)
(* form they were originally given by the user.                             *)
(*--------------------------------------------------------------------------*)

fun rewrite_rules () = map #1 (!system_rewrites);

(*--------------------------------------------------------------------------*)
(* Reference variable to hold the generalisation lemmas currently known to  *)
(* the system.                                                              *)
(*--------------------------------------------------------------------------*)

val system_gen_lemmas = ref ([] : thm list);

(*--------------------------------------------------------------------------*)
(* new_gen_lemma : thm -> unit                                              *)
(*                                                                          *)
(* Make a new generalisation lemma available.                               *)
(* Checks that the theorem has no hypotheses.                               *)
(*--------------------------------------------------------------------------*)

fun new_gen_lemma th =
   if (null (hyp th))
   then system_gen_lemmas := th::(!system_gen_lemmas)
   else failwith "new_gen_lemma";

(*--------------------------------------------------------------------------*)
(* gen_lemmas : unit -> thm list                                            *)
(*                                                                          *)
(* Returns the list of theorems currently being used as                     *)
(* generalisation lemmas.                                                   *)
(*--------------------------------------------------------------------------*)

fun gen_lemmas () = !system_gen_lemmas;

end;

end; (* BoyerMooreEnvironment *)
