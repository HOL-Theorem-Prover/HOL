(****************************************************************************)
(* FILE          : rewrite_rules.sml                                        *)
(* DESCRIPTION   : Using axioms and lemmas as rewrite rules.                *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 14th May 1991                                            *)
(*                                                                          *)
(* TRANSLATED BY : R.J.Boulton                                              *)
(* DATE          : 3rd October 1995                                         *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 4th October 1995                                         *)
(****************************************************************************)

structure BoyerMooreRewriteRules =
struct

local

open HolKernel Parse basicHol90Lib Psyntax BoyerMooreSupport;
infix THEN ;

fun failwith function =
   raise HOL_ERR {origin_structure = "BoyerMooreRewriteRules",
                  origin_function = function,
                  message = ""};

in

(*--------------------------------------------------------------------------*)
(* is_permutative : term -> bool                                            *)
(*                                                                          *)
(* Determines whether or not an equation is permutative (the left-hand and  *)
(* right-hand sides are instances of one another). A permutative equation   *)
(* may cause looping when it is used for rewriting.                         *)
(*--------------------------------------------------------------------------*)

fun is_permutative tm =
   let val (l,r) = dest_eq tm
       val bind1 = match_term l r
       and bind2 = match_term r l
   in  true
   end
   handle HOL_ERR _ => false;

(*--------------------------------------------------------------------------*)
(* lex_smaller_term : term -> term -> bool                                  *)
(*                                                                          *)
(* Computes whether the first term is `alphabetically' smaller than the     *)
(* second term. Used to avoid looping when rewriting with permutative       *)
(* rules.                                                                   *)
(*                                                                          *)
(* A constant is considered to be smaller than a variable which in turn is  *)
(* considered to be smaller than an application. Two variables or two       *)
(* constants are compared alphabetically by name. An application (f1 x1) is *)
(* considered to be smaller than another application (f2 x2) if either f1   *)
(* is smaller than f2, or f1 equals f2 and x1 is smaller than x2.           *)
(*--------------------------------------------------------------------------*)

fun lex_smaller_term tm1 tm2 =
   (case (dest_term tm1)
    of CONST {Name = name1,Ty = type1} =>
       if (is_const tm2)
       then let val {Name = name2,Ty = type2} = Rsyntax.dest_const tm2
            in  if (type1 = type2)
                then name1 < name2
                else failwith ""
            end
       else true
     | VAR {Name = name1,Ty = type1} =>
       if (is_const tm2)
       then false
       else if (is_var tm2)
            then let val {Name = name2,Ty = type2} = Rsyntax.dest_var tm2
                 in  if (type1 = type2)
                     then name1 < name2
                     else failwith ""
                 end
            else true
     | COMB {Rator = rator1,Rand = rand1} =>
       if (is_comb tm2)
       then let val {Rator = rator2,Rand = rand2} = Rsyntax.dest_comb tm2
            in  (lex_smaller_term rator1 rator2) orelse
                ((rator1 = rator2) andalso (lex_smaller_term rand1 rand2))
            end
       else false
     | LAMB _ => failwith "")
   handle HOL_ERR _ => failwith "lex_smaller_term";

(*--------------------------------------------------------------------------*)
(* inst_eq_thm :                                                            *)
(*    ((term * term) list * (hol_type * hol_type) list) -> thm -> thm       *)
(*                                                                          *)
(* Instantiates a theorem (possibly having hypotheses) with a binding.      *)
(* Assumes the conclusion is an equality, so that discharging then          *)
(* undischarging cannot cause parts of the conclusion to be moved into the  *)
(* hypotheses.                                                              *)
(*--------------------------------------------------------------------------*)

fun inst_eq_thm (tm_bind,ty_bind) th =
   let val (insts,vars) = split tm_bind
   in  (UNDISCH_ALL o (SPECL insts) o (GENL vars) o
        (INST_TYPE ty_bind) o DISCH_ALL) th
   end;

(*--------------------------------------------------------------------------*)
(* applicable_rewrites : term -> thm list                                   *)
(*                                                                          *)
(* Returns the results of rewriting the term with those rewrite rules that  *)
(* are applicable to it. A rewrite rule is not applicable if it's           *)
(* permutative and the rewriting does not produce an alphabetically smaller *)
(* term.                                                                    *)
(*--------------------------------------------------------------------------*)

fun applicable_rewrites tm =
   let fun applicable_rewrite tm th =
          let val conc = concl th
              val instth = inst_eq_thm (match_term (lhs conc) tm) th
          in  if (is_permutative conc)
              then let val (l,r) = dest_eq (concl instth)
                   in  if (lex_smaller_term r l)
                       then instth
                       else failwith ""
                   end
              else instth
          end
   in  mapfilter (applicable_rewrite tm o #2)
          (!BoyerMooreEnvironment.system_rewrites)
   end;

(*--------------------------------------------------------------------------*)
(* assump_inst_hyps : term list ->                                          *)
(*                    term ->                                               *)
(*                    term list ->                                          *)
(*                    ((term * term) list * (hol_type * hol_type) list)     *)
(*                                                                          *)
(* Searches a list of hypotheses for one that matches the specified         *)
(* assumption such that the variables instantiated are precisely those in   *)
(* the list of variables given. If such a hypothesis is found, the binding  *)
(* produced by the match is returned.                                       *)
(*--------------------------------------------------------------------------*)

fun assump_inst_hyps vars assump [] = failwith "assump_inst_hyps"
  | assump_inst_hyps vars assump (hyp::hyps) =
   let val bind = match_term hyp assump
   in  if (set_eq vars (map #2 (#1 bind)))
       then bind
       else failwith ""
   end
   handle HOL_ERR _ => assump_inst_hyps vars assump hyps;

(*--------------------------------------------------------------------------*)
(* assumps_inst_hyps : term list ->                                         *)
(*                     term list ->                                         *)
(*                     term list ->                                         *)
(*                     ((term * term) list * (hol_type * hol_type) list)    *)
(*                                                                          *)
(* Searches a list of hypotheses and a list of assumptions for a pairing    *)
(* that match (the assumption is an instance of the hypothesis) such that   *)
(* the variables instantiated are precisely those in the list of variables  *)
(* given. If such a pair is found, the binding produced by the match is     *)
(* returned.                                                                *)
(*--------------------------------------------------------------------------*)

fun assumps_inst_hyps vars [] hyps = failwith "assumps_inst_hyps"
  | assumps_inst_hyps vars (assump::assumps) hyps =
   assump_inst_hyps vars assump hyps
   handle HOL_ERR _ => assumps_inst_hyps vars assumps hyps;

(*--------------------------------------------------------------------------*)
(* inst_frees_in_hyps : term list -> thm -> thm                             *)
(*                                                                          *)
(* Takes a theorem (possibly with hypotheses) and computes a list of        *)
(* variables that are free in the hypotheses but not in the conclusion.     *)
(* If this list of variables is empty the original theorem is returned.     *)
(* The function also takes a list of assumptions as another argument. Once  *)
(* it has the list of variables it searches for an assumption and a         *)
(* hypothesis such that the hypothesis matches the assumption binding       *)
(* precisely those variables in the list. If this is successful the         *)
(* original theorem is returned having had the variables in the list        *)
(* instantiated.                                                            *)
(*--------------------------------------------------------------------------*)

fun inst_frees_in_hyps assumps th =
   let val hyps = hyp th
       val hyp_frees = mk_set (flatten (map free_vars hyps))
       val vars = subtract hyp_frees (free_vars (concl th))
   in  if (null vars)
       then th
       else let val bind = assumps_inst_hyps vars assumps hyps
            in  inst_eq_thm bind th
            end
   end
   handle HOL_ERR _ => failwith "inst_frees_in_hyps";

(*--------------------------------------------------------------------------*)
(* NOT_IMP_EQ_EQ_EQ_OR = |- (~x ==> (y = y')) = ((y \/ x) = (y' \/ x))      *)
(*--------------------------------------------------------------------------*)

val NOT_IMP_EQ_EQ_EQ_OR =
   prove
      ((--`(~x ==> (y = y')) = ((y \/ x) = (y' \/ x))`--),
       BOOL_CASES_TAC (--`x:bool`--) THEN
       BOOL_CASES_TAC (--`y:bool`--) THEN
       BOOL_CASES_TAC (--`y':bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* IMP_EQ_EQ_EQ_OR_NOT = |- (x ==> (y = y')) = ((y \/ ~x) = (y' \/ ~x))     *)
(*--------------------------------------------------------------------------*)

val IMP_EQ_EQ_EQ_OR_NOT =
   prove
      ((--`(x ==> (y = y')) = ((y \/ ~x) = (y' \/ ~x))`--),
       BOOL_CASES_TAC (--`x:bool`--) THEN
       BOOL_CASES_TAC (--`y:bool`--) THEN
       BOOL_CASES_TAC (--`y':bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* NOT_IMP_EQ_OR_EQ_EQ_OR_OR =                                              *)
(* |- (~x ==> ((y \/ t) = (y' \/ t))) = ((y \/ (x \/ t)) = (y' \/ (x \/ t)))*)
(*--------------------------------------------------------------------------*)

val NOT_IMP_EQ_OR_EQ_EQ_OR_OR =
   prove
      ((--`(~x ==> ((y \/ t) = (y' \/ t))) =
           ((y \/ (x \/ t)) = (y' \/ (x \/ t)))`--),
       BOOL_CASES_TAC (--`x:bool`--) THEN
       BOOL_CASES_TAC (--`y:bool`--) THEN
       BOOL_CASES_TAC (--`y':bool`--) THEN
       BOOL_CASES_TAC (--`t:bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* IMP_EQ_OR_EQ_EQ_OR_NOT_OR =                                              *)
(* |- (x ==> ((y \/ t) = (y' \/ t))) =                                      *)
(*    ((y \/ (~x \/ t)) = (y' \/ (~x \/ t)))                                *)
(*--------------------------------------------------------------------------*)

val IMP_EQ_OR_EQ_EQ_OR_NOT_OR =
   prove
      ((--`(x ==> ((y \/ t) = (y' \/ t))) =
           ((y \/ (~x \/ t)) = (y' \/ (~x \/ t)))`--),
       BOOL_CASES_TAC (--`x:bool`--) THEN
       BOOL_CASES_TAC (--`y:bool`--) THEN
       BOOL_CASES_TAC (--`y':bool`--) THEN
       BOOL_CASES_TAC (--`t:bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* IMP_EQ_EQ_EQ_NOT_OR = |- (x ==> (t = t')) = ((~x \/ t) = (~x \/ t'))     *)
(*--------------------------------------------------------------------------*)

val IMP_EQ_EQ_EQ_NOT_OR =
   prove
      ((--`(x ==> (t = t')) = ((~x \/ t) = (~x \/ t'))`--),
       BOOL_CASES_TAC (--`x:bool`--) THEN
       BOOL_CASES_TAC (--`t:bool`--) THEN
       BOOL_CASES_TAC (--`t':bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* IMP_NOT_EQ_EQ_EQ_OR = |- (~x ==> (t = t')) = ((x \/ t) = (x \/ t'))      *)
(*--------------------------------------------------------------------------*)

val IMP_NOT_EQ_EQ_EQ_OR =
   prove
      ((--`(~x ==> (t = t')) = ((x \/ t) = (x \/ t'))`--),
       BOOL_CASES_TAC (--`x:bool`--) THEN
       BOOL_CASES_TAC (--`t:bool`--) THEN
       BOOL_CASES_TAC (--`t':bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* T_OR = |- T \/ t = T                                                     *)
(* OR_T = |- t \/ T = T                                                     *)
(* F_OR = |- F \/ t = t                                                     *)
(* OR_F = |- t \/ F = t                                                     *)
(*--------------------------------------------------------------------------*)

val (T_OR,OR_T,F_OR,OR_F) =
   case (CONJUNCTS (SPEC_ALL OR_CLAUSES))
   of [T_OR,OR_T,F_OR,OR_F,_] => (T_OR,OR_T,F_OR,OR_F)
    | _ => raise Bind;

(*--------------------------------------------------------------------------*)
(* UNDER_DISJ_DISCH : term -> thm -> thm                                    *)
(*                                                                          *)
(*    A, ~x |- y \/ t = y' \/ t          A, x |- y \/ t = y' \/ t           *)
(*    -------------------------------    ---------------------------------  *)
(*    A |- y \/ x \/ t = y' \/ x \/ t    A |- y \/ ~x \/ t = y' \/ ~x \/ t  *)
(*                                                                          *)
(*    A, ~x |- y = y'                    A, x |- y = y'                     *)
(*    ---------------------              -----------------------            *)
(*    A |- y \/ x = y' \/ x              A |- y \/ ~x = y' \/ ~x            *)
(*                                                                          *)
(* The function assumes that y is a literal, so it is valid to test the LHS *)
(* of the theorem to see if it is a disjunction in order to determine which *)
(* rule to use.                                                             *)
(*--------------------------------------------------------------------------*)

fun UNDER_DISJ_DISCH tm th =
   let val rewrite =
          if (is_disj (lhs (concl th)))
          then if (is_neg tm)
               then NOT_IMP_EQ_OR_EQ_EQ_OR_OR
               else IMP_EQ_OR_EQ_EQ_OR_NOT_OR
          else if (is_neg tm)
               then NOT_IMP_EQ_EQ_EQ_OR
               else IMP_EQ_EQ_EQ_OR_NOT
   in  CONV_RULE (REWR_CONV rewrite) (DISCH tm th)
   end
   handle HOL_ERR _ => failwith "UNDER_DISJ_DISCH";

(*--------------------------------------------------------------------------*)
(* OVER_DISJ_DISCH : term -> thm -> thm                                     *)
(*                                                                          *)
(*    A, ~x |- t = t'                    A, x |- t = t'                     *)
(*    ---------------------              -----------------------            *)
(*    A |- x \/ t = x \/ t'              A |- ~x \/ t = ~x \/ t'            *)
(*--------------------------------------------------------------------------*)

fun OVER_DISJ_DISCH tm th =
   let val rewrite =
          if (is_neg tm)
          then IMP_NOT_EQ_EQ_EQ_OR
          else IMP_EQ_EQ_EQ_NOT_OR
   in  CONV_RULE (REWR_CONV rewrite) (DISCH tm th)
   end
   handle HOL_ERR _ => failwith "OVER_DISJ_DISCH";

(*--------------------------------------------------------------------------*)
(* MULTI_DISJ_DISCH : (term list * term list) -> thm -> thm                 *)
(*                                                                          *)
(* Examples:                                                                *)
(*                                                                          *)
(*    MULTI_DISJ_DISCH ([(--`x1`--),(--`x2`--)],[(--`~x3`--),(--`x4`--)])   *)
(*       x1, ~x3, x4, x2 |- y = y'                                          *)
(*    --->                                                                  *)
(*    |- ~x1 \/ ~x2 \/ y \/ x3 \/ ~x4 = ~x1 \/ ~x2 \/ y' \/ x3 \/ ~x4       *)
(*                                                                          *)
(*                                                                          *)
(*    MULTI_DISJ_DISCH ([(--`x1`--),(--`x2`--)],[(--`~x3`--),(--`x4`--)])   *)
(*       x1, ~x3, x4, x2 |- y = F                                           *)
(*    --->                                                                  *)
(*    |- ~x1 \/ ~x2 \/ y \/ x3 \/ ~x4 = ~x1 \/ ~x2 \/ x3 \/ ~x4             *)
(*                                                                          *)
(*                                                                          *)
(*    MULTI_DISJ_DISCH ([(--`x1`--),(--`x2`--)],[(--`~x3`--),(--`x4`--)])   *)
(*       x1, ~x3, x4, x2 |- y = T                                           *)
(*    --->                                                                  *)
(*    |- ~x1 \/ ~x2 \/ y \/ x3 \/ ~x4 = T                                   *)
(*--------------------------------------------------------------------------*)

fun MULTI_DISJ_DISCH (overs,unders) th =
   let val th1 = itlist UNDER_DISJ_DISCH unders th
       val tm1 = rhs (concl th1)
       val th2 = 
          if (is_T (#1 (dest_disj tm1)) handle HOL_ERR _ => false) then
             (CONV_RULE (RAND_CONV (REWR_CONV T_OR)) th1)
          else if (is_F (#1 (dest_disj tm1)) handle HOL_ERR _ => false) then
             (CONV_RULE (RAND_CONV (REWR_CONV F_OR)) th1)
          else th1
       val tm2 = rhs (concl th2)
       val rule =
          if (is_T tm2) then CONV_RULE (RAND_CONV (REWR_CONV OR_T)) else I
   in  itlist (fn tm => fn th => rule (OVER_DISJ_DISCH tm th)) overs th2
   end
   handle HOL_ERR _ => failwith "MULTI_DISJ_DISCH";

end;

end; (* BoyerMooreRewriteRules *)
