(****************************************************************************)
(* FILE          : decide.sml                                               *)
(* DESCRIPTION   : Combining decision procedures as described by Nelson and *)
(*                 Oppen (ACM TOPLAS 1(2), 1979, pp245-257).                *)
(*                                                                          *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                     *)
(* DATE          : 23rd February 1995                                       *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton, University of Edinburgh                     *)
(* DATE          : 24th February 1999                                       *)
(****************************************************************************)

structure Decide =
struct

local

open HolKernel Parse basicHol90Lib
     Portable_List Psyntax DecisionConv DecisionSupport DecisionNormConvs
infix THEN THENL THENC
in

fun failwith function = raise HOL_ERR{origin_structure = "Decide",
                                      origin_function = function,
                                      message = ""};

(*==========================================================================*)
(* Types for decision procedure                                             *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* Inputs to an incremental decision procedure.                             *)
(*--------------------------------------------------------------------------*)

datatype request =
   ProveFalse | GetEquality | GetEqualities | AddEquality of LazyThm.pre_thm;

(*--------------------------------------------------------------------------*)
(* Outputs from an incremental decision procedure.                          *)
(*--------------------------------------------------------------------------*)

datatype response = Thm of LazyThm.pre_thm | None;

(*--------------------------------------------------------------------------*)
(* Recursive type of incremental decision procedures.                       *)
(*--------------------------------------------------------------------------*)

datatype incremental_procedure =
   Increment of request -> response * incremental_procedure;

(*--------------------------------------------------------------------------*)
(* apply_procedure :                                                        *)
(*    incremental_procedure -> request -> response * incremental_procedure  *)
(*                                                                          *)
(* Applying an incremental decision procedure.                              *)
(*--------------------------------------------------------------------------*)

fun apply_procedure (Increment f) req = f req;

(*--------------------------------------------------------------------------*)
(* Type alias for record structure containing information about a decision  *)
(* procedure.                                                               *)
(*                                                                          *)
(* The Boolean argument taken by the Discriminator function tells it the    *)
(* context in which discrimination is taking place. When finding out to     *)
(* which theory a term belongs the argument will be set to true if no       *)
(* previous (i.e. higher priority) procedure recognised the term; otherwise *)
(* the argument will be false. When processing a term to find the           *)
(* heterogeneous subterms the argument will be set to true if processing    *)
(* the root of the term and to false if processing a strict subterm. This   *)
(* allows the discriminator to reject a subterm that may belong to a higher *)
(* priority procedure.                                                      *)
(*                                                                          *)
(* The theorem taken as argument by the Procedure function should have the  *)
(* full conjunction to be proved as an assumption and the subconjunction to *)
(* which the procedure is applicable as its conclusion.                     *)
(*--------------------------------------------------------------------------*)

type decision_procedure =
   {Name : string,
    Description : string,
    Author : string,
    Discriminator : bool -> term -> (term list -> term) * term list,
    Normalizer : conv,
    Procedure : thm -> incremental_procedure};

(*==========================================================================*)
(* Making a literal homogeneous                                             *)
(*==========================================================================*)

fun new_var s =
   let val n = ref 0
       fun inc () = (n := !n + 1; !n)
       fun new existing ty =
          let val name = s ^ int_to_string (inc ())
          in  if (member name existing)
              then new existing ty
              else mk_var (name,ty)
          end
   in  new
   end;

val SEPARATE_SUBTERM_THM =
   prove (--`!P t. P t = (?(v:'a). (P v) /\ (v = t))`--,
          REPEAT GEN_TAC THEN EQ_TAC THENL
          [DISCH_TAC THEN EXISTS_TAC (--`t:'a`--) THEN ASM_REWRITE_TAC [],
           CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
           CONV_TAC NOT_EXISTS_CONV THEN GEN_TAC THEN
           ASM_CASES_TAC (--`(v:'a) = t`--) THEN ASM_REWRITE_TAC []]);

exception Discriminate;

fun discriminate ps tm =
   let fun discrim _ _ [] = []
         | discrim unknown n ((p : decision_procedure)::ps) =
          (#Discriminator p unknown tm; (n,p) :: discrim false (n + 1) ps)
          handle _ => discrim unknown (n + 1) ps
   in  discrim true 1 ps
   end;

fun discriminate_unique ps tm =
   hd (discriminate ps tm) handle Empty => raise Discriminate;

fun top_level_discriminate ps tm =
   if (is_neg tm)
   then top_level_discriminate ps (rand tm)
   else if (is_eq tm)
        then let val (l,r) = dest_eq tm
                 val npsl = discriminate ps l
                 and npsr = discriminate ps r
                 val ns = intersect (map #1 npsl) (map #1 npsr)
             in  if (null ns)
                 then if not (is_var l) andalso not (is_var r) andalso
                         not (null npsl) andalso not (null npsr)
                      then let val npsl1 = hd npsl
                               and npsr1 = hd npsr
                           in  if (#1 npsl1 <= #1 npsr1)
                               then npsl1
                               else npsr1
                           end
                      else raise Discriminate
                 else let val n = foldl Portable_Int.min (hd ns) (tl ns)
                      in  (n,assoc n (npsl @ npsr))
                      end
             end
        else discriminate_unique ps tm;

(*--------------------------------------------------------------------------*)
(* HOMOGENIZE_CONV :                                                        *)
(*    (string list -> hol_type -> term) -> decision_procedure list -> conv  *)
(*                                                                          *)
(* Make a literal homogeneous.                                              *)
(*--------------------------------------------------------------------------*)

fun HOMOGENIZE_CONV new_var (procedures : decision_procedure list) tm =
   let val new = new_var (map (#Name o Rsyntax.dest_var) (free_vars tm))
       fun find_heterogeneities at_root d tm =
          if (is_neg tm) then
             let val (template,subst) =
                    find_heterogeneities at_root d (rand tm)
             in  (mk_neg template,subst)
             end
          else if (is_eq tm) then
             let val (template1,subst1) =
                    find_heterogeneities at_root d (arg1 tm)
                 and (template2,subst2) =
                    find_heterogeneities at_root d (arg2 tm)
             in  (mk_eq (template1,template2),subst1 @ subst2)
             end
          else let val (construct,subterms) = d at_root tm
                   val (templates,substs) =
                      unzip (map (find_heterogeneities false d) subterms)
               in  (construct templates,flat substs)
               end
               handle HOL_ERR _
                 => let val v = new (type_of tm) in (v,[(v,tm)]) end
       fun SEPARATE_SUBTERM template (v,t) =
          let val P = mk_abs (v,template)
              val th1 = ISPECL [P,t] SEPARATE_SUBTERM_THM
          in  CONV_RULE
                 (ARGS_CONV
                     [BETA_CONV,
                      RAND_CONV (ALPHA_CONV v THENC
                                 ABS_CONV (ARGS_CONV [BETA_CONV,HOMOG_CONV]))
                     ]) th1
          end
       and SEPARATE_SUBTERMS normalize template subst =
          let fun INSERT th1 th2 =
                 RIGHT_CONV_RULE (BINDER_CONV (LEFT_CONV (fn _ => th1))) th2
          in  foldl (fn (vt,th) =>
                        INSERT th (SEPARATE_SUBTERM (lhs (concl th)) vt))
                 (RULE_OF_CONV normalize template) subst
          end
       and HOMOG_CONV tm =
          let val (_,{Discriminator,Normalizer,...}) =
                 top_level_discriminate procedures tm
              val (template,subst) = find_heterogeneities true Discriminator tm
          in  SEPARATE_SUBTERMS Normalizer template subst
          end
          handle Discriminate => REFL tm
   in  HOMOG_CONV tm
   end;

(*==========================================================================*)
(* The co-operating decision procedure                                      *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* DEDUCE_SUBCONJ : thm list -> term -> thm                                 *)
(*                                                                          *)
(* Assumes conjuncts in the term are in the same order as in the list of    *)
(* theorems.                                                                *)
(*--------------------------------------------------------------------------*)

fun DEDUCE_SUBCONJ ths =
   let fun find_thm [] tm = failwith "DEDUCE_SUBCONJ"
         | find_thm (th::ths) tm =
          if (tm = concl th) then (th,ths) else find_thm ths tm
       fun traverse ths tm =
          if (is_conj tm)
          then let val (tm1,tm2) = dest_conj tm
                   val (th1,ths1) = traverse ths tm1
                   val (th2,ths2) = traverse ths1 tm2
               in  (CONJ th1 th2,ths2)
               end
          else find_thm ths tm
   in  #1 o (traverse ths)
   end;

(*--------------------------------------------------------------------------*)
(* LIST_DISJ_CASES : thm -> thm list -> thm                                 *)
(*                                                                          *)
(*     A |- t1 \/ ... \/ tn     A1 u {t1} |- t  ...  An u {tn} |- t         *)
(*    --------------------------------------------------------------        *)
(*                        A u A1 u ... u An |- t                            *)
(*--------------------------------------------------------------------------*)

local
   open LazyThm LazyRules
in

fun LIST_DISJ_CASES disjth [] = failwith "LIST_DISJ_CASES"
  | LIST_DISJ_CASES disjth [th] = MP (DISCH (concl disjth) th) disjth
  | LIST_DISJ_CASES disjth (th::ths) =
   let fun disj_in_hyps disj [] = failwith "LIST_DISJ_CASES"
         | disj_in_hyps disj [th] = th
         | disj_in_hyps disj (th::ths) =
          DISJ_CASES (ASSUME disj) th (disj_in_hyps (#2 (dest_disj disj)) ths)
   in  DISJ_CASES disjth th (disj_in_hyps (#2 (dest_disj (concl disjth))) ths)
   end;

end;

(*--------------------------------------------------------------------------*)
(* DECIDE_HOMOGENEOUS_CONV : bool -> (term * decision_procedure -> int) ->  *)
(*                           decision_procedure list -> conv                *)
(*                                                                          *)
(* The core co-operation procedure.                                         *)
(* Attempts to refute a homogeneous conjunction of literals.                *)
(*--------------------------------------------------------------------------*)

fun DECIDE_HOMOGENEOUS_CONV debug weight
       (procedures : decision_procedure list) tm =
   let fun spaces n = if (n <= 0) then "" else " " ^ spaces (n - 1)
       val debug_print = if debug then say else (fn _ => ())
       and debug_print_thm = if debug then print_thm else (fn _ => ())
       and debug_print_term = if debug then print_term else (fn _ => ())
       val deduce = DEDUCE_SUBCONJ (CONJUNCTS (ASSUME tm))
       val conjuncts = strip_conj tm
       val ns =
          map (fn t => (#1 (top_level_discriminate procedures t)
                        handle Discriminate => 0)) conjuncts
       val ncs = zip ns conjuncts
       val groups =
          map (fn count => map #2 (filter (fn (n,_) => n = count) ncs))
              (upto 1 (length procedures))
       val gps = filter (fn (g,_) => not (null g)) (zip groups procedures)
       val tps = map (fn (g,p) => (list_mk_conj g,p)) gps
       val weights = map weight tps
       val tps' =
          map #2
             (sort (fn (w1:int,_) => fn (w2,_) => w1 < w2) (zip weights tps))
       val (tms,procs) = unzip tps'
       val ths = map deduce tms
       val names = map #Name procs
       val name_size = 1 + foldl Portable_Int.max 0 (map size names)
       fun pad s = s ^ spaces (name_size - size s)
       val _ = (map (fn (name,th) => (debug_print (pad name);
                                      debug_print_thm th; debug_print "\n"))
                   (zip (map #Name procs) ths);
                debug_print "--------------------\n")
       val processes = map2 #Procedure procs ths
       fun try req [] = (None,[])
         | try req (p::ps) =
          let val (res,p') = apply_procedure p req
          in  case res
              of Thm _ => (res,p'::ps)
               | None =>
                 let val (res,ps') = try req ps
                 in  (res,p'::ps')
                 end
          end
       fun add_equality eqth p = #2 (apply_procedure p (AddEquality eqth))
       exception Cooperate
       fun cooperate ps =
          let val (res,ps1) = try ProveFalse ps
          in  case res
              of Thm th => th
               | None =>
                 let val (res,ps2) = try GetEquality ps1
                 in  case res
                     of Thm eqth =>
                        let val ps3 = map (add_equality eqth) ps2
                        in  debug_print_term (LazyThm.concl eqth);
                            debug_print "\n";
                            cooperate ps3
                        end
                      | None =>
                        let val (res,ps3) = try GetEqualities ps2
                        in  case res
                            of Thm casesth => case_split casesth ps3
                             | None => raise Cooperate
                        end
                 end
          end
       and case_split casesth ps =
          let val eqs = strip_disj (LazyThm.concl casesth)
              val eqths = map LazyRules.ASSUME eqs
              val pss = map (fn eqth => map (add_equality eqth) ps) eqths
              val ths = map cooperate pss
          in  LIST_DISJ_CASES casesth ths
          end
       val false_th =
          if (length processes <= 1)
          then case (#1 (try ProveFalse processes))
               of Thm th => th
                | None => failwith ""
          else cooperate processes handle Cooperate => failwith ""
   in  debug_print "========================================\n";
       CONV_RULE IMP_F_EQ_F_CONV (DISCH tm (LazyThm.prove_pre_thm false_th))
   end
   handle (HOL_ERR _) => failwith "DECIDE_HOMOGENEOUS_CONV";

(*--------------------------------------------------------------------------*)
(* NOT_T_F = |- ~T = F                                                      *)
(*--------------------------------------------------------------------------*)

val NOT_T_F = el 2 (CONJUNCTS NOT_CLAUSES);

(*--------------------------------------------------------------------------*)
(* NOT_F_T = |- ~F = T                                                      *)
(*--------------------------------------------------------------------------*)

val NOT_F_T = el 3 (CONJUNCTS NOT_CLAUSES);

(*--------------------------------------------------------------------------*)
(* NEGATE_CONV : conv -> conv                                               *)
(*                                                                          *)
(* Function for negating the operation of a conversion that proves a        *)
(* formula to be either true or false. For example if `conv' proves         *)
(* `0 <= n` to be equal to `T` then `NEGATE_CONV conv' will prove           *)
(* `~(0 <= n)` to be `F`. The function fails if the application of `conv'   *)
(* to the negation of the formula does not yield either `T` or `F`.         *)
(*                                                                          *)
(* If use of this function succeeds then the input term will necessarily    *)
(* have been changed. Hence it does not need to be a CONV. It can however   *)
(* take a CONV as its argument.                                             *)
(*--------------------------------------------------------------------------*)

fun NEGATE_CONV conv tm =
 let val neg = is_neg tm
     val th = RULE_OF_CONV conv (if neg then (dest_neg tm) else (mk_neg tm))
     val r = rhs (concl th)
     val truth_th =
        if (is_T r) then NOT_T_F
        else if (is_F r) then NOT_F_T
        else failwith "NEGATE_CONV"
     val neg_fn = if neg then I else TRANS (NOT_NOT_INTRO_CONV tm)
 in  neg_fn (TRANS (AP_TERM (--`$~`--) th) truth_th)
 end;

(*--------------------------------------------------------------------------*)
(* DECIDE_FORMULA_CONV : bool -> (term * decision_procedure -> int) ->      *)
(*                       decision_procedure list -> conv -> conv            *)
(*                                                                          *)
(* Decision procedure for unnormalized formulas.                            *)
(* Normalizes and homogenizes the negation of the formula and then attempts *)
(* to refute each of the resulting disjuncts.                               *)
(*--------------------------------------------------------------------------*)

fun DECIDE_FORMULA_CONV debug weight (procedures : decision_procedure list)
                                                                user_conv tm =
   let val _ = if debug
               then say ("\n***************************************" ^
                         "***************************************\n")
               else ()
       val new = new_var "v"
       val EXPAND_CONV =
          NormalizeBool.EXPAND_BOOL_CONV NormalizeBool.Disjunctive
   in  NEGATE_CONV
       (NormalizeBool.NORMALIZE_BOOL_CONV true NormalizeBool.Disjunctive false
           (user_conv THENC
            EXPAND_CONV
               (NormalizeBool.COND_OUT_CONV THENC
                EXPAND_CONV (HOMOGENIZE_CONV new procedures))) THENC
        DEPTH_EXISTS_CONV
           (DEPTH_DISJ_CONV
               (DECIDE_HOMOGENEOUS_CONV debug weight procedures) THENC
            DEPTH_CONV OR_F_CONV) THENC
        REPEATC EXISTS_SIMP_CONV)
       tm
   end
   handle HOL_ERR _ => failwith "DECIDE_FORMULA_CONV";


(*==========================================================================*)
(* Constructing a component procedure from a conversion                     *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* make_incremental_procedure : (pre_thm -> pre_thm -> pre_thm) ->          *)
(*                              (term -> pre_thm) -> thm ->                 *)
(*                              incremental_procedure                       *)
(*--------------------------------------------------------------------------*)

local

fun flip (x,y) = (y,x);

fun pair_eq (p1,p2) = (p1 = p2) orelse (p1 = flip p2);

fun pair_member p ps = exists (fn p' => pair_eq (p,p')) ps;

fun pair_subtract ps1 ps2 = filter (fn p => not (pair_member p ps2)) ps1;

fun set_of_pairs l
  = remove_duplicates (fn ((p1,_),(p2,_)) => pair_eq (p1,p2)) l;

fun equalities_in_thm th =
   let val ths = LazyRules.CONJUNCTS th
       val equalities = filter (is_eq o LazyThm.concl) ths
       val pairs =
          filter (fn ((lhs,rhs),_) => is_var lhs andalso is_var rhs)
             (map (fn th => ((dest_eq o LazyThm.concl) th,th)) equalities)
   in  set_of_pairs pairs
   end;

fun pairings f [] = []
  | pairings f (x::xs) = map (fn x' => f (x,x')) xs @ pairings f xs;

val IMPLIES_EQUALITY_THM =
   prove (--`!b x (y:'a). ((~(x = y) /\ b) = F) = (b ==> (x = y))`--,
          REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`b:bool`--) THEN
          REWRITE_TAC []);

val IMPLIES_EQUALITY =
   let fun implies_equality conc =
          let val (conj,F) = dest_eq conc
              val (diseq,b) = dest_conj conj
              val eq = dest_neg diseq
              val _ = dest_eq eq
          in  mk_imp (b,eq)
          end
       val rule = CONV_RULE (REWR_CONV IMPLIES_EQUALITY_THM)
   in  fn th =>
       (LazyThm.apply_rule1 (LazyThm.apply_to_concl implies_equality,rule) th
        handle (HOL_ERR _) => failwith "IMPLIES_EQUALITY")
   end;

in

fun make_incremental_procedure new_eq conv th =
   let type equation = term * term
       type state = bool * (LazyThm.pre_thm * LazyThm.pre_thm list *
                            equation list * equation list * equation list)
       datatype result = Result of LazyThm.pre_thm * state
                       | NoResult of state
       val conc = concl th
       val vars = free_vars conc
       fun check_false th =
          if (is_F (rhs (LazyThm.concl th)))
          then th
          else failwith "check_false"
       fun prove_false (state as (tried,s as (th,_,_,_,_))) =
          if tried
          then NoResult state
          else let val state' = (true,s)
               in  Result
                      ((C LazyRules.EQ_MP th o check_false o conv)
                          (LazyThm.concl th),
                       state')
                   handle HOL_ERR _ => NoResult state'
               end
       fun get_equality (tried,(th,eqth :: eqths,eqs,possible_eqs,get_eqs)) =
          Result (eqth,(tried,(th,eqths,eqs,possible_eqs,get_eqs)))
         | get_equality (state as (tried,(th,[],eqs,possible_eqs,get_eqs))) =
          let val pair as (v1,v2) = hd get_eqs
              and get_eqs' = tl get_eqs
          in  let val eqth =
                     (C LazyRules.MP th o IMPLIES_EQUALITY o conv)
                        (mk_conj (mk_neg (mk_eq (v1,v2)),LazyThm.concl th))
                  val eqs' = pair :: eqs
                  val possible_eqs' = pair_subtract possible_eqs [pair]
              in  Result (eqth,(tried,(th,[],eqs',possible_eqs',get_eqs')))
              end
              handle HOL_ERR _ =>
              get_equality (tried,(th,[],eqs,possible_eqs,get_eqs'))
          end
          handle Empty => NoResult state
       fun add_equality
              (state as (_,(th,eqths,eqs,possible_eqs,get_eqs))) eqth =
          let val pair as (v1,v2) = dest_eq (LazyThm.concl eqth)
          in  if (member v1 vars) andalso (member v2 vars) andalso
                 not (pair_member pair eqs)
              then let val possible_eqs' = pair_subtract possible_eqs [pair]
                   in  (false,(new_eq eqth th,eqths,pair :: eqs,
                               possible_eqs',possible_eqs'))
                   end
              else state
          end
       fun inc state ProveFalse =
          (case (prove_false state)
           of Result (falseth,state') => (Thm falseth,Increment (inc state'))
            | NoResult state' => (None,Increment (inc state')))
         | inc state GetEquality =
          (case (get_equality state)
           of Result (eqth,state') => (Thm eqth,Increment (inc state'))
            | NoResult state' => (None,Increment (inc state')))
         | inc state GetEqualities = (None,Increment (inc state))
         | inc state (AddEquality eqth) =
          (None,Increment (inc (add_equality state eqth)))
       val tried = false
       val lth = LazyThm.mk_proved_pre_thm th
       val (eqs,eqths) = unzip (equalities_in_thm lth)
       val possible_eqs = pair_subtract (pairings (fn x => x) vars) eqs
       val get_eqs = possible_eqs
   in  Increment (inc (tried,(lth,eqths,eqs,possible_eqs,get_eqs)))
   end;

end;

end;

end; (* Decide *)
