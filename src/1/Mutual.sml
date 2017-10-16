(* ===================================================================== *)
(* FILE          : Mutual.sml                                            *)
(* DESCRIPTION   : Tools associated with datatypes defined by mutual     *)
(*                 recursion. We provide an induction tactic, adapted    *)
(*                 from the standard INDUCT_THEN operator, which was     *)
(*                 translated from the HOL 88 version.                   *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 87.08.23                                              *)
(* REVISED       : 90.06.02                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* ADAPTOR       : Peter Vincent Homeier, University of Pennsylvania     *)
(* DATE          : March 27, 1998                                        *)
(* ===================================================================== *)

structure Mutual :> Mutual =
struct

open HolKernel Parse boolLib;

val ERR = mk_HOL_ERR "Mutual";

val AND = conjunction;

(* ---------------------------------------------------------------------*)
(* Internal function: 							*)
(*									*)
(* MOVEQS tys : returns a conversion that, when applied to a term with  *)
(*		universal quantifications, moves the quantifications    *)
(*		of variables of types in tys outward, and the others    *)
(*		inward towards the body; otherwise, order is preserved. *)
(*									*)
(* ---------------------------------------------------------------------*)

fun MOVEQS tys tm =
   if not (is_forall tm) then raise ERR "MOVEQS" "not a forall"
   else
   let val (Bvars,Body) = strip_forall tm
(*
       val _ = print_string "MOVEQS\n"
       val _ = print_term tm
       val _ = print_newline()
*)
       val (vars1,vars2) = partition (fn v => mem (type_of v) tys) Bvars
       val tm1 = list_mk_forall (vars1 @ vars2, Body)
       val eq_thm =
       Tactical.prove (mk_eq(tm, tm1),
                       EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[])
   in
       itlist (fn v =>
               CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV FORALL_IMP_CONV)))
              vars2 eq_thm
   end;

(* Test case:
val tys = [==`:num`==];
val tm = (--`!n b m a. b ==> (a /\ n+m < m)`--);
MOVEQS tys tm;
*)


(* ---------------------------------------------------------------------*)
(* Internal function: 							*)
(*									*)
(* REPAIR th :  returns an induction theorem by repairing th, using     *)
(*		MOVEQS on the hypotheses of the antecedent.             *)
(*									*)
(* ---------------------------------------------------------------------*)

fun REPAIR th =
   let val (Bvars,Body) = strip_forall(concl th)
       val (hy,cns) = dest_imp Body
       val tys = map (type_of o fst o dest_forall) (strip_conj cns)
   in
       CONV_RULE (((itlist (fn v => RAND_CONV o ABS_CONV) Bvars) o
                   RATOR_CONV o RAND_CONV o
                   ONCE_DEPTH_CONV) (MOVEQS tys))
              (REWRITE_RULE[AND_IMP_INTRO,GSYM CONJ_ASSOC] th)
   end;

(* Test case:
REPAIR avexp_induction handle e => (print_HOL_ERR e; raise e);
*)


(* ---------------------------------------------------------------------*)
(* Internal function: 							*)
(*									*)
(* BETAS "f" tm : returns a conversion that, when applied to a term with*)
(*		 the same structure as the input term tm, will do a	*)
(*		 beta reduction at all top-level subterms of tm which	*)
(*		 are of the form "f <arg>", for some argument <arg>.	*)
(*									*)
(* ---------------------------------------------------------------------*)

fun BETAS fnns body =
   if ((is_var body) orelse (is_const body))
   then REFL
   else if (is_abs body)
        then ABS_CONV (BETAS fnns (snd(dest_abs body)))
        else let val (Rator,Rand) = dest_comb body
             in
             if op_mem aconv Rator fnns then BETA_CONV
             else let val cnv1 = BETAS fnns Rator
                      and cnv2 = BETAS fnns Rand
                      fun f (Rator,Rand) = (cnv1 Rator, cnv2 Rand)
                  in
	          (MK_COMB o (f o dest_comb))
                  end
             end;

(* ---------------------------------------------------------------------*)
(* Internal function: GTAC						*)
(*									*)
(*   !x. tm[x]  							*)
(*  ------------  GTAC "y"   (primes the "y" if necessary).		*)
(*     tm[y]								*)
(*									*)
(* NB: the x is always a genvar, so optimized for this case.		*)
(* ---------------------------------------------------------------------*)

fun GTAC y (A,g) =
   let val (Bvar,Body) = dest_forall g
       and y' = variant (free_varsl (g::A)) y
   in
   ([(A,subst[Bvar |-> y'] Body)],
    fn [th] => GEN Bvar (INST [y' |-> Bvar] th)
     | _ => raise Match)
   end;

(* ---------------------------------------------------------------------*)
(* Internal function: TACF						*)
(*									*)
(* TACF is used to generate the subgoals for each case in an inductive 	*)
(* proof.  The argument tm is formula which states one generalized	*)
(* case in the induction. For example, the induction theorem for num is:*)
(*									*)
(*   |- !P. P 0 /\ (!n. P n ==> P(SUC n)) ==> !n. P n			*)
(*									*)
(* In this case, the argument tm will be one of:			*)
(*									*)
(*   1:  "P 0"   or   2: !n. P n ==> P(SUC n)				*)
(*   									*)
(* TACF applied to each these terms to construct a parameterized tactic *)
(* which will be used to further break these terms into subgoals.  The  *)
(* resulting tactic takes a variable name x and a user supplied theorem *)
(* continuation ttac.  For a base case, like case 1 above, the resulting*)
(* tactic just throws these parameters away and passes the goal on 	*)
(* unchanged (i.e. \x ttac. ALL_TAC).  For a step case, like case 2, the*)
(* tactic applies GTAC x as many times as required.  It then strips off *)
(* the induction hypotheses and applies ttac to each one.  For example, *)
(* if tac is the tactic generated by:					*)
(*									*)
(*    TACF "!n. P n ==> P(SUC n)" "x:num" ASSUME_TAC			*)
(*									*)
(* then applying tac to the goal A,"!n. P[n] ==> P[SUC n] has the same 	*)
(* effect as applying:							*)
(*									*)
(*    GTAC "x:num" THEN DISCH_THEN ASSUME_TAC				*)
(*									*)
(* TACF is a strictly local function, used only to define TACS, below.	*)
(* ---------------------------------------------------------------------*)
local
fun ctacs tm =
   if (is_conj tm)
   then let val tac2 = ctacs (snd(dest_conj tm))
        in fn ttac => CONJUNCTS_THEN2 ttac (tac2 ttac)
        end
   else fn ttac => ttac
val find = Lib.first;
fun findx bvars v = find (fn x => type_of x = type_of v) bvars
in
fun TACF tm =
   let val (vs,body) = strip_forall tm
   in
   if is_imp body
   then let val TTAC = ctacs (fst(dest_imp body))
        in
        fn xs => fn ttac =>
(*
           let val _ = print_string "TACF: xs = "
               val _ = print_terms xs
               val _ = print_newline()
               val _ = print_string "vs = "
               val _ = print_terms vs
               val _ = print_newline()
               val _ = print_string "map (findx xs) vs = "
               val _ = print_terms (map (findx xs) vs)
               val _ = print_newline()
           in
*)
           MAP_EVERY (GTAC o (findx xs)) vs THEN
        (* MAP_EVERY (GTAC o (Lib.K x)) vs THEN *)
           DISCH_THEN (TTAC ttac)
(*
           end
*)
        end
   else
   fn xs => fn ttac => Tactical.ALL_TAC
   end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: TACS						*)
(*									*)
(* TACS uses TACF to generate a parameterized list of tactics, one for  *)
(* each conjunct in the hypothesis of an induction theorem.		*)
(*									*)
(* For example, if tm is the hypothesis of the induction thoerem for the*)
(* natural numbers---i.e. if:						*)
(*									*)
(*   tm = "P 0 /\ (!n. P n ==> P(SUC n))"				*)
(*									*)
(* then TACS tm yields the paremterized list of tactics:		*)
(*									*)
(*   \x ttac. [TACF "P 0" x ttac; TACF "!n. P n ==> P(SUC n)" x ttac]   *)
(*									*)
(* TACS is a strictly local function, used only in MUTUAL_INDUCT_THEN.  *)
(* ---------------------------------------------------------------------*)

fun f (conj1,conj2) = (TACF conj1, TACS conj2)
and
    TACS tm =
      let val (cf,csf) = f(dest_conj tm)
                         handle HOL_ERR _ => (TACF tm, Lib.K(Lib.K[]))
      in
      fn xs => fn ttac => (cf xs ttac)::(csf xs ttac)
      end;

(* ---------------------------------------------------------------------*)
(* Internal function: GOALS						*)
(*									*)
(* GOALS generates the subgoals (and proof functions) for all the cases *)
(* in an induction. The argument A is the common assumption list for all*)
(* the goals, and tacs is a list of tactics used to generate subgoals 	*)
(* from these goals.							*)
(*									*)
(* GOALS is a strictly local function, used only in MUTUAL_INDUCT_THEN. *)
(* ---------------------------------------------------------------------*)
fun GOALS A [] tm = raise ERR "GOALS" "empty lsit"
  | GOALS A [t] tm =
      let val (sg,pf) = t (A,tm) in ([sg],[pf]) end
  | GOALS A (h::t) tm =
      let val (conj1,conj2) = dest_conj tm
          val (sgs,pfs) = GOALS A t conj2
          val (sg,pf) = h (A,conj1)
      in
      ((sg::sgs),(pf::pfs))
      end;

(* --------------------------------------------------------------------- *)
(* Internal function: GALPH						*)
(* 									*)
(* GALPH "!x1 ... xn. A ==> B":   alpha-converts the x's to genvars.	*)
(* --------------------------------------------------------------------- *)
local
fun rule v =
   let val gv = genvar(type_of v)
   in
   fn eq => let val th = FORALL_EQ v eq
            in TRANS th (GEN_ALPHA_CONV gv (rhs(concl th)))
            end
   end
in
fun GALPH tm =
   let val (vs,hy) = strip_forall tm
   in if (is_imp hy) then Lib.itlist rule vs (REFL hy) else REFL tm
   end
end;

(* --------------------------------------------------------------------- *)
(* Internal function: GALPHA                                             *)
(*                                                                       *)
(* Applies the conversion GALPH to each conjunct in a sequence.          *)
(* --------------------------------------------------------------------- *)


fun f (conj1,conj2) = (GALPH conj1, GALPHA conj2)
and GALPHA tm =
   let val (c,cs) = f(dest_conj tm)
   in
   MK_COMB(AP_TERM AND c, cs)
   end
   handle HOL_ERR _ => GALPH tm;


(* --------------------------------------------------------------------- *)
(* MUTUAL_INDUCT_THEN : general induction tactic for mutuallly recursive *)
(*                      datatypes.                                       *)
(* --------------------------------------------------------------------- *)
local val bool = genvar (Type.bool)

fun MUTUAL_INDUCT_THEN1 th =
   let val th' = REPAIR th
(*
       val _ = print_string "Repaired induction theorem:\n"
       val _ = print_theorem th'
       val _ = print_string "\n"
*)
       val (Bvars,Body) = strip_forall(concl th')
       val (hy,_) = dest_imp Body
       val bconv = BETAS Bvars hy
       and tacsf = TACS hy
       val vs = map (fn Bvar => genvar (type_of Bvar)) Bvars
       val eta_th = LIST_CONJ (map (CONV_RULE(RAND_CONV ETA_CONV))
                                       (CONJUNCTS(UNDISCH(SPECL vs th'))))
(*
       val _ = print_string "eta_th:\n"
       val _ = print_theorem eta_th
       val _ = print_string "\n"
*)
       val (asm,con) = case dest_thm eta_th
                       of ([asm],con) => (asm,con)
                        | _ => raise ERR "MUTUAL_INDUCT_THEN1" ""
       val dis = DISCH asm eta_th
       val ind = GENL vs (SUBST [bool |-> GALPHA asm] (mk_imp(bool, con)) dis)
(*
       val _ = print_string "ind:\n"
       val _ = print_theorem ind
       val _ = print_string "\n"
*)
       val find = Lib.first;
       fun findt ts v =
           find (fn x => type_of (snd(dest_comb x)) = type_of v) ts
           handle _ => let val ty = type_of v
                           val ty' = hd(snd(dest_type ty))
                           val (Tyop',Args') = dest_type ty'
                           val nm = implode [hd (explode Tyop')]
                           val v' = mk_var(nm, ty')
                       in
                       mk_forall(v', T)
                       end
       val CHECK_TAC :tactic = fn (asl,gl) => ACCEPT_TAC (ASSUME gl) (asl,gl)

   in
   fn ttac => fn (A,t) => (* t is the current goal *)
      let val ts = strip_conj t
          val lams = map (snd o dest_comb) ts
          val ts' = map (findt ts) vs
          val ts_thm = Tactical.prove
                 (mk_eq(list_mk_conj ts',list_mk_conj ts),
                   REWRITE_TAC[] THEN
                   EQ_TAC THEN STRIP_TAC THEN
                   REPEAT CONJ_TAC THEN
                   CHECK_TAC)
(*
          val _ = print_string "ts_thm:\n"
          val _ = print_theorem ts_thm
          val _ = print_string "\n"
*)
          val lams' = map (snd o dest_comb) ts'
          val spec = SPECL lams' (itlist2 (fn v => fn lam =>
                     INST_TYPE (Lib.snd(Term.match_term v lam))
                     handle HOL_ERR _ => Lib.I
                     ) vs lams' ind)
(*
          val _ = print_string "spec:\n"
          val _ = print_theorem spec
          val _ = print_string "\n"
*)
          val (ant,conseq) = dest_imp(concl spec)
          val beta = SUBST [bool |-> bconv ant] (mk_imp(bool,conseq)) spec
(*
          val _ = print_string "beta:\n"
          val _ = print_theorem beta
          val _ = print_string "\n"
*)
          val bvars = map (fst o dest_abs) lams'
          val tacs = tacsf bvars ttac
          val (gll,pl) = GOALS A tacs (fst(dest_imp(concl beta)))
          val pf = ((EQ_MP ts_thm) o (MP beta) o LIST_CONJ)
                   o mapshape(map length gll)pl
      in
      (Lib.flatten gll, pf)
      end
      handle HOL_ERR _
       => raise ERR "MUTUAL_INDUCT_THEN" "tactic application error"
   end
   handle (e as HOL_ERR
	           {origin_structure = "Mutual",
		    origin_function = "MUTUAL_INDUCT_THEN",...}) => raise e
        | _ => raise ERR "MUTUAL_INDUCT_THEN" "ill-formed induction theorem"

in

fun MUTUAL_INDUCT_THEN th ttac =
    MUTUAL_INDUCT_THEN1 th ttac
    THEN REWRITE_TAC[]
    THEN TRY (UNDISCH_TAC (concl TRUTH) THEN DISCH_THEN (fn th => ALL_TAC))

end;


fun MUTUAL_INDUCT_TAC ind = MUTUAL_INDUCT_THEN ind ASSUME_TAC;

end (* Mutual *)
