structure arm_core_decompLib :> arm_core_decompLib =
struct

open HolKernel Parse boolLib bossLib Lib

open arm_core_decompTheory progTheory helperLib arm_decompLib

val ERR = Feedback.mk_HOL_ERR "arm_core_decompLib"

(* ------------------------------------------------------------------------ *)

val (spec,_,_,_) = arm_decompLib.l3_arm_tools

val cond_var = Term.mk_var ("cond", ``:bool``)
val r15 = Term.mk_var ("r15", ``:word32``)

val arm_assert =
   ARM_ASSERT_def
   |> SPEC_ALL
   |> Conv.CONV_RULE (Conv.RHS_CONV helperLib.STAR_AC_CONV)
   |> GSYM

val targets = progSyntax.strip_star (utilsLib.lhsc arm_assert)

val precond_thm = Q.prove(
   `!b. precond b = cond (Abbrev b): 'a set set`,
   SIMP_TAC std_ss [markerTheory.Abbrev_def,set_sepTheory.precond_def])

fun add_prime v = mk_var (fst (dest_var v) ^ "'", type_of v)

val PAIR_LEMMA = Q.prove(
   `((x1 = y1) ==> (x2 = y2) ==> b) ==> (((x2,x1) = (y2:'a,y1:'b)) ==> b)`,
   SIMP_TAC std_ss [])

fun find_match [] tm = fail()
  | find_match (x::xs) tm =
       fst (match_term x tm) handle HOL_ERR _ => find_match xs tm

val ARM_ASSERT_INTRO_CONV = STAR_AC_CONV THENC Conv.REWR_CONV arm_assert

fun FORCE_DISCH_ALL thm =
   (if List.null (Thm.hyp thm) then DISCH boolSyntax.T else DISCH_ALL) thm

val INTRO_TRIPLE_RULE =
   REWRITE_RULE [] o
   SPEC cond_var o
   MATCH_MP INTRO_TRIPLE_L3_ARM o
   FORCE_DISCH_ALL o
   Conv.CONV_RULE (PRE_POST_CONV ARM_ASSERT_INTRO_CONV)

(* abbreviate posts *)
fun abbrev_conv pat post =
  if pat = r15
     then ALL_CONV post
  else if is_var pat
     then if pat = post
             then ALL_CONV post
          else ASSUME (mk_eq (post, add_prime pat))
  else if is_comb pat
     then (RAND_CONV (abbrev_conv (rand pat))
           THENC RATOR_CONV (abbrev_conv (rator pat))) post
  else if pat = post
     then ALL_CONV post
  else NO_CONV post

val precond_rule =
   UNDISCH_ALL o
   Conv.CONV_RULE
      (helperLib.PRE_CONV
          (PURE_ONCE_REWRITE_CONV [precond_thm]
           THENC helperLib.MERGE_CONDS_CONV)
       THENC PURE_ONCE_REWRITE_CONV [SPEC_MOVE_COND])

fun spec_to_triple_rule th =
   let
      val th = precond_rule th
      val fnd =
         find_match (progSyntax.strip_star (progSyntax.dest_pre (Thm.concl th)))
      val (xs, frame) =
         List.foldr (fn (t, (sbst, frm)) =>
            case Lib.total fnd t of
               SOME s => (sbst @ s, frm)
             | NONE => (sbst, t :: frm)) ([], []) targets
      val th =
         th |> INST xs
            |> SPECC_FRAME_RULE (progSyntax.list_mk_star frame)
            |> INTRO_TRIPLE_RULE
      val pat = th |> concl |> rator |> rator |> rand
   in
      th |> CONV_RULE (RAND_CONV (abbrev_conv pat))
         |> DISCH_ALL
         |> repeat (MATCH_MP PAIR_LEMMA)
         |> UNDISCH_ALL
   end

val l3_triple =
   (* cache *)
     (fn hex =>
         (case spec hex of
             ((th1,x1,y1 as SOME _), NONE) =>
                 ((spec_to_triple_rule th1,x1,y1), NONE)
           | ((th1,x1,y1 as SOME _), SOME (th2,x2,y2)) =>
                 ((spec_to_triple_rule th1,x1,y1),
                  SOME (spec_to_triple_rule th2,x2,y2))
           | _ => fail())
         handle HOL_ERR _ => raise ERR "l3_triple" hex)

val fv_spec_tm = free_vars (Thm.concl arm_assert)

val swap_primes =
   let
      val vs = (cond_var :: fv_spec_tm) |> map (fn v => (v,add_prime v))
      val ss = map (fn (x,y) => x |-> y) vs @ map (fn (x,y) => y |-> x) vs
   in
      subst ss
   end

val () = core_decompilerLib.configure
           { triple_fn = l3_triple,
             init_fn = arm_decompLib.config_for_fast,
             swap_fn = swap_primes,
             pc_tm = r15 }

(* ------------------------------------------------------------------------ *)

end
