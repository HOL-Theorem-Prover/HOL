structure tripleLib :> tripleLib =
struct

open HolKernel Parse boolLib bossLib
open progTheory tripleTheory helperLib

val ERR = Feedback.mk_HOL_ERR "triple"

(* ------------------------------------------------------------------------ *)

val CODE_CONV = RATOR_CONV o RAND_CONV
val POST_CONV = RAND_CONV o RAND_CONV
val PRE_CONV = RATOR_CONV o RATOR_CONV o POST_CONV

(* ------------------------------------------------------------------------ *)
val PAIR_LEMMA = Q.prove(
   `((x1 = y1) ==> (x2 = y2) ==> b) ==> (((x2,x1) = (y2:'a,y1:'b)) ==> b)`,
   SIMP_TAC std_ss [])

val pair_rule =
   Drule.UNDISCH_ALL o Lib.repeat (Drule.MATCH_MP PAIR_LEMMA) o DISCH_ALL

val precond_thm = Q.prove(
   `!b. precond b = cond (Abbrev b): 'a set set`,
   SIMP_TAC std_ss [markerTheory.Abbrev_def,set_sepTheory.precond_def])

val precond_rule =
   UNDISCH_ALL o
   Conv.CONV_RULE
      (helperLib.PRE_CONV
          (PURE_ONCE_REWRITE_CONV [precond_thm]
           THENC helperLib.MERGE_CONDS_CONV)
       THENC PURE_ONCE_REWRITE_CONV [progTheory.SPEC_MOVE_COND])

fun add_prime v = Term.mk_var (fst (Term.dest_var v) ^ "'", Term.type_of v)

fun find_match [] tm = fail()
  | find_match (x::xs) tm =
       fst (match_term x tm) handle HOL_ERR _ => find_match xs tm

fun FORCE_DISCH_ALL thm =
   (if List.null (Thm.hyp thm)
       then Thm.DISCH boolSyntax.T
    else Drule.DISCH_ALL) thm

fun spec_to_triple_rule (pc, assert_thm, model_def) =
   let
      val assert_rwt =
         assert_thm
         |> Drule.SPEC_ALL
         |> Conv.CONV_RULE (Conv.RHS_CONV helperLib.STAR_AC_CONV)
         |> GSYM
      val targets = progSyntax.strip_star (utilsLib.lhsc assert_rwt)
      val ASSERT_INTRO_CONV = helperLib.STAR_AC_CONV
                              THENC Conv.REWR_CONV assert_rwt
      val model = boolSyntax.lhs (Thm.concl model_def)
      val intro_triple =
         tripleTheory.INTRO_TRIPLE
         |> Drule.ISPEC model
         |> Conv.CONV_RULE (Conv.LAND_CONV (REWRITE_CONV [model_def]))
      val intro_triple_rule =
         REWRITE_RULE [] o
         Thm.SPEC (Term.mk_var ("cond", ``:bool``)) o
         Drule.MATCH_MP intro_triple o
         FORCE_DISCH_ALL o
         Conv.CONV_RULE (helperLib.PRE_POST_CONV ASSERT_INTRO_CONV)
      (* abbreviate posts *)
      fun abbrev_conv pat post =
         if pat = pc
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
   in
      fn th =>
         let
            val th = precond_rule th
            val ps = progSyntax.strip_star (progSyntax.dest_pre (Thm.concl th))
            val fnd = find_match ps
            val (xs, frame) =
               List.foldr (fn (t, (sbst, frm)) =>
                  case Lib.total fnd t of
                     SOME s => (sbst @ s, frm)
                   | NONE => (sbst, t :: frm)) ([], []) targets
            val th =
               th |> Thm.INST xs
                  |> helperLib.SPECC_FRAME_RULE (progSyntax.list_mk_star frame)
                  |> intro_triple_rule
            val pat = th |> concl |> rator |> rator |> rand
         in
            pair_rule (CONV_RULE (RAND_CONV (abbrev_conv pat)) th)
         end
   end

(* ------------------------------------------------------------------------ *)

end
