(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Common auxiliary functions *)

structure Library =
struct

  (* opens 'path' as an output text file; writes all elements of 'strings' to
     this file (in the order given); closes the file *)
  fun write_strings_to_file path strings =
  let
    val outstream = TextIO.openOut path
  in
    List.app (TextIO.output o Lib.pair outstream) strings;
    TextIO.closeOut outstream
  end

  (* A |- ... /\ t /\ ...
     --------------------
            A |- t        *)
  fun conj_elim (thm, t) =
  let
    fun elim conj =
      if t = conj then
        Lib.I
      else
        let
          val (l, r) = boolSyntax.dest_conj conj
        in
          elim l o Thm.CONJUNCT1
            handle Feedback.HOL_ERR _ =>
              elim r o Thm.CONJUNCT2
        end
  in
    elim (Thm.concl thm) thm
  end

  (*        A |- t
     --------------------
     A |- ... \/ t \/ ... *)
  fun disj_intro (thm, disj) =
    if Thm.concl thm = disj then
      thm
    else
      let
        val (l, r) = boolSyntax.dest_disj disj
      in
        Thm.DISJ1 (disj_intro (thm, l)) r
          handle Feedback.HOL_ERR _ =>
            Thm.DISJ2 l (disj_intro (thm, r))
      end

  (* |- ... \/ t \/ ... \/ ~t \/ ... *)
  fun gen_excluded_middle disj =
  let
    val (pos, neg) = Lib.tryfind (fn neg =>
      let
        val pos = boolSyntax.dest_neg neg
        fun check_is_disjunct lit disj =
          disj = lit orelse
            let
              val (l, r) = boolSyntax.dest_disj disj
            in
              check_is_disjunct lit l
                handle Feedback.HOL_ERR _ =>
                  check_is_disjunct lit r
            end
        val _ = check_is_disjunct pos disj
      in
        (pos, neg)
      end) (boolSyntax.strip_disj disj)
    val th1 = disj_intro (Thm.ASSUME pos, disj)
    val th2 = disj_intro (Thm.ASSUME neg, disj)
  in
    Thm.DISJ_CASES (Thm.SPEC pos boolTheory.EXCLUDED_MIDDLE) th1 th2
  end

  (* A |- ... /\ t /\ ... /\ ~t /\ ...
     ---------------------------------
                  A |- F               *)
  fun gen_contradiction thm =
  let
    val (pos, neg) = Lib.tryfind (fn neg =>
      let
        val pos = boolSyntax.dest_neg neg
        fun check_is_conjunct lit conj =
          conj = lit orelse
            let
              val (l, r) = boolSyntax.dest_conj conj
            in
              check_is_conjunct lit l
                handle Feedback.HOL_ERR _ =>
                  check_is_conjunct lit r
            end
        val _ = check_is_conjunct pos (Thm.concl thm)
      in
        (pos, neg)
      end) (boolSyntax.strip_conj (Thm.concl thm))
    val th1 = conj_elim (thm, pos)
    val th2 = conj_elim (thm, neg)
  in
    Thm.MP (Thm.NOT_ELIM th2) th1
  end

  (* A tactic that unfolds operations of set theory, replacing them by
     propositional logic (representing sets as predicates). *)
  val SET_SIMP_TAC =
  let
    val thms = [pred_setTheory.SPECIFICATION, pred_setTheory.GSPEC_ETA,
      pred_setTheory.EMPTY_DEF, pred_setTheory.UNIV_DEF,
      pred_setTheory.UNION_DEF, pred_setTheory.INTER_DEF]
  in
    simpLib.SIMP_TAC (simpLib.mk_simpset [pred_setTheory.SET_SPEC_ss]) thms 
  end

  (* A tactic that unfolds LET. *)
  val LET_SIMP_TAC =
    simpLib.SIMP_TAC (simpLib.mk_simpset [boolSimps.LET_ss]) []

  (* A tactic that simplifies certain word expressions. *)
  val WORD_SIMP_TAC =
    simpLib.SIMP_TAC (simpLib.++ (bossLib.pure_ss, wordsLib.WORD_ss))
      [wordsTheory.LSL_LIMIT, wordsTheory.LSR_LIMIT]

end
