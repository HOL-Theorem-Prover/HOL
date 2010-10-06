(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Common auxiliary functions *)

structure Library =
struct

  (***************************************************************************)
  (* I/O                                                                     *)
  (***************************************************************************)

  (* opens 'path' as an output text file; writes all elements of
     'strings' to this file (in the given order); closes the file *)
  fun write_strings_to_file path strings =
  let
    val outstream = TextIO.openOut path
  in
    List.app (TextIO.output o Lib.pair outstream) strings;
    TextIO.closeOut outstream
  end

  (* returns a function that returns the next character in 'instream'
     and raises 'HOL_ERR' when at the end of 'instream' *)
  fun get_buffered_char instream : unit -> char =
  (* The fastest approach would be to slurp in the whole stream at
     once. However, this is infeasible for long streams (especially
     because 'String.explode' causes a significant memory
     blowup). Reading chunks of 10000000 bytes (i.e., 10 MB) should be
     a reasonable compromise between a small memory footprint (even
     after 'String.explode') and a small number of reads. *)
  let
    val buffer = ref ([] : char list)
  in
    fn () =>
      (case !buffer of
        [] =>
        (case String.explode (TextIO.inputN (instream, 10000000)) of
          [] =>
          raise Feedback.mk_HOL_ERR "Library" "get_buffered_char"
            "end of stream"
        | c::cs =>
          (buffer := cs; c))
      | c::cs =>
        (buffer := cs; c))
  end

  (* Takes a function that returns characters
     (cf. 'get_buffered_char'), returns a function that returns
     tokens. SMT-LIB 2 tokens are separated by whitespace (which is
     dropped) or parentheses (which are tokens themselves). Tokens are
     simply strings; we use no markup. *)
  fun get_token (get_char : unit -> char) : unit -> string =
  let
    val buffer = ref (NONE : string option)
    fun (* whitespace *)
        aux [] #" " = aux [] (get_char ())
      | aux [] #"\n" = aux [] (get_char ())
      | aux [] #"\r" = aux [] (get_char ())
      | aux cs #" " = String.implode (List.rev cs)
      | aux cs #"\n" = String.implode (List.rev cs)
      | aux cs #"\r" = String.implode (List.rev cs)
      (* parentheses *)
      | aux [] #"(" = "("
      | aux [] #")" = ")"
      | aux cs #"(" = (buffer := SOME "("; String.implode (List.rev cs))
      | aux cs #")" = (buffer := SOME ")"; String.implode (List.rev cs))
      (* everything else *)
      | aux cs c = aux (c :: cs) (get_char ())
          handle Feedback.HOL_ERR _ =>
            (* end of file *)
            String.implode (List.rev (c :: cs))
  in
    fn () =>
      case !buffer of
        SOME token => (buffer := NONE; token)
      | NONE => aux [] (get_char ())
  end

  fun expect_token (expected : string) (actual : string) : unit =
    if expected = actual then
      ()
    else
      raise Feedback.mk_HOL_ERR "Library" "expect_token"
        ("'" ^ expected ^ "' expected, but '" ^ actual ^ "' found")

  (***************************************************************************)
  (* Derived rules                                                           *)
  (***************************************************************************)

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

  (***************************************************************************)
  (* Tactics                                                                 *)
  (***************************************************************************)

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
