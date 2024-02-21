(* Copyright (c) 2009-2011 Tjark Weber. All rights reserved. *)

(* Common auxiliary functions, tracing *)

structure Library =
struct

  (***************************************************************************)
  (* tracing                                                                 *)
  (***************************************************************************)

  (* possible values:
     0 - no output at all (except for fatal errors)
     1 - warnings only
     2 - also diagnostic messages of constant length
     3 - also diagnostic messages that are potentially lengthy (e.g., terms,
         models, proofs)
     4 - moreover, temporary files (for communication with the SMT solver) are
         not removed after solver invocation *)
  val trace = ref 2

  val _ = Feedback.register_trace ("HolSmtLib", trace, 4)

  (***************************************************************************)
  (* I/O, parsing                                                            *)
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
    fun line_comment () =
      if get_char () = #"\n" then
        ()
      else line_comment ()
    fun aux_symbol cs c =
      if c = #"|" then
        (* we return |x| as x *)
        String.implode (List.rev cs)
      else
        aux_symbol (c :: cs) (get_char ())
    fun aux_string cs c =
      if c = #"\"" then
        (* we return "x" as x *)
        String.implode (List.rev cs)
      else if c = #"\\" then
        (* The only escape sequences in SMT-LIB are \" and \\. We simply drop
           the backslash. *)
        aux_string (get_char () :: cs) (get_char ())
      else
        aux_string (c :: cs) (get_char ())
    fun (* whitespace *)
        aux [] #" " = aux [] (get_char ())
      | aux [] #"\t" = aux [] (get_char ())
      | aux [] #"\n" = aux [] (get_char ())
      | aux [] #"\r" = aux [] (get_char ())
      | aux cs #" " = String.implode (List.rev cs)
      | aux cs #"\t" = String.implode (List.rev cs)
      | aux cs #"\n" = String.implode (List.rev cs)
      | aux cs #"\r" = String.implode (List.rev cs)
      (* parentheses *)
      | aux [] #"(" = "("
      | aux [] #")" = ")"
      | aux cs #"(" = (buffer := SOME "("; String.implode (List.rev cs))
      | aux cs #")" = (buffer := SOME ")"; String.implode (List.rev cs))
      (* | *)
      | aux [] #"|" = aux_symbol [] (get_char ())
      | aux _ #"|" =
        raise Feedback.mk_HOL_ERR "Library" "get_token" "invalid '|'"
      (* " *)
      | aux [] #"\"" = aux_string [] (get_char ())
      | aux _ #"\"" =
        raise Feedback.mk_HOL_ERR "Library" "get_token" "invalid '\"'"
      (* ; *)
      | aux [] #";" = (line_comment (); aux [] (get_char ()))
      | aux cs #";" = (line_comment (); String.implode (List.rev cs))
      (* everything else *)
      | aux cs c = aux (c :: cs) (get_char ())
          handle Feedback.HOL_ERR _ =>
            (* end of stream *)
            String.implode (List.rev (c :: cs))
  in
    fn () =>
      let
        val token = case !buffer of
            SOME token => (buffer := NONE; token)
          | NONE => aux [] (get_char ())
      in
        if !trace > 2 then
          Feedback.HOL_MESG ("HolSmtLib: next token is '" ^ token ^ "'")
        else ();
        token
      end
  end

  fun parse_arbnum (s : string) =
    let
      fun handle_err () =
        raise Feedback.mk_HOL_ERR "Library" "parse_arbnum"
          ("numeral expected, but '" ^ s ^ "' found")
    in
      Arbnum.fromString s
        (* Moscow ML's Arbnum implementation throws Option.Option on error,
           while Poly/ML's throws the Fail exception *)
        handle Option.Option => handle_err ()
             | Fail _ => handle_err ()
    end

  fun expect_token (expected : string) (actual : string) : unit =
    if expected = actual then
      ()
    else
      raise Feedback.mk_HOL_ERR "Library" "expect_token"
        ("'" ^ expected ^ "' expected, but '" ^ actual ^ "' found")

  (* extends a dictionary that maps keys to lists of values *)
  fun extend_dict ((key, value), dict) =
  let
    val values = Redblackmap.find (dict, key)
      handle Redblackmap.NotFound => []
  in
    Redblackmap.insert (dict, key, value :: values)
  end

  (* entries in 'dict2' are prepended to entries in 'dict1' *)
  fun union_dict dict1 dict2 = Redblackmap.foldl (fn (key, vals, dict) =>
    let
      val values = Redblackmap.find (dict1, key)
        handle Redblackmap.NotFound => []
    in
      Redblackmap.insert (dict, key, vals @ values)
    end) dict1 dict2

  (* creates a dictionary that maps strings to lists of parsing functions *)
  fun dict_from_list xs
      : (string, (string -> string list -> 'a list -> 'a) list)
        Redblackmap.dict =
    List.foldl extend_dict (Redblackmap.mkDict String.compare) xs

  (***************************************************************************)
  (* auxiliary functions                                                     *)
  (***************************************************************************)

  (* `is_def_oriented` must return false when:
     1. `lhs` is not a variable in `var_set` but `rhs` is, or
     2. `lhs` and `rhs` are both variables in `var_set` but `rhs` is smaller
         than `lhs` (for some definition of "smaller").
     Otherwise, it must return true. *)
  fun is_def_oriented var_set (lhs, rhs) =
    (not (HOLset.member (var_set, rhs))) orelse
      (HOLset.member (var_set, lhs) andalso
        Term.var_compare (rhs, lhs) <> LESS)

  (* Orient a definition of the form `lhs = rhs` into `rhs = lhs`, if necessary.
     This is used to ensure that the `lhs` is a variable in `var_set`. Also, if
     both the `lhs` and the `rhs` are variables in `var_set`, then the `rhs`
     must not be "smaller" than the `lhs`. This is done to avoid ending up with
     circular definitions after they are all aggregated into the final theorem,
     i.e. we want to avoid ending up with both `var1 = var2` and `var2 = var1`. *)
  fun orient_def var_set (lhs, rhs) =
    if is_def_oriented var_set (lhs, rhs) then
      (lhs, rhs)
    else
      (rhs, lhs)

  (***************************************************************************)
  (* Derived rules                                                           *)
  (***************************************************************************)

  (* A |- ... /\ t /\ ...
     --------------------
            A |- t        *)
  fun conj_elim (thm, t) =
  let
    fun elim conj =
      if Term.aconv t conj then
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
    if Term.aconv (Thm.concl thm) disj then
      thm
    else
      let
        val (l, r) = boolSyntax.dest_disj disj
      in
        Thm.DISJ1 (disj_intro (thm, l)) r
          handle Feedback.HOL_ERR _ =>
            Thm.DISJ2 l (disj_intro (thm, r))
      end

  (* auxiliary function: fails unless 's' is a subterm of 't' with
     respect to 'destfn' *)
  fun check_subterm destfn s t =
    if Term.aconv s t then
      ()
    else
      let
        val (l, r) = destfn t
      in
        check_subterm destfn s l
          handle Feedback.HOL_ERR _ =>
            check_subterm destfn s r
      end

  (* |- ... \/ t \/ ... \/ ~t \/ ... *)
  fun gen_excluded_middle disj =
  let
    val (pos, neg) = Lib.tryfind (fn neg =>
      let
        val pos = boolSyntax.dest_neg neg
        val _ = check_subterm boolSyntax.dest_disj pos disj
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
        val _ = check_subterm boolSyntax.dest_conj pos (Thm.concl thm)
      in
        (pos, neg)
      end) (boolSyntax.strip_conj (Thm.concl thm))
    val th1 = conj_elim (thm, pos)
    val th2 = conj_elim (thm, neg)
  in
    Thm.MP (Thm.NOT_ELIM th2) th1
  end

  (* Given two terms ``lhs`` and ``rhs``, find an instantiation of free
     variables such that a theorem with the conclusion ``lhs = rhs`` can be
     returned. The instantiations become hypotheses of the returned theorem.
     e.g.:

     gen_instantiation (``x+1+z2``, ``z1+2``, {``z1``, ``z2``, ``z3``})
     returns the theorem:

     { z1 = x+1, z2 = 2 } |- x+1+z2 = z1+2

     In cases where we end up with an hypothesis of the form `var1 = var2`,
     we might orient the hypothesis to become `var2 = var1` to make sure that
     the left-hand side is a variable in `var_set`. If both `var1` and `var2`
     are in `var_set`, then we make sure that the left-hand side contains the
     "smaller" variable. This avoids creating circular definitions across
     multiple calls of this function (i.e. one call instantiating `z1 = z2`
     and another instantiating `z2 = z1`). *)
  fun gen_instantiation (lhs, rhs, var_set) =
  let
    val substs = Unify.simp_unify_terms [] lhs rhs
    fun orient {redex, residue} = orient_def var_set (redex, residue)
    val oriented_substs = List.map orient substs
    val asl = List.map boolSyntax.mk_eq oriented_substs
    val thms = List.map Thm.ASSUME asl
    val concl = boolSyntax.mk_eq (lhs, rhs)
  in
    Tactical.TAC_PROOF ((asl, concl), Tactical.THEN (Tactic.SUBST_TAC thms,
      Tactic.REFL_TAC))
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

  val TO_WORD_EXTRACT = Q.prove(
        `(!w : 'a word.
            dimindex(:'b) < dimindex(:'a) ==>
            (w2w w : 'b word = (dimindex(:'b) - 1 >< 0) w)) /\
         (!w : 'a word.
            dimindex(:'b) < dimindex(:'a) ==>
            (sw2sw w : 'b word = (dimindex(:'b) - 1 >< 0) w))`,
        BasicProvers.SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [])

  val WORD_BIT_EXTRACT = simpLib.SIMP_PROVE
        (simpLib.++(bossLib.std_ss, wordsLib.WORD_BIT_EQ_ss))
        [wordsLib.WORD_DECIDE ``1w :word1 ' 0``]
      ``!w:'a word i. i < dimindex (:'a) ==> (w ' i = ((i >< i) w = 1w:word1))``

  val WORD_SHIFT_BV = simpLib.SIMP_PROVE bossLib.bool_ss
        [wordsTheory.word_shift_bv]
      ``(!w:'a word n. n < dimword (:'a) ==> (w << n = w <<~ n2w n)) /\
        (!w:'a word n. n < dimword (:'a) ==> (w >> n = w >>~ n2w n)) /\
        (!w:'a word n. n < dimword (:'a) ==> (w >>> n = w >>>~ n2w n))``

  val bit_field_insert_rwt = simpLib.SIMP_RULE
        (simpLib.++(bossLib.bool_ss, boolSimps.LET_ss)) [] wordsTheory.bit_field_insert;

  val WORD_SIMP_TAC = let
    open Tactical Conv Tactic wordsTheory simpLib
  in
    CONV_TAC (DEPTH_CONV wordsLib.EXPAND_REDUCE_CONV) THEN
      SIMP_TAC (pureSimps.pure_ss ++ numSimps.REDUCE_ss ++ wordsLib.SIZES_ss)
        [word_rol_bv_def, word_ror_bv_def,
         w2n_n2w, word_bit_def, bit_field_insert_rwt,
         word_lsb_def, word_msb_def,
         WORD_SLICE_THM, WORD_BITS_EXTRACT,
         WORD_BIT_EXTRACT, WORD_SHIFT_BV, TO_WORD_EXTRACT] THEN
      CONV_TAC (DEPTH_CONV wordsLib.EXTEND_EXTRACT_CONV)
  end

(*
  val WORD_SIMP_TAC =
    simpLib.SIMP_TAC (simpLib.++ (bossLib.pure_ss, wordsLib.WORD_ss))
      [wordsTheory.EXTRACT_ALL_BITS, wordsTheory.WORD_EXTRACT_ZERO,
      wordsTheory.LSL_LIMIT, wordsTheory.LSR_LIMIT]
*)

end
