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
        String.implode (List.rev (c :: cs))
      else if c = #"\\" then
        (* FIXME: handle C-style quoted characters properly *)
        aux_string (get_char () :: c :: cs) (get_char ())
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
      | aux [] #"\"" = aux_string [#"\""] (get_char ())
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
    Arbnum.fromString s
      handle Option.Option =>
        raise Feedback.mk_HOL_ERR "Library" "parse_arbnum"
          ("numeral expected, but '" ^ s ^ "' found")

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
      : (string, (string -> Arbnum.num list -> 'a list -> 'a) list)
        Redblackmap.dict =
    List.foldl extend_dict (Redblackmap.mkDict String.compare) xs

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

(*
  (* A tactic that simplifies certain word expressions. *)
  val WORD_SIMP_TAC =
    simpLib.SIMP_TAC (simpLib.++ (bossLib.pure_ss, wordsLib.WORD_ss))
      [wordsTheory.EXTRACT_ALL_BITS, wordsTheory.WORD_EXTRACT_ZERO,
      wordsTheory.LSL_LIMIT, wordsTheory.LSR_LIMIT]
*)

end
