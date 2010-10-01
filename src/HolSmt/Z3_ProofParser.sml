(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Proof reconstruction for Z3: parsing of Z3's proofs *)

structure Z3_ProofParser =
struct

  (* Function 'parse_file' parses Z3's response to the SMT2
     (get-proof) command (for an unsatisfiable problem, with proofs
     enabled in Z3, i.e., "PROOF_MODE=2" in Z3's .ini file). Other
     functions in this file are just auxiliary. This parser has been
     tested with Z3 2.11 (which was released on August 17, 2010). *)

  (* I tried to implement this parser in ML-Lex/ML-Yacc, but gave up
     on that -- mainly for two reasons: 1. The whole toolchain/build
     process gets more complicated. 2. Performance and memory usage of
     the generated parser were far from satisfactory, I am guessing
     because the generated parser wasn't tail-recursive. (It might be
     a worthwhile research project to implement an *efficient* parser
     generator for SML ...) *)

local

  open Z3_Proof

  val ERR = Feedback.mk_HOL_ERR "Z3_ProofParser"
  val WARNING = Feedback.HOL_WARNING "Z3_ProofParser"

  (***************************************************************************)
  (* tokenization                                                            *)
  (***************************************************************************)

  (* The fastest approach would be to slurp in the whole proof file at
     once. However, this is infeasible for large proofs (especially
     because 'String.explode' causes a significant memory blowup, so
     it cannot be applied to large proofs in their entirety). *)

  fun get_buffered_char instream : unit -> char =
  let
    val buffer = ref ([] : char list)
  in
    fn () =>
      (case !buffer of
        [] =>
        (* reading chunks of 10485760 bytes (i.e., 10 MB) should be a
           reasonable compromise between a small memory footprint
           (even after 'String.explode') and a small number of reads *)
        (case String.explode (TextIO.inputN (instream, 10485760)) of
          [] =>
          raise ERR "get_buffered_char" "end of file"
        | c::cs =>
          (if !SolverSpec.trace > 2 then
            Feedback.HOL_MESG ("HolSmtLib: read "
              ^ Int.toString (List.length cs + 1)
              ^ " character(s) from Z3 proof file")
          else ();
          buffer := cs; c))
      | c::cs =>
        (buffer := cs; c))
  end

  (* tokens are simply strings; we use no markup *)

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
      let
        val token = case !buffer of
            SOME token => (buffer := NONE; token)
          | NONE => aux [] (get_char ())
      in
        if !SolverSpec.trace > 2 then
          Feedback.HOL_MESG
            ("HolSmtLib: next Z3 proof token is '" ^ token ^ "'")
        else ();
        token
      end
  end

  (***************************************************************************)
  (* auxiliary functions                                                     *)
  (***************************************************************************)

  fun expect_token (expected : string) (actual : string) : unit =
    if expected = actual then
      ()
    else
      raise ERR "expect_token"
        ("'" ^ expected ^ "' expected, but '" ^ actual ^ "' found")

  fun proofterm_id (name : string) : int =
    if String.isPrefix "?x" name then
      let
        val id = Option.valOf (Int.fromString (String.extract (name, 2, NONE)))
          handle Option.Option =>
            raise ERR "proofterm_id" "'?x<integer>' expected"
      in
        if id < 1 then
          raise ERR "proofterm_id" "integer less than 1 found"
        else
          id
      end
    else
      raise ERR "proofterm_id" "'?x' prefix expected"

  fun parse_arbnum (s : string) =
    Arbnum.fromString s
      handle Option.Option =>
        raise ERR "parse_arbnum" ("integer expected, but '" ^ s ^ "' found")

  (***************************************************************************)
  (* parsing of terms                                                        *)
  (***************************************************************************)

  (* In some cases, parsing a token as a term t requires knowledge of
     the argument tokens (for instance, to instantiate types in t
     accordingly). There are several possible solutions. The one
     implemented is the following: 'termfn_of_token' translates a
     token into a function that maps the (possibly empty) list of
     argument terms to a term. *)

  fun zero_args t xs =
    if List.null xs then
      t
    else
      raise ERR "zero_args" "no arguments expected"

  fun one_arg f xs =
    f (Lib.singleton_of_list xs handle Feedback.HOL_ERR _ =>
      raise ERR "one_arg" "one argument expected")

  fun two_args f xs =
    f (Lib.pair_of_list xs handle Feedback.HOL_ERR _ =>
      raise ERR "two_args" "two arguments expected")

  fun three_args f xs =
    f (Lib.triple_of_list xs handle Feedback.HOL_ERR _ =>
      raise ERR "three_args" "three arguments expected")

  fun list_args f xs =
    if List.null xs then
      raise ERR "list_args" "non-empty argument list expected"
    else
      f ts

  (* FIXME: The built-in constants should instead be chosen
            dynamically, based on a parameter that specifies the
            benchmark's SMT-LIB logic. *)

  val builtin_dict = List.foldl
    (fn ((key, value), dict) => Redblackmap.insert (dict, key, value))
    (Redblackmap.mkDict String.compare)
    [
      (* SMT-LIB theory: Core *)
      ("true", zero_args boolSyntax.T),
      ("false", zero_args boolSyntax.F),
      ("not", one_arg boolSyntax.mk_neg),
      ("implies", two_args boolSyntax.mk_imp),  (* FIXME: should be => *)
      ("and", list_args boolSyntax.list_mk_conj),
      ("or", list_args boolSyntax.list_mk_disj),
      ("xor", two_args (fn (t1, t2) => Term.mk_comb (Term.mk_comb
          (Term.prim_mk_const {Thy="HolSmt", Name="xor"}, t1), t2))),
      ("=", two_args boolSyntax.mk_eq),
      ("iff", two_args boolSyntax.mk_eq),
      ("ite", three_args boolSyntax.mk_cond),
      ("if_then_else", three_args boolSyntax.mk_cond),
      (* integer operations *)
      ("-", list_args (fn [t1] => intSyntax.mk_negated t1
        | [t1, t2] => intSyntax.mk_minus (t1, t2)
        | _ => raise ERR "<->" "at most two arguments expected")),
      ("+", two_args intSyntax.mk_plus),
      ("*", two_args intSyntax.mk_mult),
      ("<=", two_args intSyntax.mk_leq),
      ("<", two_args intSyntax.mk_less),
      (">=", two_args intSyntax.mk_geq),
      (">", two_args intSyntax.mk_great),
      (* internal Z3 function for unary negation *)
      ("~", one_arg intSyntax.mk_negated),
      (* distinct *)
      ("distinct", list_args (fn ts => listSyntax.mk_all_distinct
        (listSyntax.mk_list (ts, Term.type_of (List.hd ts))))),
      (* array lookup is translated as function application *)
      ("select", two_args Term.mk_comb),
      (* array update is translated as function update *)
      ("store", three_args (fn (array, index, value) =>
        Term.mk_comb (combinSyntax.mk_update (index, value), array))),
      (* various bit-vector operations *)
      ("bvand", two_args wordsSyntax.mk_word_and),
      ("bvadd", two_args wordsSyntax.mk_word_add),
      ("bvmul", two_args wordsSyntax.mk_word_mul),
      ("bvor", two_args wordsSyntax.mk_word_or),
      ("bvnor", two_args wordsSyntax.mk_word_nor),
      ("bvxor", two_args wordsSyntax.mk_word_xor),
      ("bvsub", two_args wordsSyntax.mk_word_sub),
      (* SMT-LIB states that division by 0w is unspecified. Thus, any
         proof (of unsatisfiability) should also be valid in HOL,
         regardless of how division by 0w is defined in HOL. *)
      ("bvudiv", two_args wordsSyntax.mk_word_div),
      ("bvudiv_i", two_args wordsSyntax.mk_word_div),
      (* presumably bvudiv0 t is an internal Z3 abbreviation for
         bvudiv t 0w *)
      ("bvudiv0", one_arg (fn t =>
        wordsSyntax.mk_word_div (t, wordsSyntax.mk_word (Arbnum.zero,
          fcpLib.index_to_num (wordsSyntax.dim_of t))))),
      ("bvurem", two_args wordsSyntax.mk_word_mod),
      ("bvurem_i", two_args wordsSyntax.mk_word_mod),
      (* presumably bvurem0 t is an internal Z3 abbreviation for
         bvurem t 0w *)
      ("bvurem0", one_arg (fn t =>
        wordsSyntax.mk_word_mod (t, wordsSyntax.mk_word (Arbnum.zero,
          fcpLib.index_to_num (wordsSyntax.dim_of t))))),
      ("bvslt", two_args wordsSyntax.mk_word_lt),
      ("bvult", two_args wordsSyntax.mk_word_lo),
      ("bvsle", two_args wordsSyntax.mk_word_le),
      ("bvule", two_args wordsSyntax.mk_word_ls),
      ("bvsgt", two_args wordsSyntax.mk_word_gt),
      ("bvugt", two_args wordsSyntax.mk_word_hi),
      ("bvsge", two_args wordsSyntax.mk_word_ge),
      ("bvuge", two_args wordsSyntax.mk_word_hs),
      ("bvnot", one_arg wordsSyntax.mk_word_1comp),
      ("bvneg", one_arg wordsSyntax.mk_word_2comp),
      (* (logical) shift left -- the number of bits to shift is given
         by the second argument, which must also be a bit-vector *)
      ("bvshl", two_args (fn (t1, t2) =>
          wordsSyntax.mk_word_lsl (t1, wordsSyntax.mk_w2n t2))),
      (* logical shift right -- the number of bits to shift is given
         by the second argument, which must also be a bit-vector *)
      ("bvlshr", two_args (fn (t1, t2) =>
        wordsSyntax.mk_word_lsr (t1, wordsSyntax.mk_w2n t2))),
      (* arithmetic shift right -- the number of bits to shift is given
         by the second argument, which must also be a bit-vector *)
      ("bvashr", two_args (fn (t1, t2) =>
        wordsSyntax.mk_word_asr (t1, wordsSyntax.mk_w2n t2))),
      (* bit-vector concatenation *)
      ("concat", two_args wordsSyntax.mk_word_concat)
    ]

  fun termfn_of_token dict (token : string) : Term.term list -> Term.term =
    case Redblackmap.peek (dict, token) of
      SOME termfn => termfn
    | NONE =>
      if String.isPrefix "bv" token then
        (* bit-vector literals (numeric value m, bit-width n) *)
        let
          val fields = String.fields (fn c => Lib.mem c [#"[", #"]"])
            (String.extract (token, 2, NONE))
          val (m, n) = case fields of [m, n, ""] => (m, n)
            | _ =>
              raise ERR "termfn_of_token"
                ("failed to parse '" ^ token ^ "' as a bit-vector literal")
        in
          zero_args (wordsSyntax.mk_word (parse_arbnum m, parse_arbnum n))
        end
      else if String.isPrefix "extract" token then
        (* extracting bits m to n from a bit-vector *)
        let
          val fields = String.fields (fn c => Lib.mem c [#"[", #":", #"]"])
            (String.extract (token, 7, NONE))
          val (m, n) = case fields of ["", m, n, ""] => (m, n)
            | _ =>
              raise ERR "termfn_of_token"
                ("failed to parse '" ^ token ^ "' as extract[m:n]")
          val m = parse_arbnum m
          val n = parse_arbnum n
          val index_type = fcpLib.index_type (Arbnum.plus1 (Arbnum.- (m, n)))
          val m = numSyntax.mk_numeral m
          val n = numSyntax.mk_numeral n
        in
          one_arg (fn t => wordsSyntax.mk_word_extract (m, n, t, index_type))
        end
      else if String.isPrefix "zero_extend" token then
        (* prepending n 0-bits to a bit vector *)
        let
          val fields = String.fields (fn c => Lib.mem c [#"[", #"]"])
            (String.extract (token, 11, NONE))
          val n = case fields of ["", n, ""] => n
            | _ =>
              raise ERR "termfn_of_token"
                ("failed to parse '" ^ token ^ "' as zero_extend[n]")
          val n = parse_arbnum n
        in
          one_arg (fn t => wordsSyntax.mk_w2w (t, fcpLib.index_type
            (Arbnum.+ (fcpLib.index_to_num (wordsSyntax.dim_of t), n))))
        end
      else if String.isPrefix "sign_extend" token then
        (* prepending the sign (i.e., the most significant bit) n
           times to a bit vector *)
        let
          val fields = String.fields (fn c => Lib.mem c [#"[", #"]"])
            (String.extract (token, 11, NONE))
          val n = case fields of ["", n, ""] => n
            | _ =>
              raise ERR "termfn_of_token"
                ("failed to parse '" ^ token ^ "' as sign_extend[n]")
          val n = parse_arbnum n
        in
          one_arg (fn t => wordsSyntax.mk_sw2sw (t, fcpLib.index_type
            (Arbnum.+ (fcpLib.index_to_num (wordsSyntax.dim_of t), n))))
        end
      else if String.isPrefix "rotate_left" token then
        (* bit rotation to the left, by n bits *)
        let
          val fields = String.fields (fn c => Lib.mem c [#"[", #"]"])
            (String.extract (token, 11, NONE))
          val n = case fields of ["", n, ""] => n
            | _ =>
              raise ERR "termfn_of_token"
                ("failed to parse '" ^ token ^ "' as rotate_left[n]")
          val n = numSyntax.mk_numeral (parse_arbnum n)
        in
          one_arg (fn t => wordsSyntax.mk_word_rol (t, n))
        end
      else if String.isPrefix "repeat" token then
        (* concatenation of n copies of a bit-vector *)
        let
          val fields = String.fields (fn c => Lib.mem c [#"[", #"]"])
            (String.extract (token, 6, NONE))
          val n = case fields of ["", n, ""] => n
            | _ =>
              raise ERR "termfn_of_token"
                ("failed to parse '" ^ token ^ "' as repeat[n]")
          val n = parse_arbnum n
          val num = numSyntax.mk_numeral n
        in
          one_arg (fn t => wordsSyntax.mk_word_replicate (num, t))
        end
      else if String.isPrefix "array_ext" token then
        (* we can infer T in array_ext[T] from either argument array,
           so we just ignore it here (without any checking) *)
        two_args (fn (t1, t2) => boolSyntax.list_mk_icomb
          (Term.prim_mk_const {Thy="HolSmt", Name="array_ext"}, [t1, t2]))
      else
        (* integer literals *)
        (zero_args (intSyntax.term_of_int (Arbint.fromString token))
          handle Option.Option =>
            (* FIXME: This is a horrible hack to (heuristically) undo
                      some horrible Z3 symbol mangling, which replaces
                      . by _ in identifiers. *)
            let
              val fields = String.fields (Lib.equal #"_") token
              fun foldthis (name, termfn, result) =
                if fields = String.fields (fn c => Lib.mem c [#"_", #"."]) name
                    then (
                  if Option.isSome result then
                    raise ERR "termfn_of_token"
                      ("symbol '" ^ token ^ "' is ambiguous")
                  else
                    SOME termfn
                ) else result
            in
              if List.length fields = 1 then
                raise ERR "termfn_of_token"
                  ("undeclared symbol '" ^ token ^ "'")
              else
                case Redblackmap.foldl foldthis NONE dict of
                  SOME termfn => termfn
                | NONE =>
                  raise ERR "termfn_of_token"
                    ("undeclared symbol '" ^ token ^ "'")
            end)

  fun parse_termlist get_token dict (acc : Term.term list) : Term.term list =
  let
    val head = get_token ()
  in
    if head = ")" then
      List.rev acc
    else if head = "(" then
      parse_termlist get_token dict
        (parse_compound_term get_token dict (get_token ()) :: acc)
    else
      parse_termlist get_token dict (termfn_of_token dict head [] :: acc)
  end

  and parse_compound_term get_token dict (head : string) : Term.term =
  let
    val headfn = termfn_of_token dict head
    val operands = parse_termlist get_token dict []
  in
    headfn operands
  end

  (***************************************************************************)
  (* parsing of proofterms                                                   *)
  (***************************************************************************)

  fun zero_prems (prems, concl) =
    if List.null prems then
      concl
    else
      raise ERR "zero_prems" "no premises expected"

  fun one_prem (prems, concl) =
    (Lib.singleton_of_list prems, concl)
    handle Feedback.HOL_ERR _ =>
      raise ERR "one_prem" "one premise expected"

  fun two_prems (prems, concl) =
    Lib.uncurry Lib.triple (Lib.pair_of_list prems) concl
    handle Feedback.HOL_ERR _ =>
      raise ERR "two_prems" "two premises expected"

  fun list_prems (prems, concl) =
    (prems, concl)

  val rule_parsers = List.foldl
    (fn ((key, value), dict) => Redblackmap.insert (dict, key, value))
    (Redblackmap.mkDict String.compare)
    [
      ("and_elim",        AND_ELIM o one_prem),
      ("asserted",        ASSERTED o zero_prems),
      ("commutativity",   COMMUTATIVITY o zero_prems),
      ("def_axiom",       DEF_AXIOM o zero_prems),
      ("elim_unused",     ELIM_UNUSED o zero_prems),
      ("hypothesis",      HYPOTHESIS o zero_prems),
      ("lemma",           LEMMA o one_prem),
      ("monotonicity",    MONOTONICITY o list_prems),
      ("mp",              MP o two_prems),
      ("not_or_elim",     NOT_OR_ELIM o one_prem),
      ("quant_intro",     QUANT_INTRO o one_prem),
      ("rewrite",         REWRITE o zero_prems),
      ("symm",            SYMM o one_prem),
      ("th_lemma[arith]", TH_LEMMA_ARITH o list_prems),
      ("th_lemma[array]", TH_LEMMA_ARRAY o list_prems),
      ("th_lemma[basic]", TH_LEMMA_BASIC o list_prems),
      ("th_lemma[bv]",    TH_LEMMA_BV o list_prems),
      ("trans",           TRANS o two_prems),
      ("true_axiom",      TRUE_AXIOM o zero_prems),
      ("unit_resolution", UNIT_RESOLUTION o list_prems)
    ]

  datatype PROOFTERM_TERM = PROOFTERM of proofterm | TERM of Term.term

  (* FIXME: I am hoping that the Z3 proof format will be changed so
            that this non-determinism/lookahead in the parser will no
            longer be necessary.  It would suffice to enclose each
            inference rule's list of premises in parentheses; then the
            parser would find a ")" token once it has parsed the last
            premise. *)

  (* parses an s-expression that is either a proofterm or a term *)
  fun parse_proofterm_or_term get_token dict =
  let
    val head = get_token ()
  in
    if head = "(" then
      let
        val head = get_token ()
      in
        case Redblackmap.peek (rule_parsers, head) of
          SOME parsefn =>
            PROOFTERM (parse_compound_proofterm get_token dict parsefn)
        | NONE =>
            TERM (parse_compound_term get_token dict head)
      end
    else
      TERM (termfn_of_token dict head [])
        handle Feedback.HOL_ERR _ =>
          PROOFTERM (ID (proofterm_id head))
        handle Feedback.HOL_ERR _ =>
          raise ERR "parse_proofterm_or_term" ("invalid token '" ^ head ^ "'")
  end

  (* parses a list of proofterms, followed by a single term *)
  and parse_prooftermlist_term get_token dict acc : proofterm list * Term.term =
    case parse_proofterm_or_term get_token dict of
      PROOFTERM pt => parse_prooftermlist_term get_token dict (pt :: acc)
    | TERM t => (List.rev acc, t)

  (* parses a single compound proofterm, with the rule already parsed
     as 'parsefn' *)
  and parse_compound_proofterm get_token dict parsefn : proofterm =
    parsefn (parse_prooftermlist_term get_token dict [])
      before expect_token ")" (get_token ())

  (***************************************************************************)
  (* parsing of let definitions                                              *)
  (***************************************************************************)

  (* returns an extended dictionary *)
  fun parse_term_definition get_token dict (name : string, head :string) =
  let
    val _ = if !SolverSpec.trace > 0 andalso
      Option.isSome (Redblackmap.peek (dict, name)) then
        WARNING "parse_term_definition"
          ("term name '" ^ name ^ "' defined more than once")
      else ()
    val t = parse_compound_term get_token dict head
  in
    Redblackmap.insert (dict, name,
      (* we only allow term definitions for ground terms (which take
         no arguments), not for functions *)
      fn [] => t
        | _ => raise ERR ("<" ^ name ^ ">") "no arguments expected")
  end

  (* returns an extended proof *)
  fun parse_proofterm_definition get_token (dict, proof) (id : int, parsefn) =
  let
    val _ = if !SolverSpec.trace > 0 andalso
      Option.isSome (Redblackmap.peek (proof, id)) then
        WARNING "parse_proofterm_definition"
          ("proofterm ID " ^ Int.toString id ^ " defined more than once")
      else ()
    val pt = parse_compound_proofterm get_token dict parsefn
  in
    Redblackmap.insert (proof, id, pt)
  end

  (* distinguishes between a term definition and a proofterm
     definition; returns a (possibly extended) dictionary and proof *)
  fun parse_definition get_token (dict, proof) =
  let
    val _ = expect_token "(" (get_token ())
    val name = get_token ()
    val _ = expect_token "(" (get_token ())
    val head = get_token ()
  in
    (case Redblackmap.peek (rule_parsers, head) of
      SOME parsefn =>
        (dict, parse_proofterm_definition get_token (dict, proof)
          (proofterm_id name, parsefn))
    | NONE =>
      (parse_term_definition get_token dict (name, head), proof))
    before expect_token ")" (get_token ())
  end

  (* entry point into the parser (i.e., the grammar's start symbol) *)
  fun parse_proof get_token (dict, proof) (rpars : int) =
  let
    val _ = expect_token "(" (get_token ())
    val head = get_token ()
  in
    if head = "let" then
      parse_proof get_token (parse_definition get_token (dict, proof))
        (rpars + 1)
    else
      case Redblackmap.peek (rule_parsers, head) of
        SOME parsefn =>
          (* Z3 assigns no ID to the final proof step; we use ID 0 *)
          parse_proofterm_definition get_token (dict, proof) (0, parsefn)
            before
              Lib.funpow rpars (fn () => expect_token ")" (get_token ())) ()
      | NONE =>
          raise ERR "parse_proof" ("unknown inference rule '" ^ head ^ "'")
  end

in

  (* 'parse_file' takes two arguments: first, a dictionary mapping
     names (namely those declared in the SMT-LIB input benchmark) to
     HOL terms; second, the name of the proof file. *)
  fun parse_file (user_dict : (string, Term.term) Redblackmap.dict)
                 (path : string) : proof =
  let
    (* form the union of built-in names and user-declared names *)
    fun map_insert (name, term, dict) =
    (
      if !SolverSpec.trace > 0 andalso
          Option.isSome (Redblackmap.peek (dict, name)) then
        WARNING "parse_file"
          ("user declaration redefines built-in name '" ^ name ^ "'")
      else ();
      Redblackmap.insert (dict, name, fn args => Term.list_mk_comb (term, args))
    )
    val dict = Redblackmap.foldl map_insert builtin_dict user_dict
    (* parse the file contents *)
    val _ = if !SolverSpec.trace > 1 then
        Feedback.HOL_MESG ("HolSmtLib: parsing Z3 proof file '" ^ path ^ "'")
      else ()
    val instream = TextIO.openIn path
    val get_token = get_token (get_buffered_char instream)
    val proof = parse_proof get_token (dict, Redblackmap.mkDict Int.compare) 0
    val _ = if !SolverSpec.trace > 0 then
        WARNING "parse_file" ("ignoring token '" ^ get_token () ^
          "' (and perhaps others) after proof")
          handle Feedback.HOL_ERR _ => ()  (* end of file, as expected *)
      else ()
    val _ = TextIO.closeIn instream
  in
    proof
  end

end  (* local *)

end
