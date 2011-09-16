(* Copyright (c) 2009-2011 Tjark Weber. All rights reserved. *)

(* Proof reconstruction for Z3: parsing of Z3's proofs *)

structure Z3_ProofParser =
struct

  (* I tried to implement this parser in ML-Lex/ML-Yacc, but gave up
     on that -- mainly for two reasons: 1. The whole toolchain/build
     process gets more complicated. 2. Performance and memory usage of
     the generated parser were far from satisfactory (probably because
     my naive definition of the underlying grammar required the parser
     to maintain a large stack internally). *)

local

  local open HolSmtTheory in end

  open Z3_Proof

  val ERR = Feedback.mk_HOL_ERR "Z3_ProofParser"
  val WARNING = Feedback.HOL_WARNING "Z3_ProofParser"

  (***************************************************************************)
  (* auxiliary functions                                                     *)
  (***************************************************************************)

  fun proofterm_id (name : string) : int =
    if String.isPrefix "@x" name then
      let
        val id = Option.valOf (Int.fromString (String.extract (name, 2, NONE)))
          handle Option.Option =>
            raise ERR "proofterm_id" "'@x' not followed by an integer"
      in
        if id < 1 then
          raise ERR "proofterm_id" "integer less than 1 found"
        else
          id
      end
    else
      raise ERR "proofterm_id" "'@x' prefix expected"

  (***************************************************************************)
  (* parsing Z3 proofterms as terms                                          *)
  (***************************************************************************)

  (* Z3 proofterms are essentially encoded in SMT-LIB term syntax, so
     we re-use the SMT-LIB parser. *)

  (* FIXME: However, there is a problem: the last argument to each
     inference rule is the inferred conclusion (thus, a term), whereas
     previous arguments are premises (thus, proofterms).
     Unfortunately, the parser does not know whether it is parsing the
     last argument until after it has parsed it.  We therefore parse
     proofterms and terms uniformly as HOL terms, encoding the former
     as terms of type :'pt.  Note that the current implementation
     might parse certain terms (namely those containing functions
     whose names coincide with Z3 inference rule names) erroneously as
     proofterms.

     I am hoping that the Z3 proof format will eventually be changed
     so that this is no longer an issue in the parser.  It would
     suffice to enclose each inference rule's list of premises in
     parentheses; then the parser would find a ")" token once it has
     parsed the last premise, and can continue by parsing a term. *)

  val pt_ty = Type.mk_vartype "'pt"

  fun zero_prems name =
    SmtLib_Theories.K_zero_one (Lib.curry Term.mk_comb (Term.mk_var
      (name, Type.--> (Type.bool, pt_ty))))

  fun one_prem name =
    SmtLib_Theories.K_zero_two (Lib.uncurry (Lib.curry Term.mk_comb o
      Lib.curry Term.mk_comb (Term.mk_var (name, boolSyntax.list_mk_fun
      ([pt_ty, Type.bool], pt_ty)))))

  fun two_prems name =
  let
    val t = Term.mk_var (name,
      boolSyntax.list_mk_fun ([pt_ty, pt_ty, Type.bool], pt_ty))
  in
    SmtLib_Theories.K_zero_three (fn (p1, p2, concl) =>
      Term.list_mk_comb (t, [p1, p2, concl]))
  end

  fun list_prems name =
    SmtLib_Theories.K_zero_list (Lib.uncurry (Lib.curry Term.mk_comb o
      (Lib.curry Term.mk_comb (Term.mk_var (name, boolSyntax.list_mk_fun
      ([listSyntax.mk_list_type pt_ty, Type.bool], pt_ty))))) o
      Lib.apfst (Lib.C (Lib.curry listSyntax.mk_list) pt_ty) o Lib.front_last)

  val z3_builtin_dict = Library.dict_from_list [
    ("and-elim",        one_prem "and-elim"),
    ("asserted",        zero_prems "asserted"),
    ("commutativity",   zero_prems "commutativity"),
    ("def-axiom",       zero_prems "def-axiom"),
    ("elim-unused",     zero_prems "elim-unused"),
    ("hypothesis",      zero_prems "hypothesis"),
    ("iff-true",        one_prem "iff-true"),
    ("lemma",           one_prem "lemma"),
    ("monotonicity",    list_prems "monotonicity"),
    ("mp",              two_prems "mp"),
    ("not-or-elim",     one_prem "not-or-elim"),
    ("quant-intro",     one_prem "quant-intro"),
    ("rewrite",         zero_prems "rewrite"),
    ("symm",            one_prem "symm"),
    ("th-lemma-arith",  list_prems "th-lemma-arith"),
    ("th-lemma-array",  list_prems "th-lemma-array"),
    ("th-lemma-basic",  list_prems "th-lemma-basic"),
    ("th-lemma-bv",     list_prems "th-lemma-bv"),
    ("trans",           two_prems "trans"),
    ("true-axiom",      zero_prems "true-axiom"),
    ("unit-resolution", list_prems "unit-resolution"),

    (* FIXME: I am hoping that the Z3 proof format will eventually be
       changed to adhere to the SMT-LIB format more strictly, i.e.,
       also for the following operations/constants, so that these
       additional parsing functions are no longer necessary. *)
    ("iff", SmtLib_Theories.K_zero_two boolSyntax.mk_eq),
    ("implies", SmtLib_Theories.K_zero_two boolSyntax.mk_imp),
    ("~", SmtLib_Theories.K_zero_one intSyntax.mk_negated),
    ("~", SmtLib_Theories.K_zero_one realSyntax.mk_negated),
    (* bit-vector constants: bvm[n] *)
    ("_", SmtLib_Theories.zero_zero (fn token =>
      if String.isPrefix "bv" token then
        let
          val args = String.extract (token, 2, NONE)
          val (value, args) = Lib.pair_of_list (String.fields (Lib.equal #"[")
            args)
          val (size, args) = Lib.pair_of_list (String.fields (Lib.equal #"]")
            args)
          val _ = args = "" orelse
            raise ERR "<z3_builtin_dict._>" "not a bit-vector constant"
          val value = Library.parse_arbnum value
          val size = Library.parse_arbnum size
        in
          wordsSyntax.mk_word (value, size)
        end
      else
        raise ERR "<z3_builtin_dict._>" "not a bit-vector constant")),
    (* extract[m:n] t *)
    ("_", SmtLib_Theories.zero_one (fn token =>
      if String.isPrefix "extract[" token then
        let
          val args = String.extract (token, 8, NONE)
          val (m, args) = Lib.pair_of_list (String.fields (Lib.equal #":") args)
          val (n, args) = Lib.pair_of_list (String.fields (Lib.equal #"]") args)
          val _ = args = "" orelse
            raise ERR "<z3_builtin_dict._>" "not extract[m:n]"
          val m = Library.parse_arbnum m
          val n = Library.parse_arbnum n
          val index_type = fcpLib.index_type (Arbnum.plus1 (Arbnum.- (m, n)))
          val m = numSyntax.mk_numeral m
          val n = numSyntax.mk_numeral n
        in
          fn t => wordsSyntax.mk_word_extract (m, n, t, index_type)
        end
      else
        raise ERR "<z3_builtin_dict._>" "not extract[m:n]")),
    (* (_ extractm n) t *)
    ("_", SmtLib_Theories.one_one (fn token => fn n =>
      if String.isPrefix "extract" token then
        let
          val m = Library.parse_arbnum (String.extract (token, 7, NONE))
          val index_type = fcpLib.index_type (Arbnum.plus1 (Arbnum.- (m, n)))
          val m = numSyntax.mk_numeral m
          val n = numSyntax.mk_numeral n
        in
          fn t => wordsSyntax.mk_word_extract (m, n, t, index_type)
        end
      else
        raise ERR "<z3_builtin_dict._>" "not extract<m> n")),
    ("bvudiv_i", SmtLib_Theories.K_zero_two wordsSyntax.mk_word_div),
    ("bvurem_i", SmtLib_Theories.K_zero_two wordsSyntax.mk_word_mod),
    (* bvudiv0 t *)
    ("bvudiv0", SmtLib_Theories.K_zero_one (fn t =>
      let
        val zero = wordsSyntax.mk_n2w (numSyntax.zero_tm, wordsSyntax.dim_of t)
      in
        wordsSyntax.mk_word_div (t, zero)
      end)),
    (* bvurem0 t *)
    ("bvurem0", SmtLib_Theories.K_zero_one (fn t =>
      let
        val zero = wordsSyntax.mk_n2w (numSyntax.zero_tm, wordsSyntax.dim_of t)
      in
        wordsSyntax.mk_word_mod (t, zero)
      end)),
    (* array_extArray[m:n] t1 t2 *)
    ("_", SmtLib_Theories.zero_two (fn token =>
      if String.isPrefix "array_ext" token then
        (fn (t1, t2) => Term.mk_comb (boolSyntax.mk_icomb
          (Term.prim_mk_const {Thy="HolSmt", Name="array_ext"}, t1), t2))
      else
        raise ERR "<z3_builtin_dict._>" "not array_ext...")),
    (* repeatn t *)
    ("_", SmtLib_Theories.zero_one (fn token =>
      if String.isPrefix "repeat" token then
        let
          val n = Library.parse_arbnum (String.extract (token, 6, NONE))
          val n = numSyntax.mk_numeral n
        in
          fn t => wordsSyntax.mk_word_replicate (n, t)
        end
      else
        raise ERR "<z3_builtin_dict._>" "not repeat<n>")),
    (* zero_extendn t *)
    ("_", SmtLib_Theories.zero_one (fn token =>
      if String.isPrefix "zero_extend" token then
        let
          val n = Library.parse_arbnum (String.extract (token, 11, NONE))
        in
          fn t => wordsSyntax.mk_w2w (t, fcpLib.index_type
            (Arbnum.+ (fcpLib.index_to_num (wordsSyntax.dim_of t), n)))
        end
      else
        raise ERR "<z3_builtin_dict._>" "not zero_extend<n>")),
    (* sign_extendn t *)
    ("_", SmtLib_Theories.zero_one (fn token =>
      if String.isPrefix "sign_extend" token then
        let
          val n = Library.parse_arbnum (String.extract (token, 11, NONE))
        in
          fn t => wordsSyntax.mk_sw2sw (t, fcpLib.index_type
            (Arbnum.+ (fcpLib.index_to_num (wordsSyntax.dim_of t), n)))
        end
      else
        raise ERR "<z3_builtin_dict._>" "not sign_extend<n>")),
    (* rotate_leftn t *)
    ("_", SmtLib_Theories.zero_one (fn token =>
      if String.isPrefix "rotate_left" token then
        let
          val n = Library.parse_arbnum (String.extract (token, 11, NONE))
          val n = numSyntax.mk_numeral n
        in
          fn t => wordsSyntax.mk_word_rol (t, n)
        end
      else
        raise ERR "<z3_builtin_dict._>" "not rotate_left<n>"))
  ]

  (***************************************************************************)
  (* turning terms into Z3 proofterms                                        *)
  (***************************************************************************)

  (* we use a reference to implement recursion through this dictionary *)
  val pt_dict = ref (Redblackmap.mkDict String.compare
    : (string, Term.term list -> proofterm) Redblackmap.dict)

  fun proofterm_of_term t =
  let
    val (hd, args) = boolSyntax.strip_comb t
    val name = Lib.fst (Term.dest_var hd)
  in
    Redblackmap.find (!pt_dict, name) args
      handle Redblackmap.NotFound =>
        ID (proofterm_id (Lib.fst (Term.dest_var t)))
      handle Feedback.HOL_ERR _ =>
        raise ERR "proofterm_of_term" "term does not encode a Z3 proofterm"
  end

  val zero_prems_pt = SmtLib_Theories.one_arg

  fun one_prem_pt f = SmtLib_Theories.two_args (f o Lib.apfst proofterm_of_term)

  fun two_prems_pt f = SmtLib_Theories.three_args (fn (t1, t2, t3) =>
    f (proofterm_of_term t1, proofterm_of_term t2, t3))

  fun list_prems_pt f =
    SmtLib_Theories.two_args (f o Lib.apfst
      (List.map proofterm_of_term o Lib.fst o listSyntax.dest_list))

  val _ = pt_dict := List.foldl
    (fn ((key, value), dict) => Redblackmap.insert (dict, key, value))
    (!pt_dict)
    [
      ("and-elim",        one_prem_pt AND_ELIM),
      ("asserted",        zero_prems_pt ASSERTED),
      ("commutativity",   zero_prems_pt COMMUTATIVITY),
      ("def-axiom",       zero_prems_pt DEF_AXIOM),
      ("elim-unused",     zero_prems_pt ELIM_UNUSED),
      ("hypothesis",      zero_prems_pt HYPOTHESIS),
      ("iff-true",        one_prem_pt IFF_TRUE),
      ("lemma",           one_prem_pt LEMMA),
      ("monotonicity",    list_prems_pt MONOTONICITY),
      ("mp",              two_prems_pt MP),
      ("not-or-elim",     one_prem_pt NOT_OR_ELIM),
      ("quant-intro",     one_prem_pt QUANT_INTRO),
      ("rewrite",         zero_prems_pt REWRITE),
      ("symm",            one_prem_pt SYMM),
      ("th-lemma-arith",  list_prems_pt TH_LEMMA_ARITH),
      ("th-lemma-array",  list_prems_pt TH_LEMMA_ARRAY),
      ("th-lemma-basic",  list_prems_pt TH_LEMMA_BASIC),
      ("th-lemma-bv",     list_prems_pt TH_LEMMA_BV),
      ("trans",           two_prems_pt TRANS),
      ("true-axiom",      zero_prems_pt TRUE_AXIOM),
      ("unit-resolution", list_prems_pt UNIT_RESOLUTION)
    ]

  (***************************************************************************)
  (* parsing of let definitions                                              *)
  (***************************************************************************)

  (* returns an extended proof; 't' must encode a proofterm *)
  fun extend_proof proof (id, t) =
  let
    val _ = if !Library.trace > 0 andalso
      Option.isSome (Redblackmap.peek (proof, id)) then
        WARNING "extend_proof"
          ("proofterm ID " ^ Int.toString id ^ " defined more than once")
      else ()
  in
    Redblackmap.insert (proof, id, proofterm_of_term t)
  end

  (* distinguishes between a term definition and a proofterm
     definition; returns a (possibly extended) dictionary and proof *)
  fun parse_definition get_token (tydict, tmdict, proof) =
  let
    val _ = Library.expect_token "(" (get_token ())
    val _ = Library.expect_token "(" (get_token ())
    val name = get_token ()
    val t = SmtLib_Parser.parse_term get_token (tydict, tmdict)
    val _ = Library.expect_token ")" (get_token ())
    val _ = Library.expect_token ")" (get_token ())
  in
    if String.isPrefix "@x" name then
      (* proofterm definition *)
      let
        val tmdict = Library.extend_dict ((name, SmtLib_Theories.K_zero_zero
          (Term.mk_var (name, pt_ty))), tmdict)
        val proof = extend_proof proof (proofterm_id name, t)
      in
        (tmdict, proof)
      end
    else
      (* term definition *)
      (Library.extend_dict ((name, SmtLib_Theories.K_zero_zero t), tmdict),
        proof)
  end

  (* entry point into the parser (i.e., the grammar's start symbol) *)
  fun parse_proof get_token (tydict, tmdict, proof) (rpars : int) =
  let
    val _ = Library.expect_token "(" (get_token ())
    val head = get_token ()
  in
    if head = "let" then
      let
        val (tmdict, proof) = parse_definition get_token (tydict, tmdict, proof)
      in
        parse_proof get_token (tydict, tmdict, proof) (rpars + 1)
      end
    else if head = "error" then (
      (* some (otherwise valid) proofs are preceded by an error message,
         which we simply ignore *)
      get_token ();
      Library.expect_token ")" (get_token ());
      parse_proof get_token (tydict, tmdict, proof) rpars
    ) else
      let
        (* undo look-ahead of 2 tokens *)
        val buffer = ref ["(", head]
        fun get_token' () =
          case !buffer of
            [] => get_token ()
          | x::xs => (buffer := xs; x)
        val t = SmtLib_Parser.parse_term get_token' (tydict, tmdict)
      in
        (* Z3 assigns no ID to the final proof step; we use ID 0 *)
        extend_proof proof (0, t) before Lib.funpow rpars
          (fn () => Library.expect_token ")" (get_token ())) ()
      end
  end

in

  (* Similar to 'parse_file' below, but for instreams.  Does not close
     the instream. *)

  fun parse_stream (tydict : (string, Type.hol_type SmtLib_Parser.parse_fn list)
    Redblackmap.dict, tmdict : (string, Term.term SmtLib_Parser.parse_fn list)
    Redblackmap.dict) (instream : TextIO.instream) : proof =
  let
    (* union of user-declared names and Z3's inference rule names *)
    val tmdict = Library.union_dict tmdict z3_builtin_dict
    (* parse the stream *)
    val _ = if !Library.trace > 1 then
        Feedback.HOL_MESG "HolSmtLib: parsing Z3 proof"
      else ()
    val get_token = Library.get_token (Library.get_buffered_char instream)
    val proof = parse_proof get_token
      (tydict, tmdict, Redblackmap.mkDict Int.compare) 0
    val _ = if !Library.trace > 0 then
        WARNING "parse_stream" ("ignoring token '" ^ get_token () ^
          "' (and perhaps others) after proof")
          handle Feedback.HOL_ERR _ => ()  (* end of stream, as expected *)
      else ()
  in
    proof
  end

  (* Function 'parse_file' parses Z3's response to the SMT2
     (get-proof) command (for an unsatisfiable problem, with proofs
     enabled in Z3, i.e., using option "PROOF_MODE=2").  It has been
     tested with proofs generated by Z3 2.13 (which was released in
     October 2010).  'parse_file' takes three arguments: two
     dictionaries mapping names of types and terms (namely those
     declared in the SMT-LIB benchmark) to lists of parsing functions
     (cf. 'SmtLib_Parser.parse_file'); and the name of the proof
     file. *)

  fun parse_file (tydict, tmdict) (path : string) : proof =
  let
    val instream = TextIO.openIn path
  in
    parse_stream (tydict, tmdict) instream
      before TextIO.closeIn instream
  end

end  (* local *)

end
