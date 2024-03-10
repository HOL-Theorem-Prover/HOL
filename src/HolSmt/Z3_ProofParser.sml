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

  fun list_args_zero_prems name =
    SmtLib_Theories.K_list_one (fn indices => fn term =>
      let
        val arg_types = List.map Term.type_of indices
        val fn_type = arg_types @ [Type.bool]
        val t = Term.mk_var (name, boolSyntax.list_mk_fun (fn_type, pt_ty))
        val args = indices @ [term]
      in
        Term.list_mk_comb (t, args)
      end)

  (* This function is used only to allow some symbols used as indices in indexed
     identifiers to be parsed (as terms) without the parser erroring out due to
     not having the symbols in the term dictionary. *)
  fun builtin_name name =
    SmtLib_Theories.K_zero_zero (Term.mk_var (name, Type.alpha))

  val z3_builtin_dict = Library.dict_from_list [
    ("and-elim",        one_prem "and-elim"),
    (* the following is used in `(_ th-lemma arith ...)` inference rules *)
    ("arith",           builtin_name "arith"),
    (* the following is used in `(_ th-lemma bv ...)` inference rules *)
    ("bv",              builtin_name "bv"),
    ("asserted",        zero_prems "asserted"),
    ("commutativity",   zero_prems "commutativity"),
    ("def-axiom",       zero_prems "def-axiom"),
    ("elim-unused",     zero_prems "elim-unused"),
    (* the following is used in `(_ th-lemma arith ...)` inference rules *)
    ("eq-propagate",    builtin_name "eq-propagate"),
    (* the following is used in `(_ th-lemma arith ...)` inference rules *)
    ("farkas",          builtin_name "farkas"),
    ("hypothesis",      zero_prems "hypothesis"),
    ("iff-true",        one_prem "iff-true"),
    ("intro-def",       zero_prems "intro-def"),
    ("lemma",           one_prem "lemma"),
    ("monotonicity",    list_prems "monotonicity"),
    ("mp",              two_prems "mp"),
    ("mp~",             two_prems "mp~"),
    ("nnf-neg",         list_prems "nnf-neg"),
    ("nnf-pos",         list_prems "nnf-pos"),
    ("not-or-elim",     one_prem "not-or-elim"),
    (* `proof-bind` doesn't seem to have semantic value, despite the Z3 v4.12.4
       source code implying that it either introduces lambda abstractions or
       `forall` quantifiers, depending on the interpretation *)
    ("proof-bind",      SmtLib_Theories.K_zero_one Lib.I),
    ("quant-inst",      list_args_zero_prems "quant-inst"),
    ("quant-intro",     one_prem "quant-intro"),
    ("refl",            zero_prems "refl"),
    ("rewrite",         zero_prems "rewrite"),
    ("sk",              zero_prems "sk"),
    ("symm",            one_prem "symm"),
    ("th-lemma",        SmtLib_Theories.list_list (fn token => fn indices =>
      fn prems =>
        let
          (* Parsing this rule: (_ |th-lemma| arith farkas 1 1 1)
             The vertical bars have already been eliminated in the tokenizer, so
             we're already matching "th-lemma".

             The indices will be passed as [``arith``, ``farkas``, ``1``, ``1``,
             ``1``] but currently we only care about the first one (the theory
             name), so we'll discard the rest.

             We'll change the name of the rule to "th-lemma-<theory>" which will
             later hook into the theory-specific rule processing. *)
          val theory_tm = List.hd indices
          val theory_str = Lib.fst (Term.dest_var theory_tm)
          val name = "th-lemma-" ^ theory_str
        in
          list_prems name token [] prems
        end)),
    ("trans",           two_prems "trans"),
    ("trans*",          list_prems "trans*"),
    (* the following is used in `(_ th-lemma arith ...)` inference rules *)
    ("triangle-eq",     builtin_name "triangle-eq"),
    ("true-axiom",      zero_prems "true-axiom"),
    ("unit-resolution", list_prems "unit-resolution"),

    (* FIXME: I am hoping that the Z3 proof format will eventually be
       changed to adhere to the SMT-LIB format more strictly, i.e.,
       also for the following operations/constants, so that these
       additional parsing functions are no longer necessary. *)
    ("iff", SmtLib_Theories.K_zero_two boolSyntax.mk_eq),
    ("implies", SmtLib_Theories.K_zero_two boolSyntax.mk_imp),
    (* equivalence modulo naming *)
    ("~", SmtLib_Theories.K_zero_two boolSyntax.mk_eq),
    (* the following two are the unary arithmetic negation operator *)
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
    ("_", SmtLib_Theories.one_one (fn token => fn n_tm =>
      if String.isPrefix "extract" token then
        let
          val m_str = String.extract (token, 7, NONE)
          val m = Library.parse_arbnum m_str
          val n = Arbint.toNat (intSyntax.int_of_term n_tm)
          val index_type = fcpLib.index_type (Arbnum.plus1 (Arbnum.- (m, n)))
          val (m, n) = Lib.pair_map numSyntax.mk_numeral (m, n)
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
        raise ERR "proofterm_of_term" ("term <" ^ Hol_pp.term_to_string t ^
          "> does not encode a Z3 proofterm")
  end

  val zero_prems_pt = SmtLib_Theories.one_arg

  fun one_prem_pt f = SmtLib_Theories.two_args (f o Lib.apfst proofterm_of_term)

  fun two_prems_pt f = SmtLib_Theories.three_args (fn (t1, t2, t3) =>
    f (proofterm_of_term t1, proofterm_of_term t2, t3))

  fun list_prems_pt f =
    SmtLib_Theories.two_args (f o Lib.apfst
      (List.map proofterm_of_term o Lib.fst o listSyntax.dest_list))

  fun list_args_zero_prems_pt f = f o Lib.front_last

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
      ("intro-def",       zero_prems_pt INTRO_DEF),
      ("lemma",           one_prem_pt LEMMA),
      ("monotonicity",    list_prems_pt MONOTONICITY),
      ("mp",              two_prems_pt MP),
      ("mp~",             two_prems_pt MP_EQ),
      ("nnf-neg",         list_prems_pt NNF_NEG),
      ("nnf-pos",         list_prems_pt NNF_POS),
      ("not-or-elim",     one_prem_pt NOT_OR_ELIM),
      ("quant-inst",      list_args_zero_prems_pt QUANT_INST),
      ("quant-intro",     one_prem_pt QUANT_INTRO),
      ("refl",            zero_prems_pt REFL),
      ("rewrite",         zero_prems_pt REWRITE),
      ("sk",              zero_prems_pt SKOLEM),
      ("symm",            one_prem_pt SYMM),
      ("th-lemma-arith",  list_prems_pt TH_LEMMA_ARITH),
      ("th-lemma-array",  list_prems_pt TH_LEMMA_ARRAY),
      ("th-lemma-basic",  list_prems_pt TH_LEMMA_BASIC),
      ("th-lemma-bv",     list_prems_pt TH_LEMMA_BV),
      ("trans",           two_prems_pt TRANS),
      ("trans*",          list_prems_pt TRANS_STAR),
      ("true-axiom",      zero_prems_pt TRUE_AXIOM),
      ("unit-resolution", list_prems_pt UNIT_RESOLUTION)
    ]

  (***************************************************************************)
  (* parsing of let definitions                                              *)
  (***************************************************************************)

  (* returns an extended proof; 't' must encode a proofterm *)
  fun extend_proof (steps, vars) (id, t) =
  let
    val _ = if !Library.trace > 0 andalso
      Option.isSome (Redblackmap.peek (steps, id)) then
        WARNING "extend_proof"
          ("proofterm ID " ^ Int.toString id ^ " defined more than once")
      else ()
  in
    (Redblackmap.insert (steps, id, proofterm_of_term t), vars)
  end

  (* Checks whether the `let` bindings are like the ones used in Z3 proof
     certificates, i.e. that there is only one binding and the name starts with
     `?x`, `$x` or `@x`. Otherwise, we'll assume it's of a real `let` expression
     as used in SMT-LIB.
     Ideally, `@x` bindings nested within `let` definitions would be treated
     specially like those being bound in the outermost `let` definitions, i.e.
     we'd create nodes in the proof graph so that we don't have to replay the
     proofs for these proofterms more than once. However, this would greatly
     complicate the parser and currently each of these nested proofterms only
     seem to be used once, so there doesn't seem to be a need to handle them
     specially. *)
  fun is_z3_proof_binding ((name, _, _) :: []) =
        String.isPrefix "?x" name orelse String.isPrefix "$x" name orelse
          String.isPrefix "@x" name
    | is_z3_proof_binding _ = false

  (* The Z3 proof certificate version of `mk_let_bindings` checks whether we are
     parsing a typical Z3 proof certificate `let` binding. If so, it binds the
     name to the corresponding term. Otherwise, it does what the SMT-LIB version
     of the parser would do. *)
  fun z3_mk_let_bindings ((tydict, tmdict), bindings)
    : Term.term SmtLib_Parser.dict =
    if is_z3_proof_binding bindings then
      (* We cannot use `Library.extend_dict_unique` because Z3 does rebind the
         same name (although when this happened, it assigned the same value). *)
      List.foldl (fn ((name, _, t), tmdict) => Library.extend_dict
        ((name, SmtLib_Theories.K_zero_zero t), tmdict)) tmdict bindings
    else
      SmtLib_Parser.smtlib_mk_let_bindings ((tydict, tmdict), bindings)

  (* The Z3 proof certificate version of `mk_let` checks whether we are parsing
     a typical Z3 proof certificate `let` binding. If so, it simply returns the
     body of the `let` expression, otherwise it does what the SMT-LIB version of
     the parser would do (i.e. create a HOL4 `let` term). *)
  fun z3_mk_let (bindings, body) : Term.term =
    if is_z3_proof_binding bindings then
      body
    else
      SmtLib_Parser.smtlib_mk_let (bindings, body)

  val z3_proof_cfg = {
    mk_let_bindings = z3_mk_let_bindings,
    mk_let = z3_mk_let,
    parse_lambda = true
  }

  (* distinguishes between a term definition and a proofterm
     definition; returns a (possibly extended) dictionary and proof *)
  fun parse_definition get_token (tydict, tmdict, proof) =
  let
    val _ = Library.expect_token "(" (get_token ())
    val _ = Library.expect_token "(" (get_token ())
    val name = get_token ()
    val t = SmtLib_Parser.parse_term_with_cfg z3_proof_cfg get_token
      (tydict, tmdict)
    val _ = Library.expect_token ")" (get_token ())
    val _ = Library.expect_token ")" (get_token ())
  in
    if String.isPrefix "@x" name then
      (* proofterm definition *)
      let
        val tmdict = Library.extend_dict_unique ((name,
          SmtLib_Theories.K_zero_zero (Term.mk_var (name, pt_ty))), tmdict)
        val proof = extend_proof proof (proofterm_id name, t)
      in
        (tmdict, proof)
      end
    else
      (* term definition *)
      (Library.extend_dict_unique ((name, SmtLib_Theories.K_zero_zero t),
        tmdict), proof)
  end

  (* Parses the actual proof expression *)
  fun parse_proof_expression get_token (tydict, tmdict, proof) (rpars : int) =
  let
    val () = Library.expect_token "(" (get_token ())
    val head = get_token ()
  in
    if head = "let" then
      let
        val (tmdict, proof) = parse_definition get_token (tydict, tmdict, proof)
      in
        parse_proof_expression get_token (tydict, tmdict, proof) (rpars + 1)
      end
    else
      let
        (* undo look-ahead of 2 tokens *)
        val get_token' = Library.undo_look_ahead ["(", head] get_token
        val t = SmtLib_Parser.parse_term_with_cfg z3_proof_cfg get_token'
          (tydict, tmdict)
      in
        (* Z3 assigns no ID to the final proof step; we use ID 0 *)
        extend_proof proof (0, t) before Lib.funpow rpars
          (fn () => Library.expect_token ")" (get_token ())) ()
      end
  end

  (* Parses the initial proof declarations *)
  fun parse_proof_decl get_token (tydict, tmdict, proof) (rpars : int) =
  let
    val () = Library.expect_token "(" (get_token ())
    val head = get_token ()
  in
    if head = "proof" then
      parse_proof_expression get_token (tydict, tmdict, proof) (rpars + 1)
    else if head = "declare-fun" then
      let
        val (tm, tmdict) = SmtLib_Parser.parse_declare_fun get_token (tydict, tmdict)
        val proof = Lib.apsnd (fn set => HOLset.add (set, tm)) proof
      in
        parse_proof_decl get_token (tydict, tmdict, proof) rpars
      end
    else if head = "error" then (
      (* some (otherwise valid) proofs are preceded by an error message,
         which we simply ignore *)
      get_token ();
      Library.expect_token ")" (get_token ());
      parse_proof_decl get_token (tydict, tmdict, proof) rpars
    ) else
      let
        (* undo look-ahead of 2 tokens *)
        val get_token' = Library.undo_look_ahead ["(", head] get_token
      in
        parse_proof_expression get_token' (tydict, tmdict, proof) rpars
      end
  end

  (* entry point into the parser (i.e., the grammar's start symbol)

     Z3 v2.19 proofs begin with:
     ```
     (error "...")          ; may or may not be present
     (let ...
     ```

     Z3 v4 proofs begin with:
     ```
     (                      ; note the extra parenthesis
       (declare-fun ...)    ; any number of these, maybe none
       (proof
         (let ...
     ```
     We'll try to seamlessly handle both styles of proof here. Namely,
     for v4 proofs we'll consume the extra parenthesis here and then
     continue parsing as normal. *)
  fun parse_proof get_token state =
  let
    val () = Library.expect_token "(" (get_token ())
    val token = get_token ()
  in
    if token = "let" orelse token = "error" then
      (* Z3 v2.19 proof *)
      let
        (* undo look-ahead of the 2 tokens *)
        val get_token' = Library.undo_look_ahead ["(", token] get_token
      in
        parse_proof_decl get_token' state 0
      end
    else
      (* Must be a Z3 v4 proof then *)
      let
        val () = Library.expect_token "(" token
        (* leave the 1st parenthesis consumed and undo the 2nd *)
        val get_token' = Library.undo_look_ahead ["("] get_token
      in
        parse_proof_decl get_token' state 1
      end
  end

in

  (* Similar to 'parse_file' below, but for instreams.  Does not close
     the instream. *)

  fun parse_stream ((tydict, tmdict): SmtLib_Parser.dicts)
    (instream : TextIO.instream) : proof =
  let
    (* union of user-declared names and Z3's inference rule names *)
    val tmdict = Library.union_dict tmdict z3_builtin_dict
    (* parse the stream *)
    val _ = if !Library.trace > 1 then
        Feedback.HOL_MESG "HolSmtLib: parsing Z3 proof"
      else ()
    val get_token = Library.get_token (Library.get_buffered_char instream)
    val empty_proof = (Redblackmap.mkDict Int.compare, Term.empty_tmset)
    val proof = parse_proof get_token
      (tydict, tmdict, empty_proof)
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
