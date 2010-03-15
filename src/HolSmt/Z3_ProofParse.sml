(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Proof reconstruction for Z3: parsing of Z3's proofs *)

structure Z3_ProofParse =
struct

  open Z3_Proof

  val ERR = Feedback.mk_HOL_ERR "Z3_ProofParse"

  (* Function 'parse_proof_file' parses Z3's output (for an unsatisfiable
     problem, with proofs enabled in Z3, i.e., "PROOF_MODE=2,
     DISPLAY_PROOF=true" in Z3's .ini file). Other functions in this file are
     just auxiliary. *)

  (* This would arguably be much nicer to implement with parser combinators.
     Or perhaps one should use mllex/mlyacc. *)

  (* string list -> Type.hol_type *)
  fun parse_typ ["int"] =
        intSyntax.int_ty
    | parse_typ ["real"] =
        realSyntax.real_ty
    | parse_typ ["bool"] =
        Type.bool
    | parse_typ [typ] =
        Type.mk_vartype ("'" ^ typ)
    | parse_typ ("(" :: "->" :: tokens) =
        let
          val _ = if List.length tokens < 3 then
              raise ERR "parse_typ" "'->' followed by insufficient tokens"
            else ()
          val (tokens, last) = Lib.front_last tokens
          val _ = if last <> ")" then
              raise ERR "parse_typ" "missing ')' at the end of function type"
            else ()
          (* separate the argument types *)
          fun separate tokens =
            let
              val (_, tokss, _) = List.foldl (fn (tok, acc) =>
                let
                  val (n, tokss, toks) = acc
                  val n = if tok = "array" then n + 1
                    else if tok = "]" then n - 1
                    else n
                in
                  if n = 0 then
                    (n, tokss @ [toks @ [tok]], [])
                  else
                    (n, tokss, toks @ [tok])
                end) (0, [], []) tokens
            in
              tokss
            end
          val typs = List.map parse_typ (separate tokens)
          val (argsT, rngT) = Lib.front_last typs
        in
          List.foldr Type.--> rngT argsT
        end
    | parse_typ ("array" :: "[" :: tokens) =
        let
          val _ = if List.length tokens < 4 then
              raise ERR "parse_typ" "'array' followed by insufficient tokens"
            else ()
          val (tokens, last) = Lib.front_last tokens
          val _ = if last <> "]" then
              raise ERR "parse_typ" "missing ']' at the end of array type"
            else ()
          (* separate at a ':' token that is not nested within brackets *)
          fun separate 0 acc (":" :: tokens) =
                (List.rev acc, tokens)
            | separate n acc ("[" :: tokens) =
                separate (n+1) ("["::acc) tokens
            | separate n acc ("]" :: tokens) =
                if n<1 then
                  raise ERR "parse_typ" "too many ']'s in array type"
                else
                  separate (n-1) ("]"::acc) tokens
            | separate n acc (t::tokens) =
                separate n (t::acc) tokens
            | separate _ _ [] =
                raise ERR "parse_typ" "missing ':' in array type"
          val (dom_toks, rng_toks) = separate 0 [] tokens
          val domT = parse_typ dom_toks
          val rngT = parse_typ rng_toks
        in
          (* arrays are translated to function types *)
          Type.--> (domT, rngT)
        end
    | parse_typ toks =
        raise ERR "parse_typ" ("unknown type: " ^ String.concatWith ", " toks)

  fun parse_integer (id_string : string) : int =
  let
    val id = valOf (Int.fromString id_string) handle Option =>
      raise ERR "parse_integer" "integer expected"
    val _ = if id < 1 then
        raise ERR "parse_integer" "integer less than 1 found"
      else ()
  in
    id
  end

  (* (int, Term.term) Redblackmap.dict -> string -> Term.term *)
  fun parse_term_id dict id =
    case Redblackmap.peek (dict, parse_integer id) of
      SOME t =>
        t
    | NONE =>
        raise ERR "parse_term_id" ("unknown term ID " ^ id)

  (* string list -> string list *)
  fun remove_right_parenthesis [] =
        raise ERR "remove_right_parenthesis" "empty token list"
    | remove_right_parenthesis tokens =
        let
          val (tokens, last) = Lib.front_last tokens
        in
          if last = ")" then
            tokens
          else
            raise ERR "remove_right_parenthesis"
              ("')' expected, but '" ^ last ^ "' found")
        end

  (* (string, Term.term) Redblackmap.dict * (int, Term.term) Redblackmap.dict
       -> string list -> term list *)
  fun parse_term_list (decl, dict) ("#" :: id :: tokens) =
        parse_term_id dict id :: parse_term_list (decl, dict) tokens
    | parse_term_list (decl, dict) (tok :: tokens) =
        parse_term (decl, dict) [tok] :: parse_term_list (decl, dict) tokens
    | parse_term_list _ [] =
        []

  (* (string, Term.term) Redblackmap.dict * (int, Term.term) Redblackmap.dict
       -> string list -> term *)
  and parse_term _ ["(", ":var", id, typ, ")"] =
        (* bound variable *)
        Term.mk_var (":var" ^ id, parse_typ [typ])
    | parse_term (_, dict) ["#", id] =
        parse_term_id dict id
    | parse_term (decl, dict) ("(" :: "forall" :: "(" :: "vars" :: tokens) =
        let
          val tokens = remove_right_parenthesis tokens
          fun parse_bvars acc (")" :: rests) =
                (acc, rests)
            | parse_bvars acc ("(" :: name :: typ :: ")" :: rests) =
                let
                  val (acc, rests) = parse_bvars acc rests
                in
                  (Term.mk_var (name, parse_typ [typ]) :: acc, rests)
                end
            | parse_bvars _ _ =
                raise ERR "parse_term" "'forall' followed by invalid tokens"
          val (bvars, tokens) = parse_bvars [] tokens
          fun drop_until_parenthesis (")" :: tokens) =
                tokens
            | drop_until_parenthesis (_ :: tokens) =
                drop_until_parenthesis tokens
            | drop_until_parenthesis [] =
                raise ERR "parse_term" "missing ')' in pattern annotation"
          fun drop_pattern ("(" :: ":pat" :: tokens) =
                drop_until_parenthesis tokens
            | drop_pattern ("(" :: ":nopat" :: tokens) =
                drop_until_parenthesis tokens
            | drop_pattern tokens =
                tokens
          val tokens = drop_pattern tokens
          val body = parse_term (decl, dict) tokens
          (* replace variables ':varN' by properly named variables *)
          val bvars_subst = Lib.mapi (fn i => fn bvar =>
            {redex = Term.mk_var (":var" ^ Int.toString i, Term.type_of bvar),
              residue = bvar}) (List.rev bvars)
          val body = Term.subst bvars_subst body
          (* decrement index of remaining (to-be-bound) variables ':varN' *)
          val dec = List.length bvars
          val fvars_subst = List.mapPartial (fn var =>
            let
              val (name, typ) = Term.dest_var var
            in
              if String.isPrefix ":var" name then
                let
                  val n = Option.valOf (Int.fromString (String.substring
                    (name, 4, String.size name - 4)))
                  val _ = if n < dec then
                      raise ERR "parse_term"
                        "bound variable remains free (type mismatch?)"
                    else ()
                in
                  SOME {redex = var, residue = Term.mk_var
                    (":var" ^ Int.toString (n - dec), typ)}
                end
              else
                NONE
            end) (Term.free_vars body)
          val body = Term.subst fvars_subst body
        in
          boolSyntax.list_mk_forall (bvars, body)
        end
    | parse_term (decl, dict) ("(" :: "~" :: tokens) =
        (* equisatisfiability is translated as equivalence *)
        let
          val tokens = remove_right_parenthesis tokens
          val operands = parse_term_list (decl, dict) tokens
          val _ = if List.length operands <> 2 then
              raise ERR "parse_term" "'~' must have 2 arguments"
            else ()
          val t1 = List.hd operands
          val t2 = List.hd (List.tl operands)
        in
          boolSyntax.mk_eq (t1, t2)
        end
    | parse_term (decl, dict) ("(" :: "distinct" :: tokens) =
        let
          val tokens = remove_right_parenthesis tokens
          val operands = parse_term_list (decl, dict) tokens
          val _ = if List.null operands then
              raise ERR "parse_term" "'distinct' used without arguments"
            else ()
        in
          listSyntax.mk_all_distinct
            (listSyntax.mk_list (operands, Term.type_of (List.hd operands)))
        end
    | parse_term (decl, dict) ("(" :: "select" :: tokens) =
        let
          val tokens = remove_right_parenthesis tokens
          val operands = parse_term_list (decl, dict) tokens
          val _ = if List.length operands <> 2 then
              raise ERR "parse_term" "'select' must have 2 arguments"
            else ()
          val array = List.hd operands
          val index = List.hd (List.tl operands)
        in
          Term.mk_comb (array, index)
        end
    | parse_term (decl, dict) ("(" :: "store" :: tokens) =
        let
          val tokens = remove_right_parenthesis tokens
          val operands = parse_term_list (decl, dict) tokens
          val _ = if List.length operands <> 3 then
              raise ERR "parse_term" "'store' must have 3 arguments"
            else ()
          val array = List.hd operands
          val index = List.hd (List.tl operands)
          val value = List.hd (List.tl (List.tl operands))
        in
          Term.mk_comb (combinSyntax.mk_update (index, value), array)
        end
    | parse_term (decl, dict) ("(" :: tok :: tokens) =
        (* function application *)
        let
          val tokens = remove_right_parenthesis tokens
          val operator = parse_term (decl, dict) [tok]
          val operands = parse_term_list (decl, dict) tokens
          val _ = if List.null operands then
              raise ERR "parse_term" "application has empty argument list"
            else ()
        in
          if operator = boolSyntax.conjunction then
            (* conjunctions of arbitrary arity *)
            boolSyntax.list_mk_conj operands
          else if operator = boolSyntax.disjunction then
            (* disjunctions of arbitrary arity *)
            boolSyntax.list_mk_disj operands
          else
            let
              (* unary minus is represented as '-' (rather than '~') in Z3's
                 proofs *)
              val operator = if operator = intSyntax.minus_tm andalso
                    List.length operands = 1 then
                  intSyntax.negate_tm
                else
                  operator
              (* overloaded operators: int vs. real *)
              val int_real_table =
                [(intSyntax.negate_tm, realSyntax.negate_tm),
                 (intSyntax.plus_tm, realSyntax.plus_tm),
                 (intSyntax.minus_tm, realSyntax.minus_tm),
                 (intSyntax.mult_tm, realSyntax.mult_tm),
                 (intSyntax.less_tm, realSyntax.less_tm),
                 (intSyntax.leq_tm, realSyntax.leq_tm),
                 (intSyntax.great_tm, realSyntax.great_tm),
                 (intSyntax.geq_tm, realSyntax.geq_tm)]
              val operator = if Term.type_of (List.hd operands) =
                    realSyntax.real_ty then
                  case List.find (fn (int_op, _) => int_op = operator)
                      int_real_table of
                    SOME (_, real_op) => real_op
                  | NONE => operator
                else
                  operator
            in
              (* the type of polymorphic operators must be instantiated to
                 match their actual argument types *)
              boolSyntax.list_mk_icomb (operator, operands)
            end
        end
    | parse_term (decl, _) [tok] =
        (case List.find (fn (_, s, _, _) => s = tok) SmtLib.OperatorsTable of
          SOME (t, _, _, _) =>
          (* built-in constants *)
          t
        | NONE =>
          (case Redblackmap.peek (decl, tok) of
            SOME t =>
            (* user-defined constants *)
            t
          | NONE =>
            let
              val length = String.size tok
            in
              if length > 5 andalso
                  String.extract (tok, length - 5, NONE) = "::int" then
                (* integer numerals *)
                let
                  val numeral = String.extract (tok, 0, SOME (length - 5))
                in
                  intSyntax.term_of_int (Arbint.fromString numeral)
                end
              else if length > 6 andalso
                  String.extract (tok, length - 6, NONE) = "::real" then
                (* real numerals *)
                let
                  val numeral = String.extract (tok, 0, SOME (length - 6))
                in
                  realSyntax.term_of_int (Arbint.fromString numeral)
                end
              else
                raise ERR "parse_term" ("unknown token '" ^ tok ^ "'")
            end))
    | parse_term _ toks =
        raise ERR "parse_term" ("invalid token sequence: " ^
          String.concatWith ", " toks)

  (* string list * 'a -> int list * 'a *)
  fun parse_int_list (tokens, x) =
  let
    fun parse_aux ("#" :: id :: tokens) =
          parse_integer id :: parse_aux tokens
      | parse_aux [] =
          []
      | parse_aux _ =
          raise ERR "parse_int_list" "invalid token sequence"
  in
    (parse_aux tokens, x)
  end

  (* 'a list * 'b -> 'b *)
  fun parse_empty ([], x) =
        x
    | parse_empty _ =
        raise ERR "parse_empty" "empty token sequence expected"

  (* string list * 'a -> int * 'a *)
  fun parse_one_int (["#", id], x) =
        (parse_integer id, x)
    | parse_one_int _ =
        raise ERR "parse_one_int" "invalid token sequence"

  (* string list * 'a -> int * int * 'a *)
  fun parse_two_int (["#", id1, "#", id2], x) =
        (parse_integer id1, parse_integer id2, x)
    | parse_two_int _ =
        raise ERR "parse_two_int" "invalid token sequence"

  fun parse_proofterm (decl, dict) tokens : proofterm =
  let
    val len = List.length tokens
    val _ = if len < 3 then
        raise ERR "parse_proofterm" "not enough tokens"
      else ()
    val rule = List.hd tokens
    val (rest, concl) = case List.drop (tokens, len - 4) of
        ["]", ":", "#", id] =>
          (List.tl (List.take (tokens, len - 4)), parse_term_id dict id)
      | _ =>
          (case List.drop (tokens, len - 3) of
            ["]", ":", tok] =>
              (List.tl (List.take (tokens, len - 3)),
                parse_term (decl, dict) [tok])
          | _ =>
              raise ERR "parse_proofterm" "conclusion not found")
  in
    (case rule of
      "and-elim"        => AND_ELIM o parse_one_int
    | "asserted"        => ASSERTED o parse_empty
    | "commutativity"   => COMMUTATIVITY o parse_empty
    | "def-axiom"       => DEF_AXIOM o parse_empty
    | "elim-unused"     => ELIM_UNUSED o parse_empty
    | "iff-false"       => IFF_FALSE o parse_one_int
    | "iff-true"        => IFF_TRUE o parse_one_int
    | "lemma"           => LEMMA o parse_one_int
    | "hypothesis"      => HYPOTHESIS o parse_empty
    | "monotonicity"    => MONOTONICITY o parse_int_list
    | "mp"              => MP o parse_two_int
    | "mp~"             => MP_TILDE o parse_two_int
    | "nnf-neg"         => NNF_NEG o parse_int_list
    | "nnf-pos"         => NNF_POS o parse_int_list
    | "not-or-elim"     => NOT_OR_ELIM o parse_one_int
    | "pull-quant"      => PULL_QUANT o parse_empty
    | "quant-inst"      => QUANT_INST o parse_empty
    | "quant-intro"     => QUANT_INTRO o parse_one_int
    | "refl"            => REFL o parse_empty
    | "rewrite"         => REWRITE o parse_empty
    | "rewrite*"        => REWRITE_STAR o parse_int_list
    | "sk"              => SK o parse_empty
    | "symm"            => SYMM o parse_one_int
    | "th-lemma"        => TH_LEMMA o parse_int_list
    | "trans"           => TRANS o parse_two_int
    | "true-axiom"      => TRUE_AXIOM o parse_empty
    | "unit-resolution" => UNIT_RESOLUTION o parse_int_list
    | _ =>
        raise ERR "parse_proofterm" ("unknown inference rule '" ^ rule ^ "'"))
      (rest, concl)
  end

  fun parse_term_declaration decl (name, tokens) :
    (string, Term.term) Redblackmap.dict =
  let
    val _ = case Redblackmap.peek (decl, name) of
        NONE => ()
      | SOME _ =>
        raise ERR "parse_term_declaration"
          ("term name '" ^ name ^ "' declared more than once")
    val t = Term.mk_var (name, parse_typ tokens)
  in
    Redblackmap.insert (decl, name, t)
  end

  fun parse_term_definition (decl, dict) (id, tokens) :
    (int, Term.term) Redblackmap.dict =
  let
    val _ = case Redblackmap.peek (dict, id) of
        NONE => ()
      | SOME _ =>
        raise ERR "parse_term_definition" ("term ID " ^ Int.toString id ^
          " defined more than once")
    val t = parse_term (decl, dict) tokens
  in
    Redblackmap.insert (dict, id, t)
  end

  fun parse_proofterm_definition (decl, dict, proof) (id, tokens) : proof =
  let
    val _ = case Redblackmap.peek (proof, id) of
        NONE => ()
      | SOME _ =>
        raise ERR "parse_proofterm_definition" ("proof ID " ^ Int.toString id ^
          " defined more than once")
    val pt = parse_proofterm (decl, dict) tokens
  in
    Redblackmap.insert (proof, id, pt)
  end

  (* parses a single line of the proof file, split into a list of tokens
     already *)
  fun parse_token_line (decl, dict, proof) [] =
      (decl, dict, proof)
    | parse_token_line (decl, dict, proof) ["unsat"] =
      (decl, dict, proof)
    | parse_token_line (decl, dict, proof) ("decl" :: name :: "::" :: tokens) =
      let
        val decl = parse_term_declaration decl (name, tokens)
      in
        (decl, dict, proof)
      end
    | parse_token_line (decl, dict, proof)
        ("#" :: _ :: ":=" :: "(" :: "pattern" :: _) =
      (* ignore pattern definitions *)
      (decl, dict, proof)
    | parse_token_line (decl, dict, proof)
        ("#" :: id :: ":=" :: "[" :: tokens) =
      let
        val id = parse_integer id
        val proof = parse_proofterm_definition (decl, dict, proof) (id, tokens)
      in
        (decl, dict, proof)
      end
    | parse_token_line (decl, dict, proof) ("#" :: id :: ":=" :: tokens) =
      let
        val id = parse_integer id
        val dict = parse_term_definition (decl, dict) (id, tokens)
      in
        (decl, dict, proof)
      end
    | parse_token_line (decl, dict, proof) ("[" :: tokens) =
      (* Z3 assigns no ID to the final proof step; we use ID 0 *)
      let
        val proof = parse_proofterm_definition (decl, dict, proof) (0, tokens)
      in
        (decl, dict, proof)
      end
    | parse_token_line _ _ =
      raise ERR "parse_token_line" "invalid token sequence"

  (* char list -> char list -> char list list *)
  fun get_tokens tok [] =
        [List.rev tok]
    | get_tokens tok (#"\r" :: cs) =
        List.rev tok :: get_tokens [] cs
    | get_tokens tok (#"\n" :: cs) =
        List.rev tok :: get_tokens [] cs
    | get_tokens tok (#" " :: cs) =
        List.rev tok :: get_tokens [] cs
    | get_tokens tok (#"#" :: cs) =
        List.rev tok :: [#"#"] :: get_tokens [] cs
    | get_tokens tok (#"(" :: cs) =
        List.rev tok :: [#"("] :: get_tokens [] cs
    | get_tokens tok (#")" :: cs) =
        List.rev tok :: [#")"] :: get_tokens [] cs
    | get_tokens tok (#"[" :: cs) =
        List.rev tok :: [#"["] :: get_tokens [] cs
    | get_tokens tok (#"]" :: cs) =
        List.rev tok :: [#"]"] :: get_tokens [] cs
    | get_tokens tok (#":" :: #"=" :: cs) =
        List.rev tok :: [#":", #"="] :: get_tokens [] cs
    | get_tokens tok (#":" :: #":" :: cs) =
        get_tokens (#":" :: #":" :: tok) cs
    | get_tokens tok (#":" :: #"v" :: #"a" :: #"r" :: cs) =
        get_tokens (#"r" :: #"a" :: #"v" :: #":" :: tok) cs
    | get_tokens tok (#":" :: #"p" :: #"a" :: #"t" :: cs) =
        get_tokens (#"t" :: #"a" :: #"p" :: #":" :: tok) cs
    | get_tokens tok (#":" :: #"n" :: #"o" :: #"p" :: #"a" :: #"t" :: cs) =
        get_tokens (#"t" :: #"a" :: #"p" :: #"o" :: #"n" :: #":" :: tok) cs
    | get_tokens tok (#":" :: cs) =
        List.rev tok :: [#":"] :: get_tokens [] cs
    | get_tokens tok (c :: cs) =
        get_tokens (c :: tok) cs

  fun parse_proof_file path : proof =
  let
    val _ = if !SolverSpec.trace > 1 then
        Feedback.HOL_MESG ("HolSmtLib: parsing Z3 proof file '" ^ path ^ "'")
      else ()
    val instream = TextIO.openIn path
    fun parse_lines (decl : (string, Term.term) Redblackmap.dict,
                     dict : (int, Term.term) Redblackmap.dict,
                     proof : proof) : proof =
      if TextIO.endOfStream instream then
        proof
      else
        let
          val line = valOf (TextIO.inputLine instream) handle Option =>
            raise ERR "parse_proof_file" "parse_lines: no more line"
          val tokens = map String.implode (List.filter (not o List.null)
            (get_tokens [] (String.explode line)))
          val _ = if !SolverSpec.trace > 2 then
              Feedback.HOL_MESG ("HolSmtLib: parsing token(s) " ^
                String.concatWith ", " tokens)
            else ()
        in
          parse_lines (parse_token_line (decl, dict, proof) tokens)
        end
    val proof = parse_lines (Redblackmap.mkDict String.compare,
                             Redblackmap.mkDict Int.compare,
                             Redblackmap.mkDict Int.compare)
    val _ = TextIO.closeIn instream
  in
    proof
  end

end
