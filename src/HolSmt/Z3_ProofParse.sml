(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Proof reconstruction for Z3: parsing of Z3's proofs *)

structure Z3_ProofParse =
struct

  (* Rules marked with "1" are only used in compressed Z3 proofs (PROOF_MODE=1).
     Other rules that are commented out are just not used in any of the
     benchmarks/proofs I've tried so far. *)

  datatype proofterm = AND_ELIM of int * Term.term
                  (* | APPLY_DEF of int * Term.term *)
                     | ASSERTED of Term.term
               (* 1: | CNF_STAR of ... *)
                     | COMMUTATIVITY of Term.term
                     | DEF_AXIOM of Term.term
                  (* | DEF_INTRO of Term.term *)
                  (* | DER of Term.term *)
                  (* | DISTRIBUTIVITY of Term.term *)
                     | ELIM_UNUSED of Term.term
                  (* | GOAL of Term.term *)
                     | HYPOTHESIS of Term.term
                     | IFF_FALSE of int * Term.term
                  (* | IFF_TILDE of int * Term.term *)
                     | IFF_TRUE of int * Term.term
                     | LEMMA of int * Term.term
                     | MONOTONICITY of int list * Term.term
                     | MP of int * int * Term.term
                     | MP_TILDE of int * int * Term.term
                     | NNF_NEG of int list * Term.term
                     | NNF_POS of int list * Term.term
               (* 1: | NNF_STAR of int list * Term.term *)
                     | NOT_OR_ELIM of int * Term.term
                     | PULL_QUANT of Term.term
               (* 1: | PULL_QUANT_STAR of Term.term *)
                  (* | PUSH_QUANT of ... *)
                     | QUANT_INST of Term.term
                     | QUANT_INTRO of int * Term.term
                     | REFL of Term.term
                     | REWRITE of Term.term
                     | REWRITE_STAR of int list * Term.term
                     | SK of Term.term
                     | SYMM of int * Term.term
                     | TH_LEMMA of int list * Term.term
                     | TRANS of int * int * Term.term
               (* 1: | TRANS_STAR of int list * Term.term *)
                     | TRUE_AXIOM of Term.term
                     | UNIT_RESOLUTION of int list * Term.term
                     | THEOREM of Thm.thm

  (* Z3 assigns no ID to the final '|- F'; we will use ID 0 *)
  type proof = (int, proofterm) Redblackmap.dict

  (* parses Z3's output (for an unsatisfiable problem, with proofs enabled,
     i.e., PROOF_MODE=2, DISPLAY_PROOF=true); returns a value of type
     'proof' *)

  (* TODO: arguably much nicer to implement with parser combinators. Or perhaps
     one should use mllex/mlyacc. *)

  fun parse_proof_file path (ty_dict, tm_dict) =
  let
    val _ = if !SolverSpec.trace > 1 then
        Feedback.HOL_MESG ("HolSmtLib: parsing Z3 proof file '" ^ path ^ "'")
      else ()
    (* invert 'ty_dict' (which is a map from types to strings): we need a map
       from strings to types *)
    val inverse_ty_dict = ref (Redblackmap.foldl (fn (ty, s, dict) =>
      case Redblackmap.peek (dict, s) of
        NONE =>
        Redblackmap.insert (dict, s, ty)
      | SOME _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
          ("inverting dictionary: more than one type maps to '" ^ s ^ "'"))
      ) (Redblackmap.mkDict String.compare) ty_dict)
    (* invert 'tm_dict' (which is a map from terms to strings): we need a map
       from strings to terms *)
    val inverse_tm_dict = ref (Redblackmap.foldl (fn (tm, s, dict) =>
      case Redblackmap.peek (dict, s) of
        NONE =>
        Redblackmap.insert (dict, s, tm)
      | SOME _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
          ("inverting dictionary: more than one term maps to '" ^ s ^ "'"))
      ) (Redblackmap.mkDict String.compare) tm_dict)
    (* char list -> char list -> char list list *)
    fun get_tokens tok [] =
          [List.rev tok]
      | get_tokens tok (#"\r"::cs) =
          List.rev tok :: get_tokens [] cs
      | get_tokens tok (#"\n"::cs) =
          List.rev tok :: get_tokens [] cs
      | get_tokens tok (#" "::cs) =
          List.rev tok :: get_tokens [] cs
      | get_tokens tok (#"#"::cs) =
          List.rev tok :: [#"#"] :: get_tokens [] cs
      | get_tokens tok (#"("::cs) =
          List.rev tok :: [#"("] :: get_tokens [] cs
      | get_tokens tok (#")"::cs) =
          List.rev tok :: [#")"] :: get_tokens [] cs
      | get_tokens tok (#"["::cs) =
          List.rev tok :: [#"["] :: get_tokens [] cs
      | get_tokens tok (#"]"::cs) =
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
      | get_tokens tok (#":"::cs) =
          List.rev tok :: [#":"] :: get_tokens [] cs
      | get_tokens tok (c::cs) =
          get_tokens (c::tok) cs
    (* string -> int *)
    fun parse_int id =
      let val id = valOf (Int.fromString id) handle Option =>
            raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
              "parsing error: integer expected")
          val _ = if id < 1 then
            raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                "parsing error: integer less than 1 found")
              else ()
      in
        id
      end
    (* string list * 'a -> int list * 'a *)
    fun parse_int_list (tokens, x) =
      let fun parse_aux ("#" :: id :: tokens) =
                parse_int id :: parse_aux tokens
            | parse_aux [] =
                []
            | parse_aux _ =
                raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                  "error parsing integer list: invalid token sequence")
      in
        (parse_aux tokens, x)
      end
    (* 'a list * 'b -> 'b *)
    fun parse_empty ([], x) =
          x
      | parse_empty _ =
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            "error parsing proofterm: empty token sequence expected")
    (* string list * 'a -> int * 'a *)
    fun parse_one_int (["#", id], x) =
          (parse_int id, x)
      | parse_one_int _ =
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            "error parsing single integer: invalid token sequence")
    (* string list * 'a -> int * int * 'a *)
    fun parse_two_int (["#", id1, "#", id2], x) =
          (parse_int id1, parse_int id2, x)
      | parse_two_int _ =
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            "error parsing pair of integers: invalid token sequence")
    (* string list -> Type.hol_type *)
    fun parse_typ ["int"] =
        intSyntax.int_ty
      | parse_typ ["real"] =
        realSyntax.real_ty
      | parse_typ ["bool"] =
        Type.bool
      | parse_typ [typ] =
        (case Redblackmap.peek (!inverse_ty_dict, typ) of
          SOME T =>
          T
        | NONE =>
          let val T = Type.mk_vartype ("'" ^ typ)
              val _ = case Redblackmap.peek (ty_dict, T) of
                  NONE => ()
                | SOME _ =>
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    ("type " ^ typ ^ " present in the input term"))
              val _ = if !SolverSpec.trace > 2 then
                  Feedback.HOL_MESG ("HolSmtLib: inventing type variable " ^
                    Hol_pp.type_to_string T)
                else ()
              val _ = inverse_ty_dict := Redblackmap.insert
                (!inverse_ty_dict, typ, T)
          in
            T
          end)
      | parse_typ ("(" :: "->" :: tokens) =
        let val _ = if List.length tokens < 3 then
                raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                  "error parsing type: '->' followed by insufficient tokens")
              else ()
            val (tokens, last) = Lib.front_last tokens
            val _ = if last <> ")" then
                raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                  "error parsing type: missing ')' at the end")
              else ()
            (* separate the argument types *)
            fun separate tokens =
              let val (_, tokss, _) =
                List.foldl (fn (tok, acc) =>
                  let val (n, tokss, toks) = acc
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
        (* arrays are translated to function types *)
        let val _ = if List.length tokens < 4 then
                raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                  "error parsing type: 'array' followed by insufficient tokens")
              else ()
            val (tokens, last) = Lib.front_last tokens
            val _ = if last <> "]" then
                raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                  "error parsing type: missing ']' at the end")
              else ()
           (* separate at a ':' token that is not nested within brackets *)
           fun separate 0 acc (":" :: tokens) =
               (List.rev acc, tokens)
             | separate n acc ("[" :: tokens) =
               separate (n+1) ("["::acc) tokens
             | separate n acc ("]" :: tokens) =
               if n<1 then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing type: too many ']'s in array type")
               else
                 separate (n-1) ("]"::acc) tokens
             | separate n acc (t::tokens) =
               separate n (t::acc) tokens
             | separate _ _ [] =
                raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                  "error parsing type: no ':' in array type")
            val (dom_toks, rng_toks) = separate 0 [] tokens
            val domT = parse_typ dom_toks
            val rngT = parse_typ rng_toks
        in
          Type.--> (domT, rngT)
        end
      | parse_typ _ =
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            "error parsing term: unknown type")
    (* (int, Term.term) Redblackmap.dict -> string -> Term.term *)
    fun parse_term_id dict id =
      case Redblackmap.peek (dict, parse_int id) of
        SOME t =>
          t
      | NONE =>
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            ("parsing error: unknown term ID '" ^ id ^ "'"))
    fun parse_proofterm dict tokens =
      let
        val len = List.length tokens
        val _ = if len < 3 then
            raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
              "error parsing proofterm: not enough tokens")
          else ()
        val rule = List.hd tokens
        val (rest, concl) = case List.drop (tokens, len - 4) of
            ["]", ":", "#", id] =>
              (List.tl (List.take (tokens, len - 4)), parse_term_id dict id)
          | _ => (case List.drop (tokens, len - 3) of
            ["]", ":", tok] =>
              (List.tl (List.take (tokens, len - 3)), parse_term dict [tok])
          | _ =>
            raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
              "error parsing proofterm: conclusion not found"))
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
            raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
              ("error parsing proofterm: unknown inference rule '" ^ rule ^
                "'"))) (rest, concl)
      end
    (* (int, Term.term) Redblackmap.dict -> string list -> term list *)
    and parse_term_list dict ("#" :: id :: tokens) =
          parse_term_id dict id :: parse_term_list dict tokens
      | parse_term_list dict (tok :: tokens) =
          parse_term dict [tok] :: parse_term_list dict tokens
      | parse_term_list _ [] =
          []
    (* (int, Term.term) Redblackmap.dict -> string list -> term *)
    and parse_term dict ["(", ":var", id, typ, ")"] =
          (* bound variable *)
          let val bvar = Term.mk_var (":var" ^ id, parse_typ [typ])
              val _ = case Redblackmap.peek (tm_dict, bvar) of
                  SOME _ =>
                    raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                      ("error parsing term: bound variable ':var" ^ id ^
                       "' present in the input term"))
                | NONE => ()
          in
            bvar
          end
      | parse_term dict ["#", id] =
          parse_term_id dict id
      | parse_term dict ("(" :: "forall" :: "(" :: "vars" :: tokens) =
          let val _ = if List.length tokens < 7 then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                "error parsing term: 'forall' followed by insufficient tokens")
                else ()
              val (tokens, last) = Lib.front_last tokens
              val _ = if last <> ")" then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'forall' missing ')' at the end")
                else ()
              fun parse_bvars acc (")" :: rests) =
                (acc, rests)
                | parse_bvars acc ("(" :: name :: typ :: ")" :: rests) =
                let val (acc, rests) = parse_bvars acc rests
                in
                  (Term.mk_var (name, parse_typ [typ]) :: acc, rests)
                end
                | parse_bvars _ _ =
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'forall' followed by invalid tokens")
              val (bvars, tokens) = parse_bvars [] tokens
              fun drop_until_paren (")" :: tokens) =
                  tokens
                | drop_until_paren (_ :: tokens) =
                  drop_until_paren tokens
                | drop_until_paren [] =
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: missing ')' in pattern annotation")
              fun skip_pat ("(" :: ":pat" :: tokens) =
                  drop_until_paren tokens
                | skip_pat ("(" :: ":nopat" :: tokens) =
                  drop_until_paren tokens
                | skip_pat tokens =
                  tokens
              val tokens = skip_pat tokens
              val body = parse_term dict tokens

              (* replace variables ':varN' by properly named variables *)
              val bvars_subst = Lib.mapi (fn i => fn bvar =>
                {redex = Term.mk_var (":var" ^ Int.toString i,
                   Term.type_of bvar), residue = bvar}) (List.rev bvars)
              val body = Term.subst bvars_subst body

              (* decrement index of remaining (to-be-bound) variables ':varN' *)
              val dec = List.length bvars
              val fvars_subst = List.mapPartial (fn var =>
                let val (name, typ) = Term.dest_var var
                in
                  if String.isPrefix ":var" name then
                    let val n = Option.valOf (Int.fromString
                          (String.substring (name, 4, String.size name - 4)))
                        val _ = if n < dec then
                            raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                              "error parsing term: bound variable remains free (type mismatch?)")
                          else ()
                    in
                      SOME {redex = var, residue =
                        Term.mk_var (":var" ^ Int.toString (n - dec), typ)}
                    end
                  else
                    NONE
                end) (Term.free_vars body)
              val body = Term.subst fvars_subst body
          in
            boolSyntax.list_mk_forall (bvars, body)
          end
      | parse_term dict ["(", "~", "#", id1, "#", id2, ")"] =
          (* equisatisfiability is translated as equivalence *)
          boolSyntax.mk_eq (parse_term_id dict id1, parse_term_id dict id2)
      | parse_term dict ("(" :: "distinct" :: tokens) =
          let val _ = if List.null tokens then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'distinct' not followed by a token")
                else ()
              val (tokens, last) = Lib.front_last tokens
              val _ = if last <> ")" then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'distinct' missing ')' at the end")
                else ()
              val operands = parse_term_list dict tokens
              val _ = if List.null operands then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'distinct' has empty argument list")
                else ()
          in
            listSyntax.mk_all_distinct (listSyntax.mk_list
                (operands, Term.type_of (List.hd operands)))
          end
      | parse_term dict ("(" :: "select" :: tokens) =
          let val _ = if List.null tokens then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'select' not followed by a token")
                else ()
              val (tokens, last) = Lib.front_last tokens
              val _ = if last <> ")" then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'select' missing ')' at the end")
                else ()
              val operands = parse_term_list dict tokens
              val _ = if List.length operands <> 2 then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'select' must have 2 arguments")
                else ()
              val array = List.hd operands
              val index = List.hd (List.tl operands)
          in
            Term.mk_comb (array, index)
          end
      | parse_term dict ("(" :: "store" :: tokens) =
          let val _ = if List.null tokens then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'store' not followed by a token")
                else ()
              val (tokens, last) = Lib.front_last tokens
              val _ = if last <> ")" then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'store' missing ')' at the end")
                else ()
              val operands = parse_term_list dict tokens
              val _ = if List.length operands <> 3 then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'store' must have 3 arguments")
                else ()
              val array = List.hd operands
              val index = List.hd (List.tl operands)
              val value = List.hd (List.tl (List.tl operands))
          in
            Term.mk_comb (combinSyntax.mk_update (index, value), array)
          end
      | parse_term dict ("(" :: tok :: tokens) =
          (* function application *)
          let val _ = if List.null tokens then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: '(' followed by a single token")
                else ()
              val (tokens, last) = Lib.front_last tokens
              val _ = if last <> ")" then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: application missing ')' at the end")
                else ()
              val operator = parse_term dict [tok]
              val operands = parse_term_list dict tokens
              val _ = if List.null operands then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: application has empty argument list")
                else ()
          in
            if operator = boolSyntax.conjunction then
              (* conjunctions of arbitrary arity *)
              boolSyntax.list_mk_conj operands
            else if operator = boolSyntax.disjunction then
              (* disjunctions of arbitrary arity *)
              boolSyntax.list_mk_disj operands
            else
              let (* unary minus is represented as '-' (rather than '~') in
                     Z3's proofs *)
                  val operator = if operator = intSyntax.minus_tm andalso
                    List.length operands = 1 then
                      intSyntax.negate_tm
                    else operator
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
      | parse_term _ [tok] =
          (case List.find (fn (_, s, _, _) => s = tok) SmtLib.OperatorsTable of
            SOME (t, _, _, _) =>
            (* built-in constants *)
            t
          | NONE =>
            (case Redblackmap.peek (!inverse_tm_dict, tok) of
              SOME t =>
              (* user-defined constants *)
              t
            | NONE =>
              let val length = String.size tok
              in
                if length > 5 andalso
                  String.extract (tok, length - 5, NONE) = "::int" then
                  (* integer numerals *)
                  let val numeral = String.extract (tok, 0, SOME (length - 5))
                  in
                    intSyntax.term_of_int (Arbint.fromString numeral)
                  end
                else if length > 6 andalso
                  String.extract (tok, length - 6, NONE) = "::real" then
                  (* real numerals *)
                  let val numeral = String.extract (tok, 0, SOME (length - 6))
                  in
                    realSyntax.term_of_int (Arbint.fromString numeral)
                  end
                else
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    ("error parsing term: unknown token '" ^ tok ^ "'"))
              end))
      | parse_term _ _ =
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            "error parsing term: invalid token sequence")
    fun parse_proof_definition (dict, proof) id tokens =
      let val _ = case Redblackmap.peek (proof, id) of
          NONE => ()
        | SOME _ =>
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            ("proof ID " ^ Int.toString id ^ " used more than once"))
          val pt = parse_proofterm dict tokens
          val proof = Redblackmap.insert (proof, id, pt)
      in
        (dict, proof)
      end
    fun parse_term_definition (dict, proof) id tokens =
      let val _ = case Redblackmap.peek (dict, id) of
          NONE => ()
        | SOME _ =>
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            ("term ID " ^ Int.toString id ^ " used more than once"))
          val t = parse_term dict tokens
          val dict = Redblackmap.insert (dict, id, t)
      in
        (dict, proof)
      end
    (* parses a single line *)
    fun parse_token_line (dict, proof) tokens =
      case tokens of
        [] =>
          (dict, proof)
      | ["unsat"] =>
          (dict, proof)
      | "decl" :: name :: "::" :: tokens =>
          let val _ = case Redblackmap.peek (!inverse_tm_dict, name) of
              NONE => ()
            | SOME _ =>
              raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                ("term name '" ^ name ^ "' used more than once"))
              val t = Term.mk_var (name, parse_typ tokens)
              val _ = inverse_tm_dict := Redblackmap.insert
                (!inverse_tm_dict, name, t)
          in
            (dict, proof)
          end
      | "#" :: _ :: ":=" :: "(" :: "pattern" :: _ =>
          (* ignore pattern definitions *)
          (dict, proof)
      | "#" :: id :: ":=" :: tokens =>
          let val id = parse_int id
          in
            case tokens of
              "[" :: tokens =>
                parse_proof_definition (dict, proof) id tokens
            | _ =>
                parse_term_definition (dict, proof) id tokens
          end
      | "[" :: tokens =>
            parse_proof_definition (dict, proof) 0 tokens
      | _ => raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                  "parse_token_line: invalid token sequence")
    val instream = TextIO.openIn path
    (* (int, Term.term) Redblackmap.dict * proof -> proof *)
    fun parse_all_lines (dict, proof) =
      if TextIO.endOfStream instream then
        proof
      else
        let val line = valOf (TextIO.inputLine instream)
              handle Option => raise (Feedback.mk_HOL_ERR "Z3"
                "parse_proof_file" "parse_all_lines: no more line")
            val tokens = map String.implode (List.filter (not o Lib.equal [])
                           (get_tokens [] (String.explode line)))
            val _ = if !SolverSpec.trace > 2 then
                Feedback.HOL_MESG ("HolSmtLib: parsing token(s) " ^
                  String.concat (Lib.separate ", " tokens))
              else ()
        in
          parse_all_lines (parse_token_line (dict, proof) tokens)
        end
    val proof = parse_all_lines (Redblackmap.mkDict Int.compare,
                                 Redblackmap.mkDict Int.compare)
    val _ = TextIO.closeIn instream
  in
    proof
  end

end
