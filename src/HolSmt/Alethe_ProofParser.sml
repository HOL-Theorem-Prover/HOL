(* Proof reconstruction for cvc5/Alethe: parsing Alethe proofs *)

structure Alethe_ProofParser =
struct

local

  val ERR = Feedback.mk_HOL_ERR "Alethe_ProofParser"

  val alethe_cfg : SmtLib_Parser.parser_cfg = {
    mk_let_bindings = SmtLib_Parser.smtlib_mk_let_bindings,
    mk_let = SmtLib_Parser.smtlib_mk_let,
    parse_lambda = false
  }

  (* --------------------------------------------------------------------- *)
  (* Mutable dicts ref — updated as :named bindings and define-fun are seen *)
  (* --------------------------------------------------------------------- *)

  type dicts = SmtLib_Parser.dicts

  fun add_to_tmdict (dicts_ref : dicts ref) name parsefn =
    let val (tydict, tmdict) = !dicts_ref
        val tmdict' = Library.extend_dict ((name, parsefn), tmdict)
    in dicts_ref := (tydict, tmdict') end

  fun add_to_tydict (dicts_ref : dicts ref) name parsefn =
    let val (tydict, tmdict) = !dicts_ref
        val tydict' = Library.extend_dict ((name, parsefn), tydict)
    in dicts_ref := (tydict', tmdict) end

  (* --------------------------------------------------------------------- *)
  (* Token-level preprocessing: strip ALL (! ... :named @X) annotations   *)
  (* --------------------------------------------------------------------- *)

  (* cvc5 Alethe proofs use (! term :named @p_N) to name subterms.
     These can be nested at any depth. SmtLib_Parser discards annotations
     but doesn't capture :named bindings. We preprocess at the token level:

     1. Collect all tokens for one balanced S-expression
     2. Recursively strip all (! INNER :named @X ...) → INNER,
        recording @X → INNER_TOKENS
     3. Feed stripped tokens to SmtLib_Parser
     4. For each @X, parse INNER_TOKENS to get the HOL term, register in dict *)

  (* Collect one balanced S-expression from a token list, returning
     (consumed_tokens, remaining_tokens) *)
  fun collect_one_sexp [] = raise ERR "collect_one_sexp" "empty"
    | collect_one_sexp ("(" :: rest) =
      let
        fun go depth acc [] = raise ERR "collect_one_sexp" "unbalanced"
          | go depth acc ("(" :: ts) = go (depth+1) ("(" :: acc) ts
          | go 0 acc (")" :: ts) = (List.rev (")" :: acc), ts)
          | go depth acc (")" :: ts) = go (depth-1) (")" :: acc) ts
          | go depth acc (t :: ts) = go depth (t :: acc) ts
      in
        let val (inner, rest') = go 0 ["("] rest
        in (inner, rest') end
      end
    | collect_one_sexp (t :: rest) = ([t], rest)

  (* Strip annotations from a token list, returning (stripped_tokens, bindings)
     where bindings = [(name, inner_tokens), ...] *)
  fun strip_named (tokens : string list)
    : string list * (string * string list) list =
  let
    val bindings : (string * string list) list ref = ref []

    fun process [] = []
      | process ("(" :: "!" :: rest) =
        (* Collect inner term tokens, then attributes *)
        let
          val (inner_toks, after_inner) = collect_one_sexp rest
          (* inner_toks is the inner term; after_inner starts with attributes *)
          val stripped_inner = process inner_toks
          (* Parse attributes until matching ")" *)
          fun parse_attrs [] = raise ERR "strip_named" "unbalanced annotation"
            | parse_attrs (")" :: rest') = rest'
            | parse_attrs (":named" :: name :: rest') =
                (bindings := (name, stripped_inner) :: !bindings;
                 parse_attrs rest')
            | parse_attrs (":" :: _ :: rest') = parse_attrs rest'
            | parse_attrs (_ :: rest') = parse_attrs rest'
          val remaining = parse_attrs after_inner
        in
          stripped_inner @ process remaining
        end
      | process ("(" :: rest) =
          "(" :: process rest
      | process (")" :: rest) =
          ")" :: process rest
      | process (t :: rest) =
          t :: process rest
  in
    (process tokens, !bindings)
  end

  (* Collect tokens for one complete term from a get_token function *)
  fun collect_term_tokens get_token : string list =
  let
    val tok = get_token ()
  in
    if tok = "(" then
      let
        fun go depth acc =
          let val t = get_token ()
          in
            if t = "(" then go (depth+1) (t :: acc)
            else if t = ")" then
              if depth = 0 then List.rev (t :: acc)
              else go (depth-1) (t :: acc)
            else go depth (t :: acc)
          end
      in "(" :: go 0 [] end
    else [tok]
  end

  (* Try to parse a cvc5 rational literal like "0/1", "3/2", "-1/1" *)
  fun try_parse_rational (s : string) : Term.term option =
  let
    fun split_slash str =
      let val fields = String.fields (fn c => c = #"/") str
      in case fields of [n, d] => SOME (n, d) | _ => NONE end
  in
    case split_slash s of
      NONE => NONE
    | SOME (num_s, den_s) =>
      let
        val num = Arbint.fromString num_s
        val den = Arbint.fromString den_s
      in
        if Arbint.compare (den, Arbint.one) = EQUAL then
          (* integer-valued rational: just make the real literal *)
          SOME (realSyntax.term_of_int num)
        else
          (* actual fraction: num/den *)
          SOME (realSyntax.mk_div (realSyntax.term_of_int num,
                                    realSyntax.term_of_int den))
      end
      handle _ => NONE
  end

  (* Parse a term: collect tokens, strip annotations, register bindings *)
  fun parse_term (dicts_ref : dicts ref) get_token : Term.term =
  let
    val tokens = collect_term_tokens get_token
    val (stripped, bindings) = strip_named tokens
    (* Register bindings BEFORE parsing so that forward references to
       @-names within the same expression can be resolved.
       Each binding is lazily parsed: on first lookup, parse the inner
       tokens and cache the result. *)
    val _ = List.app (fn (name, inner_toks) =>
      let
        val cache : Term.term option ref = ref NONE
        fun parsefn _ indices args =
          if List.null indices andalso List.null args then
            case !cache of
              SOME t => t
            | NONE =>
              let val get' = Library.undo_look_ahead inner_toks
                    (fn () => raise ERR "named" "unexpected end")
                  val t = SmtLib_Parser.parse_term_with_cfg alethe_cfg get'
                            (!dicts_ref)
              in cache := SOME t; t end
          else raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
      in add_to_tmdict dicts_ref name parsefn end) bindings
    (* Now parse the stripped tokens *)
    val get_stripped = Library.undo_look_ahead stripped
          (fn () => raise ERR "parse_term" "unexpected end of stripped tokens")
    val term = SmtLib_Parser.parse_term_with_cfg alethe_cfg get_stripped
                 (!dicts_ref)
  in
    term
  end

  fun skip_sexp get_token =
  let
    fun skip depth =
    let val tok = get_token ()
    in
      if tok = "(" then skip (depth + 1)
      else if tok = ")" then
        (if depth > 0 then skip (depth - 1) else ())
      else skip depth
    end
  in
    skip 0
  end

  (* --------------------------------------------------------------------- *)
  (* Clause parsing                                                        *)
  (* --------------------------------------------------------------------- *)

  fun parse_clause (dicts_ref : dicts ref) get_token : Term.term list =
  let val tok = get_token ()
  in
    if tok = "(" then
      let val cl_tok = get_token ()
      in
        if cl_tok = "cl" then
          parse_clause_lits dicts_ref get_token []
        else raise ERR "parse_clause"
               ("expected 'cl', got '" ^ cl_tok ^ "'")
      end
    else
      let val get_token' = Library.undo_look_ahead [tok] get_token
      in [parse_term dicts_ref get_token'] end
  end

  and parse_clause_lits (dicts_ref : dicts ref) get_token acc =
  let val tok = get_token ()
  in
    if tok = ")" then List.rev acc
    else
      let val get_token' = Library.undo_look_ahead [tok] get_token
          val lit = parse_term dicts_ref get_token'
      in parse_clause_lits dicts_ref get_token (lit :: acc) end
  end

  (* --------------------------------------------------------------------- *)
  (* Step keyword argument parsing                                         *)
  (* --------------------------------------------------------------------- *)

  fun parse_id_list get_token =
  let
    val _ = Library.expect_token "(" (get_token ())
    fun loop acc =
      let val tok = get_token ()
      in if tok = ")" then List.rev acc else loop (tok :: acc) end
  in loop [] end

  fun parse_args_list (dicts_ref : dicts ref) get_token =
  let
    val _ = Library.expect_token "(" (get_token ())
    fun loop acc =
    let val tok = get_token ()
    in
      if tok = ")" then List.rev acc
      else
        let
          val get_token' = Library.undo_look_ahead [tok] get_token
          val arg = parse_term dicts_ref get_token'
            handle Feedback.HOL_ERR _ =>
              (if tok = "(" then (skip_sexp get_token; boolSyntax.T)
               else boolSyntax.T)
        in loop (arg :: acc) end
    end
  in loop [] end

  fun parse_step_args (dicts_ref : dicts ref) get_token =
  let
    fun loop rule premises args =
    let val tok = get_token ()
    in
      if tok = ")" then {rule = rule, premises = premises, args = args}
      else if tok = ":rule" then loop (get_token ()) premises args
      else if tok = ":premises" then loop rule (parse_id_list get_token) args
      else if tok = ":args" then
        loop rule premises (parse_args_list dicts_ref get_token)
      else if tok = ":discharge" then
        (parse_id_list get_token; loop rule premises args)
      else raise ERR "parse_step_args" ("unexpected '" ^ tok ^ "'")
    end
  in loop "" [] [] end

  (* --------------------------------------------------------------------- *)
  (* Anchor parsing                                                        *)
  (* --------------------------------------------------------------------- *)

  fun parse_anchor_args get_token =
  let
    (* Skip the :args list — we don't use it in replay.
       Just consume balanced parens: ( ... ) *)
    fun skip_args_list () =
    let
      val _ = Library.expect_token "(" (get_token ())
      fun skip depth =
        let val t = get_token ()
        in
          if t = "(" then skip (depth + 1)
          else if t = ")" then
            (if depth > 0 then skip (depth - 1) else ())
          else skip depth
        end
    in skip 0 end

    fun loop step_id args =
    let val tok = get_token ()
    in
      if tok = ")" then {step_id = step_id, args = args}
      else if tok = ":step" then loop (get_token ()) args
      else if tok = ":args" then (skip_args_list (); loop step_id [])
      else raise ERR "parse_anchor_args"
        ("unexpected '" ^ tok ^ "' (step_id=" ^ step_id ^ ")")
    end
  in loop "" [] end

  (* --------------------------------------------------------------------- *)
  (* define-fun / declare-fun / declare-sort handling                      *)
  (* --------------------------------------------------------------------- *)

  fun handle_define_fun (dicts_ref : dicts ref) get_token =
  let
    val name = get_token ()
    val _ = Library.expect_token "(" (get_token ())
    fun parse_svars acc =
      let val tok = get_token ()
      in if tok = ")" then List.rev acc
         else (Library.expect_token "(" tok;
               let val vname = get_token ()
                   val vty = SmtLib_Parser.parse_type get_token
                               (Lib.fst (!dicts_ref))
                   val _ = Library.expect_token ")" (get_token ())
               in parse_svars ((vname, vty) :: acc) end)
      end
    val svars = parse_svars []
    val domain_types = List.map Lib.snd svars
    val range_type = SmtLib_Parser.parse_type get_token (Lib.fst (!dicts_ref))
    (* temporarily add params to tmdict for parsing body *)
    val saved_dicts = !dicts_ref
    val _ = List.app (fn (n, ty) =>
      let val v = Term.mk_var (n, ty)
          fun pf _ indices args =
            if List.null indices andalso List.null args then v
            else raise ERR ("<" ^ n ^ ">") "wrong number of arguments"
      in add_to_tmdict dicts_ref n pf end) svars
    val _ = parse_term dicts_ref get_token  (* parse and discard body *)
    val _ = Library.expect_token ")" (get_token ())
    (* restore dicts, then add the defined name *)
    val _ = dicts_ref := saved_dicts
    val tm = Term.mk_var (name,
      boolSyntax.list_mk_fun (domain_types, range_type))
    val args_count = List.length domain_types
    fun parsefn _ indices args =
      if List.null indices andalso List.length args = args_count then
        Term.list_mk_comb (tm, args)
      else raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
  in
    add_to_tmdict dicts_ref name parsefn
  end

  fun handle_declare_fun (dicts_ref : dicts ref) get_token =
  let
    val (_, tmdict') = SmtLib_Parser.parse_declare_fun get_token (!dicts_ref)
  in
    dicts_ref := (Lib.fst (!dicts_ref), tmdict')
  end

  fun handle_declare_sort (dicts_ref : dicts ref) get_token =
  let
    val name = get_token ()
    val _ = Library.expect_token "0" (get_token ())
    val _ = Library.expect_token ")" (get_token ())
    val ty = Type.mk_vartype ("'" ^ name)
    fun parsefn _ indices args =
      if List.null indices andalso List.null args then ty
      else raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
  in
    add_to_tydict dicts_ref name parsefn
  end

  (* --------------------------------------------------------------------- *)
  (* Top-level proof command parsing                                       *)
  (* --------------------------------------------------------------------- *)

  (* stop_cond controls when parse_commands returns:
     NONE           = top-level, only stop on EOF
     SOME (NONE)    = stop on ")" (for paren-grouped output)
     SOME (SOME id) = stop after parsing step with matching id (subproof) *)
  fun parse_commands (dicts_ref : dicts ref) get_token
                     (stop_cond : string option option) acc =
  let
    val tok = (SOME (get_token ())) handle Feedback.HOL_ERR _ => NONE
  in
    case tok of
      NONE => List.rev acc
    | SOME ")" =>
        if stop_cond = SOME NONE then List.rev acc
        else parse_commands dicts_ref get_token stop_cond acc
    | SOME "(" =>
      let val cmd = get_token ()
      in
        if cmd = "assume" then
          let val id = get_token ()
              val term = parse_term dicts_ref get_token
              val _ = Library.expect_token ")" (get_token ())
          in
            parse_commands dicts_ref get_token stop_cond
              (Alethe_Proof.ASSUME (id, term) :: acc)
          end
        else if cmd = "step" then
          let val id = get_token ()
              val clause = parse_clause dicts_ref get_token
              val {rule, premises, args} =
                parse_step_args dicts_ref get_token
              val acc' = Alethe_Proof.STEP {id=id, clause=clause, rule=rule,
                                            premises=premises, args=args} :: acc
          in
            (* If this step closes the current subproof, return *)
            if stop_cond = SOME (SOME id) then List.rev acc'
            else parse_commands dicts_ref get_token stop_cond acc'
          end
        else if cmd = "anchor" then
          let val {step_id, args = anchor_args} = parse_anchor_args get_token
              val anchor : Alethe_Proof.anchor =
                {step_id = step_id, args = anchor_args}
              (* Subproof ends when we see a step with id = step_id *)
              val sub_cmds = parse_commands dicts_ref get_token
                               (SOME (SOME step_id)) []
          in
            parse_commands dicts_ref get_token stop_cond
              (Alethe_Proof.ANCHOR (anchor, sub_cmds) :: acc)
          end
        else if cmd = "define-fun" then
          (handle_define_fun dicts_ref get_token;
           parse_commands dicts_ref get_token stop_cond acc)
        else if cmd = "declare-fun" then
          (handle_declare_fun dicts_ref get_token;
           parse_commands dicts_ref get_token stop_cond acc)
        else if cmd = "declare-sort" then
          (handle_declare_sort dicts_ref get_token;
           parse_commands dicts_ref get_token stop_cond acc)
        else if cmd = "(" then
          (* Nested grouping paren: cvc5 wraps proof in ( ... ).
             Push back the inner "(" and parse commands until ")".
             cvc5 outputs the proof twice; stop after first group. *)
          let val get_token' = Library.undo_look_ahead [cmd] get_token
              val inner = parse_commands dicts_ref get_token'
                            (SOME NONE) []
          in
            if List.null acc then
              (* First group: take it and stop *)
              List.rev (List.rev inner @ acc)
            else
              (* Already have commands; ignore duplicate *)
              List.rev acc
          end
        else
          (skip_sexp get_token;
           parse_commands dicts_ref get_token stop_cond acc)
      end
    | SOME _ =>
        parse_commands dicts_ref get_token stop_cond acc
  end

in

  fun parse_stream (tydict : Type.hol_type SmtLib_Parser.dict,
                    tmdict : Term.term SmtLib_Parser.dict)
                   (instream : TextIO.instream)
                   : Alethe_Proof.proof =
  let
    val get_char = Library.get_buffered_char instream
    val get_token = Library.get_token get_char
    (* Add a catch-all "_" entry for cvc5 rational literals like "0/1" *)
    fun cvc5_literal_parsefn token indices args =
      if List.null indices andalso List.null args then
        case try_parse_rational token of
          SOME t => t
        | NONE =>
          (* Try negative integer literal like "-1", "-42" *)
          if String.size token > 1 andalso String.sub (token, 0) = #"-" then
            let val num_str = String.extract (token, 1, NONE)
                val n = Library.parse_arbnum num_str
            in intSyntax.term_of_int (Arbint.~ (Arbint.fromNat n)) end
          (* If it's a numeral or BV literal, let the standard dictionaries
             handle it (they have their own "_" entries) *)
          else if SmtLib_Theories.is_numeral token orelse
                  String.isPrefix "#b" token orelse
                  String.isPrefix "#x" token then
            raise ERR "cvc5_literal_parsefn" "standard literal"
          (* Unknown identifier — create a free bool variable as placeholder.
             This handles bound variable names (b0, b1, ...) and other names
             that appear in cvc5 proofs but not in the inverted dictionary. *)
          else Term.mk_var (token, Type.bool)
      else if List.null indices then
        (* Applied to arguments: create a function variable *)
        let val arg_tys = List.map Term.type_of args
            val rng_ty = Type.bool (* guess — may need refinement *)
            val fun_ty = boolSyntax.list_mk_fun (arg_tys, rng_ty)
            val f = Term.mk_var (token, fun_ty)
        in Term.list_mk_comb (f, args) end
      else raise ERR "cvc5_literal_parsefn" "indexed not supported"
    val tmdict' = Library.extend_dict (("_", cvc5_literal_parsefn), tmdict)
    val dicts_ref = ref (tydict, tmdict')
  in
    parse_commands dicts_ref get_token NONE []
  end

end

end
