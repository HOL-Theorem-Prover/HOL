(* Copyright (c) 2010-2011 Tjark Weber. All rights reserved. *)

(* Parsing of SMT-LIB 2 benchmarks *)

structure SmtLib_Parser =
struct

  type 'a parse_fn = string -> Term.term list -> 'a list -> 'a

  type 'a dict = (string, 'a parse_fn list) Redblackmap.dict

  type dicts = Type.hol_type dict * Term.term dict

  type bindings = (string * Term.term * Term.term) list

  type parser_cfg = {
    mk_let_bindings: dicts * bindings -> Term.term dict,
    mk_let: bindings * Term.term -> Term.term,
    parse_lambda: bool
  }

local

  val ERR = Feedback.mk_HOL_ERR "SmtLib_Parser"
  val WARNING = Feedback.HOL_WARNING "SmtLib_Parser"

  (***************************************************************************)
  (* parsing of types/terms                                                  *)
  (***************************************************************************)

  (* 'parse_type' parses an SMT-LIB 2 type, returning a HOL4 type.

     'parse_term' parses an SMT-LIB 2 term, returning a HOL4 term.

     There are various requirements that affect the implementation:
     1. Parsing must be reasonably fast (i.e., dictionary-based, at
     least for most tokens). 2. The dictionary depends on the SMT-LIB
     logic, and possibly on local term definitions ("let"). 3. Due to
     overloading, there may be several dictionary entries for the same
     token. 4. Parsing a function symbol in some cases requires that
     the function arguments have been parsed (e.g., to instantiate
     types and to resolve overloading). 5. Parsing must deal with
     indexed identifiers, i.e., "(_ token m n ...)". 6. Parsing must
     deal with numerals. At least for these (but also for indexed
     tokens of the form tokenX, with X a numeral), a dictionary-based
     approach is not sufficient in general (but should still be used
     if possible).

     These are my solutions: 1. 'parse_term' takes a dictionary
     argument. 2. The dictionary is properly initialized by the
     caller. 3. The dictionary maps tokens to a list of parsing
     functions. 4. Each parsing function maps a (possibly empty) list
     of function arguments (parsed as HOL terms) to the HOL term that
     results from applying the (function corresponding to the) token
     to these arguments. It raises 'HOL_ERR' if the arguments are not
     valid. 'parse_term' uses the result of the first parsing function
     that does not raise 'HOL_ERR'. 5. Each parsing function
     additionally takes a list of indices, each one a `Term.term`. This
     list will be empty for non-indexed identifiers, and non-empty for
     indexed identifiers. Non-indexed identifiers are therefore
     parsed as a special case of indexed identifiers. This allows
     parsing functions for indexed and non-indexed identifiers to be
     stored in the same dictionary. 6. To deal with numerals and other
     tokens for which a dictionary-based approach is not sufficient,
     the dictionary additionally contains an entry for "_". If there
     is no dictionary entry for a token (or every parsing function in
     its dictionary entry raised 'HOL_ERR'), 'parse_term' uses the
     result of the first parsing function in the entry for "_" that
     does not raise 'HOL_ERR'. So the dictionary key "_" is NOT used
     for indexed identifiers (which are instead keyed by the first
     token following "_" in SMT-LIB syntax), but is instead used as a
     catch-all entry. The token itself is passed verbatim.

     FIXME: The current setup doesn't do implicit conversions
            properly. Certain SMT-LIB logics, e.g., AUFLIRA, insert
            implicit conversions, e.g., from Int to Real, under
            certain conditions. These could perhaps be inserted by
            'parse_compound_term' (below), only there is no way at the
            moment to tell 'parse_compound_term' what the conversions
            are, and when they should be applied.

     Some of the basic infrastructure for parsing types/terms is
     identical, but some of the high-level parsing functions
     necessarily differ: parsing terms requires two dictionaries (one
     for declared types, one for declared terms), while parsing types
     only requires one dictionary (for declared types). *)

  fun t_with_args dict (token : string) (indices : Term.term list)
      (args : 'a list) : 'a =
    Lib.tryfind (fn f => f token indices args) (Redblackmap.find (dict, token)
      handle Redblackmap.NotFound => [])
    handle Feedback.HOL_ERR _ =>
    (* catch-all *)
    Lib.tryfind (fn f => f token indices args) (Redblackmap.find (dict, "_")
      handle Redblackmap.NotFound => [])
    handle Feedback.HOL_ERR _ =>
      raise ERR "t_with_args" ("failed to parse '" ^ token ^
        "' (with indices [" ^ String.concatWith ", "
        (List.map Hol_pp.term_to_string indices) ^ "] and " ^
        Int.toString (List.length args) ^ " argument(s))")

  (***************************************************************************)
  (* type-specific parsing functions                                         *)
  (***************************************************************************)

  fun parse_indexed_type get_token dict : Type.hol_type list -> Type.hol_type =
  let
    (* returns all tokens before the next ")" *)
    fun get_tokens acc =
    let
      val token = get_token ()
    in
      if token = ")" then
        List.rev acc
      else
        get_tokens (token :: acc)
    end
  in
    case get_tokens [] of
      [] => raise ERR "parse_indexed_type" "'_' immediately followed by ')'"
    | hd::tl =>
        t_with_args dict hd (List.map (numSyntax.mk_numeral o
          Library.parse_arbnum) tl)
  end

  fun parse_type_operands get_token tydict acc : Type.hol_type list =
  let
    val token = get_token ()
  in
    if token = ")" then
      List.rev acc
    else
      let
        (* operands don't take arguments *)
        val operand = parse_type_aux get_token tydict token []
      in
        parse_type_operands get_token tydict (operand :: acc)
      end
  end

  and parse_compound_type get_token tydict (token : string) : Type.hol_type =
   let
    val headfn = parse_type_aux get_token tydict token
    val operands = parse_type_operands get_token tydict []
  in
    headfn operands
  end

  and parse_indexed_or_compound_type get_token tydict
    : Type.hol_type list -> Type.hol_type =
  let
    val token = get_token ()
  in
    if token = "_" then
      parse_indexed_type get_token tydict
    else
      let
        val t = parse_compound_type get_token tydict token
      in
        (* compounds don't take arguments *)
        fn [] => t
          | _ => raise ERR "parse_indexed_or_compound_type"
            "compound: no arguments expected"
      end
  end

  and parse_type_aux get_token tydict (token : string)
    : Type.hol_type list -> Type.hol_type =
    if token = "(" then
      parse_indexed_or_compound_type get_token tydict
    else
      t_with_args tydict token []

  fun parse_type get_token tydict : Type.hol_type =
    parse_type_aux get_token tydict (get_token ()) []

  fun parse_type_list get_token tydict : Type.hol_type list =
  (
    Library.expect_token "(" (get_token ());
    parse_type_operands get_token tydict []
  )

  (***************************************************************************)
  (* term-specific parsing functions                                         *)
  (***************************************************************************)

  fun parse_indexed_term cfg get_token (tydict, tmdict)
    : Term.term list -> Term.term =
  let
    val head = get_token ()

    (* returns all terms corresponding to the indices *)
    fun get_indices acc =
    let
      val token = get_token ()
      val get_token' = Library.undo_look_ahead [token] get_token
    in
      if token = ")" then
        List.rev acc
      else
        get_indices (parse_term_with_cfg cfg get_token' (tydict, tmdict) :: acc)
    end
  in
    t_with_args tmdict head (get_indices [])
  end

  and parse_var_bindings cfg get_token (tydict, tmdict)
    : (string * Term.term) list =
  let
    val _ = Library.expect_token "(" (get_token ())
    fun aux acc =
    let
      val token = get_token ()
    in
      if token = ")" then
        List.rev acc
      else
        let
          val _ = Library.expect_token "(" token
          val symbol = get_token ()
          val term = parse_term_with_cfg cfg get_token (tydict, tmdict)
          val _ = Library.expect_token ")" (get_token ())
        in
          aux ((symbol, term) :: acc)
        end
    end
  in
    aux []
  end

  and parse_let_term cfg get_token (tydict, tmdict) : Term.term =
  let
    val bindings = parse_var_bindings cfg get_token (tydict, tmdict)
    val bindings = List.map
      (fn (s, t) => (s, Term.mk_var (s, Term.type_of t), t)) bindings
    val tmdict = (#mk_let_bindings cfg) ((tydict, tmdict), bindings)
    val body = parse_term_with_cfg cfg get_token (tydict, tmdict)
    val _ = Library.expect_token ")" (get_token ())
  in
    (#mk_let cfg) (bindings, body)
  end

  and parse_sorted_vars get_token tydict : (string * Type.hol_type) list =
  let
    val _ = Library.expect_token "(" (get_token ())
    fun aux acc =
    let
      val token = get_token ()
    in
      if token = ")" then
        List.rev acc
      else
        let
          val _ = Library.expect_token "(" token
          val symbol = get_token ()
          val typ = parse_type get_token tydict
          val _ = Library.expect_token ")" (get_token ())
        in
          aux ((symbol, typ) :: acc)
        end
    end
  in
    aux []
  end

  and parse_binder_term cfg get_token (tydict, tmdict) mk_binder : Term.term =
  let
    val vars = parse_sorted_vars get_token tydict
    val vars = List.map (fn vT => (Lib.fst vT, Term.mk_var vT)) vars
    (* variables don't take arguments *)
    fun parsefn var token indices args =
      if List.null indices andalso List.null args then
        var
      else
        raise ERR ("<" ^ Hol_pp.term_to_string var ^ ">")
          "wrong number of arguments"
    val tmdict = List.foldl Library.extend_dict tmdict
      (List.map (Lib.apsnd parsefn) vars)
    val body = parse_term_with_cfg cfg get_token (tydict, tmdict)
    val _ = Library.expect_token ")" (get_token ())
  in
    mk_binder (List.map Lib.snd vars, body)
  end

  and parse_annotated_term cfg get_token (tydict, tmdict) : Term.term =
  let
    val term = parse_term_with_cfg cfg get_token (tydict, tmdict)
    (* we ignore all attributes; since these can be S-expressions, we
       need to count parentheses *)
    fun parse_attributes n =
    let
      val token = get_token ()
    in
      if token = ")" then
        if n = 0 then () else parse_attributes (n - 1)
      else if token = "(" then
        parse_attributes (n + 1)
      else
        parse_attributes n
    end
  in
    parse_attributes 0;
    term
  end

  and parse_term_operands cfg get_token (tydict, tmdict) acc : Term.term list =
  let
    val token = get_token ()
  in
    if token = ")" then
      List.rev acc
    else
      let
        (* operands don't take arguments *)
        val operand = parse_term_aux cfg get_token (tydict, tmdict) token []
      in
        parse_term_operands cfg get_token (tydict, tmdict) (operand :: acc)
      end
  end

  and parse_compound_term cfg get_token (tydict, tmdict) (token : string)
    : Term.term =
   let
    val headfn = parse_term_aux cfg get_token (tydict, tmdict) token
    val operands = parse_term_operands cfg get_token (tydict, tmdict) []
  in
    headfn operands
  end

  and parse_indexed_or_compound_term cfg get_token (tydict, tmdict)
    : Term.term list -> Term.term =
  let
    val token = get_token ()
  in
    if token = "_" then
      parse_indexed_term cfg get_token (tydict, tmdict)
    else
      let
        val t = if token = "let" then
            parse_let_term cfg get_token (tydict, tmdict)
          else if token = "forall" then
            parse_binder_term cfg get_token (tydict, tmdict)
              boolSyntax.list_mk_forall
          else if token = "exists" then
            parse_binder_term cfg get_token (tydict, tmdict)
              boolSyntax.list_mk_exists
          (* SMT-LIB 2.6 doesn't have special `lambda` terms, but Z3 proof
             certificates do. So we only parse them when allowed by the
             parser configuration, otherwise we will parse identifiers that are
             coincidentally named `lambda` as if they were special (this cannot
             happen in Z3 proof certificates since all user identifiers are
             renamed to non-conflicting names).
             In Z3 proof certificates, `lambda` terms only seem to be a local
             declaration of variable names/types that apparently need to be
             interpreted as free variables in the enclosed term. *)
          else if token = "lambda" andalso #parse_lambda cfg then
            parse_binder_term cfg get_token (tydict, tmdict)
              Lib.snd
          else if token = "!" then
            parse_annotated_term cfg get_token (tydict, tmdict)
          else
            parse_compound_term cfg get_token (tydict, tmdict) token
      in
        (* compounds don't take arguments *)
        fn [] => t
          | _ => raise ERR "parse_indexed_or_compound_term"
            "compound: no arguments expected"
      end
  end

  and parse_term_aux cfg get_token (tydict, tmdict) (token : string)
    : Term.term list -> Term.term =
    if token = "(" then
      parse_indexed_or_compound_term cfg get_token (tydict, tmdict)
    else
      t_with_args tmdict token []

  and parse_term_with_cfg cfg get_token (tydict, tmdict) : Term.term =
    parse_term_aux cfg get_token (tydict, tmdict) (get_token ()) []

  (* the SMT-LIB version of `mk_let_bindings` binds each name to a HOL4 variable
     with the same name *)
  fun smtlib_mk_let_bindings ((tydict, tmdict), bindings) : Term.term dict =
  let
    (* variables don't take arguments *)
    fun parsefn var token indices args =
      if List.null indices andalso List.null args then
        var
      else
        raise ERR ("<" ^ Hol_pp.term_to_string var ^ ">")
          "wrong number of arguments"
  in
    List.foldl Library.extend_dict tmdict
      (List.map (fn (s, var, _) => (s, parsefn var)) bindings)
  end

  (* the SMT-LIB version of `mk_let` constructs a HOL4 `let` term *)
  fun smtlib_mk_let (bindings, body) : Term.term =
    pairSyntax.mk_anylet (List.map (fn (_, var, t) => (var, t)) bindings, body)

  val smtlib_cfg = {
    mk_let_bindings = smtlib_mk_let_bindings,
    mk_let = smtlib_mk_let,
    parse_lambda = false
  }

  val parse_term = parse_term_with_cfg smtlib_cfg

  fun parse_term_list get_token (tydict, tmdict) : Term.term list =
  (
    Library.expect_token "(" (get_token ());
    parse_term_operands smtlib_cfg get_token (tydict, tmdict) []
  )

  (***************************************************************************)
  (* parsing of benchmarks                                                   *)
  (***************************************************************************)

  (* we simply ignore all following tokens up to the next ")" *)
  fun parse_set_info get_token =
    if get_token () = ")" then
      ()
    else
      parse_set_info get_token

  (* returns the SMT-LIB logic name and its type/term dictionaries *)
  fun parse_set_logic get_token =
  let
    val logic = get_token ()
    val (tydict, tmdict) = SmtLib_Logics.parsedicts_of_logic logic
    val _ = Library.expect_token ")" (get_token ())
  in
    (logic, tydict, tmdict)
  end

  (* returns an extended 'tydict' *)
  (* FIXME: We only allow sort declarations of arity 0 at present. *)
  fun parse_declare_sort get_token tydict =
  let
    val name = get_token ()
    val _ = Library.expect_token "0" (get_token ())
    val _ = Library.expect_token ")" (get_token ())
    val ty = Type.mk_vartype ("'" ^ name)
    fun parsefn token indices args =
      if List.null indices andalso List.null args then
        ty
      else
        raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
  in
    Library.extend_dict ((name, parsefn), tydict)
  end

  (* returns an extended 'tmdict' *)
  fun parse_declare_const_fun parse_types get_token (tydict, tmdict) =
  let
    val name = get_token ()
    val domain_types =
      if parse_types then
        parse_type_list get_token tydict
      else
        []
    val range_type = parse_type get_token tydict
    val _ = Library.expect_token ")" (get_token ())
    val tm = Term.mk_var (name,
      boolSyntax.list_mk_fun (domain_types, range_type))
    val args_count = List.length domain_types
    fun parsefn token indices args =
      if List.null indices andalso List.length args = args_count then
        Term.list_mk_comb (tm, args)
      else
        raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
  in
    (tm, Library.extend_dict ((name, parsefn), tmdict))
  end

  val parse_declare_const = parse_declare_const_fun false
  val parse_declare_fun = parse_declare_const_fun true

  (* returns an extended 'tmdict', and the definition (as a formula) *)
  fun parse_define_fun get_token (tydict, tmdict) =
  let
    val name = get_token ()
    val vars = parse_sorted_vars get_token tydict
    val domain_types = List.map Lib.snd vars
    val range_type = parse_type get_token tydict
    val vars = List.map (fn vT => (Lib.fst vT, Term.mk_var vT)) vars
    (* variables don't take arguments *)
    fun var_parsefn var token indices args =
      if List.null indices andalso List.null args then
        var
      else
        raise ERR ("<" ^ Hol_pp.term_to_string var ^ ">")
          "wrong number of arguments"
    val definiens_tmdict = List.foldl Library.extend_dict tmdict
      (List.map (Lib.apsnd var_parsefn) vars)
    val definiens = parse_term get_token (tydict, definiens_tmdict)
    val _ = Library.expect_token ")" (get_token ())
    (* 'name' from now on should be parsed as 'tm' *)
    val tm = Term.mk_var (name,
      boolSyntax.list_mk_fun (domain_types, range_type))
    val args_count = List.length domain_types
    fun parsefn token indices args =
      if List.null indices andalso List.length args = args_count then
        Term.list_mk_comb (tm, args)
      else
        raise ERR ("<" ^ name ^ ">") "wrong number of arguments"
    val tmdict = Library.extend_dict ((name, parsefn), tmdict)
    (* the semantics of define-fun: ``!x1...xn. f x1 ... xn = definiens`` *)
    val vars = List.map Lib.snd vars
    val definition = boolSyntax.list_mk_forall (vars,
      boolSyntax.mk_eq (Term.list_mk_comb (tm, vars), definiens))
  in
    (tmdict, definition)
  end

  fun dest_state cmd (SOME x) = x
    | dest_state cmd NONE     =
        raise ERR "dest_state" ("received " ^ cmd ^ " before set-logic")

  and finalize_state cmd state =
  let
    val (logic, tydict, tmdict, asserted) = dest_state cmd state
  in
    (logic, tydict, tmdict, List.rev asserted)
  end

  (* returns the logic's name, its 'tydict', its 'tmdict' extended with
     declared function symbols, and a list of asserted formulas *)
  and parse_command command get_token state =
    case command of "set-info" =>
      let
        val _ = parse_set_info get_token
      in
        parse_commands get_token state
      end
    | "set-logic" =>
      let
        val _ = not (Option.isSome state) orelse
          raise ERR "parse_commands" "set-logic issued more than once"
        val (logic, tydict, tmdict) = parse_set_logic get_token
      in
        parse_commands get_token (SOME (logic, tydict, tmdict, []))
      end
    | "declare-sort" =>
      let
        val (logic, tydict, tmdict, asserted) = dest_state "declare-sort" state
        val tydict = parse_declare_sort get_token tydict
      in
        parse_commands get_token (SOME (logic, tydict, tmdict, asserted))
      end
    | "declare-const" =>
      let
        val (logic, tydict, tmdict, asserted) = dest_state "declare-const" state
        val (_, tmdict) = parse_declare_const get_token (tydict, tmdict)
      in
        parse_commands get_token (SOME (logic, tydict, tmdict, asserted))
      end
    | "declare-fun" =>
      let
        val (logic, tydict, tmdict, asserted) = dest_state "declare-fun" state
        val (_, tmdict) = parse_declare_fun get_token (tydict, tmdict)
      in
        parse_commands get_token (SOME (logic, tydict, tmdict, asserted))
      end
    | "define-fun" =>
      let
        val (logic, tydict, tmdict, asserted) = dest_state "define-fun" state
        val (tmdict, def) = parse_define_fun get_token (tydict, tmdict)
        val asserted = def :: asserted
      in
        parse_commands get_token (SOME (logic, tydict, tmdict, asserted))
      end
    | "assert" =>
      let
        val (logic, tydict, tmdict, asserted) = dest_state "assert" state
        val asserted = parse_term get_token (tydict, tmdict) :: asserted
        val _ = Library.expect_token ")" (get_token ())
      in
        parse_commands get_token (SOME (logic, tydict, tmdict, asserted))
      end
    | "check-sat" =>
      let
        val _ = dest_state "check-sat" state
        val _ = Library.expect_token ")" (get_token ())
      in
        parse_commands get_token state
      end
    | "get-proof" =>
      let
        val _ = dest_state "get-proof" state
        val _ = Library.expect_token ")" (get_token ())
      in
        parse_commands get_token state
      end
    | "exit" =>
      finalize_state "exit" state
        before Library.expect_token ")" (get_token ())
    | _ =>
      raise ERR "parse_commands" ("unknown command '" ^ command ^ "'")

  (* returns the logic's name, its 'tydict', its 'tmdict' extended with
     declared function symbols, and a list of asserted formulas *)
  and parse_commands get_token state =
  let
    val tok = SOME (get_token ())
      (* assume an error to be end-of-stream *)
      handle _ => NONE
  in
    case tok of
      NONE => finalize_state "(end-of-stream)" state
    | SOME t => (
        Library.expect_token "(" t;
        parse_command (get_token ()) get_token state
      )
  end

  (* entry point into the parser (i.e., the grammar's start symbol) *)
  fun parse_benchmark get_token =
    parse_commands get_token NONE

in

  val smtlib_mk_let_bindings = smtlib_mk_let_bindings
  val smtlib_mk_let = smtlib_mk_let

  val parse_declare_fun = parse_declare_fun

  val parse_type = parse_type
  val parse_type_list = parse_type_list

  val parse_term_with_cfg = parse_term_with_cfg
  val parse_term = parse_term
  val parse_term_list = parse_term_list

  (* 'parse_file' parses an SMT-LIB 2 benchmark, returning the
     benchmark's logic, two dictionaries containing all types and
     terms, respectively, declared in the benchmark, and a list of
     "assert"ed formulae *)

  (* FIXME: We only parse "set-logic", "declare-sort", "declare-fun",
            "define-fun" and "assert" commands.  We ignore some and
            disallow most other SMT-LIB 2 commands.  We do NOT perform
            assertion stack management (cf. "push"/"pop" in the
            SMT-LIB 2 standard).  Our implementation, although
            oversimplified, happens to work for most benchmarks
            currently (as of 2011-05-20) found in the SMT-LIB
            library. *)

  fun parse_file (path : string)
    : string * Type.hol_type dict * Term.term dict * Term.term list =
  let
    (* parse the file contents *)
    val _ = if !Library.trace > 1 then
        Feedback.HOL_MESG
          ("HolSmtLib: parsing SMT-LIB 2 benchmark file '" ^ path ^ "'")
      else ()
    val instream = TextIO.openIn path
    val get_token = Library.get_token (Library.get_buffered_char instream)
    val result = parse_benchmark get_token
    val _ = if !Library.trace > 0 then
        WARNING "parse_file" ("ignoring token '" ^ get_token () ^
          "' (and perhaps others) after benchmark")
          handle Feedback.HOL_ERR _ => ()  (* end of file, as expected *)
      else ()
    val _ = TextIO.closeIn instream
  in
    result
  end

end  (* local *)

end
