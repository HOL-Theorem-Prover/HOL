(* Copyright (c) 2010 Tjark Weber. All rights reserved. *)

(* Translation between (the QBF-in-prenex-form subset of) HOL terms and the
   QDIMACS file format.

   This file implements (parts of) the QDIMACS standard, version 1.1 (released
   on December 21, 2005), as described at http://www.qbflib.org/qdimacs.html
*)

structure QDimacs =
struct

  val ERR = Feedback.mk_HOL_ERR "QDimacs"

(* ------------------------------------------------------------------------- *)
(* write_qdimacs_file: serializes a QBF 't' to a file in QDIMACS format. 't' *)
(*      must have the following form:                                        *)
(*        Q1 x1. Q2 x2. ... Qn xn. phi(x1, ..., xn)                          *)
(*      where n>=0, each Qi is a quantifier (either ? or !), Qn is ? (i.e.,  *)
(*      the existential quantifier), each xi is a Boolean variable, and phi  *)
(*      is a propositional formula in CNF, i.e., a conjunction of            *)
(*      disjunctions of (possibly negated) variables.  phi must actually     *)
(*      contain each xi (and all xi must be distinct).                       *)
(*                                                                           *)
(*      'write_qdimacs_file' fails if 't' does not adhere to the above       *)
(*      structure.                                                           *)
(*                                                                           *)
(*      According to the semantics of the QDIMACS format (which is backward  *)
(*      compatible with the DIMACS CNF format), free variables in phi are    *)
(*      (implicitly) existentially quantified at the outermost level: e.g.,  *)
(*      "!x. x \/ y" is satisfiable.  Contrast this with the semantics of    *)
(*      free variables in HOL theorems, which are (implicitly) universally   *)
(*      quantified at the outermost level: e.g., "!x. x \/ y" is not a       *)
(*      theorem in HOL.                                                      *)
(*                                                                           *)
(*      Returns a dictionary mapping variables in 't' to QDIMACS variable    *)
(*      indices (i.e., positive integers).                                   *)
(* ------------------------------------------------------------------------- *)

  fun write_qdimacs_file path t =
  let
    (* "global" state references (could instead be passed as arguments to the
       following functions to obtain a purely functional implementation) *)
    val freshvar = ref 1
    val dict = ref (Redblackmap.mkDict Term.compare)
    (* the following functions essentially implement the production rules of
       the QDIMACS grammar *)
    (* term -> string *)
    fun variable_to_qdimacs tm =
      if Term.is_var tm then
        Int.toString (Redblackmap.find (!dict, tm)
          handle Redblackmap.NotFound =>
            let
              val fresh = !freshvar
            in
              freshvar := fresh + 1;
              dict := Redblackmap.insert (!dict, tm, fresh);
              fresh
            end)
      else
        raise ERR "write_qdimacs_file"
          ("term is not a QBF (variable expected, subterm '" ^
          Hol_pp.term_to_string tm ^ "' found)")
    (* term -> string *)
    fun literal_to_qdimacs tm =
      "-" ^ variable_to_qdimacs (boolSyntax.dest_neg tm)
      handle Feedback.HOL_ERR _ =>  (* 'tm' is not a negation *)
        variable_to_qdimacs tm
    (* term -> string *)
    fun clause_to_qdimacs tm =
      String.concatWith " " (map literal_to_qdimacs (boolSyntax.strip_disj tm))
        ^ " 0\n"
    (* returns a string list (rather than a single string) to avoid reaching
       String.maxSize when there are many clauses; also returns the number of
       clauses *)
    (* term -> string list * int *)
    fun matrix_to_qdimacs tm =
      Lib.S Lib.pair List.length
        (map clause_to_qdimacs (boolSyntax.strip_conj tm))
    (* auxiliary function to strip off quantifiers over Boolean variables *)
    (* (term -> term * term) -> term -> term list * term *)
    fun strip_bool_quantifier dest_fn tm =
      let
        val (bvar, body) = dest_fn tm
        val _ = Term.type_of bvar = Type.bool orelse
          raise ERR "write_qdimacs_file"
            ("term is not a QBF (quantified variable '" ^
              Hol_pp.term_to_string bvar ^ "' is not of type bool)")
        (* QDIMACS requires each bound variable to occur in the matrix *)
        val _ = Term.free_in bvar body orelse
          raise ERR "write_qdimacs_file"
            ("term is not a QBF (quantified variable '" ^
              Hol_pp.term_to_string bvar ^ "' not free in the body)")
      in
        Lib.apfst (Lib.cons bvar) (strip_bool_quantifier dest_fn body)
      end
      handle (e as Feedback.HOL_ERR {origin_function, ...}) =>
        if origin_function = "write_qdimacs_file" then
          (* re-raise *)
          raise e
        else
          (* error in 'dest_fn' *)
          ([], tm)
    (* string -> term list -> string *)
    fun quantset_to_qdimacs ae bvars =
      (* add all 'bvars' to the dictionary -- at this point, we can be certain
         that no bound variable is in the dictionary yet *)
      ae ^ " " ^ String.concatWith " " (map variable_to_qdimacs bvars) ^ " 0\n"
    (* term -> string list * int *)
    fun exists_to_qdimacs tm =
      case strip_bool_quantifier boolSyntax.dest_exists tm of
        ([], _) =>
          raise ERR "write_qdimacs_file"
            "term is not a QBF (innermost quantifier must be existential)"
      | (bvars, body) =>
          Lib.apfst (Lib.cons (quantset_to_qdimacs "e" bvars))
            (optional_forall_to_qdimacs body)
    (* term -> string list * int *)
    and optional_forall_to_qdimacs tm =
      case strip_bool_quantifier boolSyntax.dest_forall tm of
        ([], _) =>
          matrix_to_qdimacs tm
      | (bvars, body) =>
          Lib.apfst (Lib.cons (quantset_to_qdimacs "a" bvars))
            (exists_to_qdimacs body)
    (* term -> string list * int *)
    fun term_to_qdimacs tm =
      case strip_bool_quantifier boolSyntax.dest_exists tm of
        ([], _) =>
          optional_forall_to_qdimacs tm
      | (bvars, body) =>
          Lib.apfst (Lib.cons (quantset_to_qdimacs "e" bvars))
            (optional_forall_to_qdimacs body)
    val (strings, number_of_clauses) = term_to_qdimacs t
    val strings = "c This file was generated by QDimacs.write_qdimacs_file\n" ::
      "p cnf " ^ Int.toString (!freshvar - 1) ^ " " ^
      Int.toString number_of_clauses ^ "\n" :: strings
  in
    QbfLibrary.write_strings_to_file path strings;
    !dict
  end

(* ------------------------------------------------------------------------- *)
(* dict_to_varfn: converts a dictionary returned by 'write_qdimacs_file'     *)
(*      into a function that can be passed to 'read_qdimacs_file' as its     *)
(*      'varfn' argument.                                                    *)
(* ------------------------------------------------------------------------- *)

  fun dict_to_varfn dict : int -> Term.term =
  let
    val inverted_dict = Redblackmap.foldl (fn (t, i, dict) =>
      Redblackmap.insert (dict, i, t)) (Redblackmap.mkDict Int.compare) dict
  in
    fn i => Redblackmap.find (inverted_dict, i)
      handle Redblackmap.NotFound =>
        raise Feedback.mk_HOL_ERR "QDimacs" "dict_to_varfn"
          ("unknown index " ^ Int.toString i)
  end

(* ------------------------------------------------------------------------- *)
(* read_qdimacs_file: returns a QBF (as a HOL term) that corresponds to the  *)
(*      QBF problem given in a file in QDIMACS format.  See the description  *)
(*      of 'write_qdimacs_file' for further explanations.                    *)
(*                                                                           *)
(*      'varfn' must map QDIMACS variable indices (i.e., positive integers)  *)
(*      to HOL variables of type bool.  'varfn' is expected to be injective, *)
(*      a function (i.e., the result only depends on its argument), and      *)
(*      reasonably fast.  (For instance, 'varfn' could prepend "v" or        *)
(*      similar to a string representation of its argument to obtain the     *)
(*      variable name.)  Also see 'dict_to_varfn'.                           *)
(*                                                                           *)
(*      'read_qdimacs_file' is slightly lenient toward certain file format   *)
(*      errors. It may fail when applied to a file that is not in QDIMACS    *)
(*      format, or it may return a term that is not a valid QBF.             *)
(* ------------------------------------------------------------------------- *)

  (* This would arguably be much nicer to implement with parser combinators.
     Or perhaps one should use mllex/mlyacc. *)

  fun read_qdimacs_file (varfn : int -> Term.term) path =
  let
    (* string list -> string list *)
    fun filter_preamble [] =
      raise ERR "read_qdimacs_file" "problem line not found in QDIMACS file"
      | filter_preamble (line :: lines) =
      if String.isPrefix "c" line then
        (* ignore comments *)
        filter_preamble lines
      else if String.isPrefix "p " line then
        (* Ignore the problem line (which must be the last line of the
           preamble), return the remaining lines.  Hence, we are a bit lenient:
           if the file contains more clauses or variables than specified in its
           preamble, this code will accept it anyway. *)
        lines
      else
        raise ERR "read_qdimacs_file"
          "preamble contains a line that does not begin with \"c \" or \"p \""
    (* string -> term *)
    fun mk_var s =
      let
        val i = Option.valOf (Int.fromString s)
          handle Option.Option =>
            raise ERR "read_qdimacs_file"
              ("integer expected, but '" ^ s ^ "' found")
      in
        varfn i
      end
    (* splits a list of strings into elements before the first "0", and those
       after it *)
    (* string list -> string list * string list *)
    val split0 =
      let
        fun split_acc acc [] =
          raise ERR "read_qdimacs_file" "missing \"0\" in QDIMACS file"
          | split_acc acc ("0" :: xs) =
          (List.rev acc, xs)
          | split_acc acc (x :: xs) =
          split_acc (x :: acc) xs
      in
        split_acc []
      end
    (* string list -> term *)
    fun matrix xs =
      let
        (* string list list * string list -> string list list *)
        fun split0s (acc, []) =
          List.rev acc
          | split0s (acc, xs) =
          split0s (Lib.apfst (Lib.C Lib.cons acc) (split0 xs))
        (* string -> term *)
        fun mk_literal s =
          if String.isPrefix "-" s then
            boolSyntax.mk_neg (mk_var (String.extract (s, 1, NONE)))
          else
            mk_var s
        val clauses = map (map mk_literal) (split0s ([], xs))
      in
        boolSyntax.list_mk_conj (map boolSyntax.list_mk_disj clauses)
      end
    (* string list -> term *)
    fun prefix ("a" :: xs) =
      (boolSyntax.list_mk_forall o Lib.## (map mk_var, prefix) o split0) xs
      | prefix ("e" :: xs) =
      (boolSyntax.list_mk_exists o Lib.## (map mk_var, prefix) o split0) xs
      | prefix xs =
      matrix xs
    val tm = (prefix
      o List.concat
      o (map (String.tokens (Lib.C Lib.mem [#" ", #"\t", #"\n"])))
      o filter_preamble
      o List.filter (fn l => l <> "\n")
      o QbfLibrary.read_lines_from_file) path
    (* The QDIMACS standard requires that all bound variables actually occur in
       the matrix.  Issue a warning if this is not the case. *)
    fun check_bvars tm =
      let
        val (var, body) = boolSyntax.dest_forall tm
          handle Feedback.HOL_ERR _ =>  (* 'tm' is not universally quantified *)
            boolSyntax.dest_exists tm
      in
        if Term.free_in var body then
          check_bvars body
        else
          Feedback.HOL_WARNING "QDimacs" "read_qdimacs_file" ("bound variable "
            ^ Hol_pp.term_to_string var ^
            " (and perhaps others) not free in matrix")
      end
      handle Feedback.HOL_ERR _ =>  (* 'tm' is not existentially quantified *)
        ()
    val _ = if !QbfTrace.trace > 0 then check_bvars tm else ()
    (* Because the semantics of free variables differs in QDIMACS (where they
       are implicitly existential) vs. HOL (where they are implicitly
       universal), we inform the user if there are any free variables. *)
    val _ = if !QbfTrace.trace > 0 andalso
      HOLset.numItems (Term.FVL [tm] Term.empty_varset) > 0 then
        Feedback.HOL_WARNING "QDimacs" "read_qdimacs_file"
          "QDIMACS problem contains free variables"
      else ()
  in
    tm
  end

end
