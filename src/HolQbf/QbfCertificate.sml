(* Copyright (c) 2010 Tjark Weber. All rights reserved. *)

(* QBF Certificates and proof reconstruction.

   As defined in "A File Format for QBF Certificates" by Daniel Kroening and
   Christoph M. Wintersteiger (2007-05-01, available at
   http://www.verify.ethz.ch/qbv/download/qbcformat.pdf).

   Also see "A First Step Towards a Unified Proof Checker for QBF" by Toni
   Jussila, Armin Biere, Carsten Sinz, Daniel Kröning and Christoph
   Wintersteiger, published at SAT 2007 (vol. 4501 of LNCS).

   We additionally require that certificates of validity contain "extensions"
   only, and that certificates of invalidity contain "resolutions" only (as
   defined in the first paper above).
*)

structure QbfCertificate =
struct

  val ERR = Feedback.mk_HOL_ERR "QbfCertificate"

(* ------------------------------------------------------------------------- *)
(* The type of QBF certificates.                                             *)
(* ------------------------------------------------------------------------- *)

  type cindex = int  (* clause index, must be >= 1 *)
  type vindex = int  (* variable index, must be >= 1 *)
  type literal = int  (* a possibly negated variable index, must be <> 0 *)

  datatype extension = ITE of literal * literal * literal
                     | AND of literal list

  type resolution = literal list * cindex list

  datatype certificate =
      VALID of (vindex, extension) Redblackmap.dict
        * (vindex, literal) Redblackmap.dict
    | INVALID of (cindex, resolution) Redblackmap.dict * cindex

(* ------------------------------------------------------------------------- *)
(* read_certificate_file: reads a QBF certificate from a file                *)
(* ------------------------------------------------------------------------- *)

  (* This would arguably be much nicer to implement with parser combinators.
     Or perhaps one should use mllex/mlyacc. *)

  fun read_certificate_file path =
  let
    (* string list -> string list *)
    fun filter_header ("QBCertificate\n" :: lines) =
      lines
      | filter_header _ =
      raise ERR "read_certificate_file" "'QBCertificate' header not found"
    (* string -> int *)
    fun int_from_string s =
      case Int.fromString s of
        NONE =>
        raise ERR "read_certificate_file"
          ("integer expected ('" ^ s ^ "' found)")
      | SOME i =>
        i
    (* literal list -> string list -> literal list *)
    fun extension_lits lits ["0"] =
      List.rev lits
      | extension_lits _ ("0" :: _) =
      raise ERR "read_certificate_file"
        "unexpected input after '0'-terminated list of extension literals"
      | extension_lits _ [] =
      raise ERR "read_certificate_file"
        "missing '0' terminator after extension literals"
      | extension_lits lits (literal :: xs) =
      extension_lits (int_from_string literal :: lits) xs
    (* (vindex, extension) dict -> string list -> (vindex, extension) dict *)
    fun extension ext [vindex, "I", lit1, lit2, lit3] =
      Redblackmap.insert (ext, int_from_string vindex,
        ITE (int_from_string lit1, int_from_string lit2, int_from_string lit3))
      | extension ext (vindex :: "A" :: lits) =
      Redblackmap.insert (ext, int_from_string vindex,
        AND (extension_lits [] lits))
      | extension _ _ =
      raise ERR "read_certificate_file" "extension: invalid format"
    (* cindex list -> string list -> cindex list *)
    fun resolution_clauses clauses ["0"] =
        List.rev clauses
      | resolution_clauses clauses ("0" :: _) =
        raise ERR "read_certificate_file"
          "unexpected input after '0'-terminated list of resolution clauses"
      | resolution_clauses clauses (cindex :: xs) =
        resolution_clauses (int_from_string cindex :: clauses) xs
      | resolution_clauses _ [] =
      raise ERR "read_certificate_file"
        "resolution: '0' expected to terminate list of resolution clauses"
    (* literal list -> string list -> resolution *)
    fun resolution_args lits ("0" :: xs) =
      (List.rev lits, resolution_clauses [] xs)
      | resolution_args lits (lit :: xs) =
      resolution_args (int_from_string lit :: lits) xs
      | resolution_args _ [] =
      raise ERR "read_certificate_file"
        "resolution: '0' expected to terminate list of resolution literals"
    (* (cindex, resolution) dict -> string list -> (cindex, resolution) dict *)
    fun resolution res (cindex :: xs) =
      Redblackmap.insert (res, int_from_string cindex, resolution_args [] xs)
      | resolution _ _ =
      raise ERR "read_certificate_file" "resolution: clause index expected"
    (* (vindex, literal) dict -> string list -> (vindex, literal) dict *)
    fun valid_conclusion dict [] =
      dict
      | valid_conclusion dict (vindex :: literal :: xs) =
      valid_conclusion (Redblackmap.insert
        (dict, int_from_string vindex, int_from_string literal)) xs
      | valid_conclusion _ _ =
      raise ERR "read_certificate_file"
        "vindex/literal pair expected in conclusion"
    (* (vindex, extension) dict * (cindex, resolution) dict -> string list ->
         conclusion *)
    fun conclusion (ext, res) ("VALID" :: xs) =
      let
        val _ = Redblackmap.isEmpty res orelse
          raise ERR "read_certificate_file"
            "conclusion is 'VALID', but there are resolutions"
      in
        VALID (ext, valid_conclusion (Redblackmap.mkDict Int.compare) xs)
      end
      | conclusion (ext, res) ["INVALID", cindex] =
      let
        val _ = Redblackmap.isEmpty ext orelse
          raise ERR "read_certificate_file"
            "conclusion is 'INVALID', but there are extensions"
      in
        INVALID (res, int_from_string cindex)
      end
      | conclusion _ _ =
      raise ERR "read_certificate_file" "conclusion: invalid format"
    (* (vindex, extension) dict * (cindex, resolution) dict -> string list list
         -> certificate *)
    fun certificate (ext, res) ["CONCLUDE" :: xs] =
        conclusion (ext, res) xs
      | certificate _ (("CONCLUDE" :: _) :: _) =
        raise ERR "read_certificate_file" "unexpected input after conclusion"
      | certificate (ext, res) (("E" :: xs) :: xss) =
      certificate (extension ext xs, res) xss
      | certificate (ext, res) (xs :: xss) =
      certificate (ext, resolution res xs) xss
      | certificate _ [] =
        raise ERR "read_certificate_file" "empty certificate"
  in
    (certificate
       (Redblackmap.mkDict Int.compare, Redblackmap.mkDict Int.compare)
    o (map (String.tokens (Lib.C Lib.mem [#" ", #"\t", #"\n"])))
    o filter_header
    o List.filter (fn l => l <> "\n")
    o QbfLibrary.read_lines_from_file) path
  end

(* ------------------------------------------------------------------------- *)
(* check: proves or disproves the QBF 't' (see QDimacs.sml for the format of *)
(*      QBFs), using an appropriate certificate.  Returns either "|- t" (if  *)
(*      the certificate is 'VALID ...') or "t |- F" (if the certificate is   *)
(*      'INVALID ...').  Fails if 't' is not a QBF, or if the certificate is *)
(*      not suitable for 't'.                                                *)
(* ------------------------------------------------------------------------- *)

  fun check t (VALID _) =
    raise ERR "check" "certificate says \"VALID\": not implemented yet"
(* ------------------------------------------------------------------------- *)
    | check t (INVALID (dict, cindex)) =
    let
      (* pre-processing: break the problem apart into clauses in sequent form
         suitable for Q-resolution *)

      (* We assume that there are no free variables in 't', so that *all*
         variables in the matrix occur in 'vars'. *)
      val (_, vars, matrix) = QbfLibrary.enumerate_quantified_vars t

      (* a dictionary that maps each variable to a pair, which consists of the
         variable's index and a Boolean that is true if the variable is
         universally quantified, and false if it is existentially quantified *)
      val var_dict = List.foldl (fn ((i, var, is_forall), var_dict) =>
        Redblackmap.insert (var_dict, var, (i, is_forall)))
        (Redblackmap.mkDict Term.var_compare) vars
      fun index_fn var =
        Redblackmap.find (var_dict, var)

      val vars = List.rev vars
      fun foldthis (clause, (i, clause_dict)) =
        let
          val clause = QbfLibrary.CLAUSE_TO_SEQUENT clause
          val lits = QbfLibrary.literals_in_clause index_fn clause
        in
          (i + 1, Redblackmap.insert (clause_dict, i,
            QbfLibrary.forall_reduce (clause, vars, matrix, lits)))
        end

      (* a dictionary that maps each clause identifier to a 4-tuple, which
         consists of 1. the clause theorem (in sequent form, cf.
         'QbfLibrary.CLAUSE_TO_SEQUENT'), 2. the list of missing variables (cf.
         'QbfLibrary.enumerate_quantified_vars', 3. the hypothesis (initially,
         this is 'matrix'), and 4. the list of literals in the clause (cf.
         'QbfLibrary.literals_in_clause' *)
      val clause_dict = Lib.snd (List.foldl foldthis
        (1, Redblackmap.mkDict Int.compare)
        (Drule.CONJUNCTS (Thm.ASSUME matrix)))

      (* depth-first recursion over the certificate (which represents a DAG),
         using QRESOLVE_CLAUSES to derive new clauses from existing ones *)
      fun derive (c_dict, index) =
        case Redblackmap.peek (c_dict, index) of
          SOME clause =>
          (c_dict, clause)
        | NONE =>
          let
            val (_, indices) = Redblackmap.find (dict, index)
              handle Redblackmap.NotFound =>
                raise ERR "check"
                  ("invalid certificate: no definition for clause ID " ^
                   Int.toString index)
            val _ = if List.null indices then
                raise ERR "check"
                  ("invalid certificate: empty definition for clause ID " ^
                     Int.toString index)
              else ()
            val (c_dict, clauses) = Lib.foldl_map derive (c_dict, indices)
            val clause = List.foldl (QbfLibrary.QRESOLVE_CLAUSES)
              (List.hd clauses) (List.tl clauses)
          in
            (Redblackmap.insert (c_dict, index, clause), clause)
          end

      (* derive "t |- F", using the certificate *)
      val thm = #1 (Lib.snd (derive (clause_dict, cindex)))

      (* sanity checks *)
      val _ = if !QbfTrace.trace < 1 orelse
          (HOLset.numItems (Thm.hypset thm) = 1 andalso
            HOLset.member (Thm.hypset thm, t)) then
          ()
        else
          Feedback.HOL_WARNING "QbfCertificate" "check" "final theorem has hyps"
      val _ = if !QbfTrace.trace < 1 orelse Thm.concl thm = boolSyntax.F then
          ()
        else
          Feedback.HOL_WARNING "QbfCertificate" "check" "final theorem not F"
    in
      thm
    end

end
