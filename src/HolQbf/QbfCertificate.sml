(* Copyright (c) 2010 Tjark Weber. All rights reserved. *)

(* QBF certificates and proof reconstruction.

   As defined in "A File Format for QBF Certificates" by Daniel Kroening and
   Christoph M. Wintersteiger (2007-05-01, available at
   http://www.cprover.org/qbv/download/qbcformat.pdf).

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
      VALID of extension Inttab.table * literal Inttab.table
    | INVALID of resolution Inttab.table * cindex

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
    (* extension Inttab.table -> string list -> extension Inttab.table *)
    fun extension ext [vindex, "I", lit1, lit2, lit3] =
      Inttab.update (int_from_string vindex,
        ITE (int_from_string lit1, int_from_string lit2, int_from_string lit3))
        ext
      | extension ext (vindex :: "A" :: lits) =
      Inttab.update (int_from_string vindex,
        AND (extension_lits [] lits)) ext
      | extension _ _ =
      raise ERR "read_certificate_file" "extension: invalid format"
    (* cindex list -> string list -> cindex list *)
    fun resolution_clauses clauses ["0"] =
        List.rev clauses
      | resolution_clauses clauses ("0" :: _) =
        raise ERR "read_certificate_file"
          "unexpected input after '0'-terminated list of clauses"
      | resolution_clauses clauses (cindex :: xs) =
        resolution_clauses (int_from_string cindex :: clauses) xs
      | resolution_clauses _ [] =
      raise ERR "read_certificate_file"
        "resolution: '0' expected to terminate list of clauses"
    (* literal list -> string list -> resolution *)
    fun resolution_args [] ("*" :: xs) =
        ([], resolution_clauses [] xs)
      | resolution_args _ ("*" :: _) =
        raise ERR "read_certificate_file"
          "resolution: '*' found after list of literals (use '0' instead)"
      | resolution_args lits ("0" :: xs) =
        (List.rev lits, resolution_clauses [] xs)
      | resolution_args lits (lit :: xs) =
        resolution_args (int_from_string lit :: lits) xs
      | resolution_args _ [] =
        raise ERR "read_certificate_file"
          "resolution: missing '*' or '0' terminator"
    (* resolution Inttab.table -> string list -> resolution Inttab.table *)
    fun resolution res (cindex :: xs) =
      Inttab.update (int_from_string cindex, resolution_args [] xs) res
      | resolution _ _ =
      raise ERR "read_certificate_file" "resolution: clause index expected"
    (* literal Inttab.table -> string list -> literal Inttab.table *)
    fun valid_conclusion dict [] =
      dict
      | valid_conclusion dict (vindex :: literal :: xs) =
      valid_conclusion
        (Inttab.update (int_from_string vindex, int_from_string literal) dict)
        xs
      | valid_conclusion _ _ =
      raise ERR "read_certificate_file"
        "vindex/literal pair expected in conclusion"
    (* extension Inttab.table * resolution Inttab.table -> string list ->
         conclusion *)
    fun conclusion (ext, res) ("VALID" :: xs) =
      let
        val _ = Inttab.is_empty res orelse
          raise ERR "read_certificate_file"
            "conclusion is 'VALID', but there are resolutions"
      in
        VALID (ext, valid_conclusion Inttab.empty xs)
      end
      | conclusion (ext, res) ["INVALID", cindex] =
      let
        val _ = Inttab.is_empty ext orelse
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
        raise ERR "read_certificate_file" "missing conclusion"
  in
    (certificate
       (Inttab.empty, Inttab.empty)
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

  local open Term in
    datatype vtype = Forall of term (* var *)
                   | Exists of (term * term) (* var, extvar *)
                   | Ext    of (term * term) (* extvar, definition *)
  end

  val sat_prove = ref HolSatLib.SAT_PROVE

  fun check t dict (VALID (exts,lits)) = let
    open Lib Thm Drule Term Type boolSyntax

    val (var_to_index, index_to_var) = let
      open String Int Option
      val s = "v"  (*TODO*)
      fun num_to_var n = mk_var(s^(toString n),bool)
      (* in this case we use the inverse of dict to
         map indexes to variables, but since dict only
         binds original variables, we update the inverse map
         on indexes of extension variables as necessary,
         (using num_to_var for extensions) *)
      fun invert_dict d =
        Termtab.fold (fn (v,n) => fn d => Inttab.update (n, v) d) d Inttab.empty
      val tcid = ref (invert_dict dict)
      fun update (n,v) = (tcid := Inttab.update (n, v) (!tcid); v)
    in
      ((fn v => valOf (Termtab.lookup dict v)),
       fn n => case Inttab.lookup (!tcid) n of
                   SOME v => v
                 | NONE => update (n, num_to_var n))
    end

    (* Strip quantifiers from t and return the matrix mat.
       Update lits map to map any unmapped variables to 0 (meaning T).
       Create vars map from a variable index to a vtype.
       Existential variables without witnesses are given an rhs of T.
       Create deps map from a variable index to a list of indexes
       indicating that this variable will appear on the rhs
       of the hypothesis defining each variable in the list.
       Deps also has the variable x_{n+1}, bound immediately
       after (inside) a variable x_n, in the list for x_n.
       After this pass, deps will map extension variables that are witnesses
       to singleton lists containing their corresponding existential variables.
       It will also map existential and universal variables to singleton
       lists containing the next bound variable (empty list for innermost) *)
    val (vars,mat,lits,deps,lvi) = let
      fun enum vars t lits' deps lvi = let
        val ((v,t), is_forall) = (dest_forall t, true)
          handle Feedback.HOL_ERR _ => (dest_exists t, false)
        val vi = var_to_index v
        val (var,lits',deps) =
          if is_forall then (Forall v,lits',deps) else
            (case Inttab.lookup lits vi of
                 SOME ext_lit =>
                 let
                   val ext_index = Int.abs ext_lit
                   val tm = index_to_var ext_index
                   val tm = if ext_lit < 0 then mk_neg tm else tm
                 in
                   (Exists (v, tm), lits',
                    Inttab.update (ext_index, [vi]) deps)
                 end
               | NONE => (Exists (v, T),
                          Inttab.update (vi, 0) lits',
                          deps))
        val deps =
            case lvi of
                NONE => deps
              | SOME lvi => Inttab.update (lvi, [vi]) deps
      in enum (Inttab.update (vi, var) vars) t lits' deps (SOME vi) end
      handle Feedback.HOL_ERR _ => (vars,t,lits',deps,lvi)
    in enum Inttab.empty t lits Inttab.empty NONE end
    val deps =
        case lvi of
            NONE => deps
          | SOME lvi => Inttab.update (lvi, []) deps

    (* add all the hypotheses for the original existential variables
       onto the front of the matrix, so we end up with
       (v1 = e1) ==> (v2 = e2) ==> ... ==> mat *)
    fun foldthis (_, Forall _) t = t
      | foldthis (_, Ext _) t = t
      | foldthis (_, Exists (v,tm)) t = mk_imp(mk_eq(v,tm),t)
    val mat = Inttab.fold foldthis vars mat

    (* extension_to_term calculates a term corresponding
         to the definition of an extension variable,
         plus the set of indexes that term depends on.
       If an extension is defined using an original existential variable v,
       replace references to v by references to v's witness (extension) variable.
       If v has no witness, replace references to v by references to T,
       but simplify as necessary.
       For example, if v has no witness:
         if v occurs in an AND, don't bother listing it.
         if ~v occurs in an AND, replace the AND by F,
         if v is the test in an ITE, replace the ITE by its consequent
         etc. *)
    local
      val empty = HOLset.empty Int.compare
      (* lit processes a literal l, accumulating dependencies in s.
         TFk is the continuation for when l has no witness.
           TFk is passed whether l was not negated
           (i.e. will be constant T, rather than constant F)
         vk is the continuation for when l has a witness.
           vk is passed the literal of the witness,
             and s with the index of the witness added *)
      fun lit (l,s) TFk vk = let
        val index = Int.abs l
      in case Inttab.lookup lits index of
             SOME el =>
             if el = 0 then TFk (l > 0) else let
               val ext_index = Int.abs el
               val s = HOLset.add(s,ext_index)
               val v = index_to_var ext_index
               val neg = if l < 0 then el > 0 else el < 0
               val v = if neg then mk_neg v else v
             in vk (v,s) end
           | NONE => let
               val s = HOLset.add(s,index)
               val v = index_to_var index
               val v = if l < 0 then mk_neg v else v
             in vk (v,s) end
      end
      exception False
      fun afold (l,(t,s)) = lit (l,s)
        (fn true=>(t,s)|false=>raise False)
        (fn(v,s)=>
         (case t of NONE   => SOME v
                  | SOME t => SOME (mk_conj(v,t)), s))
      fun negate t =
        dest_neg t handle Feedback.HOL_ERR _ => mk_neg t
    in
      fun extension_to_term (AND ls) =
      (let
            val (t,s) = List.foldl afold (NONE,empty) ls
          in case t of NONE   => (T,s)
                     | SOME t => (t,s)
          end handle False => (F,empty))
        | extension_to_term (ITE(t,c,a)) =
          lit (t,empty)
              (fn t=> lit (if t then c else a,empty)
                      (fn true=>(T,empty)|false=>(F,empty))
                      (fn(v,s)=>(v,s)))
              (fn(t,s)=> lit (c,s)
                         (fn c=> lit (a,s)
                                 (fn a=>(if c then if a then T else t
                                              else if a then negate t else F,
                                         s))
                                 (fn(a,s)=>(if c then mk_disj(t,a)
                                                 else mk_conj(negate t,a),s)))
                         (fn(c,s)=> lit (a,s)
                                    (fn a=>((if a then mk_imp else mk_conj)(t,c),s))
                                    (fn(a,s)=>(mk_cond(t,c,a),s))))
    end

    (* Compute the terms for each existential variable
       and add (e = tm) hypotheses onto the matrix.
       Fill in the rest of the vars map.
       Fill in the deps map by adding each extension variable
       to the list belonging to each variable appearing in its definition term. *)
    fun foldthis (i,ext) (t,vars,deps) = let
      val v = index_to_var i
      val (tm,ds) = extension_to_term ext
      val vars = Inttab.update (i, Ext(v,tm)) vars
      val h = mk_eq(v,tm)
      fun foldthis (n,d) =
          Inttab.update
            (n, case Inttab.lookup d n of
                    NONE => [i]
                  | SOME ls => i :: ls) d
      val deps = HOLset.foldl foldthis deps ds
    in (mk_imp(h,t),vars,deps) end
    val (mat,vars,deps) = Inttab.fold foldthis exts (mat,vars,deps)

    val thm = (!sat_prove) mat

    val deps = Lib.dict_topsort deps
    val deps = List.rev deps
    (* now deps is the list of variable indexes in the order
       they should be eliminated (quantified and have hypothesis discharged) *)

    fun foldthis (i,th) = case valOf (Inttab.lookup vars i) of
      Forall v => (fn() => GEN v th) ()
    | Exists (v,w) => (fn () => let
        val th = EXISTS (mk_exists(v,concl th),v) th
        val ex = EXISTS (mk_exists(v,mk_eq(v,w)),w) (REFL w)
        val th = CHOOSE (v,ex) th
      in th end ) ()
    | Ext (v,w) => (fn () => let
        val ex = EXISTS (mk_exists(v,mk_eq(v,w)),w) (REFL w)
        val th = CHOOSE (v,ex) th
      in th end ) ()
    val thm = DISCH_ALL (List.foldl foldthis (UNDISCH_ALL thm) deps)

      (* sanity checks *)
      val _ = if !QbfTrace.trace < 1 orelse HOLset.isEmpty (Thm.hypset thm) then
          ()
        else
          Feedback.HOL_WARNING "QbfCertificate" "check" "final theorem has hyps"
      val _ = if !QbfTrace.trace < 1 orelse Term.aconv (Thm.concl thm) t then
          ()
        else
          Feedback.HOL_WARNING "QbfCertificate" "check"
            "final theorem proves a different term"
    in
      thm
    end
(* ------------------------------------------------------------------------- *)
    | check t _ (INVALID (dict, cindex)) =
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
        Termtab.update (var, (i, is_forall)) var_dict)
        Termtab.empty vars
      fun index_fn var =
        valOf (Termtab.lookup var_dict var)

      val vars = List.rev vars
      fun foldthis (clause, (i, clause_dict)) =
        let
          val clause = QbfLibrary.CLAUSE_TO_SEQUENT clause
          val lits = QbfLibrary.literals_in_clause index_fn clause
        in
          (i + 1, Inttab.update (i,
            QbfLibrary.forall_reduce (clause, vars, matrix, lits)) clause_dict)
        end

      (* a dictionary that maps each clause identifier to a 4-tuple, which
         consists of 1. the clause theorem (in sequent form, cf.
         'QbfLibrary.CLAUSE_TO_SEQUENT'), 2. the list of missing variables (cf.
         'QbfLibrary.enumerate_quantified_vars', 3. the hypothesis (initially,
         this is 'matrix'), and 4. the list of literals in the clause (cf.
         'QbfLibrary.literals_in_clause' *)
      val clause_dict = Lib.snd (List.foldl foldthis
        (1, Inttab.empty)
        (Drule.CONJUNCTS (Thm.ASSUME matrix)))

      (* depth-first recursion over the certificate (which represents a DAG),
         using QRESOLVE_CLAUSES to derive new clauses from existing ones *)
      fun derive (c_dict, index) =
        case Inttab.lookup c_dict index of
          SOME clause =>
          (c_dict, clause)
        | NONE =>
          let
            val (_, indices) =
                case Inttab.lookup dict index of
                    SOME r => r
                  | NONE => raise ERR "check"
                              ("invalid certificate: no definition for clause ID "
                               ^ Int.toString index)
            val _ = if List.null indices then
                raise ERR "check"
                  ("invalid certificate: empty definition for clause ID " ^
                     Int.toString index)
              else ()
            val (c_dict, clauses) = Lib.foldl_map derive (c_dict, indices)
            val clause = List.foldl (QbfLibrary.QRESOLVE_CLAUSES)
              (List.hd clauses) (List.tl clauses)
          in
            (Inttab.update (index, clause) c_dict, clause)
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
      val _ = if !QbfTrace.trace < 1 orelse
        Term.aconv (Thm.concl thm) boolSyntax.F then
          ()
        else
          Feedback.HOL_WARNING "QbfCertificate" "check" "final theorem not F"
    in
      thm
    end
end
