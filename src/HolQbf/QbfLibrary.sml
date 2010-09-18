(* Copyright (c) 2010 Tjark Weber. All rights reserved. *)

(* Common auxiliary functions. *)

structure QbfLibrary =
struct

  val ERR = Feedback.mk_HOL_ERR "QbfLibrary"

(* ------------------------------------------------------------------------- *)
(* write_strings_to_file: opens 'path' as an output text file; writes all    *)
(*      elements of 'strings' to this file (in the order given); closes the  *)
(*      file                                                                 *)
(* ------------------------------------------------------------------------- *)

  fun write_strings_to_file path strings =
  let
    val outstream = TextIO.openOut path
  in
    List.app (TextIO.output o Lib.pair outstream) strings;
    TextIO.closeOut outstream
  end

(* ------------------------------------------------------------------------- *)
(* read_lines_from_file: opens 'path' as an input text file; reads all lines *)
(*      of this file (using TextIO.inputLine); closes the file before        *)
(*      returning the lines read (as a list of strings, each terminated by   *)
(*      "\n")                                                                *)
(* ------------------------------------------------------------------------- *)

  fun read_lines_from_file path =
  let
    val instream = TextIO.openIn path
    fun input acc =
      case TextIO.inputLine instream of
        SOME line =>
          input (line :: acc)
      | NONE =>
          List.rev acc
  in
    input [] before TextIO.closeIn instream
  end

(* ------------------------------------------------------------------------- *)
(* enumerate_quantified_vars: takes a term 't' of the form                   *)
(*      "Qn xn. ... Q1 x1. phi" (where n>=0, and each Qi is either ? or !),  *)
(*      and returns (n+1, [(n, xn, qn), ..., (1, x1, q1)], phi), where qi is *)
(*      true if Qi is !, and false if Qi is ?.                               *)
(* ------------------------------------------------------------------------- *)

  fun enumerate_quantified_vars t =
  let
    val ((var, body), is_forall) = (boolSyntax.dest_forall t, true)
      handle Feedback.HOL_ERR _ =>  (* 't' is not universally quantified *)
        (boolSyntax.dest_exists t, false)
    val (next_index, vars, body) = enumerate_quantified_vars body
  in
    (next_index + 1, (next_index, var, is_forall) :: vars, body)
  end
  handle Feedback.HOL_ERR _ =>  (* 't' is not quantified *)
    (1, [], t)

(* ------------------------------------------------------------------------- *)
(* A |- p1 \/ ... \/ pn                                                      *)
(* --------------------- CLAUSE_TO_SEQUENT                                   *)
(* A, ~p1, ..., ~pn |- F                                                     *)
(* ------------------------------------------------------------------------- *)

  fun CLAUSE_TO_SEQUENT thm =
  let
    val concl = Thm.concl thm
  in
    let
      val (p, q) = boolSyntax.dest_disj concl
    in
      Thm.DISJ_CASES thm
        (CLAUSE_TO_SEQUENT (Thm.ASSUME p)) (CLAUSE_TO_SEQUENT (Thm.ASSUME q))
    end
    handle Feedback.HOL_ERR _ =>  (* 'concl' is not a disjunction *)
      if concl = boolSyntax.F then
        thm
      else (
        Thm.MP (Thm.NOT_ELIM thm) (Thm.ASSUME (boolSyntax.dest_neg concl))
        handle Feedback.HOL_ERR _ =>  (* 'concl' is not a negation *)
          Thm.MP (Thm.NOT_ELIM (Thm.ASSUME (boolSyntax.mk_neg concl))) thm
      )
  end

(* ------------------------------------------------------------------------- *)
(* literals_in_clause: takes a function 'index_fn' that maps variables to a  *)
(*      pair consisting of a positive integer i and a Boolean q, and a       *)
(*      clause theorem 'thm' in sequent form, as produced by                 *)
(*      'CLAUSE_TO_SEQUENT'. Returns a list of triples ([~]i, [~]var, q),    *)
(*      with one element for every hypothesis of 'thm' that is a literal     *)
(*      (i.e., a possibly negated variable).  The list is sorted with        *)
(*      respect to the absolute value of its elements first component, [~]i. *)
(* ------------------------------------------------------------------------- *)

  fun literals_in_clause index_fn thm =
  let
    val set = HOLset.foldl (fn (t, set) =>
      let
        val (i, q) = index_fn (boolSyntax.dest_neg t)
      in
        HOLset.add (set, (~ i, t, q))
      end
      handle Feedback.HOL_ERR _ =>  (* 't' is not a negation *)
      let
        val (i, q) = index_fn t
      in
        HOLset.add (set, (i, t, q))
      end
      handle Feedback.HOL_ERR _ =>  (* 't' is not a variable *)
        set) (HOLset.empty (Int.compare o Lib.## (Int.abs o #1, Int.abs o #1)))
        (Thm.hypset thm)
  in
    HOLset.listItems set
  end

(* ------------------------------------------------------------------------- *)
(* discharge_lit: discharges a possibly negated variable (i.e., a literal)   *)
(*      from a theorem 'thm' by instantiating it to (either) "T" or "F".     *)
(*                                                                           *)
(*    A, v |- t                                                              *)
(* ---------------- discharge_lit v                                          *)
(* A[T/v] |- t[T/v]                                                          *)
(*                                                                           *)
(*    A, ~v |- t                                                             *)
(* ---------------- discharge_lit ~v                                         *)
(* A[F/v] |- t[F/v]                                                          *)
(* ------------------------------------------------------------------------- *)

local
  val NOT_FALSE = bossLib.DECIDE ``~F``
in
  fun discharge_lit lit thm =
  let
    val var = boolSyntax.dest_neg lit
  in
    Thm.MP (Thm.INST [{redex = var, residue = boolSyntax.F}]
      (Thm.DISCH lit thm)) NOT_FALSE
  end
  handle Feedback.HOL_ERR _ =>  (* 'lit' is not negated *)
    Thm.MP (Thm.INST [{redex = lit, residue = boolSyntax.T}]
      (Thm.DISCH lit thm)) boolTheory.TRUTH
end

(* ------------------------------------------------------------------------- *)
(*    A, hyp |- t                                                            *)
(* ----------------- bind_var hyp var true                                   *)
(* A, !var. hyp |- t                                                         *)
(*                                                                           *)
(*    A, hyp |- t                                                            *)
(* ----------------- bind_var hyp var false  (var not free in A or t)        *)
(* A, ?var. hyp |- t                                                         *)
(* ------------------------------------------------------------------------- *)

  fun bind_var thm hyp var is_forall =
    if is_forall then (*Profile.profile "bind_var(forall)"*) (fn () =>
      let
        val hyp' = boolSyntax.mk_forall (var, hyp)
        val thm = Thm.MP (Thm.DISCH hyp thm) (Thm.SPEC var (Thm.ASSUME hyp'))
      in
        (thm, hyp')
      end) ()
    else (*Profile.profile "bind_var(exists)"*) (fn () =>
      (* 'var' must not be free in the hypotheses of 'thm' (except in 'hyp') *)
      let
        val hyp' = boolSyntax.mk_exists (var, hyp)
        val thm = Thm.CHOOSE (var, Thm.ASSUME hyp') thm
      in
        (thm, hyp')
      end) ()

(* ------------------------------------------------------------------------- *)
(* Implements forall-reduction.  Takes a clause in sequent form, a list of   *)
(*      variables to be introduced eventually, the partial QBF (which should *)
(*      be a hypothesis of the clause) that is missing these variables, and  *)
(*      the list of literals present in the clause.  Both lists must be      *)
(*      ordered, with variables that are in the scope of other variables     *)
(*      coming first.                                                        *)
(* ------------------------------------------------------------------------- *)

  fun forall_reduce (thm, [], hyp, []) =
    (thm, [], hyp, [])
    | forall_reduce (thm, (_, var, is_forall) :: vars, hyp, []) =
    let
      val (thm, hyp) = bind_var thm hyp var is_forall
    in
      forall_reduce (thm, vars, hyp, [])
    end
    | forall_reduce (thm, vars as (i, var, v_is_forall) :: vartail, hyp,
                          lits as (j, lit, l_is_forall) :: littail) =

    if v_is_forall then
      let
        val (thm, hyp) = bind_var thm hyp var v_is_forall
        (* discharge the variable if it occurs *)
        val (thm, lits') = if i < Int.abs j then
            (thm, lits)
          else  (* i = Int.abs j *)
            ((*Profile.profile "discharge_lit"*) (discharge_lit lit) thm,
              littail)
      in
        forall_reduce (thm, vartail, hyp, lits')
      end
    else if l_is_forall then
      (* late binding of existentials: only when the innermost literal is
         universal *)
      let
        val (thm, hyp) = bind_var thm hyp var v_is_forall
      in
        forall_reduce (thm, vartail, hyp, lits)
      end
    else
      (thm, vars, hyp, lits)
    | forall_reduce (_, [], _, _ :: _) =
    raise Match

(* ------------------------------------------------------------------------- *)
(* merge: merges two lists of tuples whose first components are integers     *)
(*      sorted wrt. absolute value into a single list sorted wrt. absolute   *)
(*      value; drops duplicates that occur in both lists                     *)
(* ------------------------------------------------------------------------- *)

  fun merge xs [] : (int * 'a * 'b) list = xs
    | merge [] ys = ys
    | merge (xs as xhd :: xtails) (ys as yhd :: ytails) =
    let
      val absx = Int.abs (#1 xhd)
      val absy = Int.abs (#1 yhd)
    in
      if absx = absy then
        (* drop 'yhd' *)
        xhd :: merge xtails ytails
      else if absx < absy then
        xhd :: merge xtails ys
      else
        yhd :: merge xs ytails
    end

(* ------------------------------------------------------------------------- *)
(* QRESOLVE_CLAUSES: performs propositional resolution of clauses in sequent *)
(*      form, followed by forall-reduction.                                  *)
(* ------------------------------------------------------------------------- *)

  fun QRESOLVE_CLAUSES ((th1, vars1, hyp1, lits1),
                        (th2, vars2, hyp2, lits2)) =
  let
    (* returns the resulting set of literals, along with the pivot as it occurs
       in lits1 and lits2, respectively; cf. merge *)
    fun find_pivot acc [] _ =
      raise ERR "QRESOLVE_CLAUSES" "no pivot literal"
      | find_pivot acc _ [] =
      raise ERR "QRESOLVE_CLAUSES" "no pivot literal"
      | find_pivot acc (lits1 as (hd1 as (i, l1, _)) :: tail1)
                       (lits2 as (hd2 as (j, l2, _)) :: tail2) =
      if i = ~j then
        (List.rev acc @ merge tail1 tail2, l1, l2, i > 0)
      else if i = j then
        find_pivot (hd1 :: acc) tail1 tail2
      else if Int.abs i < Int.abs j then
        find_pivot (hd1 :: acc) tail1 lits2
      else  (* Int.abs j < Int.abs i *)
        find_pivot (hd2 :: acc) lits1 tail2
    val (lits, p, p', p_is_pos) = find_pivot [] lits1 lits2

    (* resolution *)
    val th = (*Profile.profile "resolve"*) (fn () =>
      let
        val th1 = Thm.DISCH p th1
        val th2 = Thm.DISCH p' th2
      in
        if p_is_pos then
          Thm.MP th2 (Thm.NOT_INTRO th1)
        else
          Thm.MP th1 (Thm.NOT_INTRO th2)
      end) ()

    (* since variables are always bound innermost first, we simply
       return the larger set -- no need to actually merge *)
    fun merge_vars (vars1, hyp1) ([], _) = (vars1, hyp1)
      | merge_vars ([], _) (vars2, hyp2) = (vars2, hyp2)
      | merge_vars (vars1, hyp1) (vars2, hyp2) =
      if #1 (List.hd vars1) < #1 (List.hd vars2) then
        (vars1, hyp1)
      else
        (vars2, hyp2)
    val (vars, hyp) = merge_vars (vars1, hyp1) (vars2, hyp2)
  in
    forall_reduce (th, vars, hyp, lits)
  end

end
