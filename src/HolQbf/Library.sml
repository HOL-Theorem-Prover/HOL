(* Copyright (c) 2010 Tjark Weber. All rights reserved. *)

(* Common auxiliary functions. *)

structure Library =
struct

  val ERR = Feedback.mk_HOL_ERR "Library"

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
(* merge: merges two lists of tuples whose first components are integers     *)
(*      sorted wrt. absolute value into a single list sorted wrt. absolute   *)
(*      value; drops duplicates that occur in both lists                     *)
(* ------------------------------------------------------------------------- *)

  fun merge xs [] = xs
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
(* neg_literals_in_clause: takes a clause 't' (i.e., a disjunction of        *)
(*      literals, where a literal is a possibly negated variable) and a      *)
(*      function 'index_fn' that maps variables to a positive integer index  *)
(*      and a Boolean q; returns a list of triples (~ index, neg_literal, q) *)
(*      (using integer negation for propositional negation) sorted by        *)
(*      absolute value                                                       *)
(* ------------------------------------------------------------------------- *)

  fun neg_literals_in_clause index_fn t =
  let
    fun aux t =
    let
      val (p, q) = boolSyntax.dest_disj t
    in
      merge (aux p) (aux q)
    end
    handle Feedback.HOL_ERR _ =>  (* 't' is not a disjunction *)
      let
        val var = boolSyntax.dest_neg t
        val (index, q) = index_fn var
      in
        [(index, var, q)]
      end
    handle Feedback.HOL_ERR _ =>  (* 't' is not a negation *)
      let
        val (index, q) = index_fn t
      in
        [(~ index, boolSyntax.mk_neg t, q)]
      end
  in
    aux t
  end

(* ------------------------------------------------------------------------- *)
(* discharge_lit: discharges a literal 'lit' from a theorem 'thm' by         *)
(*      instantiating its variable to (either) "T" or "F".                   *)
(* ------------------------------------------------------------------------- *)

local
  val NOT_FALSE = bossLib.DECIDE ``~F``
in
  fun discharge_lit thm lit =
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
            ((*Profile.profile "discharge_lit"*) (discharge_lit thm) lit,
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
(*        A |- x1 /\ ... /\ xn                                               *)
(* ---------------------------------- QBF_CONJUNCTS vars                     *)
(* i |-> (A_i |- x_i, vars_i, lits_i)                                        *)
(*                                                                           *)
(* Flattens a conjunctive conclusion (similar to Drule.CONJUNCTS). In        *)
(* addition, 'vars' must be a list of triples (as returned by                *)
(* 'enumerate_quantified_vars'), each of the form (index, var, is_forall),   *)
(* with innermost variables coming first.  The resulting theorems have these *)
(* variables bound in A_i (by the correct quantifier) if they do not contain *)
(* any variable in their conclusion x_i that is (more) inner.                *)
(*                                                                           *)
(* Moreover, each resulting theorem is accompanied by a list of negated      *)
(* literals that occur in its conclusion (cf. neg_literals_in_clause).       *)
(*                                                                           *)
(* The resulting theorems are stored in a dictionary, indexed by positive    *)
(* clause identifiers.                                                       *)
(*                                                                           *)
(* TODO: fix this comment                                                    *)
(* ------------------------------------------------------------------------- *)

  fun QBF_CONJUNCTS qbf =
  let
    val (_, vars, body) = enumerate_quantified_vars qbf
    val vars = List.rev vars
    val var_dict = List.foldl (fn ((i, var, is_forall), dict) =>
      Redblackmap.insert (dict, var, (i, is_forall)))
      (Redblackmap.mkDict Term.var_compare) vars
    fun index_fn var =
      Redblackmap.find (var_dict, var)

    val clauses = boolSyntax.strip_conj body
    (* number the clauses, compute their (negated) literals *)
    fun foldl_map_this (id, clause) =
      (id + 1, (id, clause, neg_literals_in_clause index_fn clause))
    val clauses = Lib.snd (Lib.foldl_map foldl_map_this (1, clauses))

    val thm = Thm.ASSUME body

(*
    (* sort the clauses wrt. the index of their innermost variable *)
    fun compare ((id1, _, lits1), (id2, _, lits2)) =
      let
        val idx1 = Int.abs (#1 (List.hd lits1))
        val idx2 = Int.abs (#1 (List.hd lits2))
      in
        case Int.compare (idx1, idx2) of
          EQUAL => Int.compare (id1, id2)
        | ord => ord
      end
    val clauses = Redblackset.listItems (Redblackset.addList
      (Redblackset.empty compare, clauses))
    val new_body = boolSyntax.list_mk_conj (List.map #2 clauses)
    (* sort the conclusion of 'thm' accordingly *)
    val thm = Thm.EQ_MP (Drule.CONJUNCTS_AC (body, new_body)) thm
*)

    fun aux th [(id, _, lits)] hyp vars dict =
      Redblackmap.insert (dict, id, (th, vars, hyp, lits))
      | aux th (hd::tl) hyp vars dict =
      let
        val dict = aux (Thm.CONJUNCT1 th) [hd] hyp vars dict
        val th = Thm.CONJUNCT2 th
      in
        aux th tl hyp vars dict
      end
      | aux _ [] _ _ _ =
      raise Match
  in
    aux thm clauses body vars (Redblackmap.mkDict Int.compare)
  end

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
(* A, p |- F   B, ~p |- F                                                    *)
(* ---------------------- QRESOLVE_CLAUSES                                   *)
(*       A, B |- F                                                           *)
(*                                                                           *)
(* Fails if there is no pivot variable that occurs positively in one premise *)
(* and negatively in the other.                                              *)
(*                                                                           *)
(* Also removes definitions and literals whose variable does not occur from  *)
(* the resulting clause (cf. remove_defs_and_lits).                          *)
(*                                                                           *)
(* TODO: fix this comment                                                    *)
(* ------------------------------------------------------------------------- *)

  val QRESOLVE_counter = ref 0

  fun QRESOLVE_CLAUSES ((th1, vars1, hyp1, lits1),
                        (th2, vars2, hyp2, lits2)) =
  let
    val _ = QRESOLVE_counter := !QRESOLVE_counter + 1

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
