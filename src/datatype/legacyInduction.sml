structure legacyInduction :> legacyInduction =
struct

open HolKernel boolLib

val ERR = mk_HOL_ERR "legacyInduction"

type operator = {induction : thm, sets : thm list}

(* ----------------------------------------------------------------------
    Reading the package's principle.
   ---------------------------------------------------------------------- *)

(* a clause's hypothesis about an operator's contents: `∀z. z ∈ set l ⇒
   P z`.  What is wanted is the bound variable, the set it is about and
   the value that set is of. *)
fun nestedHyp Pv tm =
    let
      val (z, body) = dest_forall tm
      val (ante, conc) = dest_imp body
      val (elem, set) = pred_setSyntax.dest_in ante
    in
      if aconv conc (mk_comb (Pv, z)) andalso aconv elem z then
        SOME {z = z, set = set, arg = rand set}
      else NONE
    end handle HOL_ERR _ => NONE

(* A clause need not say everything at the front: `∀t. Q t ⇒ ∀h. Q (h::t)`
   binds an argument after its hypothesis.  These take such a clause
   apart into all of its variables and all of its hypotheses, and put a
   proof of its conclusion back together in its own shape. *)
fun openAll tm =
    if is_forall tm then
      let val (v, b) = dest_forall tm
          val (vs, hs, c) = openAll b
      in (v :: vs, hs, c) end
    else
      case Lib.total dest_imp tm of
          SOME (a, c) => let val (vs, hs, cc) = openAll c
                         in (vs, strip_conj a @ hs, cc) end
        | NONE => ([], [], tm)

fun closeAs tm th =
    if is_forall tm then
      let val (v, b) = dest_forall tm in GEN v (closeAs b th) end
    else
      case Lib.total dest_imp tm of
          SOME (a, c) => DISCH a (closeAs c th)
        | NONE => th

fun hypsOf c =
    case Lib.total dest_imp (#2 (strip_forall c)) of
        NONE => []
      | SOME (ante, _) => strip_conj ante

fun nestedOf Pv c = List.mapPartial (nestedHyp Pv) (hypsOf c)

(* ----------------------------------------------------------------------
    What an operator's induction says, at the predicate this proof wants.
   ---------------------------------------------------------------------- *)

(* the operator's induction at the type the principle mentions *)
fun atType opty (ind : thm) =
    let val (Q, body) = dest_forall (concl ind)
        val (_, conc) = dest_imp body
        val (l, _) = dest_forall conc
    in
      INST_TYPE (match_type (type_of l) opty) ind
    end

(* a clause of the operator's induction, with the type's own predicate
   added at the arguments the type is at: `∀h t. Q t ⇒ Q (h::t)` becomes
   `∀h t. P h ∧ Q t ⇒ Q (h::t)` *)
fun strengthen (Pv, ty) clause =
    let
      val (args, hyps, conc) = openAll clause
      val extra = List.map (fn a => mk_comb (Pv, a))
                           (List.filter (fn a => type_of a = ty) args)
      val hyps = extra @ hyps
    in
      list_mk_forall (args,
                      case hyps of
                          [] => conc
                        | _ => mk_imp (list_mk_conj hyps, conc))
    end

(* ----------------------------------------------------------------------
    What a value's set says about its parts.

    A set equation writes a constructor's contents as a union of what
    each argument contributes: the argument itself where the type is at,
    the argument's own set where the operator is.  So a hypothesis about
    the whole says one thing about each part, and this reads them off.
   ---------------------------------------------------------------------- *)

fun inThm z S = pred_setSyntax.mk_in (z, S)

(* ⊢ ∀z. z ∈ X ⇒ P z, for X a part of the set the hypothesis is about *)
fun narrow th (z, whole, part, mk) =
    let val zin = ASSUME (inThm z part)
        val eq = PART_MATCH lhs mk (inThm z whole)
    in
      GEN z (DISCH (inThm z part) (MP (SPEC z th) (EQ_MP (SYM eq) zin)))
    end

fun contents th =
    let
      val (z, body) = dest_forall (concl th)
      val (ante, _) = dest_imp body
      val whole = rand ante
      fun union (A, B) =
          let
            val eq = PART_MATCH lhs pred_setTheory.IN_UNION (inThm z whole)
            fun side (S, d) =
                GEN z (DISCH (inThm z S)
                             (MP (SPEC z th) (EQ_MP (SYM eq) d)))
            val l = side (A, DISJ1 (ASSUME (inThm z A)) (inThm z B))
            val r = side (B, DISJ2 (inThm z A) (ASSUME (inThm z B)))
          in
            contents l @ contents r
          end
      fun insert (a, S) =
          let
            val eq = PART_MATCH lhs pred_setTheory.IN_INSERT (inThm z whole)
            val ain = EQ_MP (SYM (INST [z |-> a] eq))
                            (DISJ1 (REFL a) (inThm a S))
            val here = MP (SPEC a th) ain
            val rest =
                GEN z (DISCH (inThm z S)
                             (MP (SPEC z th)
                                 (EQ_MP (SYM eq)
                                        (DISJ2 (mk_eq (z, a))
                                               (ASSUME (inThm z S))))))
          in
            here :: contents rest
          end
    in
      case Lib.total pred_setSyntax.dest_union whole of
          SOME p => union p
        | NONE =>
          case Lib.total pred_setSyntax.dest_insert whole of
              SOME p => insert p
            | NONE => if pred_setSyntax.is_empty whole then [] else [th]
    end

(* ----------------------------------------------------------------------
    The principle itself.
   ---------------------------------------------------------------------- *)

(* the hypotheses of a clause, and its conclusion, where the clause may
   have none *)
fun openClause c =
    let val (vs, body) = strip_forall c
    in
      case Lib.total dest_imp body of
          NONE => (vs, [], body)
        | SOME (a, conc) => (vs, strip_conj a, conc)
    end

fun assemble (ops : operator list) ind =
    let
      val (Pv, body) = dest_forall (concl ind)
      val (hypsTm, _) = dest_imp body
      val ty = #1 (dom_rng (type_of Pv))
      val clauses = strip_conj hypsTm
      val nested = List.concat (List.map (nestedOf Pv) clauses)
      val _ = not (null nested) orelse
              raise ERR "mutual_induction"
                    "the principle recurses under no operator"
      (* the operators, in the order the principle's clauses first
         mention them, which is the order that names the predicates *)
      fun firstOccs [] = []
        | firstOccs (t :: ts) =
            t :: firstOccs (List.filter (not o equal t) ts)
      val optys = firstOccs (List.map (type_of o #arg) nested)
      (* the caller's operator for a type: the one whose induction is
         about it *)
      fun opFor opty =
          case List.find (fn r => Lib.can (atType opty) (#induction r)) ops of
              SOME r => r
            | NONE => raise ERR "mutual_induction"
                            ("no induction principle offered for " ^
                             type_to_string opty)
      (* and its set function, which the principle itself says *)
      fun setFor opty =
          case List.find (fn r => type_of (#arg r) = opty) nested of
              SOME r => rator (#set r)
            | NONE => raise ERR "mutual_induction" "no set function"
      val Qs = List.tabulate
                 (length optys,
                  fn i => mk_var ("Q" ^ Int.toString i,
                                  List.nth (optys, i) --> bool))
      fun Qfor opty =
          case List.find (fn (t, _) => t = opty) (ListPair.zip (optys, Qs)) of
              SOME (_, q) => q
            | NONE => raise ERR "mutual_induction" "no predicate"
      (* what a clause says once the operator has a predicate of its own *)
      fun swap h =
          case nestedHyp Pv h of
              NONE => h
            | SOME {arg, ...} => mk_comb (Qfor (type_of arg), arg)
      fun newClause c =
          let val (vs, hyps, conc) = openClause c
          in
            case hyps of
                [] => c
              | _ => list_mk_forall (vs, mk_imp (list_mk_conj
                                                   (List.map swap hyps),
                                                 conc))
          end
      val newClauses = List.map newClause clauses
      (* the operator's own clauses, with the type's predicate where the
         type is *)
      fun opClausesFor opty =
          let val oi = atType opty (#induction (opFor opty))
              val (Q, obody) = dest_forall (concl oi)
              val (oante, _) = dest_imp obody
          in
            List.map (fn c => strengthen (Pv, ty)
                                         (Term.subst [Q |-> Qfor opty] c))
                     (strip_conj oante)
          end
      val opClauses = List.concat (List.map opClausesFor optys)
      val hypterm = list_mk_conj (newClauses @ opClauses)
      val x = mk_var ("x", ty)
      val conclusion =
          list_mk_conj
            (mk_forall (x, mk_comb (Pv, x)) ::
             List.map (fn q =>
                          let val v = mk_var ("l", #1 (dom_rng (type_of q)))
                          in mk_forall (v, mk_comb (q, v)) end)
                      Qs)
      val goal = list_mk_forall (Pv :: Qs, mk_imp (hypterm, conclusion))
    in
      {goal = goal, Pv = Pv, Qs = Qs, ty = ty, optys = optys,
       clauses = clauses, newClauses = newClauses, hypterm = hypterm,
       opFor = opFor, setFor = setFor, Qfor = Qfor,
       opClausesFor = opClausesFor, nested = nested}
    end

fun mutual_induction_goal ops ind = #goal (assemble ops ind)

(* the membership hypothesis a clause of the operator's induction ends
   with, and the induction hypotheses before it *)
fun splitBridge Pv tm =
    case Lib.total dest_imp tm of
        NONE => raise ERR "mutual_induction" "a clause with no membership"
      | SOME (a, c) =>
        if isSome (nestedHyp Pv a) then ([], a, c)
        else let val (ihs, m, cc) = splitBridge Pv c
             in (strip_conj a @ ihs, m, cc) end

fun mutual_induction ops ind =
    let
      val info = assemble ops ind
      val Pv = #Pv info and ty = #ty info
      val A = ASSUME (#hypterm info)
      val parts = CONJUNCTS A
      val newParts = List.take (parts, length (#newClauses info))
      (* the operators' own clauses, in the order the statement has them *)
      val (opParts, _) =
          List.foldl (fn (opty, (acc, rest)) =>
                         let val k = length (#opClausesFor info opty)
                         in (acc @ [(opty, List.take (rest, k))],
                             List.drop (rest, k)) end)
                     ([], List.drop (parts, length (#newClauses info)))
                     (#optys info)
      fun opPartsFor opty =
          case List.find (fn (t, _) => t = opty) opParts of
              SOME (_, ps) => ps
            | NONE => raise ERR "mutual_induction" "no clauses"
      fun close vs hyps th =
          GENL vs (case hyps of [] => th | _ => DISCH (list_mk_conj hyps) th)
      (* ------------------------------------------------------------
          what the operator's predicate says of a value, from what the
          type's says of its contents
         ------------------------------------------------------------ *)
      fun bridgeFor opty =
          let
            val Sf = #setFor info opty and Q = #Qfor info opty
            val l = mk_var ("l", opty) and z = mk_var ("z", ty)
            fun memOf t = mk_forall (z, mk_imp (inThm z (mk_comb (Sf, t)),
                                                mk_comb (Pv, z)))
            val Q0 = mk_abs (l, mk_imp (memOf l, mk_comb (Q, l)))
            val inst = CONV_RULE (DEPTH_CONV BETA_CONV)
                                 (SPEC Q0 (atType opty
                                             (#induction (#opFor info opty))))
            val goals = strip_conj (#1 (dest_imp (concl inst)))
            val setEqs = #sets (#opFor info opty)
            fun prove (g, ass) =
                let
                  val (vs, hs, conc) = openAll g
                  val (ihs, memTm) =
                      (List.filter (fn h => not (isSome (nestedHyp Pv h))) hs,
                       case List.filter (isSome o nestedHyp Pv) hs of
                           m :: _ => m
                         | [] => raise ERR "mutual_induction"
                                       "a clause with no membership")
                  val cTerm = rand conc
                  val eq =
                      case List.mapPartial
                             (fn e => Lib.total (PART_MATCH lhs e)
                                                (mk_comb (Sf, cTerm)))
                             setEqs of
                          e :: _ => e
                        | [] => raise ERR "mutual_induction"
                                      ("no set equation for " ^
                                       term_to_string (mk_comb (Sf, cTerm)))
                  val memAss =
                      CONV_RULE (STRIP_QUANT_CONV
                                   (LAND_CONV (RAND_CONV (K eq))))
                                (ASSUME memTm)
                  val facts = contents memAss
                  fun factFor t =
                      case List.find (fn th => aconv (concl th) t) facts of
                          SOME th => th
                        | NONE => raise ERR "mutual_induction"
                                        ("the set says nothing of " ^
                                         term_to_string t)
                  (* an induction hypothesis wants what the set says of
                     its own argument *)
                  val gots =
                      List.map (fn ih =>
                                   let val (m, _) = dest_imp ih
                                   in MP (ASSUME ih) (factFor m) end)
                               ihs
                  val (avs, ahyps, _) = openClause (concl ass)
                  val theta = ListPair.map (fn (a, v) => a |-> v) (avs, vs)
                  val wanted = List.map (Term.subst theta) ahyps
                  fun supply w =
                      case List.find (fn th => aconv (concl th) w)
                                     (facts @ gots) of
                          SOME th => th
                        | NONE => raise ERR "mutual_induction"
                                        ("nothing gives " ^
                                         term_to_string w)
                  val res = case wanted of
                                [] => SPECL vs ass
                              | _ => MP (SPECL vs ass)
                                        (LIST_CONJ (List.map supply wanted))
                in
                  closeAs g res
                end
            val proved = ListPair.map prove (goals, opPartsFor opty)
          in
            CONV_RULE (STRIP_QUANT_CONV (QCONV (DEPTH_CONV BETA_CONV)))
                      (MP inst (LIST_CONJ proved))
          end
      val bridges = List.map (fn opty => (opty, bridgeFor opty)) (#optys info)
      fun bridgeOf opty =
          case List.find (fn (t, _) => t = opty) bridges of
              SOME (_, th) => th
            | NONE => raise ERR "mutual_induction" "no bridge"
      (* ------------------------------------------------------------
          and so the principle's own clauses, and everything of the type
         ------------------------------------------------------------ *)
      fun clauseFor (c, newPart) =
          let
            val (vs, hyps, _) = openClause c
            fun supply h =
                case nestedHyp Pv h of
                    NONE => ASSUME h
                  | SOME {arg, ...} =>
                    MP (SPEC arg (bridgeOf (type_of arg))) (ASSUME h)
            val res = case hyps of
                          [] => SPECL vs newPart
                        | _ => MP (SPECL vs newPart)
                                  (LIST_CONJ (List.map supply hyps))
          in
            close vs hyps res
          end
      val allX = MP (SPEC Pv ind)
                    (LIST_CONJ (ListPair.map clauseFor
                                             (#clauses info, newParts)))
      (* and everything of the operators', now that the type is settled *)
      fun allQfor opty =
          let
            val inst = SPEC (#Qfor info opty)
                            (atType opty (#induction (#opFor info opty)))
            val goals = strip_conj (#1 (dest_imp (concl inst)))
            fun prove (g, ass) =
                let
                  val (vs, hyps, _) = openAll g
                  val extras = List.map (fn v => SPEC v allX)
                                        (List.filter (fn v => type_of v = ty)
                                                     vs)
                  val given = extras @ List.map ASSUME hyps
                  val res = case given of
                                [] => SPECL vs ass
                              | _ => MP (SPECL vs ass) (LIST_CONJ given)
                in
                  closeAs g res
                end
          in
            MP inst (LIST_CONJ (ListPair.map prove (goals, opPartsFor opty)))
          end
    in
      GENL (Pv :: #Qs info)
           (DISCH (#hypterm info)
                  (LIST_CONJ (allX :: List.map allQfor (#optys info))))
    end

end
