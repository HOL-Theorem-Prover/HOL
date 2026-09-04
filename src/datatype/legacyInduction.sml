structure legacyInduction :> legacyInduction =
struct

open HolKernel boolLib

val ERR = mk_HOL_ERR "legacyInduction"

type operator = {induction : thm, sets : thm list}

(* ----------------------------------------------------------------------
    Reading the package's principle.
   ---------------------------------------------------------------------- *)

(* One step of the walk a hypothesis makes to reach an operator's
   contents: the value the step is about, and the set that collects the
   next step's values out of it. *)
type level = {arg : term, set : term}

(* A clause's hypothesis about an operator's contents reaches them
   through as many operators as the argument's type has:

     ∀z. z ∈ set l ⇒ P z
     ∀z. (∃x y. z ∈ s x ∧ x ∈ t y ∧ y ∈ u l) ⇒ P z

   walk one and three of them.  This reads such a hypothesis as the
   chain of levels it walks, outermost first — so the first level is
   about the clause's own argument, and the last collects values of the
   type the principle is about. *)
fun chainOf Pv tm =
    let
      val (z, body) = dest_forall tm
      val (ante, conc) = dest_imp body
      val _ = aconv conc (mk_comb (Pv, z)) orelse
              raise ERR "chainOf" "not a hypothesis about the bound variable"
      val (evs, conjs) = strip_exists ante
      val mems = List.map pred_setSyntax.dest_in (strip_conj conjs)
      fun setOf e =
          case List.find (fn (e', _) => aconv e' e) mems of
              SOME (_, set) => set
            | NONE => raise ERR "chainOf" "a step with no membership"
      (* from the element inwards-out: each step's set is of the next
         value out, until one of them is the clause's own argument *)
      fun walk e seen acc =
          let
            val set = setOf e
            val a = rand set
            val acc = {arg = a, set = set} :: acc
          in
            if not (List.exists (aconv a) evs) then acc
            else if List.exists (aconv a) seen then
              raise ERR "chainOf" "a chain that comes back on itself"
            else walk a (a :: seen) acc
          end
      val levels = walk z [z] []
      (* every membership the hypothesis states must be one the walk
         used, or the hypothesis says something this cannot see *)
      val _ = length levels = length mems orelse
              raise ERR "chainOf" "a hypothesis the walk does not cover"
    in
      SOME {z = z, levels = levels}
    end handle HOL_ERR _ => NONE

(* the outermost level alone, which is all a caller wanting the
   argument the clause states needs *)
fun nestedHyp Pv tm =
    case chainOf Pv tm of
        NONE => NONE
      | SOME {z, levels} =>
        let val {arg, set} = hd levels
        in SOME {z = z, set = set, arg = arg} end

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

(* a clause of the operator's induction, with a predicate added at
   each argument that has one: `∀h t. Q t ⇒ Q (h::t)` becomes
   `∀h t. P h ∧ Q t ⇒ Q (h::t)`.  An argument whose type the principle
   never reaches — the `bool` of a `tree list + bool` — gets nothing,
   which is what leaves the clause saying only what it can. *)
fun strengthen predOf clause =
    let
      val (args, hyps, conc) = openAll clause
      (* the operator's own induction already says what it can of an
         argument of its own type; saying it twice is a clause no proof
         of the operator's own clause discharges *)
      fun added a =
          case predOf (type_of a) of
              NONE => NONE
            | SOME P =>
              let val h = mk_comb (P, a)
              in if List.exists (aconv h) hyps then NONE else SOME h end
      val extra = List.mapPartial added args
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

(* a conjunction from its conjuncts assumed, in the shape the term
   itself has — the package nests them either way, and `LIST_CONJ`
   would settle on one *)
fun assumeConj tm =
    case Lib.total dest_conj tm of
        SOME (a, b) => CONJ (assumeConj a) (assumeConj b)
      | NONE => ASSUME tm

(* `∃v⃗. body` from a proof of `body` at the witnesses, outermost
   binder first *)
fun existsIntro tm ws th =
    case (Lib.total dest_exists tm, ws) of
        (SOME (v, b), w :: ws) =>
        EXISTS (tm, w) (existsIntro (Term.subst [v |-> w] b) ws th)
      | _ => th

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

(* what a principle says about the operators it recurses under: its
   predicate and the type that is about, the clauses, the nested
   hypotheses, and the operators in the order the clauses first mention
   them — which is the order that names the predicates *)
fun chainsOf Pv c = List.mapPartial (chainOf Pv) (hypsOf c)

(* A level with the values its set collects: the next level's argument,
   or — where the chain ends — the type the principle is about. *)
fun levelsOf ty {z = _, levels} =
    let
      fun go [] = []
        | go [{arg, set}] = [{arg = arg, set = set, elemty = ty}]
        | go ({arg, set} :: (rest as {arg = a, ...} :: _)) =
            {arg = arg, set = set, elemty = type_of a} :: go rest
    in
      go levels
    end

fun readPrinciple ind =
    let
      val (Pv, body) = dest_forall (concl ind)
      val ty = #1 (dom_rng (type_of Pv))
      (* a principle with a predicate per member says several things at
         once, and which of them a clause's hypothesis is about is not
         something this can see *)
      val _ = not (is_forall body) orelse
              raise ERR "mutual_induction"
                    "a principle with more than one predicate"
      val (hypsTm, _) = dest_imp body
      val clauses = strip_conj hypsTm
      val chains = List.concat (List.map (chainsOf Pv) clauses)
      val nested = List.concat (List.map (nestedOf Pv) clauses)
      val _ = not (null chains) orelse
              raise ERR "mutual_induction"
                    "the principle recurses under no operator"
      val levels = List.concat (List.map (levelsOf ty) chains)
      fun firstOccs [] = []
        | firstOccs (t :: ts) =
            t :: firstOccs (List.filter (not o equal t) ts)
    in
      {Pv = Pv, ty = ty, clauses = clauses,
       chains = chains, nested = nested, levels = levels,
       optys = firstOccs (List.map (type_of o #arg) levels)}
    end

(* the set function the principle collects a level's contents with, and
   the type of what it collects *)
fun levelOfType levels opty =
    case List.filter (fn r => type_of (#arg r) = opty) levels of
        [] => raise ERR "mutual_induction" "no set function"
      | r :: rs =>
        let
          val setfn = rator (#set r)
          (* two chains reaching the same type by different set
             functions are two operators sharing a name; saying which
             one a clause meant is beyond what the principle records *)
          val _ = List.all (fn r' => aconv (rator (#set r')) setfn andalso
                                     #elemty r' = #elemty r)
                           rs orelse
                  raise ERR "mutual_induction"
                        ("two ways of reaching " ^ type_to_string opty)
        in
          {setfn = setfn, elemty = #elemty r}
        end

fun setOfOperator levels opty = #setfn (levelOfType levels opty)

fun assemble (ops : operator list) ind =
    let
      val {Pv, ty, clauses, chains, nested, levels, optys} =
          readPrinciple ind
      (* the caller's operator for a type: the one whose induction is
         about it *)
      (* Two levels may recurse under the same operator, and then two
         of the caller's operators answer to the same induction
         principle.  What tells them apart is the type their set
         equations are stated at. *)
      fun statedAt opty r =
          List.exists
            (fn th => Lib.total (type_of o rand o lhs o #2 o strip_forall o
                                 concl) th = SOME opty)
            (#sets r)
      fun opFor opty =
          case List.find (statedAt opty) ops of
              SOME r => r
            | NONE =>
              case List.find (fn r => Lib.can (atType opty) (#induction r))
                             ops of
                  SOME r => r
                | NONE => raise ERR "mutual_induction"
                                ("no induction principle offered for " ^
                                 type_to_string opty)
      fun setFor opty = setOfOperator levels opty
      val Qs = List.tabulate
                 (length optys,
                  fn i => mk_var ("Q" ^ Int.toString i,
                                  List.nth (optys, i) --> bool))
      fun Qfor opty =
          case List.find (fn (t, _) => t = opty) (ListPair.zip (optys, Qs)) of
              SOME (_, q) => q
            | NONE => raise ERR "mutual_induction" "no predicate"
      (* the predicate a value of a type has, if it has one: the
         principle's own where the type is, and the operator's at every
         level a chain walks through *)
      fun predOf t =
          if t = ty then SOME Pv
          else if List.exists (fn t' => t' = t) optys then SOME (Qfor t)
          else NONE
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
            List.map (fn c => strengthen predOf
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
       opClausesFor = opClausesFor, nested = nested,
       chains = chains, levels = levels, predOf = predOf,
       elemFor = fn opty => #elemty (levelOfType levels opty)}
    end

fun mutual_induction_goal ops ind = #goal (assemble ops ind)

(* ----------------------------------------------------------------------
    Finding the operators the principle recurses under.

    A caller who has only the principle has enough: it names each
    operator and the set function that collects the operator's contents,
    the operator's own induction principle is in the TypeBase, and what
    its set function says at each of its constructors is a simplification
    away.
   ---------------------------------------------------------------------- *)

(* An operator's theory may write a set as the predicate it is —
   `sumTheory.setL_def` says `setL (INL a) = (λx. x = a)` — and a
   simplification with it leaves that lambda standing.  These put such
   a set back in the notation whose parts can be read off. *)
val setNotation =
    let
      val ss = simpLib.++ (BasicProvers.srw_ss(), pred_setLib.PRED_SET_ss)
      val x = mk_var ("x", alpha) and a = mk_var ("a", alpha)
      fun proved tm = simpLib.SIMP_PROVE ss [pred_setTheory.EXTENSION,
                                             pred_setTheory.IN_ABS] tm
      val mt = pred_setSyntax.mk_empty alpha
    in
      [proved (mk_eq (mk_abs (x, mk_eq (x, a)),
                      pred_setSyntax.mk_insert (a, mt))),
       proved (mk_eq (mk_abs (x, boolSyntax.F), mt))]
    end

fun setEqnsOf setfn opty =
    let
      val cnv = simpLib.SIMP_CONV (BasicProvers.srw_ss()) setNotation
      fun atCons c =
          let
            val c = Term.inst (match_type (#2 (strip_fun (type_of c))) opty) c
            val args = #1 (strip_fun (type_of c))
            val vs = List.tabulate
                       (length args,
                        fn i => mk_var ("a" ^ Int.toString i,
                                        List.nth (args, i)))
            val tm = mk_comb (setfn, list_mk_comb (c, vs))
          in
            (* an operator whose set function does not simplify at its
               own constructors is one the caller has to say something
               about: left to itself the equation would come back
               reflexive, and the principle built on it would be wrong *)
            cnv tm
            handle Conv.UNCHANGED =>
                   raise ERR "operators_of"
                         ("nothing simplifies " ^ term_to_string tm ^
                          "; supply the operator instead")
          end
    in
      List.map atCons (TypeBase.constructors_of opty)
    end

fun operators_of ind =
    let val {levels, optys, ...} = readPrinciple ind
    in
      List.map (fn opty =>
                   let val setfn = setOfOperator levels opty
                   in
                     {induction = TypeBase.induction_of opty,
                      sets = setEqnsOf setfn opty}
                   end)
               optys
    end

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
      (* A clause's hypotheses are discharged together, as the one
         conjunction the clause states.  DISCH takes away a hypothesis
         the theorem has, and the theorem has them one at a time, so the
         conjunction has to answer for each before it can be discharged
         — with a single hypothesis the conjunction *is* it and the
         difference does not show. *)
      fun close vs hyps th =
          GENL vs (case hyps of
                       [] => th
                     | _ =>
                       let val c = list_mk_conj hyps
                       in
                         DISCH c (List.foldl (fn (p, t) => PROVE_HYP p t) th
                                             (CONJUNCTS (ASSUME c)))
                       end)
      (* ------------------------------------------------------------
          what the operator's predicate says of a value, from what the
          type's says of its contents
         ------------------------------------------------------------ *)
      fun bridgeFor opty =
          let
            val Sf = #setFor info opty and Q = #Qfor info opty
            (* what this level collects is the next level's values, and
               the predicate to say of them is that level's own *)
            val elemty = #elemFor info opty
            val EP = case #predOf info elemty of
                         SOME P => P
                       | NONE => raise ERR "mutual_induction"
                                   ("no predicate for " ^
                                    type_to_string elemty)
            val l = mk_var ("l", opty) and z = mk_var ("z", elemty)
            fun memOf t = mk_forall (z, mk_imp (inThm z (mk_comb (Sf, t)),
                                                mk_comb (EP, z)))
            val Q0 = mk_abs (l, mk_imp (memOf l, mk_comb (Q, l)))
            val inst = CONV_RULE (DEPTH_CONV BETA_CONV)
                                 (SPEC Q0 (atType opty
                                             (#induction (#opFor info opty))))
            val goals = strip_conj (#1 (dest_imp (concl inst)))
            (* a type may recurse under the same operator at two
               levels — `(tree list + bool) option list` and
               `tree list` — and then the operator's equations come at
               whichever level was asked for first *)
            fun atLevel th =
                let
                  val c = rand (lhs (#2 (strip_forall (concl th))))
                in
                  INST_TYPE (match_type (type_of c) opty) th
                end handle HOL_ERR _ => th
            val setEqs = List.map atLevel (#sets (#opFor info opty))
            fun prove (g, ass) =
                let
                  val (vs, hs, conc) = openAll g
                  val (ihs, memTm) =
                      (List.filter (fn h => not (isSome (nestedHyp EP h))) hs,
                       case List.filter (isSome o nestedHyp EP) hs of
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
            (* A hypothesis reaching the contents through several
               operators says what it says of the innermost values
               only.  The operator's predicate at each level follows
               from that level's bridge, given the next level's
               predicate of everything the level collects — so the
               walk goes down to the values the chain is about, and
               the bridges come back up. *)
            fun supply h =
                case chainOf Pv h of
                    NONE => ASSUME h
                  | SOME {z, levels} =>
                    let
                      val (ante, _) = dest_imp (#2 (dest_forall h))
                      val (evs, conjs) = strip_exists ante
                      fun down [] = raise ERR "mutual_induction"
                                          "a hypothesis with no level"
                        | down (lvl :: rest) =
                          let
                            val v = #arg lvl
                            val bridge = SPEC v (bridgeOf (type_of v))
                          in
                            case rest of
                                [] =>
                                let
                                  val memtm = inThm z (#set lvl)
                                  val ex = existsIntro ante evs
                                                       (assumeConj conjs)
                                  val pz = MP (SPEC z (ASSUME h)) ex
                                in
                                  MP bridge (GEN z (DISCH memtm pz))
                                end
                              | nxt :: _ =>
                                let
                                  val x = #arg nxt
                                  val memtm = inThm x (#set lvl)
                                in
                                  MP bridge (GEN x (DISCH memtm (down rest)))
                                end
                          end
                    in
                      down levels
                    end
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
      (* An outer level's clause says something of the values it
         collects, which is the next level in.  So the levels settle
         from the inside out, and each has what the ones inside it
         already say. *)
      fun allQfor done opty =
          let
            val inst = SPEC (#Qfor info opty)
                            (atType opty (#induction (#opFor info opty)))
            val goals = strip_conj (#1 (dest_imp (concl inst)))
            fun settled v =
                if type_of v = ty then SOME (SPEC v allX)
                else
                  case List.find (fn (t, _) => t = type_of v) done of
                      SOME (_, th) => SOME (SPEC v th)
                    | NONE => NONE
            fun prove (g, ass) =
                let
                  val (vs, hyps, _) = openAll g
                  val extras = List.mapPartial settled vs
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
      val allQs =
          List.foldl (fn (opty, done) => (opty, allQfor done opty) :: done)
                     [] (List.rev (#optys info))
      fun allQof opty =
          case List.find (fn (t, _) => t = opty) allQs of
              SOME (_, th) => th
            | NONE => raise ERR "mutual_induction" "no proof for a level"
    in
      GENL (Pv :: #Qs info)
           (DISCH (#hypterm info)
                  (LIST_CONJ (allX :: List.map allQof (#optys info))))
    end

end
