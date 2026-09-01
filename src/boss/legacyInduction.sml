structure legacyInduction :> legacyInduction =
struct

open HolKernel Parse boolLib bossLib

val ERR = mk_HOL_ERR "legacyInduction"

(* A clause's hypothesis about an operator's contents: `∀z. z ∈ set l ⇒
   P z`, however that membership is written.  What is wanted from it is
   the bound variable, the membership itself, and the value it is about. *)
fun nestedHyp Pv tm =
    let
      val (z, body) = dest_forall tm
      val (memp, conc) = dest_imp body
      val _ = aconv conc (mk_comb (Pv, z)) orelse
              raise ERR "nestedHyp" "not about the predicate"
      val vs = List.filter (fn v => not (aconv v z)) (free_vars memp)
    in
      case vs of
          [l] => SOME {z = z, mem = memp, arg = l}
        | _ => NONE
    end handle HOL_ERR _ => NONE

(* the operator's own constructors and induction, from its entry *)
fun operatorFacts extras opty =
    let
      val ind =
          case List.find (fn th => Lib.can (match_term (concl th)) (concl th)
                                   andalso
                                   let val (_, b) = dest_forall (concl th)
                                       val (_, c) = dest_imp b
                                       val (v, _) = dest_forall c
                                   in type_of v = opty end
                                   handle HOL_ERR _ => false)
                         extras of
              SOME th => th
            | NONE => TypeBase.induction_of opty
    in
      {induction = ind, constructors = TypeBase.constructors_of opty}
    end

(* the clauses the operator's predicate satisfies: a constructor's
   arguments of the type being defined satisfy that type's predicate,
   and those of the operator's own type satisfy the operator's *)
fun operatorClauses (Pv, Qv) ty opty cs =
    let
      fun clauseOf c0 =
          let
            (* the entry's constructors are the operator's own, at its
               own arguments; here they are at this instance *)
            val c = Term.inst (match_type (#2 (strip_fun (type_of c0))) opty)
                              c0
            val (argtys, _) = strip_fun (type_of c)
            val args = List.tabulate
                         (length argtys,
                          fn i => mk_var ("a" ^ Int.toString i,
                                          List.nth (argtys, i)))
            fun hypOf a = if type_of a = ty then SOME (mk_comb (Pv, a))
                          else if type_of a = opty then SOME (mk_comb (Qv, a))
                          else NONE
            val hyps = List.mapPartial hypOf args
            val concl = mk_comb (Qv, list_mk_comb (c, args))
          in
            list_mk_forall (args,
                            case hyps of
                                [] => concl
                              | _ => mk_imp (list_mk_conj hyps, concl))
          end
    in
      List.map clauseOf cs
    end

fun statement extras ind =
    let
      val (Pv, body) = dest_forall (concl ind)
      val (hyps, _) = dest_imp body
      val ty = #1 (dom_rng (type_of Pv))
      val clauses = strip_conj hyps
      (* the operators the principle speaks of, and a predicate each *)
      fun nestedOf c =
          List.mapPartial (nestedHyp Pv) (strip_conj (#1 (dest_imp
                                            (#2 (strip_forall c))))
                                          handle HOL_ERR _ => [])
      val nested = List.concat (List.map nestedOf clauses)
      val optys = Lib.mk_set (List.map (type_of o #arg) nested)
      val _ = not (null optys) orelse
              raise ERR "mutual_induction"
                    "the principle speaks of no operator"
      val Qs = List.tabulate
                 (length optys,
                  fn i => mk_var ("P" ^ Int.toString (i + 1),
                                  List.nth (optys, i) --> bool))
      fun Qfor opty = List.nth (Qs, valOf (Lib.total (index (fn t => t = opty))
                                                     optys))
      (* each clause with the operator's predicate in place of what it
         says about the operator's contents *)
      fun rewriteClause c =
          let
            val (vs, b) = strip_forall c
          in
            case Lib.total dest_imp b of
                NONE => c
              | SOME (ante, con) =>
                let
                  fun swap h =
                      case nestedHyp Pv h of
                          NONE => h
                        | SOME {arg, ...} => mk_comb (Qfor (type_of arg), arg)
                  val ante' = list_mk_conj (List.map swap (strip_conj ante))
                in
                  list_mk_forall (vs, mk_imp (ante', con))
                end
          end
      val newClauses = List.map rewriteClause clauses
      val opClauses =
          List.concat
            (List.map (fn opty =>
                          operatorClauses (Pv, Qfor opty) ty opty
                            (#constructors (operatorFacts extras opty)))
                      optys)
      val x = mk_var ("x", ty)
      val concl =
          list_mk_conj
            (mk_forall (x, mk_comb (Pv, x)) ::
             List.map (fn q => let val v = mk_var ("l", #1 (dom_rng
                                                              (type_of q)))
                               in mk_forall (v, mk_comb (q, v)) end)
                      Qs)
      val goal = list_mk_forall
                   (Pv :: Qs,
                    mk_imp (list_mk_conj (newClauses @ opClauses), concl))
      val opInds = List.map (fn opty => #induction (operatorFacts extras opty))
                            optys
      (* what the operator's predicate says of a value, from what the
         type's says of its contents, and back again *)
      val bridges =
          List.map (fn {z, mem, arg} =>
                       let val q = Qfor (type_of arg)
                       in
                         mk_forall (arg,
                           mk_imp (mk_forall (z, mk_imp (mem,
                                                         mk_comb (Pv, z))),
                                   mk_comb (q, arg)))
                       end)
                   nested
      (* an operator's predicate follows from what the type's says of
         its contents, by the operator's own induction; then the type's
         principle, and then the operators' again *)
      val byOperator = FIRST (List.map ho_match_mp_tac opInds)
      val tac =
          rpt gen_tac >> strip_tac >>
          EVERY (List.map (fn b => SUBGOAL_THEN b assume_tac >-
                                   (byOperator >> rw[] >> metis_tac[]))
                          bridges) >>
          conj_asm1_tac >- (ho_match_mp_tac ind >> rw[] >> metis_tac[]) >>
          rpt conj_tac >> byOperator >> rw[] >> metis_tac[]
    in
      (goal, tac)
    end

fun mutual_induction_goal ind = #1 (statement [] ind)
fun mutual_induction_with extras ind =
    let val (goal, tac) = statement extras ind
    in TAC_PROOF (([], goal), tac) end
fun mutual_induction ind = mutual_induction_with [] ind

end
