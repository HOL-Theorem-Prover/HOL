(* Compset fragment evaluating finite sets as fEMPTY/fINSERT chains, the
   values Refute generates for :'a fset.

   finite_set's compset rules are its quotient lifts ([fEMPTY = fset_ABS
   []], [fIN = (I ---> fset_REP ---> I) MEM], ...), which leave every
   operation stuck at [fset_REP (fset_ABS ...)]: fset_REP picks a
   representative list and has no rule.  [register] replaces those rules
   by chain rules, so fEMPTY and fINSERT stay as they are, the way
   FEMPTY and FUPDATE do, and each covered operation reduces a chain.

   A chain is not canonical (order, duplicates), so equality is decided
   by [FSET_EQ_DECIDE_CONV] element by element: [fINSERT a s = t] is
   [fIN a t /\ fDELETE a s = fDELETE a t], whose own equality is on a
   shorter left chain.  Element equalities, nested sets' included, are
   decided by the compset in turn. *)
structure Refute_EvalFset :> Refute_EvalFset = struct

  open HolKernel boolLib

  val ERR = Feedback.mk_HOL_ERR "Refute_EvalFset"

  fun fset_const name = Term.prim_mk_const {Thy = "finite_set", Name = name}
  val fempty_tm = fset_const "fEMPTY"
  val finsert_tm = fset_const "fINSERT"

  fun is_fset_ty ty =
    case Lib.total Type.dest_thy_type ty of
        SOME {Thy = "finite_set", Tyop = "fset", ...} => true
      | _ => false

  fun is_fempty tm = Term.is_const tm andalso Term.same_const tm fempty_tm

  fun dest_finsert tm =
    case boolSyntax.strip_comb tm of
        (head, [element, rest]) =>
          if Term.is_const head andalso Term.same_const head finsert_tm
          then (element, rest)
          else raise ERR "dest_finsert" "not an fINSERT"
      | _ => raise ERR "dest_finsert" "not an fINSERT"

  fun is_chain tm =
    is_fempty tm orelse
    (case Lib.total dest_finsert tm of
         SOME (_, rest) => is_chain rest
       | NONE => false)

  (* For display: an element is dropped when an inner fINSERT of the
     chain adds an [aconv] one, which denotes the same set for any element
     type.  Not a sort, as for fmap chains: two chains denoting the same
     set may still display differently. *)
  fun canonical_chain tm =
    case Lib.total dest_finsert tm of
        NONE => tm
      | SOME (element, rest) =>
          let
            val rest' = canonical_chain rest
            fun holds chain =
              case Lib.total dest_finsert chain of
                  NONE => false
                | SOME (other, inner) =>
                    Term.aconv element other orelse holds inner
          in
            if holds rest' then rest'
            else Term.mk_comb (Term.mk_comb (Term.rator (Term.rator tm),
                   element), rest')
          end

  fun eval tm = computeLib.CBV_CONV (computeLib.the_compset ()) tm

  val chain_eq = refuteTheory.fset_chain_eq

  (* The conv is reached with both sides already reduced by call-by-value.
     It fails, leaving the redex stuck, when the evaluation does not end
     in T or F (an element equality the compset cannot decide). *)
  fun FSET_EQ_DECIDE_CONV tm =
    let
      val (l, r) = dest_eq tm
      val _ = is_fset_ty (type_of l) orelse raise ERR "conv" "not an fset"
      val _ = is_chain l andalso is_chain r
              orelse raise ERR "conv" "not fEMPTY-rooted chains"
    in
      if is_fempty l then
        if is_fempty r then EQT_INTRO (REFL l)
        else
          let val (a, s) = dest_finsert r
          in EQF_INTRO (ISPECL [a, s] finite_setTheory.NOT_EMPTY_INSERT)
          end
      else
        let
          val step = Conv.REWR_CONV chain_eq tm
          val decided = TRANS step (eval (rhs (concl step)))
          val result = rhs (concl decided)
        in
          if Term.aconv result boolSyntax.T orelse
             Term.aconv result boolSyntax.F
          then decided
          else raise ERR "conv" "undecided"
        end
    end

  (* Hung on the shared ("=", "min") key with its own type guard, as
     Refute_EvalFmap's and Refute_EvalRat's equality convs are. *)
  val fset_eq_tm =
    Term.inst [Type.alpha |-> Type.mk_thy_type
                 {Thy = "finite_set", Tyop = "fset", Args = [Type.alpha]}]
      boolSyntax.equality

  val lifted = List.map fset_const
    ["fEMPTY", "fINSERT", "fIN", "fUNION", "fDELETE", "fIMAGE",
     "fBIGUNION", "fCARD"]

  (* [fset_ABS (fset_REP s) = s] folds back the lifts of fEMPTY and
     fINSERT in rules compiled before [register]: computeLib binds each
     constant's rules when a rule is compiled, so those still unfold them
     to fset_ABS/fset_REP, whose own (empty) entries [register] extends. *)
  val chain_rules =
    let open finite_setTheory refuteTheory in
      [EQF_INTRO (SPEC_ALL NOT_IN_EMPTY), IN_INSERT,
       CONJUNCT1 (SPEC_ALL fUNION_EMPTY), fUNION_INSERT,
       DELETE_EMPTY, fset_chain_fDELETE, fIMAGE_thm, fCARD_THM,
       fset_chain_fBIGUNION, fset_chain_fset_ABS, fset_ABS_REP]
    end

  (* Runs once, from Refute's module load; a second call would append a
     second copy of the equality conv. *)
  fun register () =
    (computeLib.del_consts lifted;
     computeLib.add_funs chain_rules;
     computeLib.add_convs [(fset_eq_tm, 2, FSET_EQ_DECIDE_CONV)])

end
