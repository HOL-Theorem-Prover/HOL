(* Compset fragment deciding equality of ground finite maps.

   [finite_mapLib]'s compset rules cover FLOOKUP/FDOM/FUNION/DOMSUB but
   not [=] at :'a |-> 'b, and FUPDATE_EQ/FUPDATE_COMMUTES/
   NOT_EQ_FEMPTY_FUPDATE are simp-only.  computeLib therefore decides
   [fm = fm'] only when the two chains are literally identical (T), and
   any other pair is stuck -- so a Test node whose conclusion is such an
   equality can never reach a genuine counterexample on the compute
   substrate, and equal-but-permuted chains surface as spurious
   Potential reports.  [FMAP_EQ_DECIDE_CONV] closes both gaps for
   FEMPTY-rooted chains of literal pairs.

   F: a key from either chain where computeLib decides the two FLOOKUPs
   unequal; [f = g] yields [FLOOKUP f k = FLOOKUP g k] by congruence, so
   the decision is a contradiction.  T: each chain is proved equal to a
   sorted-dedup canonical chain (later writes shadow earlier ones by
   FUPDATE_EQ; distinct keys reorder by FUPDATE_COMMUTES, its side
   condition discharged by computeLib), and aconv canonical forms give
   the equality by TRANS.  Every step is proved, so nothing is gated on
   the keys being literals: an undischargeable side condition fails the
   conversion and the redex stays stuck, exactly as before.  The conv is
   reached with both sides already reduced by call-by-value, so keys and
   values arrive in whatever normal form the compset gives them. *)
structure Refute_EvalFmap :> sig
  val register : unit -> unit
end = struct

  open HolKernel boolLib

  val ERR = Feedback.mk_HOL_ERR "Refute_EvalFmap"

  val mk_fupdate = finite_mapSyntax.mk_fupdate
  val dest_fupdate = finite_mapSyntax.dest_fupdate
  val strip_fupdate = finite_mapSyntax.strip_fupdate
  val is_fempty = finite_mapSyntax.is_fempty
  val mk_flookup = finite_mapSyntax.mk_flookup

  fun eval tm = computeLib.CBV_CONV (computeLib.the_compset ()) tm

  (* [|- (a = b) = F] from computeLib, or NONE. *)
  fun decide_false eq =
    let val thm = eval eq
    in if Term.aconv (rhs (concl thm)) boolSyntax.F then SOME thm else NONE
    end handle Interrupt => raise Interrupt | _ => NONE

  (* [|- A = B] to [|- A |+ p = B |+ p]. *)
  fun fupdate_cong p thm =
    let val fupdate = rator (rator (mk_fupdate (lhs (concl thm), p)))
    in Thm.AP_THM (Thm.AP_TERM fupdate thm) p
    end

  (* Sorted ascending by [Term.compare] on keys, last update largest.
     [insert] proves [|- chain |+ (k,v) = chain'] with [chain'] sorted
     whenever [chain] is. *)
  fun insert (k, v) chain =
    let val p = pairSyntax.mk_pair (k, v)
    in
      case Lib.total dest_fupdate chain of
          NONE => Thm.REFL (mk_fupdate (chain, p))
        | SOME (rest, p0) =>
            let
              val (k0, v0) = pairSyntax.dest_pair p0
            in
              if Term.aconv k k0 then
                ISPECL [rest, k0, v0, v] finite_mapTheory.FUPDATE_EQ
              else if Term.compare (k, k0) = GREATER then
                Thm.REFL (mk_fupdate (chain, p))
              else
                let
                  val distinct =
                    case decide_false (mk_eq (k0, k)) of
                        SOME thm => EQF_ELIM thm
                      | NONE => raise ERR "insert" "undecided key equality"
                  val swap = MP (ISPECL [rest, k0, v0, k, v]
                                   finite_mapTheory.FUPDATE_COMMUTES)
                                distinct
                in
                  TRANS swap (fupdate_cong p0 (insert (k, v) rest))
                end
            end
    end

  (* [|- chain = canonical] for an FEMPTY-rooted chain of literal pairs. *)
  fun normalize chain =
    let
      val (base, pairs) = strip_fupdate chain
      val _ = is_fempty base orelse raise ERR "normalize" "not FEMPTY-rooted"
      fun step (p, thm) =
        TRANS (fupdate_cong p thm)
              (insert (pairSyntax.dest_pair p) (rhs (concl thm)))
    in
      List.foldl step (Thm.REFL base) pairs
    end

  fun chain_keys chain =
    List.map (fst o pairSyntax.dest_pair) (snd (strip_fupdate chain))

  fun FMAP_EQ_DECIDE_CONV tm =
    let
      val (l, r) = dest_eq tm
      val _ = finite_mapSyntax.is_fmap_ty (type_of l)
              orelse raise ERR "conv" "not an fmap"
      val _ = is_fempty (fst (strip_fupdate l))
              andalso is_fempty (fst (strip_fupdate r))
              orelse raise ERR "conv" "not FEMPTY-rooted"
      val keys = Refute_Util.distinct_terms (chain_keys l @ chain_keys r)
      fun witness k =
        Option.map (fn thm => (k, thm))
          (decide_false (mk_eq (mk_flookup (l, k), mk_flookup (r, k))))
    in
      case Lib.get_first witness keys of
          SOME (k, thm) =>
            let
              val flookup = rator (rator (mk_flookup (l, k)))
              val cong = Thm.AP_THM (Thm.AP_TERM flookup (ASSUME tm)) k
            in
              EQF_INTRO (NOT_INTRO (DISCH tm (EQ_MP thm cong)))
            end
        | NONE =>
            let
              val lthm = normalize l
              val rthm = normalize r
            in
              if Term.aconv (rhs (concl lthm)) (rhs (concl rthm)) then
                EQT_INTRO (TRANS lthm (SYM rthm))
              else raise ERR "conv" "undecided"
            end
    end

  (* Like Refute_EvalRat's rat equality conv: hung on the shared
     ("=", "min") key, guarded by its own type test, so it is tried for
     any equality redex and fails through on every non-fmap one.  Runs
     once, from Refute's module load; a second call would append a
     second copy to the chain. *)
  val fmap_eq_tm =
    Term.inst
      [Type.alpha |-> finite_mapSyntax.mk_fmap_ty (Type.alpha, Type.beta)]
      boolSyntax.equality

  fun register () =
    computeLib.add_convs [(fmap_eq_tm, 2, FMAP_EQ_DECIDE_CONV)]

end
