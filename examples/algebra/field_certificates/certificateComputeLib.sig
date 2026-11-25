signature certificateComputeLib =
sig
  (* Literal natural-number terms and untrusted inverse candidates.
     inverse_candidate p x returns Euclid's proposed residue modulo p without
     checking coprimality; callers must prove the required inverse equation. *)
  val integer : Term.term -> IntInf.int
  val literal : IntInf.int -> Term.term
  val inverse_candidate : IntInf.int -> IntInf.int -> IntInf.int

  (* Untrusted binary trajectories. Operation mode resumes from the largest
     matching assumed prefix and emits at most width bits; window mode emits
     one equation per width bits over the full exponent, without resumption.
     Candidate values stay in the caller's representation until emitted.
     Every returned equation must subsequently be proved. *)
  val BINARY_MILESTONES :
    {operations : bool, width : int, prefix : Term.term,
     exponent : IntInf.int, assumptions : Term.term list, zero : 'a,
     decode : Term.term -> 'a, encode : 'a -> Term.term,
     double : 'a -> 'a, add_base : 'a -> 'a} ->
    {equations : Term.term list, seed : Term.term option,
     continuation : bool}

  (* Assemble ordered milestone claims and reconstruct the original goal.
     final is the last milestone equality (or the zero-case equality);
     seed is an optional assumed prefix. A continuation leaves the original
     goal under final, otherwise final rewrites it to an optional residual.
     Scheduling and candidate generation remain the caller's responsibility. *)
  val MILESTONE_GOALS :
    {goal : Abbrev.goal, equations : Term.term list,
     seed : Term.term option, continuation : bool, final : Thm.thm} ->
    Abbrev.goal list * (Thm.thm list -> Thm.thm)

  (* Normalize natural arithmetic and comparisons with kernel CV arithmetic.
     Surrounding Boolean connectives are left unchanged. *)
  val NAT_CONV : Abbrev.conv

  (* Snapshot currently loaded equations and fast numeric callbacks.
     Create once per bounded-computation context. *)
  val EVAL_COMPSET : unit -> computeLib.compset
  val EVAL_CONV : unit -> Abbrev.conv

  (* Closed a ** e MOD n via expMod and the standard CV translations, without
     expanding the power when n <> 0. Closed arithmetic in a, e and n is
     normalized first; n = 0 follows HOL's unreduced-power semantics. *)
  val MODPOW_CONV : Abbrev.conv
end
