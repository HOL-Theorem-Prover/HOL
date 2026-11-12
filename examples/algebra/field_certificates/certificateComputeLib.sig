signature certificateComputeLib =
sig
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
