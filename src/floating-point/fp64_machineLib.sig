signature fp64_machineLib =
sig

  (* ----------------------------------------------------------------------
      Support 64-bit native evaluation
      (Controlled by the trace "native IEEE". Off by default.)
     ---------------------------------------------------------------------- *)

  val sqrt_CONV: Conv.conv ref
  val add_CONV: Conv.conv ref
  val sub_CONV: Conv.conv ref
  val mul_CONV: Conv.conv ref
  val div_CONV: Conv.conv ref
  val compare_CONV: Conv.conv ref
  val eq_CONV: Conv.conv ref
  val lt_CONV: Conv.conv ref
  val le_CONV: Conv.conv ref
  val gt_CONV: Conv.conv ref
  val ge_CONV: Conv.conv ref


end
