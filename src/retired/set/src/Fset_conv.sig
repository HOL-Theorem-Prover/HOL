(* =====================================================================*)
(* FILE          : fset_conv.sig                                        *)
(* DESCRIPTION   : Proof support for finite sets. Translated from hol88.*)
(*                                                                      *)
(* =====================================================================*)


signature Fset_conv =
sig
  type conv = Abbrev.conv

  val FINITE_CONV :conv
  val IN_CONV :conv -> conv
  val DELETE_CONV :conv -> conv
  val UNION_CONV :conv -> conv
  val INSERT_CONV :conv -> conv
  val IMAGE_CONV :conv -> conv -> conv
end; 
