(* ===================================================================== *)
(* FILE          : QConv.sig                                             *)
(* DESCRIPTION   : Efficient depth conversions.                          *)
(* AUTHORS       : Richard Boulton                                       *)
(* ===================================================================== *)


signature QConv =
sig
   type conv = Abbrev.conv

   exception UNCHANGED

   val QCONV            : conv -> conv
   val ALL_QCONV        : conv
   val THENQC           : conv -> conv -> conv
   val ORELSEQC         : conv -> conv -> conv
   val REPEATQC         : conv -> conv
   val CHANGED_QCONV    : conv -> conv
   val TRY_QCONV        : conv -> conv
   val SUB_QCONV        : conv -> conv
   val DEPTH_QCONV      : conv -> conv
   val REDEPTH_QCONV    : conv -> conv
   val TOP_DEPTH_QCONV  : conv -> conv
   val ONCE_DEPTH_QCONV : conv -> conv
   val TOP_SWEEP_QCONV  : conv -> conv
end
