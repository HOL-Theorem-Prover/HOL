(* ========================================================================= *)
(* STRING CONVERSIONS                                                        *)
(* ========================================================================= *)

structure extra_stringLib :> extra_stringLib =
struct

open HolKernel Parse boolLib bossLib metisLib arithmeticTheory
     listTheory numTheory simpLib
     stringTheory rich_listTheory stringSimps
     listSimps extra_stringTheory;


val safe_list_ss = (simpLib.++ (bool_ss, LIST_ss));

val safe_string_ss = (simpLib.++ (bool_ss, STRING_ss));

val arith_string_ss = (simpLib.++ (arith_ss, STRING_ss));

val string_ss = (simpLib.++ (list_ss, STRING_ss));


fun test_eq tm1 tm2 = let
        val x = match_term tm1 tm2
        in ALL_CONV tm2 end;

fun toString_CONV_helper tm =
   DEPTH_CONV (test_eq ``toString n``
                THENC SIMP_CONV (simpLib.++ (arith_string_ss, LIST_ss))
                [toString_def, rec_toString_def]);

val toString_CONV = toString_CONV_helper ``:num``;

val toStringCAT_CONV =
        toString_CONV
        THENC SIMP_CONV safe_string_ss [];

fun REPEAT_STRING_CONV (defs:thm list) =
        REPEATC (ONCE_REWRITE_CONV defs THENC toString_CONV);

fun REPEAT_STRINGCAT_CONV (defs:thm list) =
        REPEATC (ONCE_REWRITE_CONV defs THENC toStringCAT_CONV);


end