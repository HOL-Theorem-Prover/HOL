(* ------------------------------------------------------------------------- *)
(* A real simpset (includes Peano arithmetic and pairs).  This should be     *)
(* fleshed out.                                                              *)
(* ------------------------------------------------------------------------- *)

structure realSimps :> realSimps = 
struct

open Drule realTheory;

val arith_ss = 
  simpLib.++
    (simpLib.++(boolSimps.bool_ss, pairSimps.PAIR_ss),numSimps.ARITH_ss);


val real_ss = simpLib.++(arith_ss, simpLib.SIMPSET {
  ac = [(SPEC_ALL REAL_ADD_ASSOC, SPEC_ALL REAL_ADD_SYM),
        (SPEC_ALL REAL_MUL_ASSOC, SPEC_ALL REAL_MUL_SYM)],
  convs = [],
  dprocs = [],
  filter = NONE,
  rewrs = [REAL_ADD_LID, REAL_ADD_RID, REAL_MUL_LID, REAL_MUL_RID, 
           REAL_MUL_LZERO, REAL_MUL_RZERO],
  congs = []});

end;
