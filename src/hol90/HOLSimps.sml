structure HOLSimps :> HOLSimps =
struct

open Lib simpLib;
open boolSimps rich_listSimps combinSimps 
     SatisfySimps UnwindSimps arithSimps pairSimps sumSimps;

val HOL_ss = merge_ss [BOOL_ss, CONG_ss, LIST_ss, COMBIN_ss, SATISFY_ss, 
                       NOT_ss, UNWIND_ss, ARITH_ss, PAIR_ss, SUM_ss];

val hol_ss = mk_simpset [HOL_ss];;

end;
