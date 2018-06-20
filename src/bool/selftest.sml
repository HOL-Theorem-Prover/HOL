
open HolKernel Parse DB testutils

val _ = set_trace "Unicode" 0

val _ = tprint "test of apropos_in, find_in"

val _ = let
  val str = "THM" ;
  val tm = ``$/\`` ;
  val find1 = find str ;
  val list1 = apropos_in tm find1 ;
  val apropos2 = apropos tm ;
  val list2 = find_in str apropos2 ;
  val true = length list1 = length list2 ;
  (* next test may be implementation dependent *)
  val true = map #1 list1 = map #1 list2 ;
in OK() end handle _ => die "FAILED" ;
