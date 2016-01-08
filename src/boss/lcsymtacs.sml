structure lcsymtacs :> lcsymtacs =
struct

  open Abbrev HolKernel boolLib Tactic Tactical BasicProvers simpLib
  open Rewrite bossLib Thm_cont

  fun kall_tac (_: 'a) : tactic = all_tac


end
