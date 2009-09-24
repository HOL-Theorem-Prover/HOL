(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Proforma theorems, used for Z3 proof reconstruction *)

structure Z3_ProformaThms =
struct

  fun prove net t =
    Lib.tryfind
      (fn th => Drule.INST_TY_TERM (Term.match_term (Thm.concl th) t) th)
      (Net.match t net)

  fun thm_net_from_list thms =
    List.foldl (fn (th, net) => Net.insert (Thm.concl th, th) net) Net.empty
      thms

  val def_axiom_thms = thm_net_from_list
  [
    bossLib.DECIDE ``~(p <=> q) \/ ~p \/ q``,
    bossLib.DECIDE ``~(p <=> q) \/ p \/ ~q``,
    bossLib.DECIDE ``(p <=> ~q) \/ ~p \/ q``,
    bossLib.DECIDE ``(p <=> q) \/ p \/ q``,
    bossLib.DECIDE ``~(~p <=> q) \/ p \/ q``,
    bossLib.DECIDE ``~q \/ p \/ ~(q <=> p)``,
    bossLib.DECIDE ``q \/ p \/ ~(q <=> ~p)``,
    bossLib.PROVE [] ``p \/ (x = if p then y else x)``,
    bossLib.PROVE [] ``~p \/ (x = if p then x else y)``,
    bossLib.PROVE [] ``p \/ q \/ ~(if p then r else q)``,
    bossLib.PROVE [] ``~p \/ q \/ ~(if p then q else r)``,
    bossLib.PROVE [] ``(if p then q else r) \/ ~p \/ ~q``,
    bossLib.PROVE [] ``(if p then q else r) \/ p \/ ~r``
  ]

  val rewrite_thms = thm_net_from_list
  [
    bossLib.PROVE [] ``(x = y) <=> (y = x)``,
    bossLib.PROVE [] ``(x = x) <=> T``,
    bossLib.DECIDE ``(p <=> T) <=> p``,
    bossLib.DECIDE ``(p <=> F) <=> ~p``,
    bossLib.DECIDE ``(~p <=> ~q) <=> (p <=> q)``,

    bossLib.PROVE [] ``(if ~p then x else y) = (if p then y else x)``,

    bossLib.DECIDE ``(~p ==> q) <=> (p \/ q)``,
    bossLib.DECIDE ``(~p ==> q) <=> (q \/ p)``,
    bossLib.DECIDE ``(p ==> q) <=> (~p \/ q)``,
    bossLib.DECIDE ``(p ==> q) <=> (q \/ ~p)``,
    bossLib.DECIDE ``(T ==> p) <=> p``,
    bossLib.DECIDE ``(p ==> T) <=> T``,
    bossLib.DECIDE ``(F ==> p) <=> T``,
    bossLib.DECIDE ``(p ==> p) <=> T``,
    bossLib.DECIDE ``((p <=> q) ==> r) <=> (r \/ (q <=> ~p))``,

    bossLib.DECIDE ``~T <=> F``,
    bossLib.DECIDE ``~F <=> T``,
    bossLib.DECIDE ``~~p <=> p``,

    bossLib.DECIDE ``p \/ q <=> q \/ p``,
    bossLib.DECIDE ``p \/ T <=> T``,
    bossLib.DECIDE ``p \/ ~p <=> T``,
    bossLib.DECIDE ``~p \/ p <=> T``,
    bossLib.DECIDE ``T \/ p <=> T``,
    bossLib.DECIDE ``p \/ F <=> p``,
    bossLib.DECIDE ``F \/ p <=> p``,

    bossLib.DECIDE ``p /\ q <=> q /\ p``,
    bossLib.DECIDE ``p /\ T <=> p``,
    bossLib.DECIDE ``T /\ p <=> p``,
    bossLib.DECIDE ``p /\ F <=> F``,
    bossLib.DECIDE ``F /\ p <=> F``,
    bossLib.DECIDE ``p /\ q <=> ~(~p \/ ~q)``,
    bossLib.DECIDE ``~p /\ q <=> ~(p \/ ~q)``,
    bossLib.DECIDE ``p /\ ~q <=> ~(~p \/ q)``,
    bossLib.DECIDE ``~p /\ ~q <=> ~(p \/ q)``,
    bossLib.DECIDE ``p /\ q <=> ~(~q \/ ~p)``,
    bossLib.DECIDE ``~p /\ q <=> ~(~q \/ p)``,
    bossLib.DECIDE ``p /\ ~q <=> ~(q \/ ~p)``,
    bossLib.DECIDE ``~p /\ ~q <=> ~(q \/ p)``,

    simpLib.SIMP_PROVE bossLib.list_ss [] ``ALL_DISTINCT [x; x] <=> F``,
    simpLib.SIMP_PROVE bossLib.list_ss [] ``ALL_DISTINCT [x; y] <=> x <> y``,
    simpLib.SIMP_PROVE bossLib.list_ss [boolTheory.EQ_SYM_EQ]
      ``ALL_DISTINCT [x; y] <=> y <> x``,

    intLib.ARITH_PROVE ``((x :int) = y) <=> (x + -1 * y = 0)``,
    intLib.ARITH_PROVE ``((x :int) = y + z) <=> (x + -1 * z = y)``,
    intLib.ARITH_PROVE ``((x :int) = y + -1 * z) <=> (x + (-1 * y + z) = 0)``,
    intLib.ARITH_PROVE ``((x :int) = -1 * y + z) <=> (y + (-1 * z + x) = 0)``,
    intLib.ARITH_PROVE ``((x :int) = y + z) <=> (x + (-1 * y + -1 * z) = 0)``,
    intLib.ARITH_PROVE ``((x :int) = y + z) <=> (y + (z + -1 * x) = 0)``,
    intLib.ARITH_PROVE ``((x :int) = y + z) <=> (y + (-1 * x + z) = 0)``,
    intLib.ARITH_PROVE ``((x :int) = y + z) <=> (z + -1 * x = -y)``,
    intLib.ARITH_PROVE ``((x :int) = -y + z) <=> (z + -1 * x = y)``,
    intLib.ARITH_PROVE ``(-1 * (x :int) = -y) <=> (x = y)``,
    intLib.ARITH_PROVE ``(-1 * (x :int) + y = z) <=> (x + -1 * y = -z)``,
    intLib.ARITH_PROVE ``((x :int) + y = 0) <=> (y = -x)``,
    intLib.ARITH_PROVE ``((x :int) + y = z) <=> (y + -1 * z = -x)``,
    intLib.ARITH_PROVE ``((a :int) + (-1 * x + (v * y + w * z)) = 0) <=>
      (x + (-v * y + -w * z) = a)``,

    intLib.ARITH_PROVE ``0 + (x :int) = x``,
    intLib.ARITH_PROVE ``(x :int) + 0 = x``,
    intLib.ARITH_PROVE ``(x :int) + y = y + x``,
    intLib.ARITH_PROVE ``(x :int) + x = 2 * x``,
    intLib.ARITH_PROVE ``(x :int) + y + z = x + (y + z)``,
    intLib.ARITH_PROVE ``(x :int) + y + z = x + (z + y)``,
    intLib.ARITH_PROVE ``(x :int) + (y + z) = y + (z + x)``,
    intLib.ARITH_PROVE ``(x :int) + (y + z) = y + (x + z)``,
    intLib.ARITH_PROVE ``(x :int) + (y + (z + u)) = y + (z + (u + x))``,

    intLib.ARITH_PROVE ``(x :int) >= x <=> T``,
    intLib.ARITH_PROVE ``(x :int) >= y <=> x + -1 * y >= 0``,
    intLib.ARITH_PROVE ``(x :int) >= y <=> y + -1 * x <= 0``,
    intLib.ARITH_PROVE ``(x :int) >= y + z <=> y + (z + -1 * x) <= 0``,
    intLib.ARITH_PROVE ``-1 * (x :int) >= 0 <=> x <= 0``,
    intLib.ARITH_PROVE ``-1 * (x :int) >= -y <=> x <= y``,
    intLib.ARITH_PROVE ``-1 * (x :int) + y >= 0 <=> x + -1 * y <= 0``,
    intLib.ARITH_PROVE ``(x :int) + -1 * y >= 0 <=> y <= x``,

    intLib.ARITH_PROVE ``(x :int) > y <=> ~(y >= x)``,
    intLib.ARITH_PROVE ``(x :int) > y <=> ~(x <= y)``,
    intLib.ARITH_PROVE ``(x :int) > y <=> ~(x + -1 * y <= 0)``,
    intLib.ARITH_PROVE ``(x :int) > y <=> ~(y + -1 * x >= 0)``,
    intLib.ARITH_PROVE ``(x :int) > y + z <=> ~(z + -1 * x >= -y)``,

    intLib.ARITH_PROVE ``x <= (x :int) <=> T``,
    intLib.ARITH_PROVE ``0 <= (1 :int) <=> T``,
    intLib.ARITH_PROVE ``(x :int) <= y <=> y >= x``,
    intLib.ARITH_PROVE ``0 <= -(x :int) + y <=> y >= x``,
    intLib.ARITH_PROVE ``-1 * (x :int) <= 0 <=> x >= 0``,
    intLib.ARITH_PROVE ``(x :int) <= y <=> x + -1 * y <= 0``,
    intLib.ARITH_PROVE ``(x :int) <= y <=> y + -1 * x >= 0``,
    intLib.ARITH_PROVE ``-1 * (x :int) + y <= 0 <=> x + -1 * y >= 0``,
    intLib.ARITH_PROVE ``-1 * (x :int) + y <= -z <=> x + -1 * y >= z``,
    intLib.ARITH_PROVE ``-(x :int) + y <= z <=> y + -1 * z <= x``,
    intLib.ARITH_PROVE ``(x :int) + -1 * y <= z <=>
      x + (-1 * y + -1 * z) <= 0``,
    intLib.ARITH_PROVE ``(x :int) <= y + z <=> x + -1 * z <= y``,
    intLib.ARITH_PROVE ``(x :int) <= y + z <=> z + -1 * x >= -y``,
    intLib.ARITH_PROVE ``(x :int) <= y + z <=> x + (-1 * y + -1 * z) <= 0``,

    intLib.ARITH_PROVE ``(x :int) < y <=> ~(y <= x)``,
    intLib.ARITH_PROVE ``(x :int) < y <=> ~(x >= y)``,
    intLib.ARITH_PROVE ``(x :int) < y <=> ~(y + -1 * x <= 0)``,
    intLib.ARITH_PROVE ``(x :int) < y <=> ~(x + -1 * y >= 0)``,
    intLib.ARITH_PROVE ``(x :int) < y + -1 * z <=> ~(x + -1 * y + z >= 0)``,
    intLib.ARITH_PROVE ``(x :int) < y + -1 * z <=> ~(x + (-1 * y + z) >= 0)``,
    intLib.ARITH_PROVE ``(x :int) < -y + z <=> ~(z + -1 * x <= y)``,
    intLib.ARITH_PROVE ``(x :int) < -y + (z + u) <=> ~(z + (u + -1 * x) <= y)``,
    intLib.ARITH_PROVE ``(x :int) < -y + (z + (u + v)) <=>
      ~(z + (u + (v + -1 * x)) <= y)``,

    intLib.ARITH_PROVE ``-(x :int) + y < z <=> ~(y + -1 * z >= x)``,
    intLib.ARITH_PROVE ``(x :int) + y < z <=> ~(z + -1 * y <= x)``,
    intLib.ARITH_PROVE ``0 < -(x :int) + y <=> ~(y <= x)``,

    intLib.ARITH_PROVE ``(x :int) - 0 = x``,
    intLib.ARITH_PROVE ``0 - (x :int) = -x``,
    intLib.ARITH_PROVE ``0 - (x :int) = -1 * x``,
    intLib.ARITH_PROVE ``(x :int) - y = -y + x``,
    intLib.ARITH_PROVE ``(x :int) - y = x + -1 * y``,
    intLib.ARITH_PROVE ``(x :int) - y = -1 * y + x``,
    intLib.ARITH_PROVE ``(x :int) - 1 = -1 + x``,
    intLib.ARITH_PROVE ``(x :int) + y - z = x + (y + -1 * z)``,
    intLib.ARITH_PROVE ``(x :int) + y - z = x + (-1 * z + y)``,

    realLib.REAL_ARITH ``(0 = -u * (x :real)) <=> (u * x = 0)``,
    realLib.REAL_ARITH ``(a = -u * (x :real)) <=> (u * x = -a)``,
    realLib.REAL_ARITH ``((a :real) = x + (y + z)) <=>
      (x + (y + (-1 * a + z)) = 0)``,
    realLib.REAL_ARITH ``((a :real) = x + (y + z)) <=>
      (x + (y + (z + -1 * a)) = 0)``,
    realLib.REAL_ARITH ``((a :real) = -u * y + v * z) <=>
      (u * y + (-v * z + a) = 0)``,
    realLib.REAL_ARITH ``((a :real) = -u * y + -v * z) <=>
      (u * y + (a + v * z) = 0)``,
    realLib.REAL_ARITH ``(-(a :real) = -u * x + v * y) <=>
      (u * x + -v * y = a)``,
    realLib.REAL_ARITH ``((a :real) = -u * x + (-v * y + w * z)) <=>
      (u * x + (v * y + (-w * z + a)) = 0)``,
    realLib.REAL_ARITH ``((a :real) = -u * x + (v * y + w * z)) <=>
      (u * x + (-v * y + -w * z) = -a)``,
    realLib.REAL_ARITH ``((a :real) = -u * x + (v * y + -w * z)) <=>
      (u * x + (-v * y + w * z) = -a)``,
    realLib.REAL_ARITH ``((a :real) = -u * x + (-v * y + w * z)) <=>
      (u * x + (v * y + -w * z) = -a)``,
    realLib.REAL_ARITH ``((a :real) = -u * x + (-v * y + -w * z)) <=>
      (u * x + (v * y + w * z) = -a)``,
    realLib.REAL_ARITH ``(-(a :real) = -u * x + (v * y + w * z)) <=>
      (u * x + (-v * y + -w * z) = a)``,
    realLib.REAL_ARITH ``(-(a :real) = -u * x + (v * y + -w * z)) <=>
      (u * x + (-v * y + w * z) = a)``,
    realLib.REAL_ARITH ``(-(a :real) = -u * x + (-v * y + w * z)) <=>
      (u * x + (v * y + -w * z) = a)``,
    realLib.REAL_ARITH ``(-(a :real) = -u * x + (-v * y + -w * z)) <=>
      (u * x + (v * y + w * z) = a)``,
    realLib.REAL_ARITH ``((a :real) = -u * x + (-1 * y + w * z)) <=>
      (u * x + (y + -w * z) = -a)``,
    realLib.REAL_ARITH ``((a :real) = -u * x + (-1 * y + -w * z)) <=>
      (u * x + (y + w * z) = -a)``,
    realLib.REAL_ARITH ``(-u * (x :real) + -v * y = -a) <=>
      (u * x + v * y = a)``,
    realLib.REAL_ARITH ``(-1 * (x :real) + (-v * y + -w * z) = -a) <=>
      (x + (v * y + w * z) = a)``,
    realLib.REAL_ARITH ``(-u * (x :real) + (v * y + w * z) = -a) <=>
      (u * x + (-v * y + -w * z) = a)``,
    realLib.REAL_ARITH ``(-u * (x :real) + (-v * y + w * z) = -a) <=>
      (u * x + (v * y + -w * z) = a)``,
    realLib.REAL_ARITH ``(-u * (x :real) + (-v * y + -w * z) = -a) <=>
      (u * x + (v * y + w * z) = a)``,

    realLib.REAL_ARITH ``(x :real) + -1 * y >= 0 <=> y <= x``,
    realLib.REAL_ARITH ``(x :real) >= y <=> x + -1 * y >= 0``,

    realLib.REAL_ARITH ``(x :real) > y <=> ~(x + -1 * y <= 0)``,

    realLib.REAL_ARITH ``(x :real) <= y <=> x + -1 * y <= 0``,
    realLib.REAL_ARITH ``(x :real) <= y + z <=> x + -1 * z <= y``,
    realLib.REAL_ARITH ``-u * (x :real) <= a <=> u * x >= -a``,
    realLib.REAL_ARITH ``-u * (x :real) <= -a <=> u * x >= a``,
    realLib.REAL_ARITH ``-u * (x :real) + v * y <= 0 <=> u * x + -v * y >= 0``,
    realLib.REAL_ARITH ``-u * (x :real) + v * y <= a <=> u * x + -v * y >= -a``,
    realLib.REAL_ARITH ``-u * (x :real) + v * y <= -a <=> u * x + -v * y >= a``,
    realLib.REAL_ARITH ``-u * (x :real) + -v * y <= a <=> u * x + v * y >= -a``,
    realLib.REAL_ARITH ``-u * (x :real) + -v * y <= -a <=> u * x + v * y >= a``,
    realLib.REAL_ARITH ``-u * (x :real) + (v * y + w * z) <= 0 <=>
      u * x + (-v * y + -w * z) >= 0``,
    realLib.REAL_ARITH ``-u * (x :real) + (v * y + -w * z) <= 0 <=>
      u * x + (-v * y + w * z) >= 0``,
    realLib.REAL_ARITH ``-u * (x :real) + (-v * y + w * z) <= 0 <=>
      u * x + (v * y + -w * z) >= 0``,
    realLib.REAL_ARITH ``-u * (x :real) + (-v * y + -w * z) <= 0 <=>
      u * x + (v * y + w * z) >= 0``,
    realLib.REAL_ARITH ``-u * (x :real) + (v * y + w * z) <= a <=>
      u * x + (-v * y + -w * z) >= -a``,
    realLib.REAL_ARITH ``-u * (x :real) + (v * y + w * z) <= -a <=>
      u * x + (-v * y + -w * z) >= a``,
    realLib.REAL_ARITH ``-u * (x :real) + (v * y + -w * z) <= a <=>
      u * x + (-v * y + w * z) >= -a``,
    realLib.REAL_ARITH ``-u * (x :real) + (v * y + -w * z) <= -a <=>
      u * x + (-v * y + w * z) >= a``,
    realLib.REAL_ARITH ``-u * (x :real) + (-v * y + w * z) <= a <=>
      u * x + (v * y + -w * z) >= -a``,
    realLib.REAL_ARITH ``-u * (x :real) + (-v * y + w * z) <= -a <=>
      u * x + (v * y + -w * z) >= a``,
    realLib.REAL_ARITH ``-u * (x :real) + (-v * y + -w * z) <= a <=>
      u * x + (v * y + w * z) >= -a``,
    realLib.REAL_ARITH ``-u * (x :real) + (-v * y + -w * z) <= -a <=>
      u * x + (v * y + w * z) >= a``,
    realLib.REAL_ARITH ``(-1 * (x :real) + (v * y + w * z) <= -a) <=>
      (x + (-v * y + -w * z) >= a)``,

    realLib.REAL_ARITH ``(x :real) < y <=> ~(x >= y)``,
    realLib.REAL_ARITH ``-u * (x :real) < a <=> ~(u * x <= -a)``,
    realLib.REAL_ARITH ``-u * (x :real) < -a <=> ~(u * x <= a)``,
    realLib.REAL_ARITH ``-u * (x :real) + v * y < 0 <=>
      ~(u * x + -v * y <= 0)``,
    realLib.REAL_ARITH ``-u * (x :real) + -v * y < 0 <=>
      ~(u * x + v * y <= 0)``,
    realLib.REAL_ARITH ``-u * (x :real) + v * y < a <=>
      ~(u * x + -v * y <= -a)``,
    realLib.REAL_ARITH ``-u * (x :real) + v * y < -a <=>
      ~(u * x + -v * y <= a)``,
    realLib.REAL_ARITH ``-u * (x :real) + -v * y < a <=>
      ~(u * x + v * y <= -a)``,
    realLib.REAL_ARITH ``-u * (x :real) + -v * y < -a <=>
      ~(u * x + v * y <= a)``,
    realLib.REAL_ARITH ``-u * (x :real) + (v * y + w * z) < a <=>
      ~(u * x + (-v * y + -w * z) <= -a)``,
    realLib.REAL_ARITH ``-u * (x :real) + (v * y + w * z) < -a <=>
      ~(u * x + (-v * y + -w * z) <= a)``,
    realLib.REAL_ARITH ``-u * (x :real) + (v * y + -w * z) < a <=>
      ~(u * x + (-v * y + w * z) <= -a)``,
    realLib.REAL_ARITH ``-u * (x :real) + (v * y + -w * z) < -a <=>
      ~(u * x + (-v * y + w * z) <= a)``,
    realLib.REAL_ARITH ``-u * (x :real) + (-v * y + w * z) < a <=>
      ~(u * x + (v * y + -w * z) <= -a)``,
    realLib.REAL_ARITH ``-u * (x :real) + (-v * y + w * z) < -a <=>
      ~(u * x + (v * y + -w * z) <= a)``,
    realLib.REAL_ARITH ``-u * (x :real) + (-v * y + -w * z) < a <=>
      ~(u * x + (v * y + w * z) <= -a)``,
    realLib.REAL_ARITH ``-u * (x :real) + (-v * y + -w * z) < -a <=>
      ~(u * x + (v * y + w * z) <= a)``,
    realLib.REAL_ARITH ``-u * (x :real) + (-v * y + w * z) < 0 <=>
      ~(u * x + (v * y + -w * z) <= 0)``,
    realLib.REAL_ARITH ``-u * (x :real) + (-v * y + -w * z) < 0 <=>
      ~(u * x + (v * y + w * z) <= 0)``,
    realLib.REAL_ARITH ``-1 * (x :real) + (v * y + w * z) < a <=>
      ~(x + (-v * y + -w * z) <= -a)``,
    realLib.REAL_ARITH ``-1 * (x :real) + (v * y + w * z) < -a <=>
      ~(x + (-v * y + -w * z) <= a)``,
    realLib.REAL_ARITH ``-1 * (x :real) + (v * y + -w * z) < a <=>
      ~(x + (-v * y + w * z) <= -a)``,
    realLib.REAL_ARITH ``-1 * (x :real) + (v * y + -w * z) < -a <=>
      ~(x + (-v * y + w * z) <= a)``,
    realLib.REAL_ARITH ``-1 * (x :real) + (-v * y + w * z) < a <=>
      ~(x + (v * y + -w * z) <= -a)``,
    realLib.REAL_ARITH ``-1 * (x :real) + (-v * y + w * z) < -a <=>
      ~(x + (v * y + -w * z) <= a)``,
    realLib.REAL_ARITH ``-1 * (x :real) + (-v * y + -w * z) < a <=>
      ~(x + (v * y + w * z) <= -a)``,
    realLib.REAL_ARITH ``-1 * (x :real) + (-v * y + -w * z) < -a <=>
      ~(x + (v * y + w * z) <= a)``,
    realLib.REAL_ARITH ``-u * (x :real) + (-1 * y + -w * z) < -a <=>
      ~(u * x + (y + w * z) <= a)``,
    realLib.REAL_ARITH ``-u * (x :real) + (v * y + -1 * z) < -a <=>
      ~(u * x + (-v * y + z) <= a)``,

    realLib.REAL_ARITH ``0 + (x :real) = x``,
    realLib.REAL_ARITH ``(x :real) + 0 = x``,
    realLib.REAL_ARITH ``(x :real) + y = y + x``,
    realLib.REAL_ARITH ``(x :real) + x = 2 * x``,
    realLib.REAL_ARITH ``(x :real) + y + z = x + (y + z)``,
    realLib.REAL_ARITH ``(x :real) + y + z = x + (z + y)``,
    realLib.REAL_ARITH ``(x :real) + (y + z) = y + (z + x)``,
    realLib.REAL_ARITH ``(x :real) + (y + z) = y + (x + z)``,

    realLib.REAL_ARITH ``0 - (x :real) = -x``,
    realLib.REAL_ARITH ``0 - u * (x :real) = -u * x``,
    realLib.REAL_ARITH ``(x :real) - 0 = x``,
    realLib.REAL_ARITH ``(x :real) - y = x + -1 * y``,
    realLib.REAL_ARITH ``(x :real) - y = -1 * y + x``,
    realLib.REAL_ARITH ``(x :real) - u * y = x + -u * y``,
    realLib.REAL_ARITH ``(x :real) - u * y = -u * y + x``,
    realLib.REAL_ARITH ``(x :real) + y - z = x + (y + -1 * z)``,
    realLib.REAL_ARITH ``(x :real) + y - z = x + (-1 * z + y)``,
    realLib.REAL_ARITH ``(x :real) + y - u * z = -u * z + (x + y)``,
    realLib.REAL_ARITH ``(x :real) + y - u * z = x + (-u * z + y)``,
    realLib.REAL_ARITH ``(x :real) + y - u * z = x + (y + -u * z)``,

    realLib.REAL_ARITH ``0 * (x :real) = 0``,
    realLib.REAL_ARITH ``1 * (x :real) = x``
  ]

  val th_lemma_thms = thm_net_from_list
  [
    intLib.ARITH_PROVE ``((x :int) <> y) \/ (x <= y)``,
    intLib.ARITH_PROVE ``((x :int) <> y) \/ (x >= y)``,
    intLib.ARITH_PROVE ``((x :int) <> y) \/ (x + -1 * y >= 0)``,
    intLib.ARITH_PROVE ``((x :int) <> y) \/ (x + -1 * y <= 0)``,
    intLib.ARITH_PROVE ``((x :int) = y) \/ ~(x <= y) \/ ~(x >= y)``,
    intLib.ARITH_PROVE ``~((x :int) <= 0) \/ x <= 1``,
    intLib.ARITH_PROVE ``~((x :int) <= -1) \/ x <= 0``,
    intLib.ARITH_PROVE ``~((x :int) >= 0) \/ x >= -1``,
    intLib.ARITH_PROVE ``~((x :int) >= 0) \/ ~(x <= -1)``,
    intLib.ARITH_PROVE ``(x :int) >= y \/ x <= y``,

    realLib.REAL_ARITH ``(x :real) <> y \/ x + -1 * y >= 0``
  ]

end
