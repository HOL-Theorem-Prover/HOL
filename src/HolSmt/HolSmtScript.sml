(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Various theorems for HolSmtLib. *)

structure HolSmtScript =
struct

  val D = bossLib.DECIDE
  val P = bossLib.PROVE []
  val S = simpLib.SIMP_PROVE bossLib.list_ss
  val A = intLib.ARITH_PROVE
  val R = realLib.REAL_ARITH

  val s = Theory.save_thm

  val _ = Theory.new_theory "HolSmt"

  (* used for Z3 proof replay *)

  val _ = s ("ALL_DISTINCT_NIL", S [] ``ALL_DISTINCT [] = T``)
  val _ = s ("ALL_DISTINCT_CONS", S []
    ``!h t. ALL_DISTINCT (h::t) = ~MEM h t /\ ALL_DISTINCT t``)
  val _ = s ("NOT_MEM_NIL", S [] ``!x. ~MEM x [] = T``)
  val _ = s ("NOT_MEM_CONS", S []
    ``!x h t. ~MEM x (h::t) = (x <> h) /\ ~MEM x t``)
  val _ = s ("NOT_MEM_CONS_SWAP", S [boolTheory.EQ_SYM_EQ]
    ``!x h t. ~MEM x (h::t) = (h <> x) /\ ~MEM x t``)
  val _ = s ("AND_T", D ``!p. p /\ T <=> p``)
  val _ = s ("T_AND", D ``!p q. (T /\ p <=> T /\ q) ==> (p <=> q)``)
  val _ = s ("F_OR", D ``!p q. (F \/ p <=> F \/ q) ==> (p <=> q)``)
  val _ = s ("CONJ_CONG", D
    ``!p q r s. (p <=> q) ==> (r <=> s) ==> (p /\ r <=> q /\ s)``)
  val _ = s ("NOT_NOT_ELIM", D ``!p. ~~p ==> p``)
  val _ = s ("NOT_FALSE", D ``!p. p ==> ~p ==> F``)
  val _ = s ("NNF_CONJ", D
    ``!p q r s. (~p <=> r) ==> (~q <=> s) ==> (~(p /\ q) <=> r \/ s)``)
  val _ = s ("NNF_DISJ", D
    ``!p q r s. (~p <=> r) ==> (~q <=> s) ==> (~(p \/ q) <=> r /\ s)``)
  val _ = s ("NNF_NOT_NOT", D ``!p q. (p <=> q) ==> (~~p <=> q)``)
  val _ = s ("NEG_IFF_1", D ``!p q. (p <=> q) ==> ~(q <=> ~p)``)
  val _ = s ("NEG_IFF_2", D ``!p q. ~(p <=> ~q) ==> (q <=> p)``)
  val _ = s ("DISJ_ELIM_1", D ``!p q r. (p \/ q ==> r) ==> p ==> r``)
  val _ = s ("DISJ_ELIM_2", D ``!p q r. (p \/ q ==> r) ==> q ==> r``)
  val _ = s ("IMP_DISJ_1", D ``!p q. (p ==> q) ==> ~p \/ q``)
  val _ = s ("IMP_DISJ_2", D ``!p q. (~p ==> q) ==> p \/ q``)
  val _ = s ("IMP_FALSE", D ``!p. (~p ==> F) ==> p``)

  (* used for Z3's proof rule def-axiom *)

  val _ = s ("th001", D ``~(p <=> q) \/ ~p \/ q``)
  val _ = s ("th002", D ``~(p <=> q) \/ p \/ ~q``)
  val _ = s ("th003", D ``(p <=> ~q) \/ ~p \/ q``)
  val _ = s ("th003a", D ``(p <=> q) \/ ~p \/ ~q``)
  val _ = s ("th004", D ``(p <=> q) \/ p \/ q``)
  val _ = s ("th005", D ``~(~p <=> q) \/ p \/ q``)
  val _ = s ("th006", D ``~(p <=> ~q) \/ p \/ q``)
  val _ = s ("th007", D ``~q \/ p \/ ~(q <=> p)``)
  val _ = s ("th008", D ``q \/ p \/ ~(q <=> ~p)``)
  val _ = s ("th009", P ``p \/ (x = if p then y else x)``)
  val _ = s ("th010", P ``~p \/ (x = if p then x else y)``)
  val _ = s ("th011", P ``p \/ q \/ ~(if p then r else q)``)
  val _ = s ("th012", P ``~p \/ q \/ ~(if p then q else r)``)
  val _ = s ("th013", P ``(if p then q else r) \/ ~p \/ ~q``)
  val _ = s ("th014", P ``(if p then q else r) \/ p \/ ~r``)
  val _ = s ("th015", P ``~(if p then q else r) \/ ~p \/ q``)
  val _ = s ("th016", P ``~(if p then q else r) \/ p \/ r``)

  (* used for Z3's proof rule rewrite *)

  val _ = s ("th017", P ``(x = y) <=> (y = x)``)
  val _ = s ("th018", P ``(x = x) <=> T``)
  val _ = s ("th019", D ``(p <=> T) <=> p``)
  val _ = s ("th020", D ``(p <=> F) <=> ~p``)
  val _ = s ("th021", D ``(~p <=> ~q) <=> (p <=> q)``)

  val _ = s ("th022", P ``(if ~p then x else y) = (if p then y else x)``)

  val _ = s ("th023", D ``(~p ==> q) <=> (p \/ q)``)
  val _ = s ("th024", D ``(~p ==> q) <=> (q \/ p)``)
  val _ = s ("th025", D ``(p ==> q) <=> (~p \/ q)``)
  val _ = s ("th026", D ``(p ==> q) <=> (q \/ ~p)``)
  val _ = s ("th027", D ``(T ==> p) <=> p``)
  val _ = s ("th028", D ``(p ==> T) <=> T``)
  val _ = s ("th029", D ``(F ==> p) <=> T``)
  val _ = s ("th030", D ``(p ==> p) <=> T``)
  val _ = s ("th031", D ``((p <=> q) ==> r) <=> (r \/ (q <=> ~p))``)

  val _ = s ("th032", D ``~T <=> F``)
  val _ = s ("th033", D ``~F <=> T``)
  val _ = s ("th034", D ``~~p <=> p``)

  val _ = s ("th035", D ``p \/ q <=> q \/ p``)
  val _ = s ("th036", D ``p \/ T <=> T``)
  val _ = s ("th037", D ``p \/ ~p <=> T``)
  val _ = s ("th038", D ``~p \/ p <=> T``)
  val _ = s ("th039", D ``T \/ p <=> T``)
  val _ = s ("th040", D ``p \/ F <=> p``)
  val _ = s ("th041", D ``F \/ p <=> p``)

  val _ = s ("th042", D ``p /\ q <=> q /\ p``)
  val _ = s ("th043", D ``p /\ T <=> p``)
  val _ = s ("th044", D ``T /\ p <=> p``)
  val _ = s ("th045", D ``p /\ F <=> F``)
  val _ = s ("th046", D ``F /\ p <=> F``)
  val _ = s ("th047", D ``p /\ q <=> ~(~p \/ ~q)``)
  val _ = s ("th048", D ``~p /\ q <=> ~(p \/ ~q)``)
  val _ = s ("th049", D ``p /\ ~q <=> ~(~p \/ q)``)
  val _ = s ("th050", D ``~p /\ ~q <=> ~(p \/ q)``)
  val _ = s ("th051", D ``p /\ q <=> ~(~q \/ ~p)``)
  val _ = s ("th052", D ``~p /\ q <=> ~(~q \/ p)``)
  val _ = s ("th053", D ``p /\ ~q <=> ~(q \/ ~p)``)
  val _ = s ("th054", D ``~p /\ ~q <=> ~(q \/ p)``)

  val _ = s ("th055", S [] ``ALL_DISTINCT [x; x] <=> F``)
  val _ = s ("th056", S [] ``ALL_DISTINCT [x; y] <=> x <> y``)
  val _ = s ("th057", S [boolTheory.EQ_SYM_EQ] ``ALL_DISTINCT [x; y] <=> y <> x``)

  val _ = s ("th058", A ``((x :int) = y) <=> (x + -1 * y = 0)``)
  val _ = s ("th059", A ``((x :int) = y + z) <=> (x + -1 * z = y)``)
  val _ = s ("th060", A ``((x :int) = y + -1 * z) <=> (x + (-1 * y + z) = 0)``)
  val _ = s ("th061", A ``((x :int) = -1 * y + z) <=> (y + (-1 * z + x) = 0)``)
  val _ = s ("th062", A ``((x :int) = y + z) <=> (x + (-1 * y + -1 * z) = 0)``)
  val _ = s ("th063", A ``((x :int) = y + z) <=> (y + (z + -1 * x) = 0)``)
  val _ = s ("th064", A ``((x :int) = y + z) <=> (y + (-1 * x + z) = 0)``)
  val _ = s ("th065", A ``((x :int) = y + z) <=> (z + -1 * x = -y)``)
  val _ = s ("th066", A ``((x :int) = -y + z) <=> (z + -1 * x = y)``)
  val _ = s ("th067", A ``(-1 * (x :int) = -y) <=> (x = y)``)
  val _ = s ("th068", A ``(-1 * (x :int) + y = z) <=> (x + -1 * y = -z)``)
  val _ = s ("th069", A ``((x :int) + y = 0) <=> (y = -x)``)
  val _ = s ("th070", A ``((x :int) + y = z) <=> (y + -1 * z = -x)``)
  val _ = s ("th071", A
    ``((a :int) + (-1 * x + (v * y + w * z)) = 0) <=> (x + (-v * y + -w * z) = a)``)

  val _ = s ("th072", A ``0 + (x :int) = x``)
  val _ = s ("th073", A ``(x :int) + 0 = x``)
  val _ = s ("th074", A ``(x :int) + y = y + x``)
  val _ = s ("th075", A ``(x :int) + x = 2 * x``)
  val _ = s ("th076", A ``(x :int) + y + z = x + (y + z)``)
  val _ = s ("th077", A ``(x :int) + y + z = x + (z + y)``)
  val _ = s ("th078", A ``(x :int) + (y + z) = y + (z + x)``)
  val _ = s ("th079", A ``(x :int) + (y + z) = y + (x + z)``)
  val _ = s ("th080", A ``(x :int) + (y + (z + u)) = y + (z + (u + x))``)

  val _ = s ("th081", A ``(x :int) >= x <=> T``)
  val _ = s ("th082", A ``(x :int) >= y <=> x + -1 * y >= 0``)
  val _ = s ("th083", A ``(x :int) >= y <=> y + -1 * x <= 0``)
  val _ = s ("th084", A ``(x :int) >= y + z <=> y + (z + -1 * x) <= 0``)
  val _ = s ("th085", A ``-1 * (x :int) >= 0 <=> x <= 0``)
  val _ = s ("th086", A ``-1 * (x :int) >= -y <=> x <= y``)
  val _ = s ("th087", A ``-1 * (x :int) + y >= 0 <=> x + -1 * y <= 0``)
  val _ = s ("th088", A ``(x :int) + -1 * y >= 0 <=> y <= x``)

  val _ = s ("th089", A ``(x :int) > y <=> ~(y >= x)``)
  val _ = s ("th090", A ``(x :int) > y <=> ~(x <= y)``)
  val _ = s ("th091", A ``(x :int) > y <=> ~(x + -1 * y <= 0)``)
  val _ = s ("th092", A ``(x :int) > y <=> ~(y + -1 * x >= 0)``)
  val _ = s ("th093", A ``(x :int) > y + z <=> ~(z + -1 * x >= -y)``)

  val _ = s ("th094", A ``x <= (x :int) <=> T``)
  val _ = s ("th095", A ``0 <= (1 :int) <=> T``)
  val _ = s ("th096", A ``(x :int) <= y <=> y >= x``)
  val _ = s ("th097", A ``0 <= -(x :int) + y <=> y >= x``)
  val _ = s ("th098", A ``-1 * (x :int) <= 0 <=> x >= 0``)
  val _ = s ("th099", A ``(x :int) <= y <=> x + -1 * y <= 0``)
  val _ = s ("th100", A ``(x :int) <= y <=> y + -1 * x >= 0``)
  val _ = s ("th101", A ``-1 * (x :int) + y <= 0 <=> x + -1 * y >= 0``)
  val _ = s ("th102", A ``-1 * (x :int) + y <= -z <=> x + -1 * y >= z``)
  val _ = s ("th103", A ``-(x :int) + y <= z <=> y + -1 * z <= x``)
  val _ = s ("th104", A ``(x :int) + -1 * y <= z <=> x + (-1 * y + -1 * z) <= 0``)
  val _ = s ("th105", A ``(x :int) <= y + z <=> x + -1 * z <= y``)
  val _ = s ("th106", A ``(x :int) <= y + z <=> z + -1 * x >= -y``)
  val _ = s ("th107", A ``(x :int) <= y + z <=> x + (-1 * y + -1 * z) <= 0``)

  val _ = s ("th108", A ``(x :int) < y <=> ~(y <= x)``)
  val _ = s ("th109", A ``(x :int) < y <=> ~(x >= y)``)
  val _ = s ("th110", A ``(x :int) < y <=> ~(y + -1 * x <= 0)``)
  val _ = s ("th111", A ``(x :int) < y <=> ~(x + -1 * y >= 0)``)
  val _ = s ("th112", A ``(x :int) < y + -1 * z <=> ~(x + -1 * y + z >= 0)``)
  val _ = s ("th113", A ``(x :int) < y + -1 * z <=> ~(x + (-1 * y + z) >= 0)``)
  val _ = s ("th114", A ``(x :int) < -y + z <=> ~(z + -1 * x <= y)``)
  val _ = s ("th115", A ``(x :int) < -y + (z + u) <=> ~(z + (u + -1 * x) <= y)``)
  val _ = s ("th116", A
    ``(x :int) < -y + (z + (u + v)) <=> ~(z + (u + (v + -1 * x)) <= y)``)

  val _ = s ("th117", A ``-(x :int) + y < z <=> ~(y + -1 * z >= x)``)
  val _ = s ("th118", A ``(x :int) + y < z <=> ~(z + -1 * y <= x)``)
  val _ = s ("th119", A ``0 < -(x :int) + y <=> ~(y <= x)``)

  val _ = s ("th120", A ``(x :int) - 0 = x``)
  val _ = s ("th121", A ``0 - (x :int) = -x``)
  val _ = s ("th122", A ``0 - (x :int) = -1 * x``)
  val _ = s ("th123", A ``(x :int) - y = -y + x``)
  val _ = s ("th124", A ``(x :int) - y = x + -1 * y``)
  val _ = s ("th125", A ``(x :int) - y = -1 * y + x``)
  val _ = s ("th126", A ``(x :int) - 1 = -1 + x``)
  val _ = s ("th127", A ``(x :int) + y - z = x + (y + -1 * z)``)
  val _ = s ("th128", A ``(x :int) + y - z = x + (-1 * z + y)``)

  val _ = s ("th129", R ``(0 = -u * (x :real)) <=> (u * x = 0)``)
  val _ = s ("th130", R ``(a = -u * (x :real)) <=> (u * x = -a)``)
  val _ = s ("th131", R ``((a :real) = x + (y + z)) <=> (x + (y + (-1 * a + z)) = 0)``)
  val _ = s ("th132", R ``((a :real) = x + (y + z)) <=> (x + (y + (z + -1 * a)) = 0)``)
  val _ = s ("th133", R ``((a :real) = -u * y + v * z) <=> (u * y + (-v * z + a) = 0)``)
  val _ = s ("th134", R ``((a :real) = -u * y + -v * z) <=> (u * y + (a + v * z) = 0)``)
  val _ = s ("th135", R ``(-(a :real) = -u * x + v * y) <=> (u * x + -v * y = a)``)
  val _ = s ("th136", R
    ``((a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + (-w * z + a)) = 0)``)
  val _ = s ("th137", R
    ``((a :real) = -u * x + (v * y + w * z)) <=> (u * x + (-v * y + -w * z) = -a)``)
  val _ = s ("th138", R
    ``((a :real) = -u * x + (v * y + -w * z)) <=> (u * x + (-v * y + w * z) = -a)``)
  val _ = s ("th139", R
    ``((a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + -w * z) = -a)``)
  val _ = s ("th140", R ``((a :real) = -u * x + (-v * y + -w * z)) <=> (u * x + (v * y + w * z) = -a)``)
  val _ = s ("th141", R ``(-(a :real) = -u * x + (v * y + w * z)) <=> (u * x + (-v * y + -w * z) = a)``)
  val _ = s ("th142", R ``(-(a :real) = -u * x + (v * y + -w * z)) <=> (u * x + (-v * y + w * z) = a)``)
  val _ = s ("th143", R ``(-(a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + -w * z) = a)``)
  val _ = s ("th144", R ``(-(a :real) = -u * x + (-v * y + -w * z)) <=> (u * x + (v * y + w * z) = a)``)
  val _ = s ("th145", R ``((a :real) = -u * x + (-1 * y + w * z)) <=> (u * x + (y + -w * z) = -a)``)
  val _ = s ("th146", R ``((a :real) = -u * x + (-1 * y + -w * z)) <=> (u * x + (y + w * z) = -a)``)
  val _ = s ("th147", R ``(-u * (x :real) + -v * y = -a) <=> (u * x + v * y = a)``)
  val _ = s ("th148", R ``(-1 * (x :real) + (-v * y + -w * z) = -a) <=> (x + (v * y + w * z) = a)``)
  val _ = s ("th149", R ``(-u * (x :real) + (v * y + w * z) = -a) <=> (u * x + (-v * y + -w * z) = a)``)
  val _ = s ("th150", R ``(-u * (x :real) + (-v * y + w * z) = -a) <=> (u * x + (v * y + -w * z) = a)``)
  val _ = s ("th151", R ``(-u * (x :real) + (-v * y + -w * z) = -a) <=> (u * x + (v * y + w * z) = a)``)

  val _ = s ("th152", R ``(x :real) + -1 * y >= 0 <=> y <= x``)
  val _ = s ("th153", R ``(x :real) >= y <=> x + -1 * y >= 0``)

  val _ = s ("th154", R ``(x :real) > y <=> ~(x + -1 * y <= 0)``)

  val _ = s ("th155", R ``(x :real) <= y <=> x + -1 * y <= 0``)
  val _ = s ("th156", R ``(x :real) <= y + z <=> x + -1 * z <= y``)
  val _ = s ("th157", R ``-u * (x :real) <= a <=> u * x >= -a``)
  val _ = s ("th158", R ``-u * (x :real) <= -a <=> u * x >= a``)
  val _ = s ("th159", R ``-u * (x :real) + v * y <= 0 <=> u * x + -v * y >= 0``)
  val _ = s ("th160", R ``-u * (x :real) + v * y <= a <=> u * x + -v * y >= -a``)
  val _ = s ("th161", R ``-u * (x :real) + v * y <= -a <=> u * x + -v * y >= a``)
  val _ = s ("th162", R ``-u * (x :real) + -v * y <= a <=> u * x + v * y >= -a``)
  val _ = s ("th163", R ``-u * (x :real) + -v * y <= -a <=> u * x + v * y >= a``)
  val _ = s ("th164", R
    ``-u * (x :real) + (v * y + w * z) <= 0 <=> u * x + (-v * y + -w * z) >= 0``)
  val _ = s ("th165", R
    ``-u * (x :real) + (v * y + -w * z) <= 0 <=> u * x + (-v * y + w * z) >= 0``)
  val _ = s ("th166", R
    ``-u * (x :real) + (-v * y + w * z) <= 0 <=> u * x + (v * y + -w * z) >= 0``)
  val _ = s ("th167", R
    ``-u * (x :real) + (-v * y + -w * z) <= 0 <=> u * x + (v * y + w * z) >= 0``)
  val _ = s ("th168", R
    ``-u * (x :real) + (v * y + w * z) <= a <=> u * x + (-v * y + -w * z) >= -a``)
  val _ = s ("th169", R
    ``-u * (x :real) + (v * y + w * z) <= -a <=> u * x + (-v * y + -w * z) >= a``)
  val _ = s ("th170", R
    ``-u * (x :real) + (v * y + -w * z) <= a <=> u * x + (-v * y + w * z) >= -a``)
  val _ = s ("th171", R
    ``-u * (x :real) + (v * y + -w * z) <= -a <=> u * x + (-v * y + w * z) >= a``)
  val _ = s ("th172", R
    ``-u * (x :real) + (-v * y + w * z) <= a <=> u * x + (v * y + -w * z) >= -a``)
  val _ = s ("th173", R
    ``-u * (x :real) + (-v * y + w * z) <= -a <=> u * x + (v * y + -w * z) >= a``)
  val _ = s ("th174", R
    ``-u * (x :real) + (-v * y + -w * z) <= a <=> u * x + (v * y + w * z) >= -a``)
  val _ = s ("th175", R
    ``-u * (x :real) + (-v * y + -w * z) <= -a <=> u * x + (v * y + w * z) >= a``)
  val _ = s ("th176", R
    ``(-1 * (x :real) + (v * y + w * z) <= -a) <=> (x + (-v * y + -w * z) >= a)``)

  val _ = s ("th177", R ``(x :real) < y <=> ~(x >= y)``)
  val _ = s ("th178", R ``-u * (x :real) < a <=> ~(u * x <= -a)``)
  val _ = s ("th179", R ``-u * (x :real) < -a <=> ~(u * x <= a)``)
  val _ = s ("th180", R ``-u * (x :real) + v * y < 0 <=> ~(u * x + -v * y <= 0)``)
  val _ = s ("th181", R ``-u * (x :real) + -v * y < 0 <=> ~(u * x + v * y <= 0)``)
  val _ = s ("th182", R ``-u * (x :real) + v * y < a <=> ~(u * x + -v * y <= -a)``)
  val _ = s ("th183", R ``-u * (x :real) + v * y < -a <=> ~(u * x + -v * y <= a)``)
  val _ = s ("th184", R ``-u * (x :real) + -v * y < a <=> ~(u * x + v * y <= -a)``)
  val _ = s ("th185", R ``-u * (x :real) + -v * y < -a <=> ~(u * x + v * y <= a)``)
  val _ = s ("th186", R
    ``-u * (x :real) + (v * y + w * z) < a <=> ~(u * x + (-v * y + -w * z) <= -a)``)
  val _ = s ("th187", R
    ``-u * (x :real) + (v * y + w * z) < -a <=> ~(u * x + (-v * y + -w * z) <= a)``)
  val _ = s ("th188", R
    ``-u * (x :real) + (v * y + -w * z) < a <=> ~(u * x + (-v * y + w * z) <= -a)``)
  val _ = s ("th189", R
    ``-u * (x :real) + (v * y + -w * z) < -a <=> ~(u * x + (-v * y + w * z) <= a)``)
  val _ = s ("th190", R
    ``-u * (x :real) + (-v * y + w * z) < a <=> ~(u * x + (v * y + -w * z) <= -a)``)
  val _ = s ("th191", R
    ``-u * (x :real) + (-v * y + w * z) < -a <=> ~(u * x + (v * y + -w * z) <= a)``)
  val _ = s ("th192", R
    ``-u * (x :real) + (-v * y + -w * z) < a <=> ~(u * x + (v * y + w * z) <= -a)``)
  val _ = s ("th193", R
    ``-u * (x :real) + (-v * y + -w * z) < -a <=> ~(u * x + (v * y + w * z) <= a)``)
  val _ = s ("th194", R
    ``-u * (x :real) + (-v * y + w * z) < 0 <=> ~(u * x + (v * y + -w * z) <= 0)``)
  val _ = s ("th195", R
    ``-u * (x :real) + (-v * y + -w * z) < 0 <=> ~(u * x + (v * y + w * z) <= 0)``)
  val _ = s ("th196", R
    ``-1 * (x :real) + (v * y + w * z) < a <=> ~(x + (-v * y + -w * z) <= -a)``)
  val _ = s ("th197", R
    ``-1 * (x :real) + (v * y + w * z) < -a <=> ~(x + (-v * y + -w * z) <= a)``)
  val _ = s ("th198", R
    ``-1 * (x :real) + (v * y + -w * z) < a <=> ~(x + (-v * y + w * z) <= -a)``)
  val _ = s ("th199", R
    ``-1 * (x :real) + (v * y + -w * z) < -a <=> ~(x + (-v * y + w * z) <= a)``)
  val _ = s ("th200", R
    ``-1 * (x :real) + (-v * y + w * z) < a <=> ~(x + (v * y + -w * z) <= -a)``)
  val _ = s ("th201", R
    ``-1 * (x :real) + (-v * y + w * z) < -a <=> ~(x + (v * y + -w * z) <= a)``)
  val _ = s ("th202", R
    ``-1 * (x :real) + (-v * y + -w * z) < a <=> ~(x + (v * y + w * z) <= -a)``)
  val _ = s ("th203", R
    ``-1 * (x :real) + (-v * y + -w * z) < -a <=> ~(x + (v * y + w * z) <= a)``)
  val _ = s ("th204", R
    ``-u * (x :real) + (-1 * y + -w * z) < -a <=> ~(u * x + (y + w * z) <= a)``)
  val _ = s ("th205", R
    ``-u * (x :real) + (v * y + -1 * z) < -a <=> ~(u * x + (-v * y + z) <= a)``)

  val _ = s ("th206", R ``0 + (x :real) = x``)
  val _ = s ("th207", R ``(x :real) + 0 = x``)
  val _ = s ("th208", R ``(x :real) + y = y + x``)
  val _ = s ("th209", R ``(x :real) + x = 2 * x``)
  val _ = s ("th210", R ``(x :real) + y + z = x + (y + z)``)
  val _ = s ("th211", R ``(x :real) + y + z = x + (z + y)``)
  val _ = s ("th212", R ``(x :real) + (y + z) = y + (z + x)``)
  val _ = s ("th213", R ``(x :real) + (y + z) = y + (x + z)``)

  val _ = s ("th214", R ``0 - (x :real) = -x``)
  val _ = s ("th215", R ``0 - u * (x :real) = -u * x``)
  val _ = s ("th216", R ``(x :real) - 0 = x``)
  val _ = s ("th217", R ``(x :real) - y = x + -1 * y``)
  val _ = s ("th218", R ``(x :real) - y = -1 * y + x``)
  val _ = s ("th219", R ``(x :real) - u * y = x + -u * y``)
  val _ = s ("th220", R ``(x :real) - u * y = -u * y + x``)
  val _ = s ("th221", R ``(x :real) + y - z = x + (y + -1 * z)``)
  val _ = s ("th222", R ``(x :real) + y - z = x + (-1 * z + y)``)
  val _ = s ("th223", R ``(x :real) + y - u * z = -u * z + (x + y)``)
  val _ = s ("th224", R ``(x :real) + y - u * z = x + (-u * z + y)``)
  val _ = s ("th225", R ``(x :real) + y - u * z = x + (y + -u * z)``)

  val _ = s ("th226", R ``0 * (x :real) = 0``)
  val _ = s ("th227", R ``1 * (x :real) = x``)

  (* used for Z3's proof rule th-lemma *)

  val _ = s ("th228", A ``((x :int) <> y) \/ (x <= y)``)
  val _ = s ("th229", A ``((x :int) <> y) \/ (x >= y)``)
  val _ = s ("th230", A ``((x :int) <> y) \/ (x + -1 * y >= 0)``)
  val _ = s ("th231", A ``((x :int) <> y) \/ (x + -1 * y <= 0)``)
  val _ = s ("th232", A ``((x :int) = y) \/ ~(x <= y) \/ ~(x >= y)``)
  val _ = s ("th233", A ``~((x :int) <= 0) \/ x <= 1``)
  val _ = s ("th234", A ``~((x :int) <= -1) \/ x <= 0``)
  val _ = s ("th235", A ``~((x :int) >= 0) \/ x >= -1``)
  val _ = s ("th236", A ``~((x :int) >= 0) \/ ~(x <= -1)``)
  val _ = s ("th237", A ``(x :int) >= y \/ x <= y``)

  val _ = s ("th238", R ``(x :real) <> y \/ x + -1 * y >= 0``)

  val _ = Theory.export_theory ()

end
