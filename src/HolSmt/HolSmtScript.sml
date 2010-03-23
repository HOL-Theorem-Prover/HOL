(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

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

  (* used for Z3 proof reconstruction *)

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

  val _ = s ("d001", D ``~(p <=> q) \/ ~p \/ q``)
  val _ = s ("d002", D ``~(p <=> q) \/ p \/ ~q``)
  val _ = s ("d003", D ``(p <=> ~q) \/ ~p \/ q``)
  val _ = s ("d004", D ``(~p <=> q) \/ p \/ ~q``)
  val _ = s ("d005", D ``(p <=> q) \/ ~p \/ ~q``)
  val _ = s ("d006", D ``(p <=> q) \/ p \/ q``)
  val _ = s ("d007", D ``~(~p <=> q) \/ p \/ q``)
  val _ = s ("d008", D ``~(p <=> ~q) \/ p \/ q``)
  val _ = s ("d009", D ``~q \/ p \/ ~(q <=> p)``)
  val _ = s ("d010", D ``q \/ p \/ ~(q <=> ~p)``)
  val _ = s ("d011", D ``~(~(p <=> q) <=> r) \/ ~p \/ q \/ r``)
  val _ = s ("d012", D ``~(~(p <=> q) <=> r) \/ p \/ ~q \/ r``)
  val _ = s ("d013", D ``~(~(p <=> q) <=> r) \/ p \/ q \/ ~r``)
  val _ = s ("d014", D ``(~p /\ ~q) \/ p \/ q``)
  val _ = s ("d015", D ``(~p /\ q) \/ p \/ ~q``)
  val _ = s ("d016", D ``(p /\ ~q) \/ ~p \/ q``)
  val _ = s ("d017", D ``(p /\ q) \/ ~p \/ ~q``)
  val _ = s ("d018", P ``p \/ (x = if p then y else x)``)
  val _ = s ("d019", P ``~p \/ (x = if p then x else y)``)
  val _ = s ("d020", P ``p \/ q \/ ~(if p then r else q)``)
  val _ = s ("d021", P ``~p \/ q \/ ~(if p then q else r)``)
  val _ = s ("d022", P ``(if p then q else r) \/ ~p \/ ~q``)
  val _ = s ("d023", P ``(if p then q else r) \/ p \/ ~r``)
  val _ = s ("d024", P ``~(if p then q else r) \/ ~p \/ q``)
  val _ = s ("d025", P ``~(if p then q else r) \/ p \/ r``)

  (* used for Z3's proof rule rewrite *)

  val _ = s ("r001", P ``(x = y) <=> (y = x)``)
  val _ = s ("r002", P ``(x = x) <=> T``)
  val _ = s ("r003", D ``(p <=> T) <=> p``)
  val _ = s ("r004", D ``(p <=> F) <=> ~p``)
  val _ = s ("r005", D ``(~p <=> ~q) <=> (p <=> q)``)

  val _ = s ("r006", P ``(if ~p then x else y) = (if p then y else x)``)

  val _ = s ("r007", D ``(~p ==> q) <=> (p \/ q)``)
  val _ = s ("r008", D ``(~p ==> q) <=> (q \/ p)``)
  val _ = s ("r009", D ``(p ==> q) <=> (~p \/ q)``)
  val _ = s ("r010", D ``(p ==> q) <=> (q \/ ~p)``)
  val _ = s ("r011", D ``(T ==> p) <=> p``)
  val _ = s ("r012", D ``(p ==> T) <=> T``)
  val _ = s ("r013", D ``(F ==> p) <=> T``)
  val _ = s ("r014", D ``(p ==> p) <=> T``)
  val _ = s ("r015", D ``((p <=> q) ==> r) <=> (r \/ (q <=> ~p))``)

  val _ = s ("r016", D ``~T <=> F``)
  val _ = s ("r017", D ``~F <=> T``)
  val _ = s ("r018", D ``~~p <=> p``)

  val _ = s ("r019", D ``p \/ q <=> q \/ p``)
  val _ = s ("r020", D ``p \/ T <=> T``)
  val _ = s ("r021", D ``p \/ ~p <=> T``)
  val _ = s ("r022", D ``~p \/ p <=> T``)
  val _ = s ("r023", D ``T \/ p <=> T``)
  val _ = s ("r024", D ``p \/ F <=> p``)
  val _ = s ("r025", D ``F \/ p <=> p``)

  val _ = s ("r026", D ``p /\ q <=> q /\ p``)
  val _ = s ("r027", D ``p /\ T <=> p``)
  val _ = s ("r028", D ``T /\ p <=> p``)
  val _ = s ("r029", D ``p /\ F <=> F``)
  val _ = s ("r030", D ``F /\ p <=> F``)
  val _ = s ("r031", D ``p /\ q <=> ~(~p \/ ~q)``)
  val _ = s ("r032", D ``~p /\ q <=> ~(p \/ ~q)``)
  val _ = s ("r033", D ``p /\ ~q <=> ~(~p \/ q)``)
  val _ = s ("r034", D ``~p /\ ~q <=> ~(p \/ q)``)
  val _ = s ("r035", D ``p /\ q <=> ~(~q \/ ~p)``)
  val _ = s ("r036", D ``~p /\ q <=> ~(~q \/ p)``)
  val _ = s ("r037", D ``p /\ ~q <=> ~(q \/ ~p)``)
  val _ = s ("r038", D ``~p /\ ~q <=> ~(q \/ p)``)

  val _ = s ("r039", S [] ``ALL_DISTINCT [x; x] <=> F``)
  val _ = s ("r040", S [] ``ALL_DISTINCT [x; y] <=> x <> y``)
  val _ = s ("r041", S [boolTheory.EQ_SYM_EQ] ``ALL_DISTINCT [x; y] <=> y <> x``)

  val _ = s ("r042", A ``((x :int) = y) <=> (x + -1 * y = 0)``)
  val _ = s ("r043", A ``((x :int) = y + z) <=> (x + -1 * z = y)``)
  val _ = s ("r044", A ``((x :int) = y + -1 * z) <=> (x + (-1 * y + z) = 0)``)
  val _ = s ("r045", A ``((x :int) = -1 * y + z) <=> (y + (-1 * z + x) = 0)``)
  val _ = s ("r046", A ``((x :int) = y + z) <=> (x + (-1 * y + -1 * z) = 0)``)
  val _ = s ("r047", A ``((x :int) = y + z) <=> (y + (z + -1 * x) = 0)``)
  val _ = s ("r048", A ``((x :int) = y + z) <=> (y + (-1 * x + z) = 0)``)
  val _ = s ("r049", A ``((x :int) = y + z) <=> (z + -1 * x = -y)``)
  val _ = s ("r050", A ``((x :int) = -y + z) <=> (z + -1 * x = y)``)
  val _ = s ("r051", A ``(-1 * (x :int) = -y) <=> (x = y)``)
  val _ = s ("r052", A ``(-1 * (x :int) + y = z) <=> (x + -1 * y = -z)``)
  val _ = s ("r053", A ``((x :int) + y = 0) <=> (y = -x)``)
  val _ = s ("r054", A ``((x :int) + y = z) <=> (y + -1 * z = -x)``)
  val _ = s ("r055", A
    ``((a :int) + (-1 * x + (v * y + w * z)) = 0) <=> (x + (-v * y + -w * z) = a)``)

  val _ = s ("r056", A ``0 + (x :int) = x``)
  val _ = s ("r057", A ``(x :int) + 0 = x``)
  val _ = s ("r058", A ``(x :int) + y = y + x``)
  val _ = s ("r059", A ``(x :int) + x = 2 * x``)
  val _ = s ("r060", A ``(x :int) + y + z = x + (y + z)``)
  val _ = s ("r061", A ``(x :int) + y + z = x + (z + y)``)
  val _ = s ("r062", A ``(x :int) + (y + z) = y + (z + x)``)
  val _ = s ("r063", A ``(x :int) + (y + z) = y + (x + z)``)
  val _ = s ("r064", A ``(x :int) + (y + (z + u)) = y + (z + (u + x))``)

  val _ = s ("r065", A ``(x :int) >= x <=> T``)
  val _ = s ("r066", A ``(x :int) >= y <=> x + -1 * y >= 0``)
  val _ = s ("r067", A ``(x :int) >= y <=> y + -1 * x <= 0``)
  val _ = s ("r068", A ``(x :int) >= y + z <=> y + (z + -1 * x) <= 0``)
  val _ = s ("r069", A ``-1 * (x :int) >= 0 <=> x <= 0``)
  val _ = s ("r070", A ``-1 * (x :int) >= -y <=> x <= y``)
  val _ = s ("r071", A ``-1 * (x :int) + y >= 0 <=> x + -1 * y <= 0``)
  val _ = s ("r072", A ``(x :int) + -1 * y >= 0 <=> y <= x``)

  val _ = s ("r073", A ``(x :int) > y <=> ~(y >= x)``)
  val _ = s ("r074", A ``(x :int) > y <=> ~(x <= y)``)
  val _ = s ("r075", A ``(x :int) > y <=> ~(x + -1 * y <= 0)``)
  val _ = s ("r076", A ``(x :int) > y <=> ~(y + -1 * x >= 0)``)
  val _ = s ("r077", A ``(x :int) > y + z <=> ~(z + -1 * x >= -y)``)

  val _ = s ("r078", A ``x <= (x :int) <=> T``)
  val _ = s ("r079", A ``0 <= (1 :int) <=> T``)
  val _ = s ("r080", A ``(x :int) <= y <=> y >= x``)
  val _ = s ("r081", A ``0 <= -(x :int) + y <=> y >= x``)
  val _ = s ("r082", A ``-1 * (x :int) <= 0 <=> x >= 0``)
  val _ = s ("r083", A ``(x :int) <= y <=> x + -1 * y <= 0``)
  val _ = s ("r084", A ``(x :int) <= y <=> y + -1 * x >= 0``)
  val _ = s ("r085", A ``-1 * (x :int) + y <= 0 <=> x + -1 * y >= 0``)
  val _ = s ("r086", A ``-1 * (x :int) + y <= -z <=> x + -1 * y >= z``)
  val _ = s ("r087", A ``-(x :int) + y <= z <=> y + -1 * z <= x``)
  val _ = s ("r088", A ``(x :int) + -1 * y <= z <=> x + (-1 * y + -1 * z) <= 0``)
  val _ = s ("r089", A ``(x :int) <= y + z <=> x + -1 * z <= y``)
  val _ = s ("r090", A ``(x :int) <= y + z <=> z + -1 * x >= -y``)
  val _ = s ("r091", A ``(x :int) <= y + z <=> x + (-1 * y + -1 * z) <= 0``)

  val _ = s ("r092", A ``(x :int) < y <=> ~(y <= x)``)
  val _ = s ("r093", A ``(x :int) < y <=> ~(x >= y)``)
  val _ = s ("r094", A ``(x :int) < y <=> ~(y + -1 * x <= 0)``)
  val _ = s ("r095", A ``(x :int) < y <=> ~(x + -1 * y >= 0)``)
  val _ = s ("r096", A ``(x :int) < y + -1 * z <=> ~(x + -1 * y + z >= 0)``)
  val _ = s ("r097", A ``(x :int) < y + -1 * z <=> ~(x + (-1 * y + z) >= 0)``)
  val _ = s ("r098", A ``(x :int) < -y + z <=> ~(z + -1 * x <= y)``)
  val _ = s ("r099", A ``(x :int) < -y + (z + u) <=> ~(z + (u + -1 * x) <= y)``)
  val _ = s ("r100", A
    ``(x :int) < -y + (z + (u + v)) <=> ~(z + (u + (v + -1 * x)) <= y)``)

  val _ = s ("r101", A ``-(x :int) + y < z <=> ~(y + -1 * z >= x)``)
  val _ = s ("r102", A ``(x :int) + y < z <=> ~(z + -1 * y <= x)``)
  val _ = s ("r103", A ``0 < -(x :int) + y <=> ~(y <= x)``)

  val _ = s ("r104", A ``(x :int) - 0 = x``)
  val _ = s ("r105", A ``0 - (x :int) = -x``)
  val _ = s ("r106", A ``0 - (x :int) = -1 * x``)
  val _ = s ("r107", A ``(x :int) - y = -y + x``)
  val _ = s ("r108", A ``(x :int) - y = x + -1 * y``)
  val _ = s ("r109", A ``(x :int) - y = -1 * y + x``)
  val _ = s ("r110", A ``(x :int) - 1 = -1 + x``)
  val _ = s ("r111", A ``(x :int) + y - z = x + (y + -1 * z)``)
  val _ = s ("r112", A ``(x :int) + y - z = x + (-1 * z + y)``)

  val _ = s ("r113", R ``(0 = -u * (x :real)) <=> (u * x = 0)``)
  val _ = s ("r114", R ``(a = -u * (x :real)) <=> (u * x = -a)``)
  val _ = s ("r115", R ``((a :real) = x + (y + z)) <=> (x + (y + (-1 * a + z)) = 0)``)
  val _ = s ("r116", R ``((a :real) = x + (y + z)) <=> (x + (y + (z + -1 * a)) = 0)``)
  val _ = s ("r117", R ``((a :real) = -u * y + v * z) <=> (u * y + (-v * z + a) = 0)``)
  val _ = s ("r118", R ``((a :real) = -u * y + -v * z) <=> (u * y + (a + v * z) = 0)``)
  val _ = s ("r119", R ``(-(a :real) = -u * x + v * y) <=> (u * x + -v * y = a)``)
  val _ = s ("r120", R
    ``((a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + (-w * z + a)) = 0)``)
  val _ = s ("r121", R
    ``((a :real) = -u * x + (v * y + w * z)) <=> (u * x + (-v * y + -w * z) = -a)``)
  val _ = s ("r122", R
    ``((a :real) = -u * x + (v * y + -w * z)) <=> (u * x + (-v * y + w * z) = -a)``)
  val _ = s ("r123", R
    ``((a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + -w * z) = -a)``)
  val _ = s ("r124", R ``((a :real) = -u * x + (-v * y + -w * z)) <=> (u * x + (v * y + w * z) = -a)``)
  val _ = s ("r125", R ``(-(a :real) = -u * x + (v * y + w * z)) <=> (u * x + (-v * y + -w * z) = a)``)
  val _ = s ("r126", R ``(-(a :real) = -u * x + (v * y + -w * z)) <=> (u * x + (-v * y + w * z) = a)``)
  val _ = s ("r127", R ``(-(a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + -w * z) = a)``)
  val _ = s ("r128", R ``(-(a :real) = -u * x + (-v * y + -w * z)) <=> (u * x + (v * y + w * z) = a)``)
  val _ = s ("r129", R ``((a :real) = -u * x + (-1 * y + w * z)) <=> (u * x + (y + -w * z) = -a)``)
  val _ = s ("r130", R ``((a :real) = -u * x + (-1 * y + -w * z)) <=> (u * x + (y + w * z) = -a)``)
  val _ = s ("r131", R ``(-u * (x :real) + -v * y = -a) <=> (u * x + v * y = a)``)
  val _ = s ("r132", R ``(-1 * (x :real) + (-v * y + -w * z) = -a) <=> (x + (v * y + w * z) = a)``)
  val _ = s ("r133", R ``(-u * (x :real) + (v * y + w * z) = -a) <=> (u * x + (-v * y + -w * z) = a)``)
  val _ = s ("r134", R ``(-u * (x :real) + (-v * y + w * z) = -a) <=> (u * x + (v * y + -w * z) = a)``)
  val _ = s ("r135", R ``(-u * (x :real) + (-v * y + -w * z) = -a) <=> (u * x + (v * y + w * z) = a)``)

  val _ = s ("r136", R ``(x :real) + -1 * y >= 0 <=> y <= x``)
  val _ = s ("r137", R ``(x :real) >= y <=> x + -1 * y >= 0``)

  val _ = s ("r138", R ``(x :real) > y <=> ~(x + -1 * y <= 0)``)

  val _ = s ("r139", R ``(x :real) <= y <=> x + -1 * y <= 0``)
  val _ = s ("r140", R ``(x :real) <= y + z <=> x + -1 * z <= y``)
  val _ = s ("r141", R ``-u * (x :real) <= a <=> u * x >= -a``)
  val _ = s ("r142", R ``-u * (x :real) <= -a <=> u * x >= a``)
  val _ = s ("r143", R ``-u * (x :real) + v * y <= 0 <=> u * x + -v * y >= 0``)
  val _ = s ("r144", R ``-u * (x :real) + v * y <= a <=> u * x + -v * y >= -a``)
  val _ = s ("r145", R ``-u * (x :real) + v * y <= -a <=> u * x + -v * y >= a``)
  val _ = s ("r146", R ``-u * (x :real) + -v * y <= a <=> u * x + v * y >= -a``)
  val _ = s ("r147", R ``-u * (x :real) + -v * y <= -a <=> u * x + v * y >= a``)
  val _ = s ("r148", R
    ``-u * (x :real) + (v * y + w * z) <= 0 <=> u * x + (-v * y + -w * z) >= 0``)
  val _ = s ("r149", R
    ``-u * (x :real) + (v * y + -w * z) <= 0 <=> u * x + (-v * y + w * z) >= 0``)
  val _ = s ("r150", R
    ``-u * (x :real) + (-v * y + w * z) <= 0 <=> u * x + (v * y + -w * z) >= 0``)
  val _ = s ("r151", R
    ``-u * (x :real) + (-v * y + -w * z) <= 0 <=> u * x + (v * y + w * z) >= 0``)
  val _ = s ("r152", R
    ``-u * (x :real) + (v * y + w * z) <= a <=> u * x + (-v * y + -w * z) >= -a``)
  val _ = s ("r153", R
    ``-u * (x :real) + (v * y + w * z) <= -a <=> u * x + (-v * y + -w * z) >= a``)
  val _ = s ("r154", R
    ``-u * (x :real) + (v * y + -w * z) <= a <=> u * x + (-v * y + w * z) >= -a``)
  val _ = s ("r155", R
    ``-u * (x :real) + (v * y + -w * z) <= -a <=> u * x + (-v * y + w * z) >= a``)
  val _ = s ("r156", R
    ``-u * (x :real) + (-v * y + w * z) <= a <=> u * x + (v * y + -w * z) >= -a``)
  val _ = s ("r157", R
    ``-u * (x :real) + (-v * y + w * z) <= -a <=> u * x + (v * y + -w * z) >= a``)
  val _ = s ("r158", R
    ``-u * (x :real) + (-v * y + -w * z) <= a <=> u * x + (v * y + w * z) >= -a``)
  val _ = s ("r159", R
    ``-u * (x :real) + (-v * y + -w * z) <= -a <=> u * x + (v * y + w * z) >= a``)
  val _ = s ("r160", R
    ``(-1 * (x :real) + (v * y + w * z) <= -a) <=> (x + (-v * y + -w * z) >= a)``)

  val _ = s ("r161", R ``(x :real) < y <=> ~(x >= y)``)
  val _ = s ("r162", R ``-u * (x :real) < a <=> ~(u * x <= -a)``)
  val _ = s ("r163", R ``-u * (x :real) < -a <=> ~(u * x <= a)``)
  val _ = s ("r164", R ``-u * (x :real) + v * y < 0 <=> ~(u * x + -v * y <= 0)``)
  val _ = s ("r165", R ``-u * (x :real) + -v * y < 0 <=> ~(u * x + v * y <= 0)``)
  val _ = s ("r166", R ``-u * (x :real) + v * y < a <=> ~(u * x + -v * y <= -a)``)
  val _ = s ("r167", R ``-u * (x :real) + v * y < -a <=> ~(u * x + -v * y <= a)``)
  val _ = s ("r168", R ``-u * (x :real) + -v * y < a <=> ~(u * x + v * y <= -a)``)
  val _ = s ("r169", R ``-u * (x :real) + -v * y < -a <=> ~(u * x + v * y <= a)``)
  val _ = s ("r170", R
    ``-u * (x :real) + (v * y + w * z) < a <=> ~(u * x + (-v * y + -w * z) <= -a)``)
  val _ = s ("r171", R
    ``-u * (x :real) + (v * y + w * z) < -a <=> ~(u * x + (-v * y + -w * z) <= a)``)
  val _ = s ("r172", R
    ``-u * (x :real) + (v * y + -w * z) < a <=> ~(u * x + (-v * y + w * z) <= -a)``)
  val _ = s ("r173", R
    ``-u * (x :real) + (v * y + -w * z) < -a <=> ~(u * x + (-v * y + w * z) <= a)``)
  val _ = s ("r174", R
    ``-u * (x :real) + (-v * y + w * z) < a <=> ~(u * x + (v * y + -w * z) <= -a)``)
  val _ = s ("r175", R
    ``-u * (x :real) + (-v * y + w * z) < -a <=> ~(u * x + (v * y + -w * z) <= a)``)
  val _ = s ("r176", R
    ``-u * (x :real) + (-v * y + -w * z) < a <=> ~(u * x + (v * y + w * z) <= -a)``)
  val _ = s ("r177", R
    ``-u * (x :real) + (-v * y + -w * z) < -a <=> ~(u * x + (v * y + w * z) <= a)``)
  val _ = s ("r178", R
    ``-u * (x :real) + (-v * y + w * z) < 0 <=> ~(u * x + (v * y + -w * z) <= 0)``)
  val _ = s ("r179", R
    ``-u * (x :real) + (-v * y + -w * z) < 0 <=> ~(u * x + (v * y + w * z) <= 0)``)
  val _ = s ("r180", R
    ``-1 * (x :real) + (v * y + w * z) < a <=> ~(x + (-v * y + -w * z) <= -a)``)
  val _ = s ("r181", R
    ``-1 * (x :real) + (v * y + w * z) < -a <=> ~(x + (-v * y + -w * z) <= a)``)
  val _ = s ("r182", R
    ``-1 * (x :real) + (v * y + -w * z) < a <=> ~(x + (-v * y + w * z) <= -a)``)
  val _ = s ("r183", R
    ``-1 * (x :real) + (v * y + -w * z) < -a <=> ~(x + (-v * y + w * z) <= a)``)
  val _ = s ("r184", R
    ``-1 * (x :real) + (-v * y + w * z) < a <=> ~(x + (v * y + -w * z) <= -a)``)
  val _ = s ("r185", R
    ``-1 * (x :real) + (-v * y + w * z) < -a <=> ~(x + (v * y + -w * z) <= a)``)
  val _ = s ("r186", R
    ``-1 * (x :real) + (-v * y + -w * z) < a <=> ~(x + (v * y + w * z) <= -a)``)
  val _ = s ("r187", R
    ``-1 * (x :real) + (-v * y + -w * z) < -a <=> ~(x + (v * y + w * z) <= a)``)
  val _ = s ("r188", R
    ``-u * (x :real) + (-1 * y + -w * z) < -a <=> ~(u * x + (y + w * z) <= a)``)
  val _ = s ("r189", R
    ``-u * (x :real) + (v * y + -1 * z) < -a <=> ~(u * x + (-v * y + z) <= a)``)

  val _ = s ("r190", R ``0 + (x :real) = x``)
  val _ = s ("r191", R ``(x :real) + 0 = x``)
  val _ = s ("r192", R ``(x :real) + y = y + x``)
  val _ = s ("r193", R ``(x :real) + x = 2 * x``)
  val _ = s ("r194", R ``(x :real) + y + z = x + (y + z)``)
  val _ = s ("r195", R ``(x :real) + y + z = x + (z + y)``)
  val _ = s ("r196", R ``(x :real) + (y + z) = y + (z + x)``)
  val _ = s ("r197", R ``(x :real) + (y + z) = y + (x + z)``)

  val _ = s ("r198", R ``0 - (x :real) = -x``)
  val _ = s ("r199", R ``0 - u * (x :real) = -u * x``)
  val _ = s ("r200", R ``(x :real) - 0 = x``)
  val _ = s ("r201", R ``(x :real) - y = x + -1 * y``)
  val _ = s ("r202", R ``(x :real) - y = -1 * y + x``)
  val _ = s ("r203", R ``(x :real) - u * y = x + -u * y``)
  val _ = s ("r204", R ``(x :real) - u * y = -u * y + x``)
  val _ = s ("r205", R ``(x :real) + y - z = x + (y + -1 * z)``)
  val _ = s ("r206", R ``(x :real) + y - z = x + (-1 * z + y)``)
  val _ = s ("r207", R ``(x :real) + y - u * z = -u * z + (x + y)``)
  val _ = s ("r208", R ``(x :real) + y - u * z = x + (-u * z + y)``)
  val _ = s ("r209", R ``(x :real) + y - u * z = x + (y + -u * z)``)

  val _ = s ("r210", R ``0 * (x :real) = 0``)
  val _ = s ("r211", R ``1 * (x :real) = x``)

  (* used for Z3's proof rule th-lemma *)

  val _ = s ("t001", A ``((x :int) <> y) \/ (x <= y)``)
  val _ = s ("t002", A ``((x :int) <> y) \/ (x >= y)``)
  val _ = s ("t003", A ``((x :int) <> y) \/ (x + -1 * y >= 0)``)
  val _ = s ("t004", A ``((x :int) <> y) \/ (x + -1 * y <= 0)``)
  val _ = s ("t005", A ``((x :int) = y) \/ ~(x <= y) \/ ~(x >= y)``)
  val _ = s ("t006", A ``~((x :int) <= 0) \/ x <= 1``)
  val _ = s ("t007", A ``~((x :int) <= -1) \/ x <= 0``)
  val _ = s ("t008", A ``~((x :int) >= 0) \/ x >= -1``)
  val _ = s ("t009", A ``~((x :int) >= 0) \/ ~(x <= -1)``)
  val _ = s ("t010", A ``(x :int) >= y \/ x <= y``)

  val _ = s ("t011", R ``(x :real) <> y \/ x + -1 * y >= 0``)

  val _ = Theory.export_theory ()

end
