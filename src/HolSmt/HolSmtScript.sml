(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Various theorems for HolSmtLib *)

  val T = tautLib.TAUT_PROVE
  val P = bossLib.PROVE []
  val S = simpLib.SIMP_PROVE (simpLib.++ (simpLib.++ (simpLib.++
    (bossLib.list_ss, boolSimps.COND_elim_ss), wordsLib.WORD_ss),
    wordsLib.WORD_BIT_EQ_ss)) [boolTheory.EQ_SYM_EQ]
  val A = intLib.ARITH_PROVE
  val R = realLib.REAL_ARITH
  val W = wordsLib.WORD_DECIDE
  val B = blastLib.BBLAST_PROVE

  (* simplify 't' using 'thms', then prove the simplified term using
     'TAUT_PROVE' *)
  fun U thms t =
  let
    val t_eq_t' = simpLib.SIMP_CONV (simpLib.++ (simpLib.++ (simpLib.++
      (bossLib.std_ss, boolSimps.COND_elim_ss), wordsLib.WORD_ss),
      wordsLib.WORD_BIT_EQ_ss)) thms t
    val t' = tautLib.TAUT_PROVE (boolSyntax.rhs (Thm.concl t_eq_t'))
  in
    Thm.EQ_MP (Thm.SYM t_eq_t') t'
  end

  val s = Theory.save_thm

  val _ = Theory.new_theory "HolSmt"
  val _ = ParseExtras.temp_loose_equality()


  (* constants used by Z3 *)

  (* exclusive or *)
  val xor_def = bossLib.Define `xor x y = ~(x <=> y)`

  (* array_ext[T] yields an index i such that select A i <> select B i
     (provided A and B are different arrays of type T) *)
  val array_ext_def = bossLib.Define `array_ext A B = @i. A i <> B i`

  (* used for Z3 proof reconstruction *)

  val _ = s ("ALL_DISTINCT_NIL", S ``ALL_DISTINCT [] = T``)
  val _ = s ("ALL_DISTINCT_CONS", S
    ``!h t. ALL_DISTINCT (h::t) = ~MEM h t /\ ALL_DISTINCT t``)
  val _ = s ("NOT_MEM_NIL", S ``!x. ~MEM x [] = T``)
  val _ = s ("NOT_MEM_CONS", S ``!x h t. ~MEM x (h::t) = (x <> h) /\ ~MEM x t``)
  val _ = s ("AND_T", T ``!p. p /\ T <=> p``)
  val _ = s ("T_AND", T ``!p q. (T /\ p <=> T /\ q) ==> (p <=> q)``)
  val _ = s ("F_OR", T ``!p q. (F \/ p <=> F \/ q) ==> (p <=> q)``)
  val _ = s ("CONJ_CONG", T
    ``!p q r s. (p <=> q) ==> (r <=> s) ==> (p /\ r <=> q /\ s)``)
  val _ = s ("NOT_NOT_ELIM", T ``!p. ~~p ==> p``)
  val _ = s ("NOT_FALSE", T ``!p. p ==> ~p ==> F``)
  val _ = s ("NNF_CONJ", T
    ``!p q r s. (~p <=> r) ==> (~q <=> s) ==> (~(p /\ q) <=> r \/ s)``)
  val _ = s ("NNF_DISJ", T
    ``!p q r s. (~p <=> r) ==> (~q <=> s) ==> (~(p \/ q) <=> r /\ s)``)
  val _ = s ("NNF_NOT_NOT", T ``!p q. (p <=> q) ==> (~~p <=> q)``)
  val _ = s ("NEG_IFF_1_1", T ``!p q. (q <=> p) ==> ~(p <=> ~q)``)
  val _ = s ("NEG_IFF_1_2", T ``!p q. ~(p <=> ~q) ==> (q <=> p)``)
  val _ = s ("NEG_IFF_2_1", T ``!p q. (p <=> ~q) ==> ~(p <=> q)``)
  val _ = s ("NEG_IFF_2_2", T ``!p q. ~(p <=> q) ==> (p <=> ~q)``)
  val _ = s ("DISJ_ELIM_1", T ``!p q r. (p \/ q ==> r) ==> p ==> r``)
  val _ = s ("DISJ_ELIM_2", T ``!p q r. (p \/ q ==> r) ==> q ==> r``)
  val _ = s ("IMP_DISJ_1", T ``!p q. (p ==> q) ==> ~p \/ q``)
  val _ = s ("IMP_DISJ_2", T ``!p q. (~p ==> q) ==> p \/ q``)
  val _ = s ("IMP_FALSE", T ``!p. (~p ==> F) ==> p``)
  val _ = s ("AND_IMP_INTRO_SYM", T ``!p q r. p /\ q ==> r <=> p ==> q ==> r``)
  val _ = s ("VALID_IFF_TRUE", T ``!p. p ==> (p <=> T)``)

  (* used for Z3's proof rule def-axiom *)

  val _ = s ("d001", T ``~(p <=> q) \/ ~p \/ q``)
  val _ = s ("d002", T ``~(p <=> q) \/ p \/ ~q``)
  val _ = s ("d003", T ``(p <=> ~q) \/ ~p \/ q``)
  val _ = s ("d004", T ``(~p <=> q) \/ p \/ ~q``)
  val _ = s ("d005", T ``(p <=> q) \/ ~p \/ ~q``)
  val _ = s ("d006", T ``(p <=> q) \/ p \/ q``)
  val _ = s ("d007", T ``~(~p <=> q) \/ p \/ q``)
  val _ = s ("d008", T ``~(p <=> ~q) \/ p \/ q``)
  val _ = s ("d009", T ``~p \/ q \/ ~(p <=> q)``)
  val _ = s ("d010", T ``p \/ ~q \/ ~(p <=> q)``)
  val _ = s ("d011", T ``p \/ q \/ ~(~p <=> q)``)
  val _ = s ("d012", T ``p \/ q \/ ~(p <=> ~q)``)
  val _ = s ("d013", T ``(~p /\ ~q) \/ p \/ q``)
  val _ = s ("d014", T ``(~p /\ q) \/ p \/ ~q``)
  val _ = s ("d015", T ``(p /\ ~q) \/ ~p \/ q``)
  val _ = s ("d016", T ``(p /\ q) \/ ~p \/ ~q``)
  val _ = s ("d017", P ``p \/ (y = if p then x else y)``)
  val _ = s ("d018", P ``~p \/ (x = if p then x else y)``)
  val _ = s ("d019", P ``p \/ ((if p then x else y) = y)``)
  val _ = s ("d020", P ``~p \/ ((if p then x else y) = x)``)
  val _ = s ("d021", P ``p \/ q \/ ~(if p then r else q)``)
  val _ = s ("d022", P ``~p \/ q \/ ~(if p then q else r)``)
  val _ = s ("d023", P ``(if p then q else r) \/ ~p \/ ~q``)
  val _ = s ("d024", P ``(if p then q else r) \/ p \/ ~r``)
  val _ = s ("d025", P ``(if p then ~q else r) \/ ~p \/ q``)
  val _ = s ("d026", P ``(if p then q else ~r) \/ p \/ r``)
  val _ = s ("d027", P ``~(if p then q else r) \/ ~p \/ q``)
  val _ = s ("d028", P ``~(if p then q else r) \/ p \/ r``)

  (* used for Z3's proof rule rewrite *)

  val _ = s ("r001", P ``(x = y) <=> (y = x)``)
  val _ = s ("r002", P ``(x = x) <=> T``)
  val _ = s ("r003", T ``(p <=> T) <=> p``)
  val _ = s ("r004", T ``(T <=> p) <=> p``)
  val _ = s ("r005", T ``(p <=> F) <=> ~p``)
  val _ = s ("r006", T ``(F <=> p) <=> ~p``)
  val _ = s ("r007", T ``(~p <=> ~q) <=> (p <=> q)``)
  val _ = s ("r008", T ``~(p <=> ~q) <=> (p <=> q)``)
  val _ = s ("r009", T ``~(~p <=> q) <=> (p <=> q)``)

  val _ = s ("r010", P ``(if T then x else y) = x``)
  val _ = s ("r011", P ``(if F then x else y) = y``)
  val _ = s ("r012", T ``(if p then q else T) <=> (~p \/ q)``)
  val _ = s ("r013", T ``(if p then q else T) <=> (q \/ ~p)``)
  val _ = s ("r014", T ``(if p then q else ~q) <=> (p <=> q)``)
  val _ = s ("r015", T ``(if p then q else ~q) <=> (q <=> p)``)
  val _ = s ("r016", T ``(if p then ~q else q) <=> (p <=> ~q)``)
  val _ = s ("r017", T ``(if p then ~q else q) <=> (~q <=> p)``)
  val _ = s ("r018", P ``(if ~p then x else y) = (if p then y else x)``)
  val _ = s ("r019", P
    ``(if p then (if q then x else y) else x) = (if p /\ ~q then y else x)``)
  val _ = s ("r020", P
    ``(if p then (if q then x else y) else x) = (if ~q /\ p then y else x)``)
  val _ = s ("r021", P
    ``(if p then (if q then x else y) else y) = (if p /\ q then x else y)``)
  val _ = s ("r022", P
    ``(if p then (if q then x else y) else y) = (if q /\ p then x else y)``)
  val _ = s ("r023", P
    ``(if p then x else (if p then y else z)) = (if p then x else z)``)
  val _ = s ("r024", P
    ``(if p then x else (if q then x else y)) = (if p \/ q then x else y)``)
  val _ = s ("r025", P
    ``(if p then x else (if q then x else y)) = (if q \/ p then x else y)``)
  val _ = s ("r026", P
    ``(if p then x = y else x = z) <=> (x = if p then y else z)``)
  val _ = s ("r027", P
    ``(if p then x = y else y = z) <=> (y = if p then x else z)``)
  val _ = s ("r028", P
    ``(if p then x = y else z = y) <=> (y = if p then x else z)``)

  val _ = s ("r029", T ``(~p ==> q) <=> (p \/ q)``)
  val _ = s ("r030", T ``(~p ==> q) <=> (q \/ p)``)
  val _ = s ("r031", T ``(p ==> q) <=> (~p \/ q)``)
  val _ = s ("r032", T ``(p ==> q) <=> (q \/ ~p)``)
  val _ = s ("r033", T ``(T ==> p) <=> p``)
  val _ = s ("r034", T ``(p ==> T) <=> T``)
  val _ = s ("r035", T ``(F ==> p) <=> T``)
  val _ = s ("r036", T ``(p ==> p) <=> T``)
  val _ = s ("r037", T ``((p <=> q) ==> r) <=> (r \/ (q <=> ~p))``)

  val _ = s ("r038", T ``~T <=> F``)
  val _ = s ("r039", T ``~F <=> T``)
  val _ = s ("r040", T ``~~p <=> p``)

  val _ = s ("r041", T ``p \/ q <=> q \/ p``)
  val _ = s ("r042", T ``p \/ T <=> T``)
  val _ = s ("r043", T ``p \/ ~p <=> T``)
  val _ = s ("r044", T ``~p \/ p <=> T``)
  val _ = s ("r045", T ``T \/ p <=> T``)
  val _ = s ("r046", T ``p \/ F <=> p``)
  val _ = s ("r047", T ``F \/ p <=> p``)

  val _ = s ("r048", T ``p /\ q <=> q /\ p``)
  val _ = s ("r049", T ``p /\ T <=> p``)
  val _ = s ("r050", T ``T /\ p <=> p``)
  val _ = s ("r051", T ``p /\ F <=> F``)
  val _ = s ("r052", T ``F /\ p <=> F``)
  val _ = s ("r053", T ``p /\ q <=> ~(~p \/ ~q)``)
  val _ = s ("r054", T ``~p /\ q <=> ~(p \/ ~q)``)
  val _ = s ("r055", T ``p /\ ~q <=> ~(~p \/ q)``)
  val _ = s ("r056", T ``~p /\ ~q <=> ~(p \/ q)``)
  val _ = s ("r057", T ``p /\ q <=> ~(~q \/ ~p)``)
  val _ = s ("r058", T ``~p /\ q <=> ~(~q \/ p)``)
  val _ = s ("r059", T ``p /\ ~q <=> ~(q \/ ~p)``)
  val _ = s ("r060", T ``~p /\ ~q <=> ~(q \/ p)``)

  val _ = s ("r061", U [combinTheory.APPLY_UPDATE_ID] ``(x =+ f x) f = f``)

  val _ = s ("r062", S ``ALL_DISTINCT [x; x] <=> F``)
  val _ = s ("r063", S ``ALL_DISTINCT [x; y] <=> x <> y``)
  val _ = s ("r064", S ``ALL_DISTINCT [x; y] <=> y <> x``)

  val _ = s ("r065", A ``((x :int) = y) <=> (x + -1 * y = 0)``)
  val _ = s ("r066", A ``((x :int) = y + z) <=> (x + -1 * z = y)``)
  val _ = s ("r067", A ``((x :int) = y + -1 * z) <=> (x + (-1 * y + z) = 0)``)
  val _ = s ("r068", A ``((x :int) = -1 * y + z) <=> (y + (-1 * z + x) = 0)``)
  val _ = s ("r069", A ``((x :int) = y + z) <=> (x + (-1 * y + -1 * z) = 0)``)
  val _ = s ("r070", A ``((x :int) = y + z) <=> (y + (z + -1 * x) = 0)``)
  val _ = s ("r071", A ``((x :int) = y + z) <=> (y + (-1 * x + z) = 0)``)
  val _ = s ("r072", A ``((x :int) = y + z) <=> (z + -1 * x = -y)``)
  val _ = s ("r073", A ``((x :int) = -y + z) <=> (z + -1 * x = y)``)
  val _ = s ("r074", A ``(-1 * (x :int) = -y) <=> (x = y)``)
  val _ = s ("r075", A ``(-1 * (x :int) + y = z) <=> (x + -1 * y = -z)``)
  val _ = s ("r076", A ``((x :int) + y = 0) <=> (y = -x)``)
  val _ = s ("r077", A ``((x :int) + y = z) <=> (y + -1 * z = -x)``)
  val _ = s ("r078", A
    ``((a :int) + (-1 * x + (v * y + w * z)) = 0) <=> (x + (-v * y + -w * z) = a)``)

  val _ = s ("r079", A ``0 + (x :int) = x``)
  val _ = s ("r080", A ``(x :int) + 0 = x``)
  val _ = s ("r081", A ``(x :int) + y = y + x``)
  val _ = s ("r082", A ``(x :int) + x = 2 * x``)
  val _ = s ("r083", A ``(x :int) + y + z = x + (y + z)``)
  val _ = s ("r084", A ``(x :int) + y + z = x + (z + y)``)
  val _ = s ("r085", A ``(x :int) + (y + z) = y + (z + x)``)
  val _ = s ("r086", A ``(x :int) + (y + z) = y + (x + z)``)
  val _ = s ("r087", A ``(x :int) + (y + (z + u)) = y + (z + (u + x))``)

  val _ = s ("r088", A ``(x :int) >= x <=> T``)
  val _ = s ("r089", A ``(x :int) >= y <=> x + -1 * y >= 0``)
  val _ = s ("r090", A ``(x :int) >= y <=> y + -1 * x <= 0``)
  val _ = s ("r091", A ``(x :int) >= y + z <=> y + (z + -1 * x) <= 0``)
  val _ = s ("r092", A ``-1 * (x :int) >= 0 <=> x <= 0``)
  val _ = s ("r093", A ``-1 * (x :int) >= -y <=> x <= y``)
  val _ = s ("r094", A ``-1 * (x :int) + y >= 0 <=> x + -1 * y <= 0``)
  val _ = s ("r095", A ``(x :int) + -1 * y >= 0 <=> y <= x``)

  val _ = s ("r096", A ``(x :int) > y <=> ~(y >= x)``)
  val _ = s ("r097", A ``(x :int) > y <=> ~(x <= y)``)
  val _ = s ("r098", A ``(x :int) > y <=> ~(x + -1 * y <= 0)``)
  val _ = s ("r099", A ``(x :int) > y <=> ~(y + -1 * x >= 0)``)
  val _ = s ("r100", A ``(x :int) > y + z <=> ~(z + -1 * x >= -y)``)

  val _ = s ("r101", A ``x <= (x :int) <=> T``)
  val _ = s ("r102", A ``0 <= (1 :int) <=> T``)
  val _ = s ("r103", A ``(x :int) <= y <=> y >= x``)
  val _ = s ("r104", A ``0 <= -(x :int) + y <=> y >= x``)
  val _ = s ("r105", A ``-1 * (x :int) <= 0 <=> x >= 0``)
  val _ = s ("r106", A ``(x :int) <= y <=> x + -1 * y <= 0``)
  val _ = s ("r107", A ``(x :int) <= y <=> y + -1 * x >= 0``)
  val _ = s ("r108", A ``-1 * (x :int) + y <= 0 <=> x + -1 * y >= 0``)
  val _ = s ("r109", A ``-1 * (x :int) + y <= -z <=> x + -1 * y >= z``)
  val _ = s ("r110", A ``-(x :int) + y <= z <=> y + -1 * z <= x``)
  val _ = s ("r111", A ``(x :int) + -1 * y <= z <=> x + (-1 * y + -1 * z) <= 0``)
  val _ = s ("r112", A ``(x :int) <= y + z <=> x + -1 * z <= y``)
  val _ = s ("r113", A ``(x :int) <= y + z <=> z + -1 * x >= -y``)
  val _ = s ("r114", A ``(x :int) <= y + z <=> x + (-1 * y + -1 * z) <= 0``)

  val _ = s ("r115", A ``(x :int) < y <=> ~(y <= x)``)
  val _ = s ("r116", A ``(x :int) < y <=> ~(x >= y)``)
  val _ = s ("r117", A ``(x :int) < y <=> ~(y + -1 * x <= 0)``)
  val _ = s ("r118", A ``(x :int) < y <=> ~(x + -1 * y >= 0)``)
  val _ = s ("r119", A ``(x :int) < y + -1 * z <=> ~(x + -1 * y + z >= 0)``)
  val _ = s ("r120", A ``(x :int) < y + -1 * z <=> ~(x + (-1 * y + z) >= 0)``)
  val _ = s ("r121", A ``(x :int) < -y + z <=> ~(z + -1 * x <= y)``)
  val _ = s ("r122", A ``(x :int) < -y + (z + u) <=> ~(z + (u + -1 * x) <= y)``)
  val _ = s ("r123", A
    ``(x :int) < -y + (z + (u + v)) <=> ~(z + (u + (v + -1 * x)) <= y)``)

  val _ = s ("r124", A ``-(x :int) + y < z <=> ~(y + -1 * z >= x)``)
  val _ = s ("r125", A ``(x :int) + y < z <=> ~(z + -1 * y <= x)``)
  val _ = s ("r126", A ``0 < -(x :int) + y <=> ~(y <= x)``)

  val _ = s ("r127", A ``(x :int) - 0 = x``)
  val _ = s ("r128", A ``0 - (x :int) = -x``)
  val _ = s ("r129", A ``0 - (x :int) = -1 * x``)
  val _ = s ("r130", A ``(x :int) - y = -y + x``)
  val _ = s ("r131", A ``(x :int) - y = x + -1 * y``)
  val _ = s ("r132", A ``(x :int) - y = -1 * y + x``)
  val _ = s ("r133", A ``(x :int) - 1 = -1 + x``)
  val _ = s ("r134", A ``(x :int) + y - z = x + (y + -1 * z)``)
  val _ = s ("r135", A ``(x :int) + y - z = x + (-1 * z + y)``)

  val _ = s ("r136", R ``(0 = -u * (x :real)) <=> (u * x = 0)``)
  val _ = s ("r137", R ``(a = -u * (x :real)) <=> (u * x = -a)``)
  val _ = s ("r138", R ``((a :real) = x + (y + z)) <=> (x + (y + (-1 * a + z)) = 0)``)
  val _ = s ("r139", R ``((a :real) = x + (y + z)) <=> (x + (y + (z + -1 * a)) = 0)``)
  val _ = s ("r140", R ``((a :real) = -u * y + v * z) <=> (u * y + (-v * z + a) = 0)``)
  val _ = s ("r141", R ``((a :real) = -u * y + -v * z) <=> (u * y + (a + v * z) = 0)``)
  val _ = s ("r142", R ``(-(a :real) = -u * x + v * y) <=> (u * x + -v * y = a)``)
  val _ = s ("r143", R
    ``((a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + (-w * z + a)) = 0)``)
  val _ = s ("r144", R
    ``((a :real) = -u * x + (v * y + w * z)) <=> (u * x + (-v * y + -w * z) = -a)``)
  val _ = s ("r145", R
    ``((a :real) = -u * x + (v * y + -w * z)) <=> (u * x + (-v * y + w * z) = -a)``)
  val _ = s ("r146", R
    ``((a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + -w * z) = -a)``)
  val _ = s ("r147", R ``((a :real) = -u * x + (-v * y + -w * z)) <=> (u * x + (v * y + w * z) = -a)``)
  val _ = s ("r148", R ``(-(a :real) = -u * x + (v * y + w * z)) <=> (u * x + (-v * y + -w * z) = a)``)
  val _ = s ("r149", R ``(-(a :real) = -u * x + (v * y + -w * z)) <=> (u * x + (-v * y + w * z) = a)``)
  val _ = s ("r150", R ``(-(a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + -w * z) = a)``)
  val _ = s ("r151", R ``(-(a :real) = -u * x + (-v * y + -w * z)) <=> (u * x + (v * y + w * z) = a)``)
  val _ = s ("r152", R ``((a :real) = -u * x + (-1 * y + w * z)) <=> (u * x + (y + -w * z) = -a)``)
  val _ = s ("r153", R ``((a :real) = -u * x + (-1 * y + -w * z)) <=> (u * x + (y + w * z) = -a)``)
  val _ = s ("r154", R ``(-u * (x :real) + -v * y = -a) <=> (u * x + v * y = a)``)
  val _ = s ("r155", R ``(-1 * (x :real) + (-v * y + -w * z) = -a) <=> (x + (v * y + w * z) = a)``)
  val _ = s ("r156", R ``(-u * (x :real) + (v * y + w * z) = -a) <=> (u * x + (-v * y + -w * z) = a)``)
  val _ = s ("r157", R ``(-u * (x :real) + (-v * y + w * z) = -a) <=> (u * x + (v * y + -w * z) = a)``)
  val _ = s ("r158", R ``(-u * (x :real) + (-v * y + -w * z) = -a) <=> (u * x + (v * y + w * z) = a)``)

  val _ = s ("r159", R ``(x :real) + -1 * y >= 0 <=> y <= x``)
  val _ = s ("r160", R ``(x :real) >= y <=> x + -1 * y >= 0``)

  val _ = s ("r161", R ``(x :real) > y <=> ~(x + -1 * y <= 0)``)

  val _ = s ("r162", R ``(x :real) <= y <=> x + -1 * y <= 0``)
  val _ = s ("r163", R ``(x :real) <= y + z <=> x + -1 * z <= y``)
  val _ = s ("r164", R ``-u * (x :real) <= a <=> u * x >= -a``)
  val _ = s ("r165", R ``-u * (x :real) <= -a <=> u * x >= a``)
  val _ = s ("r166", R ``-u * (x :real) + v * y <= 0 <=> u * x + -v * y >= 0``)
  val _ = s ("r167", R ``-u * (x :real) + v * y <= a <=> u * x + -v * y >= -a``)
  val _ = s ("r168", R ``-u * (x :real) + v * y <= -a <=> u * x + -v * y >= a``)
  val _ = s ("r169", R ``-u * (x :real) + -v * y <= a <=> u * x + v * y >= -a``)
  val _ = s ("r170", R ``-u * (x :real) + -v * y <= -a <=> u * x + v * y >= a``)
  val _ = s ("r171", R
    ``-u * (x :real) + (v * y + w * z) <= 0 <=> u * x + (-v * y + -w * z) >= 0``)
  val _ = s ("r172", R
    ``-u * (x :real) + (v * y + -w * z) <= 0 <=> u * x + (-v * y + w * z) >= 0``)
  val _ = s ("r173", R
    ``-u * (x :real) + (-v * y + w * z) <= 0 <=> u * x + (v * y + -w * z) >= 0``)
  val _ = s ("r174", R
    ``-u * (x :real) + (-v * y + -w * z) <= 0 <=> u * x + (v * y + w * z) >= 0``)
  val _ = s ("r175", R
    ``-u * (x :real) + (v * y + w * z) <= a <=> u * x + (-v * y + -w * z) >= -a``)
  val _ = s ("r176", R
    ``-u * (x :real) + (v * y + w * z) <= -a <=> u * x + (-v * y + -w * z) >= a``)
  val _ = s ("r177", R
    ``-u * (x :real) + (v * y + -w * z) <= a <=> u * x + (-v * y + w * z) >= -a``)
  val _ = s ("r178", R
    ``-u * (x :real) + (v * y + -w * z) <= -a <=> u * x + (-v * y + w * z) >= a``)
  val _ = s ("r179", R
    ``-u * (x :real) + (-v * y + w * z) <= a <=> u * x + (v * y + -w * z) >= -a``)
  val _ = s ("r180", R
    ``-u * (x :real) + (-v * y + w * z) <= -a <=> u * x + (v * y + -w * z) >= a``)
  val _ = s ("r181", R
    ``-u * (x :real) + (-v * y + -w * z) <= a <=> u * x + (v * y + w * z) >= -a``)
  val _ = s ("r182", R
    ``-u * (x :real) + (-v * y + -w * z) <= -a <=> u * x + (v * y + w * z) >= a``)
  val _ = s ("r183", R
    ``(-1 * (x :real) + (v * y + w * z) <= -a) <=> (x + (-v * y + -w * z) >= a)``)

  val _ = s ("r184", R ``(x :real) < y <=> ~(x >= y)``)
  val _ = s ("r185", R ``-u * (x :real) < a <=> ~(u * x <= -a)``)
  val _ = s ("r186", R ``-u * (x :real) < -a <=> ~(u * x <= a)``)
  val _ = s ("r187", R ``-u * (x :real) + v * y < 0 <=> ~(u * x + -v * y <= 0)``)
  val _ = s ("r188", R ``-u * (x :real) + -v * y < 0 <=> ~(u * x + v * y <= 0)``)
  val _ = s ("r189", R ``-u * (x :real) + v * y < a <=> ~(u * x + -v * y <= -a)``)
  val _ = s ("r190", R ``-u * (x :real) + v * y < -a <=> ~(u * x + -v * y <= a)``)
  val _ = s ("r191", R ``-u * (x :real) + -v * y < a <=> ~(u * x + v * y <= -a)``)
  val _ = s ("r192", R ``-u * (x :real) + -v * y < -a <=> ~(u * x + v * y <= a)``)
  val _ = s ("r193", R
    ``-u * (x :real) + (v * y + w * z) < a <=> ~(u * x + (-v * y + -w * z) <= -a)``)
  val _ = s ("r194", R
    ``-u * (x :real) + (v * y + w * z) < -a <=> ~(u * x + (-v * y + -w * z) <= a)``)
  val _ = s ("r195", R
    ``-u * (x :real) + (v * y + -w * z) < a <=> ~(u * x + (-v * y + w * z) <= -a)``)
  val _ = s ("r196", R
    ``-u * (x :real) + (v * y + -w * z) < -a <=> ~(u * x + (-v * y + w * z) <= a)``)
  val _ = s ("r197", R
    ``-u * (x :real) + (-v * y + w * z) < a <=> ~(u * x + (v * y + -w * z) <= -a)``)
  val _ = s ("r198", R
    ``-u * (x :real) + (-v * y + w * z) < -a <=> ~(u * x + (v * y + -w * z) <= a)``)
  val _ = s ("r199", R
    ``-u * (x :real) + (-v * y + -w * z) < a <=> ~(u * x + (v * y + w * z) <= -a)``)
  val _ = s ("r200", R
    ``-u * (x :real) + (-v * y + -w * z) < -a <=> ~(u * x + (v * y + w * z) <= a)``)
  val _ = s ("r201", R
    ``-u * (x :real) + (-v * y + w * z) < 0 <=> ~(u * x + (v * y + -w * z) <= 0)``)
  val _ = s ("r202", R
    ``-u * (x :real) + (-v * y + -w * z) < 0 <=> ~(u * x + (v * y + w * z) <= 0)``)
  val _ = s ("r203", R
    ``-1 * (x :real) + (v * y + w * z) < a <=> ~(x + (-v * y + -w * z) <= -a)``)
  val _ = s ("r204", R
    ``-1 * (x :real) + (v * y + w * z) < -a <=> ~(x + (-v * y + -w * z) <= a)``)
  val _ = s ("r205", R
    ``-1 * (x :real) + (v * y + -w * z) < a <=> ~(x + (-v * y + w * z) <= -a)``)
  val _ = s ("r206", R
    ``-1 * (x :real) + (v * y + -w * z) < -a <=> ~(x + (-v * y + w * z) <= a)``)
  val _ = s ("r207", R
    ``-1 * (x :real) + (-v * y + w * z) < a <=> ~(x + (v * y + -w * z) <= -a)``)
  val _ = s ("r208", R
    ``-1 * (x :real) + (-v * y + w * z) < -a <=> ~(x + (v * y + -w * z) <= a)``)
  val _ = s ("r209", R
    ``-1 * (x :real) + (-v * y + -w * z) < a <=> ~(x + (v * y + w * z) <= -a)``)
  val _ = s ("r210", R
    ``-1 * (x :real) + (-v * y + -w * z) < -a <=> ~(x + (v * y + w * z) <= a)``)
  val _ = s ("r211", R
    ``-u * (x :real) + (-1 * y + -w * z) < -a <=> ~(u * x + (y + w * z) <= a)``)
  val _ = s ("r212", R
    ``-u * (x :real) + (v * y + -1 * z) < -a <=> ~(u * x + (-v * y + z) <= a)``)

  val _ = s ("r213", R ``0 + (x :real) = x``)
  val _ = s ("r214", R ``(x :real) + 0 = x``)
  val _ = s ("r215", R ``(x :real) + y = y + x``)
  val _ = s ("r216", R ``(x :real) + x = 2 * x``)
  val _ = s ("r217", R ``(x :real) + y + z = x + (y + z)``)
  val _ = s ("r218", R ``(x :real) + y + z = x + (z + y)``)
  val _ = s ("r219", R ``(x :real) + (y + z) = y + (z + x)``)
  val _ = s ("r220", R ``(x :real) + (y + z) = y + (x + z)``)

  val _ = s ("r221", R ``0 - (x :real) = -x``)
  val _ = s ("r222", R ``0 - u * (x :real) = -u * x``)
  val _ = s ("r223", R ``(x :real) - 0 = x``)
  val _ = s ("r224", R ``(x :real) - y = x + -1 * y``)
  val _ = s ("r225", R ``(x :real) - y = -1 * y + x``)
  val _ = s ("r226", R ``(x :real) - u * y = x + -u * y``)
  val _ = s ("r227", R ``(x :real) - u * y = -u * y + x``)
  val _ = s ("r228", R ``(x :real) + y - z = x + (y + -1 * z)``)
  val _ = s ("r229", R ``(x :real) + y - z = x + (-1 * z + y)``)
  val _ = s ("r230", R ``(x :real) + y - u * z = -u * z + (x + y)``)
  val _ = s ("r231", R ``(x :real) + y - u * z = x + (-u * z + y)``)
  val _ = s ("r232", R ``(x :real) + y - u * z = x + (y + -u * z)``)

  val _ = s ("r233", R ``0 * (x :real) = 0``)
  val _ = s ("r234", R ``1 * (x :real) = x``)

  val _ = s ("r235", W ``0w + x = x``)
  val _ = s ("r236", W ``(x :'a word) + y = y + x``)
  val _ = s ("r237", W ``1w + (1w + x) = 2w + x``)
  val _ = s ("r238", Drule.EQT_ELIM
    (wordsLib.WORD_ARITH_CONV ``((x :'a word) + z = y + x) <=> (y = z)``))

  val _ = s ("r239", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0] ``FINITE univ(:'a) ==> x < dimword(:'b) ==>
      ((0w :'a word) @@ (n2w x :'b word) = (n2w x :'c word))``))
  val _ = s ("r240", Drule.UNDISCH (simpLib.SIMP_PROVE bossLib.std_ss
    [wordsTheory.w2w_n2w, Thm.SYM (Drule.SPEC_ALL wordsTheory.MOD_DIMINDEX)]
    ``x < dimword(:'a) ==> (w2w (n2w x :'a word) = (n2w x :'b word))``))
  val _ = s ("r241", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((0w :'a word) @@ (x :'b word) = (n2w y :'c word)) <=> (x = n2w y))``))
  val _ = s ("r242", Drule.UNDISCH_ALL (bossLib.PROVE
      [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((0w :'a word) @@ (x :'b word) = (n2w y :'c word)) <=> (n2w y = x))``))
  val _ = s ("r243", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((n2w y :'c word) = (0w :'a word) @@ (x :'b word)) <=> (x = n2w y))``))
  val _ = s ("r244", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((n2w y :'c word) = (0w :'a word) @@ (x :'b word)) <=> (n2w y = x))``))

  val _ = s ("r245", W ``x && y = y && x``)
  val _ = s ("r246", W ``x && y && z = y && x && z``)
  val _ = s ("r247", W ``x && y && z = (x && y) && z``)
  val _ = s ("r248", W ``(1w = (x :word1) && y) <=> (1w = x) /\ (1w = y)``)
  val _ = s ("r249", W ``(1w = (x :word1) && y) <=> (1w = y) /\ (1w = x)``)
  val _ = s ("r250", W ``(7 >< 0) (x :word8) = x``)
  val _ = s ("r251", W ``x <+ y <=> ~(y <=+ x)``)
  val _ = s ("r252", W ``(x :'a word) * y = y * x``)
  val _ = s ("r253", W ``(0 >< 0) (x :word1) = x``)
  val _ = s ("r254", W ``(x && y) && z = x && y && z``)
  val _ = s ("r255", W ``0w || x = x``)

  (* used for Z3's proof rule th_lemma *)

  val _ = s ("t001", U [boolTheory.EQ_SYM_EQ, combinTheory.UPDATE_def]
    ``(x = y) \/ (f x = (y =+ z) f x)``)
  val _ = s ("t002", U [boolTheory.EQ_SYM_EQ, combinTheory.UPDATE_def]
    ``(x = y) \/ (f y = (x =+ z) f y)``)
  val _ = s ("t003", U [boolTheory.EQ_SYM_EQ, combinTheory.UPDATE_def]
    ``(x = y) \/ ((y =+ z) f x = f x)``)
  val _ = s ("t004", U [boolTheory.EQ_SYM_EQ, combinTheory.UPDATE_def]
    ``(x = y) \/ ((x =+ z) f y = f y)``)
  val _ = s ("t005", Tactical.prove
    (``(f = g) \/ (f (array_ext f g) <> g (array_ext f g))``,
    Tactical.THEN (Tactic.DISJ_CASES_TAC
        (Thm.SPEC ``?x. f x <> g x`` boolTheory.EXCLUDED_MIDDLE),
      Tactical.THEN (Rewrite.REWRITE_TAC [array_ext_def],
        bossLib.METIS_TAC []))))

  val _ = s ("t006", A ``((x :int) <> y) \/ (x <= y)``)
  val _ = s ("t007", A ``((x :int) <> y) \/ (x >= y)``)
  val _ = s ("t008", A ``((x :int) <> y) \/ (x + -1 * y >= 0)``)
  val _ = s ("t009", A ``((x :int) <> y) \/ (x + -1 * y <= 0)``)
  val _ = s ("t010", A ``((x :int) = y) \/ ~(x <= y) \/ ~(x >= y)``)
  val _ = s ("t011", A ``~((x :int) <= 0) \/ x <= 1``)
  val _ = s ("t012", A ``~((x :int) <= -1) \/ x <= 0``)
  val _ = s ("t013", A ``~((x :int) >= 0) \/ x >= -1``)
  val _ = s ("t014", A ``~((x :int) >= 0) \/ ~(x <= -1)``)
  val _ = s ("t015", A ``(x :int) >= y \/ x <= y``)

  val _ = s ("t016", R ``(x :real) <> y \/ x + -1 * y >= 0``)

  val _ = s ("t017", Tactical.prove (``(x :'a word) <> ~x``,
    let
      val RW = bossLib.RW_TAC (bossLib.++ (bossLib.bool_ss, fcpLib.FCP_ss))
    in
      Tactical.THEN (RW [],
        Tactical.THEN (Tactic.EXISTS_TAC ``0 :num``,
          Tactical.THEN (RW [wordsTheory.DIMINDEX_GT_0,
              wordsTheory.word_1comp_def],
            tautLib.TAUT_TAC)))
    end))
  val _ = s ("t018", W ``(x = y) ==> x ' i ==> y ' i``)
  val _ = s ("t019", S ``(1w = ~(x :word1)) \/ x ' 0``)
  val _ = s ("t020", S ``(x :word1) ' 0 ==> (0w = ~x)``)
  val _ = s ("t021", S ``(x :word1) ' 0 ==> (1w = x)``)
  val _ = s ("t022", S ``~((x :word1) ' 0) ==> (0w = x)``)
  val _ = s ("t023", S ``~((x :word1) ' 0) ==> (1w = ~x)``)
  val _ = s ("t024", S ``(0w = ~(x :word1)) \/ ~(x ' 0)``)
  val _ = s ("t025", U []
    ``(1w = ~(x :word1) || ~y) \/ ~(~(x ' 0) \/ ~(y ' 0))``)
  val _ = s ("t026", U []
    ``(0w = (x :word8)) \/ x ' 0 \/ x ' 1 \/ x ' 2 \/ x ' 3 \/ x ' 4 \/ x ' 5 \/ x ' 6 \/ x ' 7``)
  val _ = s ("t027", S
    ``(((x :word1) = 1w) <=> p) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t028", S
    ``((1w = (x :word1)) <=> p) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t029", S
    ``(p <=> ((x :word1) = 1w)) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t030", S
    ``(p <=> (1w = (x :word1))) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t031", B
    ``(0w:word32 = 0xFFFFFFFFw * sw2sw (x :word8)) ==> ~(x ' 0)``)
  val _ = s ("t032", B
    ``(0w:word32 = 0xFFFFFFFFw * sw2sw (x :word8)) ==> ~(x ' 1 <=> ~(x ' 0))``)
  val _ = s ("t033", B ``(0w:word32 = 0xFFFFFFFFw * sw2sw (x :word8)) ==>
      ~(x ' 2 <=> ~(x ' 0) /\ ~(x ' 1))``)
  val _ = s ("t034",
    bossLib.METIS_PROVE [simpLib.SIMP_PROVE bossLib.bool_ss
        [wordsTheory.WORD_ADD_BIT0, wordsLib.WORD_DECIDE ``1w :'a word ' 0``]
        ``x ' 0 ==> ~(1w + (x :'a word)) ' 0``]
      ``(1w + (x :'a word) = y) ==> x ' 0 ==> ~(y ' 0)``)
  val _ = s ("t035", S ``(1w = x :word1) \/ (0 >< 0) x <> (1w :word1)``)

  (* used to prove hypotheses of other proforma theorems (recursively) *)

  val _ = s ("p001", wordsTheory.ZERO_LT_dimword)  (* ``0 < dimword(:'a)`` *)
  val _ = s ("p002", wordsTheory.ONE_LT_dimword)  (* ``1 < dimword(:'a)`` *)
  val _ = s ("p003", S ``255 < dimword (:8)``)
  val _ = s ("p004", S ``FINITE univ(:unit)``)
  val _ = s ("p005", S ``FINITE univ(:16)``)
  val _ = s ("p006", S ``FINITE univ(:24)``)
  val _ = s ("p007", S ``FINITE univ(:30)``)
  val _ = s ("p008", S ``FINITE univ(:31)``)
  val _ = s ("p009", S ``dimindex (:8) <= dimindex (:32)``)

  val _ = Theory.export_theory ()
