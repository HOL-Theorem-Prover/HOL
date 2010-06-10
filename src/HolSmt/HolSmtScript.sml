(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Various theorems for HolSmtLib. *)

structure HolSmtScript =
struct

  val T = tautLib.TAUT_PROVE
  val P = bossLib.PROVE []
  val S = simpLib.SIMP_PROVE (simpLib.++ (simpLib.++ (simpLib.++
    (bossLib.list_ss, boolSimps.COND_elim_ss), wordsLib.WORD_ss),
    wordsLib.WORD_BIT_EQ_ss)) [boolTheory.EQ_SYM_EQ]
  val A = intLib.ARITH_PROVE
  val R = realLib.REAL_ARITH
  val W = wordsLib.WORD_DECIDE
  val B = fn t => Tactical.prove (t, blastLib.BBLAST_TAC)

  (*TODO*) fun X t = Thm.mk_thm ([], t)

  (* simplify 't' using 'thms', then prove the simplified term using
     'TAUT_PROVE' *)
  fun U thms t =
  let
    val t_eq_t' = simpLib.SIMP_CONV (simpLib.++ (simpLib.++ (bossLib.std_ss,
      wordsLib.WORD_ss), wordsLib.WORD_BIT_EQ_ss)) thms t
    val t' = tautLib.TAUT_PROVE (boolSyntax.rhs (Thm.concl t_eq_t'))
  in
    Thm.EQ_MP (Thm.SYM t_eq_t') t'
  end

  val s = Theory.save_thm

  val _ = Theory.new_theory "HolSmt"

  (* constants used by Z3 (internally, but they also appear in proofs) *)

  (* exclusive or *)
  val xor_def = bossLib.Define`
    xor x y = ~(x <=> y)
  `;

  (* ternary xor (i.e., the lower output bit of a full adder) *)
  val xor3_def = bossLib.Define`
    xor3 x y z = xor (xor x y) z
  `;

  (* the carry output of a full adder *)
  val carry_def = bossLib.Define`
    carry x y z = (x /\ y) \/ (x /\ z) \/ (y /\ z)
  `;

  (* used for Z3 proof reconstruction *)

  val _ = s ("ALL_DISTINCT_NIL", S ``ALL_DISTINCT [] = T``)
  val _ = s ("ALL_DISTINCT_CONS", S
    ``!h t. ALL_DISTINCT (h::t) = ~MEM h t /\ ALL_DISTINCT t``)
  val _ = s ("NOT_MEM_NIL", S ``!x. ~MEM x [] = T``)
  val _ = s ("NOT_MEM_CONS", S ``!x h t. ~MEM x (h::t) = (x <> h) /\ ~MEM x t``)
  val _ = s ("NOT_MEM_CONS_SWAP", S
    ``!x h t. ~MEM x (h::t) = (h <> x) /\ ~MEM x t``)
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
  val _ = s ("NEG_IFF_1", T ``!p q. (p <=> q) ==> ~(q <=> ~p)``)
  val _ = s ("NEG_IFF_2", T ``!p q. ~(p <=> ~q) ==> (q <=> p)``)
  val _ = s ("DISJ_ELIM_1", T ``!p q r. (p \/ q ==> r) ==> p ==> r``)
  val _ = s ("DISJ_ELIM_2", T ``!p q r. (p \/ q ==> r) ==> q ==> r``)
  val _ = s ("IMP_DISJ_1", T ``!p q. (p ==> q) ==> ~p \/ q``)
  val _ = s ("IMP_DISJ_2", T ``!p q. (~p ==> q) ==> p \/ q``)
  val _ = s ("IMP_FALSE", T ``!p. (~p ==> F) ==> p``)

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
  val _ = s ("d011", T ``p \/ q \/ ~(p <=> ~q)``)
  val _ = s ("d012", T ``(~p /\ ~q) \/ p \/ q``)
  val _ = s ("d013", T ``(~p /\ q) \/ p \/ ~q``)
  val _ = s ("d014", T ``(p /\ ~q) \/ ~p \/ q``)
  val _ = s ("d015", T ``(p /\ q) \/ ~p \/ ~q``)
  val _ = s ("d016", U [xor3_def, xor_def] ``~xor3 p q r \/ ~p \/ ~q \/ r``)
  val _ = s ("d017", U [xor3_def, xor_def] ``~xor3 p q r \/ ~p \/ q \/ ~r``)
  val _ = s ("d018", U [xor3_def, xor_def] ``~xor3 p q r \/ p \/ ~q \/ ~r``)
  val _ = s ("d019", U [xor3_def, xor_def] ``~xor3 p q r \/ p \/ q \/ r``)
  val _ = s ("d020", U [xor3_def, xor_def] ``xor3 p q r \/ ~p \/ ~q \/ ~r``)
  val _ = s ("d021", U [xor3_def, xor_def] ``xor3 p q r \/ ~p \/ q \/ r``)
  val _ = s ("d022", U [xor3_def, xor_def] ``xor3 p q r \/ p \/ ~q \/ r``)
  val _ = s ("d023", U [xor3_def, xor_def] ``xor3 p q r \/ p \/ q \/ ~r``)
  val _ = s ("d024", U [carry_def] ``~carry p q r \/ p \/ q``)
  val _ = s ("d025", U [carry_def] ``~carry p q r \/ p \/ r``)
  val _ = s ("d026", U [carry_def] ``~carry p q r \/ q \/ r``)
  val _ = s ("d027", U [carry_def] ``carry p q r \/ ~p \/ ~q``)
  val _ = s ("d028", U [carry_def] ``carry p q r \/ ~p \/ ~r``)
  val _ = s ("d029", U [carry_def] ``carry p q r \/ ~q \/ ~r``)
  val _ = s ("d030", P ``p \/ (x = if p then y else x)``)
  val _ = s ("d031", P ``~p \/ (x = if p then x else y)``)
  val _ = s ("d032", P ``p \/ ((if p then x else y) = y)``)
  val _ = s ("d033", P ``~p \/ ((if p then x else y) = x)``)
  val _ = s ("d034", P ``p \/ q \/ ~(if p then r else q)``)
  val _ = s ("d035", P ``~p \/ q \/ ~(if p then q else r)``)
  val _ = s ("d036", P ``(if p then q else r) \/ ~p \/ ~q``)
  val _ = s ("d037", P ``(if p then q else r) \/ p \/ ~r``)
  val _ = s ("d038", P ``~(if p then q else r) \/ ~p \/ q``)
  val _ = s ("d039", P ``~(if p then q else r) \/ p \/ r``)

  (* used for Z3's proof rule rewrite *)

  val _ = s ("r001", P ``(x = y) <=> (y = x)``)
  val _ = s ("r002", P ``(x = x) <=> T``)
  val _ = s ("r003", T ``(p <=> T) <=> p``)
  val _ = s ("r004", T ``(p <=> F) <=> ~p``)
  val _ = s ("r005", T ``(~p <=> ~q) <=> (p <=> q)``)

  val _ = s ("r006", P ``(if ~p then x else y) = (if p then y else x)``)
  val _ = s ("r007", P
    ``(if p then (if q then x else y) else x) = (if p /\ ~q then y else x)``)
  val _ = s ("r008", P
    ``(if p then (if q then x else y) else y) = (if p /\ q then x else y)``)
  val _ = s ("r009", P
    ``(if p then (if q then x else y) else y) = (if q /\ p then x else y)``)
  val _ = s ("r010", P
    ``(if p then x else (if q then x else y)) <=> (if p \/ q then x else y)``)
  val _ = s ("r011", P
    ``(if p then x else (if q then x else y)) <=> (if q \/ p then x else y)``)
  val _ = s ("r012", P
    ``(if p then x = y else x = z) <=> (x = if p then y else z)``)
  val _ = s ("r013", P
    ``(if p then x = y else y = z) <=> (y = if p then x else z)``)
  val _ = s ("r014", P
    ``(if p then x = y else z = y) <=> (y = if p then x else z)``)

  val _ = s ("r015", T ``(~p ==> q) <=> (p \/ q)``)
  val _ = s ("r016", T ``(~p ==> q) <=> (q \/ p)``)
  val _ = s ("r017", T ``(p ==> q) <=> (~p \/ q)``)
  val _ = s ("r018", T ``(p ==> q) <=> (q \/ ~p)``)
  val _ = s ("r019", T ``(T ==> p) <=> p``)
  val _ = s ("r020", T ``(p ==> T) <=> T``)
  val _ = s ("r021", T ``(F ==> p) <=> T``)
  val _ = s ("r022", T ``(p ==> p) <=> T``)
  val _ = s ("r023", T ``((p <=> q) ==> r) <=> (r \/ (q <=> ~p))``)

  val _ = s ("r024", T ``~T <=> F``)
  val _ = s ("r025", T ``~F <=> T``)
  val _ = s ("r026", T ``~~p <=> p``)

  val _ = s ("r027", T ``p \/ q <=> q \/ p``)
  val _ = s ("r028", T ``p \/ T <=> T``)
  val _ = s ("r029", T ``p \/ ~p <=> T``)
  val _ = s ("r030", T ``~p \/ p <=> T``)
  val _ = s ("r031", T ``T \/ p <=> T``)
  val _ = s ("r032", T ``p \/ F <=> p``)
  val _ = s ("r033", T ``F \/ p <=> p``)

  val _ = s ("r034", T ``p /\ q <=> q /\ p``)
  val _ = s ("r035", T ``p /\ T <=> p``)
  val _ = s ("r036", T ``T /\ p <=> p``)
  val _ = s ("r037", T ``p /\ F <=> F``)
  val _ = s ("r038", T ``F /\ p <=> F``)
  val _ = s ("r039", T ``p /\ q <=> ~(~p \/ ~q)``)
  val _ = s ("r040", T ``~p /\ q <=> ~(p \/ ~q)``)
  val _ = s ("r041", T ``p /\ ~q <=> ~(~p \/ q)``)
  val _ = s ("r042", T ``~p /\ ~q <=> ~(p \/ q)``)
  val _ = s ("r043", T ``p /\ q <=> ~(~q \/ ~p)``)
  val _ = s ("r044", T ``~p /\ q <=> ~(~q \/ p)``)
  val _ = s ("r045", T ``p /\ ~q <=> ~(q \/ ~p)``)
  val _ = s ("r046", T ``~p /\ ~q <=> ~(q \/ p)``)

  val _ = s ("r047", S ``ALL_DISTINCT [x; x] <=> F``)
  val _ = s ("r048", S ``ALL_DISTINCT [x; y] <=> x <> y``)
  val _ = s ("r049", S ``ALL_DISTINCT [x; y] <=> y <> x``)

  val _ = s ("r050", A ``((x :int) = y) <=> (x + -1 * y = 0)``)
  val _ = s ("r051", A ``((x :int) = y + z) <=> (x + -1 * z = y)``)
  val _ = s ("r052", A ``((x :int) = y + -1 * z) <=> (x + (-1 * y + z) = 0)``)
  val _ = s ("r053", A ``((x :int) = -1 * y + z) <=> (y + (-1 * z + x) = 0)``)
  val _ = s ("r054", A ``((x :int) = y + z) <=> (x + (-1 * y + -1 * z) = 0)``)
  val _ = s ("r055", A ``((x :int) = y + z) <=> (y + (z + -1 * x) = 0)``)
  val _ = s ("r056", A ``((x :int) = y + z) <=> (y + (-1 * x + z) = 0)``)
  val _ = s ("r057", A ``((x :int) = y + z) <=> (z + -1 * x = -y)``)
  val _ = s ("r058", A ``((x :int) = -y + z) <=> (z + -1 * x = y)``)
  val _ = s ("r059", A ``(-1 * (x :int) = -y) <=> (x = y)``)
  val _ = s ("r060", A ``(-1 * (x :int) + y = z) <=> (x + -1 * y = -z)``)
  val _ = s ("r061", A ``((x :int) + y = 0) <=> (y = -x)``)
  val _ = s ("r062", A ``((x :int) + y = z) <=> (y + -1 * z = -x)``)
  val _ = s ("r063", A
    ``((a :int) + (-1 * x + (v * y + w * z)) = 0) <=> (x + (-v * y + -w * z) = a)``)

  val _ = s ("r064", A ``0 + (x :int) = x``)
  val _ = s ("r065", A ``(x :int) + 0 = x``)
  val _ = s ("r066", A ``(x :int) + y = y + x``)
  val _ = s ("r067", A ``(x :int) + x = 2 * x``)
  val _ = s ("r068", A ``(x :int) + y + z = x + (y + z)``)
  val _ = s ("r069", A ``(x :int) + y + z = x + (z + y)``)
  val _ = s ("r070", A ``(x :int) + (y + z) = y + (z + x)``)
  val _ = s ("r071", A ``(x :int) + (y + z) = y + (x + z)``)
  val _ = s ("r072", A ``(x :int) + (y + (z + u)) = y + (z + (u + x))``)

  val _ = s ("r073", A ``(x :int) >= x <=> T``)
  val _ = s ("r074", A ``(x :int) >= y <=> x + -1 * y >= 0``)
  val _ = s ("r075", A ``(x :int) >= y <=> y + -1 * x <= 0``)
  val _ = s ("r076", A ``(x :int) >= y + z <=> y + (z + -1 * x) <= 0``)
  val _ = s ("r077", A ``-1 * (x :int) >= 0 <=> x <= 0``)
  val _ = s ("r078", A ``-1 * (x :int) >= -y <=> x <= y``)
  val _ = s ("r079", A ``-1 * (x :int) + y >= 0 <=> x + -1 * y <= 0``)
  val _ = s ("r080", A ``(x :int) + -1 * y >= 0 <=> y <= x``)

  val _ = s ("r081", A ``(x :int) > y <=> ~(y >= x)``)
  val _ = s ("r082", A ``(x :int) > y <=> ~(x <= y)``)
  val _ = s ("r083", A ``(x :int) > y <=> ~(x + -1 * y <= 0)``)
  val _ = s ("r084", A ``(x :int) > y <=> ~(y + -1 * x >= 0)``)
  val _ = s ("r085", A ``(x :int) > y + z <=> ~(z + -1 * x >= -y)``)

  val _ = s ("r086", A ``x <= (x :int) <=> T``)
  val _ = s ("r087", A ``0 <= (1 :int) <=> T``)
  val _ = s ("r088", A ``(x :int) <= y <=> y >= x``)
  val _ = s ("r089", A ``0 <= -(x :int) + y <=> y >= x``)
  val _ = s ("r090", A ``-1 * (x :int) <= 0 <=> x >= 0``)
  val _ = s ("r091", A ``(x :int) <= y <=> x + -1 * y <= 0``)
  val _ = s ("r092", A ``(x :int) <= y <=> y + -1 * x >= 0``)
  val _ = s ("r093", A ``-1 * (x :int) + y <= 0 <=> x + -1 * y >= 0``)
  val _ = s ("r094", A ``-1 * (x :int) + y <= -z <=> x + -1 * y >= z``)
  val _ = s ("r095", A ``-(x :int) + y <= z <=> y + -1 * z <= x``)
  val _ = s ("r096", A ``(x :int) + -1 * y <= z <=> x + (-1 * y + -1 * z) <= 0``)
  val _ = s ("r097", A ``(x :int) <= y + z <=> x + -1 * z <= y``)
  val _ = s ("r098", A ``(x :int) <= y + z <=> z + -1 * x >= -y``)
  val _ = s ("r099", A ``(x :int) <= y + z <=> x + (-1 * y + -1 * z) <= 0``)

  val _ = s ("r100", A ``(x :int) < y <=> ~(y <= x)``)
  val _ = s ("r101", A ``(x :int) < y <=> ~(x >= y)``)
  val _ = s ("r102", A ``(x :int) < y <=> ~(y + -1 * x <= 0)``)
  val _ = s ("r103", A ``(x :int) < y <=> ~(x + -1 * y >= 0)``)
  val _ = s ("r104", A ``(x :int) < y + -1 * z <=> ~(x + -1 * y + z >= 0)``)
  val _ = s ("r105", A ``(x :int) < y + -1 * z <=> ~(x + (-1 * y + z) >= 0)``)
  val _ = s ("r106", A ``(x :int) < -y + z <=> ~(z + -1 * x <= y)``)
  val _ = s ("r107", A ``(x :int) < -y + (z + u) <=> ~(z + (u + -1 * x) <= y)``)
  val _ = s ("r108", A
    ``(x :int) < -y + (z + (u + v)) <=> ~(z + (u + (v + -1 * x)) <= y)``)

  val _ = s ("r109", A ``-(x :int) + y < z <=> ~(y + -1 * z >= x)``)
  val _ = s ("r110", A ``(x :int) + y < z <=> ~(z + -1 * y <= x)``)
  val _ = s ("r111", A ``0 < -(x :int) + y <=> ~(y <= x)``)

  val _ = s ("r112", A ``(x :int) - 0 = x``)
  val _ = s ("r113", A ``0 - (x :int) = -x``)
  val _ = s ("r114", A ``0 - (x :int) = -1 * x``)
  val _ = s ("r115", A ``(x :int) - y = -y + x``)
  val _ = s ("r116", A ``(x :int) - y = x + -1 * y``)
  val _ = s ("r117", A ``(x :int) - y = -1 * y + x``)
  val _ = s ("r118", A ``(x :int) - 1 = -1 + x``)
  val _ = s ("r119", A ``(x :int) + y - z = x + (y + -1 * z)``)
  val _ = s ("r120", A ``(x :int) + y - z = x + (-1 * z + y)``)

  val _ = s ("r121", R ``(0 = -u * (x :real)) <=> (u * x = 0)``)
  val _ = s ("r122", R ``(a = -u * (x :real)) <=> (u * x = -a)``)
  val _ = s ("r123", R ``((a :real) = x + (y + z)) <=> (x + (y + (-1 * a + z)) = 0)``)
  val _ = s ("r124", R ``((a :real) = x + (y + z)) <=> (x + (y + (z + -1 * a)) = 0)``)
  val _ = s ("r125", R ``((a :real) = -u * y + v * z) <=> (u * y + (-v * z + a) = 0)``)
  val _ = s ("r126", R ``((a :real) = -u * y + -v * z) <=> (u * y + (a + v * z) = 0)``)
  val _ = s ("r127", R ``(-(a :real) = -u * x + v * y) <=> (u * x + -v * y = a)``)
  val _ = s ("r128", R
    ``((a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + (-w * z + a)) = 0)``)
  val _ = s ("r129", R
    ``((a :real) = -u * x + (v * y + w * z)) <=> (u * x + (-v * y + -w * z) = -a)``)
  val _ = s ("r130", R
    ``((a :real) = -u * x + (v * y + -w * z)) <=> (u * x + (-v * y + w * z) = -a)``)
  val _ = s ("r131", R
    ``((a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + -w * z) = -a)``)
  val _ = s ("r132", R ``((a :real) = -u * x + (-v * y + -w * z)) <=> (u * x + (v * y + w * z) = -a)``)
  val _ = s ("r133", R ``(-(a :real) = -u * x + (v * y + w * z)) <=> (u * x + (-v * y + -w * z) = a)``)
  val _ = s ("r134", R ``(-(a :real) = -u * x + (v * y + -w * z)) <=> (u * x + (-v * y + w * z) = a)``)
  val _ = s ("r135", R ``(-(a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + -w * z) = a)``)
  val _ = s ("r136", R ``(-(a :real) = -u * x + (-v * y + -w * z)) <=> (u * x + (v * y + w * z) = a)``)
  val _ = s ("r137", R ``((a :real) = -u * x + (-1 * y + w * z)) <=> (u * x + (y + -w * z) = -a)``)
  val _ = s ("r138", R ``((a :real) = -u * x + (-1 * y + -w * z)) <=> (u * x + (y + w * z) = -a)``)
  val _ = s ("r139", R ``(-u * (x :real) + -v * y = -a) <=> (u * x + v * y = a)``)
  val _ = s ("r140", R ``(-1 * (x :real) + (-v * y + -w * z) = -a) <=> (x + (v * y + w * z) = a)``)
  val _ = s ("r141", R ``(-u * (x :real) + (v * y + w * z) = -a) <=> (u * x + (-v * y + -w * z) = a)``)
  val _ = s ("r142", R ``(-u * (x :real) + (-v * y + w * z) = -a) <=> (u * x + (v * y + -w * z) = a)``)
  val _ = s ("r143", R ``(-u * (x :real) + (-v * y + -w * z) = -a) <=> (u * x + (v * y + w * z) = a)``)

  val _ = s ("r144", R ``(x :real) + -1 * y >= 0 <=> y <= x``)
  val _ = s ("r145", R ``(x :real) >= y <=> x + -1 * y >= 0``)

  val _ = s ("r146", R ``(x :real) > y <=> ~(x + -1 * y <= 0)``)

  val _ = s ("r147", R ``(x :real) <= y <=> x + -1 * y <= 0``)
  val _ = s ("r148", R ``(x :real) <= y + z <=> x + -1 * z <= y``)
  val _ = s ("r149", R ``-u * (x :real) <= a <=> u * x >= -a``)
  val _ = s ("r150", R ``-u * (x :real) <= -a <=> u * x >= a``)
  val _ = s ("r151", R ``-u * (x :real) + v * y <= 0 <=> u * x + -v * y >= 0``)
  val _ = s ("r152", R ``-u * (x :real) + v * y <= a <=> u * x + -v * y >= -a``)
  val _ = s ("r153", R ``-u * (x :real) + v * y <= -a <=> u * x + -v * y >= a``)
  val _ = s ("r154", R ``-u * (x :real) + -v * y <= a <=> u * x + v * y >= -a``)
  val _ = s ("r155", R ``-u * (x :real) + -v * y <= -a <=> u * x + v * y >= a``)
  val _ = s ("r156", R
    ``-u * (x :real) + (v * y + w * z) <= 0 <=> u * x + (-v * y + -w * z) >= 0``)
  val _ = s ("r157", R
    ``-u * (x :real) + (v * y + -w * z) <= 0 <=> u * x + (-v * y + w * z) >= 0``)
  val _ = s ("r158", R
    ``-u * (x :real) + (-v * y + w * z) <= 0 <=> u * x + (v * y + -w * z) >= 0``)
  val _ = s ("r159", R
    ``-u * (x :real) + (-v * y + -w * z) <= 0 <=> u * x + (v * y + w * z) >= 0``)
  val _ = s ("r160", R
    ``-u * (x :real) + (v * y + w * z) <= a <=> u * x + (-v * y + -w * z) >= -a``)
  val _ = s ("r161", R
    ``-u * (x :real) + (v * y + w * z) <= -a <=> u * x + (-v * y + -w * z) >= a``)
  val _ = s ("r162", R
    ``-u * (x :real) + (v * y + -w * z) <= a <=> u * x + (-v * y + w * z) >= -a``)
  val _ = s ("r163", R
    ``-u * (x :real) + (v * y + -w * z) <= -a <=> u * x + (-v * y + w * z) >= a``)
  val _ = s ("r164", R
    ``-u * (x :real) + (-v * y + w * z) <= a <=> u * x + (v * y + -w * z) >= -a``)
  val _ = s ("r165", R
    ``-u * (x :real) + (-v * y + w * z) <= -a <=> u * x + (v * y + -w * z) >= a``)
  val _ = s ("r166", R
    ``-u * (x :real) + (-v * y + -w * z) <= a <=> u * x + (v * y + w * z) >= -a``)
  val _ = s ("r167", R
    ``-u * (x :real) + (-v * y + -w * z) <= -a <=> u * x + (v * y + w * z) >= a``)
  val _ = s ("r168", R
    ``(-1 * (x :real) + (v * y + w * z) <= -a) <=> (x + (-v * y + -w * z) >= a)``)

  val _ = s ("r169", R ``(x :real) < y <=> ~(x >= y)``)
  val _ = s ("r170", R ``-u * (x :real) < a <=> ~(u * x <= -a)``)
  val _ = s ("r171", R ``-u * (x :real) < -a <=> ~(u * x <= a)``)
  val _ = s ("r172", R ``-u * (x :real) + v * y < 0 <=> ~(u * x + -v * y <= 0)``)
  val _ = s ("r173", R ``-u * (x :real) + -v * y < 0 <=> ~(u * x + v * y <= 0)``)
  val _ = s ("r174", R ``-u * (x :real) + v * y < a <=> ~(u * x + -v * y <= -a)``)
  val _ = s ("r175", R ``-u * (x :real) + v * y < -a <=> ~(u * x + -v * y <= a)``)
  val _ = s ("r176", R ``-u * (x :real) + -v * y < a <=> ~(u * x + v * y <= -a)``)
  val _ = s ("r177", R ``-u * (x :real) + -v * y < -a <=> ~(u * x + v * y <= a)``)
  val _ = s ("r178", R
    ``-u * (x :real) + (v * y + w * z) < a <=> ~(u * x + (-v * y + -w * z) <= -a)``)
  val _ = s ("r179", R
    ``-u * (x :real) + (v * y + w * z) < -a <=> ~(u * x + (-v * y + -w * z) <= a)``)
  val _ = s ("r180", R
    ``-u * (x :real) + (v * y + -w * z) < a <=> ~(u * x + (-v * y + w * z) <= -a)``)
  val _ = s ("r181", R
    ``-u * (x :real) + (v * y + -w * z) < -a <=> ~(u * x + (-v * y + w * z) <= a)``)
  val _ = s ("r182", R
    ``-u * (x :real) + (-v * y + w * z) < a <=> ~(u * x + (v * y + -w * z) <= -a)``)
  val _ = s ("r183", R
    ``-u * (x :real) + (-v * y + w * z) < -a <=> ~(u * x + (v * y + -w * z) <= a)``)
  val _ = s ("r184", R
    ``-u * (x :real) + (-v * y + -w * z) < a <=> ~(u * x + (v * y + w * z) <= -a)``)
  val _ = s ("r185", R
    ``-u * (x :real) + (-v * y + -w * z) < -a <=> ~(u * x + (v * y + w * z) <= a)``)
  val _ = s ("r186", R
    ``-u * (x :real) + (-v * y + w * z) < 0 <=> ~(u * x + (v * y + -w * z) <= 0)``)
  val _ = s ("r187", R
    ``-u * (x :real) + (-v * y + -w * z) < 0 <=> ~(u * x + (v * y + w * z) <= 0)``)
  val _ = s ("r188", R
    ``-1 * (x :real) + (v * y + w * z) < a <=> ~(x + (-v * y + -w * z) <= -a)``)
  val _ = s ("r189", R
    ``-1 * (x :real) + (v * y + w * z) < -a <=> ~(x + (-v * y + -w * z) <= a)``)
  val _ = s ("r190", R
    ``-1 * (x :real) + (v * y + -w * z) < a <=> ~(x + (-v * y + w * z) <= -a)``)
  val _ = s ("r191", R
    ``-1 * (x :real) + (v * y + -w * z) < -a <=> ~(x + (-v * y + w * z) <= a)``)
  val _ = s ("r192", R
    ``-1 * (x :real) + (-v * y + w * z) < a <=> ~(x + (v * y + -w * z) <= -a)``)
  val _ = s ("r193", R
    ``-1 * (x :real) + (-v * y + w * z) < -a <=> ~(x + (v * y + -w * z) <= a)``)
  val _ = s ("r194", R
    ``-1 * (x :real) + (-v * y + -w * z) < a <=> ~(x + (v * y + w * z) <= -a)``)
  val _ = s ("r195", R
    ``-1 * (x :real) + (-v * y + -w * z) < -a <=> ~(x + (v * y + w * z) <= a)``)
  val _ = s ("r196", R
    ``-u * (x :real) + (-1 * y + -w * z) < -a <=> ~(u * x + (y + w * z) <= a)``)
  val _ = s ("r197", R
    ``-u * (x :real) + (v * y + -1 * z) < -a <=> ~(u * x + (-v * y + z) <= a)``)

  val _ = s ("r198", R ``0 + (x :real) = x``)
  val _ = s ("r199", R ``(x :real) + 0 = x``)
  val _ = s ("r200", R ``(x :real) + y = y + x``)
  val _ = s ("r201", R ``(x :real) + x = 2 * x``)
  val _ = s ("r202", R ``(x :real) + y + z = x + (y + z)``)
  val _ = s ("r203", R ``(x :real) + y + z = x + (z + y)``)
  val _ = s ("r204", R ``(x :real) + (y + z) = y + (z + x)``)
  val _ = s ("r205", R ``(x :real) + (y + z) = y + (x + z)``)

  val _ = s ("r206", R ``0 - (x :real) = -x``)
  val _ = s ("r207", R ``0 - u * (x :real) = -u * x``)
  val _ = s ("r208", R ``(x :real) - 0 = x``)
  val _ = s ("r209", R ``(x :real) - y = x + -1 * y``)
  val _ = s ("r210", R ``(x :real) - y = -1 * y + x``)
  val _ = s ("r211", R ``(x :real) - u * y = x + -u * y``)
  val _ = s ("r212", R ``(x :real) - u * y = -u * y + x``)
  val _ = s ("r213", R ``(x :real) + y - z = x + (y + -1 * z)``)
  val _ = s ("r214", R ``(x :real) + y - z = x + (-1 * z + y)``)
  val _ = s ("r215", R ``(x :real) + y - u * z = -u * z + (x + y)``)
  val _ = s ("r216", R ``(x :real) + y - u * z = x + (-u * z + y)``)
  val _ = s ("r217", R ``(x :real) + y - u * z = x + (y + -u * z)``)

  val _ = s ("r218", R ``0 * (x :real) = 0``)
  val _ = s ("r219", R ``1 * (x :real) = x``)

  val _ = s ("r220", W ``0w + x = x``)
  val _ = s ("r221", W ``(x :'a word) + y = y + x``)
  val _ = s ("r222", W ``1w + (1w + x) = 2w + x``)

  val _ = s ("r223", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0] ``FINITE univ(:'a) ==> x < dimword(:'b) ==>
      ((0w :'a word) @@ (n2w x :'b word) = (n2w x :'c word))``))
  val _ = s ("r224", Drule.UNDISCH (simpLib.SIMP_PROVE bossLib.std_ss
    [wordsTheory.w2w_n2w, Thm.SYM (Drule.SPEC_ALL wordsTheory.MOD_DIMINDEX)]
    ``x < dimword(:'a) ==> (w2w (n2w x :'a word) = (n2w x :'b word))``))
  val _ = s ("r225", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((0w :'a word) @@ (x :'b word) = (n2w y :'c word)) <=> (x = n2w y))``))
  val _ = s ("r226", Drule.UNDISCH_ALL (bossLib.PROVE
      [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((0w :'a word) @@ (x :'b word) = (n2w y :'c word)) <=> (n2w y = x))``))
  val _ = s ("r227", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((n2w y :'c word) = (0w :'a word) @@ (x :'b word)) <=> (x = n2w y))``))
  val _ = s ("r228", Drule.UNDISCH_ALL (bossLib.PROVE
    [wordsTheory.word_concat_0_eq] ``FINITE univ(:'a) ==>
      dimindex(:'b) <= dimindex(:'c) ==> y < dimword(:'b) ==>
      (((n2w y :'c word) = (0w :'a word) @@ (x :'b word)) <=> (n2w y = x))``))

  val _ = s ("r229", W ``x && y = y && x``)
  val _ = s ("r230", W ``x && y && z = y && x && z``)
  val _ = s ("r231", W ``x && y && z = (x && y) && z``)
  val _ = s ("r232", W ``(1w = (x :word1) && y) <=> (1w = x) /\ (1w = y)``)
  val _ = s ("r233", W ``(1w = (x :word1) && y) <=> (1w = y) /\ (1w = x)``)
  val _ = s ("r234", W ``(7 >< 0) (x :word8) = x``)
  val _ = s ("r235", W ``x <+ y <=> ~(y <=+ x)``)
  val _ = s ("r236", W ``(x :'a word) * y = y * x``)
  val _ = s ("r237", W ``(0 >< 0) (x :word1) = x``)
  val _ = s ("r238", W ``(x && y) && z = x && y && z``)
  val _ = s ("r239", W ``0w !! x = x``)

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

  val _ = s ("t012", Tactical.prove (``(x :'a word) <> ~x``,
    let
      val RW = bossLib.RW_TAC (bossLib.++ (bossLib.bool_ss, fcpLib.FCP_ss))
    in
      Tactical.THEN (RW [],
        Tactical.THEN (Tactic.EXISTS_TAC ``0 :num``,
          Tactical.THEN (RW [wordsTheory.DIMINDEX_GT_0,
              wordsTheory.word_1comp_def],
            tautLib.TAUT_TAC)))
    end))
  val _ = s ("t013", W ``(x = y) ==> x ' i ==> y ' i``)
  val _ = s ("t014", S ``(1w = ~(x :word1)) \/ x ' 0``)
  val _ = s ("t015", S ``(x :word1) ' 0 ==> (0w = ~x)``)
  val _ = s ("t016", S ``(x :word1) ' 0 ==> (1w = x)``)
  val _ = s ("t017", S ``~((x :word1) ' 0) ==> (0w = x)``)
  val _ = s ("t018", S ``~((x :word1) ' 0) ==> (1w = ~x)``)
  val _ = s ("t019", S ``(0w = ~(x :word1)) \/ ~(x ' 0)``)
  val _ = s ("t020", U []
    ``(1w = ~(x :word1) !! ~y) \/ ~(~(x ' 0) \/ ~(y ' 0))``)
  val _ = s ("t021", U []
    ``(0w = (x :word8)) \/ x ' 0 \/ x ' 1 \/ x ' 2 \/ x ' 3 \/ x ' 4 \/ x ' 5 \/ x ' 6 \/ x ' 7``)
  val _ = s ("t022", S
    ``(((x :word1) = 1w) <=> p) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t023", S
    ``((1w = (x :word1)) <=> p) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t024", S
    ``(p <=> ((x :word1) = 1w)) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t025", S
    ``(p <=> (1w = (x :word1))) <=> (x = if p then 1w else 0w)``)
  val _ = s ("t026", B
    ``(0w:word32 = 0xFFFFFFFFw * sw2sw (x :word8)) ==> ~(x ' 0)``)
  val _ = s ("t027", B
    ``(0w:word32 = 0xFFFFFFFFw * sw2sw (x :word8)) ==> ~(x ' 1 <=> ~(x ' 0))``)
  val _ = s ("t028", B ``(0w:word32 = 0xFFFFFFFFw * sw2sw (x :word8)) ==>
      ~(x ' 2 <=> ~(x ' 0) /\ ~(x ' 1))``)
  val _ = s ("t029", X ``(1w + (x :'a word) = y) ==> x ' 0 ==> ~(y ' 0)``)

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

end
