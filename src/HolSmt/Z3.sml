(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Functions to invoke the Z3 SMT solver *)

structure Z3 = struct

  fun write_strings_to_file path strings =
  let val outstream = TextIO.openOut path
  in
    ignore (List.map (TextIO.output o Lib.pair outstream) strings);
    TextIO.closeOut outstream
  end

  (* returns SAT if Z3 reported 'sat_line', UNSAT if Z3 reported 'unsat_line' *)
  fun is_sat sat_line unsat_line path =
    let val instream = TextIO.openIn path
        (* skip over Z3's other output (e.g., proofs) *)
        fun last_line () =
          let val line = TextIO.inputLine instream
          in
            if TextIO.endOfStream instream then
              line
            else
              last_line ()
          end
        val line = last_line ()
    in
      TextIO.closeIn instream;
      if line = SOME sat_line then
        SolverSpec.SAT NONE
      else if line = SOME unsat_line then
        SolverSpec.UNSAT NONE
      else
        SolverSpec.UNKNOWN NONE
    end

  (* DOS-style CR/LF line breaks *)
  val is_sat_DOS = is_sat "sat\r\n" "unsat\r\n"

  (* Unix-style line breaks *)
  val is_sat_Unix = is_sat "sat\n" "unsat\n"

  (*** proof reconstruction ***)

  (* Rules marked with "1" are only used in compressed Z3 proofs (PROOF_MODE=1).
     Other rules that are commented out are just not used in any of the
     benchmarks/proofs I've tried so far. *)

  datatype proofterm = AND_ELIM of int * Term.term
                  (* | APPLY_DEF of int * Term.term *)
                     | ASSERTED of Term.term
               (* 1: | CNF_STAR of ... *)
                     | COMMUTATIVITY of Term.term
                     | DEF_AXIOM of Term.term
                  (* | DEF_INTRO of Term.term *)
                  (* | DER of Term.term *)
                  (* | DISTRIBUTIVITY of Term.term *)
                     | ELIM_UNUSED of Term.term
                  (* | GOAL of Term.term *)
                     | HYPOTHESIS of Term.term
                     | IFF_FALSE of int * Term.term
                  (* | IFF_TILDE of int * Term.term *)
                     | IFF_TRUE of int * Term.term
                     | LEMMA of int * Term.term
                     | MONOTONICITY of int list * Term.term
                     | MP of int * int * Term.term
                     | MP_TILDE of int * int * Term.term
                     | NNF_NEG of int list * Term.term
                     | NNF_POS of int list * Term.term
               (* 1: | NNF_STAR of int list * Term.term *)
                     | NOT_OR_ELIM of int * Term.term
                     | PULL_QUANT of Term.term
               (* 1: | PULL_QUANT_STAR of Term.term *)
                  (* | PUSH_QUANT of ... *)
                     | QUANT_INST of Term.term
                     | QUANT_INTRO of int * Term.term
                     | REFL of Term.term
                     | REWRITE of Term.term
                     | REWRITE_STAR of int list * Term.term
                     | SK of Term.term
                     | SYMM of int * Term.term
                     | TH_LEMMA of int list * Term.term
                     | TRANS of int * int * Term.term
               (* 1: | TRANS_STAR of int list * Term.term *)
                     | TRUE_AXIOM of Term.term
                     | UNIT_RESOLUTION of int list * Term.term
                     | THEOREM of Thm.thm

  (* Z3 assigns no ID to the final '|- F'; we will use ID 0 *)
  type proof = (int, proofterm) Redblackmap.dict

  (* proforma theorems *)

  val def_axiom_thms = List.foldl (fn (th, net) =>
    Net.insert (Thm.concl th, th) net) Net.empty
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

  val rewrite_thms = List.foldl (fn (th, net) =>
    Net.insert (Thm.concl th, th) net) Net.empty
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
    intLib.ARITH_PROVE ``((a :int) + (-1 * x + (v * y + w * z)) = 0) <=> (x + (-v * y + -w * z) = a)``,

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
    intLib.ARITH_PROVE
      ``(x :int) + -1 * y <= z <=> x + (-1 * y + -1 * z) <= 0``,
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
    intLib.ARITH_PROVE
      ``(x :int) < -y + (z + (u + v)) <=> ~(z + (u + (v + -1 * x)) <= y)``,

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

    realLib.REAL_ARITH
      ``(0 = -u * (x :real)) <=> (u * x = 0)``,
    realLib.REAL_ARITH
      ``(a = -u * (x :real)) <=> (u * x = -a)``,
    realLib.REAL_ARITH
      ``((a :real) = x + (y + z)) <=> (x + (y + (-1 * a + z)) = 0)``,
    realLib.REAL_ARITH
      ``((a :real) = x + (y + z)) <=> (x + (y + (z + -1 * a)) = 0)``,
    realLib.REAL_ARITH
      ``((a :real) = -u * y + v * z) <=> (u * y + (-v * z + a) = 0)``,
    realLib.REAL_ARITH
      ``((a :real) = -u * y + -v * z) <=> (u * y + (a + v * z) = 0)``,
    realLib.REAL_ARITH
      ``(-(a :real) = -u * x + v * y) <=> (u * x + -v * y = a)``,
    realLib.REAL_ARITH
      ``((a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + (-w * z + a)) = 0)``,
    realLib.REAL_ARITH
      ``((a :real) = -u * x + (v * y + w * z)) <=> (u * x + (-v * y + -w * z) = -a)``,
    realLib.REAL_ARITH
      ``((a :real) = -u * x + (v * y + -w * z)) <=> (u * x + (-v * y + w * z) = -a)``,
    realLib.REAL_ARITH
      ``((a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + -w * z) = -a)``,
    realLib.REAL_ARITH
      ``((a :real) = -u * x + (-v * y + -w * z)) <=> (u * x + (v * y + w * z) = -a)``,
    realLib.REAL_ARITH
      ``(-(a :real) = -u * x + (v * y + w * z)) <=> (u * x + (-v * y + -w * z) = a)``,
    realLib.REAL_ARITH
      ``(-(a :real) = -u * x + (v * y + -w * z)) <=> (u * x + (-v * y + w * z) = a)``,
    realLib.REAL_ARITH
      ``(-(a :real) = -u * x + (-v * y + w * z)) <=> (u * x + (v * y + -w * z) = a)``,
    realLib.REAL_ARITH
      ``(-(a :real) = -u * x + (-v * y + -w * z)) <=> (u * x + (v * y + w * z) = a)``,
    realLib.REAL_ARITH
      ``((a :real) = -u * x + (-1 * y + w * z)) <=> (u * x + (y + -w * z) = -a)``,
    realLib.REAL_ARITH
      ``((a :real) = -u * x + (-1 * y + -w * z)) <=> (u * x + (y + w * z) = -a)``,
    realLib.REAL_ARITH
      ``(-u * (x :real) + -v * y = -a) <=> (u * x + v * y = a)``,
    realLib.REAL_ARITH
      ``(-1 * (x :real) + (-v * y + -w * z) = -a) <=> (x + (v * y + w * z) = a)``,
    realLib.REAL_ARITH
      ``(-u * (x :real) + (v * y + w * z) = -a) <=> (u * x + (-v * y + -w * z) = a)``,
    realLib.REAL_ARITH
      ``(-u * (x :real) + (-v * y + w * z) = -a) <=> (u * x + (v * y + -w * z) = a)``,
    realLib.REAL_ARITH
      ``(-u * (x :real) + (-v * y + -w * z) = -a) <=> (u * x + (v * y + w * z) = a)``,

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
    realLib.REAL_ARITH
      ``-u * (x :real) + (v * y + w * z) <= 0 <=> u * x + (-v * y + -w * z) >= 0``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (v * y + -w * z) <= 0 <=> u * x + (-v * y + w * z) >= 0``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (-v * y + w * z) <= 0 <=> u * x + (v * y + -w * z) >= 0``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (-v * y + -w * z) <= 0 <=> u * x + (v * y + w * z) >= 0``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (v * y + w * z) <= a <=> u * x + (-v * y + -w * z) >= -a``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (v * y + w * z) <= -a <=> u * x + (-v * y + -w * z) >= a``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (v * y + -w * z) <= a <=> u * x + (-v * y + w * z) >= -a``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (v * y + -w * z) <= -a <=> u * x + (-v * y + w * z) >= a``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (-v * y + w * z) <= a <=> u * x + (v * y + -w * z) >= -a``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (-v * y + w * z) <= -a <=> u * x + (v * y + -w * z) >= a``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (-v * y + -w * z) <= a <=> u * x + (v * y + w * z) >= -a``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (-v * y + -w * z) <= -a <=> u * x + (v * y + w * z) >= a``,
    realLib.REAL_ARITH
      ``(-1 * (x :real) + (v * y + w * z) <= -a) <=> (x + (-v * y + -w * z) >= a)``,

    realLib.REAL_ARITH ``(x :real) < y <=> ~(x >= y)``,
    realLib.REAL_ARITH ``-u * (x :real) < a <=> ~(u * x <= -a)``,
    realLib.REAL_ARITH ``-u * (x :real) < -a <=> ~(u * x <= a)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + v * y < 0 <=> ~(u * x + -v * y <= 0)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + -v * y < 0 <=> ~(u * x + v * y <= 0)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + v * y < a <=> ~(u * x + -v * y <= -a)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + v * y < -a <=> ~(u * x + -v * y <= a)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + -v * y < a <=> ~(u * x + v * y <= -a)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + -v * y < -a <=> ~(u * x + v * y <= a)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (v * y + w * z) < a <=> ~(u * x + (-v * y + -w * z) <= -a)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (v * y + w * z) < -a <=> ~(u * x + (-v * y + -w * z) <= a)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (v * y + -w * z) < a <=> ~(u * x + (-v * y + w * z) <= -a)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (v * y + -w * z) < -a <=> ~(u * x + (-v * y + w * z) <= a)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (-v * y + w * z) < a <=> ~(u * x + (v * y + -w * z) <= -a)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (-v * y + w * z) < -a <=> ~(u * x + (v * y + -w * z) <= a)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (-v * y + -w * z) < a <=> ~(u * x + (v * y + w * z) <= -a)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (-v * y + -w * z) < -a <=> ~(u * x + (v * y + w * z) <= a)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (-v * y + w * z) < 0 <=> ~(u * x + (v * y + -w * z) <= 0)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (-v * y + -w * z) < 0 <=> ~(u * x + (v * y + w * z) <= 0)``,
    realLib.REAL_ARITH
      ``-1 * (x :real) + (v * y + w * z) < a <=> ~(x + (-v * y + -w * z) <= -a)``,
    realLib.REAL_ARITH
      ``-1 * (x :real) + (v * y + w * z) < -a <=> ~(x + (-v * y + -w * z) <= a)``,
    realLib.REAL_ARITH
      ``-1 * (x :real) + (v * y + -w * z) < a <=> ~(x + (-v * y + w * z) <= -a)``,
    realLib.REAL_ARITH
      ``-1 * (x :real) + (v * y + -w * z) < -a <=> ~(x + (-v * y + w * z) <= a)``,
    realLib.REAL_ARITH
      ``-1 * (x :real) + (-v * y + w * z) < a <=> ~(x + (v * y + -w * z) <= -a)``,
    realLib.REAL_ARITH
      ``-1 * (x :real) + (-v * y + w * z) < -a <=> ~(x + (v * y + -w * z) <= a)``,
    realLib.REAL_ARITH
      ``-1 * (x :real) + (-v * y + -w * z) < a <=> ~(x + (v * y + w * z) <= -a)``,
    realLib.REAL_ARITH
      ``-1 * (x :real) + (-v * y + -w * z) < -a <=> ~(x + (v * y + w * z) <= a)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (-1 * y + -w * z) < -a <=> ~(u * x + (y + w * z) <= a)``,
    realLib.REAL_ARITH
      ``-u * (x :real) + (v * y + -1 * z) < -a <=> ~(u * x + (-v * y + z) <= a)``,

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

  val th_lemma_thms = List.foldl (fn (th, net) =>
    Net.insert (Thm.concl th, th) net) Net.empty
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

  fun proforma net t =
    Lib.tryfind (fn th => Drule.INST_TY_TERM (Term.match_term (Thm.concl th) t)
      th) (Net.match t net)

  val EXCLUDED_MIDDLE = bossLib.DECIDE ``!p. p \/ ~p``

  val ALL_DISTINCT_NIL = simpLib.SIMP_PROVE bossLib.list_ss []
    ``ALL_DISTINCT [] = T``
  val ALL_DISTINCT_CONS = simpLib.SIMP_PROVE bossLib.list_ss []
    ``!h t. ALL_DISTINCT (h::t) = ~MEM h t /\ ALL_DISTINCT t``
  val NOT_MEM_NIL = simpLib.SIMP_PROVE bossLib.list_ss []
    ``!x. ~MEM x [] = T``
  val NOT_MEM_CONS = simpLib.SIMP_PROVE bossLib.list_ss []
    ``!x h t. ~MEM x (h::t) = (x <> h) /\ ~MEM x t``
  val NOT_MEM_CONS_SWAP = simpLib.SIMP_PROVE bossLib.list_ss
    [boolTheory.EQ_SYM_EQ] ``!x h t. ~MEM x (h::t) = (h <> x) /\ ~MEM x t``
  val AND_T = bossLib.DECIDE ``!p. p /\ T <=> p``

  val T_AND = bossLib.DECIDE ``!p q. (T /\ p <=> T /\ q) ==> (p <=> q)``
  val F_OR = bossLib.DECIDE ``!p q. (F \/ p <=> F \/ q) ==> (p <=> q)``

  val CONJ_CONG = bossLib.DECIDE
    ``!p q r s. (p <=> q) ==> (r <=> s) ==> (p /\ r <=> q /\ s)``

  val NOT_NOT_ELIM = bossLib.DECIDE ``!p. ~~p ==> p``
  val NOT_FALSE = bossLib.DECIDE ``!p. p ==> ~p ==> F``

  val NNF_CONJ = bossLib.DECIDE
    ``!p q r s. (~p <=> r) ==> (~q <=> s) ==> (~(p /\ q) <=> r \/ s)``
  val NNF_DISJ = bossLib.DECIDE
    ``!p q r s. (~p <=> r) ==> (~q <=> s) ==> (~(p \/ q) <=> r /\ s)``
  val NNF_NOT_NOT = bossLib.DECIDE ``!p q. (p <=> q) ==> (~~p <=> q)``

  val NEG_IFF_1 = bossLib.DECIDE ``!p q. (p <=> q) ==> ~(q <=> ~p)``
  val NEG_IFF_2 = bossLib.DECIDE ``!p q. ~(p <=> ~q) ==> (q <=> p)``

  val DISJ_ELIM_1 = bossLib.DECIDE ``!p q r. (p \/ q ==> r) ==> p ==> r``
  val DISJ_ELIM_2 = bossLib.DECIDE ``!p q r. (p \/ q ==> r) ==> q ==> r``

  val IMP_DISJ_1 = bossLib.DECIDE ``!p q. (p ==> q) ==> ~p \/ q``
  val IMP_DISJ_2 = bossLib.DECIDE ``!p q. (~p ==> q) ==> p \/ q``
  val IMP_FALSE = bossLib.DECIDE ``!p. (~p ==> F) ==> p``

  fun check_proof prf =
  let
    val _ = if !SolverSpec.trace > 1 then
        Feedback.HOL_MESG "HolSmtLib: checking Z3 proof"
      else ()

    (*** references storing "global" state ***)
    (* stores definitions "sk = ..." (where sk is a variable) introduced for
       Skolemization; these are eliminated at the end of proof reconstruction *)
    val skolem_defs = ref ([] : Term.term list)
    (* stores assumptions, (only) these may remain in the final theorem *)
    val asserted_hyps = ref (HOLset.empty Term.compare)
    (* stores theorems of linear arithmetic (proved by 'rewrite' or 'th_lemma')
       for later retrieval, to avoid re-reproving them *)
    val arith_cache = ref Net.empty

    (*** auxiliary functions ***)
    (* e.g.   (A --> B) --> C --> D   ==>   [A, B, C, D] *)
    fun strip_fun_tys ty =
      let val (dom, rng) = Type.dom_rng ty
      in
        strip_fun_tys dom @ strip_fun_tys rng
      end
      handle Feedback.HOL_ERR _ => [ty]
    (* approximate: only descends into combination terms and function types *)
    fun term_contains_real_ty tm =
      let val (rator, rand) = Term.dest_comb tm
      in
        term_contains_real_ty rator orelse term_contains_real_ty rand
      end
      handle Feedback.HOL_ERR _ =>
        List.exists (fn ty => ty = realSyntax.real_ty)
          (strip_fun_tys (Term.type_of tm))
    (* A |- ... /\ t /\ ...
       --------------------
              A |- t        *)
    fun conj_elim (thm, t) =
      let fun elim conj =
            if t = conj then
              Lib.I
            else
              let val (l, r) = boolSyntax.dest_conj conj
              in
                elim l o Thm.CONJUNCT1
                  handle Feedback.HOL_ERR _ =>
                    elim r o Thm.CONJUNCT2
              end
      in
        elim (Thm.concl thm) thm
      end
    (*        A |- t
       --------------------
       A |- ... \/ t \/ ... *)
    fun disj_intro (thm, disj) =
      if Thm.concl thm = disj then
        thm
      else
        let val (l, r) = boolSyntax.dest_disj disj
        in
          Thm.DISJ1 (disj_intro (thm, l)) r
            handle Feedback.HOL_ERR _ =>
              Thm.DISJ2 l (disj_intro (thm, r))
        end
    (* |- ... \/ t \/ ... \/ ~t \/ ... *)
    fun gen_excluded_middle disj =
      let val (pos, neg) = Lib.tryfind (fn neg =>
            let val pos = boolSyntax.dest_neg neg
                fun check_is_disjunct lit disj =
                  disj = lit orelse
                    let val (l, r) = boolSyntax.dest_disj disj
                    in
                      check_is_disjunct lit l
                        handle Feedback.HOL_ERR _ =>
                          check_is_disjunct lit r
                    end
                val _ = check_is_disjunct pos disj
            in
              (pos, neg)
            end) (boolSyntax.strip_disj disj)
          val th1 = disj_intro (Thm.ASSUME pos, disj)
          val th2 = disj_intro (Thm.ASSUME neg, disj)
      in
        Thm.DISJ_CASES (Thm.SPEC pos EXCLUDED_MIDDLE) th1 th2
      end
    (* A |- ... /\ t /\ ... /\ ~t /\ ...
       ---------------------------------
                    A |- F               *)
    fun gen_contradiction thm =
      let val (pos, neg) = Lib.tryfind (fn neg =>
            let val pos = boolSyntax.dest_neg neg
                fun check_is_conjunct lit conj =
                  conj = lit orelse
                    let val (l, r) = boolSyntax.dest_conj conj
                    in
                      check_is_conjunct lit l
                        handle Feedback.HOL_ERR _ =>
                          check_is_conjunct lit r
                    end
                val _ = check_is_conjunct pos (Thm.concl thm)
            in
              (pos, neg)
            end) (boolSyntax.strip_conj (Thm.concl thm))
          val th1 = conj_elim (thm, pos)
          val th2 = conj_elim (thm, neg)
      in
        Thm.MP (Thm.MP (Thm.SPEC pos NOT_FALSE) th1) th2
      end
    (* returns "|- l = r", provided 'l' and 'r' are conjunctions that can be
       obtained from each other using associativity, commutativity and
       idempotence of conjunction, and identity of "T" wrt. conjunction.

       If 'r' is "F", 'l' must either contain "F" as a conjunct, or 'l'
       must contain both a literal and its negation.
    *)
    fun rewrite_conj (l, r) =
      let val Tl = boolSyntax.mk_conj (boolSyntax.T, l)
          val Tr = boolSyntax.mk_conj (boolSyntax.T, r)
          val Tl_eq_Tr = Drule.CONJUNCTS_AC (Tl, Tr)
      in
        Thm.MP (Drule.SPECL [l, r] T_AND) Tl_eq_Tr
      end
      handle Feedback.HOL_ERR _ =>
        if r = boolSyntax.F then
          let val l_imp_F = Thm.DISCH l (gen_contradiction (Thm.ASSUME l))
          in
            Drule.EQF_INTRO (Thm.NOT_INTRO l_imp_F)
          end
        else
          raise (Feedback.mk_HOL_ERR "Z3" "check_proof" "rewrite_conj")
    (* returns "|- l = r", provided 'l' and 'r' are disjunctions that can be
       obtained from each other using associativity, commutativity and
       idempotence of disjunction, and identity of "F" wrt. disjunction.

       If 'r' is "T", 'l' must contain "T" as a disjunct, or 'l' must contain
       both a literal and its negation.
    *)
    fun rewrite_disj (l, r) =
      let val Fl = boolSyntax.mk_disj (boolSyntax.F, l)
          val Fr = boolSyntax.mk_disj (boolSyntax.F, r)
          val Fl_eq_Fr = Drule.DISJUNCTS_AC (Fl, Fr)
      in
        Thm.MP (Drule.SPECL [l, r] F_OR) Fl_eq_Fr
      end
      handle Feedback.HOL_ERR _ =>
        if r = boolSyntax.T then
          Drule.EQT_INTRO (gen_excluded_middle l)
        else
          raise (Feedback.mk_HOL_ERR "Z3" "check_proof" "rewrite_disj")
    (* Returns "|- ALL_DISTINCT [x, y, z] = x <> y /\ x <> z /\ y <> z"; if
       'swap' is true, then each inequation "x <> y" is swapped to "y <> x" if
       y < x (according to Term.compare); if 'swap' is true, the resulting
       conjunction may contain parentheses; may raise Conv.UNCHANGED *)
    fun ALL_DISTINCT_CONV swap tm =
      let fun not_mem_conv tm =
            let val (x, list) = listSyntax.dest_mem (boolSyntax.dest_neg tm)
            in
              if listSyntax.is_nil list then
                (* |- ~MEM x [] = T *)
                Drule.ISPEC x NOT_MEM_NIL
              else
                let val (h, t) = listSyntax.dest_cons list
                    (* |- ~MEM x (h::t) = (x <> h) /\ ~MEM x t *)
                    val th1 = Drule.ISPECL [x, h, t] (if swap andalso
                      Term.compare (h, x) = LESS then
                        NOT_MEM_CONS_SWAP
                      else
                        NOT_MEM_CONS)
                    val (neq, notmem) = boolSyntax.dest_conj (boolSyntax.rhs
                      (Thm.concl th1))
                    (* |- ~MEM x t = rhs *)
                    val th2 = not_mem_conv notmem
                    (* |- ~MEM x (h::t) = (x <> h) /\ rhs *)
                    val th3 = Thm.TRANS th1 (Thm.AP_TERM (Term.mk_comb
                      (boolSyntax.conjunction, neq)) th2)
                in
                  if boolSyntax.rhs (Thm.concl th2) = boolSyntax.T then
                    Thm.TRANS th3 (Thm.SPEC neq AND_T)
                  else
                    th3
                end
            end
          fun all_distinct_conv tm =
            let val list = listSyntax.dest_all_distinct tm
            in
              if listSyntax.is_nil list then
                (* |- ALL_DISTINCT [] = T *)
                Thm.INST_TYPE [{redex = Type.alpha, residue =
                  listSyntax.dest_nil list}] ALL_DISTINCT_NIL
              else
                let val (h, t) = listSyntax.dest_cons list
                    (* |- ALL_DISTINCT (h::t) = ~MEM h t /\ ALL_DISTINCT t *)
                    val th1 = Drule.ISPECL [h, t] ALL_DISTINCT_CONS
                    val (notmem, alldistinct) = boolSyntax.dest_conj
                      (boolSyntax.rhs (Thm.concl th1))
                    (* |- ~MEM h t = something *)
                    val th2 = not_mem_conv notmem
                    (* |- ALL_DISTINCT t = rhs *)
                    val th3 = all_distinct_conv alldistinct
                    val th4 = Drule.SPECL [notmem, boolSyntax.rhs (Thm.concl
                      th2), alldistinct, boolSyntax.rhs (Thm.concl th3)]
                      CONJ_CONG
                    (* ~MEM h t /\ ALL_DISTINCT t = something /\ rhs *)
                    val th5 = Thm.MP (Thm.MP th4 th2) th3
                    val th6 = Thm.TRANS th1 th5
                in
                  if boolSyntax.rhs (Thm.concl th3) = boolSyntax.T then
                    Thm.TRANS th6 (Thm.SPEC (boolSyntax.rhs (Thm.concl th2))
                      AND_T)
                  else
                    th6
                end
            end
          val th1 = all_distinct_conv tm
      in
        if swap then
          th1
        else
          (* get rid of parentheses *)
          let val conj = boolSyntax.rhs (Thm.concl th1)
              val new = boolSyntax.list_mk_conj (boolSyntax.strip_conj conj)
              val th2 = Drule.CONJUNCTS_AC (conj, new)
          in
            Thm.TRANS th1 th2
          end
      end
      handle Feedback.HOL_ERR _ =>
        raise Conv.UNCHANGED
    (* replaces distinct if-then-else terms by distinct variables; returns the
       generalized term and a map from ite-subterms to variables; treats
       anything but combinations as atomic (i.e., does NOT descend into
       lambda-abstractions) *)
    fun generalize_ite t =
    let fun aux (dict, t) =
          if boolSyntax.is_cond t then
            (case Redblackmap.peek (dict, t) of
              SOME var =>
              (dict, var)
            | NONE =>
              let val var = Term.genvar (Term.type_of t)
              in
                (Redblackmap.insert (dict, t, var), var)
              end)
          else
            (let val (l, r) = Term.dest_comb t
                 val (dict, l) = aux (dict, l)
                 val (dict, r) = aux (dict, r)
             in
               (dict, Term.mk_comb (l, r))
             end
             handle Feedback.HOL_ERR _ =>
               (* 't' is not a combination *)
               (dict, t))
    in
      aux (Redblackmap.mkDict Term.compare, t)
    end

    (*** implementation of Z3's inference rules ***)
    fun and_elim (thm, t) =
      conj_elim (thm, t)
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("and_elim: " ^
          Hol_pp.thm_to_string thm ^ ", " ^ Hol_pp.term_to_string t))
    fun asserted t =
      let val _ = asserted_hyps := HOLset.add (!asserted_hyps, t)
      in
        Thm.ASSUME t
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("asserted: " ^
          Hol_pp.term_to_string t))
    fun commutativity t =
      let val (x, y) = boolSyntax.dest_eq (boolSyntax.lhs t)
      in
        Drule.ISPECL [x, y] boolTheory.EQ_SYM_EQ
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("commutativity: " ^
          Hol_pp.term_to_string t))
    (* Instances of Tseitin-style propositional tautologies:
       (or (not (and p q)) p)
       (or (not (and p q)) q)
       (or (and p q) (not p) (not q))
       (or (not (or p q)) p q)
       (or (or p q) (not p))
       (or (or p q) (not q))
       (or (not (iff p q)) (not p) q)
       (or (not (iff p q)) p (not q))
       (or (iff p q) (not p) (not q))
       (or (iff p q) p q)
       (or (not (ite a b c)) (not a) b)
       (or (not (ite a b c)) a c)
       (or (ite a b c) (not a) (not b))
       (or (ite a b c) a (not c))
       (or (not (not a)) (not a))
       (or (not a) a)

       Also
       (or p (= x (ite p y x)))

       Also
       ~ALL_DISTINCT [x; y; z] \/ (x <> y /\ x <> z /\ y <> z)

       There is a complication: 't' may contain arbitarily many irrelevant
       (nested) conjuncts/disjuncts, i.e., conjunction/disjunction in the above
       tautologies can be of arbitrary arity.

       For the most part, 'def_axiom' could be implemented by a single call to
       TAUT_PROVE. The (partly less general) implementation below, however, is
       considerably faster.
    *)
    fun def_axiom t =
      proforma def_axiom_thms t
      handle Feedback.HOL_ERR _ =>
      (* or (or ... p ...) (not p) *)
      (* or (or ... (not p) ...) p *)
      gen_excluded_middle t
      handle Feedback.HOL_ERR _ =>
      (* (or (not (and ... p ...)) p) *)
      let val (lhs, rhs) = boolSyntax.dest_disj t
          val conj = boolSyntax.dest_neg lhs
          (* conj |- rhs *)
          val thm = conj_elim (Thm.ASSUME conj, rhs)  (* may fail *)
      in
        (* |- lhs \/ rhs *)
        Drule.IMP_ELIM (Thm.DISCH conj thm)
      end
      handle Feedback.HOL_ERR _ =>
      (* ~ALL_DISTINCT [x; y; z] \/ x <> y /\ x <> z /\ y <> z *)
      let val (not_all_distinct, _) = boolSyntax.dest_disj t
          val all_distinct = boolSyntax.dest_neg not_all_distinct
          val all_distinct_th = ALL_DISTINCT_CONV false all_distinct
            handle Conv.UNCHANGED =>
              raise (Feedback.mk_HOL_ERR "" "" "")
      in
        Drule.IMP_ELIM (Lib.fst (Thm.EQ_IMP_RULE all_distinct_th))
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("def_axiom: " ^
          Hol_pp.term_to_string t))
    fun elim_unused t =  (* (!x y z. P) = P *)
      let val (lhs, rhs) = boolSyntax.dest_eq t
          fun strip_some_foralls forall =
          let
              val (var, body) = boolSyntax.dest_forall forall
              val th1 = Thm.DISCH forall (Thm.SPEC var (Thm.ASSUME forall))
              val th2 = Thm.DISCH body (Thm.GEN var (Thm.ASSUME body))
              val strip_th = Drule.IMP_ANTISYM_RULE th1 th2
          in
            if body = rhs then
              strip_th  (* stripped enough quantifiers *)
            else
              Thm.TRANS strip_th (strip_some_foralls body)
          end
      in
        strip_some_foralls lhs
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("elim_unused: " ^
          Hol_pp.term_to_string t))
    fun hypothesis t =
      Thm.ASSUME t
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("hypothesis: " ^
          Hol_pp.term_to_string t))
    fun iff_false (thm, t) =
      Drule.EQF_INTRO thm
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("iff_false: " ^
          Hol_pp.thm_to_string thm ^ ", " ^ Hol_pp.term_to_string t))
    fun iff_true (thm, t) =
      Drule.EQT_INTRO thm
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("iff_true: " ^
          Hol_pp.thm_to_string thm ^ ", " ^ Hol_pp.term_to_string t))
    (*  [l1, ..., ln] |- F
       --------------------
       |- ~l1 \/ ... \/ ~ln

       'lemma' could be implemented by a single call to 'TAUT_PROVE'. The (less
       general) implementation below, however, is considerably faster.
    *)
    fun lemma (thm, t) =
    let fun prove_literal maybe_no_hyp (th, lit) =
          let val (is_neg, neg_lit) = (true, boolSyntax.dest_neg lit)
                handle Feedback.HOL_ERR _ => (false, boolSyntax.mk_neg lit)
          in
            if maybe_no_hyp orelse HOLset.member (Thm.hypset th, neg_lit) then
              let val concl = Thm.concl th
                  val th1 = Thm.DISCH neg_lit th
              in
                if is_neg then (
                  if concl = boolSyntax.F then
                    (* [...] |- ~neg_lit *)
                    Thm.NOT_INTRO th1
                  else
                    (* [...] |- ~neg_lit \/ concl *)
                    Thm.MP (Drule.SPECL [neg_lit, concl] IMP_DISJ_1) th1
                ) else
                  if concl = boolSyntax.F then
                    (* [...] |- lit *)
                    Thm.MP (Thm.SPEC lit IMP_FALSE) th1
                  else
                    (* [...] |- lit \/ concl *)
                    Thm.MP (Drule.SPECL [lit, concl] IMP_DISJ_2) th1
              end
            else
              raise (Feedback.mk_HOL_ERR "" "" "")
          end
        fun prove (th, disj) =
          prove_literal false (th, disj)
            handle Feedback.HOL_ERR _ =>
              let val (l, r) = boolSyntax.dest_disj disj
              in
                (* We do NOT break 'l' apart recursively (because that would be
                   slightly tricky to implement, and require associativity of
                   disjunction).  Thus, 't' must be parenthesized to the right
                   (e.g., "l1 \/ (l2 \/ l3)"). *)
                prove_literal true (prove (th, r), l)
              end
    in
      prove (thm, t)
    end
    handle Feedback.HOL_ERR _ =>
      raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("lemma: " ^
        Hol_pp.thm_to_string thm ^ ", " ^ Hol_pp.term_to_string t))
    fun monotonicity (thms, t) =
      let val l_r_thms = List.map (fn thm =>
            (boolSyntax.dest_eq (Thm.concl thm), thm)) thms
          fun make_equal (l, r) =
            Thm.ALPHA l r
            handle Feedback.HOL_ERR _ =>
            Lib.tryfind (fn ((l', r'), thm) =>
              Thm.TRANS (Thm.ALPHA l l') (Thm.TRANS thm (Thm.ALPHA r' r))
              handle Feedback.HOL_ERR _ =>
              Thm.TRANS (Thm.ALPHA l r') (Thm.TRANS (Thm.SYM thm)
                (Thm.ALPHA l' r))) l_r_thms
            handle Feedback.HOL_ERR _ =>
            let val (l_op, l_arg) = Term.dest_comb l
                val (r_op, r_arg) = Term.dest_comb r
            in
              Thm.MK_COMB (make_equal (l_op, r_op), make_equal (l_arg, r_arg))
            end
      in
        make_equal (boolSyntax.dest_eq t)
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("monotonicity: " ^
          String.concat (Lib.separate ", " (List.map Hol_pp.thm_to_string thms))
          ^ ", " ^ Hol_pp.term_to_string t))
    fun mp (thm1, thm2, t) =
      Thm.MP thm2 thm1
      handle Feedback.HOL_ERR _ =>
        Thm.EQ_MP thm2 thm1
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("mp: " ^
          Hol_pp.thm_to_string thm1 ^ ", " ^ Hol_pp.thm_to_string thm2 ^ ", "
          ^ Hol_pp.term_to_string t))
    fun mp_tilde (thm1, thm2, t) =
      Thm.EQ_MP thm2 thm1
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("mp~: " ^
          Hol_pp.thm_to_string thm1 ^ ", " ^ Hol_pp.thm_to_string thm2 ^ ", " ^
          Hol_pp.term_to_string t))
    (*      |- ~s1 = r1  ...  |- ~sn = rn
       ---------------------------------------
       |- ~(s1 /\ ... /\ sn) = r1 \/ ... \/ rn

            |- ~s1 = r1  ...  |- ~sn = rn
       ---------------------------------------
       |- ~(s1 \/ ... \/ sn) = r1 /\ ... /\ rn

       |- ~s1 = r1  |- ~s2 = r2  |- s1 = r1'  |- s2 = r2'
       --------------------------------------------------
           |- ~(s1 = s2) = (r1 \/ r2) /\ (r1' \/ r2')

        |- s = r
       ----------
       |- ~~s = r

       'nnf_neg' could be implemented by a single call to 'TAUT_PROVE', but the
       (less general) implementation below is considerably faster.
    *)
    fun nnf_neg (thms, t) =
      let fun nnf_aux is_conj (thms, t) =
            let val _ = if List.null thms then
                    raise (Feedback.mk_HOL_ERR "" "" "")
                  else ()
                val th = List.hd thms
                val (neg_p, r) = boolSyntax.dest_eq (Thm.concl th)
            in
              if boolSyntax.dest_neg neg_p = t then
                (* |- ~t = r *)
                th
              else
                let val (p, q) = (if is_conj then boolSyntax.dest_conj else
                      boolSyntax.dest_disj) t
                    (* |- ~q = s *)
                    val q_th = nnf_aux is_conj (List.tl thms, q)
                    val s = boolSyntax.rhs (Thm.concl q_th)
                    val nnf_th = if is_conj then NNF_CONJ else NNF_DISJ
                in
                    (* |- ~t = r op s, where op is /\ or \/ *)
                    Thm.MP (Thm.MP (Drule.SPECL [p, q, r, s] nnf_th) th) q_th
                end
            end
          val neg_l = boolSyntax.dest_neg (boolSyntax.lhs t)
      in
        Thm.MP (Drule.SPECL [boolSyntax.dest_neg neg_l, boolSyntax.rhs t]
          NNF_NOT_NOT) (List.hd thms)
        handle Feedback.HOL_ERR _ =>
          nnf_aux (boolSyntax.is_conj neg_l) (thms, neg_l)
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("nnf_neg: " ^
          String.concat (Lib.separate ", " (List.map Hol_pp.thm_to_string thms))
          ^ ", " ^ Hol_pp.term_to_string t))
    fun nnf_pos (thms, t) =
      let val concl = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
          val th = tautLib.TAUT_PROVE concl
      in
        Drule.LIST_MP thms th
      end
      handle Feedback.HOL_ERR _ =>
        (if List.length thms = 1 then
           quant_intro (List.hd thms, t)
         else
           raise (Feedback.mk_HOL_ERR "" "" ""))
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("nnf_pos: " ^
          String.concat (Lib.separate ", " (List.map Hol_pp.thm_to_string thms))
          ^ ", " ^ Hol_pp.term_to_string t))
    (* ~(... \/ p \/ ...)
       ------------------
               ~p         *)
    and not_or_elim (thm, t) =
      let val (is_neg, neg_t) = (true, boolSyntax.dest_neg t)
            handle Feedback.HOL_ERR _ =>
              (false, boolSyntax.mk_neg t)
          val disj = boolSyntax.dest_neg (Thm.concl thm)
          (* neg_t |- disj *)
          val th1 = disj_intro (Thm.ASSUME neg_t, disj)
          (* |- ~disj ==> ~neg_t *)
          val th1 = Drule.CONTRAPOS (Thm.DISCH neg_t th1)
          (* |- ~neg_t *)
          val th1 = Thm.MP th1 thm
      in
        if is_neg then
          th1
        else
          Thm.MP (Thm.SPEC t NOT_NOT_ELIM) th1
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("not_or_elim: " ^
          Hol_pp.thm_to_string thm ^ ", " ^ Hol_pp.term_to_string t))
    (* (iff (f (forall (x) q(x)) r) (forall (x) (f (q x) r))) *)
    and pull_quant t =
      Thm.REFL (boolSyntax.lhs t) (* TODO *)
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("pull_quant: " ^
          Hol_pp.term_to_string t))
    and quant_inst t =  (* ~(!x. P x) \/ P a *)
      let val (lhs, rhs) = boolSyntax.dest_disj t
          val Px = boolSyntax.dest_neg lhs
          val (bvars, _) = boolSyntax.strip_forall Px
          (* "P a" may be a quantified proposition itself; only retain *new*
             quantifiers *)
          val bvars = List.take (bvars, List.length bvars -
            List.length (Lib.fst (boolSyntax.strip_forall rhs)))
          fun strip_some_foralls 0 term =
            term
            | strip_some_foralls n term =
            strip_some_foralls (n - 1) (Lib.snd (boolSyntax.dest_forall term))
          val len = List.length bvars
          val (tmsubst, _) = Term.match_term (strip_some_foralls len Px) rhs
          val bvars' = List.map (Term.subst tmsubst) bvars
      in
        Drule.IMP_ELIM (Thm.DISCH Px (Drule.SPECL bvars' (Thm.ASSUME Px)))
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("quant_inst: " ^
          Hol_pp.term_to_string t))
    and quant_intro (thm, t) =  (* from P = Q derive (!x. P x) = (!y. Q y) *)
      let val (lhs, rhs) = boolSyntax.dest_eq t
          val (bvars, _) = boolSyntax.strip_forall lhs
          (* P may be a quantified proposition itself; only retain *new*
             quantifiers *)
          val (P, _) = boolSyntax.dest_eq (Thm.concl thm)
          val bvars = List.take (bvars, List.length bvars -
            List.length (Lib.fst (boolSyntax.strip_forall P)))
          (* P and Q in the conclusion may require variable renaming to match
             the premise -- we only look at P and hope Q will come out right *)
          fun strip_some_foralls 0 term =
            term
            | strip_some_foralls n term =
            strip_some_foralls (n - 1) (Lib.snd (boolSyntax.dest_forall term))
          val len = List.length bvars
          val (tmsubst, _) = Term.match_term P (strip_some_foralls len lhs)
          val thm = Thm.INST tmsubst thm
          (* add quantifiers (on both sides) *)
          val thm = List.foldr (fn (bvar, th) => Drule.FORALL_EQ bvar th)
            thm bvars
          (* rename bvars on rhs if necessary *)
          val (_, intermediate_rhs) = boolSyntax.dest_eq (Thm.concl thm)
          val thm = Thm.TRANS thm (Thm.ALPHA intermediate_rhs rhs)
      in
        thm
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("quant_intro: " ^
          Hol_pp.thm_to_string thm ^ ", " ^ Hol_pp.term_to_string t))
    fun refl t =
      Thm.REFL (boolSyntax.lhs t)
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("refl: " ^
          Hol_pp.term_to_string t))
    fun rewrite t =
      let val (l, r) = boolSyntax.dest_eq t
      in
        if l = r then
          Thm.REFL l
        else

        (* proforma theorems *)
          (*Profile.profile "rewrite(proforma)"*) (fn () =>
            proforma rewrite_thms t) ()
        handle Feedback.HOL_ERR _ =>

        (* re-ordering conjunctions and disjunctions *)
          (if boolSyntax.is_conj l then
            (*Profile.profile "rewrite(conj)"*) rewrite_conj (l, r)
          else if boolSyntax.is_disj l then
            (*Profile.profile "rewrite(disj)"*) rewrite_disj (l, r)
          else
            raise (Feedback.mk_HOL_ERR "" "" ""))
        handle Feedback.HOL_ERR _ =>

        (* |- r1 /\ ... /\ rn = ~(s1 \/ ... \/ sn) *)
        (* Note that p <=> q may be negated to q <=> ~p. *)
          (*Profile.profile "rewrite(nnf)"*) (fn () =>
            let val disj = boolSyntax.dest_neg r
                val disj_th = Thm.ASSUME disj
                val conj_ths = Drule.CONJUNCTS (Thm.ASSUME l)
                (* (p <=> q) ==> ~(q <=> ~p) *)
                val neg_iffs = List.mapPartial (Lib.total (fn th =>
                  let val (p, q, ty) = boolSyntax.dest_eq_ty (Thm.concl th)
                      val _ = (ty = Type.bool) orelse
                        raise (Feedback.mk_HOL_ERR "" "" "")
                  in
                    Thm.MP (Drule.SPECL [p, q] NEG_IFF_1) th
                  end)) conj_ths
                val False = unit_resolution (disj_th :: conj_ths @ neg_iffs,
                  boolSyntax.F)

                fun disjuncts dict (thmfun, concl) =
                  let val (l, r) = boolSyntax.dest_disj concl
                  in
                    disjuncts (disjuncts dict (fn th => thmfun (Thm.DISJ1 th r),
                      l)) (fn th => thmfun (Thm.DISJ2 l th), r)
                  end
                  handle Feedback.HOL_ERR _ =>
                    let (* |- concl ==> disjunction *)
                        val th = Thm.DISCH concl (thmfun (Thm.ASSUME concl))
                        (* ~disjunction |- ~concl *)
                        val th = Drule.UNDISCH (Drule.CONTRAPOS th)
                        val th = let val neg_concl = boolSyntax.dest_neg concl
                          in
                            Thm.MP (Thm.SPEC neg_concl NOT_NOT_ELIM) th
                          end
                          handle Feedback.HOL_ERR _ =>
                            th
                        val dict = Redblackmap.insert (dict, Thm.concl th, th)
                        (* ~(p <=> ~q) ==> (q <=> p) *)
                        val dict = let val (p, neg_q) = boolSyntax.dest_eq
                          (boolSyntax.dest_neg (Thm.concl th))
                                       val q = boolSyntax.dest_neg neg_q
                                       val th = Thm.MP (Drule.SPECL [p, q]
                                         NEG_IFF_2) th
                                   in
                                     Redblackmap.insert (dict, Thm.concl th, th)
                                   end
                                   handle Feedback.HOL_ERR _ =>
                                     dict
                    in
                      dict
                    end
                fun prove dict conj =
                  Redblackmap.find (dict, conj)
                    handle Redblackmap.NotFound =>
                      let val (l, r) = boolSyntax.dest_conj conj
                      in
                        Thm.CONJ (prove dict l) (prove dict r)
                      end
                val empty = Redblackmap.mkDict Term.compare
                val dict = disjuncts empty (Lib.I, disj)
                val r_imp_l = Thm.DISCH r (prove dict l)
                val l_imp_r = Thm.DISCH l (Thm.NOT_INTRO (Thm.DISCH disj False))
            in
              Drule.IMP_ANTISYM_RULE l_imp_r r_imp_l
            end) ()
        handle Feedback.HOL_ERR _ =>

        (* ALL_DISTINCT [x, y, z] = ... *)
          (*Profile.profile "rewrite(all_distinct)"*) (fn () =>
            let val l_eq_l' = ALL_DISTINCT_CONV true l
                  handle Conv.UNCHANGED =>
                    raise (Feedback.mk_HOL_ERR "" "" "")
                val r_eq_r' = ALL_DISTINCT_CONV true r
                  handle Conv.UNCHANGED =>
                    Thm.REFL r
                val l' = boolSyntax.rhs (Thm.concl l_eq_l')
                val r' = boolSyntax.rhs (Thm.concl r_eq_r')
                val l'_eq_r' = Drule.CONJUNCTS_AC (l', r')
            in
              Thm.TRANS (Thm.TRANS l_eq_l' l'_eq_r') (Thm.SYM r_eq_r')
            end) ()
        handle Feedback.HOL_ERR _ =>

          (*Profile.profile "rewrite(TAUT_PROVE)"*) tautLib.TAUT_PROVE t
        handle Feedback.HOL_ERR _ =>

          (*Profile.profile "rewrite(update)"*) (fn () =>
            simpLib.SIMP_PROVE intSimps.int_ss [combinTheory.UPDATE_def,
              boolTheory.EQ_SYM_EQ] t) ()
        handle Feedback.HOL_ERR _ =>

          (*Profile.profile "rewrite(cache)"*) (fn () =>
            proforma (!arith_cache) t) ()
        handle Feedback.HOL_ERR _ =>

          let val th = if term_contains_real_ty t then
                (*Profile.profile "rewrite(REAL_ARITH)"*) realLib.REAL_ARITH t
              else
                (*Profile.profile "rewrite(ARITH_PROVE)"*) intLib.ARITH_PROVE t
          in
            arith_cache := Net.insert (t, th) (!arith_cache);
            th
          end
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("rewrite: " ^
          Hol_pp.term_to_string t))
    and rewrite_star (thms, t) =
      raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("rewrite*: " ^
        String.concat (Lib.separate ", " (List.map Hol_pp.thm_to_string thms))
        ^ ", " ^ Hol_pp.term_to_string t))
    and sk t = (* (~ (not (forall x (p x y))) (not (p (sk y) y)))
                  (~ (exists x (p x y)) (p (sk y) y)) *)
      let fun NOT_FORALL_CONV tm =  (* |- ~(!x y z. P) = (?x y z. ~P) *)
            let val thm = Conv.NOT_FORALL_CONV tm
                (* transform the rhs recursively *)
                val rhs = boolSyntax.rhs (Thm.concl thm)
                val (var, body) = boolSyntax.dest_exists rhs
            in
              Thm.TRANS thm (Drule.EXISTS_EQ var (NOT_FORALL_CONV body))
                handle Feedback.HOL_ERR _ => thm
            end
          val (not_forall, skolemized) = boolSyntax.dest_eq t
          (* we assume that p is not universally quantified, so that we may
             turn *all* universal quantifiers into existential ones *)
          val not_forall_eq_exists_th = NOT_FORALL_CONV not_forall
          val exists = boolSyntax.rhs (Thm.concl not_forall_eq_exists_th)
          val (vars, body) = boolSyntax.strip_exists exists
          (* 'tmsubst' maps (existentially quantified) variables to Skolem
             functions applied to some arguments. *)
          val (tmsubst, _) = Term.match_term body skolemized
          (* replaces existentially quantified variables by Skolem functions,
             assuming suitable definitions in terms of HOL's SELECT operator *)
          (* [...] |- P[skx/x, sky/y, skz/z] = (?x y z. P) *)
          fun SKOLEM_CONV tm =
            let val (var, body) = boolSyntax.dest_exists tm
                val select = boolSyntax.mk_select (var, body)
                val thm = Conv.SELECT_CONV (Term.subst [{redex = var,
                  residue = select}] body)

                val (sk, args) = boolSyntax.strip_comb (Term.subst tmsubst var)
                val sk_def =
                  boolSyntax.mk_eq (sk, boolSyntax.list_mk_abs (args, select))
                (* store definition in global ref *)
                val _ = skolem_defs := sk_def :: !skolem_defs

                val def_th = Thm.ASSUME sk_def
                val rewrite_th = List.foldl (fn (arg, th) =>
                  let val ap_th = Thm.AP_THM th arg
                      val beta_th = Thm.BETA_CONV (boolSyntax.rhs
                        (Thm.concl ap_th))
                  in
                    Thm.TRANS ap_th beta_th
                  end) def_th args (* [.] |- sk x y z = select *)
                val thm = Thm.SUBST
                  [{redex = var, residue = Thm.SYM rewrite_th}]
                  (boolSyntax.mk_eq (body, tm)) thm
            in
              (* transform the lhs recursively *)
              Thm.TRANS (SKOLEM_CONV (boolSyntax.lhs (Thm.concl thm))) thm
                handle Feedback.HOL_ERR _ => thm
            end
          val skolemized_eq_exists_th = SKOLEM_CONV exists
      in
        Thm.TRANS not_forall_eq_exists_th (Thm.SYM skolemized_eq_exists_th)
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("sk: " ^
          Hol_pp.term_to_string t))
    and symm (thm, t) =
      Thm.SYM thm
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("symm: " ^
          Hol_pp.thm_to_string thm ^ ", " ^ Hol_pp.term_to_string t))
    and th_lemma (thms, t) =
      (* proforma theorems *)
      (*Profile.profile "th_lemma(proforma)"*)
        (fn () => proforma th_lemma_thms t) ()
      handle Feedback.HOL_ERR _ =>
      let val concl = boolSyntax.list_mk_imp (List.map Thm.concl thms, t)
      in
        (* cache *)
        Drule.LIST_MP thms (proforma (!arith_cache) concl)
        handle Feedback.HOL_ERR _ =>

        let val (dict, concl) = generalize_ite concl
            val th = if term_contains_real_ty concl then
                (*Profile.profile "th_lemma(REAL_ARITH)"*)
                  realLib.REAL_ARITH concl
              else
                (*Profile.profile "th_lemma(ARITH_PROVE)"*)
                  intLib.ARITH_PROVE concl
            val _ = arith_cache := Net.insert (concl, th) (!arith_cache)
            val subst = List.map (fn (term, var) =>
              {redex = var, residue = term}) (Redblackmap.listItems dict)
        in
          Drule.LIST_MP thms (Thm.INST subst th)
        end
      end
      handle Feedback.HOL_ERR _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("th_lemma: " ^
          String.concat (Lib.separate ", " (List.map Hol_pp.thm_to_string thms))
          ^ ", " ^ Hol_pp.term_to_string t))
    and trans (thm1, thm2, t) =
      Thm.TRANS thm1 thm2
      handle Feedback.HOL_ERR _ =>
      if Thm.concl thm2 = t then
        thm2  (* oddly enough, thm1 is sometimes not needed -- this is arguably
                 a bug in Z3 *)
      else
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("trans: " ^
          Hol_pp.thm_to_string thm1 ^ ", " ^ Hol_pp.thm_to_string thm2 ^ ", " ^
          Hol_pp.term_to_string t))
    and true_axiom t =
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("true_axiom: " ^
          Hol_pp.term_to_string t))
    (* l1 \/ l2 \/ ... \/ ln \/ t   ~l1   ~l2   ...   ~ln
       --------------------------------------------------
                                t

       The input clause (including "t") is really treated as a set of literals:
       the resolvents need not be in the correct order, "t" need not be the
       rightmost disjunct (and if "t" is a disjunction, its disjuncts may even
       be spread throughout the input clause).  Note also that "t" may be F, in
       which case it need not be present in the input clause.

       We treat all "~li" as atomic, even if they are negated disjunctions.
    *)
    and unit_resolution (thms, t) =
    let val _ = if List.null thms then
            raise (Feedback.mk_HOL_ERR "" "" "")
          else ()
(* QF_UF: 689.157 s
        (* cf. DISJUNCTS_AC *)
        fun disjuncts dict (thmfun, concl) =
          let val (l, r) = boolSyntax.dest_disj concl
          in
            disjuncts (disjuncts dict (fn th => thmfun (Thm.DISJ1 th r), l))
              (fn th => thmfun (Thm.DISJ2 l th), r)
          end
          handle Feedback.HOL_ERR _ =>
            Redblackmap.insert (dict, concl, thmfun (Thm.ASSUME concl))
        fun prove dict disj =
          Redblackmap.find (dict, disj)
            handle Redblackmap.NotFound =>
              let val (l, r) = boolSyntax.dest_disj disj
                  val l_th = prove dict l
                  val r_th = prove dict r
              in
                Thm.DISJ_CASES (Thm.ASSUME disj) l_th r_th
              end
        val empty = Redblackmap.mkDict Term.compare
        val dict = disjuncts empty (Lib.I, t)
        (* derive 't' from each negated resolvent *)
        val dict = List.foldl (fn (th, dict) =>
          let val lit = Thm.concl th
              val (is_neg, neg_lit) = (true, boolSyntax.dest_neg lit)
                handle Feedback.HOL_ERR _ =>
                  (false, boolSyntax.mk_neg lit)
              (* |- neg_lit ==> F *)
              val th = if is_neg then
                  Thm.NOT_ELIM th
                else
                  Thm.MP (Thm.SPEC lit NOT_FALSE) th
              (* neg_lit |- t *)
              val th = Thm.CCONTR t (Drule.UNDISCH th)
          in
            Redblackmap.insert (dict, neg_lit, th)
          end) dict (List.tl thms)
        val clause = Thm.concl (List.hd thms)
        val clause_imp_t = prove dict clause
    in
      Thm.MP (Thm.DISCH clause clause_imp_t) (List.hd thms)
    end
*)
(* QF_UF: 1402.885 s
          fun disjuncts dict thm =
            let val (disj, concl) = boolSyntax.dest_imp_only (Thm.concl thm)
            in
              let val (l, r) = boolSyntax.dest_disj disj
                  val l_imp_concl = Thm.MP (Drule.SPECL [l, r, concl] DISJ_ELIM_1) thm
                  val r_imp_concl = Thm.MP (Drule.SPECL [l, r, concl] DISJ_ELIM_2) thm
              in
                disjuncts (disjuncts dict l_imp_concl) r_imp_concl
              end
              handle Feedback.HOL_ERR _ =>
                Redblackmap.insert (dict, disj, Thm.MP thm (Thm.ASSUME disj))
            end
          fun prove_from_disj dict disj =
            Redblackmap.find (dict, disj)
            handle Redblackmap.NotFound =>
              let val (l, r) = boolSyntax.dest_disj disj
                  val l_th = prove_from_disj dict l
                  val r_th = prove_from_disj dict r
              in
                Thm.DISJ_CASES (Thm.ASSUME disj) l_th r_th
              end
          val empty = Redblackmap.mkDict Term.compare
          val dict = disjuncts empty (Thm.DISCH t (Thm.ASSUME t))
        (* derive 't' from each negated resolvent *)
        val dict = List.foldl (fn (th, dict) =>
          let val lit = Thm.concl th
              val (is_neg, neg_lit) = (true, boolSyntax.dest_neg lit)
                handle Feedback.HOL_ERR _ =>
                  (false, boolSyntax.mk_neg lit)
              (* |- neg_lit ==> F *)
              val th = if is_neg then
                  Thm.NOT_ELIM th
                else
                  Thm.MP (Thm.SPEC lit NOT_FALSE) th
              (* neg_lit |- t *)
              val th = Thm.CCONTR t (Drule.UNDISCH th)
          in
            Redblackmap.insert (dict, neg_lit, th)
          end) dict (List.tl thms)
        val clause = Thm.concl (List.hd thms)
        val clause_imp_t = prove_from_disj dict clause
    in
      Thm.MP (Thm.DISCH clause clause_imp_t) (List.hd thms)
    end
*)
(* QF_UF: 663.996 s *)
          fun disjuncts dict (disj, thm) =
            let val (l, r) = boolSyntax.dest_disj disj
                (* |- l \/ r ==> ... *)
                val thm = Thm.DISCH disj thm
                val l_th = Thm.DISJ1 (Thm.ASSUME l) r
                val r_th = Thm.DISJ2 l (Thm.ASSUME r)
                val l_imp_concl = Thm.MP thm l_th
                val r_imp_concl = Thm.MP thm r_th
            in
              disjuncts (disjuncts dict (l, l_imp_concl)) (r, r_imp_concl)
            end
            handle Feedback.HOL_ERR _ =>
              Redblackmap.insert (dict, disj, thm)
          fun prove_from_disj dict disj =
            Redblackmap.find (dict, disj)
            handle Redblackmap.NotFound =>
              let val (l, r) = boolSyntax.dest_disj disj
                  val l_th = prove_from_disj dict l
                  val r_th = prove_from_disj dict r
              in
                Thm.DISJ_CASES (Thm.ASSUME disj) l_th r_th
              end
          val empty = Redblackmap.mkDict Term.compare
          val dict = disjuncts empty (t, Thm.ASSUME t)
        (* derive 't' from each negated resolvent *)
        val dict = List.foldl (fn (th, dict) =>
          let val lit = Thm.concl th
              val (is_neg, neg_lit) = (true, boolSyntax.dest_neg lit)
                handle Feedback.HOL_ERR _ =>
                  (false, boolSyntax.mk_neg lit)
              (* |- neg_lit ==> F *)
              val th = if is_neg then
                  Thm.NOT_ELIM th
                else
                  Thm.MP (Thm.SPEC lit NOT_FALSE) th
              (* neg_lit |- t *)
              val th = Thm.CCONTR t (Thm.MP th (Thm.ASSUME neg_lit))
          in
            Redblackmap.insert (dict, neg_lit, th)
          end) dict (List.tl thms)
        val clause = Thm.concl (List.hd thms)
        val clause_imp_t = prove_from_disj dict clause
    in
      Thm.MP (Thm.DISCH clause clause_imp_t) (List.hd thms)
    end
(* QF_UF: 934.531 s
        val dict = List.foldl (fn (th, dict) =>
          Redblackmap.insert (dict, Thm.concl th, th))
            (Redblackmap.mkDict Term.compare) (List.tl thms)
        fun move_lits_into_hyps th =
          let val concl = Thm.concl th
          in
            if concl = boolSyntax.F then
              th
            else
              (let val (is_neg, neg_concl) = (true, boolSyntax.dest_neg concl)
                    handle Feedback.HOL_ERR _ =>
                      (false, boolSyntax.mk_neg concl)
                  val th1 = Redblackmap.find (dict, neg_concl)
                  (* |- neg_concl ==> F *)
                  val th2 = (if is_neg then Thm.NOT_ELIM th else
                    Thm.MP (Thm.SPEC concl NOT_FALSE) th)
                  val th2 = Thm.MP th2 th1
              in
                th2
              end
              handle Redblackmap.NotFound =>

              let val (l, r) = boolSyntax.dest_disj concl
                  val (is_neg, neg_l) = (true, boolSyntax.dest_neg l)
                    handle Feedback.HOL_ERR _ =>
                      (false, boolSyntax.mk_neg l)
                  val th1 = if is_neg then Drule.SPECL [neg_l, r] DISJ_IMP_2
                    else Drule.SPECL [l, r] DISJ_IMP_1
                  (* |- neg_l ==> r *)
                  val th1 = Thm.MP th1 th
                  val th1 = Thm.MP th1 (Redblackmap.find (dict, neg_l)
                    handle Redblackmap.NotFound => Thm.ASSUME neg_l)
              in
                move_lits_into_hyps th1
              end
              handle Feedback.HOL_ERR _ =>

              let val (is_neg, neg_concl) = (true, boolSyntax.dest_neg concl)
                    handle Feedback.HOL_ERR _ =>
                      (false, boolSyntax.mk_neg concl)
                  (* |- neg_concl ==> F *)
                  val th1 = (if is_neg then Thm.NOT_ELIM th else
                    Thm.MP (Thm.SPEC concl NOT_FALSE) th)
                  val th1 = Thm.MP th1 (Thm.ASSUME neg_concl)
              in
                th1
              end)
          end
        val false_th = move_lits_into_hyps (List.hd thms)
        val th = if t = boolSyntax.F then false_th else lemma (false_th, t)
(*
        val union = List.foldl HOLset.union (HOLset.empty Term.compare)
          (List.map Thm.hypset thms)
        val _ = HOLset.isSubset (Thm.hypset th, union) orelse
          raise (Feedback.mk_HOL_ERR "" "" "")
*)
    in
      th
    end
*)
    handle Feedback.HOL_ERR _ =>
      raise (Feedback.mk_HOL_ERR "Z3" "check_proof" ("unit_resolution: " ^
        String.concat (Lib.separate ", " (List.map Hol_pp.thm_to_string thms)) ^
        ", " ^ Hol_pp.term_to_string t))
    (*** end of inference rule implementations ***)

    fun verify_theorem rule id t thm =
      Profile.profile "verify_theorem" (fn () =>
        (if !SolverSpec.trace > 0 andalso Thm.concl thm <> t then
          Feedback.HOL_WARNING "Z3" "check_proof" ("#" ^ Int.toString id ^ " ("
            ^ rule ^ "): conclusion is " ^ Hol_pp.term_to_string (Thm.concl thm)
            ^ ", expected: " ^ Hol_pp.term_to_string t)
        else ();
        if !SolverSpec.trace > 2 then
          Feedback.HOL_MESG ("HolSmtLib: proved #" ^ Int.toString id ^ " (" ^
            rule ^ "): " ^ Hol_pp.thm_to_string thm)
        else ())) ()
    fun check_proof_id (prf, id) =
      case Redblackmap.peek (prf, id) of
        SOME (AND_ELIM (id1, t)) =>
        let val (prf, thm) = check_proof_id (prf, id1)
            val thm = Profile.profile "and_elim" and_elim (thm, t)
            val _ = verify_theorem "and_elim" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (ASSERTED t) =>
        let val thm = Profile.profile "asserted" asserted t
            val _ = verify_theorem "asserted" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (COMMUTATIVITY t) =>
        let val thm = Profile.profile "commutativity" commutativity t
            val _ = verify_theorem "commutativity" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (DEF_AXIOM t) =>
        let val thm = Profile.profile "def_axiom" def_axiom t
            val _ = verify_theorem "def-axiom" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (ELIM_UNUSED t) =>
        let val thm = Profile.profile "elim_unused" elim_unused t
            val _ = verify_theorem "elim-unused" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (IFF_FALSE (id1, t)) =>
        let val (prf, thm) = check_proof_id (prf, id1)
            val thm = Profile.profile "iff_false" iff_false (thm, t)
            val _ = verify_theorem "iff-false" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (IFF_TRUE (id1, t)) =>
        let val (prf, thm) = check_proof_id (prf, id1)
            val thm = Profile.profile "iff_true" iff_true (thm, t)
            val _ = verify_theorem "iff-true" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (LEMMA (id1, t)) =>
        let val (prf, thm) = check_proof_id (prf, id1)
            val thm = Profile.profile "lemma" lemma (thm, t)
            val _ = verify_theorem "lemma" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (HYPOTHESIS t) =>
        let val thm = Profile.profile "hypothesis" hypothesis t
            val _ = verify_theorem "hypothesis" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (MONOTONICITY (ids, t)) =>
        let val (prf, thms) = Lib.foldl_map check_proof_id (prf, ids)
            val thm = Profile.profile "monotonicity" monotonicity (thms, t)
            val _ = verify_theorem "monotonicity" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (MP (id1, id2, t)) =>
        let val (prf, thm1) = check_proof_id (prf, id1)
            val (prf, thm2) = check_proof_id (prf, id2)
            val thm = Profile.profile "mp" mp (thm1, thm2, t)
            val _ = verify_theorem "mp" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (MP_TILDE (id1, id2, t)) =>
        let val (prf, thm1) = check_proof_id (prf, id1)
            val (prf, thm2) = check_proof_id (prf, id2)
            val thm = Profile.profile "mp~" mp_tilde (thm1, thm2, t)
            val _ = verify_theorem "mp~" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (NNF_NEG (ids, t)) =>
        let val (prf, thms) = Lib.foldl_map check_proof_id (prf, ids)
            val thm = Profile.profile "nnf_neg" nnf_neg (thms, t)
            val _ = verify_theorem "nnf-neg" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (NNF_POS (ids, t)) =>
        let val (prf, thms) = Lib.foldl_map check_proof_id (prf, ids)
            val thm = Profile.profile "nnf_pos" nnf_pos (thms, t)
            val _ = verify_theorem "nnf-pos" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (NOT_OR_ELIM (id1, t)) =>
        let val (prf, thm) = check_proof_id (prf, id1)
            val thm = Profile.profile "not_or_elim" not_or_elim (thm, t)
            val _ = verify_theorem "not-or-elim" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (PULL_QUANT t) =>
        let val thm = Profile.profile "pull_quant" pull_quant t
            val _ = verify_theorem "pull-quant" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (QUANT_INST t) =>
        let val thm = Profile.profile "quant_inst" quant_inst t
            val _ = verify_theorem "quant-inst" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (QUANT_INTRO (id1, t)) =>
        let val (prf, thm) = check_proof_id (prf, id1)
            val thm = Profile.profile "quant_intro" quant_intro (thm, t)
            val _ = verify_theorem "quant-intro" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (REFL t) =>
        let val thm = Profile.profile "refl" refl t
            val _ = verify_theorem "refl" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (REWRITE t) =>
        let val thm = Profile.profile "rewrite" rewrite t
            val _ = verify_theorem "rewrite" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (REWRITE_STAR (ids, t)) =>
        let val (prf, thms) = Lib.foldl_map check_proof_id (prf, ids)
            val thm = Profile.profile "rewrite_star" rewrite_star (thms, t)
            val _ = verify_theorem "rewrite-star" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (SK t) =>
        let val thm = Profile.profile "sk" sk t
            val _ = verify_theorem "sk" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (SYMM (id1, t)) =>
        let val (prf, thm) = check_proof_id (prf, id1)
            val thm = Profile.profile "symm" symm (thm, t)
            val _ = verify_theorem "symm" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (TH_LEMMA (ids, t)) =>
        let val (prf, thms) = Lib.foldl_map check_proof_id (prf, ids)
            val thm = Profile.profile "th_lemma" th_lemma (thms, t)
            val _ = verify_theorem "th-lemma" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (TRANS (id1, id2, t)) =>
        let val (prf, thm1) = check_proof_id (prf, id1)
            val (prf, thm2) = check_proof_id (prf, id2)
            val thm = Profile.profile "trans" trans (thm1, thm2, t)
            val _ = verify_theorem "trans" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (TRUE_AXIOM t) =>
        let val thm = Profile.profile "true_axiom" true_axiom t
            val _ = verify_theorem "true-axiom" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (UNIT_RESOLUTION (ids, t)) =>
        let val (prf, thms) = Lib.foldl_map check_proof_id (prf, ids)
            val thm = Profile.profile "unit_resolution" unit_resolution (thms, t)
            val _ = verify_theorem "unit-resolution" id t thm
            val prf = Redblackmap.insert (prf, id, THEOREM thm)
        in
          (prf, thm)
        end
      | SOME (THEOREM thm) =>
        (prf, thm)
      | NONE =>
        raise (Feedback.mk_HOL_ERR "Z3" "check_proof"
          ("no proofterm with ID " ^ Int.toString id))
    val thm = Lib.snd (check_proof_id (prf, 0))
    val _ = if !SolverSpec.trace > 0 andalso Thm.concl thm <> boolSyntax.F then
        Feedback.HOL_WARNING "Z3" "check_proof" "final conclusion is not 'F'"
      else ()
    (* eliminate Skolemization hypotheses "sk = def"; cf. function 'sk' above *)
    val thm = List.foldl (fn (sk_def, th) =>
      let val (sk, def) = boolSyntax.dest_eq sk_def
          val th = Thm.INST [{redex = sk, residue = def}] th
          val def_th = Thm.REFL def
          val _ = if !SolverSpec.trace > 0 andalso
                not (HOLset.member (Thm.hypset th, Thm.concl def_th)) then
              Feedback.HOL_WARNING "Z3" "check_proof" "Skolem hyp not found"
            else ()
      in
        Drule.PROVE_HYP def_th th
      end) thm (!skolem_defs)
      (* check that the final theorem contains no hyps other than those that
         have been asserted *)
      val _ = Profile.profile "check_proof(hypcheck)" (fn () =>
        if !SolverSpec.trace > 0 andalso not (HOLset.isSubset (Thm.hypset thm,
          !asserted_hyps)) then
          Feedback.HOL_WARNING "Z3" "check_proof"
            "final theorem contains additional hyp(s)"
        else ()) ()
  in
    thm
  end

  (* parses Z3's output (for an unsatisfiable problem, with proofs enabled,
     i.e., PROOF_MODE=2, DISPLAY_PROOF=true) to obtain a value of type
     'proof' *)

  (* TODO: arguably much nicer to implement with parser combinators *)

  fun parse_proof_file path (ty_dict, tm_dict) : proof =
  let
    val _ = if !SolverSpec.trace > 1 then
        Feedback.HOL_MESG ("HolSmtLib: parsing Z3 proof file '" ^ path ^ "'")
      else ()
    (* invert 'ty_dict' (which is a map from types to strings): we need a map
       from strings to types *)
    val inverse_ty_dict = ref (Redblackmap.foldl (fn (ty, s, dict) =>
      case Redblackmap.peek (dict, s) of
        NONE =>
        Redblackmap.insert (dict, s, ty)
      | SOME _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
          ("inverting dictionary: more than one type maps to '" ^ s ^ "'"))
      ) (Redblackmap.mkDict String.compare) ty_dict)
    (* invert 'tm_dict' (which is a map from terms to strings): we need a map
       from strings to terms *)
    val inverse_tm_dict = ref (Redblackmap.foldl (fn (tm, s, dict) =>
      case Redblackmap.peek (dict, s) of
        NONE =>
        Redblackmap.insert (dict, s, tm)
      | SOME _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
          ("inverting dictionary: more than one term maps to '" ^ s ^ "'"))
      ) (Redblackmap.mkDict String.compare) tm_dict)
    (* char list -> char list -> char list list *)
    fun get_tokens tok [] =
          [List.rev tok]
      | get_tokens tok (#"\r"::cs) =
          List.rev tok :: get_tokens [] cs
      | get_tokens tok (#"\n"::cs) =
          List.rev tok :: get_tokens [] cs
      | get_tokens tok (#" "::cs) =
          List.rev tok :: get_tokens [] cs
      | get_tokens tok (#"#"::cs) =
          List.rev tok :: [#"#"] :: get_tokens [] cs
      | get_tokens tok (#"("::cs) =
          List.rev tok :: [#"("] :: get_tokens [] cs
      | get_tokens tok (#")"::cs) =
          List.rev tok :: [#")"] :: get_tokens [] cs
      | get_tokens tok (#"["::cs) =
          List.rev tok :: [#"["] :: get_tokens [] cs
      | get_tokens tok (#"]"::cs) =
          List.rev tok :: [#"]"] :: get_tokens [] cs
      | get_tokens tok (#":" :: #"=" :: cs) =
          List.rev tok :: [#":", #"="] :: get_tokens [] cs
      | get_tokens tok (#":" :: #":" :: cs) =
          get_tokens (#":" :: #":" :: tok) cs
      | get_tokens tok (#":" :: #"v" :: #"a" :: #"r" :: cs) =
          get_tokens (#"r" :: #"a" :: #"v" :: #":" :: tok) cs
      | get_tokens tok (#":" :: #"p" :: #"a" :: #"t" :: cs) =
          get_tokens (#"t" :: #"a" :: #"p" :: #":" :: tok) cs
      | get_tokens tok (#":" :: #"n" :: #"o" :: #"p" :: #"a" :: #"t" :: cs) =
          get_tokens (#"t" :: #"a" :: #"p" :: #"o" :: #"n" :: #":" :: tok) cs
      | get_tokens tok (#":"::cs) =
          List.rev tok :: [#":"] :: get_tokens [] cs
      | get_tokens tok (c::cs) =
          get_tokens (c::tok) cs
    (* string -> int *)
    fun parse_int id =
      let val id = valOf (Int.fromString id) handle Option =>
            raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
              "parsing error: integer expected")
          val _ = if id < 1 then
            raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                "parsing error: integer less than 1 found")
              else ()
      in
        id
      end
    (* string list * 'a -> int list * 'a *)
    fun parse_int_list (tokens, x) =
      let fun parse_aux ("#" :: id :: tokens) =
                parse_int id :: parse_aux tokens
            | parse_aux [] =
                []
            | parse_aux _ =
                raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                  "error parsing integer list: invalid token sequence")
      in
        (parse_aux tokens, x)
      end
    (* 'a list * 'b -> 'b *)
    fun parse_empty ([], x) =
          x
      | parse_empty _ =
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            "error parsing proofterm: empty token sequence expected")
    (* string list * 'a -> int * 'a *)
    fun parse_one_int (["#", id], x) =
          (parse_int id, x)
      | parse_one_int _ =
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            "error parsing single integer: invalid token sequence")
    (* string list * 'a -> int * int * 'a *)
    fun parse_two_int (["#", id1, "#", id2], x) =
          (parse_int id1, parse_int id2, x)
      | parse_two_int _ =
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            "error parsing pair of integers: invalid token sequence")
    (* string list -> Type.hol_type *)
    fun parse_typ ["int"] =
        intSyntax.int_ty
      | parse_typ ["real"] =
        realSyntax.real_ty
      | parse_typ ["bool"] =
        Type.bool
      | parse_typ [typ] =
        (case Redblackmap.peek (!inverse_ty_dict, typ) of
          SOME T =>
          T
        | NONE =>
          let val T = Type.mk_vartype ("'" ^ typ)
              val _ = case Redblackmap.peek (ty_dict, T) of
                  NONE => ()
                | SOME _ =>
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    ("type " ^ typ ^ " present in the input term"))
              val _ = if !SolverSpec.trace > 2 then
                  Feedback.HOL_MESG ("HolSmtLib: inventing type variable " ^
                    Hol_pp.type_to_string T)
                else ()
              val _ = inverse_ty_dict := Redblackmap.insert
                (!inverse_ty_dict, typ, T)
          in
            T
          end)
      | parse_typ ("(" :: "->" :: tokens) =
        let val _ = if List.length tokens < 3 then
                raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                  "error parsing type: '->' followed by insufficient tokens")
              else ()
            val (tokens, last) = Lib.front_last tokens
            val _ = if last <> ")" then
                raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                  "error parsing type: missing ')' at the end")
              else ()
            (* separate the argument types *)
            fun separate tokens =
              let val (_, tokss, _) =
                List.foldl (fn (tok, acc) =>
                  let val (n, tokss, toks) = acc
                      val n = if tok = "array" then n + 1
                        else if tok = "]" then n - 1
                        else n
                  in
                    if n = 0 then
                      (n, tokss @ [toks @ [tok]], [])
                    else
                      (n, tokss, toks @ [tok])
                  end) (0, [], []) tokens
              in
                tokss
              end
            val typs = List.map parse_typ (separate tokens)
            val (argsT, rngT) = Lib.front_last typs
        in
          List.foldr Type.--> rngT argsT
        end
      | parse_typ ("array" :: "[" :: tokens) =
        (* arrays are translated to function types *)
        let val _ = if List.length tokens < 4 then
                raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                  "error parsing type: 'array' followed by insufficient tokens")
              else ()
            val (tokens, last) = Lib.front_last tokens
            val _ = if last <> "]" then
                raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                  "error parsing type: missing ']' at the end")
              else ()
           (* separate at a ':' token that is not nested within brackets *)
           fun separate 0 acc (":" :: tokens) =
               (List.rev acc, tokens)
             | separate n acc ("[" :: tokens) =
               separate (n+1) ("["::acc) tokens
             | separate n acc ("]" :: tokens) =
               if n<1 then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing type: too many ']'s in array type")
               else
                 separate (n-1) ("]"::acc) tokens
             | separate n acc (t::tokens) =
               separate n (t::acc) tokens
             | separate _ _ [] =
                raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                  "error parsing type: no ':' in array type")
            val (dom_toks, rng_toks) = separate 0 [] tokens
            val domT = parse_typ dom_toks
            val rngT = parse_typ rng_toks
        in
          Type.--> (domT, rngT)
        end
      | parse_typ _ =
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            "error parsing term: unknown type")
    (* (int, Term.term) Redblackmap.dict -> string -> Term.term *)
    fun parse_term_id dict id =
      case Redblackmap.peek (dict, parse_int id) of
        SOME t =>
          t
      | NONE =>
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            ("parsing error: unknown term ID '" ^ id ^ "'"))
    fun parse_proofterm dict tokens =
      let
        val len = List.length tokens
        val _ = if len < 3 then
            raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
              "error parsing proofterm: not enough tokens")
          else ()
        val rule = List.hd tokens
        val (rest, concl) = case List.drop (tokens, len - 4) of
            ["]", ":", "#", id] =>
              (List.tl (List.take (tokens, len - 4)), parse_term_id dict id)
          | _ => (case List.drop (tokens, len - 3) of
            ["]", ":", tok] =>
              (List.tl (List.take (tokens, len - 3)), parse_term dict [tok])
          | _ =>
            raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
              "error parsing proofterm: conclusion not found"))
      in
        (case rule of
          "and-elim"        => AND_ELIM o parse_one_int
        | "asserted"        => ASSERTED o parse_empty
        | "commutativity"   => COMMUTATIVITY o parse_empty
        | "def-axiom"       => DEF_AXIOM o parse_empty
        | "elim-unused"     => ELIM_UNUSED o parse_empty
        | "iff-false"       => IFF_FALSE o parse_one_int
        | "iff-true"        => IFF_TRUE o parse_one_int
        | "lemma"           => LEMMA o parse_one_int
        | "hypothesis"      => HYPOTHESIS o parse_empty
        | "monotonicity"    => MONOTONICITY o parse_int_list
        | "mp"              => MP o parse_two_int
        | "mp~"             => MP_TILDE o parse_two_int
        | "nnf-neg"         => NNF_NEG o parse_int_list
        | "nnf-pos"         => NNF_POS o parse_int_list
        | "not-or-elim"     => NOT_OR_ELIM o parse_one_int
        | "pull-quant"      => PULL_QUANT o parse_empty
        | "quant-inst"      => QUANT_INST o parse_empty
        | "quant-intro"     => QUANT_INTRO o parse_one_int
        | "refl"            => REFL o parse_empty
        | "rewrite"         => REWRITE o parse_empty
        | "rewrite*"        => REWRITE_STAR o parse_int_list
        | "sk"              => SK o parse_empty
        | "symm"            => SYMM o parse_one_int
        | "th-lemma"        => TH_LEMMA o parse_int_list
        | "trans"           => TRANS o parse_two_int
        | "true-axiom"      => TRUE_AXIOM o parse_empty
        | "unit-resolution" => UNIT_RESOLUTION o parse_int_list
        | _ =>
            raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
              ("error parsing proofterm: unknown inference rule '" ^ rule ^
                "'"))) (rest, concl)
      end
    (* (int, Term.term) Redblackmap.dict -> string list -> term list *)
    and parse_term_list dict ("#" :: id :: tokens) =
          parse_term_id dict id :: parse_term_list dict tokens
      | parse_term_list dict (tok :: tokens) =
          parse_term dict [tok] :: parse_term_list dict tokens
      | parse_term_list _ [] =
          []
    (* (int, Term.term) Redblackmap.dict -> string list -> term *)
    and parse_term dict ["(", ":var", id, typ, ")"] =
          (* bound variable *)
          let val bvar = Term.mk_var (":var" ^ id, parse_typ [typ])
              val _ = case Redblackmap.peek (tm_dict, bvar) of
                  SOME _ =>
                    raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                      ("error parsing term: bound variable ':var" ^ id ^
                       "' present in the input term"))
                | NONE => ()
          in
            bvar
          end
      | parse_term dict ["#", id] =
          parse_term_id dict id
      | parse_term dict ("(" :: "forall" :: "(" :: "vars" :: tokens) =
          let val _ = if List.length tokens < 7 then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                "error parsing term: 'forall' followed by insufficient tokens")
                else ()
              val (tokens, last) = Lib.front_last tokens
              val _ = if last <> ")" then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'forall' missing ')' at the end")
                else ()
              fun parse_bvars acc (")" :: rests) =
                (acc, rests)
                | parse_bvars acc ("(" :: name :: typ :: ")" :: rests) =
                let val (acc, rests) = parse_bvars acc rests
                in
                  (Term.mk_var (name, parse_typ [typ]) :: acc, rests)
                end
                | parse_bvars _ _ =
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'forall' followed by invalid tokens")
              val (bvars, tokens) = parse_bvars [] tokens
              fun drop_until_paren (")" :: tokens) =
                  tokens
                | drop_until_paren (_ :: tokens) =
                  drop_until_paren tokens
                | drop_until_paren [] =
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: missing ')' in pattern annotation")
              fun skip_pat ("(" :: ":pat" :: tokens) =
                  drop_until_paren tokens
                | skip_pat ("(" :: ":nopat" :: tokens) =
                  drop_until_paren tokens
                | skip_pat tokens =
                  tokens
              val tokens = skip_pat tokens
              val body = parse_term dict tokens

              (* replace variables ':varN' by properly named variables *)
              val bvars_subst = Lib.mapi (fn i => fn bvar =>
                {redex = Term.mk_var (":var" ^ Int.toString i,
                   Term.type_of bvar), residue = bvar}) (List.rev bvars)
              val body = Term.subst bvars_subst body

              (* decrement index of remaining (to-be-bound) variables ':varN' *)
              val dec = List.length bvars
              val fvars_subst = List.mapPartial (fn var =>
                let val (name, typ) = Term.dest_var var
                in
                  if String.isPrefix ":var" name then
                    let val n = Option.valOf (Int.fromString
                          (String.substring (name, 4, String.size name - 4)))
                        val _ = if n < dec then
                            raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                              "error parsing term: bound variable remains free (type mismatch?)")
                          else ()
                    in
                      SOME {redex = var, residue =
                        Term.mk_var (":var" ^ Int.toString (n - dec), typ)}
                    end
                  else
                    NONE
                end) (Term.free_vars body)
              val body = Term.subst fvars_subst body
          in
            boolSyntax.list_mk_forall (bvars, body)
          end
      | parse_term dict ["(", "~", "#", id1, "#", id2, ")"] =
          (* equisatisfiability is translated as equivalence *)
          boolSyntax.mk_eq (parse_term_id dict id1, parse_term_id dict id2)
      | parse_term dict ("(" :: "distinct" :: tokens) =
          let val _ = if List.null tokens then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'distinct' not followed by a token")
                else ()
              val (tokens, last) = Lib.front_last tokens
              val _ = if last <> ")" then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'distinct' missing ')' at the end")
                else ()
              val operands = parse_term_list dict tokens
              val _ = if List.null operands then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'distinct' has empty argument list")
                else ()
          in
            listSyntax.mk_all_distinct (listSyntax.mk_list
                (operands, Term.type_of (List.hd operands)))
          end
      | parse_term dict ("(" :: "select" :: tokens) =
          let val _ = if List.null tokens then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'select' not followed by a token")
                else ()
              val (tokens, last) = Lib.front_last tokens
              val _ = if last <> ")" then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'select' missing ')' at the end")
                else ()
              val operands = parse_term_list dict tokens
              val _ = if List.length operands <> 2 then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'select' must have 2 arguments")
                else ()
              val array = List.hd operands
              val index = List.hd (List.tl operands)
          in
            Term.mk_comb (array, index)
          end
      | parse_term dict ("(" :: "store" :: tokens) =
          let val _ = if List.null tokens then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'store' not followed by a token")
                else ()
              val (tokens, last) = Lib.front_last tokens
              val _ = if last <> ")" then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'store' missing ')' at the end")
                else ()
              val operands = parse_term_list dict tokens
              val _ = if List.length operands <> 3 then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: 'store' must have 3 arguments")
                else ()
              val array = List.hd operands
              val index = List.hd (List.tl operands)
              val value = List.hd (List.tl (List.tl operands))
          in
            Term.mk_comb (combinSyntax.mk_update (index, value), array)
          end
      | parse_term dict ("(" :: tok :: tokens) =
          (* function application *)
          let val _ = if List.null tokens then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: '(' followed by a single token")
                else ()
              val (tokens, last) = Lib.front_last tokens
              val _ = if last <> ")" then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: application missing ')' at the end")
                else ()
              val operator = parse_term dict [tok]
              val operands = parse_term_list dict tokens
              val _ = if List.null operands then
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    "error parsing term: application has empty argument list")
                else ()
          in
            if operator = boolSyntax.conjunction then
              (* conjunctions of arbitrary arity *)
              boolSyntax.list_mk_conj operands
            else if operator = boolSyntax.disjunction then
              (* disjunctions of arbitrary arity *)
              boolSyntax.list_mk_disj operands
            else
              let (* unary minus is represented as '-' (rather than '~') in
                     Z3's proofs *)
                  val operator = if operator = intSyntax.minus_tm andalso
                    List.length operands = 1 then
                      intSyntax.negate_tm
                    else operator
                  (* overloaded operators: int vs. real *)
                  val int_real_table =
                    [(intSyntax.negate_tm, realSyntax.negate_tm),
                     (intSyntax.plus_tm, realSyntax.plus_tm),
                     (intSyntax.minus_tm, realSyntax.minus_tm),
                     (intSyntax.mult_tm, realSyntax.mult_tm),
                     (intSyntax.less_tm, realSyntax.less_tm),
                     (intSyntax.leq_tm, realSyntax.leq_tm),
                     (intSyntax.great_tm, realSyntax.great_tm),
                     (intSyntax.geq_tm, realSyntax.geq_tm)]
                  val operator = if Term.type_of (List.hd operands) =
                    realSyntax.real_ty then
                      case List.find (fn (int_op, _) => int_op = operator)
                        int_real_table of
                        SOME (_, real_op) => real_op
                      | NONE => operator
                    else
                      operator
              in
                (* the type of polymorphic operators must be instantiated to
                   match their actual argument types *)
                boolSyntax.list_mk_icomb (operator, operands)
              end
          end
      | parse_term _ [tok] =
          (case List.find (fn (_, s, _, _) => s = tok) SmtLib.OperatorsTable of
            SOME (t, _, _, _) =>
            (* built-in constants *)
            t
          | NONE =>
            (case Redblackmap.peek (!inverse_tm_dict, tok) of
              SOME t =>
              (* user-defined constants *)
              t
            | NONE =>
              let val length = String.size tok
              in
                if length > 5 andalso
                  String.extract (tok, length - 5, NONE) = "::int" then
                  (* integer numerals *)
                  let val numeral = String.extract (tok, 0, SOME (length - 5))
                  in
                    intSyntax.term_of_int (Arbint.fromString numeral)
                  end
                else if length > 6 andalso
                  String.extract (tok, length - 6, NONE) = "::real" then
                  (* real numerals *)
                  let val numeral = String.extract (tok, 0, SOME (length - 6))
                  in
                    realSyntax.term_of_int (Arbint.fromString numeral)
                  end
                else
                  raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                    ("error parsing term: unknown token '" ^ tok ^ "'"))
              end))
      | parse_term _ _ =
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            "error parsing term: invalid token sequence")
    fun parse_proof_definition (dict, proof) id tokens =
      let val _ = case Redblackmap.peek (proof, id) of
          NONE => ()
        | SOME _ =>
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            ("proof ID " ^ Int.toString id ^ " used more than once"))
          val pt = parse_proofterm dict tokens
          val proof = Redblackmap.insert (proof, id, pt)
      in
        (dict, proof)
      end
    fun parse_term_definition (dict, proof) id tokens =
      let val _ = case Redblackmap.peek (dict, id) of
          NONE => ()
        | SOME _ =>
          raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
            ("term ID " ^ Int.toString id ^ " used more than once"))
          val t = parse_term dict tokens
          val dict = Redblackmap.insert (dict, id, t)
      in
        (dict, proof)
      end
    (* parses a single line *)
    fun parse_token_line (dict, proof) tokens =
      case tokens of
        [] =>
          (dict, proof)
      | ["unsat"] =>
          (dict, proof)
      | "decl" :: name :: "::" :: tokens =>
          let val _ = case Redblackmap.peek (!inverse_tm_dict, name) of
              NONE => ()
            | SOME _ =>
              raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                ("term name '" ^ name ^ "' used more than once"))
              val t = Term.mk_var (name, parse_typ tokens)
              val _ = inverse_tm_dict := Redblackmap.insert
                (!inverse_tm_dict, name, t)
          in
            (dict, proof)
          end
      | "#" :: _ :: ":=" :: "(" :: "pattern" :: _ =>
          (* ignore pattern definitions *)
          (dict, proof)
      | "#" :: id :: ":=" :: tokens =>
          let val id = parse_int id
          in
            case tokens of
              "[" :: tokens =>
                parse_proof_definition (dict, proof) id tokens
            | _ =>
                parse_term_definition (dict, proof) id tokens
          end
      | "[" :: tokens =>
            parse_proof_definition (dict, proof) 0 tokens
      | _ => raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
                  "parse_token_line: invalid token sequence")
    val instream = TextIO.openIn path
    (* (int, Term.term) Redblackmap.dict * proof -> proof *)
    fun parse_all_lines (dict, proof) =
      if TextIO.endOfStream instream then
        proof
      else
        let val line = valOf (TextIO.inputLine instream)
              handle Option => raise (Feedback.mk_HOL_ERR "Z3"
                "parse_proof_file" "parse_all_lines: no more line")
            val tokens = map String.implode (List.filter (not o Lib.equal [])
                           (get_tokens [] (String.explode line)))
            val _ = if !SolverSpec.trace > 2 then
                Feedback.HOL_MESG ("HolSmtLib: parsing token(s) " ^
                  String.concat (Lib.separate ", " tokens))
              else ()
        in
          parse_all_lines (parse_token_line (dict, proof) tokens)
        end
    val proof = parse_all_lines (Redblackmap.mkDict Int.compare,
                                 Redblackmap.mkDict Int.compare)
    val _ = TextIO.closeIn instream
  in
    proof
  end

  local val infile = "input.z3.smt"
        val outfile = "output.z3"
  in
    (* Z3 (via Wine), SMT-LIB file format, no proofs *)
    val Z3_Wine_SMT_Oracle = SolverSpec.make_solver
      (write_strings_to_file infile o Lib.snd o SmtLib.term_to_SmtLib)
      ("wine C:\\\\Z3\\\\bin\\\\z3.exe /smt " ^ infile ^ " > " ^ outfile)
      (fn () => is_sat_DOS outfile)
      [infile, outfile]

    (* Z3 (Linux/Unix), SMT-LIB file format, no proofs *)
    val Z3_SMT_Oracle = SolverSpec.make_solver
      (write_strings_to_file infile o Lib.snd o SmtLib.term_to_SmtLib)
      ("z3 -smt " ^ infile ^ " > " ^ outfile)
      (fn () => is_sat_Unix outfile)
      [infile, outfile]

    (* Z3 (Linux/Unix), SMT-LIB file format, with proofs *)
    val Z3_SMT_Prover = SolverSpec.make_solver
      (fn tm => let val (ty_tm_dict, lines) = SmtLib.term_to_SmtLib tm
                in
                  write_strings_to_file infile lines;
                  (tm, ty_tm_dict)
                end)
      ("z3 -ini:z3.ini -smt " ^ infile ^ " > " ^ outfile)
      (fn (tm, ty_tm_dict) => let val result = is_sat_Unix outfile
         in
           case result of
             SolverSpec.UNSAT NONE =>
             let val thm = check_proof (parse_proof_file outfile ty_tm_dict)
                 (* discharging definitions: INT_MIN, INT_MAX, ABS *)
                 val INT_ABS = intLib.ARITH_PROVE
                   ``!n. ABS (n:int) = if n < 0 then 0 - n else n``
                 val thm = List.foldl (fn (hyp, th) =>
                   let val hyp_th = bossLib.METIS_PROVE
                     [integerTheory.INT_MIN, integerTheory.INT_MAX, INT_ABS] hyp
                   in
                     Drule.PROVE_HYP hyp_th th
                   end handle Feedback.HOL_ERR _ =>
                     th) thm (Thm.hyp thm)
                 (* unfolding definitions in 'tm' *)
                 val tm_eq_simp = simpLib.SIMP_CONV simpLib.empty_ss
                   [boolTheory.bool_case_DEF] tm
                   handle Conv.UNCHANGED =>
                     Thm.REFL tm
                 val tm_eq_simp = Conv.BETA_RULE tm_eq_simp
                 val simp_eq_tm = Thm.SYM tm_eq_simp
                 val thm = Drule.DISCH_ALL thm
                 val thm = simpLib.SIMP_RULE simpLib.empty_ss [simp_eq_tm] thm
                 val thm = Drule.UNDISCH_ALL thm
             in
               SolverSpec.UNSAT (SOME thm)
             end
           | _ => result
           end)
      [infile, outfile]
  end

end
