open HolKernel Parse boolLib bossLib finite_mapTheory;
open recursivefnsTheory;
open prnlistTheory;
open primrecfnsTheory;
open listTheory;
open arithmeticTheory;
open numpairTheory;
open pred_setTheory;
val _ = new_theory "turing_machine";

(*
Li and Vitayi book
Turing mahines consist of
    Finite program
    Cells
    List of cells called tape
    Head, on one of the cells
    Tape has left and right
    Each cell is either 0,1 or Blank
    Finite program can be in a finite set of states Q
    Time, which is in the set {0,1,2,...}
    Head is said     to 'scan' the cell it is currently over
    At time 0 the cell the head is over is called the start cell
    At time 0 every cell is Blank except
        a finite congituous sequence from the strat cell to the right, containing only 0' and 1's
    This sequence is called the input

    We have two operations
        We can write A = {0,1,B} in the cell being scanned
        The head can shift left or right
    There is one operation per time unit (step)
    After each step, the program takes on a state from Q

    The machine follows a set of rules
    The rules are of the form (p,s,a,q)
        p is the current state of the program
        s is the symbol under scan
        a is the next operation to be exectued, in S = {0,1,B,L,R}
        q is the next state of the program
    For any two rules, the first two elements must differ
    Not every possible rule (in particular, combination of first two rules) is in the set of rules
    This way the device can perform the 'no' operation, if this happens the device halts

    We define a turing machine as a mapping from a finite subset of QxA to SxQ

    We can associate a partial function to each Turing machine
        The input to the machine is presented as an n-tuple (x1,...xn) of binary strings
        in the form of a single binary string consisting of self-deliminating versions of xi's
        The integer repesented by the maxiaml binary string of which some bit is scanned
        or '0' if Blank is scanned by the time the machine halts is the output


    This all leads to this definition
    Each turing machine defines a partial function from n-tuples of integers into inetgers n>0
    Such a function is called 'partially recursive' or 'computable'
    If total then just recursive
                           *)


val _ = remove_termtok {term_name = "O", tok = "O"}

val _ = Datatype `action = Wr0 | Wr1 | L | R`;


val _ = Datatype `cell = Z | O `;

val _ = Datatype `TM = <| state : num;
                          prog : ((num # cell) |->  (num # action));
                          tape_l : cell list;
                          tape_h : cell;
                          tape_r : cell list
                       |>`;

val concatWith_def = Define`
  (concatWith sep [] = []) /\
  (concatWith sep [x] = x) /\
  (concatWith sep (x::y::rest) = x ++ sep ++ concatWith sep (y::rest))`;

val INITIAL_TAPE_TM_def = Define `
  (INITIAL_TAPE_TM tm [] = tm) ∧
  (INITIAL_TAPE_TM tm (h::t) =
    tm with <|tape_l := [] ; tape_h := h ; tape_r := t|>)
`;

val INITIAL_TM_def = Define`
  INITIAL_TM p args =
    INITIAL_TAPE_TM <| state := 0;  prog := p;tape_l := [];
                       tape_h := Z;tape_r := [] |>
                    (concatWith [Z] (MAP (GENLIST (K O)) args))`;

val UPDATE_TAPE_def = Define `
  UPDATE_TAPE tm =
    if (tm.state,tm.tape_h) IN FDOM tm.prog ∧ tm.state <> 0 then
      let tm' = tm with state := FST (tm.prog ' (tm.state, tm.tape_h))
      in
        case SND (tm.prog ' (tm.state ,tm.tape_h)) of
          Wr0 => tm' with tape_h := Z
        | Wr1 => tm' with tape_h := O
        | L   => if (tm.tape_l = [])
                 then tm' with <| tape_l := []; tape_h := Z ;
                                  tape_r := tm.tape_h::tm.tape_r |>
                 else tm' with <| tape_l := TL tm.tape_l;
                                  tape_h := HD tm.tape_l ;
                                  tape_r := tm.tape_h::tm.tape_r |>
        | R   => if (tm.tape_r = []) then
                  tm' with <| tape_l := tm.tape_h::tm.tape_l; tape_h := Z;
                              tape_r := [] |>
                 else tm' with <| tape_l := tm.tape_h::tm.tape_l;
                                  tape_h := HD tm.tape_r;
                                  tape_r := TL tm.tape_r |>
    else tm with state := 0
`;

val _ = overload_on("RUN",``FUNPOW UPDATE_TAPE``);


val DECODE_def = tDefine "DECODE" `
  (DECODE 0 = []) ∧
  (DECODE n = if (ODD n) then [O] ++ (DECODE ((n-1) DIV 2))
              else [Z] ++ (DECODE (n DIV 2)))`
  (WF_REL_TAC `$<` >> rw[] >> fs[ODD_EXISTS] >>
   `2 * m DIV 2 = m` by metis_tac[MULT_COMM, DECIDE “0 < 2”, MULT_DIV] >>
   simp[])

val ENCODE_def = Define `
  (ENCODE [] = 0) ∧
  (ENCODE (h::t) = case h of
                     Z => 0 + (2 * (ENCODE t))
                   | O => 1 + (2 * (ENCODE t))
                   | _ => 0)`;

(* Change TO simpler def of DECODE*)

(* Lemmas for ENCODE/DECODE*)

val ENCODE_DECODE_thm = store_thm(
  "ENCODE_DECODE_thm",
  ``!n. ENCODE (DECODE n) = n``,
  completeInduct_on `n` >> Cases_on `n` >- EVAL_TAC >> rw[DECODE_def]
  >- (rw[ENCODE_def]
      >> `0<2` by fs[] >> `n' DIV 2 <= n'` by metis_tac[DIV_LESS_EQ]
      >> `n' < SUC n'` by fs[] >> `n' DIV 2 < SUC n'` by fs[]
      >> `ENCODE (DECODE (n' DIV 2)) = n' DIV 2` by fs[] >> rw[]
      >> `~ODD n'` by metis_tac[ODD]
      >> `EVEN n'` by metis_tac[EVEN_OR_ODD]
      >> `n' MOD 2 =0` by metis_tac[EVEN_MOD2]
      >> `2 * (n' DIV 2) = n'` by metis_tac[MULT_EQ_DIV]
      >> rw[])
  >> rw[ENCODE_def]
  >> `EVEN (SUC n')` by metis_tac[EVEN_OR_ODD]
  >> `(SUC n') MOD 2 =0` by metis_tac[EVEN_MOD2]
  >> `2 * ((SUC n') DIV 2) = SUC n'` by fs[MULT_EQ_DIV]);

val DECODE_EMPTY_lem = Q.store_thm (
  "DECODE_EMPTY_lem",
  `∀ n. (DECODE n = []) ==> (n=0)`,
  Induct_on `n` >- EVAL_TAC >> fs[] >> rw[DECODE_def]  );

val ENCODE_TM_TAPE_def = Define `
  ENCODE_TM_TAPE tm =
       if tm.tape_h = Z then
           (ENCODE tm.tape_l   *,   (2 * (ENCODE tm.tape_r)))
       else
           (ENCODE tm.tape_l   *,   (2 * (ENCODE tm.tape_r) + 1))
`;

val DECODE_TM_TAPE_def = Define `
  DECODE_TM_TAPE n =
       if EVEN (nsnd n) then
           (DECODE (nfst n), Z , DECODE ( (nsnd n) DIV 2))
       else
           (DECODE (nfst n), O , DECODE ( (nsnd n - 1) DIV 2))`;

(* Halted definition and TM examples *)
val HALTED_def = Define `HALTED tm <=> (tm.state = 0)`;

(*

The set of Partial Recursive Functions is identical to the set of
Turing Machines computable functions

Total Recursive Function correspond to Turing Machine computable functions that always halt

One can enumerate the Valid Turing Machines (by enumerating programs)

*)

val NUM_CELL_def = Define `
  (NUM_CELL Z = 0:num) ∧
  (NUM_CELL O = 1:num) `;

val CELL_NUM_def = Define `
  (CELL_NUM 0n = Z) ∧
  (CELL_NUM 1 = O) `;

val ACT_TO_NUM_def = Define `
  (ACT_TO_NUM Wr0 = 0:num) ∧
  (ACT_TO_NUM Wr1 = 1:num) ∧
  (ACT_TO_NUM L   = 2:num) ∧
  (ACT_TO_NUM R   = 3:num) `;

val NUM_TO_ACT_def = Define `
  (NUM_TO_ACT 0n = Wr0 ) ∧
  (NUM_TO_ACT 1 = Wr1) ∧
  (NUM_TO_ACT 2 = L) ∧
  (NUM_TO_ACT 3 = R) `;

val FULL_ENCODE_TM_def = Define `
  FULL_ENCODE_TM tm = tm.state *, ENCODE_TM_TAPE tm
`;


val FULL_DECODE_TM_def = Define `
  FULL_DECODE_TM n = <| state:=  nfst n;
                        tape_l := FST (DECODE_TM_TAPE (nsnd n));
                        tape_h := FST (SND (DECODE_TM_TAPE (nsnd n)));
                        tape_r := SND (SND (DECODE_TM_TAPE (nsnd n)))|>
`;

(* Perform action an move to state *)
val UPDATE_ACT_S_TM_def = Define `UPDATE_ACT_S_TM s act tm =
           let tm' = tm with state := s
           in
               case act of
                   Wr0 => tm' with tape_h := Z
                 | Wr1 => tm' with tape_h := O
                 | L   => if (tm.tape_l = [])
                          then tm' with <| tape_l := [];
                               tape_h := Z ;
                               tape_r := tm.tape_h::tm.tape_r |>
                          else tm' with <| tape_l := TL tm.tape_l;
               tape_h := HD tm.tape_l ;
               tape_r := tm.tape_h::tm.tape_r |>
               | R   => if (tm.tape_r = [])
                        then tm' with <| tape_l := tm.tape_h::tm.tape_l;
                             tape_h := Z ;
                             tape_r := [] |>
                        else tm' with <| tape_l := tm.tape_h::tm.tape_l;
               tape_h := HD tm.tape_r;
               tape_r := TL tm.tape_r |>`;

val ODD_DIV_2_lem = Q.store_thm ("ODD_DIV_2_lem",
  `∀ y. ODD y ==> (y DIV 2 = (y-1) DIV 2)`,
  simp[ODD_EXISTS, PULL_EXISTS, ADD1, ADD_DIV_RWT]);

val WRITE_0_HEAD_lem = Q.store_thm("WRITE_0_HEAD_lem",
  `∀ tm s. (UPDATE_ACT_S_TM s Wr0 tm).tape_h = Z`,
  rpt strip_tac >> rw[UPDATE_ACT_S_TM_def] );


val WRITE_1_HEAD_lem = Q.store_thm("WRITE_1_HEAD_lem",
  `∀ tm s. (UPDATE_ACT_S_TM s Wr1 tm).tape_h = O`,
  rpt strip_tac >> rw[UPDATE_ACT_S_TM_def] );

val ODD_TL_DECODE_lem = Q.store_thm ("ODD_TL_DECODE_lem",
  `∀ n. ODD n ==> (TL (DECODE n) = DECODE ((n-1) DIV 2))`,
  rpt strip_tac >> `EVEN 0` by EVAL_TAC >> `n ≠ 0` by metis_tac[EVEN_AND_ODD]>>
  rw[DECODE_def] >> Cases_on `DECODE n` >- `n=0` by fs[DECODE_EMPTY_lem] >>
  EVAL_TAC >> Cases_on `n` >- fs[] >> fs[DECODE_def] >> rfs[] );

val EVEN_TL_DECODE_lem = Q.store_thm ("EVEN_TL_DECODE_lem",
  `∀ n. ((EVEN n) ∧ (n > 0)) ==> (TL (DECODE n) = DECODE (n DIV 2))`,
  rpt strip_tac >> Cases_on `n` >- fs[]  >>
  rw[DECODE_def] >> metis_tac[EVEN_AND_ODD] );

val ODD_MOD_TWO_lem = Q.store_thm ("ODD_MOD_TWO_lem",
  `∀n. (ODD n) ==> (n MOD 2 = 1)`,
  rpt strip_tac  >> fs[MOD_2] >> `~EVEN n` by metis_tac[EVEN_AND_ODD] >> rw[]);

val containment_lem = Q.store_thm("containment_lem",
  `((OLEAST n. (nfst n,CELL_NUM (nsnd n)) ∈ FDOM p) = NONE) <=> (p = FEMPTY)`,
  rw[] >> eq_tac >> simp[] >> csimp[fmap_EXT] >>
  simp[EXTENSION,pairTheory.FORALL_PROD] >> strip_tac >>
  qx_gen_tac `a` >> qx_gen_tac `b` >>
  `∃c. b = CELL_NUM c` by metis_tac[CELL_NUM_def,theorem"cell_nchotomy"] >>
  rw[] >>
  pop_assum (qspec_then `a *, c` mp_tac) >> simp[]);


val UPDATE_TAPE_ACT_STATE_TM_thm = Q.store_thm("UPDATE_TAPE_ACT_STATE_TM_thm",
  `∀ tm.
    ((tm.state , tm.tape_h) ∈ FDOM tm.prog) ∧ tm.state <> 0 ==>
    (UPDATE_ACT_S_TM (FST (tm.prog ' (tm.state, tm.tape_h)))
                     (SND (tm.prog ' (tm.state, tm.tape_h)))
                     tm
       =
     UPDATE_TAPE tm)`,
  strip_tac >> fs[UPDATE_ACT_S_TM_def,UPDATE_TAPE_def]  );

val NUM_TO_ACT_TO_NUM = Q.store_thm("NUM_TO_ACT_TO_NUM[simp]",
  `((ACT_TO_NUM k) < 4) ==> (NUM_TO_ACT (ACT_TO_NUM k) = k)`,
  rw[NUM_TO_ACT_def,ACT_TO_NUM_def] >>
  `(ACT_TO_NUM k = 0) ∨ (ACT_TO_NUM k = 1) ∨(ACT_TO_NUM k = 2)∨
   (ACT_TO_NUM k = 3)` by simp[] >>rw[]>>
  EVAL_TAC >> Cases_on `k` >> rfs[ACT_TO_NUM_def] >> EVAL_TAC);
val _ = export_rewrites ["NUM_CELL_def"]

val TM_PROG_P_TAPE_H = Q.store_thm("TM_PROG_P_TAPE_H[simp]",
  `(tm with prog := p).tape_h = tm.tape_h`,
  fs[]);

val TM_PROG_P_STATE = Q.store_thm("TM_PROG_P_STATE[simp]",
  `(tm with prog := p).state = tm.state`,
  fs[]);

val UPDATE_TM_ARB_Q = Q.store_thm("UPDATE_TM_ARB_Q",
  `(tm.state,tm.tape_h) ∈ FDOM p ∧ tm.state <> 0 ==>
   (UPDATE_ACT_S_TM (FST (p ' (tm.state,tm.tape_h)))
                    (SND (p ' (tm.state,tm.tape_h)))
                    (tm with prog := q) =
    (UPDATE_TAPE (tm with prog := p)) with prog := q)`,
  rw[UPDATE_TAPE_def,UPDATE_ACT_S_TM_def] >>
  Cases_on `SND (p ' (tm.state,tm.tape_h))` >> simp[] )

val tm_with_prog = Q.store_thm("tm_with_prog",
  `tm with prog := tm.prog = tm`,simp[theorem("TM_component_equality")])

val FST_DECODE_TM_TAPE = Q.store_thm(
  "FST_DECODE_TM_TAPE[simp]",
  `FST (DECODE_TM_TAPE tp) = DECODE (nfst tp)`,
  rw[DECODE_TM_TAPE_def])

val DECODE_EQ_NIL = Q.store_thm(
  "DECODE_EQ_NIL[simp]",
  `(DECODE n = []) ⇔ (n = 0)`,
  metis_tac[DECODE_EMPTY_lem, DECODE_def]);

val ODD_HD_DECODE = Q.store_thm(
  "ODD_HD_DECODE",
  `ODD n ==> (HD (DECODE n) = O)`,
  Cases_on `n` >> simp[DECODE_def]);

val EVEN_HD_DECODE = Q.store_thm(
 "EVEN_HD_DECODE",
`EVEN n ∧ (n ≠ 0)  ==> (HD (DECODE n) = Z)`,
Cases_on `n` >> simp[DECODE_def] >> metis_tac[EVEN_AND_ODD,listTheory.HD]);

val SND_SND_DECODE_TM_TAPE = Q.store_thm("SND_SND_DECODE_TM_TAPE",
`SND (SND (DECODE_TM_TAPE (nsnd tmn))) = DECODE (nsnd (nsnd tmn) DIV 2)`,
rw[DECODE_TM_TAPE_def] >> `ODD (nsnd (nsnd tmn))` by metis_tac[EVEN_OR_ODD] >>
  rw[ODD_DIV_2_lem]);

val SND_SND_DECODE_TM_TAPE_FULL = Q.store_thm(
  "SND_SND_DECODE_TM_TAPE_FULL[simp]",
  `SND (SND (DECODE_TM_TAPE (t))) = DECODE (nsnd ( t) DIV 2)`,
  rw[DECODE_TM_TAPE_def] >> `ODD (nsnd (t))` by metis_tac[EVEN_OR_ODD] >>
  rw[ODD_DIV_2_lem]);

val FST_SND_DECODE_TM_TAPE_FULL = Q.store_thm(
  "FST_SND_DECODE_TM_TAPE_FULL[simp]",
  `ODD (nsnd (t)) ==> (FST (SND (DECODE_TM_TAPE (t))) = O)`,
  rw[DECODE_TM_TAPE_def] >> metis_tac[EVEN_AND_ODD]);

val FST_SND_DECODE_TM_TAPE_EVEN_FULL = Q.store_thm(
  "FST_SND_DECODE_TM_TAPE_EVEN_FULL[simp]",
  `EVEN (nsnd (t)) ==> (FST (SND (DECODE_TM_TAPE (t))) = Z)`,
  rw[DECODE_TM_TAPE_def]);

val MEMBER_CARD = Q.store_thm(
  "MEMBER_CARD",
  `a ∈ FDOM p ⇒ 0 < CARD (FDOM p)`,
  Induct_on `p` >> simp[] );

val npair_lem = Q.store_thm("npair_lem",
  `(∀n. P n) <=> (∀j k. P (j *, k))`,
  eq_tac >> simp[] >>
  rpt strip_tac >> `∃j k. j *, k = n` by metis_tac[npair_cases] >> rw[] );

val NUM_TO_CELL_TO_NUM = Q.store_thm("NUM_TO_CELL_TO_NUM",
  `((c=0) ∨ (c=1)) ==> (NUM_CELL (CELL_NUM c) = c)`,
  strip_tac >> rw[NUM_CELL_def,CELL_NUM_def]);

val FULL_ENCODE_TM_STATE = Q.store_thm("FULL_ENCODE_TM_STATE[simp]",
  `nfst (FULL_ENCODE_TM tm) = tm.state`,
  fs[FULL_ENCODE_TM_def]);

val tri_mono = Q.store_thm ("tri_mono[simp]",
  `∀x y. (tri x <= tri y) <=> (x <= y)`,
  Induct_on `y` >> simp[]  );

val npair_mono = Q.store_thm ("npair_mono[simp]",
  `(x *, y < x *, z )<=> (y<z)`,
  simp[EQ_IMP_THM,npair_def] >> conj_tac
  >- (spose_not_then strip_assume_tac >> `z<=y` by simp[] >>
      `tri(x+z) <= tri(x+y)` by simp[] >>
      `z+tri(x+z) <= y+tri(x+y)` by simp[] >> fs[])
  >- (strip_tac >>
      irule (DECIDE “x < y ∧ a < b ⇒ x + a < y + b”) >> simp[]));


val CELL_NUM_LEM1 = Q.store_thm("CELL_NUM_LEM1",
  `(∀n'. n' < n ⊗ c ⇒ (nfst n',CELL_NUM (nsnd n')) ∉ FDOM p) ∧
   (n,CELL_NUM c) ∈ FDOM p ==> (c=0) ∨ (c=1)`,
  spose_not_then strip_assume_tac >> Cases_on `CELL_NUM c`
  >- (`0<c` by simp[] >>
      metis_tac[nfst_npair,nsnd_npair,npair_mono,CELL_NUM_def]) >>
  `1<c` by simp[] >> metis_tac[nfst_npair,nsnd_npair,npair_mono,CELL_NUM_def]);

val TM_ACT_LEM_1 = Q.store_thm("TM_ACT_LEM_1[simp]",
  `( (nsnd (nsnd (FULL_ENCODE_TM tm))) MOD 2) = NUM_CELL (tm.tape_h)`,
  simp[FULL_ENCODE_TM_def,ENCODE_TM_TAPE_def] >> rw[] >> Cases_on `tm.tape_h` >- fs[] >- EVAL_TAC)

val _ = add_rule {term_name = "FULL_ENCODE_TM",fixity = Closefix,
                  block_style = (AroundEachPhrase,(PP.CONSISTENT,0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "⟦",TM,TOK"⟧"]}

val FULL_ENCODE_IGNORES_PROGS = Q.store_thm("FULL_ENCODE_IGNORES_PROGS[simp]",
`⟦tm with prog := p⟧ = ⟦tm⟧`,
simp[FULL_ENCODE_TM_def,ENCODE_TM_TAPE_def]);

val NUM_CELL_INJ = Q.store_thm("NUM_CELL_INJ",
`(NUM_CELL a = NUM_CELL b) <=> (a = b)`,
eq_tac >- (Cases_on ` a` >> Cases_on `b` >> rw[] ) >- (rw[]) )

val ACT_TO_NUM_LESS_4 = Q.store_thm("ACT_TO_NUM_LESS_4",
`ACT_TO_NUM a < 4`,
Cases_on `a` >> EVAL_TAC)

val TWO_TIMES_DIV_TWO_thm = Q.store_thm("TWO_TIMES_DIV_TWO_thm[simp]",
  `2 *  n DIV 2 = n`,
  metis_tac[DECIDE “0 < 2”, MULT_DIV, MULT_COMM]);

val TWO_TIMES_P_ONE_DIV_TWO_thm = Q.store_thm(
  "TWO_TIMES_P_ONE_DIV_TWO_thm[simp]",
  `(2 * n + 1) DIV 2 = n`,
  metis_tac[DECIDE “1 < 2”, DIV_MULT, MULT_COMM]);

val ENCODE_CONS_DECODE_ENCODE_thm = Q.store_thm(
  "ENCODE_CONS_DECODE_ENCODE_thm[simp]",
  `ENCODE (h::DECODE (ENCODE t)) = ENCODE (h::t)`,
  fs[ENCODE_def,DECODE_def,ENCODE_DECODE_thm]);

val NFST_ENCODE_TM_TAPE = Q.store_thm("NFST_ENCODE_TM_TAPE[simp]",
`nfst (ENCODE_TM_TAPE tm) = ENCODE tm.tape_l`,
rw[ENCODE_TM_TAPE_def]);

val FST_SND_DECODE_TM_TAPE = Q.store_thm("FST_SND_DECODE_TM_TAPE[simp]",
`FST (SND (DECODE_TM_TAPE (ENCODE_TM_TAPE tm))) = tm.tape_h`,
rw[DECODE_TM_TAPE_def,ENCODE_TM_TAPE_def] >> fs[EVEN_MULT,EVEN_ADD] >>
Cases_on `tm.tape_h` >> fs[]);

val NSND_ENCODE_TM_TAPE_DIV2 = Q.store_thm("NSND_ENCODE_TM_TAPE_DIV2[simp]",
`(nsnd (ENCODE_TM_TAPE tm) DIV 2) = ENCODE tm.tape_r`,
rw[ENCODE_TM_TAPE_def]);

val _ = export_theory();
