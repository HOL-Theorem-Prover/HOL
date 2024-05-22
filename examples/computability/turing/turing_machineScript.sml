open HolKernel Parse boolLib bossLib finite_mapTheory;
open recursivefnsTheory;
open prnlistTheory;
open nlistTheory
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

Datatype:
  action = Wr0 | Wr1 | L | R
End

Datatype:
  cell = Z | O
End

Datatype:
  TM = <| state : num;
          prog : ((num # cell) |->  (num # action));
          tape_l : cell list;
          tape_h : cell;
          tape_r : cell list
       |>
End

Definition concatWith_def:
  (concatWith sep [] = []) /\
  (concatWith sep [x] = x) /\
  (concatWith sep (x::y::rest) = x ++ sep ++ concatWith sep (y::rest))
End

Definition INITIAL_TAPE_TM_def:
  (INITIAL_TAPE_TM tm [] = tm) ∧
  (INITIAL_TAPE_TM tm (h::t) =
    tm with <|tape_l := [] ; tape_h := h ; tape_r := t|>)
End

Definition INITIAL_TM_def:
  INITIAL_TM p args =
    INITIAL_TAPE_TM <| state := 0;  prog := p;tape_l := [];
                       tape_h := Z;tape_r := [] |>
                    (concatWith [Z] (MAP (GENLIST (K O)) args))
End

Definition UPDATE_TAPE_def:
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
End

Overload "RUN" = ``FUNPOW UPDATE_TAPE``

Definition DECODE_def:
  (DECODE 0 = []) ∧
  (DECODE n = if (ODD n) then [O] ++ (DECODE ((n-1) DIV 2))
              else [Z] ++ (DECODE (n DIV 2)))
Termination
   WF_REL_TAC `$<` >> rw[] >> fs[ODD_EXISTS] >>
   `2 * m DIV 2 = m` by metis_tac[MULT_COMM, DECIDE “0 < 2”, MULT_DIV] >>
   simp[]
End

Definition ENCODE_def:
  (ENCODE [] = 0) ∧
  (ENCODE (h::t) = case h of
                     Z => 0 + (2 * (ENCODE t))
                   | O => 1 + (2 * (ENCODE t))
                   | _ => 0)
End

(* Change TO simpler def of DECODE*)

(* Lemmas for ENCODE/DECODE*)

Theorem ENCODE_DECODE_thm:
 !n. ENCODE (DECODE n) = n
Proof
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
  >> `2 * ((SUC n') DIV 2) = SUC n'` by fs[MULT_EQ_DIV]
QED

Theorem DECODE_EMPTY_lem:
  ∀ n. (DECODE n = []) ==> (n=0)
Proof
  Induct_on `n` >- EVAL_TAC >> fs[] >> rw[DECODE_def]
QED

Definition ENCODE_TM_TAPE_def:
  ENCODE_TM_TAPE tm =
       if tm.tape_h = Z then
           (ENCODE tm.tape_l   *,   (2 * (ENCODE tm.tape_r)))
       else
           (ENCODE tm.tape_l   *,   (2 * (ENCODE tm.tape_r) + 1))
End

Definition DECODE_TM_TAPE_def:
  DECODE_TM_TAPE n =
       if EVEN (nsnd n) then
           (DECODE (nfst n), Z , DECODE ( (nsnd n) DIV 2))
       else
         (DECODE (nfst n), O , DECODE ( (nsnd n - 1) DIV 2))
End

(* Halted definition and TM examples *)
Definition HALTED_def:
  HALTED tm <=> (tm.state = 0)
End

(*

The set of Partial Recursive Functions is identical to the set of
Turing Machines computable functions

Total Recursive Function correspond to Turing Machine computable functions that always halt

One can enumerate the Valid Turing Machines (by enumerating programs)

*)

Definition NUM_CELL_def:
  (NUM_CELL Z = 0:num) ∧
  (NUM_CELL O = 1:num)
End

Definition CELL_NUM_def:
  (CELL_NUM 0n = Z) ∧
  (CELL_NUM 1 = O)
End

Definition ACT_TO_NUM_def:
  (ACT_TO_NUM Wr0 = 0:num) ∧
  (ACT_TO_NUM Wr1 = 1:num) ∧
  (ACT_TO_NUM L   = 2:num) ∧
  (ACT_TO_NUM R   = 3:num)
End

Definition NUM_TO_ACT_def:
  (NUM_TO_ACT 0n = Wr0 ) ∧
  (NUM_TO_ACT 1 = Wr1) ∧
  (NUM_TO_ACT 2 = L) ∧
  (NUM_TO_ACT 3 = R)
End

Definition FULL_ENCODE_TM_def:
  FULL_ENCODE_TM tm = tm.state *, ENCODE_TM_TAPE tm
End


Definition FULL_DECODE_TM_def:
  FULL_DECODE_TM n = <| state:=  nfst n;
                        tape_l := FST (DECODE_TM_TAPE (nsnd n));
                        tape_h := FST (SND (DECODE_TM_TAPE (nsnd n)));
                        tape_r := SND (SND (DECODE_TM_TAPE (nsnd n)))|>
End

(* Perform action an move to state *)
Definition UPDATE_ACT_S_TM_def:
  UPDATE_ACT_S_TM s act tm =
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
               tape_r := TL tm.tape_r |>
End

Theorem ODD_DIV_2_lem:
  ∀ y. ODD y ==> (y DIV 2 = (y-1) DIV 2)
Proof
  simp[ODD_EXISTS, PULL_EXISTS, ADD1, ADD_DIV_RWT]
QED

Theorem WRITE_0_HEAD_lem:
  ∀ tm s. (UPDATE_ACT_S_TM s Wr0 tm).tape_h = Z
Proof
  rpt strip_tac >> rw[UPDATE_ACT_S_TM_def]
QED


Theorem WRITE_1_HEAD_lem:
  ∀ tm s. (UPDATE_ACT_S_TM s Wr1 tm).tape_h = O
Proof
  rpt strip_tac >> rw[UPDATE_ACT_S_TM_def]
QED

Theorem ODD_TL_DECODE_lem:
  ∀ n. ODD n ==> (TL (DECODE n) = DECODE ((n-1) DIV 2))
Proof
  rpt strip_tac >> `EVEN 0` by EVAL_TAC >> `n ≠ 0` by metis_tac[EVEN_AND_ODD]>>
  rw[DECODE_def] >> Cases_on `DECODE n` >- `n=0` by fs[DECODE_EMPTY_lem] >>
  EVAL_TAC >> Cases_on `n` >- fs[] >> fs[DECODE_def] >> rfs[]
QED

Theorem EVEN_TL_DECODE_lem:
  ∀ n. ((EVEN n) ∧ (n > 0)) ==> (TL (DECODE n) = DECODE (n DIV 2))
Proof
  rpt strip_tac >> Cases_on `n` >- fs[]  >>
  rw[DECODE_def] >> metis_tac[EVEN_AND_ODD]
QED

Theorem ODD_MOD_TWO_lem:
  ∀n. (ODD n) ==> (n MOD 2 = 1)
Proof
  rpt strip_tac  >> fs[MOD_2] >> `~EVEN n` by metis_tac[EVEN_AND_ODD] >> rw[]
QED

Theorem containment_lem:
  ((OLEAST n. (nfst n,CELL_NUM (nsnd n)) ∈ FDOM p) = NONE) <=> (p = FEMPTY)
Proof
  rw[] >> eq_tac >> simp[] >> csimp[fmap_EXT] >>
  simp[EXTENSION,pairTheory.FORALL_PROD] >> strip_tac >>
  qx_gen_tac `a` >> qx_gen_tac `b` >>
  `∃c. b = CELL_NUM c` by metis_tac[CELL_NUM_def,theorem"cell_nchotomy"] >>
  rw[] >>
  pop_assum (qspec_then `a *, c` mp_tac) >> simp[]
QED


Theorem UPDATE_TAPE_ACT_STATE_TM_thm:
  ∀ tm.
    ((tm.state , tm.tape_h) ∈ FDOM tm.prog) ∧ tm.state <> 0 ==>
    (UPDATE_ACT_S_TM (FST (tm.prog ' (tm.state, tm.tape_h)))
                     (SND (tm.prog ' (tm.state, tm.tape_h)))
                     tm
       =
     UPDATE_TAPE tm)
Proof
  strip_tac >> fs[UPDATE_ACT_S_TM_def,UPDATE_TAPE_def]
QED

Theorem NUM_TO_ACT_TO_NUM[simp]:
  ((ACT_TO_NUM k) < 4) ==> (NUM_TO_ACT (ACT_TO_NUM k) = k)
Proof
  rw[NUM_TO_ACT_def,ACT_TO_NUM_def] >>
  `(ACT_TO_NUM k = 0) ∨ (ACT_TO_NUM k = 1) ∨(ACT_TO_NUM k = 2)∨
   (ACT_TO_NUM k = 3)` by simp[] >>rw[]>>
  EVAL_TAC >> Cases_on `k` >> rfs[ACT_TO_NUM_def] >> EVAL_TAC
QED
val _ = export_rewrites ["NUM_CELL_def"]

Theorem TM_PROG_P_TAPE_H[simp]:
  (tm with prog := p).tape_h = tm.tape_h
Proof
  fs[]
QED

Theorem TM_PROG_P_STATE[simp]:
  (tm with prog := p).state = tm.state
Proof
  fs[]
QED

Theorem UPDATE_TM_ARB_Q:
  (tm.state,tm.tape_h) ∈ FDOM p ∧ tm.state <> 0 ==>
   (UPDATE_ACT_S_TM (FST (p ' (tm.state,tm.tape_h)))
                    (SND (p ' (tm.state,tm.tape_h)))
                    (tm with prog := q) =
    (UPDATE_TAPE (tm with prog := p)) with prog := q)
Proof
  rw[UPDATE_TAPE_def,UPDATE_ACT_S_TM_def] >>
  Cases_on `SND (p ' (tm.state,tm.tape_h))` >> simp[]
QED

Theorem tm_with_prog:
  tm with prog := tm.prog = tm
Proof
  simp[theorem("TM_component_equality")]
QED

Theorem FST_DECODE_TM_TAPE[simp]:
  FST (DECODE_TM_TAPE tp) = DECODE (nfst tp)
Proof
  rw[DECODE_TM_TAPE_def]
QED

Theorem DECODE_EQ_NIL[simp]:
  (DECODE n = []) ⇔ (n = 0)
Proof
  metis_tac[DECODE_EMPTY_lem, DECODE_def]
QED

Theorem ODD_HD_DECODE:
  ODD n ==> (HD (DECODE n) = O)
Proof
  Cases_on `n` >> simp[DECODE_def]
QED

Theorem EVEN_HD_DECODE:
  EVEN n ∧ (n ≠ 0)  ==> (HD (DECODE n) = Z)
Proof
Cases_on `n` >> simp[DECODE_def] >> metis_tac[EVEN_AND_ODD,listTheory.HD]
QED

Theorem SND_SND_DECODE_TM_TAPE:
  SND (SND (DECODE_TM_TAPE (nsnd tmn))) = DECODE (nsnd (nsnd tmn) DIV 2)
Proof
rw[DECODE_TM_TAPE_def] >> `ODD (nsnd (nsnd tmn))` by metis_tac[EVEN_OR_ODD] >>
  rw[ODD_DIV_2_lem]
QED

Theorem SND_SND_DECODE_TM_TAPE_FULL[simp]:
  SND (SND (DECODE_TM_TAPE (t))) = DECODE (nsnd ( t) DIV 2)
Proof
  rw[DECODE_TM_TAPE_def] >> `ODD (nsnd (t))` by metis_tac[EVEN_OR_ODD] >>
  rw[ODD_DIV_2_lem]
QED

Theorem FST_SND_DECODE_TM_TAPE_FULL[simp]:
  ODD (nsnd (t)) ==> (FST (SND (DECODE_TM_TAPE (t))) = O)
Proof
  rw[DECODE_TM_TAPE_def] >> metis_tac[EVEN_AND_ODD]
QED

Theorem FST_SND_DECODE_TM_TAPE_EVEN_FULL[simp]:
  EVEN (nsnd (t)) ==> (FST (SND (DECODE_TM_TAPE (t))) = Z)
Proof
  rw[DECODE_TM_TAPE_def]
QED

Theorem MEMBER_CARD:
  a ∈ FDOM p ⇒ 0 < CARD (FDOM p)
Proof
  Induct_on `p` >> simp[]
QED

Theorem npair_lem:
  (∀n. P n) <=> (∀j k. P (j *, k))
Proof
  eq_tac >> simp[] >>
  rpt strip_tac >> `∃j k. j *, k = n` by metis_tac[npair_cases] >> rw[]
QED

Theorem NUM_TO_CELL_TO_NUM:
  ((c=0) ∨ (c=1)) ==> (NUM_CELL (CELL_NUM c) = c)
Proof
  strip_tac >> rw[NUM_CELL_def,CELL_NUM_def]
QED

Theorem FULL_ENCODE_TM_STATE[simp]:
  nfst (FULL_ENCODE_TM tm) = tm.state
Proof
  fs[FULL_ENCODE_TM_def]
QED

Theorem tri_mono[simp]:
  ∀x y. (tri x <= tri y) <=> (x <= y)
Proof
  Induct_on `y` >> simp[]
QED

Theorem CELL_NUM_LEM1:
  (∀n'. n' < n ⊗ c ⇒ (nfst n',CELL_NUM (nsnd n')) ∉ FDOM p) ∧
   (n,CELL_NUM c) ∈ FDOM p ==> (c=0) ∨ (c=1)
Proof
  spose_not_then strip_assume_tac >> Cases_on `CELL_NUM c`
  >- (`0<c` by simp[] >>
      metis_tac[nfst_npair,nsnd_npair,npair2_lt,CELL_NUM_def]) >>
  `1<c` by simp[] >> metis_tac[nfst_npair,nsnd_npair,npair2_lt,CELL_NUM_def]
QED

Theorem TM_ACT_LEM_1[simp]:
  ( (nsnd (nsnd (FULL_ENCODE_TM tm))) MOD 2) = NUM_CELL (tm.tape_h)
Proof
  simp[FULL_ENCODE_TM_def,ENCODE_TM_TAPE_def] >> rw[] >> Cases_on `tm.tape_h` >- fs[] >- EVAL_TAC
QED

val _ = add_rule {term_name = "FULL_ENCODE_TM",fixity = Closefix,
                  block_style = (AroundEachPhrase,(PP.CONSISTENT,0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "⟦",TM,TOK"⟧"]}

Theorem FULL_ENCODE_IGNORES_PROGS[simp]:
  ⟦tm with prog := p⟧ = ⟦tm⟧
Proof
simp[FULL_ENCODE_TM_def,ENCODE_TM_TAPE_def]
QED

Theorem NUM_CELL_INJ:
  (NUM_CELL a = NUM_CELL b) <=> (a = b)
Proof
eq_tac >- (Cases_on ` a` >> Cases_on `b` >> rw[] ) >- (rw[])
QED

Theorem ACT_TO_NUM_LESS_4:
  ACT_TO_NUM a < 4
Proof
Cases_on `a` >> EVAL_TAC
QED

Theorem TWO_TIMES_DIV_TWO_thm[simp]:
  2 *  n DIV 2 = n
Proof
  metis_tac[DECIDE “0 < 2”, MULT_DIV, MULT_COMM]
QED

Theorem TWO_TIMES_P_ONE_DIV_TWO_thm[simp]:
  (2 * n + 1) DIV 2 = n
Proof
  metis_tac[DECIDE “1 < 2”, DIV_MULT, MULT_COMM]
QED

Theorem ENCODE_CONS_DECODE_ENCODE_thm[simp]:
  ENCODE (h::DECODE (ENCODE t)) = ENCODE (h::t)
Proof
  fs[ENCODE_def,DECODE_def,ENCODE_DECODE_thm]
QED

Theorem NFST_ENCODE_TM_TAPE[simp]:
  nfst (ENCODE_TM_TAPE tm) = ENCODE tm.tape_l
Proof
rw[ENCODE_TM_TAPE_def]
QED

Theorem FST_SND_DECODE_TM_TAPE[simp]:
  FST (SND (DECODE_TM_TAPE (ENCODE_TM_TAPE tm))) = tm.tape_h
Proof
rw[DECODE_TM_TAPE_def,ENCODE_TM_TAPE_def] >> fs[EVEN_MULT,EVEN_ADD] >>
Cases_on `tm.tape_h` >> fs[]
QED

Theorem NSND_ENCODE_TM_TAPE_DIV2[simp]:
  (nsnd (ENCODE_TM_TAPE tm) DIV 2) = ENCODE tm.tape_r
Proof
rw[ENCODE_TM_TAPE_def]
QED

val _ = export_theory();
