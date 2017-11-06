
open HolKernel Parse boolLib bossLib finite_mapTheory;
open recfunsTheory;
open recursivefnsTheory;
open prnlistTheory;
open primrecfnsTheory;
open listTheory;
open arithmeticTheory;
open numpairTheory;
open pred_setTheory;
val _ = new_theory "turing_machine";

val _ = intLib.deprecate_int()


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

val _ = Datatype `state = <| n : num |>`;

val _ = Datatype `TM = <| state : state;
                  prog : ((state # cell) |->  (state # action));
                  tape_l : cell list;
                  tape_h : cell;
                  tape_r : cell list
                       |>`;

val concatWith_def = Define`
  (concatWith sep [] = []) /\
  (concatWith sep [x] = x) /\
  (concatWith sep (x::y::rest) = x ++ sep ++ concatWith sep (y::rest))`;

EVAL ``concatWith [0n] [[1;2;3;4]; [4;5]; [10;11;13]]``;

EVAL ``GENLIST (K O) 24 ``;

val INITIAL_TAPE_TM_def = Define `(INITIAL_TAPE_TM tm [] = tm) ∧
  (INITIAL_TAPE_TM tm (h::t) = tm with <|tape_l := [] ; tape_h := h ; tape_r := t|>)`;

val INITIAL_TM_def = Define`
INITIAL_TM p args =
INITIAL_TAPE_TM <|state := <|n:=0|>;  prog := p;tape_l := [];tape_h := Z;tape_r := []|> (concatWith [Z] (MAP (GENLIST (K O)) args ))`;

EVAL ``INITIAL_TM FEMPTY [2;3]``;

val UPDATE_STATE_TIME = Define `UPDATE_STATE_TIME tm =
  if(((tm.state),(tm.tape_h)) IN FDOM tm.prog)
  then tm with
    <|state := (FST (tm.prog ' ((tm.state) ,(tm.tape_h)) )) |>
    else (tm)
                               `;

val UPDATE_TAPE_def = Define `UPDATE_TAPE tm =
  if (((tm.state),(tm.tape_h)) IN FDOM tm.prog)
  then let tm' = tm with
    <|    state := (FST (tm.prog ' ((tm.state) ,(tm.tape_h)) )) |> in
      case (SND (tm.prog ' ((tm.state) ,(tm.tape_h)) )) of
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
  else (tm)
                                  `;


val _ = overload_on("RUN",``FUNPOW UPDATE_TAPE``);


val DECODE_def = tDefine "DECODE" `
(DECODE 0 = []) ∧
(DECODE n = if (ODD n)
            then [O] ++ (DECODE ((n-1) DIV 2))
            else [Z] ++ (DECODE (n DIV 2)))`
(WF_REL_TAC `$<` >> rw[] >> intLib.ARITH_TAC)


val ENCODE_def = Define `(ENCODE [] = 0) ∧
(ENCODE (h::t) = case h of
                     Z => 0 + (2 * (ENCODE t))
                   | O => 1 + (2 * (ENCODE t))
                   | _ => 0)`;


EVAL `` (DECODE (ENCODE [O;O;Z;O;Z;O;Z;O;O;O]) )``;

EVAL `` ENCODE (DECODE 99999999999)``;

EVAL ``ENCODE [O;Z;Z;Z;Z]``;

(* Change TO simpler def of DECODE*)

(* Lemmas for ENCODE/DECODE*)

val SUC_CANCEL_lem = Q.store_thm(
        "SUC_CANCEL_lem",
`! n m. (SUC n = SUC m) ==> (m = n)`,
Induct_on `n` >- fs[]
          >> Induct_on `m`
>- fs[]
>- fs[]
    );

val DIV_3_lem = Q.store_thm(
        "DIV_3_lem",
    `∀ n.(n DIV 3 = 0) ==> (n<3) `,
    Induct_on `n` >- fs[] >> strip_tac
              >> `SUC 0 DIV 3 = 0` by fs[]
              >> `SUC 1 DIV 3 = 0` by fs[]
              >> Cases_on `n`
              >- fs[]
              >> Cases_on `n'`
                >- fs[]
                >> Cases_on `n`
                  >- fs[]
                  >> `n'>= 0` by fs[]
                  >> `SUC (SUC (SUC (SUC n'))) >= 3` by fs[]
                  >> `~(SUC (SUC (SUC (SUC n'))) < 3)` by fs[]
                  >> fs[]
                  >> `SUC (SUC (SUC (SUC n'))) = n' + 4` by fs[]
                  >> `SUC (SUC (SUC n')) = n' + 3` by fs[]
                  >> `n' + 3 DIV 3 ≠ 0` by fs[]
                  >> `(n' + 4 DIV 3 = 0) <=> F` by fs[]
                  >> rw[]
                  >> `SUC (SUC (SUC (SUC n'))) DIV 3 <= n' + 4 DIV 3` by fs[]
                  >> `(SUC (SUC (SUC (SUC n')))) DIV 3 = (n' + 4) DIV 3` by prove_tac[]
                  >> `(n'+4) DIV 3 = 0` by fs[]
                  >> `n'+4 = (n'+4)` by fs[]
                  >> `n'>=0` by fs[]
                  >> `4 <= n'+4` by fs[]
                  >> `0<3` by fs[]
                  >> `4 DIV 3 = 1` by fs[]
                  >> `4 DIV 3 <= (n' +4) DIV 3` by metis_tac[DIV_LE_MONOTONE]
                  >> `1 <=0` by fs[]
                  >> fs[]
    );


val MOD_3_lem = Q.store_thm (
        "MOD_3_lem",
`∀ n. (n MOD 3 = 0) ∨ (n MOD 3 = 1) ∨ (n MOD 3 = 2)`,
Induct_on `n` >- fs[] >> rw[] >> `SUC n MOD 3 < 3` by fs[] >> `1 < SUC n MOD 3` by fs[]
          >> `2 <=  SUC n MOD 3` by fs[]
          >> `0<3` by fs[] >> `SUC n MOD 3 <= SUC n` by metis_tac[MOD_LESS_EQ]
          >> `SUC n MOD 3 < 2 + 1` by fs[]
          >> `SUC n MOD 3 <= 2` by metis_tac[LE_LT1]
          >> fs[]
    );


val MOD_DIV_3_lem = Q.store_thm(
        "MOD_DIV_3_lem",
`∀ n. ((n DIV 3 = 0) ∧ (n MOD 3 = 0)) ==> (n = 0)`,
Induct_on `n` >- fs[]
          >> rw[] >> `SUC n = n+1` by fs[] >> CCONTR_TAC >> fs[] >> rw[]
          >> `SUC n DIV 3 = SUC n MOD 3` by fs[]
          >> `SUC n < 3` by metis_tac[DIV_3_lem]
          >> `SUC n = 0` by fs[]
          >> fs[]
    );


(* Examples *)

EVAL ``LENGTH (TL [h])``;


EVAL ``2 MOD 3``;


(*
val ENCODE_DECODE_lem_Z = Q.store_thm(
    "ENCODE_DECODE_lem1[simp]",
    `!n. ENCODE_tern (2*(3**(LENGTH n)) + DECODE n) = Z::n`,
    strip_tac >> completeInduct_on `LENGTH n` >> strip_tac
    >> strip_tac >> Cases_on `LENGTH n` >- fs[] >> EVAL_TAC >>
    >> strip_tac >> strip_tac
    );
*)

val ENCODE_DECODE_thm = store_thm(
    "ENCODE_DECODE_thm",
    ``!n. ENCODE (DECODE n) = n``,
    completeInduct_on `n` >> Cases_on `n` >- EVAL_TAC >> rw[DECODE_def] >- (rw[ENCODE_def]
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
 );

val DECODE_EMPTY_lem = Q.store_thm (
        "DECODE_EMPTY_lem",
`∀ n. (DECODE n = []) ==> (n=0)`,
    Induct_on `n` >- EVAL_TAC >> fs[] >> rw[DECODE_def]  );

(*
Not a theorem

val DECODE_ENCODE_thm = store_thm(
    "DECODE_ENCODE_thm",
    `!l. DECODE (ENCODE l) = l`,
    completeInduct_on `ENCODE l` >> rpt  strip_tac >>  Cases_on `DECODE (ENCODE l)` >-
        (`DECODE 0 = []` by fs[DECODE_def]
      >> Cases_on `l` >- fs[] >> fs[] >> `ENCODE (h::t) = 0` by fs[DECODE_EMPTY_lem]
      >> rw[])
      >> rw[] >> Cases_on `h` >- ( rw[DECODE_def,ENCODE_def] )

    );
*)

EVAL ``7 DIV 3``;

val ENCODE_TM_TAPE_def = Define `ENCODE_TM_TAPE tm =
       if tm.tape_h = Z then
           ((ENCODE tm.tape_l) *,  (2 * (ENCODE tm.tape_r)))
       else
           ((ENCODE tm.tape_l) *, ( (2 * (ENCODE tm.tape_r)) + 1 ))`;

val DECODE_TM_TAPE_def = Define `DECODE_TM_TAPE n =
       if EVEN (nsnd n) then
           (DECODE (nfst n), Z , DECODE ( (nsnd n) DIV 2))
       else
           (DECODE (nfst n), O , DECODE ( ((nsnd n) - 1) DIV 2))`;

(* Halted definition and TM examples *)


val HALTED_def = Define `HALTED tm = ~(((tm.state),(tm.tape_h)) IN FDOM tm.prog)`;

val st_def= Define`st n : state = <| n := n  |>`;
val _ = add_numeral_form(#"s", SOME "st");


(* EVAL ``(RUN 3
   <| state := 0;
      prog := FEMPTY |++ [((0,Z),(0,R)); ((0,O),(0,R)); ((1,O),(1,Wr0))] ;
      tape_l := [];
      tape_h := Z;
      tape_r := [Z]
     |>
      [Z])``; *)


(* unary addition machine *)
                          (*
EVAL ``(RUN 10
   <| state := 0;
        prog := FEMPTY |++ [((0,Z),(1,Wr1)); ((0,O),(0,R));
                            ((1,Z),(2,L)); ((1,O),(1,R));
                            ((2,O),(3,Wr0)) ] ;
      tape_l := [];
      tape_h := Z;
      tape_r := [] |>
      [O;O;O;Z;O;O])``;


type_of ``(SET_TO_LIST (FDOM (<| state := 0;
       prog := FEMPTY |++ [((0,Z),(0,R)); ((0,O),(1,Wr0)); ((1,Z),(1,R)); ((1,O),(2,Wr1)) ] ;
       tape_l := [];
       tape_h := Z;
       tape_r := [Z] |>.prog)))
       ``;
*)

(*

The set of Partial Recursive Functions is identical to the set of
Turing Machines computable functions

Total Recursive Function correspond to Turing Machine computable functions that always halt

One can enumerate the Valid Turing Machines (by enumerating programs)

*)

val NUM_CELL_def = Define `(NUM_CELL Z = 0:num) ∧
  (NUM_CELL O = 1:num) `;

val CELL_NUM_def = Define `(CELL_NUM 0n = Z) ∧
  (CELL_NUM 1 = O) `;

val ACT_TO_NUM_def = Define `(ACT_TO_NUM Wr0 = 0:num) ∧
  (ACT_TO_NUM Wr1 = 1:num) ∧
  (ACT_TO_NUM L   = 2:num) ∧
  (ACT_TO_NUM R   = 3:num) `;

val NUM_TO_ACT_def = Define `(NUM_TO_ACT 0n = Wr0 ) ∧
  (NUM_TO_ACT 1 = Wr1) ∧
  (NUM_TO_ACT 2 = L) ∧
  (NUM_TO_ACT 3 = R) `;

EVAL ``ACT_TO_NUM (NUM_TO_ACT 2)``;


(* Definition of a Turing complete function, not working atm *)

(*
val TURING_COMPLETE_def = Define `TURING_COMPLETE f = ∃ tm. ∀ n. ∃ t. DECODE_TM_TAPE (RUN t tm (ENCODE n)) = f `
*)

(*
Previous idea, using enumeration over program set
*)

EVAL ``HD (ncons_inv 88)``;

EVAL ``HD (TL (ncons_inv 88))``;

EVAL `` ncons (HD (ncons_inv 88)) (HD (TL (ncons_inv 88)))``;

(*
Previous diea of enumerating programs

val NCONS_INVERSE_def = Define `(ncons_inv 1 = []) ∧ (ncons_inv c = [nfst (c-1) ; nsnd (c-1)] )`;

EVAL `` MIN_SET {1:num;2:num;3:num;5:num;10:num}``;

val LEAST_IN_SET_def = Define `
LEAST_IN_SET s = let nconsset = { ncons (STATE_TO_NUM (FST c)) (NUM_CELL (SND c)) | c IN s } in
  ncons_inv (MIN_SET nconsset) `;

val LEAST_SET_TO_LIST_def = Define `
LEAST_SET_TO_LIST s =
if FINITE s then
  if s={} then []
  else let k = (NUM_TO_STATE (HD (LEAST_IN_SET s)), CELL_NUM (HD (TL (LEAST_IN_SET s))))  in
    k :: LEAST_SET_TO_LIST (s DELETE k)
else ARB`;

val tcons_def = Define `
tcons a b tm = (ncons (STATE_TO_NUM a) (NUM_CELL b)) *,
                                                     (ncons (STATE_TO_NUM (FST (FAPPLY tm.prog ((a),(b)) ))) (NUM_ACT (SND (FAPPLY tm.prog ((a),(b)) )))) + 1`;

val tlist_of = Define `
(tlist_of [] tm = 0) ∧
(tlist_of (h::t) tm = ncons (tcons (FST h) (SND h) tm)  (tlist_of t tm))`;

val TURING_MACHINE_P_ENCODING_def = Define `
TURING_MACHINE_P_ENCODING tm = tlist_of (SET_TO_LIST (FDOM tm.prog)) tm`;

val FULL_ENCODE_TM_with_P_def = Define `FULL_ENCODE_TM_with_P tm =
nlist_of [TURING_MACHINE_P_ENCODING tm; STATE_TO_NUM tm.state ; DECODE_TM_TAPE tm] `;


*)

(*
Idea is, for each instruction in the program, which is an (a,b,c,d)
val tcons_def = Define `
(tcons (a,b,c,d) = (ncons a (NUM_CELL b)) *, (ncons c (NUM_ACT d)) + 1)`;
*)

val STATE_TO_NUM_def = Define `STATE_TO_NUM a = a.n`;

val NUM_TO_STATE_def = Define `NUM_TO_STATE n = <| n:=n |>`;


EVAL ``STATE_TO_NUM (NUM_TO_STATE 10)``;

val FULL_ENCODE_TM_def = Define `FULL_ENCODE_TM tm =
 STATE_TO_NUM tm.state *, ENCODE_TM_TAPE tm `;


val FULL_DECODE_TM_def = Define `FULL_DECODE_TM n =
<|state:=  NUM_TO_STATE (nfst n);  tape_l := FST (DECODE_TM_TAPE (nsnd n));
tape_h := FST (SND (DECODE_TM_TAPE (nsnd n)));
tape_r := SND (SND (DECODE_TM_TAPE (nsnd n)))|> `;





(* EVAL and type checks *)

(*
num_step tm (takes tm as number and does step, purely arithmetic)
*)

EVAL ``FULL_ENCODE_TM <| state := 0;
prog := FEMPTY |++ [((0,Z),(0,R)); ((0,Z),(1,Wr0)); ((1,Z),(1,R)); ((1,Z),(2,Wr0)) ] ;
tape_l := [];
tape_h := Z;
tape_r := [Z;O;O] |>``;

EVAL `` FULL_DECODE_TM 4185``;

type_of ``recfn f 1``;



(* Perform action an move to state *)
val UPDATE_ACT_S_TM_def = Define `UPDATE_ACT_S_TM s act tm =
           let tm' = tm with
                        <|  state := s |> in
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

(* EVAL checks *)

EVAL ``FULL_ENCODE_TM (UPDATE_ACT_S_TM 0 Wr1 <| state := 0;
               prog := FEMPTY |++ [((0,Z),(0,R)); ((0,Z),(1,Wr0)); ((1,Z),(1,R)); ((1,Z),(2,Wr0)) ] ;
               tape_l := [];
               tape_h := Z;
               tape_r := [Z;O;O] |>)``;



EVAL `` 0 *, nsnd 10``;

val ODD_DIV_2_lem = Q.store_thm ("ODD_DIV_2_lem",
`∀ y. ODD y ==> (y DIV 2 = (y-1) DIV 2)`,
Induct_on `y` >- EVAL_TAC >> rw[] >> `SUC y = y+1` by fs[] >> rw[] >>
`~(ODD y)` by fs[ODD] >>
`1 DIV 2 = 0` by EVAL_TAC >> `0<2` by fs[] >> `EVEN y` by metis_tac[EVEN_OR_ODD] >>
`y MOD 2 = 0` by metis_tac[EVEN_MOD2] >>
`(y+1) DIV 2 = (y DIV 2) + (1 DIV 2)` by fs[ADD_DIV_RWT] >> rw[]
);

val WRITE_0_HEAD_lem = Q.store_thm("WRITE_0_HEAD_lem",
`∀ tm s. (UPDATE_ACT_S_TM s Wr0 tm).tape_h = Z`,
rpt strip_tac >> rw[UPDATE_ACT_S_TM_def] );


val WRITE_1_HEAD_lem = Q.store_thm("WRITE_1_HEAD_lem",
`∀ tm s. (UPDATE_ACT_S_TM s Wr1 tm).tape_h = O`,
rpt strip_tac >> rw[UPDATE_ACT_S_TM_def] );


val TMN_Z_MOD_1_lem = Q.store_thm ("TMN_Z_MOD_1_lem",
`∀ tmn. ((nfst (nsnd tmn) MOD 2 = 1) ∧ (HD (FST (DECODE_TM_TAPE (nsnd tmn))) = Z)) <=> F`,
strip_tac >> rw[]  >> `~(nfst (nsnd tmn) MOD 2 = 0)` by fs[] >>
`~EVEN (nfst (nsnd tmn))` by metis_tac[EVEN_MOD2] >>
`ODD (nfst (nsnd tmn))` by metis_tac[EVEN_OR_ODD] >>
`EVEN 0` by fs[] >>
`~((nfst (nsnd tmn)) = 0)` by metis_tac[EVEN_OR_ODD] >>
Cases_on `nfst (nsnd tmn)` >- fs[] >> 
`DECODE (SUC n) = [O] ++ (DECODE (((SUC n) - 1) DIV 2))` by fs[DECODE_def] >>
`TL (DECODE (SUC n)) = (DECODE ((SUC n -1) DIV 2))` by fs[DECODE_def] >>
rw[] >> rw[DECODE_TM_TAPE_def] );


val ODD_TL_DECODE_lem = Q.store_thm ("ODD_TL_DECODE_lem",
`∀ n. (ODD n) ==> (TL (DECODE n) = DECODE ((n-1) DIV 2))`,
rpt strip_tac >> `EVEN 0` by EVAL_TAC >> `~(n = 0)` by metis_tac[EVEN_AND_ODD]>>
rw[DECODE_def] >> Cases_on `DECODE n` >- `n=0` by fs[DECODE_EMPTY_lem] >>
EVAL_TAC >> Cases_on `n` >- fs[] >> fs[DECODE_def] >> rfs[] );


val EVEN_TL_DECODE_lem = Q.store_thm ("EVEN_TL_DECODE_lem",
`∀ n. ((EVEN n) ∧ (n > 0)) ==> (TL (DECODE n) = DECODE (n DIV 2))`,
rpt strip_tac >> Cases_on `n` >- fs[]  >>
    rw[DECODE_def] >> metis_tac[EVEN_AND_ODD] );


val EVEN_ENCODE_Z_DECODE_lem = Q.store_thm ("EVEN_ENCODE_Z_DECODE_lem",
`∀ n. (EVEN n) ==> (n = ENCODE (Z::DECODE (n DIV 2)))`,
rpt strip_tac >> Cases_on `n` >- EVAL_TAC >> rfs[DECODE_def,ENCODE_def] >>
 rw[ENCODE_DECODE_thm] >> `(SUC n') MOD 2 = 0` by metis_tac[EVEN_MOD2] >>
`2*(SUC n' DIV 2) = SUC n'` by fs[MULT_EQ_DIV] >> rw[] );

val ODD_ENCODE_O_DECODE_lem = Q.store_thm ("EVEN_ENCODE_Z_DECODE_lem",
`∀ n. (ODD n) ==> (n = ENCODE (O::DECODE ((n-1) DIV 2)))`,
rpt strip_tac >> Cases_on `n` >- fs[] >> rfs[DECODE_def,ENCODE_def] >>
    rw[ENCODE_DECODE_thm] >> `~(ODD n')` by fs[ODD] >> `EVEN n'` by metis_tac[EVEN_OR_ODD] >>
`n' MOD 2 = 0` by metis_tac[EVEN_MOD2] >>
`2*( n' DIV 2) =  n'` by fs[MULT_EQ_DIV] >> rw[] );


val ODD_MINUS_1_lem = Q.store_thm ("ODD_MINUS_1_lem",
`∀ n. (ODD n) ==> (~ODD (n-1))`,
rpt strip_tac >> Cases_on `n` >- fs[] >> `SUC n' - 1 = n'` by fs[SUC_SUB1] >>
`ODD n'` by fs[] >> fs[ODD] )


val ONE_LE_ODD_lem = Q.store_thm ("ONE_LE_ODD_lem",
`∀n. (ODD n) ==> (1 <= n)`,
rpt strip_tac >> Cases_on `n` >-  fs[] >> `SUC n' = 1+n'` by fs[SUC_ONE_ADD] >>
rw[])


val ODD_MOD_TWO_lem = Q.store_thm ("ODD_MOD_TWO_lem",
`∀n. (ODD n) ==> (n MOD 2 = 1)`,
rpt strip_tac  >> fs[MOD_2] >> `~(EVEN n)` by metis_tac[EVEN_AND_ODD] >> rw[] );


val oleast_eq_none = Q.store_thm("oleast_eq_none",
`($OLEAST P = NONE) <=> (∀n. ¬(P n)) `,
DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >> simp[] >> metis_tac[]);

val containment_lem = Q.store_thm("containment_lem",
`((OLEAST n. (NUM_TO_STATE (nfst n),CELL_NUM (nsnd n)) ∈ FDOM p) =
  NONE) <=> (p = FEMPTY)`,
rw[oleast_eq_none] >> eq_tac >> simp[] >> csimp[fmap_EXT] >>
simp[EXTENSION,pairTheory.FORALL_PROD,NUM_TO_STATE_def] >> strip_tac >>
qx_gen_tac `a` >> qx_gen_tac `b` >>
`∃n. a= <| n := n|>  ` by metis_tac[theorem"state_literal_nchotomy"] >>
`∃c. b = CELL_NUM c` by metis_tac[CELL_NUM_def,theorem"cell_nchotomy"] >> rw[] >>
pop_assum (qspec_then `n *, c` mp_tac) >> simp[]);


val UPDATE_TAPE_ACT_STATE_TM_thm = Q.store_thm("UPDATE_TAPE_ACT_STATE_TM_thm",
`∀ tm.(((tm.state) ,(tm.tape_h)) ∈ FDOM tm.prog) ==> (UPDATE_ACT_S_TM (FST (tm.prog ' ((tm.state) ,(tm.tape_h)) ))
  (SND (tm.prog ' ((tm.state) ,(tm.tape_h)) )) tm = UPDATE_TAPE tm)`,
strip_tac >> fs[UPDATE_ACT_S_TM_def,UPDATE_TAPE_def]  );

val NUM_TO_ACT_TO_NUM = Q.store_thm("NUM_TO_ACT_TO_NUM[simp]",
`((ACT_TO_NUM k) < 4) ==> (NUM_TO_ACT (ACT_TO_NUM k) = k)`,
rw[NUM_TO_ACT_def,ACT_TO_NUM_def] >>
`(ACT_TO_NUM k = 0) ∨ (ACT_TO_NUM k = 1) ∨(ACT_TO_NUM k = 2)∨(ACT_TO_NUM k = 3)` by simp[] >>rw[]>>
EVAL_TAC >> Cases_on `k` >> rfs[ACT_TO_NUM_def] >> EVAL_TAC);

val _ = export_rewrites ["NUM_CELL_def"]
val TM_PROG_P_TAPE_H = Q.store_thm("TM_PROG_P_TAPE_H[simp]",
`(tm with prog := p).tape_h = tm.tape_h`,
fs[]);

val TM_PROG_P_STATE = Q.store_thm("TM_PROG_P_STATE[simp]",
`(tm with prog := p).state = tm.state`,
fs[]);

val UPDATE_TM_ARB_Q = Q.store_thm("UPDATE_TM_ARB_Q",
`((tm.state,tm.tape_h) ∈ FDOM p) ==> ((UPDATE_ACT_S_TM (FST (p ' (tm.state,tm.tape_h))) (SND (p ' (tm.state,tm.tape_h))) (tm with prog := q)) = ((UPDATE_TAPE (tm with prog := p)) with prog := q))`,
rw[UPDATE_TAPE_def,UPDATE_ACT_S_TM_def] >>
Cases_on `SND (p ' (tm.state,tm.tape_h))` >> simp[] )

val NUM_TO_STATE_TO_NUM = Q.store_thm ("NUM_TO_STATE_TO_NUM[simp]",
`NUM_TO_STATE (STATE_TO_NUM k) = k`,
fs[STATE_TO_NUM_def,NUM_TO_STATE_def,theorem("state_component_equality")]  );

val tm_with_prog = Q.store_thm("tm_with_prog",`tm with prog := tm.prog = tm`,simp[theorem("TM_component_equality")])



val _ = export_theory();






