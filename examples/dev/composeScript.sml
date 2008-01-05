
(*****************************************************************************)
(* Definitions and theorem to support composition of handshaking components  *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)
(******************************************************************************
* Load theories
* (commented out for compilation)
******************************************************************************)
(* 
quietdec := true;
(* show_assums := true; *)
map load  ["metisLib","TotalDefn","jrhUtils"];
open arithmeticTheory metisLib TotalDefn jrhUtils;
quietdec := false;
*) 

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)

open HolKernel Parse boolLib bossLib metisLib arithmeticTheory; 

(******************************************************************************
* Open theories
******************************************************************************)


(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Function used with PAT_ASSUM:   PAT_ASSUM <term> kill                     *)
(*****************************************************************************)

val kill = (fn theorem => K ALL_TAC theorem);
val PROVE_TAC = METIS_TAC;


(*****************************************************************************)
(* Start new theory "compose"                                                *)
(*****************************************************************************)

val _ = new_theory "compose";

(*****************************************************************************)
(* Definitions                                                               *)
(*****************************************************************************)

(*
HOLDF (t1,t2) i is true iff i:num->bool is F in the interval [t1..t2)
*)

val HOLDF_def =
 Define
  `HOLDF (t1,t2) i = !t. ((t1 <= t) /\ (t < t2)) ==> ~(i t)`;

(*
POSEDGE i t is true iff t>0 and i(t-1) = F and i t = T
*)

val POSEDGE_def =
 Define
  `POSEDGE i t = if t=0 then F else (~i(t-1) /\ i t)`;

(*
           load       inp
            |          |
            |          |
         |----------------|
         |                |
         |       f        |
         |                |
         |----------------|
            |          |
            |          |
           done       out

The load and done lines are boolean controls; inp and out carry data.

The output done being true indicates the device is available (i.e. no
computation is in progress). If done is true at time t and there is a
posedge on load at the next cycle (i.e. POSEDGE load (t+1)), then inp
is sampled at t+1 and at some strictly later time t' the value
f(inp(t+1)) is output at out. 

During the computation -- i.e. during [t+1..t') -- done is F, but at
time t' it goes to T (so POSEDGE done t').

In addition, if done is T then it stays true if there is no POSEDGE on
load.
*)

val SAFE_DEV_def =
 Define
  `SAFE_DEV f (load,inp,done,out) =
    (!t. done t /\ POSEDGE load (t+1) 
         ==> 
         ?t'. t' > t+1            /\ 
              HOLDF (t+1,t') done /\ 
              done t'             /\ 
              (out t' = f(inp(t+1))))
    /\
    (!t. done t /\ ~(POSEDGE load (t+1)) ==> done(t+1))`;

(*****************************************************************************)
(* To show that handshaking devices exist, we define below an implementation *)
(* ATM of a handshaking device that takes one cycle to compute               *)
(* a given function f. It satisfies:                                         *)
(*                                                                           *)
(*  |- ATM f (load,inp,done,out)                                             *)
(*     ==>                                                                   *)
(*     SAFE_DEV f (load,inp,done,out)                                        *)
(*                                                                           *)
(* which is proved as theorem ATM below.                                     *)
(*****************************************************************************)

(*****************************************************************************)
(* Some basic components used to implement handshaking devices.              *)
(*****************************************************************************)

(*
Combinational (i.e. zero-delay) conponent with input inp and output out
which computes a function f.
*)
val COMB_def =
 Define `COMB f (inp,out) = !t. out t = f(inp t)`;   

(*
Component that constantly outputs T at out.
*)
val TRUE_def =
 Define `TRUE out = !t. out t = T`;

(*
Component that constantly outputs F at out.
*)
val TRUE_def =
 Define `FALSE out = !t. out t = F`;

(*
Combinational AND-gate, with inputs in1, in2 and output out.
*)
val AND_def =
 Define `AND(in1,in2,out) = !t. out t = (in1 t /\ in2 t)`;

(*
Combinational OR-gate, with inputs in1, in2 and output out.
*)
val OR_def =
 Define `OR(in1,in2,out) = !t. out t = (in1 t \/ in2 t)`;

(*
Combinational NOT-gate (i.e. inverter), with inputs inp and output out.
*)
val NOT_def =
 Define `NOT(inp,out) = !t. out t = ~(inp t)`;

(* 
Combinational multiplexer, with select input sel that connects input
in1 to output out if T and connects input in2 to output out if F.
*)
val MUX_def =
 Define 
  `MUX(sel,in1,in2,out) = !t. out t = if sel t then in1 t else in2 t`

(*
Polymorphic unit delay component (i.e. a register):
*)
val DEL_def =
 Define `DEL(inp,out) = !t. out(t+1) = inp t`;

(*
Boolean unit delay component that initialises into state T
*)
val DELT_def =
 Define `DELT(inp,out) = (out 0 = T) /\ !t. out(t+1) = inp t`;

(*
Boolean unit delay component that initialises into state F
*)
val DELF_def =
 Define `DELF(inp,out) = (out 0 = F) /\ !t. out(t+1) = inp t`;

(*****************************************************************************)
(* Now some implementations built using the basic components,                *)
(* starting with a component to compute POSEDGE.                             *)
(*****************************************************************************)

(*
      inp
       |
       |--------|
       |        |
   |-------|    |
   | DELT  |    |
   |-------|    |
       |        |
    c0 |        |
       |        |
    |-----|     |
    | NOT |     | 
    |-----|     |
       |        |
    c1 |        |
       |        |
    |--------------|
    |      AND     |
    |--------------|
           |
           |
          out

POSEDGE_IMP implements POSEDGE in the sense that 

 |- POSEDGE_IMP(inp,out) ==> !t. out(t+1) = POSEDGE inp (t+1)

which is proved as theorem POSEDGE_IMPL below.
*)

val POSEDGE_IMP_def =
 Define
  `POSEDGE_IMP(inp,out) =
     ?c0 c1. DELT(inp,c0) /\ NOT(c0,c1) /\ AND(c1,inp,out)`;

(*****************************************************************************)
(* Implementation of an atomic handshaking device.                           *)
(*****************************************************************************)

(* 
        
        load            inp
         |               |
         |               |
  |-------------|   |----------|
  | POSEDGE_IMP |   |  COMB f  |
  |-------------|   |----------|
         |               |
      c0 |            c1 |
         |               |
      |-----|       |----------|
      | NOT |       |   DEL    |
      |-----|       |----------|
         |               |
         |               |
         |               |
        done            out

Implementation of a handshaking device that takes one cycle
to compute a given function f. The implementation satisfies:

 |- ATM f (load,inp,done,out)
    ==>
    SAFE_DEV f (load,inp,done,out)

which is proved as theorem ATM below.
*)

val ATM_def = 
 Define
  `ATM f (load,inp,done,out) =
    ?c0 c1. POSEDGE_IMP(load,c0) /\ 
            NOT(c0,done)         /\
            COMB f (inp,c1)      /\ 
            DEL(c1,out)`;

(*****************************************************************************)
(* Next we define the serial composition of two handskaking devices.         *)
(*****************************************************************************)

(*
                          Load     inp
                           |        |
                           |        |
                           |        |
    |-----------------|    |        |
    |                 |    |        |
    |              |-----| |        |
    |              | NOT | |        |
    |              |-----| |        |
    |                 |    |        |
    |          not_c2 |    |        |
    |                 |    |        |
    |              |----------|     |
    |              |    OR    |     |
    |              |----------|     |
    |                    |          |
    |                 c0 |          |
    |                    |          |
    |                 |----------------|
    |                 |                |
    |                 |       f        |
    |                 |                |
    |                 |----------------|
    |                    |          |
    |                 c1 |    data  |
    |                    |          |
    |     |--------------|          |
    |     |              |          |
    |     |              |          |
    |     |           |----------------|
    |     |           |                |
    |     |           |       g        |
    |     |           |                |
    |     |           |----------------|
    |     |              |          |
    |     |           c2 |          |
    |     |              |          |
    |---- | -------------|          |
          |              |          |
          |---------|    |          |
                    |    |          |
                 |----------|       |
                 |   AND    |       |
                 |----------|       |
                       |            |
                       |            |
                       |            |
                      done         out

Sequential composition of handshaking devices.  The feedback c2 is to
disable any posedges on load whilst SAFE_DEV g is still computing 
(this prevents any pipelining). The correctness of the composition
is given by:

 |- SEQ (SAFE_DEV f) (SAFE_DEV g) (load,inp,done,out)
    ==>
    SAFE_DEV (g o f) (load,inp,done,out)

which is proved as theorem SEQ below.
*)

(* 
Sequential composition of devices d1 and d2 
*)
val SEQ_def =
 Define
  `SEQ d1 d2  (load,inp,done,out) =
    ?not_c2 c0 c1 c2 data. 
     NOT(c2,not_c2)     /\
     OR(not_c2,load,c0) /\
     d1(c0,inp,c1,data) /\
     d2(c1,data,c2,out) /\
     AND(c1,c2,done)`;


(*****************************************************************************)
(* Data flip-flop                                                            *)
(*****************************************************************************)
val DFF_def = 
 Define 
  `DFF (d,sel,q) = 
    !t. q (t+1) = if POSEDGE sel (t+1) then d (t+1) else q t`;


(*****************************************************************************)
(* The parallel composition                                                  *)
(*****************************************************************************)

val PAR_def = Define `PAR f g (load,inp,done,out) =
         ?c0 c1 start done' done'' data' data'' out' out''.
           POSEDGE_IMP(load,c0) /\ DEL(done,c1) /\
           AND (c0,c1,start) /\
           f (start,inp,done',data') /\ g (start,inp,done'',data'') /\
           DFF (data',done',out') /\ DFF (data'',done'',out'') /\
           AND (done',done'',done) /\
           (out = (\t. (out' t, out'' t)))`;


(*
                   load               done
                    |         |--------------------| 
                    |         |                    |
                    |         |                    |
           |-------------| |-----|                 |
           | POSEDGE_IMP | | DEL |                 |
           |-------------| |-----|                 |
                    |         |                    |
                 c0 |         | c1                 |
                    |         |                    |
                  |-------------|                  |
                  |     AND     |                  |
                  |-------------|                  | 
                          |                        |
                          | start                  |
          inp             |              inp       |
           |          |--------|          |        |
           |          |        |          |        |
           |          |        |          |        |
         |--------------|    |--------------|      |
         |      f       |    |      g       |      |
         |--------------|    |--------------|      |
           |          |        |          |        |
     data' |   done'  |        | done''   | data'' |
           |          |        |          |        | 
         |--------|   |        |   |--------|      |
         | d      |   |        |   |      d |      |
         | q  sel |---|        |---| sel  q |      |
         |--------|   |        |   |--------|      |
           |          |        |          |        |
           |        |------------|        |        |
           |        |    AND     |        |        |
          out'      |------------|       out''     |
                          |                        |
                          |------------------------|
                          |
                        done
*)


(*****************************************************************************)
(* The conditional                                                           *)
(*****************************************************************************)
val ITE_def = 
   Define `ITE e f g (load,inp,done,out) =
      ?c0 c1 c2 start start' done_e data_e q not_e 
       data_f data_g sel done_f done_g start_f start_g.
        POSEDGE_IMP(load,c0) /\
        DEL(done,c1) /\ AND(c0,c1,start) /\
        e(start,inp,done_e,data_e) /\
        POSEDGE_IMP(done_e,start') /\
        DFF(data_e,done_e,sel) /\
        DFF(inp,start,q) /\
        AND(start',data_e,start_f) /\ 
        NOT(data_e,not_e) /\ AND(start',not_e,start_g) /\
        f(start_f,q,done_f,data_f) /\
        g(start_g,q,done_g,data_g) /\
        MUX(sel,data_f,data_g,out) /\
        AND(done_e,done_f,c2) /\ AND(c2,done_g,done)`;



(*****************************************************************************)
(* TOTAL(f1,f2,f3) checks the termination for                                *)
(* TAILREC f1 f2 f3 = \x. if (f1 x) then (f2 x) else TAILREC f1 f2 f3 (f3 x) *)
(*****************************************************************************)

val TOTAL_def = 
 Define 
   `TOTAL(f1,f2,f3) = 
      ?variant. !x. ~(f1 x) ==> (variant (f3 x)) < (variant x)`;

val TAILREC_def = 
 TotalDefn.DefineSchema `TAILREC x = if f1 x then f2 x else TAILREC (f3 x)`;

val TAILREC_THM = Q.prove
(`!f1 f2 f3 x. 
    (?R. WF R /\ !x. ~f1 x ==> R (f3 x) x) ==> 
    (TAILREC f1 f2 f3 x = if f1 x then f2 x else TAILREC f1 f2 f3 (f3 x))`,
  METIS_TAC [DISCH_ALL TAILREC_def]);

val TOTAL_LEMMA = Q.store_thm
("TOTAL_LEMMA",
 `TOTAL(f1,f2,f3) ==> 
   !x. (TAILREC f1 f2 f3) x =
          if f1 x then f2 x else TAILREC f1 f2 f3 (f3 x)`,
 RW_TAC std_ss [TOTAL_def]
   THEN MATCH_MP_TAC TAILREC_THM
   THEN Q.EXISTS_TAC `measure variant`
   THEN METIS_TAC [prim_recTheory.WF_measure,
                   prim_recTheory.measure_thm]);

(*****************************************************************************)
(* The recursion                                                             *)
(* The circuit is divided in 3 parts (SELECT, FINISH, CALL) for simplicity.  *)
(*****************************************************************************)

val SELECT_def = Define `SELECT (done_e,data_e,start_f,start_g) =
      ?start' not_e.
        POSEDGE_IMP(done_e,start') /\
        AND(start',data_e,start_f) /\ 
        NOT(data_e,not_e) /\ AND(not_e,start',start_g)`;
val FINISH_def = Define `FINISH (done_e,done_f,done_g,done) =
       ?c2 c3 c4. DEL (done_g,c3) /\ AND (done_g,c3,c4) /\
                  AND (done_f,done_e,c2) /\ AND (c2,c4,done)`;
val CALL_def = Define `CALL (load,inp,done,done_g,data_g,start_e,inp_e) =
      ?c0 c1 start sel.
        POSEDGE_IMP(load,c0) /\
        DEL(done,c1) /\ AND(c0,c1,start) /\
        OR(start,sel,start_e) /\
        POSEDGE_IMP(done_g,sel) /\ 
        MUX(sel,data_g,inp,inp_e)`;

val REC_def = Define `REC e f g (load,inp,done,out) =
      ?done_g data_g start_e q done_e 
       data_e start_f start_g inp_e done_f.
        CALL (load,inp,done,done_g,data_g,start_e,inp_e) /\
        DFF(inp_e,start_e,q) /\
        e (start_e,inp_e,done_e,data_e) /\
        SELECT (done_e,data_e,start_f,start_g) /\
        f (start_f,q,done_f,out) /\ 
        g (start_g,q,done_g,data_g) /\
        FINISH (done_e,done_f,done_g,done)`;


(*****************************************************************************)
(* COMPUTE encapsulates a property of SAFE_DEV                               *)
(* This definition is used in the proof of REC                               *)
(*****************************************************************************)

val COMPUTE_def = Define `COMPUTE(t,f,inp,done,out) =
       (?t'. t' > t + 1 /\ HOLDF (t + 1,t') done /\ done t' /\
            (out t' = f (inp (t + 1))))`;

(*****************************************************************************)
(* Now we start the proofs                                                   *)
(*****************************************************************************)

val POSEDGE =
 Q.store_thm
  ("POSEDGE",
   `(POSEDGE i 0 = F) /\ (POSEDGE i (t+1) = ~(i t) /\ i(t+1))`,
   RW_TAC arith_ss [POSEDGE_def]);


val POSEDGE_IMPL =
  Q.store_thm
    ("POSEDGE_IMPL",
    `POSEDGE_IMP(inp,out) ==> !t. out t = POSEDGE inp t`,
    RW_TAC arith_ss [POSEDGE_IMP_def, POSEDGE]
    THEN Cases_on `t=0`
    THENL [FULL_SIMP_TAC arith_ss [DELT_def, NOT_def, AND_def,POSEDGE_def],
           `?n. t = n+1` by PROVE_TAC [num_CASES,ADD1]
            THEN FULL_SIMP_TAC arith_ss [DELT_def, NOT_def, AND_def, POSEDGE]]);


val ATM_SPEC_def =
 Define
  `ATM_SPEC f (load,inp,done,out) =
    !t. (out(t+1)  = f (inp t)) /\
        (done(t+1) = if done t then ~(POSEDGE load (t+1)) else T)`;

val ATM_SPEC =
 Q.store_thm
  ("ATM_SPEC",
   `ATM_SPEC f (load,inp,done,out)
     ==>
     SAFE_DEV f (load,inp,done,out)`,
   RW_TAC std_ss [SAFE_DEV_def,ATM_SPEC_def,HOLDF_def]
    THEN Q.EXISTS_TAC `t+1+1`
    THEN RW_TAC arith_ss []
    THEN `t''=t+1` by DECIDE_TAC
    THEN RW_TAC arith_ss []);

val ATM_IMP =
 Q.store_thm
  ("ATM_IMP",
   `ATM f (load,inp,done,out)
     ==>
     ATM_SPEC f (load,inp,done,out)`,
   RW_TAC arith_ss [ATM_SPEC_def, ATM_def,
                    NOT_def,MUX_def,DEL_def,COMB_def]
    THEN RW_TAC std_ss []
    THEN Cases_on `done t`
    THEN IMP_RES_TAC POSEDGE_IMPL 
    THEN RW_TAC arith_ss [POSEDGE_def]
    THEN PROVE_TAC[]);

val SAFE_ATM =
 Q.store_thm
  ("SAFE_ATM",
   `ATM f (load,inp,done,out)
     ==>
     SAFE_DEV f (load,inp,done,out)`,
   PROVE_TAC[ATM_SPEC,ATM_IMP]);

val HOLDF_POSEDGE =
 Q.store_thm
  ("HOLDF_POSEDGE",
   `t' > t+1 /\ HOLDF (t + 1,t') i /\ i t' ==> POSEDGE i t'`,
   RW_TAC arith_ss [HOLDF_def,POSEDGE_def]);

val DECIDE = DECIDE o Term;

val HOLDF_NOT =
 Q.store_thm
  ("HOLDF_NOT",
    `c1 t                /\
     c2 t                /\
     t' > t+1            /\ 
     HOLDF (t + 1,t') c1 /\
     (!t. c2 t /\ ~POSEDGE c1 (t+1) ==> c2 (t + 1)) 
     ==> c2(t'-1)`,
   Induct_on `t'`
    THEN RW_TAC arith_ss [HOLDF_def]
    THEN FULL_SIMP_TAC arith_ss [arithmeticTheory.ADD1]
    THEN `~(POSEDGE c1 (t+1))` by PROVE_TAC[POSEDGE,HOLDF_def]
    THEN Cases_on `t'=t+1`
    THEN RW_TAC arith_ss []
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(Q.SPEC `t'-1` (el 3 thl)))
    THEN `t' - 1 + 1 = t'` by DECIDE_TAC
    THEN POP_ASSUM(fn th => FULL_SIMP_TAC std_ss [th])
    THEN `t' > t+1` by DECIDE_TAC
    THEN `c2 (t' - 1)` by PROVE_TAC[HOLDF_def,DECIDE`m < n ==> m < n+1`]
    THEN `t+1 <= t'` by DECIDE_TAC
    THEN PROVE_TAC[POSEDGE_def,DECIDE`m < m+1`]);

val HOLDF_TRANS =
 Q.store_thm
  ("HOLDF_TRANS",
   `HOLDF (m,n) f /\ HOLDF (n,p) f ==> HOLDF (m,p) f`,
   RW_TAC std_ss [HOLDF_def]
    THEN Cases_on `t < n`
    THEN RW_TAC std_ss []
    THEN `n <= t` by DECIDE_TAC
    THEN PROVE_TAC[]);

val HOLDF_DEC =
 Q.store_thm
  ("HOLDF_DEC",
   `HOLDF (m,n+1) f ==> HOLDF (m,n) f`,
   RW_TAC arith_ss [HOLDF_def]);

(* The following is a technical lemma needed for SEQ *)

val HOLDF_INTERVAL_LEMMA =
 Q.store_thm
  ("HOLDF_INTERVAL_LEMMA",
   `t'' > t' /\
     c1 t'                                            /\
     (!t. c0 t = not_c2 t \/ load t)                  /\
     (!t. c1 t /\ ~POSEDGE c0 (t + 1) ==> c1 (t + 1)) /\
     (!t. not_c2 t = ~c2 t)                           /\
     HOLDF (t',t'') c2
     ==>
     c1 t''`,
   Induct_on `t''`
    THEN RW_TAC arith_ss [HOLDF_def]
    THEN FULL_SIMP_TAC std_ss [ADD1]
    THEN Cases_on `t''=t'`
    THEN RW_TAC arith_ss []
    THENL
     [ASSUM_LIST
       (fn thl => ASSUME_TAC(SIMP_RULE arith_ss [el 4 thl,el 5 thl,POSEDGE_def] 
                                       (Q.SPEC `t'` (el 3 thl))))
       THEN PROVE_TAC[DECIDE`t'<=t' /\ t' < t'+1`],
   `t'' > t'` by DECIDE_TAC
    THEN `HOLDF(t',t''+1)c2` by PROVE_TAC[HOLDF_def]
    THEN IMP_RES_TAC HOLDF_DEC
    THEN RES_TAC
    THEN `t' <= t''` by DECIDE_TAC
    THEN `c0 t''` by PROVE_TAC[HOLDF_def,DECIDE `m < m+1`]
    THEN `~(POSEDGE c0 (t''+1))` by PROVE_TAC[POSEDGE]
    THEN PROVE_TAC[]]);

val SAFE_SEQ =
 Q.store_thm
  ("SAFE_SEQ",
   `SEQ (SAFE_DEV f) (SAFE_DEV g) (load,inp,done,out)
     ==>
     SAFE_DEV (g o f) (load,inp,done,out)`,
   RW_TAC std_ss [SEQ_def,SAFE_DEV_def,AND_def,OR_def,NOT_def]
    THENL
     [`~(c0 t)` by PROVE_TAC[POSEDGE]
       THEN `c0(t+1)` by PROVE_TAC[POSEDGE]
       THEN `POSEDGE c0 (t+1)` by PROVE_TAC[POSEDGE]
       THEN RES_TAC
       THEN `t'-1+1 = t'` by DECIDE_TAC
       THEN `POSEDGE c1 t'` by PROVE_TAC[HOLDF_POSEDGE]
       THEN `c2 (t' - 1)` by PROVE_TAC[HOLDF_NOT]
       THEN ASSUM_LIST
             (fn thl => 
               STRIP_ASSUME_TAC
                (SIMP_RULE arith_ss 
                  [el 1 thl, el 2 thl, el 3 thl](Q.SPEC `t'-1` (el 18 thl))))
       THEN `HOLDF (t+1,t') done` by PROVE_TAC[HOLDF_def]
       THEN `HOLDF (t',t'') done` by PROVE_TAC[HOLDF_def]
       THEN `HOLDF (t+1,t'') done` by PROVE_TAC[HOLDF_TRANS]
       THEN Q.EXISTS_TAC `t''`
       THEN RW_TAC arith_ss []
       THEN IMP_RES_TAC HOLDF_INTERVAL_LEMMA,
      `c1 t` by PROVE_TAC[]
       THEN `c2 t` by PROVE_TAC[]
       THEN `~(not_c2 t)` by PROVE_TAC[]
       THEN `c0 t = load t` by PROVE_TAC[]
       THEN `~(POSEDGE c1 (t+1))` by PROVE_TAC[POSEDGE]
       THEN `c2 (t+1)` by PROVE_TAC[]
       THEN RW_TAC std_ss []
       THEN Cases_on `load t`
       THENL
        [`~(POSEDGE c0 (t+1))` by PROVE_TAC[POSEDGE]
          THEN PROVE_TAC[],
         `~(c0 (t+1))` by PROVE_TAC[POSEDGE]
          THEN `~(POSEDGE c0 (t+1))` by PROVE_TAC[POSEDGE]
          THEN PROVE_TAC[]]]);


val DFF_SUC = Q.store_thm("DFF_SUC",
              `DFF (d,sel,q) ==> 
                (!t. t > 0 ==> (q t = if POSEDGE sel t then d t else q (t-1)))`,
              RW_TAC arith_ss [] 
              THEN Cases_on `t`
              THENL [(* `~(0 > 0)` by RW_TAC arith_ss [],*)
                     FULL_SIMP_TAC arith_ss [],
                     `SUC n = n+1` by RW_TAC arith_ss []
                     THEN `SUC n - 1 = n` by RW_TAC arith_ss []
                     THEN PROVE_TAC [DFF_def]]);


val DFF_INTERVAL = Q.store_thm("DFF_INTERVAL",
     `(DFF(d,sel,q) /\ POSEDGE sel t0 /\ 
       (!t. 0 < t0 /\ t0 < t /\ t <= t1 ==> sel t)) ==>  
       (!t. 0 < t0 /\ t0 < t /\ t <= t1 ==> (q t = d t0))`,
      STRIP_TAC
      THEN `sel t0` by PROVE_TAC [POSEDGE_def]
      THEN `!t. 0 < t0 /\ t0 <= t /\ t <= t1 ==> sel t` by RW_TAC arith_ss []
      THENL [Cases_on `t=t0`
        THENL [PROVE_TAC [],
          `0 < t0 /\ t0 < t /\ t <= t1` by RW_TAC arith_ss []
           THEN PROVE_TAC []],
          `!t. 0 < t0 /\ t0 < t /\ t <= t1 ==> ~(POSEDGE sel t)` by 
               RW_TAC arith_ss [POSEDGE_def]
          THEN Induct_on `t1`
          THENL [RW_TAC arith_ss [], (* base *)
            RW_TAC arith_ss []  (* inductive step *)
            THEN Cases_on `t < SUC t1`
            THENL [RW_TAC arith_ss [],
            `t = t1+1` by RW_TAC arith_ss []
            THEN `~POSEDGE sel (t1+1)` by PROVE_TAC [POSEDGE]
            THEN `q (t1+1) = q t1` by PROVE_TAC [DFF_def]
            THEN Cases_on `t0 < t1`
            THENL [`t0 < t1 /\ t1 <= t1` by RW_TAC arith_ss []
              THEN `!t. t0 < t /\ t <= t1 ==> 
                   ~POSEDGE sel t` by RW_TAC arith_ss []
              THEN `!t. t0 <= t /\ t <= t1 ==> sel t` 
                   by RW_TAC arith_ss []
              THEN `!t. t0 < t /\ t <= t1 ==> sel t` 
                   by RW_TAC arith_ss []
              THEN `!t. (t0 < t /\ t <= t1) ==> (q t = d t0)`
                   by PROVE_TAC []
              THEN PROVE_TAC [],
              `t0 = t1` by RW_TAC arith_ss []
              THEN `t = t0 + 1` by RW_TAC arith_ss []
              THEN Cases_on `t0 = 0`
              THENL [
                `q t0 = d t0` by PROVE_TAC [DFF_def]
                THEN RW_TAC arith_ss [],
                `t0 > 0` by RW_TAC arith_ss []
                THEN PROVE_TAC [DFF_def, DFF_SUC]
                ]
              ]
           ] 
        ]
     ]);


val DFF_INTERVAL2 = Q.store_thm("DFF_INTERVAL2",
     `(DFF(d,sel,q) /\ POSEDGE sel t0 /\ 
       (!t. 0 < t0 /\ t0 < t /\ t <= t1 ==> ~(sel t))) ==>  
       (!t. 0 < t0 /\ t0 < t /\ t <= t1 ==> (q t = d t0))`,
          STRIP_TAC
          THEN `!t. 0 < t0 /\ t0 < t /\ t <= t1 ==> ~(POSEDGE sel t)` by 
               RW_TAC arith_ss [POSEDGE_def]
          THEN Induct_on `t1`
          THENL [RW_TAC arith_ss [], (* base *)
            RW_TAC arith_ss []  (* inductive step *)
            THEN Cases_on `t < SUC t1`
            THENL [RW_TAC arith_ss [],
            `t = t1+1` by RW_TAC arith_ss []
            THEN `~POSEDGE sel (t1+1)` by PROVE_TAC [POSEDGE]
            THEN `q (t1+1) = q t1` by PROVE_TAC [DFF_def]
            THEN Cases_on `t0 < t1`
            THENL [`t0 < t1 /\ t1 <= t1` by RW_TAC arith_ss []
              THEN `!t. t0 < t /\ t <= t1 ==> 
                   ~POSEDGE sel t` by RW_TAC arith_ss []
              THEN `!t. t0 < t /\ t <= t1 ==> ~(sel t)`
                   by RW_TAC arith_ss []
              THEN `!t. (t0 < t /\ t <= t1) ==> (q t = d t0)`
                   by PROVE_TAC []
              THEN PROVE_TAC [],
              `t0 = t1` by RW_TAC arith_ss []
              THEN `t = t0 + 1` by RW_TAC arith_ss []
              THEN Cases_on `t0 = 0`
              THENL [
                `q t0 = d t0` by PROVE_TAC [DFF_def]
                THEN RW_TAC arith_ss [],
                `t0 > 0` by RW_TAC arith_ss []
                THEN PROVE_TAC [DFF_def, DFF_SUC]
                ]
              ]
           ] 
        ]);



val DONE_INTERVAL = Q.store_thm("DONE_INTERVAL",
          `!done s t0 t1.
               ((!t. (((done t) /\ ~(POSEDGE s (t+1))) ==> done (t+1))) /\
                (t0 < t1) /\ (done t0) /\
                (!t. (((t0 < t) /\ (t <= t1)) ==> ~(POSEDGE s t)))) ==>
                  (!t. (((t0 < t) /\ (t <= t1)) ==> done t))`,
          RW_TAC arith_ss []
          THEN Induct_on `t`
          THENL [RW_TAC arith_ss [],
                 `SUC t = t+1` by RW_TAC arith_ss []
                 THEN RW_TAC arith_ss []
                 THEN Cases_on `t=t0`
                 THEN RW_TAC arith_ss []]);


val HOLDF_DEL = Q.store_thm("HOLDF_DEL",
      `HOLDF (a,b) s /\ DEL (s,p) ==> HOLDF (a+1,b+1) p`,
      RW_TAC arith_ss [HOLDF_def, DEL_def]
      THEN Cases_on `t`
      THENL [`~(a+1 <= 0)` by RW_TAC arith_ss [],
             `SUC n = n+1` by RW_TAC arith_ss []
             THEN RW_TAC arith_ss []]);

val HOLDF_SUC = Q.store_thm("HOLD_SUC",
      `HOLDF (n+1,m+1) s ==> !t. (n < t /\ t <= m) ==> ~(s t)`,
      RW_TAC arith_ss [HOLDF_def]);


val SAFE_PAR = 
  Q.store_thm("SAFE_PAR",
    `PAR (SAFE_DEV f) (SAFE_DEV g) (load,inp,done,out) ==>
      SAFE_DEV (\x.(f x,g x)) (load,inp,done,out)`,
    RW_TAC arith_ss [PAR_def, SAFE_DEV_def]             (* POSEDGE start (t+1) *)
    THENL [ 
      (* data computation *)
      `~(start t) /\ (start (t+1)) /\ (done' t) /\ (done'' t)`
           by (IMP_RES_TAC POSEDGE_IMPL THEN 
               PROVE_TAC [AND_def, DEL_def, POSEDGE, POSEDGE_IMP_def])
      THEN `POSEDGE start (t+1)` by PROVE_TAC [POSEDGE]
      THEN (* tf and tg are the termination time for f and g, respectively *)
           `?tf. tf > t + 1 /\ HOLDF (t + 1,tf) done' /\ done' tf /\
                 (data' tf = f (inp (t + 1)))` by PROVE_TAC []
      THEN `?tg. tg > t + 1 /\ HOLDF (t + 1,tg) done'' /\ done'' tg /\
                 (data'' tg = g (inp (t + 1)))` by PROVE_TAC []
      THEN `0 < tf /\ 0 < tg` by RW_TAC arith_ss []
      THEN Cases_on `tf < tg`
      THENL [
        (* tf < tg *)
        (* done tg *)
        `HOLDF (t+1,tg) done` by FULL_SIMP_TAC arith_ss [AND_def, HOLDF_def]
        THEN `!tt. ((t+1) < tt /\ tt <= tg) ==> ~(c1 tt)`
              by PROVE_TAC [HOLDF_DEL, HOLDF_SUC]
        THEN `!tt. ((t+1) < tt /\ tt <= tg) ==> ~(start tt)`
             by PROVE_TAC [AND_def]
        THEN `!tt. ((t+1) < tt /\ tt <= tg) ==> ~(POSEDGE start tt)`
              by PROVE_TAC [POSEDGE_def]
        THEN `!tt. tf < tt /\ tt <= tg ==> ~(POSEDGE start tt)`
              by RW_TAC arith_ss []
        THEN `!tt. tt <= tg ==> tf < tt ==> done' tt` 
             by IMP_RES_TAC DONE_INTERVAL
        THEN `done' tg` by RW_TAC arith_ss []
        THEN `done tg` by PROVE_TAC [AND_def]
        (* out' = f... /\ out'' = g... *)
        THEN `!tt. tf < tt /\ tt <= tg ==> done' tt` by RW_TAC arith_ss []
        THEN `POSEDGE done' tf` by PROVE_TAC [HOLDF_POSEDGE]
        THEN `!tt. tf < tt /\ tt <= tg ==> (out' tt = data' tf)` 
             by PROVE_TAC [DFF_INTERVAL]
        THEN `out' tg = f (inp (t+1))` by RW_TAC arith_ss []
        THEN `POSEDGE done'' tg` by PROVE_TAC [HOLDF_POSEDGE]
        THEN `t+1 <= (tg-1) /\ (tg-1) < tg` by RW_TAC arith_ss []
        THEN `~(done (tg-1))` by FULL_SIMP_TAC arith_ss [HOLDF_def,AND_def]
        THEN `(tg-1)+1 = tg` by RW_TAC arith_ss []
        THEN `~(POSEDGE start tg)`  by PROVE_TAC [POSEDGE, POSEDGE_IMPL, 
             POSEDGE_IMP_def, DEL_def, AND_def]
        THEN `out'' tg = g (inp (t+1))` by PROVE_TAC [DFF_def]
        THEN PROVE_TAC [],
        (* tf >= tg *)
        Cases_on `tg < tf`
        THENL
          [ (* tf < tf *)
            (* done tf *)
           `HOLDF (t+1,tf) done` by FULL_SIMP_TAC arith_ss [AND_def, HOLDF_def]
           THEN `!tt. ((t+1) < tt /\ tt <= tf) ==> ~(c1 tt)`
                by PROVE_TAC [HOLDF_DEL, HOLDF_SUC]
           THEN `!tt. ((t+1) < tt /\ tt <= tf) ==> ~(start tt)`
                by PROVE_TAC [AND_def]
           THEN `!tt. ((t+1) < tt /\ tt <= tf) ==> ~(POSEDGE start tt)`
                by PROVE_TAC [POSEDGE_def]
           THEN `!tt. tg < tt /\ tt <= tf ==> ~(POSEDGE start tt)`
                by RW_TAC arith_ss []
           THEN `!t. t <= tf ==> tg < t ==> done'' t` by IMP_RES_TAC DONE_INTERVAL
           THEN `done'' tf` by RW_TAC arith_ss []
           THEN `done tf` by PROVE_TAC [AND_def]
 
           (* out' = f... /\ out'' = g... *)
           THEN `!tt. tg < tt /\ tt <= tf ==> done'' tt` by RW_TAC arith_ss []
           THEN `POSEDGE done'' tg` by PROVE_TAC [HOLDF_POSEDGE]
           THEN `!tt. tg < tt /\ tt <= tf ==> (out'' tt = data'' tg)` 
                by PROVE_TAC [DFF_INTERVAL]
           THEN `out'' tf = g (inp (t+1))` by RW_TAC arith_ss []
           THEN `POSEDGE done' tf` by PROVE_TAC [HOLDF_POSEDGE]
           THEN `t+1 <= (tf-1) /\ (tf-1) < tf` by RW_TAC arith_ss []
           THEN `~(done (tf-1))` by FULL_SIMP_TAC arith_ss [HOLDF_def,AND_def]
           THEN `(tf-1)+1 = tf` by RW_TAC arith_ss []
           THEN `~(POSEDGE start tf)` 
                by PROVE_TAC [POSEDGE, POSEDGE_IMPL, POSEDGE_IMP_def, 
                   DEL_def, AND_def]
           THEN `out' tf = f (inp (t+1))` by PROVE_TAC [DFF_def]
           THEN PROVE_TAC [],
           (* tf = tg *)
           `tf=tg` by RW_TAC arith_ss []
           THEN `HOLDF (t+1,tf) done` by FULL_SIMP_TAC arith_ss[HOLDF_def, AND_def]
           THEN `done tf` by PROVE_TAC [AND_def]
           THEN `POSEDGE done' tf` by PROVE_TAC [HOLDF_POSEDGE]
           THEN `POSEDGE done'' tg` by PROVE_TAC [HOLDF_POSEDGE]
           THEN `tf > 0 /\ tg > 0` by RW_TAC arith_ss []
           THEN `out' tf = f (inp (t+1))` by PROVE_TAC [DFF_SUC]
           THEN `out'' tg = g (inp (t+1))` by PROVE_TAC [DFF_SUC]
           THEN `out'' tf = g (inp (t+1))` by PROVE_TAC [DFF_SUC]
           THEN PROVE_TAC []
          ]
      ],
      (* done (t+1) *)

      REPEAT (Q.PAT_ASSUM `DFF x` (K ALL_TAC)) THEN
      NTAC 2 (Q.PAT_ASSUM `!t. P t ==> ?t'. Q t t'` (K ALL_TAC)) THEN
      FULL_SIMP_TAC arith_ss [AND_def, DEL_def] THEN
      `!t. c0 t = POSEDGE load t` by PROVE_TAC [POSEDGE_IMPL] THEN
      PROVE_TAC [POSEDGE, POSEDGE_def]
      ]);

val POSEDGE_LEMMA =  Q.store_thm
("POSEDGE_LEMMA",
 `t > 0 /\ POSEDGE_IMP (inp,out) /\ POSEDGE inp t ==> POSEDGE out t`,
 Cases_on `t` THEN 
 RW_TAC arith_ss [POSEDGE_IMP_def, POSEDGE_def,AND_def, DELT_def, NOT_def]
 THEN RW_TAC arith_ss [] THEN PROVE_TAC [ADD1]);

val INTERVAL_LEMMA = Q.store_thm("INTERVAL_LEMMA",
    `(((s t0) /\ (!t. t0 < t /\ t <= t1 ==> s t)) ==>
           (!t. t0 <= t /\ t <= t1 ==> s t)) /\
     ((~(s t0) /\ (!t. t0 < t /\ t <= t1 ==> ~(s t))) ==>
           (!t. t0 <= t /\ t <= t1 ==> ~(s t))) /\
     (((!t. t0 < t /\ t < t1 ==> ~(s t)) /\ (~(s t1))) ==>
      (!t. t0 < t /\ t <= t1 ==> ~(s t))) /\
     (((!t. t0 < t /\ t < t1 ==> (s t)) /\ (s t1)) ==>
      (!t. t0 < t /\ t <= t1 ==> (s t)))`,
   REPEAT STRIP_TAC
   THENL [Cases_on `t0 = t`
          THENL [PROVE_TAC [],
                `t0 < t /\ t <= t1` by RW_TAC arith_ss []
                THEN PROVE_TAC []],
          Cases_on `t0 = t`
          THENL [PROVE_TAC [],
                `t0 < t /\ t <= t1` by RW_TAC arith_ss []
                THEN PROVE_TAC []],
          Cases_on `t1=t`
          THENL [PROVE_TAC [],
                `t0 < t /\ t < t1` by RW_TAC arith_ss []
                THEN PROVE_TAC []],
          Cases_on `t1=t`
          THENL [PROVE_TAC [],
                `t0 < t /\ t < t1` by RW_TAC arith_ss []
                THEN PROVE_TAC []]
          ]);


val HOLDT_NOT_POSEDGE = Q.store_thm("HOLDT_NOT_POSEDGE",
     `(!t. t0 <= t /\ t <= t1 ==> s t) ==>
       !t. t0 < t /\ t <= t1 ==> ~POSEDGE s t`,
   Induct_on `t1`
   THENL [RW_TAC arith_ss [], (* base *)
          `SUC t1 = t1 + 1` by RW_TAC arith_ss []
          THEN RW_TAC arith_ss []
          THEN Cases_on `t=t1+1`
          THENL [`s t1` by RW_TAC arith_ss []
                 THEN PROVE_TAC [POSEDGE],
                 RW_TAC arith_ss []]]);


val POSEDGE_IMP_INTERVAL = Q.store_thm ("POSEDGE_IMP_INTERVAL",
    `(POSEDGE_IMP(inp,out) /\ (!t. t0 < t /\ t <= t1 ==> ~POSEDGE inp t)) ==>
      (!t. t0 < t /\ t <= t1 ==> ~(out t))`,
   RW_TAC arith_ss [] 
   THEN Induct_on `t1`
   THENL [RW_TAC arith_ss [],
          `SUC t1 = t1 + 1` by RW_TAC arith_ss []
          THEN RW_TAC arith_ss []
          THEN Cases_on `t=t1+1`
          THENL [PROVE_TAC [POSEDGE,POSEDGE_IMP_def, POSEDGE_IMPL],
                 `t <= t1` by RW_TAC arith_ss []
                 THEN RW_TAC arith_ss []]]);

val SAFE_ITE = Q.store_thm("SAFE_ITE",
   `ITE (SAFE_DEV e) (SAFE_DEV f) (SAFE_DEV g) (load,inp,done,out) ==>
     SAFE_DEV (\x. if (e x) then (f x) else (g x))
          (load,inp,done, out)`,
   RW_TAC arith_ss [SAFE_DEV_def,ITE_def]
   THENL 
      [
      (* POSEDGE start (t+1) *)
      `~(start t) /\ (start (t+1))` by (IMP_RES_TAC POSEDGE_IMPL THEN 
               PROVE_TAC [AND_def, DEL_def, POSEDGE, POSEDGE_IMP_def])
      THEN `POSEDGE start (t+1)` by PROVE_TAC [POSEDGE_def, POSEDGE]
      THEN (Q.PAT_ASSUM `~(start t)` kill) THEN (Q.PAT_ASSUM `start (t+1)` kill)

      (* te is the time e finishes *)
      THEN `done_e t` by PROVE_TAC [AND_def]
      THEN `?te. te > t + 1 /\ HOLDF (t + 1,te) done_e /\ done_e te /\
           (data_e te = e (inp (t + 1)))` by RW_TAC arith_ss []

      (* POSEDGE start' te *)
      THEN `POSEDGE done_e te` by PROVE_TAC [HOLDF_POSEDGE]
      THEN `te > 0` by RW_TAC arith_ss []
      THEN `POSEDGE start' te` by PROVE_TAC [POSEDGE_LEMMA]
      THEN (Q.PAT_ASSUM `te > 0` kill)

      (* 1. instatiate tf and tg *)
      THEN `done_f t /\ done_g t` 
            by (FULL_SIMP_TAC std_ss [AND_def] THEN PROVE_TAC [])

      (* 1.1 done_f tte /\ done_g tte *)
      THEN `?tte. tte = te-1` by RW_TAC arith_ss []
      THEN `te = tte+1` by RW_TAC arith_ss []
      THEN `!t0 t1 s. HOLDF (t0 + 1,t1) s ==> !t. t0 < t /\ t <= t1 - 1 ==> ~s t`
            by RW_TAC arith_ss [HOLDF_def]
      THEN `(!tt. (t < tt /\ tt <= tte) ==> ~(POSEDGE start_f tt)) /\
            (!tt. (t < tt /\ tt <= tte) ==> ~(POSEDGE start_g tt))`
            by PROVE_TAC [POSEDGE_def, POSEDGE_IMP_def,AND_def]
      THEN `t < tte` by RW_TAC arith_ss []
      THEN `tte <= tte ==> done_f tte` by IMP_RES_TAC DONE_INTERVAL
      THEN `tte <= tte ==> done_g tte` by IMP_RES_TAC DONE_INTERVAL 
      THEN `done_f tte /\ done_g tte` by RW_TAC arith_ss []

      THEN Q.PAT_ASSUM `!t0 t1 s. HOLDF (t0 + 1,t1) s ==> 
               !t. t0 < t /\ t <= t1 - 1 ==> ~s t` kill
      THEN Q.PAT_ASSUM `t < tte` kill
      THEN REPEAT (Q.PAT_ASSUM `tte <= tte ==> X tte` kill)

      THEN `~(start_f tte)` by PROVE_TAC [POSEDGE_def, AND_def]
      THEN `~(start_g tte)` by PROVE_TAC [POSEDGE_def, AND_def]
      THEN Q.PAT_ASSUM `done t`   kill THEN Q.PAT_ASSUM `POSEDGE load (t + 1)` kill
      THEN Q.PAT_ASSUM `done_e t` kill (* THEN Q.PAT_ASSUM `done_e te` kill *)
      THEN Q.PAT_ASSUM `done_f t` kill THEN Q.PAT_ASSUM `done_g t` kill

      THEN Cases_on `data_e te`
      THENL
         [ (* IF branch *)
         `start_f te` by PROVE_TAC [POSEDGE_def, AND_def]
         THEN `POSEDGE start_f te` by PROVE_TAC [POSEDGE_def, AND_def]
         THEN `POSEDGE start_f (tte+1)` by RW_TAC arith_ss []

         (* tf is the completion time of f *)
         THEN `?tf. tf > tte + 1 /\ HOLDF (tte + 1,tf) done_f /\ done_f tf /\
               (data_f tf = f (q (tte + 1)))` by PROVE_TAC []
         THEN REPEAT (Q.PAT_ASSUM `POSEDGE start_f X` kill)

         (* done_e tf *)
         THEN `HOLDF (tte+1,tf) done` by FULL_SIMP_TAC arith_ss [AND_def,HOLDF_def]
         THEN `HOLDF (tte+1+1,tf+1) c1` by PROVE_TAC [HOLDF_DEL]
         THEN `HOLDF (tte+1+1,tf+1) start` by FULL_SIMP_TAC arith_ss [AND_def,HOLDF_def]
         THEN `!tt. tte+1+1 <= tt /\ tt < tf+1 ==> ~(POSEDGE start tt)`
              by PROVE_TAC [HOLDF_def,POSEDGE_def]
         THEN `!tt. te < tt /\ tt <= tf ==> ~(POSEDGE start tt)`
              by RW_TAC arith_ss []
         THEN `te < tf` by RW_TAC arith_ss []
         THEN `!t. te < t /\ t <= tf ==> done_e t` 
            by (Q.UNDISCH_THEN `te = tte+1` (K ALL_TAC) 
                THEN MATCH_MP_TAC 
                      (Q.SPECL [`done_e`, `start`,`te`, `tf`] DONE_INTERVAL))
         THEN ASM_REWRITE_TAC []
         THEN `done_e tf` by RW_TAC arith_ss []
         THEN REPEAT (Q.PAT_ASSUM `HOLDF (tte+1+1,tf+1) Z` kill)
         THEN Q.PAT_ASSUM `!tt. tte+1+1 <= tt /\ tt < tf+1 ==> ~(POSEDGE start tt)` kill
         THEN Q.PAT_ASSUM `te < tf` kill

         (* done_g tf *)
         THEN `!tt. te <= tt /\ tt <= tf ==> done_e tt` 
               by PROVE_TAC [CONJUNCT1 INTERVAL_LEMMA]
         THEN `!tt. te < tt /\ tt <= tf ==> ~(POSEDGE done_e tt)` 
              by PROVE_TAC [HOLDT_NOT_POSEDGE]
         THEN `!tt. te < tt /\ tt <= tf ==> ~start' tt`  
              by (IMP_RES_TAC POSEDGE_IMP_INTERVAL
                   THEN PROVE_TAC [])
         THEN `~(start_g te)` by FULL_SIMP_TAC arith_ss [AND_def,NOT_def]
         THEN `!tt. te < tt /\ tt <= tf ==> ~(start_g tt)` by FULL_SIMP_TAC arith_ss [AND_def]
         THEN `!tt. te <= tt /\ tt <= tf ==> ~(start_g tt)` 
              by PROVE_TAC [CONJUNCT1(CONJUNCT2 INTERVAL_LEMMA)]
         THEN `!tt. te <= tt /\ tt <= tf ==> ~(POSEDGE start_g tt)` 
              by PROVE_TAC [POSEDGE_def]
         THEN `!tt. tte < tt /\ tt <= tf ==> ~(POSEDGE start_g tt)` 
              by RW_TAC arith_ss []
         THEN `tte < tf` by RW_TAC arith_ss []
         THEN `tf <= tf ==> done_g tf` by IMP_RES_TAC DONE_INTERVAL
         THEN `done_g tf` by RW_TAC arith_ss []
         THEN REPEAT (Q.PAT_ASSUM `!tt. X ==> ~start_g tt` kill)
         THEN REPEAT (Q.PAT_ASSUM `!tt. X ==> ~(POSEDGE start_g tt)` kill)
         THEN REPEAT (Q.PAT_ASSUM `tte < tf` kill)

         (* done tf *)
         THEN `done tf` by FULL_SIMP_TAC arith_ss [AND_def]

         (* tf > t+1 *)
         THEN `tf > t+1` by RW_TAC arith_ss []

         (* HOLDF (t + 1,tf) done *)
         THEN `HOLDF (t+1,te) done` by FULL_SIMP_TAC arith_ss [HOLDF_def,AND_def]
         THEN `HOLDF (te,tf) done` by RW_TAC arith_ss [HOLDF_def]
         THEN `HOLDF (t+1,tf) done` by PROVE_TAC [HOLDF_TRANS]
         THEN Q.PAT_ASSUM `HOLDF (tte+1,tf) done` kill
         THEN Q.PAT_ASSUM `HOLDF (te,tf) done` kill 
         THEN TRY (Q.PAT_ASSUM `(done:(num->bool)) (t:num)` kill)
         THEN TRY (Q.PAT_ASSUM `(done_e:(num->bool)) (t:num)` kill)
         THEN Q.PAT_ASSUM `HOLDF (t + 1,te) done_e` kill
         THEN Q.PAT_ASSUM `(done_e:(num->bool)) (te:num)` kill
         THEN Q.PAT_ASSUM `POSEDGE start' te` kill
         THEN TRY (Q.PAT_ASSUM `(done_f:(num->bool)) (t:num)` kill)
         THEN Q.PAT_ASSUM `(done_f:(num->bool)) (tte:num)` kill
         THEN Q.PAT_ASSUM `(done_g:(num->bool)) (tte:num)` kill
         THEN Q.PAT_ASSUM `(start_f:(num->bool)) (te:num)` kill
         THEN Q.PAT_ASSUM `HOLDF (tte + 1,tf) done_f` kill
         THEN Q.PAT_ASSUM `(done_f:(num->bool)) (tf:num)` kill
         THEN Q.PAT_ASSUM `!tt. te < tt /\ tt <= tf ==> ~POSEDGE start tt` kill
         THEN Q.PAT_ASSUM `(done_e:(num->bool)) (tf:num)` kill
         THEN Q.PAT_ASSUM `!tt. te <= tt /\ tt <= tf ==> done_e tt` kill
         THEN Q.PAT_ASSUM `!tt. te < tt /\ tt <= tf ==> ~POSEDGE done_e tt` kill
         THEN Q.PAT_ASSUM `!tt. te < tt /\ tt <= tf ==> ~start' tt` kill
         THEN Q.PAT_ASSUM ` ~((start_g:(num->bool)) (te:num))` kill
         THEN Q.PAT_ASSUM `tf <= tf ==> (done_g:(num->bool)) (tf:num)` kill
         THEN Q.PAT_ASSUM `(done_g:(num->bool)) (tf:num)` kill

         (* (out tf = if e (inp (t + 1)) then f (inp (t + 1)) else ... *)

         (* !tt. 0 < (t+1) /\ (t+1) < tt /\ tt <= te ==> ~(start tt)` *)
         THEN `!tt. (t+1+1) <= tt /\ tt < (te+1) ==> ~(c1 tt)`
              by (IMP_RES_TAC HOLDF_DEL THEN 
                  FULL_SIMP_TAC arith_ss [HOLDF_def])
         THEN `!tt. 0 < (t+1) /\ (t+1) < tt /\ tt <= te ==> ~(c1 tt)` by RW_TAC arith_ss []
         THEN `!tt. 0 < (t+1) /\ (t+1) < tt /\ tt <= te ==> ~(start tt)`
              by FULL_SIMP_TAC std_ss [AND_def]
         THEN Q.PAT_ASSUM `!tt. (t+1+1) <= tt /\ tt < (te+1) ==> ~(c1 tt)` kill
         THEN Q.PAT_ASSUM `!tt. 0 < (t+1) /\ (t+1) < tt /\ tt <= te ==> ~(c1 tt)` kill
         THEN Q.PAT_ASSUM `HOLDF (t+1,te) done` kill

         (* data_f tf = f .... (t+1) *)
         THEN `!tt. (0 < (t+1) /\ (t+1) < tt /\ tt <= te) ==> (q tt = inp (t+1))`
              by PROVE_TAC [DFF_INTERVAL2]
         THEN `data_f tf = f (inp (t+1))` by RW_TAC arith_ss []
         THEN Q.PAT_ASSUM `!tt. 0 < (t+1) /\ (t+1) < tt /\ tt <= te ==> ~(start tt)` kill
         THEN Q.PAT_ASSUM `!tt. (0 < (t+1) /\ (t+1) < tt /\ tt <= te) ==> 
               (q tt = inp (t+1))` kill

         (* sel tf = e (inp (t+1)) *)
         THEN `!tt. 0 < te /\ te < tt /\ tt <= tf ==> done_e tt`
              by RW_TAC arith_ss []
         THEN `!t. ((0 < te) /\ (te < t) /\ (t <= tf)) ==> (sel t = data_e te)` 
              by PROVE_TAC [DFF_INTERVAL]
         THEN `sel tf = data_e te` by RW_TAC arith_ss []
         THEN `sel tf = e (inp (t+1))` by PROVE_TAC []
         THEN Q.PAT_ASSUM `!tt. 0 < te /\ te < tt /\ tt <= tf ==> done_e tt` kill
         THEN Q.PAT_ASSUM `!t. ((0 < te) /\ (te < t) /\ (t <= tf)) ==> 
                   (sel t = data_e te)` kill

         (* out tf = f (inp (t+1)) *)
         THEN `out tf = f (inp (t+1))` by PROVE_TAC [MUX_def] THEN PROVE_TAC []

         , (* ELSE branch *)
         `start_g te` by FULL_SIMP_TAC std_ss [POSEDGE_def, NOT_def, AND_def]
         THEN `POSEDGE start_g te` by FULL_SIMP_TAC std_ss [POSEDGE_def, AND_def]
         THEN `POSEDGE start_g (tte+1)` by RW_TAC arith_ss []

         (* tg is the completion time of g *)
         THEN `?tg. tg > tte + 1 /\ HOLDF (tte + 1,tg) done_g /\ done_g tg /\
              (data_g tg = g (q (tte + 1)))` by PROVE_TAC []
         THEN REPEAT (Q.PAT_ASSUM `POSEDGE start_f X` kill)

         (* done_g tg *)
         THEN `HOLDF (tte+1,tg) done` by FULL_SIMP_TAC std_ss[AND_def,HOLDF_def]
         THEN `HOLDF (tte+1+1,tg+1) c1` by PROVE_TAC [HOLDF_DEL]
         THEN `HOLDF (tte+1+1,tg+1) start` by FULL_SIMP_TAC std_ss [AND_def,HOLDF_def]
         THEN `!tt. tte+1+1 <= tt /\ tt < tg+1 ==> ~(POSEDGE start tt)`
              by PROVE_TAC [HOLDF_def,POSEDGE_def]
         THEN `!tt. te < tt /\ tt <= tg ==> ~(POSEDGE start tt)`
               by RW_TAC arith_ss []
         THEN `te < tg` by RW_TAC arith_ss []
         THEN `!t. te < t /\ t <= tg ==> done_e t` 
                 by (IMP_RES_TAC DONE_INTERVAL THEN PROVE_TAC [])
         THEN `done_e tg` by RW_TAC arith_ss []
         THEN REPEAT (Q.PAT_ASSUM `HOLDF (tte+1+1,tg+1) Z` kill)
         THEN Q.PAT_ASSUM `!tt. tte+1+1 <= tt /\ tt < tg+1 ==> ~(POSEDGE start tt)` kill
         THEN Q.PAT_ASSUM `te < tg` kill

         (* done_f tf *)
         THEN `!tt. te <= tt /\ tt <= tg ==> done_e tt` 
               by (IMP_RES_TAC (CONJUNCT1 INTERVAL_LEMMA) THEN PROVE_TAC [])
         THEN `!tt. te < tt /\ tt <= tg ==> ~(POSEDGE done_e tt)` 
              by PROVE_TAC [HOLDT_NOT_POSEDGE]
         THEN `!tt. te < tt /\ tt <= tg ==> ~(start' tt)`  
              by (IMP_RES_TAC POSEDGE_IMP_INTERVAL THEN PROVE_TAC[])
         THEN `~start_f te` by FULL_SIMP_TAC std_ss [AND_def,NOT_def]
         THEN `!tt. te < tt /\ tt <= tg ==> ~(start_f tt)` 
              by FULL_SIMP_TAC std_ss [AND_def]
         THEN `!tt. te <= tt /\ tt <= tg ==> ~(start_f tt)` 
               by (IMP_RES_TAC (CONJUNCT1 (CONJUNCT2 INTERVAL_LEMMA))
                   THEN PROVE_TAC [])
         THEN `!tt. te <= tt /\ tt <= tg ==> ~(POSEDGE start_f tt)` 
              by PROVE_TAC [POSEDGE_def]
         THEN `!tt. tte < tt /\ tt <= tg ==> ~(POSEDGE start_f tt)` by RW_TAC arith_ss []
         THEN `tte < tg` by RW_TAC arith_ss []
         THEN `tg <= tg ==> done_f tg` by IMP_RES_TAC DONE_INTERVAL
         THEN `done_f tg` by RW_TAC arith_ss []
         THEN REPEAT (Q.PAT_ASSUM `!tt. X ==> ~start_f tt` kill)
         THEN REPEAT (Q.PAT_ASSUM `!tt. X ==> ~(POSEDGE start_f tt)` kill)
         THEN REPEAT (Q.PAT_ASSUM `tte < tg` kill)

         (* done tg *)
         THEN `done tg` by FULL_SIMP_TAC std_ss [AND_def]

         (* tg > t+1 *)
         THEN `tg > t+1` by RW_TAC arith_ss []

         (* HOLDF (t + 1,tg) done *)
         THEN `HOLDF (t+1,te) done` by FULL_SIMP_TAC std_ss [HOLDF_def,AND_def]
         THEN `HOLDF (te,tg) done` by RW_TAC arith_ss [HOLDF_def]
         THEN `HOLDF (t+1,tg) done` by PROVE_TAC [HOLDF_TRANS]
         THEN Q.PAT_ASSUM `HOLDF (tte+1,tg) done` kill
         THEN Q.PAT_ASSUM `HOLDF (te,tg) done` kill
         THEN TRY (Q.PAT_ASSUM `(done:(num->bool)) (t:num)` kill)
         THEN TRY (Q.PAT_ASSUM `(done_e:(num->bool)) (t:num)` kill)
         THEN Q.PAT_ASSUM `HOLDF (t + 1,te) done_e` kill
         THEN Q.PAT_ASSUM `(done_e:(num->bool)) (te:num)` kill
         THEN Q.PAT_ASSUM `POSEDGE start' te` kill
         THEN TRY(Q.PAT_ASSUM `(done_f:(num->bool)) (t:num)` kill)
         THEN Q.PAT_ASSUM `(done_f:(num->bool)) (tte:num)` kill
         THEN Q.PAT_ASSUM `(done_g:(num->bool)) (tte:num)` kill
         THEN Q.PAT_ASSUM `(start_g:(num->bool)) (te:num)` kill
         THEN Q.PAT_ASSUM `HOLDF (tte + 1,tg) done_g` kill
         THEN Q.PAT_ASSUM `(done_g:(num->bool)) (tg:num)` kill
         THEN Q.PAT_ASSUM `!tt. te < tt /\ tt <= tg ==> ~POSEDGE start tt` kill
         THEN Q.PAT_ASSUM `(done_e:(num->bool)) (tg:num)` kill
         THEN Q.PAT_ASSUM `!tt. te <= tt /\ tt <= tg ==> done_e tt` kill
         THEN Q.PAT_ASSUM `!tt. te < tt /\ tt <= tg ==> ~POSEDGE done_e tt` kill
         THEN Q.PAT_ASSUM `!tt. te < tt /\ tt <= tg ==> ~start' tt` kill
         THEN Q.PAT_ASSUM ` ~((start_f:(num->bool)) (te:num))` kill
         THEN Q.PAT_ASSUM `tg <= tg ==> (done_f:(num->bool)) (tg:num)` kill
         THEN Q.PAT_ASSUM `(done_f:(num->bool)) (tg:num)` kill

         (* (out tg = if e (inp (t + 1)) then ... else g (inp (t + 1)))) *)

         (* !tt. 0 < (t+1) /\ (t+1) < tt /\ tt <= te ==> ~(start tt)` *)
         THEN `!tt. (t+1+1) <= tt /\ tt < (te+1) ==> ~(c1 tt)` 
              by (IMP_RES_TAC HOLDF_DEL THEN PROVE_TAC [HOLDF_def])
         THEN `!tt. 0 < (t+1) /\ (t+1) < tt /\ tt <= te ==> ~(c1 tt)` by RW_TAC arith_ss []
         THEN `!tt. 0 < (t+1) /\ (t+1) < tt /\ tt <= te ==> ~(start tt)` 
               by FULL_SIMP_TAC std_ss [AND_def]
         THEN Q.PAT_ASSUM `!tt. (t+1+1) <= tt /\ tt < (te+1) ==> ~(c1 tt)` kill
         THEN Q.PAT_ASSUM `!tt. 0 < (t+1) /\ (t+1) < tt /\ tt <= te ==> ~(c1 tt)` kill
         THEN Q.PAT_ASSUM `HOLDF (t+1,te) done` kill

         (* data_g tg = g .... (t+1) *)
         THEN `!tt. (0 < (t+1) /\ (t+1) < tt /\ tt <= te) ==> (q tt = inp (t+1))`
              by PROVE_TAC [DFF_INTERVAL2]
         THEN `data_g tg = g (inp (t+1))` by RW_TAC arith_ss []
         THEN Q.PAT_ASSUM `!tt. 0 < (t+1) /\ (t+1) < tt /\ tt <= te ==> ~(start tt)` kill
         THEN Q.PAT_ASSUM `!tt. (0 < (t+1) /\ (t+1) < tt /\ tt <= te) ==> 
                          (q tt = inp (t+1))` kill

         (* sel tg = e (inp (t+1)) *)
         THEN `!tt. 0 < te /\ te < tt /\ tt <= tg ==> done_e tt` by RW_TAC arith_ss []
         THEN `!t. ((0 < te) /\ (te < t) /\ (t <= tg)) ==> (sel t = data_e te)` 
               by PROVE_TAC [DFF_INTERVAL]
         THEN `sel tg = data_e te` by RW_TAC arith_ss []
         THEN `sel tg = e (inp (t+1))` by PROVE_TAC []
         THEN Q.PAT_ASSUM `!tt. 0 < te /\ te < tt /\ tt <= tg ==> done_e tt` kill
         THEN Q.PAT_ASSUM `!t. ((0 < te) /\ (te < t) /\ (t <= tg)) ==> 
                   (sel t = data_e te)` kill

         (* out tg = g (inp (t+1)) *)
         THEN `out tg = g (inp (t+1))` by PROVE_TAC [MUX_def]
         THEN PROVE_TAC []
         ]
      , (* the done (t+1) *)
     `~POSEDGE start (t+1)` 
           by (IMP_RES_TAC POSEDGE_IMPL
               THEN PROVE_TAC [POSEDGE_def, POSEDGE_IMP_def, AND_def])
      THEN `done_e (t+1)` by PROVE_TAC [AND_def]
      THEN `done_e t` by PROVE_TAC [AND_def]
      THEN `~(POSEDGE done_e (t+1))` by PROVE_TAC [POSEDGE]
      THEN `done_g (t+1) /\ done_f (t+1)` 
           by (IMP_RES_TAC POSEDGE_IMPL THEN 
               PROVE_TAC [POSEDGE_IMP_def, POSEDGE, AND_def])
      THEN FULL_SIMP_TAC std_ss [AND_def]
      ]);


val CALL_POSEDGE = Q.store_thm
("CALL_POSEDGE",
 `CALL (load,inp,done,done_g,data_g,start_e,inp_e) /\
  FINISH (done_e,done_f,done_g,done) /\ done t /\
  POSEDGE load (t + 1) ==> POSEDGE start_e (t + 1)`,
 RW_TAC arith_ss [CALL_def,FINISH_def]
   THEN `~(start t) /\ start (t+1)` 
         by PROVE_TAC [AND_def, DEL_def, POSEDGE,POSEDGE_IMP_def,POSEDGE_IMPL]
   THEN `~sel t` by RW_TAC arith_ss [] THENL 
   [Cases_on `t=0` THENL 
    [PROVE_TAC [POSEDGE_IMPL,POSEDGE,POSEDGE_IMP_def],
     `?x. t = x+1` by PROVE_TAC [num_CASES,ADD1] THEN RW_TAC arith_ss []
       THEN POP_ASSUM (K ALL_TAC)
       THEN `done_g x /\ done_g (x+1)` by 
            (FULL_SIMP_TAC std_ss [AND_def, DEL_def] THEN PROVE_TAC [])
       THEN PROVE_TAC [POSEDGE_IMPL,POSEDGE,POSEDGE_IMP_def]],
    PROVE_TAC [POSEDGE,OR_def]
  ]);

val SIMP_SAFE_DEV = Q.store_thm("SIMP_SAFE_DEV",
       `SAFE_DEV f (load,inp,done,out) = 
        (!t. done t /\ POSEDGE load (t + 1) ==> COMPUTE (t,f,inp,done,out)) /\
        (!t. done t /\ ~POSEDGE load (t + 1) ==> done (t + 1))`,
        RW_TAC arith_ss [SAFE_DEV_def, COMPUTE_def]);

val EXT_CALL = Q.store_thm ("EXT_CALL",
         `CALL (load,inp,done,done_g,data_g,start_e,inp_e) /\
           FINISH (done_e,done_f,done_g,done) /\
           done t /\ POSEDGE load (t + 1) ==>
           (inp_e (t + 1) = inp (t + 1))`,
        RW_TAC arith_ss [CALL_def,FINISH_def] 
        THEN `~sel (t+1)` by PROVE_TAC [POSEDGE,POSEDGE_IMPL,
                                        POSEDGE_IMP_def,AND_def,DEL_def]
        THEN PROVE_TAC [MUX_def]);


(*****************************************************
 BASE_LEMMA
 when the base case is busy, cond and step remain idle 
*****************************************************)

val BASE_LEMMA = Q.store_thm("BASE_LEMMA",
    `DFF (inp_e,start_e,q) /\
     done_e te /\
     done_g te /\
     done_g (te - 1) /\
     HOLDF (te,tf) done_f /\
     tf > te /\
     CALL (load,inp,done,done_g,data_g,start_e,inp_e) /\
     SELECT (done_e,data_e,start_f,start_g) /\
     FINISH (done_e,done_f,done_g,done) /\
     SAFE_DEV e (start_e,inp_e,done_e,data_e) /\
     SAFE_DEV f (start_f,q,done_f,out) /\
     SAFE_DEV g (start_g,q,done_g,data_g)
     ==>
     (!tt. te < tt /\ tt <= tf ==> (done_g tt) /\ (done_e tt))`,
     ASM_REWRITE_TAC [SAFE_DEV_def,CALL_def,SELECT_def,FINISH_def]
     THEN STRIP_TAC
     THEN Induct_on `tf`
     THENL [
     RW_TAC arith_ss [] (* base *)
     ,
     STRIP_TAC THEN STRIP_TAC (* inductive *)
     THEN `SUC tf = tf+1` by RW_TAC arith_ss []
     THEN PURE_ASM_REWRITE_TAC []
     THEN `HOLDF (te,tf) done_f` by RW_TAC arith_ss [HOLDF_def]
     THENL [
     `!tt. te <= tt /\ tt < (tf+1) ==> ~(done_f tt)` by PROVE_TAC [HOLDF_def]
     THEN `!tt. te <= tt /\ tt < tf ==> ~(done_f tt)` by RW_TAC arith_ss []
     THEN RW_TAC arith_ss []
     ,
     `!tt. te < tt /\ tt <= tf ==> done_g tt /\ done_e tt` by ASM_REWRITE_TAC []
     THENL [
     Cases_on `tf <= te`
     THENL [
     RW_TAC arith_ss []
     ,
     `tf > te` by RW_TAC arith_ss []
     THEN PROVE_TAC []
     ]
     ,
     Cases_on `tf > te`
     THENL [
     `done_e tf` by RW_TAC arith_ss []
     THEN `done_g tf` by RW_TAC arith_ss []
     THEN `done_g (tf-1)` by RW_TAC arith_ss []
     THENL [
     Cases_on `(tf-1)= te`
     THENL [
     PROVE_TAC []
     ,
     `te < (tf-1) /\ (tf-1) < tf` by RW_TAC arith_ss [] 
     THEN `tf - 1 <= tf ==> done_g (tf - 1)` by RES_TAC
     THEN RW_TAC arith_ss []
     ]
     ,
     `~(POSEDGE done_g (tf+1))` by PROVE_TAC [POSEDGE]
     THEN `~(sel (tf+1))` by PROVE_TAC [POSEDGE_IMPL,POSEDGE_def,POSEDGE]
     THEN `!tt. te <= tt /\ tt < (SUC tf) ==> ~(done_f tt)` by PROVE_TAC [HOLDF_def]
     THEN `~(done_f tf)` by RW_TAC arith_ss []
     THEN `~(done tf)` by FULL_SIMP_TAC std_ss [AND_def]
     THEN `~(c1 (tf+1))` by FULL_SIMP_TAC std_ss [DEL_def]
     THEN `~(start (tf+1))` by FULL_SIMP_TAC std_ss [AND_def]
     THEN `~(POSEDGE start_e (tf+1))` by FULL_SIMP_TAC std_ss [OR_def,POSEDGE]
     THEN `done_e (tf+1)` by PROVE_TAC []
     THEN `~(POSEDGE done_e (tf+1))` by FULL_SIMP_TAC std_ss [POSEDGE]
     THEN `~(start' (tf+1))` by PROVE_TAC [POSEDGE_IMPL,POSEDGE]
     THEN `~(POSEDGE start_g (tf+1))` by FULL_SIMP_TAC std_ss [AND_def, POSEDGE]
     THEN `done_g (tf+1)` by PROVE_TAC []
     THEN `(!tt. te < tt /\ tt < (tf+1) ==> done_g tt) /\
           (!tt. te < tt /\ tt < (tf+1) ==> done_e tt)` by RW_TAC arith_ss []
     THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [IMP_CONJ_THM] THEN CONJ_TAC
     THEN Q.ID_SPEC_TAC `tt`
     THEN MATCH_MP_TAC (last (CONJUNCTS INTERVAL_LEMMA))
     THEN ASM_REWRITE_TAC []
     ]
     ,
     Cases_on `tf < te`
     THENL [
     RW_TAC arith_ss []
     ,
     `tf = te` by RW_TAC arith_ss []
     THEN RW_TAC arith_ss []
     THENL [
     `tt = te + 1` by RW_TAC arith_ss []
     THEN `~(POSEDGE done_g (te+1))` by RW_TAC std_ss [POSEDGE]
     THEN `~(sel (te+1))` by PROVE_TAC [POSEDGE_IMPL,POSEDGE_def,POSEDGE]
     THEN `!tt. te <= tt /\ tt < (SUC te) ==> ~(done_f tt)` by PROVE_TAC [HOLDF_def]
     THEN `~(done_f te)` by RW_TAC arith_ss []
     THEN `~(done te)` by FULL_SIMP_TAC std_ss [AND_def]
     THEN `~(c1 (te+1))` by FULL_SIMP_TAC std_ss [DEL_def]
     THEN `~(start (te+1))` by FULL_SIMP_TAC std_ss [AND_def]
     THEN `~(POSEDGE start_e (te+1))` by FULL_SIMP_TAC std_ss [OR_def,POSEDGE]
     THEN `done_e (te+1)` by PROVE_TAC []
     THEN `~(POSEDGE done_e (te+1))` by RW_TAC std_ss [POSEDGE]
     THEN `~(start' (te+1))` by PROVE_TAC [POSEDGE_IMPL,POSEDGE]
     THEN `~(POSEDGE start_g (te+1))` by FULL_SIMP_TAC std_ss [AND_def, POSEDGE]
     THEN `done_g (te+1)` by PROVE_TAC []
     THEN PROVE_TAC []
     ,
     `tt = te + 1` by RW_TAC arith_ss []
     THEN `~(POSEDGE done_g (te+1))` by RW_TAC std_ss [POSEDGE]
     THEN `~(sel (te+1))` by PROVE_TAC [POSEDGE_IMPL,POSEDGE_def,POSEDGE]
     THEN `!tt. te <= tt /\ tt < (SUC te) ==> ~(done_f tt)` by PROVE_TAC [HOLDF_def]
     THEN `~(done_f te)` by RW_TAC arith_ss []
     THEN `~(done te)` by FULL_SIMP_TAC std_ss [AND_def]
     THEN `~(c1 (te+1))` by FULL_SIMP_TAC std_ss [DEL_def]
     THEN `~(start (te+1))` by FULL_SIMP_TAC std_ss [AND_def]
     THEN `~(POSEDGE start_e (te+1))` by FULL_SIMP_TAC std_ss [OR_def,POSEDGE]
     THEN `done_e (te+1)` by PROVE_TAC []
     THEN PROVE_TAC []
     ]]]]]]);


(*******************************************************
 REC_LEMMA
*****************************************************)
val REC_LEMMA = Q.store_thm("REC_LEMMA",
    `(CALL (load,inp,done,done_g,data_g,start_e,inp_e) /\
      DFF (inp_e,start_e,q) /\
      SELECT (done_e,data_e,start_f,start_g) /\
      FINISH (done_e,done_f,done_g,done) /\
      (!x. ~f1 x ==> variant (f3 x) < variant x) /\
      (done_e t) /\
      (done_f (t + 1)) /\
      (done_g (t + 1)) /\
      (POSEDGE start_e (t + 1)) /\
      (SAFE_DEV f1 (start_e,inp_e,done_e,data_e)) /\
      (SAFE_DEV f2 (start_f,q,done_f,out)) /\
      (SAFE_DEV f3 (start_g,q,done_g,data_g))) ==>
      COMPUTE
           (t,TAILREC f1 f2 f3,inp_e,done,out)`,
     RW_TAC arith_ss [SAFE_DEV_def,COMPUTE_def, CALL_def,SELECT_def,FINISH_def]
     THEN completeInduct_on `variant (inp_e (t+1))`
     THEN REPEAT STRIP_TAC
     THEN `?te. te > t + 1 /\ HOLDF (t + 1,te) done_e /\ done_e te /\
          (data_e te = f1 (inp_e (t+1)))` by RW_TAC arith_ss []
     THEN Cases_on `data_e te`
     THENL [
     Q.PAT_ASSUM `!(m:num). (m:num) < v ==> X` kill (* delete the ind hyp *)
     THEN `POSEDGE start_f te` by RW_TAC arith_ss []
     THENL [
     `POSEDGE done_e te` by IMP_RES_TAC HOLDF_POSEDGE
     THEN `~(done_e (te-1))` by FULL_SIMP_TAC std_ss [POSEDGE_def]
     THEN `~(POSEDGE done_e (te-1))` by FULL_SIMP_TAC std_ss [POSEDGE_def]
     THEN `~(start' (te-1))` by PROVE_TAC [POSEDGE,POSEDGE_def,
                                POSEDGE_IMP_def, POSEDGE_IMPL]
     THEN `start' te` by PROVE_TAC [POSEDGE,POSEDGE_def,
                             POSEDGE_IMP_def, POSEDGE_IMPL]
     THEN FULL_SIMP_TAC std_ss [AND_def, POSEDGE_def]
     ,
     (* POSEDGE start_f te prvd *)
     `done_f (te-1)` by RW_TAC arith_ss []
     THENL [
     `!t0 t1 s. HOLDF (t0 + 1,t1) s ==> !t. t0 < t /\ t <= t1 - 1 ==> ~s t`
            by RW_TAC arith_ss [HOLDF_def]
     THEN `!tt. t < tt /\ tt <= (te-1) ==> ~POSEDGE start_f tt`
           by PROVE_TAC [POSEDGE_def, POSEDGE_IMP_def, AND_def]  (* slow *)
     THEN `!tt. ((t+1) < tt /\ tt <= (te-1) ==> ~(POSEDGE start_f tt))` 
          by RW_TAC arith_ss []
     THEN `t + 1 < te - 1 ==> !t'. t + 1 < t' ==> t' <= te - 1 ==> done_f t'`
          by IMP_RES_TAC DONE_INTERVAL
     THEN Cases_on `t+1 < te-1`
          THENL [RW_TAC arith_ss [],
              `t+1 = te-1` by RW_TAC arith_ss []
              THEN PROVE_TAC []]
     ,
     (* done_f (te-1) prvd *)
     `q te = inp_e (t+1)` by RW_TAC arith_ss []
     THENL [
     `!tt. (t+1) < tt /\ tt <= te ==> ~(sel tt)` by ASM_REWRITE_TAC []
     THENL [
     `!tt. (t+1) <= tt /\ tt < te ==> ~(done_e tt)` by FULL_SIMP_TAC std_ss [HOLDF_def]
     THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(start' tt)` 
          by PROVE_TAC [POSEDGE_def, POSEDGE,POSEDGE_IMPL]
     THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(start_g tt)` 
          by FULL_SIMP_TAC std_ss [AND_def]
     THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(POSEDGE start_g tt)` 
          by FULL_SIMP_TAC std_ss [POSEDGE_def]
     THEN `!tt. (t+1) < tt /\ tt < te ==> ~(POSEDGE start_g tt)` by RW_TAC arith_ss []
     THEN `~(POSEDGE start_g te)` 
          by FULL_SIMP_TAC std_ss [NOT_def,AND_def,POSEDGE_def]
     THEN `!tt. (t+1) < tt /\ tt <= te ==> ~(POSEDGE start_g tt)` 
          by (MATCH_MP_TAC (el 3 (CONJUNCTS INTERVAL_LEMMA))
              THEN ASM_REWRITE_TAC [])
     THEN `t + 1 < te ==> !t'. t' <= te ==> t + 1 < t' ==> done_g t'` 
          by IMP_RES_TAC DONE_INTERVAL
     THEN `!tt. (t+1) < tt /\ tt <= te ==> done_g tt` by RW_TAC arith_ss []
     THEN `!tt. (t+1) <= tt /\ tt <= te ==> done_g tt` 
          by (MATCH_MP_TAC (CONJUNCT1 INTERVAL_LEMMA) THEN ASM_REWRITE_TAC [])
     THEN `!tt. t + 1 < tt ==> tt <= te ==> ~POSEDGE done_g tt`
          by IMP_RES_TAC HOLDT_NOT_POSEDGE
     THEN `!tt. t + 1 < tt /\ tt <= te ==> ~POSEDGE done_g tt` by RW_TAC arith_ss []
     THEN PROVE_TAC [POSEDGE_IMPL,POSEDGE,POSEDGE_def]
     ,
     (* !tt. (t+1) < tt /\ tt <= te ==> ~(sel tt) prvd *)
     `!tt. t + 1 < tt /\ tt <= te ==> ~(start_e tt)` by ASM_REWRITE_TAC []
     THENL [
     `HOLDF (t+1,te) done` by FULL_SIMP_TAC std_ss [HOLDF_def,AND_def]
     THEN `HOLDF ((t+1)+1,te+1) c1` by IMP_RES_TAC HOLDF_DEL
     THEN `!tt. t + 1 +1 <= tt /\ tt < (te+1) ==> ~(c1 tt)` 
          by PROVE_TAC [HOLDF_def]
     THEN `!tt. t + 1 < tt /\ tt <= te ==> ~(c1 tt)` by RW_TAC arith_ss []
     THEN `!tt. t + 1 < tt /\ tt <= te ==> ~(c1 tt)` by RW_TAC arith_ss []
     THEN FULL_SIMP_TAC std_ss [AND_def,OR_def]
     ,
     (* !tt. t+1 < tt /\ tt <= te ==> ~(start tt) prvd *)
     `!tt. 0 < (t+1) /\ (t+1) < tt /\ tt <= te ==> ~(start_e tt)` by RW_TAC arith_ss []
     THEN `0 < t + 1 ==> !tt. (t+1) < tt ==> tt <= te ==> (q tt = inp_e (t + 1))`
          by IMP_RES_TAC DFF_INTERVAL2
     THEN `0 < (t+1)` by RW_TAC arith_ss []
     THEN `!tt. t + 1 < tt ==> tt <= te ==> (q tt = (inp_e (t + 1)))` 
          by RW_TAC arith_ss []
     THEN RW_TAC arith_ss []
     ]
     ]
     ,
     (* q te = inp_e (t+1) prvd *)
     `?tte. tte = te-1` by RW_TAC arith_ss []
     THEN `?tf. tf > tte + 1 /\ HOLDF (tte + 1,tf) done_f /\ done_f tf /\
                (out tf = f2 (q (tte + 1)))` by RW_TAC arith_ss []
     THEN `tte+1 = te` by RW_TAC arith_ss []
     THEN `tf > t+1` by RW_TAC arith_ss []
     THEN `out tf = TAILREC f1 f2 f3 (inp_e (t + 1))`
          by REWRITE_TAC []
     THENL [
     `TOTAL(f1,f2,f3)` by PROVE_TAC [TOTAL_def]
     THEN `!x. TAILREC f1 f2 f3 x =
                 if f1 x then f2 x else TAILREC f1 f2 f3 (f3 x)`
            by IMP_RES_TAC TOTAL_LEMMA
     THEN PROVE_TAC []
     ,
     (* out tf = (@f..) (inp_e (t+1)) prvd *)
     `HOLDF (t + 1,tf) done` by RW_TAC arith_ss []
     THENL [
     `HOLDF (t+1,tte+1) done` by FULL_SIMP_TAC std_ss [HOLDF_def, AND_def]
     THEN `HOLDF (tte+1,tf) done` by FULL_SIMP_TAC std_ss [HOLDF_def, AND_def]
     THEN IMP_RES_TAC HOLDF_TRANS
     ,
     (* HOLDF (t+1,tf) done prvd *)
     `done tf` by REWRITE_TAC []
     THENL [
     `done_g te` by ASM_REWRITE_TAC []
     THENL [
     `!tt. (t+1) <= tt /\ tt < te ==> ~(done_e tt)` by PROVE_TAC [HOLDF_def]
     THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(start' tt)` 
          by PROVE_TAC [POSEDGE_def, POSEDGE,POSEDGE_IMPL]
     THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(start_g tt)` 
          by FULL_SIMP_TAC std_ss [AND_def]
     THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(POSEDGE start_g tt)` 
          by RW_TAC std_ss [POSEDGE_def]
     THEN `!tt. (t+1) < tt /\ tt < te ==> ~(POSEDGE start_g tt)` by RW_TAC arith_ss []
     THEN `~(POSEDGE start_g te)` 
          by FULL_SIMP_TAC std_ss [NOT_def,AND_def,POSEDGE_def]
     THEN `!tt. (t+1) < tt /\ tt <= te ==> ~(POSEDGE start_g tt)` 
          by (MATCH_MP_TAC (el 3 (CONJUNCTS INTERVAL_LEMMA))
              THEN ASM_REWRITE_TAC[])
     THEN `t + 1 < te ==> !t'. t' <= te ==> t + 1 < t' ==> done_g t'` 
          by IMP_RES_TAC DONE_INTERVAL
     THEN RW_TAC arith_ss []
     ,
     (* done_g te prvd *)
     `done_g (te-1)` by REWRITE_TAC []
     THENL [
     `!tt. (t+1) <= tt /\ tt < te ==> ~(done_e tt)` 
           by FULL_SIMP_TAC std_ss [HOLDF_def]
     THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(start' tt)` 
           by PROVE_TAC [POSEDGE_def, POSEDGE,POSEDGE_IMPL]
     THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(start_g tt)` by FULL_SIMP_TAC std_ss [AND_def]
     THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(POSEDGE start_g tt)` 
          by RW_TAC std_ss [POSEDGE_def]
     THEN `!tt. (t+1) < tt /\ tt < te ==> ~(POSEDGE start_g tt)` by RW_TAC arith_ss []
     THEN `~(POSEDGE start_g te)` by FULL_SIMP_TAC std_ss [NOT_def,AND_def,POSEDGE_def]
     THEN `!tt. (t+1) < tt /\ tt <= te ==> ~(POSEDGE start_g tt)` 
          by (MATCH_MP_TAC (el 3 (CONJUNCTS INTERVAL_LEMMA))
              THEN ASM_REWRITE_TAC[])
     THEN `t + 1 < te ==> !t'. t' <= te ==> t + 1 < t' ==> done_g t'` 
          by IMP_RES_TAC DONE_INTERVAL
     THEN `!tt. (t+1) < tt /\ tt <= te ==> done_g tt` by RW_TAC arith_ss []
     THEN `!tt. (t+1) <= tt /\ tt <= te ==> done_g tt` 
          by (MATCH_MP_TAC (el 1 (CONJUNCTS INTERVAL_LEMMA))
              THEN ASM_REWRITE_TAC[])
     THEN `done_g (te-1)` by RW_TAC arith_ss []
     ,
     (* done_g (te-1) prvd *)
     `!tt. (tte+1) < tt /\ tt <= tf ==> done_g tt` by REWRITE_TAC []
     THENL [ (* cleaning *)
     Q.PAT_ASSUM `done_e (t:num)` kill
     THEN Q.PAT_ASSUM `done_f ((t:num) + 1)` kill
     THEN Q.PAT_ASSUM `done_g ((t:num) + 1)` kill
     THEN Q.PAT_ASSUM `POSEDGE start_e ((t:num) + 1)` kill
     THEN Q.PAT_ASSUM `HOLDF ((t:num) + 1,te) done_e` kill
     THEN Q.PAT_ASSUM `data_e (te:num) = X` kill
     THEN Q.PAT_ASSUM `data_e (te:num)` kill
     THEN Q.PAT_ASSUM `POSEDGE start_f (te:num)` kill
     THEN Q.PAT_ASSUM `done_f ((te:num) - 1)` kill
     THEN Q.PAT_ASSUM `done_f (tf:num)` kill
     THEN Q.PAT_ASSUM `(tf:num) > t + 1` kill
     THEN Q.PAT_ASSUM `out (tf:num) = X` kill
     THEN Q.PAT_ASSUM `HOLDF ((t:num) + 1,tf) done` kill
     THEN Q.PAT_ASSUM `(te:num) > t+1` kill
     THEN `HOLDF (te,tf) done_f` by RW_TAC arith_ss []
     THEN Q.PAT_ASSUM `HOLDF ((tte:num)+1,tf) done_f` kill
     THEN `tf > te` by RW_TAC arith_ss []
     THEN PURE_ASM_REWRITE_TAC []
     THEN Q.PAT_ASSUM `(tte:num) = te - 1` kill
     THEN Q.PAT_ASSUM `(tte:num)+1 = te` kill
     THEN Q.PAT_ASSUM `(tf:num) > tte + 1` kill
     THEN `CALL (load,inp,done,done_g,data_g,start_e,inp_e)`
          by PROVE_TAC [CALL_def]
     THEN `SELECT (done_e,data_e,start_f,start_g)` by PROVE_TAC [SELECT_def]
     THEN `FINISH (done_e,done_f,done_g,done)` by PROVE_TAC [FINISH_def]
     THEN REPEAT (Q.PAT_ASSUM `POSEDGE_IMP X` kill)
     THEN REPEAT (Q.PAT_ASSUM `DEL X` kill)
     THEN REPEAT (Q.PAT_ASSUM `AND X` kill)
     THEN Q.PAT_ASSUM `OR ((start:num->bool),sel,start_e)` kill
     THEN Q.PAT_ASSUM `MUX X` kill
     THEN Q.PAT_ASSUM `NOT X` kill
     THEN `SAFE_DEV f1 (start_e,inp_e,done_e,data_e)` by IMP_RES_TAC SAFE_DEV_def
     THEN `!t. done_f t /\ POSEDGE start_f (t + 1) ==>
        ?t'. t' > t + 1 /\ HOLDF (t + 1,t') done_f /\ done_f t' /\
              (out t' = (f2 (q (t + 1))))` by RW_TAC arith_ss []
     THEN `SAFE_DEV f2 (start_f,q,done_f,out)` by IMP_RES_TAC SAFE_DEV_def
     THEN `SAFE_DEV f3 (start_g,q,done_g,data_g)` by IMP_RES_TAC SAFE_DEV_def 
     THEN REPEAT (Q.PAT_ASSUM `!(t:num). X` kill)
     THEN TRY (Q.PAT_ASSUM `data_e (te:num) = X` kill)
     THEN Q.PAT_ASSUM `!(x:'a). ~f1 x ==> X` kill
     THEN Q.PAT_ASSUM `out (tf:num) = X` kill
     THEN Q.PAT_ASSUM `(v:num) = variant (inp_e (t + 1))` kill
     (* end of cleaning *)
     THEN `!tt. te < tt /\ tt <= tf ==> done_g tt` 
          by (MATCH_MP_TAC (GEN_ALL(DISCH_ALL (Q.GEN `tt`
                  (MATCH_MP (DECIDE `(a ==> b /\ c) ==> (a ==> b)`)
                            (SPEC_ALL (UNDISCH BASE_LEMMA))))))
              THEN ASM_REWRITE_TAC[]
              THEN PROVE_TAC[])
     THEN RW_TAC arith_ss []
     ,
  (* !tt. (tte+1) < tt /\ tt <= tf ==> done_g tt prvd *)
     `done_g tf /\ done_g (tf-1)` by REWRITE_TAC []
     THENL [
     `done_g tf` by RW_TAC arith_ss []
     THEN `done_g (tte+1)` by RW_TAC arith_ss []
     THEN `!tt. tte + 1 <= tt /\ tt <= tf ==> done_g tt` 
         by (MATCH_MP_TAC (CONJUNCT1 INTERVAL_LEMMA)
             THEN ASM_REWRITE_TAC [])
     THEN `done_g (tf-1)` by RW_TAC arith_ss []
     THEN RW_TAC arith_ss []
     ,
     (* done_g tf /\ done_g (tf-1) prvd *)
     `done_e tf` by REWRITE_TAC []
     THENL [
     `!tt. te < tt /\ tt <= tf ==> ~(sel tt)` by REWRITE_TAC []
     THENL [
     `!tt. te < tt /\ tt <= tf ==> done_g tt` by RW_TAC arith_ss []
     THEN `!tt. te <= tt /\ tt <= tf ==> done_g tt` 
          by (MATCH_MP_TAC (CONJUNCT1 INTERVAL_LEMMA)
              THEN RW_TAC std_ss [])
     THEN `!tt. te < tt /\ tt <= tf ==> ~POSEDGE done_g tt` 
          by PROVE_TAC [HOLDT_NOT_POSEDGE]
     THEN PROVE_TAC [POSEDGE_def,POSEDGE_IMPL,POSEDGE]
     ,
     (* !tt. te < tt /\ tt <= tf ==> ~(sel tt) prvd *)
     `!tt. te < tt /\ tt <= tf ==> ~(c1 tt)` by REWRITE_TAC []
     THENL [
     `HOLDF (t+1+1,tf+1) c1` by IMP_RES_TAC HOLDF_DEL
     THEN `!tt. (t+1+1) <= tt /\ tt < (tf+1) ==> ~(c1 tt)` 
          by FULL_SIMP_TAC std_ss [HOLDF_def]
     THEN `!tt. (t+1+1) < tt /\ tt <= tf ==> ~(c1 tt)` by RW_TAC arith_ss []
     THEN RW_TAC arith_ss []
     ,
     (* !tt. te < tt /\ tt <= tf ==> ~(c1 tt) prvd *)
     `!tt. te < tt /\ tt <= tf ==> ~(start_e tt)` by FULL_SIMP_TAC std_ss [AND_def,OR_def]
     THEN `!tt. te < tt /\ tt <= tf ==> ~(POSEDGE start_e tt)` 
          by RW_TAC std_ss [POSEDGE_def]
     THEN `te < tf ==> !t. t <= tf ==> te < t ==> done_e t` 
          by IMP_RES_TAC DONE_INTERVAL
     THEN RW_TAC arith_ss []
     ]]
      ,
     (* done_e tf prvd *)
     `c3 ((tf-1)+1) = done_g (tf-1)` by PROVE_TAC [DEL_def]
     THEN `(tf-1)+1 = tf` by RW_TAC arith_ss []
     THEN FULL_SIMP_TAC std_ss [AND_def]
     ]]]]]
     ,
     (* done tf prvd *)
     Q.EXISTS_TAC `tf` THEN RW_TAC arith_ss []
     ]]]]]]
     ,
     (* Case ~(data_e te) *)
     `POSEDGE start_g te` by RW_TAC arith_ss []
     THENL [
     Q.PAT_ASSUM `!(m:num). m < X ==> Y` kill
     THEN `POSEDGE done_e te` by IMP_RES_TAC HOLDF_POSEDGE
     THEN `~(done_e (te-1))` by PROVE_TAC [POSEDGE_def]
     THEN `~(POSEDGE done_e (te-1))` by PROVE_TAC [POSEDGE_def]
     THEN `~(start' (te-1))` by PROVE_TAC [POSEDGE,POSEDGE_def,
                                POSEDGE_IMP_def, POSEDGE_IMPL]
     THEN `start' te` by PROVE_TAC [POSEDGE,POSEDGE_def,
                             POSEDGE_IMP_def, POSEDGE_IMPL]
     THEN FULL_SIMP_TAC std_ss [AND_def,NOT_def, POSEDGE_def]
     ,
     (* POSEDGE start_g te *)
     `done_g (te-1)` by RW_TAC arith_ss []
     THENL [
     Q.PAT_ASSUM `!(m:num). m < X ==> Y` kill
     THEN `!t0 t1 s. HOLDF (t0 + 1,t1) s ==> !t. t0 < t /\ t <= t1 - 1 ==> ~s t`
            by RW_TAC arith_ss [HOLDF_def]
     THEN `!tt. (t < tt /\ tt <= (te-1) ==> ~(POSEDGE start_g tt))`
           by PROVE_TAC [POSEDGE_def, POSEDGE_IMP_def, AND_def]
     THEN `!tt. ((t+1) < tt /\ tt <= (te-1) ==> ~(POSEDGE start_g tt))`
          by RW_TAC arith_ss []
     THEN `t + 1 < te - 1 ==> !t'. t + 1 < t' ==> t' <= te - 1 ==> done_g t'`
          by IMP_RES_TAC DONE_INTERVAL
     THEN Cases_on `t+1 < te-1`
        THENL [RW_TAC arith_ss [],
              `t+1 = te-1` by RW_TAC arith_ss []
              THEN PROVE_TAC []]
     ,
     (* done_g (te-1) prvd *)
     `?tg. (tg > te) /\ HOLDF (te,tg) done_g /\ done_g tg /\
              (data_g tg = f3 (inp_e (t+1)))` by REWRITE_TAC []
     THENL [
     Q.PAT_ASSUM `!(m:num). m < X ==> Y` kill
     THEN `?tte. tte = te-1` by RW_TAC arith_ss []
     THEN `?tg. tg > tte + 1 /\ HOLDF (tte + 1,tg) done_g /\ done_g tg /\
        (data_g tg = f3 (q (tte+1)))` by RW_TAC arith_ss []
     THEN `tte + 1 = te` by RW_TAC arith_ss []
     THEN `tg > te` by RW_TAC arith_ss []
     THEN `HOLDF (te,tg) done_g` by RW_TAC arith_ss []
     THEN `q te = inp_e (t+1)` by ASM_REWRITE_TAC []
     THENL [
     `!tt. (t+1) < tt /\ tt <= te ==> ~(sel tt)` by ASM_REWRITE_TAC []
     THENL [
     `t + 1 < (te-1) ==> !tt. tt <= (te-1) ==> t + 1 < tt ==> done_g tt` 
          by ASM_REWRITE_TAC []
     THENL [
     `!tt. (t+1) <= tt /\ tt < te ==> ~(done_e tt)` by PROVE_TAC [HOLDF_def]
     THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(start' tt)`
          by PROVE_TAC [POSEDGE_def, POSEDGE,POSEDGE_IMPL]
     THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(start_g tt)` 
          by FULL_SIMP_TAC std_ss [AND_def]
     THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(POSEDGE start_g tt)` 
          by FULL_SIMP_TAC std_ss [POSEDGE_def]
     THEN `!tt. (t+1) < tt /\ tt < te ==> ~(POSEDGE start_g tt)` by RW_TAC arith_ss []
     THEN `!tt. (t+1) < tt /\ tt <= (te-1) ==> ~(POSEDGE start_g tt)` 
         by RW_TAC arith_ss []
     THEN IMP_RES_TAC DONE_INTERVAL
     ,
     (* t + 1 < (te-1) ==> !tt. tt <= (te-1) ==> t + 1 < tt ==> done_g tt prvd *)
     Cases_on `t+1 < (te-1)`
     THENL [
     `!tt. (t+1) < tt /\ tt <= (te-1) ==> done_g tt` by RW_TAC arith_ss []
     THEN `!tt. (t+1) <= tt ==> tt <= (te-1) ==> done_g tt` by IMP_RES_TAC INTERVAL_LEMMA
     THEN `!tt. (t+1) <= tt /\ tt <= (te-1) ==> done_g tt` by RW_TAC arith_ss []
     THEN `!tt. tt <= te - 1 ==> t + 1 < tt ==> ~POSEDGE done_g tt`
          by IMP_RES_TAC HOLDT_NOT_POSEDGE
     THEN `!tt. tt <= te - 1 ==> t + 1 < tt ==> ~(sel tt)`
          by PROVE_TAC [POSEDGE_def,POSEDGE,POSEDGE_IMPL]
     THEN `!tt. te <= tt /\ tt < tg ==> ~(done_g tt)` 
          by FULL_SIMP_TAC std_ss [HOLDF_def]
     THEN `~(done_g te)` by RW_TAC arith_ss []
     THEN `~(sel te)` by PROVE_TAC [POSEDGE_def,POSEDGE,POSEDGE_IMPL]
     THEN `!tt. t+1 < tt /\ tt < te ==> ~sel tt` by RW_TAC arith_ss []
     THEN `!tt. tt <= te ==> t + 1 < tt ==> ~sel tt` by IMP_RES_TAC INTERVAL_LEMMA
     THEN RW_TAC arith_ss []
     ,
     (* Case ~(t+1 < te-1) *)
     `t+1 = te-1` by RW_TAC arith_ss []
     THEN RW_TAC arith_ss []
     THEN `tt=tte+1` by RW_TAC arith_ss []
     THEN `!tt. (tte+1) <= tt /\ tt < tg ==> ~(done_g tt)` by PROVE_TAC [HOLDF_def]
     THEN `~(done_g (tte+1))` by RW_TAC arith_ss []
     THEN PROVE_TAC [POSEDGE_def,POSEDGE,POSEDGE_IMPL]
     ]]
     , 
     (* !tt. (t+1) < tt /\ tt <= te ==> ~(sel tt) pvrd *)
     `!tt. t + 1 < tt /\ tt <= te ==> ~(start_e tt)` by ASM_REWRITE_TAC []
     THENL [
     `HOLDF (t+1,te) done` by FULL_SIMP_TAC std_ss [HOLDF_def,AND_def]
     THEN `HOLDF ((t+1)+1,te+1) c1` by IMP_RES_TAC HOLDF_DEL
     THEN `!tt. t + 1 +1 <= tt /\ tt < (te+1) ==> ~(c1 tt)` 
          by FULL_SIMP_TAC std_ss [HOLDF_def]
     THEN `!tt. t + 1 < tt /\ tt <= te ==> ~(c1 tt)` by RW_TAC arith_ss []
     THEN FULL_SIMP_TAC std_ss [AND_def,OR_def]
     ,
     (* !tt. t + 1 < tt /\ tt <= te ==> ~(start_e tt) prvd *)
     `!tt. 0 < (t+1) /\ (t+1) < tt /\ tt <= te ==> ~(start_e tt)` by RW_TAC arith_ss []
     THEN `0 < t + 1 ==> !tt. (t+1) < tt ==> tt <= te ==> (q tt = (inp_e (t + 1)))`
          by IMP_RES_TAC DFF_INTERVAL2 
     THEN RW_TAC arith_ss []
     ]]
     ,
     (* q te = inp_e (t+1) *)
     Q.EXISTS_TAC `tg` THEN RW_TAC arith_ss []
     ]
     ,
     (* ?tg. (tg > te) /\ ... prvd *)
     `POSEDGE start_e tg` by ASM_REWRITE_TAC []
     THENL [
     Q.PAT_ASSUM `!(m:num). m < X ==> Y` kill
     THEN `!tt. te <= tt /\ tt < tg ==> ~(done_g tt)` by FULL_SIMP_TAC std_ss [HOLDF_def]
     THEN `~(done_g (tg-1))` by RW_TAC arith_ss []
     THEN `tg-1 > 0` by RW_TAC arith_ss []
     THEN `POSEDGE done_g ((tg-1)+1)` by RW_TAC arith_ss [POSEDGE]
     THEN `tg-1+1 = tg` by RW_TAC arith_ss []
     THEN `POSEDGE done_g tg` by PROVE_TAC []
     THEN `~(sel (tg-1)) /\ sel tg` by PROVE_TAC [POSEDGE,POSEDGE_def,POSEDGE_IMPL]
     THEN `HOLDF (t+1,te) done` by FULL_SIMP_TAC std_ss [HOLDF_def,AND_def]
     THEN `HOLDF (te,tg) done` by  FULL_SIMP_TAC std_ss [HOLDF_def,AND_def]
     THEN `HOLDF (t+1,tg) done` by IMP_RES_TAC HOLDF_TRANS
     THEN `HOLDF (t+1+1,tg+1) c1` by IMP_RES_TAC HOLDF_DEL
     THEN `!tt. t+1+1 <= tt /\ tt < tg+1 ==> ~(c1 tt)` 
          by FULL_SIMP_TAC std_ss [HOLDF_def]
     THEN `~(c1 (tg-1))` by RW_TAC arith_ss []
     THEN FULL_SIMP_TAC std_ss [AND_def,OR_def,POSEDGE_def]
     ,
     (* POSEDGE start_e tg` prvd *)
     `done_e (tg-1)` by ASM_REWRITE_TAC []
     THENL [
     Q.PAT_ASSUM `!(m:num). m < X ==> Y` kill
     THEN Cases_on `te < (tg-1)`
     THENL [
     `!tt. te <= tt /\ tt < tg ==> ~(done_g tt)` 
        by FULL_SIMP_TAC std_ss [HOLDF_def]
     THEN `!tt. te <= tt /\ tt <= (tg-1) ==> ~(done_g tt)` by RW_TAC arith_ss []
     THEN `!tt. te <= tt /\ tt <= (tg-1) ==> ~(sel tt)` 
          by PROVE_TAC [POSEDGE,POSEDGE_def,POSEDGE_IMPL]
     THEN `HOLDF (te,tg) done` by  FULL_SIMP_TAC std_ss [HOLDF_def,AND_def]
     THEN `HOLDF (te+1,tg+1) c1` by IMP_RES_TAC HOLDF_DEL
     THEN `!tt. te+1 <= tt /\ tt < tg+1 ==> ~(c1 tt)` by FULL_SIMP_TAC std_ss [HOLDF_def]
     THEN `!tt. te < tt /\ tt <= (tg-1) ==> ~(c1 tt)` by RW_TAC arith_ss []
     THEN `!tt. te < tt /\ tt <= (tg-1) ==> ~(sel tt)` by RW_TAC arith_ss []
     THEN `!tt. te < tt /\ tt <= (tg-1) ==> ~(start tt)` by FULL_SIMP_TAC std_ss [AND_def]
     THEN `!tt. te < tt /\ tt <= (tg-1) ==> ~(POSEDGE start_e tt)` 
          by  FULL_SIMP_TAC std_ss [OR_def,POSEDGE_def]
     THEN `!tt. tt <= tg - 1 ==> te < tt ==> done_e tt` by IMP_RES_TAC DONE_INTERVAL
     THEN `done_e (tg-1)` by RW_TAC arith_ss []
     ,
     (* Case ~(te < (tg-1)) *)
     `te = tg-1` by RW_TAC arith_ss [] THEN RW_TAC arith_ss []
     ]
     ,
     (* `done_e (tg-1)` prvd *)
     `done_f tg` by ASM_REWRITE_TAC []
     THENL [
     Q.PAT_ASSUM `!(m:num). m < X ==> Y` kill
     THEN `t+1 < tg` by RW_TAC arith_ss []
     THEN `!tt. (t+1) <= tt /\ tt <= te ==> ~(POSEDGE start_f tt)` by ASM_REWRITE_TAC []
     THENL [
     `~(POSEDGE start_f te)` by FULL_SIMP_TAC std_ss [AND_def,POSEDGE_def]
     THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(done_e tt)` 
          by FULL_SIMP_TAC std_ss [HOLDF_def]
     THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(start' tt)`
          by PROVE_TAC [POSEDGE_def,POSEDGE,POSEDGE_IMPL]
     THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(POSEDGE start_f tt)` 
          by FULL_SIMP_TAC std_ss [AND_def,POSEDGE_def]
     THEN `!tt. t < tt /\ tt < te ==> ~(POSEDGE start_f tt)` by RW_TAC arith_ss []
     THEN `!tt. t < tt ==> tt <= te ==> ~(POSEDGE start_f tt)` 
          by IMP_RES_TAC INTERVAL_LEMMA
     THEN RW_TAC arith_ss []
     ,
     (* !tt. (t+1) <= tt /\ tt <= te ==> ~(POSEDGE start_f tt)` prvd *)
     Cases_on `te < (tg-1)`
     THENL [
     `!tt. te + 1 <= tt /\ tt <= tg - 1 ==> ~POSEDGE start_f tt` by ASM_REWRITE_TAC []
     THENL [
     `!tt. te <= tt /\ tt < tg ==> ~(done_g tt)` by FULL_SIMP_TAC std_ss [HOLDF_def]
     THEN `!tt. te <= tt /\ tt <= (tg-1) ==> ~(done_g tt)` by RW_TAC arith_ss []
     THEN `!tt. te <= tt /\ tt <= (tg-1) ==> ~(sel tt)` 
          by PROVE_TAC [POSEDGE,POSEDGE_def,POSEDGE_IMPL]
     THEN `HOLDF (te,tg) done` by  FULL_SIMP_TAC std_ss [HOLDF_def,AND_def]
     THEN `HOLDF (te+1,tg+1) c1` by IMP_RES_TAC HOLDF_DEL
     THEN `!tt. te+1 <= tt /\ tt < tg+1 ==> ~(c1 tt)` by FULL_SIMP_TAC std_ss [HOLDF_def]
     THEN `!tt. te < tt /\ tt <= (tg-1) ==> ~(c1 tt)` by RW_TAC arith_ss []
     THEN `!tt. te < tt /\ tt <= (tg-1) ==> ~(sel tt)` by RW_TAC arith_ss []
     THEN `!tt. te < tt /\ tt <= (tg-1) ==> ~(start tt)` by FULL_SIMP_TAC std_ss [AND_def]
     THEN `!tt. te < tt /\ tt <= (tg-1) ==> ~(POSEDGE start_e tt)` 
          by FULL_SIMP_TAC std_ss [OR_def,POSEDGE_def]
     THEN `!tt. tt <= tg - 1 ==> te < tt ==> done_e tt` by IMP_RES_TAC DONE_INTERVAL
     THEN `!tt. (te+1) <= tt /\ tt <= tg-1 ==> done_e tt` by RW_TAC arith_ss []
     THEN `!tt. (te+1) < tt ==> tt <= (tg-1) ==> ~POSEDGE done_e tt` 
          by IMP_RES_TAC HOLDT_NOT_POSEDGE
     THEN `!tt. (te+1) < tt /\ tt <= (tg-1) ==> ~POSEDGE done_e tt` by RW_TAC arith_ss []
     THEN `!tt. (te+1) < tt /\ tt <= (tg-1) ==> ~(start' tt)` 
          by PROVE_TAC [POSEDGE_def,POSEDGE,POSEDGE_IMPL]
     THEN `!tt. (te+1) < tt /\ tt <= (tg-1) ==> ~(POSEDGE start_f tt)` 
          by FULL_SIMP_TAC std_ss [AND_def,POSEDGE_def]
     THEN `~(POSEDGE start_f te)` by FULL_SIMP_TAC std_ss [AND_def,POSEDGE_def]
     THEN `~(POSEDGE done_e (te+1))` by FULL_SIMP_TAC std_ss [POSEDGE]
     THEN `~(start' (te+1))` by PROVE_TAC [POSEDGE_def,POSEDGE,POSEDGE_IMPL]
     THEN `~(POSEDGE start_f (te+1))` by FULL_SIMP_TAC std_ss [AND_def,POSEDGE_def]
     THEN `!tt. te + 1 <= tt ==> tt <= tg - 1 ==> ~POSEDGE start_f tt` 
          by IMP_RES_TAC INTERVAL_LEMMA
     THEN RW_TAC arith_ss []
     ,
     (* !tt. te + 1 <= tt /\ tt <= tg - 1 ==> ~POSEDGE start_f tt prvd *)
     `~(POSEDGE start_f tg)` by ASM_REWRITE_TAC []
     THENL [
     `?te'. te' > tg /\ HOLDF (tg,te') done_e` by ASM_REWRITE_TAC []
     THENL [
     `?ttg. ttg = tg -1` by RW_TAC arith_ss []
     THEN `?te'. te' > ttg + 1 /\ HOLDF (ttg + 1,te') done_e /\ done_e te' /\
        (data_e te' = f1 (inp_e (ttg+1)))` by RW_TAC arith_ss []
     THEN `ttg+1 = tg` by RW_TAC arith_ss []
     THEN PROVE_TAC []
     ,
     (* ?te'. te' > tg /\ HOLDF (tg,te') done_e prvd *)
     `!tt. tg <= tt /\ tt < te' ==> ~(done_e tt)` by FULL_SIMP_TAC std_ss [HOLDF_def]
     THEN `~(done_e tg)` by RW_TAC arith_ss []
     THEN `~(start' tg)` by PROVE_TAC [POSEDGE_IMPL,POSEDGE_def,POSEDGE]
     THEN FULL_SIMP_TAC std_ss [AND_def,POSEDGE_def]
     ]
     ,
     (* `~(POSEDGE start_f tg)` prvd *)
     `!tt. te + 1 <= tt /\ tt <= tg ==> ~POSEDGE start_f tt` by ASM_REWRITE_TAC []
     THENL [
     `!tt. te < tt /\ tt < tg ==> ~(POSEDGE start_f tt)` by RW_TAC arith_ss []
     THEN `!tt. te < tt /\ tt <= tg ==> ~(POSEDGE start_f tt)` 
          by (MATCH_MP_TAC (el 3 (CONJUNCTS INTERVAL_LEMMA))
              THEN ASM_REWRITE_TAC [])
     THEN RW_TAC arith_ss []
     ,
     (* !tt. te + 1 <= tt /\ tt <= tg ==> ~POSEDGE start_f tt prvd *)
     `!tt. t+1 < tt /\ tt <= tg ==> ~(POSEDGE start_f tt)` by ASM_REWRITE_TAC []
     THENL [
     RW_TAC arith_ss []
     THEN Cases_on `tt <= te`
     THEN RW_TAC arith_ss []
     THEN RW_TAC arith_ss []
     ,
     (* !tt. t+1 < tt /\ tt <= tg ==> ~(POSEDGE start_f tt) prvd *)
     `!tt. tt <= tg ==> (t + 1) < tt ==> done_f tt` by IMP_RES_TAC DONE_INTERVAL
     THEN RW_TAC arith_ss []
     ]
     ]
     ]
     ]
     ,
     (* Case ~(te < (tg-1)) *)
     `te = tg-1` by RW_TAC arith_ss []
     THEN `t+1 < te` by RW_TAC arith_ss []
     THEN `!tt. t+1 < tt /\ tt <= te ==> ~(POSEDGE start_f tt)` by RW_TAC arith_ss []
     THEN `!tt. tt <= te ==> (t+1) < tt ==> done_f tt` by IMP_RES_TAC DONE_INTERVAL
     THEN `done_f te` by RW_TAC arith_ss []
     THEN `done_e te` by RW_TAC arith_ss []
     THEN `~(POSEDGE done_e (te+1))` by RW_TAC std_ss [POSEDGE]
     THEN `~(start' (te+1))` by PROVE_TAC [POSEDGE_IMPL,POSEDGE_def]
     THEN `~(POSEDGE start_f (te+1))` by FULL_SIMP_TAC std_ss [AND_def,POSEDGE,POSEDGE_def]
     THEN `done_f (te+1)` by PROVE_TAC []
     THEN `tg -1 + 1 = tg` by RW_TAC arith_ss []
     THEN PROVE_TAC []
     ]
     ]
     ,
     (* done_f tg prvd *)
     `?ttg. ttg = tg-1` by RW_TAC arith_ss []
     THEN `variant (f3 (inp_e (t+1))) < v` by REWRITE_TAC []
     THENL [
     Q.PAT_ASSUM `!(m:num). m < X ==> Y` kill
     THEN `~f1 (inp_e (t+1))` by PROVE_TAC []
     THEN PROVE_TAC []
     ,
     (* variant (f3 (inp_e (t+1))) < v prvd *)
     Q.PAT_ASSUM `!(m:num). (m < v) ==> X` (fn th => ASSUME_TAC 
        (Q.SPEC `((variant:'a->num) ((f3:'a->'a) ((inp_e:num->'a) (t+1)))):num` th))
     THEN ASSUM_LIST (fn thl => ASSUME_TAC(MP (el 1 thl) (el 2 thl)))
     THEN Q.PAT_ASSUM `variant X < Y ==> Z` kill
     THEN Q.PAT_ASSUM `!(variant':'a->num) (inp_e':num->'a) (t':num). X` 
         (fn th => ASSUME_TAC (Q.SPEC `variant:'a->num` th))
     THEN Q.PAT_ASSUM `!(inp_e':num->'a) (t':num). X` 
         (fn th => ASSUME_TAC (Q.SPEC `inp_e:num->'a` th))
     THEN Q.PAT_ASSUM `!(t':num). X` 
         (fn th => ASSUME_TAC (Q.SPEC `ttg:num` th))
     THEN `variant (f3 (inp_e (t+1))) = variant ((inp_e (ttg+1)))`
          by REWRITE_TAC []
     THENL [
     `f3 (inp_e (t+1)) = (inp_e (ttg+1))` by REWRITE_TAC []
     THENL [
     `tg > (te-1)+1` by RW_TAC arith_ss []
     THEN `HOLDF ((te-1)+1,tg) done_g` by RW_TAC arith_ss []
     THEN `POSEDGE done_g tg` by IMP_RES_TAC HOLDF_POSEDGE
     THEN `sel tg` by PROVE_TAC [POSEDGE_IMPL]
     THEN `inp_e tg = data_g tg` by PROVE_TAC [MUX_def]
     THEN RW_TAC arith_ss []
     ,
     (* f3 (inp_e (t+1)) = (inp_e (ttg+1)) *)
     PROVE_TAC []
     ]
     ,
     (* variant (f3 (inp_e (t+1))) = variant ((inp_e (ttg+1))) *)
     `?tf'. tf' > ttg + 1 /\ HOLDF (ttg + 1,tf') done /\ done tf' /\
          (out tf' = TAILREC f1 f2 f3 (inp_e (ttg + 1)))` by RW_TAC arith_ss []
     THEN Q.PAT_ASSUM `(variant (f3 (inp_e (t+1))) = variant (inp_e (ttg+1))) ==> X` kill
     THEN `tf' > t+1` by RW_TAC arith_ss []
     THEN `HOLDF (t+1,tf') done` by ASM_REWRITE_TAC []
     THENL [
     `HOLDF (t+1,te) done` by FULL_SIMP_TAC std_ss [HOLDF_def,AND_def]
     THEN `HOLDF (te,tg) done` by FULL_SIMP_TAC std_ss [HOLDF_def,AND_def]
     THEN `HOLDF (t+1,tg) done` by IMP_RES_TAC HOLDF_TRANS
     THEN `ttg+1 = tg` by RW_TAC arith_ss []
     THEN `HOLDF (tg,tf') done` by RW_TAC arith_ss []
     THEN IMP_RES_TAC HOLDF_TRANS
     ,
     (* HOLDF (t+1),tf') done prvd *)
     `f3 (inp_e (t+1)) = (inp_e (ttg+1))` by REWRITE_TAC []
     THENL [
     `tg > (te-1)+1` by RW_TAC arith_ss []
     THEN `HOLDF ((te-1)+1,tg) done_g` by RW_TAC arith_ss []
     THEN `POSEDGE done_g tg` by IMP_RES_TAC HOLDF_POSEDGE
     THEN `sel tg` by PROVE_TAC [POSEDGE_IMPL]
     THEN `inp_e tg = data_g tg` by FULL_SIMP_TAC std_ss [MUX_def]
     THEN RW_TAC arith_ss []
     ,
     (* f3 (inp_e (t+1)) = (inp_e (ttg+1)) prvd *)
     `TOTAL(f1,f2,f3)` by PROVE_TAC[TOTAL_def]
     THEN `!x. TAILREC f1 f2 f3 x = if f1 x then f2 x else TAILREC f1 f2 f3 (f3 x)`
           by IMP_RES_TAC TOTAL_LEMMA
     THEN `TAILREC f1 f2 f3 (inp_e (ttg+1)) = TAILREC f1 f2 f3 (inp_e (t+1))`
           by PROVE_TAC []
     THEN `out tf' = TAILREC f1 f2 f3 (inp_e (t+1))` by PROVE_TAC []
     THEN Q.EXISTS_TAC `tf'`
     THEN PROVE_TAC []
     ]]]]]]]]]]]);




(******************** SAFE_REC  ******************)

val SAFE_REC = Q.store_thm ("SAFE_REC",
  `TOTAL(f1,f2,f3) /\ 
   REC (SAFE_DEV f1) (SAFE_DEV f2) (SAFE_DEV f3) (load,inp,done,out)
   ==>
   SAFE_DEV (TAILREC f1 f2 f3) (load,inp,done,out)`,
   ASM_REWRITE_TAC [REC_def,SIMP_SAFE_DEV,TOTAL_def] THEN (REPEAT STRIP_TAC)  
     THENL [
     `inp_e (t+1) = inp (t+1)` by IMP_RES_TAC EXT_CALL
     THEN `done_e t /\ done_f (t+1) /\ done_g (t+1) /\ POSEDGE start_e (t+1)` 
          by RW_TAC arith_ss []
     THENL [
     FULL_SIMP_TAC std_ss [AND_def,FINISH_def] THEN PROVE_TAC[]
     ,
     `POSEDGE start_e (t+1)` by IMP_RES_TAC CALL_POSEDGE
     THEN `done_e t` by (FULL_SIMP_TAC std_ss [FINISH_def,AND_def] THEN PROVE_TAC[])
     THEN `~(POSEDGE done (t+1))` by RW_TAC std_ss [POSEDGE]
     THEN `~(start_f (t+1)) /\ ~(start_g (t+1))`
          by PROVE_TAC [SELECT_def, AND_def, POSEDGE,POSEDGE_IMPL,POSEDGE_IMP_def]
     THEN `~(POSEDGE start_f (t+1)) /\ ~(POSEDGE start_g (t+1))`
          by PROVE_TAC [SELECT_def, AND_def, POSEDGE,POSEDGE_IMPL,POSEDGE_IMP_def]
     THEN `done_f t /\ done_g t` 
          by (FULL_SIMP_TAC std_ss [FINISH_def,AND_def] THEN PROVE_TAC[])
     THEN PROVE_TAC []
     ,
     `POSEDGE start_e (t+1)` by IMP_RES_TAC CALL_POSEDGE
     THEN `done_e t` by (FULL_SIMP_TAC std_ss [FINISH_def,AND_def] THEN PROVE_TAC [])
     THEN `~(POSEDGE done (t+1))` by PROVE_TAC [POSEDGE]
     THEN `~(start_f (t+1)) /\ ~(start_g (t+1))`
          by PROVE_TAC [SELECT_def, AND_def, POSEDGE,POSEDGE_IMPL,POSEDGE_IMP_def]
     THEN `~(POSEDGE start_f (t+1)) /\ ~(POSEDGE start_g (t+1))`
          by PROVE_TAC [SELECT_def, AND_def, POSEDGE,POSEDGE_IMPL,POSEDGE_IMP_def]
     THEN `done_f t /\ done_g t` 
          by (FULL_SIMP_TAC std_ss [FINISH_def,AND_def] THEN PROVE_TAC [])
     THEN PROVE_TAC []
     ,
     IMP_RES_TAC CALL_POSEDGE
     ,
     (* done_e t /\ done_f (t+1) /\ done_g (t+1) /\ POSEDGE start_e (t+1) prvd *)
     `SAFE_DEV f1 (start_e,inp_e,done_e,data_e)` by IMP_RES_TAC SIMP_SAFE_DEV
     THEN `SAFE_DEV f2 (start_f,q,done_f,out)` by IMP_RES_TAC SIMP_SAFE_DEV
     THEN `SAFE_DEV f3 (start_g,q,done_g,data_g)` by IMP_RES_TAC SIMP_SAFE_DEV
     THEN Q.PAT_ASSUM `!(t:num). done_e t /\ 
                         ~POSEDGE start_e (t + 1) ==> done_e (t + 1)` kill
     THEN Q.PAT_ASSUM `!(t:num). done_e t /\ POSEDGE start_e (t + 1) ==>
                       COMPUTE (t,f1,inp_e,done_e,data_e)` kill
     THEN Q.PAT_ASSUM `!(t:num). done_f t /\ POSEDGE start_f (t + 1) ==>
                         COMPUTE (t,f2,q,done_f,out)` kill
     THEN Q.PAT_ASSUM `!(t:num).  done_g t /\ POSEDGE start_g (t + 1) ==>
                         COMPUTE (t,f3,q,done_g,data_g)` kill
     THEN Q.PAT_ASSUM `!(t:num). done_f t /\ ~POSEDGE start_f (t + 1) ==> 
                         done_f (t + 1)` kill
     THEN Q.PAT_ASSUM `!(t:num). done_g t /\ ~POSEDGE start_g (t + 1) ==> 
                         done_g (t + 1)` kill
     THEN `COMPUTE (t,TAILREC f1 f2 f3,inp_e,done,out)` by IMP_RES_TAC REC_LEMMA
     THEN REWRITE_TAC [COMPUTE_def]
     THEN IMP_RES_TAC COMPUTE_def
     THEN (REPEAT (Q.PAT_ASSUM `HOLDF Y X ==> Z` kill))
     THEN PROVE_TAC []
     ]
     ,
     (* goal: done (t+1) *)
     `done_e t /\ done_f t /\ done_g t` 
      by (FULL_SIMP_TAC std_ss [FINISH_def,AND_def] THEN PROVE_TAC [])
     THEN `~(POSEDGE done_g (t+1))` 
          by (FULL_SIMP_TAC arith_ss [FINISH_def,AND_def, POSEDGE_def] THEN PROVE_TAC[])
     THEN `~(start_e (t+1))` by 
           (FULL_SIMP_TAC std_ss [CALL_def,OR_def,AND_def]
             THEN REPEAT (Q.PAT_ASSUM `DEL x` (K ALL_TAC))
             THEN Q.PAT_ASSUM `!x. ~f1 x ==> y` (K ALL_TAC)
             THEN Q.PAT_ASSUM `MUX y` (K ALL_TAC)
             THEN Q.PAT_ASSUM `DFF y` (K ALL_TAC)
             THEN Q.PAT_ASSUM `SELECT y` (K ALL_TAC)
             THEN REPEAT (Q.PAT_ASSUM `!t. x ==> COMPUTE y` (K ALL_TAC))
             THEN IMP_RES_TAC POSEDGE_IMPL
             THEN PROVE_TAC [POSEDGE_def,AND_def,POSEDGE_IMP_def])
     THEN `~(POSEDGE start_e (t+1))` by RW_TAC std_ss [POSEDGE_def]
     THEN `done_e (t+1)` by PROVE_TAC []
     THEN `~(POSEDGE start_f (t+1)) /\ ~(POSEDGE start_g (t+1))` 
         by (FULL_SIMP_TAC std_ss [SELECT_def]
              THEN IMP_RES_TAC POSEDGE_IMPL
              THEN PROVE_TAC [POSEDGE, AND_def,POSEDGE_IMP_def])
     THEN `done_f (t+1) /\ done_g (t+1)` by PROVE_TAC []
     THEN FULL_SIMP_TAC std_ss [FINISH_def, DEL_def, AND_def]
     ]);

val _ = export_theory();
