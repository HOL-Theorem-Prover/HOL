(* ========================================================================= *)
(* FILE          : io_onestepScript.sml                                      *)
(* DESCRIPTION   : Algebraic framework for verifying processor correctness   *)
(*                 with input and output                                     *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2003 - 2005                                               *)
(* ========================================================================= *)

(* interactive use:
  app load ["rich_listTheory", "onestepTheory"];
*)

open HolKernel boolLib bossLib Q;
open simpLib numLib combinTheory pairTheory arithmeticTheory;
open prim_recTheory pred_setTheory rich_listTheory onestepTheory;

val _ = new_theory "io_onestep";
val _ = ParseExtras.temp_loose_equality();

(* vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv *)

val op >- = op THEN1;

val bool_ss = bool_ss ++ boolSimps.LET_ss;

(* ------------------------------------------------------------------------- *)

val _ = Hol_datatype `state_inp = <| state : 'a; inp : num -> 'b |>`;
val _ = Hol_datatype `state_out = <| state : 'a; out : 'b |>`;

(*---------------------------------------------------------------------------
  - Paired Iterated Maps ----------------------------------------------------
  ---------------------------------------------------------------------------*)

val ADVANCE_def = Define `ADVANCE t1 s t2 = s (t1 + t2)`;

val PINIT_def = Define`
  PINIT init out =
    \x. let s = init x.state in
        <| state := <| state := s; out := out s |>; inp := x.inp|>`;

val PNEXT_def = Define`
  PNEXT next out =
    \x. let s = next (x.state).state (x.inp 0) in
      <| state := <| state := s; out := out s |>; inp := ADVANCE 1 x.inp |>`;

val PMAP_def = Define `
  PMAP f init next out =
    (!x. f 0 x = PINIT init out x) /\
    (!t x. f (SUC t) x = (PNEXT next out) (f t x))`;

val IS_PMAP_INIT_def = Define`
  IS_PMAP_INIT f init out = ?next. PMAP f init next out`;

val IS_PMAP_def = Define`
  IS_PMAP f = ?init next out. PMAP f init next out`;

val THE_PMAP_def = Define`
  (THE_PMAP init next out 0 x = PINIT init out x) /\
  (THE_PMAP init next out (SUC t) x =
     (PNEXT next out) (THE_PMAP init next out t x))`;

val Pstate_out_state = Define`
  Pstate_out_state x = <| state := (x.state).state; inp := x.inp |>`;

(*---------------------------------------------------------------------------
  - Output ------------------------------------------------------------------
  ---------------------------------------------------------------------------*)

val POUTPUT_def = Define`
  POUTPUT g x (t:num) = (state_inp_state (g t x)).out`;

val OUTPUT_def = Define`
  OUTPUT g x (t:num) = (g t x).out`;

val IMM_LEN_def = Define`
  IMM_LEN imm t = imm (t + 1) - imm t`;

val IMM_RET_def = Define`
  IMM_RET imm s = LEAST t. s < imm (t + 1)`;

val IMM_START_def = Define`
  IMM_START imm = imm o (IMM_RET imm)`;

val SERIALIZE_def = Define`
  SERIALIZE imm strm s = EL (s - IMM_START imm s) (strm (IMM_RET imm s))`;

val PACK_def = Define`
  PACK imm strm t = GENLIST (\s. strm (imm t + s)) (IMM_LEN imm t)`;

val COMBINE_def = Define`
  COMBINE f astrm bstrm (t:num) = f (astrm t) (bstrm t)`;

val MAP_STRM_def = Define`
  MAP_STRM f strm (t:num) = f (strm t)`;

val EVERY_STRM_def = Define`
  EVERY_STRM p strm = !(t:num). p (strm t)`;

val PACKED_STRM_def = Define`
  PACKED_STRM imm strm = !t. LENGTH (strm t) = IMM_LEN imm t`;

val OSMPL_def = Define`
  OSMPL f impl imm (x,i) t =
    f <| state := (impl (imm x t) x).state; inp := ADVANCE (imm x t) x.inp|>
      (PACK (imm x) i t)`;

(* ---- *)

val LEAST_THM = store_thm("LEAST_THM",
  `!n. (!m. m < n ==> ~P m) /\ P n ==> ($LEAST P = n)`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC whileTheory.FULL_LEAST_INTRO
    \\ Cases_on `$LEAST P = n` >- ASM_REWRITE_TAC []
    \\ `$LEAST P < n` by DECIDE_TAC
    \\ PROVE_TAC []);

val lem = prove(
  `(!t1 t2. t1 < t2 ==> imm t1 < imm t2) ==>
   (!m. m < x ==> imm (m + 1) <= imm x)`,
  RW_TAC arith_ss []
    \\ Cases_on `m + 1 = x` >- ASM_SIMP_TAC arith_ss []
    \\ `m + 1 < x` by DECIDE_TAC
    \\ RES_TAC \\ DECIDE_TAC);

val lem2 = (SIMP_RULE std_ss [NOT_LESS] o SPEC `x` o
            INST [`P` |-> `\t. imm x < imm (t + 1)`]) LEAST_THM;

val IMM_RET_THM = store_thm("IMM_RET_THM",
  `!imm. FREE_IMMERSION imm ==> ((IMM_RET imm) o imm = I)`,
  RW_TAC bool_ss [FREE_IMMERSION_def]
    \\ REWRITE_TAC [FUN_EQ_THM]
    \\ SIMP_TAC std_ss [IMM_RET_def]
    \\ STRIP_TAC \\ IMP_RES_TAC lem
    \\ POP_ASSUM (SPEC_THEN `x` ASSUME_TAC)
    \\ PAT_X_ASSUM `!t1 t2. P`
         (SPECL_THEN [`x`,`x + 1`] (ASSUME_TAC o SIMP_RULE arith_ss []))
    \\ IMP_RES_TAC lem2);

(* ---- *)

val PACKED_THM = store_thm("PACKED_THM",
  `!imm strm. PACKED_STRM imm (PACK imm strm)`,
  RW_TAC bool_ss [PACK_def,PACKED_STRM_def,LENGTH_GENLIST]);

(* ---- *)

val LIST_EQ = prove(
  `!a b. (a = b) = (LENGTH a = LENGTH b) /\ !n. n < LENGTH a ==>
         (EL n a = EL n b)`,
  REPEAT STRIP_TAC \\ EQ_TAC \\ RW_TAC bool_ss []
    \\ NTAC 2 (POP_ASSUM MP_TAC)
    \\ SPEC_TAC (`a`,`a`) \\ SPEC_TAC (`b`,`b`)
    \\ Induct \\ RW_TAC list_ss [LENGTH_NIL]
    \\ Cases_on `a` \\ FULL_SIMP_TAC list_ss []
    \\ POP_ASSUM (fn th => (ASSUME_TAC o SPEC `0`) th
                        \\ (ASSUME_TAC o GEN `n` o SPEC `SUC n`) th)
    \\ FULL_SIMP_TAC list_ss []);

val EL_GENLIST = prove(
  `!f n x. x < n ==> (EL x (GENLIST f n) = f x)`,
  Induct_on `n` >- SIMP_TAC arith_ss []
    \\ REPEAT STRIP_TAC \\ REWRITE_TAC [GENLIST]
    \\ Cases_on `x < n`
    \\ POP_ASSUM (fn th =>
          ASSUME_TAC (SUBS [(GSYM o SPECL [`f`,`n`]) LENGTH_GENLIST] th) \\
          ASSUME_TAC th)
    >- ASM_SIMP_TAC bool_ss [EL_SNOC]
    \\ `x = LENGTH (GENLIST f n)` by FULL_SIMP_TAC arith_ss [LENGTH_GENLIST]
    \\ ASM_SIMP_TAC bool_ss [EL_LENGTH_SNOC]
    \\ REWRITE_TAC [LENGTH_GENLIST]);

val lem = prove(
  `!x imm. FREE_IMMERSION imm ==> x <= imm x`,
  RW_TAC arith_ss [FREE_IMMERSION_def]
    \\ SPEC_TAC (`x`,`x`)
    \\ Induct
    \\ ASM_SIMP_TAC arith_ss [ADD1]
    \\ PAT_X_ASSUM `!t1 t2. P`
         (SPECL_THEN [`x`,`x + 1`] (ASSUME_TAC o SIMP_RULE arith_ss []))
    \\ DECIDE_TAC);

val lem2 = prove(
  `!x imm. FREE_IMMERSION imm ==> x < imm (IMM_RET imm x + 1)`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC lem
    \\ FULL_SIMP_TAC std_ss [IMM_RET_def,FREE_IMMERSION_def]
    \\ POP_ASSUM (SPEC_THEN `x` ASSUME_TAC)
    \\ PAT_X_ASSUM `!t1 t2. P`
         (SPECL_THEN [`x`,`x + 1`] (ASSUME_TAC o SIMP_RULE arith_ss []))
    \\ IMP_RES_TAC LESS_EQ_LESS_TRANS
    \\ METIS_TAC [(SIMP_RULE std_ss [] o SPECL
         [`\t. x < imm (t + 1)`,`\t. x < imm (t + 1)`]) whileTheory.LEAST_ELIM]
);

val lem3 = prove(
  `!x imm. FREE_IMMERSION imm ==> ?t. x < imm (t + 1)`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC lem
    \\ EXISTS_TAC `x`
    \\ POP_ASSUM (SPEC_THEN `x` ASSUME_TAC)
    \\ FULL_SIMP_TAC std_ss [FREE_IMMERSION_def]
    \\ PAT_X_ASSUM `!t1 t2. P`
         (SPECL_THEN [`x`,`x + 1`] (ASSUME_TAC o SIMP_RULE arith_ss []))
    \\ IMP_RES_TAC LESS_EQ_LESS_TRANS);

val lem4 = prove(
  `!x imm. FREE_IMMERSION imm ==> imm (IMM_RET imm x) <= x`,
  RW_TAC std_ss [IMM_RET_def]
    \\ IMP_RES_TAC (CONV_RULE (ONCE_DEPTH_CONV EXISTS_LEAST_CONV) lem3)
    \\ POP_ASSUM (SPEC_THEN `x` STRIP_ASSUME_TAC)
    \\ IMP_RES_TAC ((SIMP_RULE std_ss [] o
         INST [`P` |-> `\t. x < imm (t + 1)`] o SPEC `t`) LEAST_THM)
    \\ FULL_SIMP_TAC std_ss [FREE_IMMERSION_def]
    \\ Cases_on `t` >- ASM_SIMP_TAC arith_ss []
    \\ PAT_X_ASSUM `!t. t < SUC n ==> p`
         (SPEC_THEN `n` (ASSUME_TAC o SIMP_RULE arith_ss [NOT_LESS]))
    \\ ASM_REWRITE_TAC [ADD1]);

val PACK_SERIALIZE = store_thm("PACK_SERIALIZE",
  `!imm. FREE_IMMERSION imm ==>
      (!strm. PACKED_STRM imm strm ==>
             (PACK imm (SERIALIZE imm strm) = strm)) /\
      (!strm. SERIALIZE imm (PACK imm strm) = strm)`,
  RW_TAC bool_ss [PACKED_STRM_def]
    \\ REWRITE_TAC [FUN_EQ_THM,LIST_EQ]
    THENL [
      RW_TAC bool_ss [PACK_def,LENGTH_GENLIST,EL_GENLIST]
        \\ SIMP_TAC arith_ss [SERIALIZE_def,IMM_START_def,IMM_RET_def]
        \\ Cases_on `x`
        THENL [
          FULL_SIMP_TAC arith_ss [FREE_IMMERSION_def,IMM_LEN_def,
            (SIMP_RULE arith_ss [NOT_LESS] o
             INST [`P` |-> `\t. n < imm (t + 1)`] o SPEC `0`) LEAST_THM],
          FULL_SIMP_TAC std_ss [FREE_IMMERSION_def]
             \\ `n + imm (SUC n') < imm (SUC n' + 1)`
             by FULL_SIMP_TAC arith_ss [IMM_LEN_def]
             \\ `!m. m < n' ==> imm (m + 1) <= n + imm (SUC n')`
             by METIS_TAC [DECIDE ``a < b ==> a <= n + b /\ a + 1 < b + 1``,
                           ADD1]
             \\ `!m. (m = n') ==> imm (n' + 1) <= n + imm (SUC n')`
             by ASM_SIMP_TAC arith_ss [ADD1]
             \\ IMP_RES_TAC ((CONV_RULE (DEPTH_CONV FORALL_AND_CONV) o
                  SIMP_RULE std_ss [NOT_LESS,DISJ_IMP_THM,
                    (GSYM o REWRITE_RULE [LESS_OR_EQ,GSYM ADD1]) LE_LT1] o
                  INST [`P` |-> `\t. n + imm (SUC n') < imm (t + 1)`] o
                  SPEC `SUC n'`) LEAST_THM)
             \\ ASM_SIMP_TAC arith_ss []],
      IMP_RES_TAC (CONJ lem2 lem4)
        \\ STRIP_TAC \\ POP_ASSUM (SPEC_THEN `x` ASSUME_TAC)
        \\ PAT_X_ASSUM `!x. P` (SPEC_THEN `x` ASSUME_TAC)
        \\ ASM_SIMP_TAC arith_ss
             [SERIALIZE_def,PACK_def,EL_GENLIST,IMM_START_def,IMM_LEN_def]]);

(*---------------------------------------------------------------------------
  - Stream Abstraction ------------------------------------------------------
  ---------------------------------------------------------------------------*)

(* The following definition is too strong for the ARM6 verification.

 - Mapping from the ARM6 to the pipelined ISA it is not the case that all
   sequences of of interrupts can occur from a given state.  This
   is primarily due to interrupt latency.

 - From the pipelined to instruction stream ISA it is not the case
   that all sequences of instruction registers can be given by
   the sequence of interrupts.  Furthermore, neither is it the case that all
   instruction sequences can be generated from a given state.

val STREAM_ABSTRACTION_def = Define `
  STREAM_ABSTRACTION smpl sstrm istrm =
    (?i. sstrm i) /\ !a i. sstrm i = ?j. istrm j /\ (i = smpl (a,j))`;
*)

(* This weaker condition ensures that the stream space is non-empty
   and that the sampled stream is of the right type *)

val STREAM_ABSTRACTION_def = Define `
  STREAM_ABSTRACTION smpl sstrm istrm =
    (?i. i IN istrm) /\ !x. x.inp IN istrm ==> smpl x IN sstrm`;

(*---------------------------------------------------------------------------
  - Immersions : General and Uniform ----------------------------------------
  ---------------------------------------------------------------------------*)

val IMMERSION_def = Define `
  IMMERSION imm = !x:(('a,'b) state_inp). FREE_IMMERSION (imm x)`;

val IMMERSION = REWRITE_RULE [FREE_IMMERSION_def] IMMERSION_def;

val PUIMMERSION_def = Define `
  PUIMMERSION imm f dur =
    ((!x:(('a,'b) state_inp). 0 < dur x) /\
     (!x. imm x 0 = 0) /\
     (!x t. imm x (SUC t) = dur (Pstate_out_state (f (imm x t) x)) + imm x t))`;

val PUNIFORM_def = Define`
  PUNIFORM imm f = ?dur. PUIMMERSION imm f dur`;

(*---------------------------------------------------------------------------
  - Correctness Definitions -------------------------------------------------
  ---------------------------------------------------------------------------*)

val PCORRECT_def = Define `
  PCORRECT spec impl imm abs osmpl ismpl sstrm istrm =
    IMMERSION imm /\
    DATA_ABSTRACTION abs (state_out_state o state_inp_state o (impl 0))
                         (state_out_state o state_inp_state o (spec 0)) /\
    STREAM_ABSTRACTION ismpl sstrm istrm /\
    (!x. x.inp IN istrm ==>
       let y = <| state := abs x.state; inp:= ismpl x|> in
       (!t. ((spec t y).state).state = abs ((impl (imm x t) x).state).state) /\
       (POUTPUT spec y = osmpl (x,POUTPUT impl x)))`;

(*---------------------------------------------------------------------------
  - Time-Consistent State Functions -----------------------------------------
  ---------------------------------------------------------------------------*)

val PTCON_def = Define `
  PTCON f strm = !t1 t2 x:('a,'b) state_inp.
     x.inp IN strm ==>
     (f t2 x).inp IN strm /\
     (Pstate_out_state (f (t1 + t2) x) =
        Pstate_out_state (f t1 (Pstate_out_state (f t2 x))))`;

val PTCON_IMMERSION_def = Define `
  PTCON_IMMERSION f imm strm =
    !t1:num t2 x:('a,'b) state_inp.
      x.inp IN strm ==>
      let s2 = imm x t2 in
      let x2 = Pstate_out_state (f s2 x) in
      let s1 = imm x2 t1 in
        x2.inp IN strm /\
        (Pstate_out_state (f (s1 + s2) x) = Pstate_out_state (f s1 x2))`;

val FST_Pstate_out_state = prove(
  `!x. (Pstate_out_state x).state = (state_inp_state x).state`,
  SIMP_TAC (srw_ss()) [Pstate_out_state]);

val SND_Pstate_out_state = prove(
  `!x. (Pstate_out_state x).inp = x.inp`,
  SIMP_TAC (srw_ss()) [Pstate_out_state]);

val PTCON_IMMERSION =
  SIMP_RULE (bool_ss++boolSimps.LET_ss) [SND_Pstate_out_state]
  PTCON_IMMERSION_def;

(*---------------------------------------------------------------------------
  - Time-Consistent Sampling ------------------------------------------------
  ---------------------------------------------------------------------------*)

val PTCON_SMPL_def = Define `
  PTCON_SMPL smpl imm f strm =
    !t x. x.inp IN strm ==>
           (smpl (Pstate_out_state (f (imm x t) x)) = ADVANCE t (smpl x))`;

(*---------------------------------------------------------------------------
  - Uniform Immersions are Immersions ---------------------------------------
  ---------------------------------------------------------------------------*)

val SUC_COMM_LEMMA =
  prove(`!t p. t + (SUC p + 1) = SUC (t + (p + 1))`,ARITH_TAC);

val PUIMMERSION_MONO_LEMMA = prove(
  `!imm f dur a i t. PUIMMERSION imm f dur ==> imm x t < imm x (SUC t)`,
  RW_TAC bool_ss [PUIMMERSION_def]
    \\ ONCE_REWRITE_TAC [GSYM PAIR]
    \\ ASM_SIMP_TAC bool_ss [ADD_COMM,LESS_NOT_EQ,LESS_ADD_NONZERO]);

val PUIMMERSION_MONO_LEMMA2 = prove(
  `!imm f dur a i t p. PUIMMERSION imm f dur ==> imm x t < imm x (t + (p + 1))`,
  REPEAT STRIP_TAC
   \\ IMP_RES_TAC PUIMMERSION_MONO_LEMMA
   \\ Induct_on `p`
   >- ASM_REWRITE_TAC [SYM ONE,GSYM ADD1,PUIMMERSION_MONO_LEMMA]
   \\ FULL_SIMP_TAC bool_ss
        [SUC_COMM_LEMMA,LESS_IMP_LESS_ADD,ADD_COMM,PUIMMERSION_def]);

val PUIMMERSION_IS_IMMERSION_LEMMA = prove(
  `!imm f dur. PUIMMERSION imm f dur ==> IMMERSION imm`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC PUIMMERSION_MONO_LEMMA2
    \\ FULL_SIMP_TAC bool_ss [PUIMMERSION_def]
    \\ RW_TAC bool_ss [IMMERSION]
    \\ IMP_RES_TAC LESS_ADD_1
    \\ ASM_REWRITE_TAC [PUIMMERSION_MONO_LEMMA2]);

val PUNIFORM_IMP_IMMERSION = prove(
  `!imm f. PUNIFORM imm f ==> IMMERSION imm`,
  PROVE_TAC [PUNIFORM_def,PUIMMERSION_IS_IMMERSION_LEMMA]);

val PUIMMERSION_ONE = prove(
  `!f init out imm dur.
     IS_PMAP_INIT f init out /\ PUIMMERSION imm f dur ==>
     !x. imm x 1 = dur (Pstate_out_state (PINIT init out x))`,
  RW_TAC bool_ss [PUIMMERSION_def,IS_PMAP_INIT_def,PMAP_def,ONE,ADD_0]
    \\ ASM_REWRITE_TAC []);

(*---------------------------------------------------------------------------
  - Paired Map Results ------------------------------------------------------
  ---------------------------------------------------------------------------*)

val ADVANCE_ZERO = store_thm("ADVANCE_ZERO",
  `!i. ADVANCE 0 i = i`,
  REWRITE_TAC [ADD,FUN_EQ_THM,ADVANCE_def]);

val ADVANCE_COMP = store_thm("ADVANCE_COMP",
  `!t1 t2 i. ADVANCE (t1 + t2) i = ADVANCE t1 (ADVANCE t2 i)`,
  SIMP_TAC arith_ss [FUN_EQ_THM,ADVANCE_def]);

val ADVANCE_ONE = save_thm("ADVANCE_ONE",
  (GEN_ALL o REWRITE_RULE [GSYM SUC_ONE_ADD] o SPECL [`1`,`t`]) ADVANCE_COMP);

val PMAP2 = prove(
  `!f. IS_PMAP f ==> !t x. (f t x).inp = ADVANCE t x.inp`,
  RW_TAC bool_ss [IS_PMAP_def,PMAP_def,PINIT_def,PNEXT_def]
    \\ Induct_on `t`
    \\ ASM_SIMP_TAC (srw_ss()) [ADVANCE_ZERO,ADVANCE_ONE,ADVANCE_def]);

val STATE_FUNPOW_LEMMA = prove(
  `!f init next out. PMAP f init next out ==>
     (!t x. f t x = FUNPOW (PNEXT next out) t (PINIT init out x))`,
  RW_TAC bool_ss [PMAP_def]
    \\ Induct_on `t`
    \\ ASM_REWRITE_TAC [FUNPOW,FUNPOW_THM]);

val PMAP_INIT = prove(
  `!f init. PMAP f init next out ==> (f 0 = PINIT init out)`,
  RW_TAC bool_ss [PMAP_def]
    \\ REWRITE_TAC [FUN_EQ_THM]
    \\ ASM_SIMP_TAC std_ss []);

(*---------------------------------------------------------------------------
  - Time-Consistency Results ------------------------------------------------
  ---------------------------------------------------------------------------*)

val PNEXT_OUT_FREE = prove(
  `!next out a b. (Pstate_out_state a = Pstate_out_state b) ==>
         (PNEXT next out a = PNEXT next out b)`,
  SIMP_TAC (srw_ss()) [PNEXT_def,Pstate_out_state]);

val FUNPOW_PNEXT_OUT_FREE = prove(
  `!t x next out. (Pstate_out_state (PINIT init out (Pstate_out_state x)) =
                   Pstate_out_state x) ==>
         (Pstate_out_state (FUNPOW (PNEXT next out) t
            (PINIT init out (Pstate_out_state x))) =
          Pstate_out_state (FUNPOW (PNEXT next out) t x))`,
  Induct \\ RW_TAC (srw_ss()) [FUNPOW,PNEXT_def,PINIT_def,Pstate_out_state]);

val PTCON_THM = prove(
  `!strm f init out.  IS_PMAP_INIT f init out /\
     (!t x. x.inp IN strm ==>
        (ADVANCE t x.inp) IN strm /\
        (Pstate_out_state (PINIT init out (Pstate_out_state (f t x))) =
         Pstate_out_state (f t x))) ==>
     PTCON f strm`,
  RW_TAC bool_ss [PTCON_def,IS_PMAP_INIT_def]
    THENL [
      `IS_PMAP f` by PROVE_TAC [IS_PMAP_def]
        \\ IMP_RES_TAC PMAP2 \\ ASM_SIMP_TAC bool_ss [],
      FULL_SIMP_TAC bool_ss [PMAP_def]
        \\ Induct_on `t1` \\ ASM_SIMP_TAC arith_ss [ADD_CLAUSES,ADVANCE_def]
        \\ ISPECL_THEN [`next`,`out`] IMP_RES_TAC PNEXT_OUT_FREE
        \\ PROVE_TAC []]);

(*
 |- !strm h f.
      IS_PMAP_INIT f I out /\
      (!t x. x.inp IN strm ==> ADVANCE t x.inp IN strm) ==> PTCON f strm
*)

val PTCON_I_THM =
  (GEN_ALL o SIMP_RULE (srw_ss()++boolSimps.LET_ss)
    [PINIT_def,I_THM,PAIR,Pstate_out_state] o
   SPECL [`strm`,`f`,`I`]) PTCON_THM;

val PTCON_IMP_PTCON_IMMERSION = prove(
  `!strm f. PTCON f strm ==> !imm. PTCON_IMMERSION f imm strm`,
  RW_TAC bool_ss [PTCON_def,PTCON_IMMERSION] \\ PROVE_TAC []);

val PTCON_IMMERSION_PTCON = prove(
  `!strm f. PTCON_IMMERSION f (\a t. t) strm = PTCON f strm`,
  REPEAT STRIP_TAC \\ EQ_TAC \\
    SIMP_TAC bool_ss [PTCON_IMP_PTCON_IMMERSION,PTCON_def,PTCON_IMMERSION]);

val PTCON_IMMERSION_LEMMA = prove(
  `!strm f init out imm. IS_PMAP_INIT f init out /\ IMMERSION imm ==>
     (PTCON_IMMERSION f imm strm =
      !t x. x.inp IN strm ==>
        (ADVANCE (imm x t) x.inp) IN strm /\
        (Pstate_out_state (PINIT init out (Pstate_out_state (f (imm x t) x))) =
         Pstate_out_state (f (imm x t) x)))`,
  RW_TAC bool_ss [IS_PMAP_INIT_def,IMMERSION,PTCON_IMMERSION]
   \\ EQ_TAC \\ REPEAT STRIP_TAC
   THENL [
     `IS_PMAP f` by PROVE_TAC [IS_PMAP_def]
       \\ PAT_X_ASSUM `!t1:num t2 x. P`
            (fn th => ASSUME_TAC (GSYM (SPECL [`0`,`t`] th)))
       \\ IMP_RES_TAC PMAP2
       \\ POP_ASSUM (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]))
       \\ ASM_SIMP_TAC bool_ss [],
     PAT_X_ASSUM `!t1:num t2 x. P`
            (fn th => ASSUME_TAC (GSYM (SPECL [`0`,`t`] th)))
       \\ PAT_X_ASSUM `!x. a /\ b`
            (fn th => RULE_ASSUM_TAC (SIMP_RULE arith_ss [th]))
       \\ RULE_ASSUM_TAC (SIMP_RULE bool_ss [PMAP_def])
       \\ PAT_X_ASSUM `(!x. f 0 x = PINIT init out x) /\ y`
            (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]))
       \\ ASM_SIMP_TAC bool_ss [],
     `IS_PMAP f` by PROVE_TAC [IS_PMAP_def]
       \\ IMP_RES_TAC PMAP2
       \\ ASM_SIMP_TAC bool_ss [],
     IMP_RES_TAC STATE_FUNPOW_LEMMA
       \\ ASM_REWRITE_TAC [FUNPOW_COMP]
       \\ POP_ASSUM (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]))
       \\ METIS_TAC [FUNPOW_PNEXT_OUT_FREE]]);

val PTCON_IMMERSION_LEMMA2 = prove(
  `!strm f init out imm. IS_PMAP_INIT f init out /\ IMMERSION imm /\
     PTCON_IMMERSION f imm strm ==>
    (!t x. x.inp IN strm ==> (ADVANCE (imm x t) x.inp) IN strm /\
      (Pstate_out_state (PINIT init out (Pstate_out_state (f (imm x t) x))) =
      Pstate_out_state (f (imm x t) x)))`,
  PROVE_TAC [PTCON_IMMERSION_LEMMA]);

val PTCON_IMMERSION_LEMMA3 = prove(
  `!strm f imm. IS_PMAP f /\ IMMERSION imm /\ PTCON_IMMERSION f imm strm ==>
    (!x. x.inp IN strm ==>
      (!t1 t2. Pstate_out_state (f t1 (Pstate_out_state (f (imm x t2) x))) =
               Pstate_out_state (f (t1 + imm x t2) x)))`,
  RW_TAC std_ss [IS_PMAP_def]
    \\ IMP_RES_TAC STATE_FUNPOW_LEMMA
    \\ ONCE_ASM_REWRITE_TAC []
    \\ `IS_PMAP_INIT f init out` by PROVE_TAC [IS_PMAP_INIT_def]
    \\ IMP_RES_TAC PTCON_IMMERSION_LEMMA2
    \\ METIS_TAC [GSYM FUNPOW_COMP,FUNPOW_PNEXT_OUT_FREE]);

(*---------------------------------------------------------------------------
  - Input Stream Sampling One-Step Theorem ----------------------------------
  ---------------------------------------------------------------------------*)

val STRM_ABS_THM = prove(
  `!smpl sstrm istrm.  STREAM_ABSTRACTION smpl sstrm istrm ==>
      !x. x.inp IN istrm ==> (smpl x) IN sstrm`,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [STREAM_ABSTRACTION_def,IN_DEF]);

(*
val TC_STRM_ONE_STEP_THM = prove(
  `!strm. (!t i. i IN strm ==> (ADVANCE t i)) IN strm =
            (!i. i IN strm ==> (ADVANCE 1 i) IN strm)`,
  STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
    >- ASM_SIMP_TAC bool_ss []
    \\ Induct_on `t`
    \\ ASM_SIMP_TAC bool_ss [ADVANCE_ZERO,ADVANCE_ONE]
);
*)

(*---------------------------------------------------------------------------
  - Time-Consistency One-Step Theorems --------------------------------------
  ---------------------------------------------------------------------------*)

val IS_PMAP_THM = prove(
  `!f. IS_PMAP f = ?init out. IS_PMAP_INIT f init out`,
  REWRITE_TAC [IS_PMAP_def,IS_PMAP_INIT_def] \\ PROVE_TAC []
);

val SPLIT_ITER_LEMMA = prove(
  `!f init next out imm dur. PMAP f init next out /\ PUIMMERSION imm f dur ==>
    (!t x. f (dur (Pstate_out_state
         (PINIT init out (Pstate_out_state (f (imm x t) x)))) + imm x t) x =
       FUNPOW (PNEXT next out) (imm (Pstate_out_state (f (imm x t) x)) 1)
         (f (imm x t) x))`,
  REPEAT STRIP_TAC
    \\ `IS_PMAP_INIT f init out` by PROVE_TAC [IS_PMAP_INIT_def]
    \\ IMP_RES_TAC (GSYM PUIMMERSION_ONE)
    \\ POP_ASSUM (fn th => REWRITE_TAC [th])
    \\ IMP_RES_TAC STATE_FUNPOW_LEMMA
    \\ ASM_REWRITE_TAC [FUNPOW_COMP]);

val SPLIT_ITER_LEMMA2 = prove(
  `!t x f init out imm dur. IS_PMAP_INIT f init out /\ PUNIFORM imm f /\
     (Pstate_out_state (PINIT init out (Pstate_out_state (f (imm x t) x))) =
      Pstate_out_state (f (imm x t) x)) ==>
     (imm x (SUC t) = imm (Pstate_out_state (f (imm x t) x)) 1 + imm x t)`,
  RW_TAC bool_ss [IS_PMAP_INIT_def,PMAP_def,PUNIFORM_def,PUIMMERSION_def,ONE]
    \\ ASM_SIMP_TAC std_ss [ADD_0]);

val PTCON_IMMERSION_ONE_STEP_THM = prove(
  `!strm f init out imm. IS_PMAP_INIT f init out /\ PUNIFORM imm f ==>
   (PTCON_IMMERSION f imm strm =
     (!x. x.inp IN strm ==>
        (Pstate_out_state (PINIT init out (Pstate_out_state (f (imm x 0) x))) =
         Pstate_out_state (f (imm x 0) x))) /\
     (!x. x.inp IN strm ==>
        (ADVANCE (imm x 1) x.inp) IN strm /\
        (Pstate_out_state (PINIT init out (Pstate_out_state (f (imm x 1) x))) =
         Pstate_out_state (f (imm x 1) x))))`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC PUNIFORM_IMP_IMMERSION
    \\ EQ_TAC \\ STRIP_TAC
    \\ ASM_SIMP_TAC bool_ss [PTCON_IMMERSION_LEMMA2]
    \\ IMP_RES_TAC PTCON_IMMERSION_LEMMA
    >- RW_TAC bool_ss []
    \\ NTAC 3 (POP_ASSUM (K ALL_TAC))
    \\ POP_ASSUM (fn th => REWRITE_TAC [th])
    \\ Induct
    >- FULL_SIMP_TAC bool_ss [PUNIFORM_def,PUIMMERSION_def,ADVANCE_ZERO]
    \\ REPEAT STRIP_TAC
    THENL [
      `imm x (SUC t) = imm (Pstate_out_state (f (imm x t) x)) 1 + imm x t`
        by PROVE_TAC [SPLIT_ITER_LEMMA2]
        \\ `IS_PMAP f` by PROVE_TAC [IS_PMAP_THM]
        \\ IMP_RES_TAC PMAP2
        \\ ASM_SIMP_TAC bool_ss [ADVANCE_COMP]
        \\ METIS_TAC [SND_Pstate_out_state],
      FULL_SIMP_TAC bool_ss [PUNIFORM_def,IS_PMAP_INIT_def]
        \\ PAT_X_ASSUM `PUIMMERSION imm f dur`
             (fn th => REWRITE_TAC [REWRITE_RULE [PUIMMERSION_def] th] \\
                       ASSUME_TAC th)
        \\ PAT_X_ASSUM
             `!x. x.inp IN strm ==> (ADVANCE (imm x t) x.inp) IN strm /\ P`
             (fn th => ASSUME_TAC th \\ (ASSUME_TAC o GSYM o SPEC `x`) th)
        \\ POP_ASSUM IMP_RES_TAC
        \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th] \\ ASSUME_TAC (GSYM th))
        \\ IMP_RES_TAC SPLIT_ITER_LEMMA
        \\ POP_ASSUM (fn th => REWRITE_TAC [th])
        \\ IMP_RES_TAC FUNPOW_PNEXT_OUT_FREE
        \\ POP_ASSUM (fn th => (ONCE_REWRITE_TAC [GSYM th] \\ ASSUME_TAC th))
        \\ IMP_RES_TAC STATE_FUNPOW_LEMMA
        \\ POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
        \\ `IS_PMAP f` by PROVE_TAC [IS_PMAP_def]
        \\ IMP_RES_TAC PMAP2
        \\ METIS_TAC [SND_Pstate_out_state]]);

val lem = prove(
  `!istrm sstrm smpl f init out imm.
     STREAM_ABSTRACTION smpl sstrm istrm /\ IS_PMAP_INIT f init out /\
     PUNIFORM imm f ==>
     ((!x. x.inp IN istrm ==>
       (Pstate_out_state (PINIT init out (Pstate_out_state (f (imm x 0) x))) =
        Pstate_out_state (f (imm x 0) x))) =
    !x. Pstate_out_state (PINIT init out (Pstate_out_state (f (imm x 0) x))) =
        Pstate_out_state (f (imm x 0) x))`,
  RW_TAC bool_ss [IS_PMAP_INIT_def,PMAP_def]
    \\ IMP_RES_TAC STREAM_ABSTRACTION_def
    \\ IMP_RES_TAC PUNIFORM_IMP_IMMERSION
    \\ FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss) [IMMERSION,PINIT_def]
    \\ EQ_TAC \\ REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [Pstate_out_state]
    \\ POP_ASSUM (ISPEC_THEN  `<| state := x.state; inp := i |>`
         (IMP_RES_TAC o SIMP_RULE (srw_ss()) []))
    \\ FULL_SIMP_TAC (srw_ss()) [Pstate_out_state]);

val PTCON_IMMERSION_ONE_STEP_THM2 = prove(
  `!istrm sstrm smpl f init out imm.
    STREAM_ABSTRACTION smpl sstrm istrm /\ IS_PMAP_INIT f init out /\
    PUNIFORM imm f ==>
    (PTCON_IMMERSION f imm istrm =
    (!x. (Pstate_out_state (PINIT init out (Pstate_out_state (f (imm x 0) x))) =
          Pstate_out_state (f (imm x 0) x))) /\
    (!x. x.inp IN istrm ==>
       (ADVANCE (imm x 1) x.inp) IN istrm /\
       (Pstate_out_state (PINIT init out (Pstate_out_state (f (imm x 1) x))) =
        Pstate_out_state (f (imm x 1) x))))`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC PTCON_IMMERSION_ONE_STEP_THM
    \\ NTAC 5 (POP_ASSUM (K ALL_TAC))
    \\ ISPEC_THEN `istrm` IMP_RES_TAC lem
    \\ RW_TAC bool_ss []);

val PUNIFORM_ID = prove(
  `!f. PUNIFORM (\a t. t) f`,
  RW_TAC bool_ss [PUNIFORM_def] \\ EXISTS_TAC `\a. 1`
    \\ REWRITE_TAC [PUIMMERSION_def] \\ SIMP_TAC arith_ss []);

(*
 |- !strm out init f.
       IS_PMAP_INIT f init out ==>
       (PTCON f strm =
        (!x.
           x.inp IN strm ==>
           (Pstate_out_state (PINIT init out (Pstate_out_state (f 0 x))) =
            Pstate_out_state (f 0 x))) /\
        !x.
          x.inp IN strm ==>
          ADVANCE 1 x.inp IN strm /\
          (Pstate_out_state (PINIT init out (Pstate_out_state (f 1 x))) =
           Pstate_out_state (f 1 x)))
*)
val PTCON_ONE_STEP_THM =
  (GEN_ALL o SIMP_RULE std_ss [PUNIFORM_ID,PTCON_IMMERSION_PTCON] o
   SPECL [`strm`,`f`,`init`,`out`,`\a t. t`]) PTCON_IMMERSION_ONE_STEP_THM;

val lem = prove(
  `!strm f imm dur.
     IS_PMAP f /\ PUNIFORM imm f /\ PTCON_IMMERSION f imm strm ==>
     !t x. x.inp IN strm ==> (imm (Pstate_out_state (f 0 x)) t = imm x t)`,
  RW_TAC bool_ss [PUNIFORM_def,PUIMMERSION_def]
   \\ Induct_on `t` >- ASM_REWRITE_TAC []
   \\ FULL_SIMP_TAC bool_ss [PTCON_IMMERSION]
   \\ PAT_X_ASSUM `!t1 t2 x. P` (SPECL_THEN [`t`,`0`,`x`] IMP_RES_TAC)
   \\ PAT_X_ASSUM `!x. imm x 0 = 0`
        (fn th => RULE_ASSUM_TAC (REWRITE_RULE [ADD_CLAUSES,th]))
   \\ POP_ASSUM (SPEC_THEN `t` ASSUME_TAC)
   \\ PAT_X_ASSUM `imm (Pstate_out_state (f 0 x)) t = imm x t`
        (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]))
   \\ POP_ASSUM (fn th => REWRITE_TAC [GSYM th]));

val PTCON_IMMERSION_COR = prove(
  `!strm f imm.
    IS_PMAP f /\ PUNIFORM imm f /\ PTCON_IMMERSION f imm strm ==>
     !t1 t2 x. x.inp IN strm ==>
     (imm x (t1 + t2) = imm (Pstate_out_state (f (imm x t1) x)) t2 + imm x t1)`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC lem
    \\ FULL_SIMP_TAC bool_ss [PUNIFORM_def,PUIMMERSION_def]
    \\ Induct_on `t2` \\ ASM_REWRITE_TAC [ADD_CLAUSES]
    \\ RW_TAC arith_ss []
    \\ FULL_SIMP_TAC bool_ss [PTCON_IMMERSION]
    \\ PAT_X_ASSUM `!t1 t2 x. P` (SPECL_THEN [`t2`,`t1`,`x`] IMP_RES_TAC)
    \\ POP_ASSUM (fn th => SIMP_TAC arith_ss [GSYM th]));

(*---------------------------------------------------------------------------
  - Correctnes One-Step Theorems --------------------------------------------
  ---------------------------------------------------------------------------*)

val ONE_STEP_LEMMA = prove(
  `!strm f imm dur.
     IS_PMAP f /\ PUNIFORM imm f /\ PTCON_IMMERSION f imm strm ==>
     (!t x. x.inp IN strm ==>
       (imm x (SUC t) = (imm (Pstate_out_state (f (imm x t) x)) 1 + imm x t)))`,
  RW_TAC bool_ss [IS_PMAP_THM]
   \\ IMP_RES_TAC PUNIFORM_IMP_IMMERSION
   \\ IMP_RES_TAC PTCON_IMMERSION_LEMMA2
   \\ FULL_SIMP_TAC bool_ss [PUNIFORM_def]
   \\ IMP_RES_TAC PUIMMERSION_ONE
   \\ FULL_SIMP_TAC bool_ss [PUIMMERSION_def]);

val lem = prove(
  `!f init out. IS_PMAP_INIT f init out ==>
     (!t x. ((f t x).state).out = out ((Pstate_out_state (f t x)).state))`,
  RW_TAC std_ss [IS_PMAP_INIT_def,PMAP_def]
    \\ Cases_on `x` \\ SPEC_TAC (`t`,`t`) \\ Induct
    \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss)
         [PINIT_def,PNEXT_def,Pstate_out_state]);

val POUPUT_ONE_STEP_THM = prove(
  `!sstrm istrm spec impl imm abs ismpl f.
     IS_PMAP spec /\ IS_PMAP impl /\
     PUNIFORM imm impl /\
     STREAM_ABSTRACTION ismpl sstrm istrm /\
     PTCON spec sstrm /\ PTCON_IMMERSION impl imm istrm /\
     PTCON_SMPL ismpl imm impl istrm /\
     (!x. x.inp IN istrm ==>
        (!t. ((spec t <| state := abs x.state; inp := ismpl x|>).state).state =
               abs ((impl (imm x t) x).state).state)) ==>
     ((!x. x.inp IN istrm ==>
         (POUTPUT spec <| state := abs x.state; inp := ismpl x|> =
         (\(x,i) t. f (Pstate_out_state (impl (imm x t) x))
                      ((PACK (imm x) i) t)) (x,POUTPUT impl x))) =
      (!x. x.inp IN istrm ==>
         (POUTPUT spec <| state := abs x.state; inp := ismpl x|> 0 =
         (\(x,i). f (Pstate_out_state (impl (imm x 0) x))
                    ((PACK (imm x) i) 0)) (x,POUTPUT impl x))))`,
  RW_TAC std_ss []
    \\ EQ_TAC \\ RW_TAC std_ss []
    \\ REWRITE_TAC [FUN_EQ_THM]
    \\ X_GEN_TAC `t`
    \\ IMP_RES_TAC IS_PMAP_THM
    \\ PAT_X_ASSUM `!x. a ==> (POUTPUT spec b 0 = c)`
         (SPEC_THEN `Pstate_out_state (impl (imm x t) x)` ASSUME_TAC)
    \\ PAT_X_ASSUM `!x. a ==> b` (SPEC_THEN `x` IMP_RES_TAC)
    \\ POP_ASSUM (SPEC_THEN `t` (fn th => FULL_SIMP_TAC std_ss
         [SYM th,FST_Pstate_out_state,PTCON_def,POUTPUT_def,
          MAP_STRM_def,PACK_def]))
    \\ IMP_RES_TAC lem
    \\ `!x t. (spec t x).inp = ADVANCE t x.inp` by IMP_RES_TAC PMAP2
    \\ `ismpl x IN sstrm` by METIS_TAC [STREAM_ABSTRACTION_def]
    \\ PAT_X_ASSUM `!t1 t2 x. P`
         (SPECL_THEN [`0`,`t`,`<| state := abs x.state; inp := ismpl x |>`]
            (IMP_RES_TAC o SIMP_RULE (srw_ss()) []))
    \\ FULL_SIMP_TAC std_ss [PTCON_SMPL_def]
    \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
    \\ PAT_X_ASSUM `!t x. a ==> b` (SPECL_THEN [`t`,`x`]
         (IMP_RES_TAC o GSYM o SIMP_RULE std_ss [ADVANCE_ZERO]))
    \\ POP_ASSUM (SPEC_THEN `t` (fn th => FULL_SIMP_TAC arith_ss
         [ADVANCE_def,SYM th]))
    \\ PAT_X_ASSUM `!x t. y = ADVANCE t x.inp`
         (SPECL_THEN [`<| state := abs x.state; inp := ismpl x |>`,`t`]
            (fn th => SUBST_ALL_TAC (SIMP_RULE (srw_ss()) [] (GSYM th))))
    \\ IMP_RES_TAC ONE_STEP_LEMMA \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [ADD1])
    \\ IMP_RES_TAC PUNIFORM_IMP_IMMERSION
    \\ IMP_RES_TAC PTCON_IMMERSION_LEMMA3 \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ FULL_SIMP_TAC (srw_ss()) [PTCON_IMMERSION,IMMERSION_def,
         FREE_IMMERSION_def,IMM_LEN_def]
    \\ FULL_SIMP_TAC std_ss [FST_Pstate_out_state,SND_Pstate_out_state,
        GSYM Pstate_out_state]);

val lem = prove(
  `!x y. x.inp IN y ==> (Pstate_out_state x).inp IN y`,
  SIMP_TAC (srw_ss()) [Pstate_out_state]);

val PONE_STEP_THM = prove(
  `!sstrm istrm spec impl imm abs osmpl ismpl f .
     IS_PMAP spec /\ IS_PMAP impl /\ PUNIFORM imm impl /\
     DATA_ABSTRACTION abs (state_out_state o state_inp_state o (impl 0))
                          (state_out_state o state_inp_state o (spec 0)) /\
     STREAM_ABSTRACTION ismpl sstrm istrm /\
     (osmpl = (\(x,i) t. f (Pstate_out_state (impl (imm x t) x))
                ((PACK (imm x) i) t))) /\
     PTCON spec sstrm /\ PTCON_IMMERSION impl imm istrm /\
     PTCON_SMPL ismpl imm impl istrm /\
     (!x. x.inp IN istrm ==>
        (((spec 0 <| state := abs x.state; inp := ismpl x|>).state).state =
           abs ((impl (imm x 0) x).state).state)) /\
     (!x. x.inp IN istrm ==>
        (((spec 1 <| state := abs x.state; inp := ismpl x|>).state).state =
           abs ((impl (imm x 1) x).state).state)) /\
     (!x. x.inp IN istrm ==>
        (POUTPUT spec <| state := abs x.state; inp := ismpl x|> 0 =
         osmpl (x,POUTPUT impl x) 0)) ==>
     PCORRECT spec impl imm abs osmpl ismpl sstrm istrm`,
 REPEAT STRIP_TAC
    \\ IMP_RES_TAC ONE_STEP_LEMMA
    \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ RW_TAC bool_ss [PCORRECT_def]
    THENL [
       IMP_RES_TAC PUNIFORM_IMP_IMMERSION,
       PAT_X_ASSUM `IS_PMAP impl` (K ALL_TAC),
       SPECL_THEN [`sstrm`,`istrm`,`spec`,`impl`,`imm`,`abs`,`ismpl`,`f`]
              ASSUME_TAC POUPUT_ONE_STEP_THM
         \\ PAT_X_ASSUM `IS_PMAP impl` (fn th => FULL_SIMP_TAC bool_ss [th])
         \\ PAT_X_ASSUM `IS_PMAP spec`
              (fn th => FULL_SIMP_TAC bool_ss [th] \\ ASSUME_TAC th)
         \\ PAT_X_ASSUM `PUNIFORM imm impl`
              (fn th => FULL_SIMP_TAC bool_ss [th] \\ ASSUME_TAC th)
         \\ PAT_X_ASSUM `STREAM_ABSTRACTION ismpl sstrm istrm`
              (fn th => FULL_SIMP_TAC bool_ss [th] \\ ASSUME_TAC th)
         \\ PAT_X_ASSUM `PTCON spec sstrm`
              (fn th => FULL_SIMP_TAC bool_ss [th] \\ ASSUME_TAC th)
         \\ PAT_X_ASSUM `PTCON_IMMERSION impl imm istrm`
              (fn th => FULL_SIMP_TAC bool_ss [th] \\ ASSUME_TAC th)
         \\ PAT_X_ASSUM `PTCON_SMPL ismpl imm impl istrm`
              (fn th => FULL_SIMP_TAC std_ss [th,MAP_STRM_def] \\ ASSUME_TAC th)
         \\ PAT_X_ASSUM `!x. a ==> (POUTPUT spec b 0 = c)`
              (fn th => FULL_SIMP_TAC bool_ss [th])
         \\ PAT_X_ASSUM `x.inp IN istrm` MP_TAC
         \\ SPEC_TAC (`x`,`x`)
         \\ PAT_X_ASSUM `a ==> b` MATCH_MP_TAC
         \\ REPEAT STRIP_TAC
    ]
    \\ Induct_on `t` >- ASM_SIMP_TAC bool_ss []
    \\ PAT_X_ASSUM `!x. x.inp IN istrm ==> !t. P` IMP_RES_TAC
    \\ POP_ASSUM (fn th => REWRITE_TAC [th])
    \\ PAT_X_ASSUM `PTCON_IMMERSION impl imm istrm`
         (fn th => IMP_RES_TAC (SIMP_RULE (srw_ss())
            [Pstate_out_state,CLOSED_PAIR_EQ,PTCON_IMMERSION] th))
    \\ POP_ASSUM (fn th => FULL_SIMP_TAC (srw_ss()) [GSYM Pstate_out_state])
    \\ POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM (fn th => ASSUME_TAC (MATCH_MP lem (SPEC `t` th)))
    \\ PAT_X_ASSUM `!x. x.inp IN istrm ==>
         (((spec 1 <| state := abs x.state; inp := smpl x|>).state).state =
          abs ((impl (imm x 1) x).state).state)`
         (fn th => IMP_RES_TAC (GSYM th) \\ POP_ASSUM (K ALL_TAC))
    \\ POP_ASSUM (fn th => REWRITE_TAC [ONE,th])
    \\ RULE_ASSUM_TAC (REWRITE_RULE [PTCON_SMPL_def])
    \\ PAT_X_ASSUM `!t x. P` (fn th => ASM_SIMP_TAC (srw_ss()) [th])
    \\ PAT_X_ASSUM `IS_PMAP spec` (fn th => ASSUME_TAC (MATCH_MP (GSYM PMAP2) th))
    \\ POP_ASSUM (ISPECL_THEN [`t`,`<| state := abs x.state; inp := ismpl x|>`]
         (SUBST1_TAC o SIMP_RULE (srw_ss()) []))
    \\ POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM (fn th => REWRITE_TAC
         [(SYM o GEN_REWRITE_RULE (RAND_CONV o DEPTH_CONV) empty_rewrites
           [GSYM FST_Pstate_out_state]) th])
    \\ IMP_RES_TAC STRM_ABS_THM
    \\ RULE_ASSUM_TAC (REWRITE_RULE [PTCON_def])
    \\ PAT_X_ASSUM `!t1 t2 x. P` (fn th => IMP_RES_TAC
          ((GSYM o REWRITE_RULE [ONE] o SIMP_RULE (srw_ss()) [] o
            SPECL [`SUC 0`,`t`,
         `<|state := abs (x:('e, 'b) state_inp).state; inp := ismpl x|>`]) th))
    \\ FULL_SIMP_TAC arith_ss
         [GSYM FST_Pstate_out_state,GSYM SND_Pstate_out_state,ADD1]
    \\ FULL_SIMP_TAC (srw_ss()) [Pstate_out_state]);

(* -- *)
(* -- *)
(* -- *)
(* -- *)

(*---------------------------------------------------------------------------
  - Iterated Maps -----------------------------------------------------------
  ---------------------------------------------------------------------------*)

val IMAP_def = Define `
  IMAP f init next out =
    (!x. (f 0 x).state = init x.state) /\
    (!t x. (f (SUC t) x).state = next (f t x).state (x.inp t)) /\
    (!t x. (f t x).out = out (f t x).state)`;

val IS_IMAP_INIT_def = Define`
  IS_IMAP_INIT f init = ?next out. IMAP f init next out`;

val IS_IMAP_def = Define`
  IS_IMAP f = ?init next out. IMAP f init next out`;

val SINIT_def = Define`
  SINIT init = \x. <| state := init x.state; inp := x.inp |>`;

val SNEXT_def = Define`
  SNEXT next =
    \x. <| state := next x.state (x.inp 0); inp := ADVANCE 1 x.inp |>`;

val SNEXT = store_thm("SNEXT",
  `!f s i. SNEXT f <|state := s; inp := i |> =
      <| state := f s (i 0); inp := ADVANCE 1 i |>`,
  RW_TAC std_ss [SNEXT_def]);

(*---------------------------------------------------------------------------
  - Uniform Immersions ------------------------------------------------------
  ---------------------------------------------------------------------------*)

val UIMMERSION_def = Define `
  UIMMERSION imm f dur =
    ((!x:('a,'b) state_inp. 0 < dur x) /\
     (!x. imm x 0 = 0) /\
     (!x t. imm x (SUC t) =
             dur <| state := (f (imm x t) x).state;
                     inp := ADVANCE (imm x t) x.inp |> + imm x t))`;

val UNIFORM_def = Define`
  UNIFORM imm f = ?dur. UIMMERSION imm f dur`;

(*---------------------------------------------------------------------------
  - Correctness Definitions -------------------------------------------------
  ---------------------------------------------------------------------------*)

val CORRECT_def = Define `
 CORRECT spec impl imm abs osmpl ismpl sstrm istrm =
  IMMERSION imm /\
  DATA_ABSTRACTION abs (state_out_state o impl 0) (state_out_state o spec 0) /\
  STREAM_ABSTRACTION ismpl sstrm istrm /\
  (!x. x.inp IN istrm ==> let y = <| state := abs x.state; inp := ismpl x |> in
     (!t. (spec t y).state = abs (impl (imm x t) x).state) /\
     (OUTPUT spec y = osmpl (x,OUTPUT impl x)))`;

val IS_CORRECT_def = Define`
  IS_CORRECT spec impl =
    ?imm abs osmpl ismpl sstrm istrm.
      CORRECT spec impl imm abs osmpl ismpl sstrm istrm`;

(*---------------------------------------------------------------------------
  - Time-Consistent State Functions -----------------------------------------
  ---------------------------------------------------------------------------*)

val TCON_def = Define `
  TCON f sstrm = !t1 t2 x:('a,'b) state_inp.
     x.inp IN sstrm ==>
     (ADVANCE t2 x.inp) IN sstrm /\
     ((f (t1 + t2) x).state =
      (f t1 <| state := (f t2 x).state; inp := ADVANCE t2 x.inp|>).state)`;

val TCON_IMMERSION_def = Define `
  TCON_IMMERSION f imm strm =
    !t1:num t2 x:('a,'b) state_inp.
      x.inp IN strm ==>
      let s2 = imm x t2 in
      let x2 = <| state := (f s2 x).state; inp := ADVANCE s2 x.inp |> in
      let s1 = imm x2 t1 in
        (ADVANCE s2 x.inp) IN strm /\
        ((f (s1 + s2) x).state = (f s1 x2).state)`;

val TCON_IMMERSION = save_thm("TCON_IMMERSION",
  SIMP_RULE (bool_ss++boolSimps.LET_ss) [] TCON_IMMERSION_def);

(*---------------------------------------------------------------------------
  - Time-Consistent Sampling ------------------------------------------------
  ---------------------------------------------------------------------------*)

val TCON_SMPL_def = Define `
  TCON_SMPL smpl imm f strm =
    !t x. x.inp IN strm ==>
          (smpl <| state := (f (imm x t) x).state;
                   inp := ADVANCE (imm x t) x.inp |> = ADVANCE t (smpl x))`;

(*---------------------------------------------------------------------------
  - Transfer over one-step results ------------------------------------------
  ---------------------------------------------------------------------------*)

val state_inp_component_equality = theorem "state_inp_component_equality";
val state_out_component_equality = theorem "state_out_component_equality";

val UIMMERSION_ONE = store_thm("UIMMERSION_ONE",
  `!f init out imm dur.
     IS_IMAP_INIT f init /\ UIMMERSION imm f dur ==>
     !x. imm x 1 = dur <| state := init x.state; inp := x.inp |>`,
  RW_TAC bool_ss [UIMMERSION_def,IS_IMAP_INIT_def,IMAP_def,
    ADVANCE_ZERO,ONE,ADD_0] \\ ASM_SIMP_TAC (srw_ss()) []);

val IMAP_PMAP = prove(
  `!f g init next out.
      IMAP f init next out /\ PMAP g init next out ==>
        (!t x. g t x = <| state := f t x; inp := ADVANCE t x.inp |>)`,
  RW_TAC bool_ss [PMAP_def,IMAP_def,PINIT_def,PNEXT_def]
    \\ Induct_on `t`
    \\ RW_TAC arith_ss [state_out_component_equality,ADVANCE_ZERO,
         ADVANCE_ONE,ADVANCE_def]);

val THE_PMAP = prove(
  `!init next out. PMAP (THE_PMAP init next out) init next out`,
  REWRITE_TAC [THE_PMAP_def,PMAP_def]);

val IMAP_UNIFORM = prove(
  `!f init next out imm. IMAP f init next out ==>
      (UNIFORM imm f = PUNIFORM imm (THE_PMAP init next out))`,
  RW_TAC bool_ss [UNIFORM_def,PUNIFORM_def]
   \\ ISPECL_THEN [`init`,`next`,`out`] ASSUME_TAC THE_PMAP
   \\ IMP_RES_TAC IMAP_PMAP
   \\ EQ_TAC \\ STRIP_TAC \\ EXISTS_TAC `dur`
   \\ FULL_SIMP_TAC (srw_ss()) [Pstate_out_state,PUIMMERSION_def,UIMMERSION_def]
);

val IMAP_TCON_IMMERSION = prove(
  `!strm f init next out imm. IMAP f init next out ==>
      (TCON_IMMERSION f imm strm =
      PTCON_IMMERSION (THE_PMAP init next out) imm strm)`,
  RW_TAC bool_ss [TCON_IMMERSION,PTCON_IMMERSION]
    \\ ISPECL_THEN [`init`,`next`,`out`] ASSUME_TAC THE_PMAP
    \\ IMP_RES_TAC IMAP_PMAP
    \\ EQ_TAC \\ REPEAT STRIP_TAC
    \\ PAT_X_ASSUM `!x t. THE_PMAP init next out t x =
          <| state := f t x; inp := ADVANCE t x.inp |>`
         (fn th => FULL_SIMP_TAC (srw_ss()) [Pstate_out_state,ADVANCE_COMP,th])
);

val TCON_IMMERSION_ONE_STEP_THM = store_thm("TCON_IMMERSION_ONE_STEP_THM",
  `!strm f init out imm . IS_IMAP_INIT f init /\ UNIFORM imm f ==>
    (TCON_IMMERSION f imm strm =
       (!x. x.inp IN strm ==>
          (init (f (imm x 0) x).state = (f (imm x 0) x).state)) /\
       (!x. x.inp IN strm ==> (ADVANCE (imm x 1) x.inp) IN strm /\
          (init (f (imm x 1) x).state = (f (imm x 1) x).state)))`,
  RW_TAC bool_ss [IS_IMAP_INIT_def]
    \\ ISPECL_THEN [`init`,`next`,`out`] ASSUME_TAC THE_PMAP
    \\ IMP_RES_TAC IMAP_PMAP
    \\ `IS_PMAP_INIT (THE_PMAP init next out) init out`
    by PROVE_TAC [IS_PMAP_INIT_def]
    \\ IMP_RES_TAC IMAP_UNIFORM
    \\ IMP_RES_TAC PTCON_IMMERSION_ONE_STEP_THM
    \\ NTAC 5 (POP_ASSUM (K ALL_TAC))
    \\ IMP_RES_TAC IMAP_TCON_IMMERSION \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss) [Pstate_out_state,PINIT_def]);

val UNIFORM_ID = prove(
  `!f. UNIFORM (\a t. t) f`,
  RW_TAC bool_ss [UNIFORM_def] \\ EXISTS_TAC `\a. 1`
    \\ REWRITE_TAC [UIMMERSION_def] \\ SIMP_TAC arith_ss []);

val TCON_IMP_TCON_IMMERSION = store_thm("TCON_IMP_TCON_IMMERSION",
  `!strm f. TCON f strm ==> !imm. TCON_IMMERSION f imm strm`,
  RW_TAC bool_ss [TCON_def,TCON_IMMERSION]);

val TCON_IMMERSION_TCON = prove(
  `!strm f. TCON_IMMERSION f (\a t. t) strm = TCON f strm`,
  REPEAT STRIP_TAC \\ EQ_TAC \\
    SIMP_TAC bool_ss [TCON_IMP_TCON_IMMERSION,TCON_def,TCON_IMMERSION]);

(*
 |- !strm out init f.
       IS_IMAP_INIT f init ==>
       (TCON f strm =
        (!x. SND x IN strm ==> (init (f 0 x).state = (f 0 x).state)) /\
        !x.
          SND x IN strm ==>
          ADVANCE 1 (SND x) IN strm /\
          (init (f 1 x).state = (f 1 x).state))
*)

val TCON_ONE_STEP_THM = save_thm("TCON_ONE_STEP_THM",
  (GEN_ALL o SIMP_RULE std_ss [UNIFORM_ID,TCON_IMMERSION_TCON] o
      SPECL [`strm`,`f`,`init`,`out`,`\a t. t`]) TCON_IMMERSION_ONE_STEP_THM);

(*
 |- !strm f.
       IS_IMAP_INIT f I ==>
       (TCON f strm = !x. SND x IN strm ==> ADVANCE 1 (SND x) IN strm)
*)

val TCON_I_THM = save_thm("TCON_I_THM",
  (GEN `strm` o GEN `f` o SIMP_RULE std_ss [I_THM] o
   SPECL [`strm`,`I`,`f`]) TCON_ONE_STEP_THM);

val IMAP_TCON = prove(
  `!sstrm f init next out. IMAP f init next out ==>
     (TCON f sstrm = PTCON (THE_PMAP init next out) sstrm)`,
  RW_TAC bool_ss [TCON_def,PTCON_def]
    \\ ISPECL_THEN [`init`,`next`,`out`] ASSUME_TAC THE_PMAP
    \\ IMP_RES_TAC IMAP_PMAP
    \\ EQ_TAC \\ RW_TAC (srw_ss()++boolSimps.LET_ss)
         [Pstate_out_state,ADVANCE_COMP]);

val TCON_IMMERSION_COR = store_thm("TCON_IMMERSION_COR",
  `!strm f imm dur.
     IS_IMAP f /\ UNIFORM imm f /\ TCON_IMMERSION f imm strm ==>
       !t1 t2 x.
           x.inp IN strm ==> (imm x (t1 + t2) =
              imm <| state := (f (imm x t1) x).state;
                     inp := ADVANCE (imm x t1) x.inp|> t2 + imm x t1)`,
  RW_TAC bool_ss [IS_IMAP_def]
    \\ ISPECL_THEN [`init`,`next`,`out`] ASSUME_TAC THE_PMAP
    \\ IMP_RES_TAC IMAP_PMAP
    \\ `IS_PMAP (THE_PMAP init next out)` by PROVE_TAC [IS_PMAP_def]
    \\ `PTCON_IMMERSION (THE_PMAP init next out) imm strm`
    by IMP_RES_TAC IMAP_TCON_IMMERSION
    \\ PAT_X_ASSUM `TCON_IMMERSION impl imm istrm` (K ALL_TAC)
    \\ `PUNIFORM imm (THE_PMAP init next out)` by IMP_RES_TAC IMAP_UNIFORM
    \\ PAT_X_ASSUM `UNIFORM imm impl` (K ALL_TAC)
    \\ IMP_RES_TAC (REWRITE_RULE [Pstate_out_state] PTCON_IMMERSION_COR)
    \\ FULL_SIMP_TAC (srw_ss()) []);

val IMAP_TCON_SMPL = prove(
  `!strm smpl imm f init next out. IMAP f init next out ==>
     (TCON_SMPL smpl imm f strm =
     PTCON_SMPL smpl imm (THE_PMAP init next out) strm)`,
  RW_TAC bool_ss [TCON_SMPL_def,PTCON_SMPL_def]
    \\ ISPECL_THEN [`init`,`next`,`out`] ASSUME_TAC THE_PMAP
    \\ IMP_RES_TAC IMAP_PMAP
    \\ ASM_SIMP_TAC (srw_ss()) [Pstate_out_state]);

val IMAP_DATA_ABSTRACTION = prove(
  `!abs f init1 next1 out1 g init2 next2 out2.
   IMAP f init1 next1 out1 /\ IMAP g init2 next2 out2 ==>
    (DATA_ABSTRACTION abs (state_out_state o (g 0)) (state_out_state o (f 0)) =
     DATA_ABSTRACTION abs
        (state_out_state o state_inp_state o (THE_PMAP init2 next2 out2 0))
        (state_out_state o state_inp_state o (THE_PMAP init1 next1 out1 0)))`,
  RW_TAC bool_ss [DATA_ABSTRACTION_def]
    \\ ISPECL_THEN [`init1`,`next1`,`out1`] ASSUME_TAC THE_PMAP
    \\ ISPECL_THEN [`init2`,`next2`,`out2`] ASSUME_TAC THE_PMAP
    \\ IMP_RES_TAC IMAP_PMAP
    \\ ASM_SIMP_TAC (srw_ss())
         [GSPEC_T,IN_UNIV,IMAGE_DEF,RANGE_def,Pstate_out_state]);

val IMAP_OUTPUT = prove(
  `!f init next out. IMAP f init next out ==>
      (!x. POUTPUT (THE_PMAP init next out) x = OUTPUT f x)`,
  REPEAT STRIP_TAC
    \\ REWRITE_TAC [FUN_EQ_THM,OUTPUT_def,POUTPUT_def]
    \\ ISPECL_THEN [`init`,`next`,`out`] ASSUME_TAC THE_PMAP
    \\ IMP_RES_TAC IMAP_PMAP
    \\ ASM_SIMP_TAC (srw_ss()) [Pstate_out_state]);

val IMAP_CORRECT = prove(
  `!sstrm istrm spec init1 next1 out1 impl init2 next2 out2 imm abs osmpl ismpl.
       IMAP spec init1 next1 out1 /\ IMAP impl init2 next2 out2 ==>
         (CORRECT spec impl imm abs osmpl ismpl sstrm istrm =
         PCORRECT (THE_PMAP init1 next1 out1) (THE_PMAP init2 next2 out2)
           imm abs osmpl ismpl sstrm istrm)`,
  RW_TAC bool_ss [CORRECT_def,PCORRECT_def]
    \\ ISPECL_THEN [`init1`,`next1`,`out1`] ASSUME_TAC THE_PMAP
    \\ ISPECL_THEN [`init2`,`next2`,`out2`] ASSUME_TAC THE_PMAP
    \\ IMP_RES_TAC IMAP_PMAP
    \\ IMP_RES_TAC IMAP_OUTPUT
    \\ ISPECL_THEN [`abs`,`spec`,`init1`,`next1`,`out1`,`impl`,
         `init2`,`next2`,`out2`] ASSUME_TAC IMAP_DATA_ABSTRACTION
    \\ RES_TAC \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ `IS_IMAP_INIT spec init1 /\ IS_IMAP_INIT impl init2`
    by METIS_TAC [IS_IMAP_INIT_def]
    \\ `IS_PMAP_INIT (THE_PMAP init1 next1 out1) init1 out1 /\
        IS_PMAP_INIT (THE_PMAP init2 next2 out2) init2 out2`
    by METIS_TAC [IS_PMAP_INIT_def]
    \\ EQ_TAC \\ RW_TAC (srw_ss()) []);

val OSMPL = prove(
  `!f impl imm. OSMPL f impl imm =
     (\(x,i) t. f <| state := (impl (imm x t) x).state;
                     inp := ADVANCE (imm x t) x.inp|> (PACK (imm x) i t))`,
  REWRITE_TAC [FUN_EQ_THM] \\ REPEAT STRIP_TAC
    \\ Cases_on `x` \\ SIMP_TAC (srw_ss()) [OSMPL_def]);

val ONE_STEP_THM = store_thm("ONE_STEP_THM",
  `!sstrm istrm spec impl imm abs osmpl ismpl f.
      IS_IMAP spec /\ IS_IMAP impl /\ UNIFORM imm impl /\
      DATA_ABSTRACTION abs (state_out_state o (impl 0))
                           (state_out_state o (spec 0)) /\
      STREAM_ABSTRACTION ismpl sstrm istrm /\
      TCON spec sstrm /\ TCON_IMMERSION impl imm istrm /\
      TCON_SMPL ismpl imm impl istrm /\ (osmpl = OSMPL f impl imm) /\
      (!x. x.inp IN istrm ==>
         ((spec 0 <| state := abs x.state; inp := ismpl x|>).state =
          abs (impl (imm x 0) x).state)) /\
      (!x. x.inp IN istrm ==>
         ((spec 1 <| state := abs x.state; inp := ismpl x|>).state =
          abs (impl (imm x 1) x).state)) /\
      (!x. x.inp IN istrm ==>
         (OUTPUT spec <| state := abs x.state; inp := ismpl x|> 0 =
          osmpl (x,OUTPUT impl x) 0)) ==>
      CORRECT spec impl imm abs osmpl ismpl sstrm istrm`,
  RW_TAC bool_ss [IS_IMAP_def,OSMPL] \\ RULE_ASSUM_TAC PairRules.PBETA_RULE
    \\ `PTCON (THE_PMAP init next out) sstrm` by IMP_RES_TAC IMAP_TCON
    \\ PAT_X_ASSUM `TCON spec sstrm` (K ALL_TAC)
    \\ `PUNIFORM imm (THE_PMAP init' next' out')` by IMP_RES_TAC IMAP_UNIFORM
    \\ PAT_X_ASSUM `UNIFORM imm impl` (K ALL_TAC)
    \\ `PTCON_IMMERSION (THE_PMAP init' next' out') imm istrm`
    by IMP_RES_TAC IMAP_TCON_IMMERSION
    \\ PAT_X_ASSUM `TCON_IMMERSION impl imm istrm` (K ALL_TAC)
    \\ ISPECL_THEN [`istrm`,`ismpl`,`imm`,`impl`,`init'`,`next'`,`out'`]
         ASSUME_TAC IMAP_TCON_SMPL
    \\ POP_ASSUM IMP_RES_TAC
    \\ PAT_X_ASSUM `TCON_SMPL ismpl imm impl istrm` (K ALL_TAC)
    \\ ISPECL_THEN [`init`,`next`,`out`] ASSUME_TAC THE_PMAP
    \\ ISPECL_THEN [`init'`,`next'`,`out'`] ASSUME_TAC THE_PMAP
    \\ IMP_RES_TAC IMAP_PMAP
    \\ ISPECL_THEN [`abs`,`spec`,`init`,`next`,`out`,`impl`,
         `init'`,`next'`,`out'`] ASSUME_TAC IMAP_DATA_ABSTRACTION
    \\ POP_ASSUM IMP_RES_TAC
    \\ PAT_X_ASSUM `DATA_ABSTRACTION abs
          (state_out_state o impl 0) (state_out_state o spec 0)` (K ALL_TAC)
    \\ `IS_PMAP (THE_PMAP init next out)` by METIS_TAC [IS_PMAP_def]
    \\ `IS_PMAP (THE_PMAP init' next' out')` by METIS_TAC [IS_PMAP_def]
    \\ NTAC 2 (PAT_X_ASSUM `PMAP (THE_PMAP a b c) a b c` (K ALL_TAC))
    \\ ISPECL_THEN [`sstrm`,`istrm`,`THE_PMAP init next out`,
         `THE_PMAP init' next' out'`, `imm`,`abs`,
         `\(x,i) t. f <|state := (impl (imm x t) x).state;
              inp := ADVANCE (imm x t) x.inp|> ((PACK (imm x) i) t)`,
         `ismpl`,`f`] ASSUME_TAC PONE_STEP_THM
    \\ ISPECL_THEN [`sstrm`,`istrm`,`spec`,`init`,`next`,`out`,`impl`,`init'`,
         `next'`,`out'`,`imm`,`abs`,
         `\(x,i) t. f <|state := (impl (imm x t) x).state;
           inp := ADVANCE (imm x t) x.inp|> ((PACK (imm x) i) t)`,`ismpl`]
         ASSUME_TAC IMAP_CORRECT
    \\ POP_ASSUM (fn th =>
         `CORRECT spec impl imm abs
             (\(x,i) t. f <| state := (impl (imm x t) x).state;
                             inp := ADVANCE (imm x t) x.inp|>
             ((PACK (imm x) i) t)) ismpl sstrm istrm =
          PCORRECT (THE_PMAP init next out) (THE_PMAP init' next' out') imm abs
             (\(x,i) t. f <| state := (impl (imm x t) x).state;
                             inp := ADVANCE (imm x t) x.inp|>
             ((PACK (imm x) i) t)) ismpl sstrm istrm` by IMP_RES_TAC th)
    \\ IMP_RES_TAC IMAP_OUTPUT \\ POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [th])
    \\ IMP_RES_TAC IMAP_OUTPUT
    \\ POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [th,Pstate_out_state])
    \\ NTAC 2 (PAT_X_ASSUM `!x t. THE_PMAP _ _ _ t x = _`
         (fn th => FULL_SIMP_TAC (srw_ss()) [th])));

(*---------------------------------------------------------------------------
  - Data Abstraction Id -----------------------------------------------------
  ---------------------------------------------------------------------------*)

val lem = prove(
  `!a b c. (a = <| state := b; out := c |>) ==> (a.state = b)`,
  SIMP_TAC (srw_ss()) []);

val lem2 = prove(
  `!a b c. (a = <| state := b; inp := c |>) ==> (a.state = b)`,
  SIMP_TAC (srw_ss()) []);

val DATA_ABSTRACTION_I = store_thm("DATA_ABSTRACTION_I",
  `!f fo g h go abs. IS_IMAP_INIT f I /\ IS_IMAP_INIT g h ==>
     (DATA_ABSTRACTION abs (state_out_state o g 0) (state_out_state o f 0) =
        (!a. ?b. abs (h b) = a))`,
  RW_TAC (srw_ss()++boolSimps.LET_ss) [IS_IMAP_INIT_def,IMAP_def,
    DATA_ABSTRACTION_def,RANGE_def,IMAGE_DEF,SURJ_DEF,IN_UNIV,GSPECIFICATION]
    \\ Tactical.REVERSE EQ_TAC >- METIS_TAC [lem,lem2]
    \\ REPEAT STRIP_TAC
    \\ PAT_X_ASSUM `!x. (f 0 x).state = y` (SPEC_THEN `<|state := a; inp := i|>`
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [] o SYM))
    \\ PAT_X_ASSUM `!x. (?x'. x = (f 0 x').state) ==>
         ?y. (?x. y = (g 0 x).state) /\ (abs y = x)` (SPEC_THEN `a` IMP_RES_TAC)
    \\ PAT_X_ASSUM `!x. (g 0 x).state = z` (SPEC_THEN `x` (ASSUME_TAC o SYM))
    \\ METIS_TAC [GSYM lem,GSYM lem2]);

val DATA_ABSTRACTION_I_ABS = store_thm("DATA_ABSTRACTION_I_ABS",
  `!f. DATA_ABSTRACTION I f f`,
  RW_TAC std_ss [onestepTheory.DATA_ABSTRACTION_def,RANGE_def,IMAGE_DEF,
    SURJ_DEF,IN_UNIV,GSPECIFICATION]);

val lem = prove(
   `!x. <| state := x.state; inp := x.inp |> = x`,
  SIMP_TAC (srw_ss()) [theorem "state_inp_component_equality"]);

val CORRECT = prove(
  `!spec impl imm abs osmpl ismpl sstrm istrm.
         CORRECT spec impl imm abs osmpl ismpl sstrm istrm =
         IMMERSION imm /\
         DATA_ABSTRACTION abs (state_out_state o impl 0)
           (state_out_state o spec 0) /\
         STREAM_ABSTRACTION ismpl sstrm istrm /\
         (!a i. let x = <| state := a; inp := i |> in
           i IN istrm ==>
           (let y = <|state := abs a; inp := ismpl x|> in
              (!t. (spec t y).state = abs (impl (imm x t) x).state) /\
              (OUTPUT spec y = osmpl (x,OUTPUT impl x))))`,
  RW_TAC (srw_ss()++boolSimps.LET_ss) [CORRECT_def]
    \\ EQ_TAC \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) []
    THENL [
      PAT_X_ASSUM `!x. P` (SPEC_THEN `<| state := a; inp := i |>`
        (IMP_RES_TAC o SIMP_RULE (srw_ss()) [])),
      PAT_X_ASSUM `!x. P` (SPEC_THEN `<| state := a; inp := i |>`
        (IMP_RES_TAC o SIMP_RULE (srw_ss()) [])),
      PAT_X_ASSUM `!a i. P` (SPECL_THEN [`x.state`,`x.inp`]
        (IMP_RES_TAC o SIMP_RULE (srw_ss()) [lem])),
      PAT_X_ASSUM `!a i. P` (SPECL_THEN [`x.state`,`x.inp`]
        (IMP_RES_TAC o SIMP_RULE (srw_ss()) [lem]))]
    \\ ASM_SIMP_TAC (srw_ss()) []);

val CORRECT_TRANS = store_thm("CORRECT_TRANS",
  `!f1 f2 f3 imm1 imm2 abs1 abs2 osmpl1 osmpl2 ismpl1 ismpl2 strm1 strm2 strm3.
     CORRECT f1 f2 imm1 abs1 osmpl1 ismpl1 strm1 strm2 /\
     CORRECT f2 f3 imm2 abs2 osmpl2 ismpl2 strm2 strm3 ==>
     CORRECT f1 f3 (\x. imm2 x o imm1 <| state := abs2 x.state; inp := ismpl2 x|>)
       (abs1 o abs2) (\(x,stm). osmpl1 (<|state := abs2 x.state; inp := ismpl2 x|>,osmpl2 (x,stm)))
       (\x. ismpl1 <| state := abs2 x.state; inp := ismpl2 x|>) strm1 strm3`,
  RW_TAC (srw_ss()++boolSimps.LET_ss) [CORRECT,IMMERSION_def,
    DATA_ABSTRACTION_def,STREAM_ABSTRACTION_def,o_THM,FREE_IMMERSION_def,
    SURJ_DEF,RANGE_def,IMAGE_DEF,IN_UNIV,GSPECIFICATION]
    \\ PROVE_TAC []);

val STATE_FUNPOW_INIT = store_thm("STATE_FUNPOW_INIT",
  `!f init next out. IMAP f init next out ==>
     (!t x. f t x = (FUNPOW (PNEXT next out) t (PINIT init out x)).state)`,
  REPEAT STRIP_TAC
    \\ SPECL_THEN [`f`,`THE_PMAP init next out`,`init`,`next`,`out`]
         ASSUME_TAC IMAP_PMAP
    \\ SPECL_THEN [`THE_PMAP init next out`,`init`,`next`,`out`]
         ASSUME_TAC STATE_FUNPOW_LEMMA
    \\ FULL_SIMP_TAC (srw_ss()) [THE_PMAP]);

val STATE_FUNPOW_INIT2 = prove(
  `!next out t x. (FUNPOW (PNEXT next out) t x).inp = ADVANCE t x.inp`,
  Induct_on `t`
    \\ ASM_SIMP_TAC std_ss [ADVANCE_ZERO,ADVANCE_ONE,FUNPOW,FUNPOW_THM]
    \\ FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss) [PNEXT_def]
);

val STATE_FUNPOW_INIT3 = prove(
  `!next t x. (FUNPOW (SNEXT next) t x).inp = ADVANCE t x.inp`,
  Induct_on `t`
    \\ ASM_SIMP_TAC arith_ss [ADVANCE_ZERO,ADVANCE_ONE,FUNPOW,FUNPOW_THM]
    \\ FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss) [SNEXT_def]);

val STATE_FUNPOW_INIT4 = store_thm("STATE_FUNPOW_INIT4",
  `!f init next out. IMAP f init next out ==>
     (!t x. (f t x).state = (FUNPOW (SNEXT next) t (SINIT init x)).state)`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC STATE_FUNPOW_INIT
    \\ SPEC_TAC (`t`,`t`)
    \\ Induct
    >- ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss) [FUNPOW,PINIT_def,SINIT_def]
    \\ FULL_SIMP_TAC (srw_ss() ++ boolSimps.LET_ss)
         [FUNPOW_SUC, PNEXT_def, SNEXT_def,
          SIMP_RULE (srw_ss()) [PNEXT_def] STATE_FUNPOW_INIT2,
          SIMP_RULE (srw_ss()) [SNEXT_def] STATE_FUNPOW_INIT3]
    \\ PAT_X_ASSUM `!x t. P` (fn th => ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss)
         [GSYM th, PINIT_def,SINIT_def]));

val STATE_FUNPOW_INIT2 = store_thm("STATE_FUNPOW_INIT2",
  `!next t x.  <|state := (FUNPOW (SNEXT next) t x).state;
                 inp := ADVANCE t x.inp|> = FUNPOW (SNEXT next) t x`,
  REWRITE_TAC [GSYM STATE_FUNPOW_INIT3]
    \\ SIMP_TAC (srw_ss()) [theorem "state_inp_component_equality"]);

val OUTPUT_THM = store_thm("OUTPUT_THM",
  `!f init next out. IMAP f init next out ==>
    (!t x. (f t x).out = out ((f t x).state))`,
  RW_TAC bool_ss [IMAP_def]);

val lem = prove(
  `!P a b. (a < SUC b ==> P a) ==> (a < b ==> P a)`, RW_TAC arith_ss []);

val lem2 = prove(
  `!f init next out. IMAP f init next out ==>
     !t x i j. (!t2. t2 < t ==> (i t2 = j t2)) ==>
        ((f t <|state := x; inp := i|>).state =
         (f t <|state := x; inp := j|>).state)`,
  NTAC 5 STRIP_TAC \\ FULL_SIMP_TAC std_ss [IMAP_def]
    \\ Induct \\ RW_TAC arith_ss []
    \\ SPEC_THEN `\a. i a = j a` (ASSUME_TAC o SIMP_RULE std_ss []) lem
    \\ METIS_TAC []);

val lem3 = prove(
  `!t2 t. t2 < t ==> ((\s. (if s = t then i else y s)) t2 = y t2)`,
  RW_TAC arith_ss []);

val IMAP_NEXT = store_thm("IMAP_NEXT",
  `!spec init next out.
     IMAP spec init next out ==>
       !t a b c d e f.
       (spec t <| state := a; inp := b |> = <| state:= c; out := d |>) /\
       (next c e = f) /\
       (out f = g) ==>
       (spec (SUC t) <| state := a; inp := \s. if s = t then e else b s |> =
                     <| state := f; out:= g|>)`,
  NTAC 5 STRIP_TAC \\ IMP_RES_TAC lem2
    \\ FULL_SIMP_TAC std_ss [IMAP_def]
    \\ RW_TAC std_ss [state_out_component_equality]
    \\ POP_ASSUM (ASSUME_TAC o GEN_ALL o INST
         [`i` |-> `(\s. (if s = t then e else b s))`, `j` |-> `b`] o SPEC_ALL)
    \\ FULL_SIMP_TAC std_ss [lem3]);

(*---------------------------------------------------------------------------
  - All Input Stream Specialisation -----------------------------------------
  ---------------------------------------------------------------------------*)

val STREAM_ABSTRACTIONa = prove(
  `STREAM_ABSTRACTION smpl UNIV UNIV`,
  SIMP_TAC std_ss [STREAM_ABSTRACTION_def,IN_UNIV]);

val TCONa_def = Define `TCONa f = TCON f UNIV`;

val TCON_IMMERSIONa_def = Define`
  TCON_IMMERSIONa f imm = TCON_IMMERSION f imm UNIV`;

val TCON_SMPLa_def = Define`
  TCON_SMPLa smpl imm f = TCON_SMPL smpl imm f UNIV`;

val CORRECTa_def = Define `
  CORRECTa spec impl imm abs osmpl ismpl =
   CORRECT spec impl imm abs osmpl ismpl UNIV UNIV`;

(* - Simplifications ------------------------------------------------------- *)

val TCONa = save_thm("TCONa",
  (GEN_ALL o REWRITE_RULE [GSYM TCONa_def,GSYM UNIV_DEF] o
   SIMP_RULE bool_ss [IN_UNIV] o SPECL [`f`,`UNIV`]) TCON_def);

val TCON_IMMERSIONa = save_thm("TCON_IMMERSIONa",
  (REWRITE_RULE [GSYM TCON_IMMERSIONa_def,GSYM UNIV_DEF] o
   SIMP_RULE bool_ss [IN_UNIV] o INST [`strm` |-> `UNIV`] o SPEC_ALL)
  TCON_IMMERSION);

val TCON_SMPLa = save_thm("TCON_SMPLa",
  (GEN_ALL o REWRITE_RULE [GSYM TCON_SMPLa_def,GSYM UNIV_DEF] o
   SIMP_RULE bool_ss [IN_UNIV] o INST [`strm` |-> `UNIV`] o SPEC_ALL)
  TCON_SMPL_def);

val CORRECTa = save_thm("CORRECTa",
  (GEN_ALL o
   REWRITE_RULE [GSYM CORRECTa_def,STREAM_ABSTRACTIONa,GSYM UNIV_DEF] o
   SIMP_RULE bossLib.bool_ss [IN_UNIV] o
   INST [`sstrm` |-> `UNIV`,`istrm` |-> `UNIV`] o SPEC_ALL) CORRECT_def);


(* ------------------------------------------------------------------------- *)

val TCON_IMMERSION_ONE_STEP_THMa = save_thm("TCON_IMMERSION_ONE_STEP_THMa",
  (GEN_ALL o REWRITE_RULE [GSYM TCON_IMMERSIONa_def,GSYM UNIV_DEF] o
   SIMP_RULE bool_ss [IN_UNIV] o SPEC `UNIV`) TCON_IMMERSION_ONE_STEP_THM);

val TCON_IMP_TCON_IMMERSIONa = save_thm("TCON_IMP_TCON_IMMERSIONa",
  (GEN_ALL o
   REWRITE_RULE [GSYM TCON_IMMERSIONa_def,GSYM TCONa_def,GSYM UNIV_DEF] o
   SIMP_RULE bool_ss [IN_UNIV] o SPEC `UNIV`) TCON_IMP_TCON_IMMERSION);

val TCON_ONE_STEP_THMa = save_thm("TCON_ONE_STEP_THMa",
  (GEN_ALL o REWRITE_RULE [GSYM TCONa_def,GSYM UNIV_DEF] o
   SIMP_RULE bool_ss [IN_UNIV] o SPEC `UNIV`) TCON_ONE_STEP_THM);

val TCON_I_THMa = save_thm("TCON_I_THMa",
  (GEN_ALL o REWRITE_RULE [GSYM TCONa_def,GSYM UNIV_DEF] o
   SIMP_RULE bool_ss [IN_UNIV] o SPEC `UNIV`) TCON_I_THM);

val ONE_STEP_THMa = save_thm("ONE_STEP_THMa",
  (GEN_ALL o REWRITE_RULE (map GSYM
      [CORRECTa_def,TCON_SMPLa_def,TCON_IMMERSIONa_def,
       TCONa_def,STREAM_ABSTRACTIONa,UNIV_DEF]) o
   SIMP_RULE bool_ss [IN_UNIV] o SPECL [`UNIV`,`UNIV`]) ONE_STEP_THM);

(* ------------------------------------------------------------------------- *)

val TCON_IMMERSION_THM = store_thm("TCON_IMMERSION_THM",
  `!f imm strm.
         TCON_IMMERSION f imm strm =
           (let g = \t x. <|state:= (f t x).state; inp := ADVANCE t x.inp|> in
              !t1 t2 x. x.inp IN strm ==>
              (let s2 = imm x t2 in
               let s1 = imm (g s2 x) t1 in
              ADVANCE s2 x.inp IN strm /\
              (g (s1 + s2) x = (g s1 o g s2) x)))`,
  RW_TAC (srw_ss()++boolSimps.LET_ss) [ADVANCE_COMP,TCON_IMMERSION_def]);

val PP_TCON_IMMERSION_ONE_STEP_THM = store_thm("PP_TCON_IMMERSION_ONE_STEP_THM",
  `!strm f init out imm.
         IS_IMAP_INIT f init /\ UNIFORM imm f ==>
         (TCON_IMMERSION f imm strm =
          (!x. x.inp IN strm ==>
             (init (f (imm x 0) x).state = (f (imm x 0) x).state) /\
             (init (f (imm x 1) x).state = (f (imm x 1) x).state) /\
            ADVANCE (imm x 1) x.inp IN strm))`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC TCON_IMMERSION_ONE_STEP_THM
    \\ NTAC 5 (POP_ASSUM (K ALL_TAC))
    \\ ASM_SIMP_TAC (std_ss++boolSimps.DNF_ss) [AC CONJ_COMM CONJ_ASSOC]);

val PP_ONE_STEP_THM = store_thm("PP_ONE_STEP_THM",
  `!sstrm istrm spec impl imm abs osmpl ismpl f.
     IS_IMAP spec /\ IS_IMAP impl /\ UNIFORM imm impl /\
     DATA_ABSTRACTION abs
       (state_out_state o impl 0) (state_out_state o spec 0) /\
     STREAM_ABSTRACTION ismpl sstrm istrm /\ TCON spec sstrm /\
     TCON_IMMERSION impl imm istrm /\ TCON_SMPL ismpl imm impl istrm /\
     (osmpl = OSMPL f impl imm) /\
     (!x. x.inp IN istrm ==>
        let y = <|state := abs x.state; inp := ismpl x|> in
        ((spec 0 y).state = abs (impl (imm x 0) x).state) /\
        ((spec 1 y).state = abs (impl (imm x 1) x).state) /\
        (OUTPUT spec y 0 = osmpl (x,OUTPUT impl x) 0)) ==>
     CORRECT spec impl imm abs osmpl ismpl sstrm istrm`,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC ONE_STEP_THM
    \\ EXISTS_TAC `f` \\ FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss) []);

val lem = prove(
   `!x. <| state := x.state; inp := x.inp |> = x`,
  SIMP_TAC (srw_ss()) [state_inp_component_equality]);

val SELF_CORRECT = prove(
  `!f strm. ?i. i IN strm ==>
     CORRECT f f (\x t. t) I SND state_inp_inp strm strm`,
  RW_TAC (srw_ss()++boolSimps.LET_ss)
    [CORRECT_def,STREAM_ABSTRACTION_def,pred_setTheory.SURJ_DEF,
     onestepTheory.DATA_ABSTRACTION_def,IMMERSION_def,
     onestepTheory.FREE_IMMERSION_def,lem]
    \\ PROVE_TAC []);

(* ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ *)

val _ = export_theory();
