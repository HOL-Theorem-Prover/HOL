
open HolKernel Parse boolLib bossLib finite_mapTheory;
open recfunsTheory;
open recursivefnsTheory;
open prnlistTheory;
open primrecfnsTheory;
open listTheory;
open arithmeticTheory;
open numpairTheory;
open pred_setTheory;
open turing_machineTheory;
val _ = new_theory "turing_machine_primeq";

val _ = intLib.deprecate_int()

val updn_def = Define `(updn [] = 0) ∧ (updn [x] = tri x) ∧
 (updn [x;y] =  if y = 0 then tri x
                else if y = 1 then tri (x + 2) + 2
                else if y = 2 then tri x
                else nB (y = 3) * tri x) ∧
 (updn [s;actn;tmn] =
  let tape = (nsnd tmn) in
  let tl = (nfst tape) in
  let th = ((nsnd tape) MOD 2) in
  let tr = ((nsnd tape) DIV 2) in
      if actn = 0 then (* Write 0 *)
          s *, (tl *, ((2 * tr)))
      else if actn = 1 then (* Write 1 *)
          s *, (tl *, ((2 * tr) + 1 ))
      else if actn = 2 then (* Move left *)
          if tl MOD 2 = 1 then
              s *, (((tl-1) DIV 2) *, ((2 * (th + (2 * tr))) + 1))
          else
              s *, ((tl DIV 2) *, (2 * (( th + (2 * tr)))))
      else if actn = 3 then  (* Move right *)
          if tr MOD 2 = 1 then
              s *, ((th + (2 * tl)) *, ((2 * ((tr-1) DIV 2)) + 1))
          else
              s *, ((th + (2 * tl)) *, (2 * (tr DIV 2)))
      else tmn) ∧
       (updn (s::actn::tmn::a::b) = updn [s;actn;tmn])
`;

EVAL ``FULL_DECODE_TM 5564``;

EVAL ``updn[0;1;4185]``;

val UPDATE_TM_NUM_act0_lem = Q.store_thm ("UPDATE_TM_NUM_act0_lem",
`∀ s tmn actn. (actn = 0) ==>  (updn [s;actn;tmn] =
FULL_ENCODE_TM (UPDATE_ACT_S_TM (NUM_TO_STATE s) (NUM_TO_ACT actn) (FULL_DECODE_TM tmn)))`,
REWRITE_TAC [updn_def] >> rpt strip_tac >>
 (* actn = 0*)
    simp[NUM_TO_ACT_def] >>
        rw[FULL_DECODE_TM_def,FULL_ENCODE_TM_def]
        >- ( rw[UPDATE_ACT_S_TM_def] >> EVAL_TAC)
        >> rw[ENCODE_TM_TAPE_def]
        >- ( rw[UPDATE_ACT_S_TM_def] >> rw[DECODE_TM_TAPE_def]
               >> simp[ENCODE_DECODE_thm ]  )
        >-  ( rw[UPDATE_ACT_S_TM_def] >> rw[DECODE_TM_TAPE_def] >>
                simp[ENCODE_DECODE_thm ] >>
`ODD (nsnd (nsnd tmn))` by metis_tac[EVEN_OR_ODD] >>
fs[ODD_DIV_2_lem] )
        >> (`(UPDATE_ACT_S_TM (NUM_TO_STATE s) Wr0
                             <|state := NUM_TO_STATE (nfst tmn);
             tape_l := FST (DECODE_TM_TAPE (nsnd tmn));
             tape_h := FST (SND (DECODE_TM_TAPE (nsnd tmn)));
             tape_r := SND (SND (DECODE_TM_TAPE (nsnd tmn)))|>).tape_h = Z` by fs[WRITE_0_HEAD_lem] >> rfs[])
);


val UPDATE_TM_NUM_act1_lem = Q.store_thm ("UPDATE_TM_NUM_act1_lem",
`∀ s tmn actn. (actn = 1) ==>  (updn [s;actn;tmn] =
FULL_ENCODE_TM (UPDATE_ACT_S_TM (NUM_TO_STATE s) (NUM_TO_ACT actn) (FULL_DECODE_TM tmn)))`,
REWRITE_TAC [updn_def] >> rpt strip_tac >>
simp[NUM_TO_ACT_def] >>
     rw[FULL_DECODE_TM_def] >> rw[FULL_ENCODE_TM_def]
     >- ( rw[UPDATE_ACT_S_TM_def] >> EVAL_TAC)
     >> rw[ENCODE_TM_TAPE_def]
     >- ( rw[UPDATE_ACT_S_TM_def] >> rw[DECODE_TM_TAPE_def]
            >> simp[ENCODE_DECODE_thm ]  )
     >-  ( `(UPDATE_ACT_S_TM (NUM_TO_STATE s) Wr1
                             <|state := NUM_TO_STATE (nfst tmn);
             tape_l := FST (DECODE_TM_TAPE (nsnd tmn));
             tape_h := FST (SND (DECODE_TM_TAPE (nsnd tmn)));
             tape_r := SND (SND (DECODE_TM_TAPE (nsnd tmn)))|>).tape_h = O` by fs[WRITE_1_HEAD_lem] >> `O=Z` by fs[] >> fs[])
     >- (rw[UPDATE_ACT_S_TM_def] >> rw[DECODE_TM_TAPE_def] >>
           simp[ENCODE_DECODE_thm ])
     >> (rw[UPDATE_ACT_S_TM_def] >> rw[DECODE_TM_TAPE_def] >>
           simp[ENCODE_DECODE_thm ]
           >> `ODD (nsnd (nsnd tmn))` by metis_tac[EVEN_OR_ODD]
           >> fs[ODD_DIV_2_lem] )
);



val UPDATE_TM_NUM_act2_lem = Q.store_thm ("UPDATE_TM_NUM_act2_lem",
`∀ s tmn actn.
    (actn = 2) ==>
    (updn [s;actn;tmn] =
       FULL_ENCODE_TM (UPDATE_ACT_S_TM (NUM_TO_STATE s) (NUM_TO_ACT actn) (FULL_DECODE_TM tmn)))`,
REWRITE_TAC [updn_def] >> rpt strip_tac >>
simp[NUM_TO_ACT_def, FULL_DECODE_TM_def, FULL_ENCODE_TM_def, UPDATE_ACT_S_TM_def] >>
rw[] >- (fs[])
>- (`~EVEN (nfst (nsnd tmn))` by metis_tac[MOD_2, DECIDE ``0n <> 1``] >>
    `ODD (nfst (nsnd tmn))` by metis_tac[EVEN_OR_ODD] >>
    simp[ENCODE_TM_TAPE_def, ODD_TL_DECODE_lem, ENCODE_DECODE_thm] >> 
    rw[ENCODE_def, ENCODE_DECODE_thm,DECODE_TM_TAPE_def] >> rfs[ODD_HD_DECODE]
    >- metis_tac[MOD_2]
    >- (rw[MOD_2] >> metis_tac[ODD_DIV_2_lem, EVEN_OR_ODD]))
>- (simp[ENCODE_TM_TAPE_def, ODD_TL_DECODE_lem, ENCODE_DECODE_thm] >> 
    rw[ENCODE_def,DECODE_TM_TAPE_def,ENCODE_DECODE_thm,MOD_2] >>
    metis_tac[ODD_DIV_2_lem, EVEN_OR_ODD])
>- (`EVEN (nfst (nsnd tmn))` by metis_tac[MOD_2, DECIDE ``0n <> 1``] >>
    `~ODD (nfst (nsnd tmn))` by metis_tac[EVEN_AND_ODD] >>
    simp[ENCODE_TM_TAPE_def, EVEN_TL_DECODE_lem, ENCODE_DECODE_thm] >>
    rw[ENCODE_def,DECODE_TM_TAPE_def, ENCODE_DECODE_thm] >> rfs[EVEN_HD_DECODE]
    >- simp[MOD_2]
    >- (rw[MOD_2] >> metis_tac[ODD_DIV_2_lem, EVEN_OR_ODD]))
 );





val UPDATE_TM_NUM_act3_lem = Q.store_thm ("UPDATE_TM_NUM_act3_lem",
`∀ s tmn actn.
    (actn = 3) ==>
    (updn [s;actn;tmn] =
       FULL_ENCODE_TM (UPDATE_ACT_S_TM (NUM_TO_STATE s) (NUM_TO_ACT actn) (FULL_DECODE_TM tmn)))`,
REWRITE_TAC [updn_def] >> rpt strip_tac >>
simp[NUM_TO_ACT_def, FULL_DECODE_TM_def, FULL_ENCODE_TM_def, UPDATE_ACT_S_TM_def] >>
rw[] >- (fs[SND_SND_DECODE_TM_TAPE])
>- (simp[ENCODE_TM_TAPE_def, ENCODE_DECODE_thm] >>
    `~EVEN (nsnd (nsnd tmn) DIV 2)` by metis_tac[MOD_2, DECIDE ``0n <> 1``] >>
    `ODD (nsnd (nsnd tmn) DIV 2)` by metis_tac[EVEN_OR_ODD] >>
    rfs[SND_SND_DECODE_TM_TAPE] >> simp[ENCODE_def] >> fs[ODD_TL_DECODE_lem,ENCODE_DECODE_thm] >>
    `HD (DECODE (nsnd (nsnd tmn) DIV 2)) = O` by fs[ODD_HD_DECODE] >> simp[] >>
    rw[ENCODE_def,DECODE_TM_TAPE_def,ENCODE_DECODE_thm,MOD_2] )
>- ( simp[ENCODE_TM_TAPE_def, ENCODE_DECODE_thm] >>
    `EVEN (nsnd (nsnd tmn) DIV 2)` by metis_tac[MOD_2, DECIDE ``0n <> 1``] >>
    `~ODD (nsnd (nsnd tmn) DIV 2)` by metis_tac[EVEN_AND_ODD] >>
    rfs[SND_SND_DECODE_TM_TAPE]  >>
    rw[ENCODE_def,DECODE_TM_TAPE_def, ENCODE_DECODE_thm,MOD_2] )
>- (simp[ENCODE_TM_TAPE_def, ENCODE_DECODE_thm] >>
    `EVEN (nsnd (nsnd tmn) DIV 2)` by metis_tac[MOD_2, DECIDE ``0n <> 1``] >>
    fs[SND_SND_DECODE_TM_TAPE,EVEN_HD_DECODE] >>
    rw[ENCODE_def,DECODE_TM_TAPE_def, ENCODE_DECODE_thm,MOD_2] >>
    fs[EVEN_TL_DECODE_lem,ENCODE_DECODE_thm])
 );


val UPDATE_TM_NUM_thm = Q.store_thm ("UPDATE_TM_NUM_Theorem",
`∀ s tmn actn. (actn < 4) ==>  (updn [s;actn;tmn] =
 FULL_ENCODE_TM (UPDATE_ACT_S_TM (NUM_TO_STATE s) (NUM_TO_ACT actn) (FULL_DECODE_TM tmn)))`,
 rpt strip_tac >>
`(actn = 0) ∨ (actn = 1) ∨ (actn = 2) ∨ (actn = 3)` by simp[]
>- (* actn = 0*)
   fs[UPDATE_TM_NUM_act0_lem]
>-  (* actn = 1*)
   fs[UPDATE_TM_NUM_act1_lem]
>- (* actn = 2*)
    fs[UPDATE_TM_NUM_act2_lem]
>- (* actn = 3*)
    fs[UPDATE_TM_NUM_act3_lem]);



val pr3_def = Define`
(pr3 f [] = f 0 0 0 : num) ∧
(pr3 f [x:num] = f x 0 0) ∧
(pr3 f [x;y] = f x y 0) ∧
(pr3 f (x::y::z::t) = f x y z)
`;

val GENLIST1 = prove(``GENLIST f 1 = [f 0]``,
                     SIMP_TAC bool_ss [ONE, GENLIST, SNOC]);

val GENLIST2 = prove(
``GENLIST f 2 = [f 0; f 1]``,
SIMP_TAC bool_ss [TWO, ONE, GENLIST, SNOC]);

val GENLIST3 = prove(
``GENLIST f 3 = [f 0; f 1; f 2]``,
EVAL_TAC );

val ternary_primrec_eq = store_thm(
        "ternary_primrec_eq",
``primrec f 3 ∧ (∀n m p. f [n; m; p] = g n m p) ⇒ (f = pr3 g)``,
SRW_TAC [][] >> SIMP_TAC (srw_ss()) [FUN_EQ_THM] >>
Q.X_GEN_TAC `l` >>
`(l = []) ∨ ∃n ns. l = n :: ns` by (Cases_on `l` >> SRW_TAC [][]) THENL [
SRW_TAC [][] >>
`f [] = f (GENLIST (K 0) 3)` by METIS_TAC [primrec_nil] >>
SRW_TAC [][GENLIST3,pr3_def] ,
`(ns = []) ∨ ∃m ms. ns = m::ms` by (Cases_on `ns` THEN SRW_TAC [][]) >>
SRW_TAC [][] THENL [
IMP_RES_THEN (Q.SPEC_THEN `[n]` MP_TAC) primrec_short >>
              SRW_TAC [][GENLIST1] >> EVAL_TAC,
`(ms = []) ∨ ∃p ps. ms = p::ps` by (Cases_on `ms` THEN SRW_TAC [][]) THENL [
    fs[pr3_def] >> `f [n;m] = f ([n;m] ++ GENLIST (K 0) (3 - LENGTH [n;m]))` by fs[primrec_short] >>
      `GENLIST (K 0) (3 - LENGTH [n;m]) = [0]` by EVAL_TAC >> rfs[], IMP_RES_THEN (Q.SPEC_THEN `(n::m::p::ps)` MP_TAC) primrec_arg_too_long >>
        SRW_TAC [ARITH_ss][] >> fs[pr3_def]  ] ] ]);


val primrec_pr3 = store_thm(
        "primrec_pr3",
``(∃g. primrec g 3 ∧ (∀m n p. g [m; n; p] = f m n p)) ⇒ primrec (pr3 f) 3``,
METIS_TAC [ternary_primrec_eq]);


val MULT2_def = Define `MULT2 x = 2*x`;



val pr_pr_up_case1_def = Define`pr_pr_up_case1  =
  Cn (pr2 $*,) [ proj 0;Cn (pr2 $*,) [proj 2;Cn (pr1 MULT2) [proj 4]] ] `

val pr_up_case1_thm = Q.store_thm("pr_up_case1_thm",
`∀ x. ((proj 0 x) *, (proj 2 x) *, (2 * (proj 4 x)) ) = (Cn (pr2 $*,) [ proj 0;Cn (pr2 $*,) [proj 2;Cn (pr1 MULT2) [proj 4]] ] x)`,
strip_tac >> rfs[MULT2_def] );

val pr_pr_up_case2_def = Define`pr_pr_up_case2  =
        Cn (pr2 $*,) [ proj 0;Cn (pr2 $*,) [proj 2;Cn (succ) [Cn (pr1 MULT2) [proj 4]] ] ] `;

val pr_pr_up_case3_def = Define`pr_pr_up_case3  =
        Cn (pr2 $*,) [ proj 0;Cn (pr2 $*,) [Cn (pr1 DIV2) [Cn (pr1 PRE) [proj 2]];
        Cn (succ) [Cn (pr1 MULT2) [Cn (pr2 (+)) [proj 3; Cn (pr1 MULT2) [proj 4]]]] ] ] `;

val pr_pr_up_case4_def = Define`pr_pr_up_case4  =
        Cn (pr2 $*,) [ proj 0;Cn (pr2 $*,) [Cn (pr1 DIV2) [proj 2];
        Cn (pr1 MULT2) [Cn (pr2 (+)) [proj 3; Cn (pr1 MULT2) [proj 4]]] ] ] `;

val pr_pr_up_case5_def = Define`pr_pr_up_case5  =
        Cn (pr2 $*,) [ proj 0;Cn (pr2 $*,) [Cn (pr2 (+)) [proj 3;Cn (pr1 MULT2) [proj 2]];
        Cn (succ) [Cn (pr1 MULT2) [Cn (pr1 DIV2) [Cn (pr1 PRE) [proj 4]]]] ] ] `;

val pr_pr_up_case6_def = Define`pr_pr_up_case6  =
        Cn (pr2 $*,) [ proj 0;Cn (pr2 $*,) [Cn (pr2 (+)) [proj 3;Cn (pr1 MULT2) [proj 2]];
       Cn (pr1 MULT2) [Cn (pr1 DIV2) [proj 4]]]  ] `;

val pr_pr_up_case7_def = Define`pr_pr_up_case7  =
  proj 5 `;


val _ = overload_on ("onef", ``K 1 : num list -> num``)

val _ = overload_on ("twof", ``K 2 : num list -> num``)

val _ = overload_on ("threef", ``K 3 : num list -> num``)

val _ = overload_on ("fourf", ``K 4 : num list -> num``)

val nB_cond_elim = prove(
``nB p * x + nB (~p) * y = if p then x else y``,
Cases_on `p` >> simp[]);


val updn_zero_thm = Q.store_thm ("updn_zero_thm",
`∀ x. updn [x;0] = updn [x]`,
strip_tac >> fs[updn_def])

val updn_two_lem_1 = Q.store_thm("updn_two_lem_1",
`∀ x. ((x <> []) ∧ (LENGTH x <= 2)) ==> ( ∃ h. (x = [h])) ∨  (∃ h t. (x = [h;t]))`,
rpt strip_tac >>  Cases_on `x` >- fs[] >> Cases_on `t` >- fs[] >> Cases_on `t'` >- fs[] >> rfs[] );

val updn_two_lem_2 = Q.store_thm("updn_two_lem_2",
`∀x. (LENGTH x = 2) ==> (∃h t. (x = [h;t]))`,
rpt strip_tac >>  Cases_on `x` >> fs[] >> Cases_on `t` >> fs[])

val updn_three_lem_1 = Q.store_thm("updn_three_lem_1",
`∀ x.  ¬(LENGTH x <= 2) ==> (∃ a b c. (x = [a;b;c]) ) ∨ (∃ a b c d e. (x = (a::b::c::d::e) ) )`,
rpt strip_tac >>  Cases_on `x` >- fs[] >> Cases_on `t` >- fs[] >> Cases_on `t'` >- fs[] >> rfs[] >> strip_tac >> Cases_on `t` >- fs[] >> fs[] );


val prim_pr_rec_updn = Q.store_thm ("prim_pr_rec_updn",
`updn  = Cn
             (pr_cond (Cn pr_eq [proj 1;zerof] ) (pr_pr_up_case1) (
                   pr_cond (Cn pr_eq [proj 1; onef] ) (pr_pr_up_case2) (
                       pr_cond (Cn pr_eq [proj 1; twof] ) (
                           pr_cond (Cn pr_eq [Cn (pr_mod) [proj 2;twof];onef]) (pr_pr_up_case3) (pr_pr_up_case4) ) (
                           pr_cond (Cn pr_eq [proj 1;threef]) (
                               pr_cond (Cn pr_eq [Cn (pr_mod) [proj 4;twof];onef]) (pr_pr_up_case5) (pr_pr_up_case6) )
                                   (pr_cond (Cn pr_eq [proj 1;fourf]) (pr_pr_up_case7) (pr_pr_up_case7)  )  ) )  )  )
             [proj 0;proj 1; Cn (pr1 nfst) [Cn (pr1 nsnd) [proj 2]] ;
              Cn (pr_mod) [Cn (pr1 nsnd) [ Cn (pr1 nsnd) [proj 2]];twof];
              Cn (pr1 DIV2) [Cn (pr1 nsnd) [ Cn (pr1 nsnd) [proj 2]]]; proj 2 ]  `,
rw[Cn_def,FUN_EQ_THM]
  >>  fs[pr_pr_up_case1_def,pr_pr_up_case2_def,pr_pr_up_case3_def,pr_pr_up_case4_def,pr_pr_up_case5_def,pr_pr_up_case6_def] >> rw[]
  >- ( rw[proj_def,updn_def,updn_zero_thm,updn_three_lem_1]
    >- EVAL_TAC
    >- rfs[]
    >-( EVAL_TAC >> `(∃h. x = [h]) ∨ (∃h t. x = [h;t])` by simp[updn_two_lem_1]
      >- (rw[updn_def])
      >- (rfs[updn_def,updn_zero_thm] >> `proj 1 x = t` by fs[] >> fs[] )
           )
    >- (`(∃ a b c. x = [a;b;c]) ∨ (∃ a b c d e. x = (a::b::c::d::e))` by simp[updn_three_lem_1]
      >- (`proj 1 x = b` by fs[] >> fs[] >> fs[updn_def,MULT2_def,DIV2_def] )
      >-  fs[updn_def,MULT2_def,DIV2_def] )
     )
  >- ( fs[proj_def,updn_def,updn_zero_thm,pr_pr_up_case2_def] >> rw[]
    >- (rfs[])
    >- (rfs[])
    >- (EVAL_TAC >> `(∃h. x = [h]) ∨ (∃h t. x = [h;t])` by simp[updn_two_lem_1]
      >-(fs[])
      >-(rfs[updn_def,updn_zero_thm] >> fs[])
            )
    >- (`(∃ a b c. x = [a;b;c]) ∨ (∃ a b c d e. x = (a::b::c::d::e))` by simp[updn_three_lem_1]
      >-(fs[updn_def,MULT2_def,DIV2_def])
      >-(fs[updn_def,MULT2_def,DIV2_def])
            )
     )
  >- ( fs[proj_def,updn_def,updn_zero_thm,pr_pr_up_case3_def] >> rw[]
    >-(rfs[])
    >-(rfs[])
    >-(EVAL_TAC >> `(∃h. x = [h]) ∨ (∃h t. x = [h;t])` by simp[updn_two_lem_1]
      >-(fs[])
      >-(rfs[updn_def,updn_zero_thm] >> fs[] >> `nfst (nsnd 0) = 0 ` by EVAL_TAC >> fs[])
      )
    >-(`(∃ a b c. x = [a;b;c]) ∨ (∃ a b c d e. x = (a::b::c::d::e))` by simp[updn_three_lem_1]
      >-(fs[updn_def,MULT2_def,DIV2_def])
      >-(fs[updn_def,MULT2_def,DIV2_def]))
     )
  >- (fs[proj_def,updn_def,updn_zero_thm,pr_pr_up_case4_def] >> rw[]
    >- (rfs[])
    >- (rfs[])
    >- (EVAL_TAC >> `(∃h. x = [h]) ∨ (∃h t. x = [h;t])` by simp[updn_two_lem_1]
      >-(fs[])
      >- (rfs[updn_def,updn_zero_thm] >> fs[] ) )
    >- (`(∃ a b c. x = [a;b;c]) ∨ (∃ a b c d e. x = (a::b::c::d::e))` by simp[updn_three_lem_1]
      >-(fs[updn_def,MULT2_def,DIV2_def])
      >-(fs[updn_def,MULT2_def,DIV2_def])))
  >- (fs[proj_def,updn_def,updn_zero_thm,pr_pr_up_case5_def] >> rw[]
    >- (rfs[])
    >- (rfs[])
    >- (EVAL_TAC >> `(∃h. x = [h]) ∨ (∃h t. x = [h;t])` by simp[updn_two_lem_1]
      >- (fs[updn_def])
      >- (fs[] >> `nsnd (nsnd 0) = 0` by EVAL_TAC >> fs[]))
    >- (`(∃ a b c. x = [a;b;c]) ∨ (∃ a b c d e. x = (a::b::c::d::e))` by simp[updn_three_lem_1]
      >-(fs[updn_def,MULT2_def,DIV2_def])
      >-(fs[updn_def,MULT2_def,DIV2_def])))
  >- (fs[proj_def,updn_def,updn_zero_thm,pr_pr_up_case6_def] >> rw[]
    >- (rfs[])
    >- (rfs[])
    >- (EVAL_TAC >> `(∃h. x = [h]) ∨ (∃h t. x = [h;t])` by simp[updn_two_lem_1]
      >- (fs[updn_def])
      >- (rfs[updn_def,updn_zero_thm] >> fs[]) )
    >- (`(∃ a b c. x = [a;b;c]) ∨ (∃ a b c d e. x = (a::b::c::d::e))` by simp[updn_three_lem_1]
      >-(fs[updn_def,MULT2_def,DIV2_def])
      >-(fs[updn_def,MULT2_def,DIV2_def])) )
  >- (fs[proj_def,updn_def,updn_zero_thm,pr_pr_up_case7_def] >> rw[]

    >- (EVAL_TAC >> `(x=[]) ∨ (x<>[])` by fs[] >- (rw[] >> EVAL_TAC)  >>
       `(∃h. x = [h]) ∨ (∃h t. x = [h;t])` by simp[updn_two_lem_1]
       >- (rfs[updn_def] >> `LENGTH x <= 1` by fs[] >> fs[] )
       >- (rfs[updn_def] >> `LENGTH x = 2` by fs[] >> fs[]  ) )
    >- (`(∃ a b c. x = [a;b;c])∨ (∃ a b c d e. x = (a::b::c::d::e))` by simp[updn_three_lem_1]
       >- (fs[updn_def]  )
       >- (fs[updn_def]) )
     ) );

val primrec_cn = List.nth(CONJUNCTS primrec_rules, 3);

val primrec_pr = List.nth(CONJUNCTS primrec_rules, 4);

val primrec_mult2 = Q.store_thm("primrec_mult2",
`primrec (pr1 MULT2) 1`,
MATCH_MP_TAC primrec_pr1 >>
Q.EXISTS_TAC `Cn (pr2 $*) [proj 0; twof]` >> conj_tac >-
  SRW_TAC [][primrec_rules, alt_Pr_rule,Pr_thm,Pr_def ] >>
  SRW_TAC [][primrec_rules, alt_Pr_rule,Pr_thm,Pr_def ] >> rw[MULT2_def]);

val primrec_div2 = Q.store_thm("primrec_div2",
`primrec (pr1 DIV2) 1`,
MATCH_MP_TAC primrec_pr1 >>
Q.EXISTS_TAC `Cn (pr_div) [proj 0; twof]` >> conj_tac >-
SRW_TAC [][primrec_rules, alt_Pr_rule,Pr_thm,Pr_def,primrec_pr_div ] >>
SRW_TAC [][primrec_rules, alt_Pr_rule,Pr_thm,Pr_def,primrec_pr_div ] >> rw[DIV2_def]);

val primrec_pr_case1 = Q.store_thm("primrec_pr_case1",
`primrec pr_pr_up_case1 6`,
SRW_TAC [][pr_pr_up_case1_def] >>
rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> rw[primrec_mult2]
                               );

val primrec_pr_case2 = Q.store_thm("primrec_pr_case2",
`primrec pr_pr_up_case2 6`,
SRW_TAC [][pr_pr_up_case2_def] >>
        rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> rw[primrec_mult2]
                                  );

val primrec_pr_case3 = Q.store_thm("primrec_pr_case3",
`primrec pr_pr_up_case3 6`,
SRW_TAC [][pr_pr_up_case3_def] >>
        rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >>
        rw[primrec_mult2,primrec_div2]                                  );

val primrec_pr_case4 = Q.store_thm("primrec_pr_case4",
`primrec pr_pr_up_case4 6`,
SRW_TAC [][pr_pr_up_case4_def] >>
        rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> rw[primrec_mult2,primrec_div2]
                                  );

val primrec_pr_case5 = Q.store_thm("primrec_pr_case5",
`primrec pr_pr_up_case5 6`,
SRW_TAC [][pr_pr_up_case5_def] >>
        rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> rw[primrec_mult2,primrec_div2]
                                  );

val primrec_pr_case6 = Q.store_thm("primrec_pr_case6",
`primrec pr_pr_up_case6 6`,
SRW_TAC [][pr_pr_up_case6_def] >>
        rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> rw[primrec_mult2,primrec_div2]
                                  );

val primrec_proj = List.nth(CONJUNCTS primrec_rules, 2);

val primrec_pr_case7 = Q.store_thm("primrec_pr_case7",
`primrec pr_pr_up_case7 6`,
SRW_TAC [][pr_pr_up_case7_def] >>
      `5<6` by fs[]   >> SRW_TAC [][primrec_proj]
                                  );

val UPDATE_TM_NUM_PRIMREC = Q.store_thm("UPDATE_TM_NUM_PRIMREC",
`primrec updn 3`,
SRW_TAC [][updn_def,primrec_rules,prim_pr_rec_updn] >> SRW_TAC [][pr_cond_def] >>
        rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules])
        >> fs[primrec_pr_case1,primrec_pr_case2,primrec_pr_case3,primrec_pr_case4,
               primrec_pr_case5,primrec_pr_case6,primrec_pr_case7,primrec_div2]
         );


val tmstepf_def = tDefine "tmstepf" `tmstepf p tmn =
     case OLEAST n. (NUM_TO_STATE (nfst n), CELL_NUM (nsnd n)) ∈ FDOM p of
         NONE => (tmn)
       | SOME n => let s = NUM_TO_STATE (nfst n) in
                       let sym = CELL_NUM (nsnd n) in
                   let (s',actn) = p ' (s,sym) in
        ( if ((nfst tmn) = STATE_TO_NUM s) ∧ (((nsnd (nsnd tmn)) MOD 2) = NUM_CELL sym)
          then updn [STATE_TO_NUM s'; ACT_TO_NUM actn; tmn]
          else tmstepf (p \\ (s,sym)) tmn
          )` (WF_REL_TAC `measure (CARD o FDOM o FST)` >> simp[OLEAST_EQ_SOME] >>
                     metis_tac[MEMBER_CARD]);





val HEAD_DECODE_ENCDOE_EQ = Q.store_thm("HEAD_DECODE_ENCDOE_EQ[simp]",
`(HD (DECODE (ENCODE t)) = Z) ==> (HD t = Z)`,
Cases_on `t`
  >- (EVAL_TAC)
  >- (fs[ENCODE_def,DECODE_def]  >> Cases_on `h` >> fs[] >> `2* ENCODE t' +1 = SUC (2* ENCODE t')` by fs[] >> rw[DECODE_def] >> rfs[ODD_DOUBLE] ) )

val ENCODE_ONE_TL_ZERO = Q.store_thm("ENCODE_ONE_TL_ZERO",
`(ENCODE t = 1) ==> (ENCODE (TL t) = 0)`,
Cases_on ` t` >> fs[] >- (EVAL_TAC) >- (fs[ENCODE_def] >> Cases_on `h` >> fs[]) )


val HD_DECODE_DOUBLED = Q.store_thm("HD_DECODE_DOUBLED[simp]",
`(x <> 0) ==> (HD (DECODE (2 * x)) = Z)`,
Cases_on `x` >> fs[] >> `2*(SUC n) =SUC (SUC (2* n))` by simp[] >> simp[DECODE_def,ODD,ODD_MULT] )


val TL_DECODE_DOUBLED = Q.store_thm("TL_DECODE_DOUBLED[simp]",
`(x <> 0) ==> (TL (DECODE (2 * x)) = DECODE x)`,
Cases_on `x` >> fs[] >> `2 * (SUC n) =SUC (SUC (2* n))` by simp[] >>
         simp[DECODE_def,SimpLHS,ODD,ODD_MULT] >> pop_assum(SUBST1_TAC o SYM) >> fs[TWO_TIMES_DIV_TWO_thm] )

val HD_DECODE_DOUBLED = Q.store_thm("HD_DECODE_DOUBLED[simp]",
`(HD (DECODE (2 * x + 1)) = O)`,
simp[GSYM(ADD1),DECODE_def,ODD,ODD_MULT]  )


val TL_DECODE_DOUBLED = Q.store_thm("TL_DECODE_DOUBLED[simp]",
`(TL (DECODE (2 * x + 1)) = DECODE x)`,
simp[GSYM(ADD1),DECODE_def,ODD,ODD_MULT]  )



val ENCODED_DECODED_ENCODED_UPDATE_TM_thm = Q.store_thm("ENCODED_DECODED_ENCODED_UPDATE_TM_thm",
`⟦UPDATE_ACT_S_TM (FST (p ' (tm.state,tm.tape_h)))
                  (SND (p ' (tm.state,tm.tape_h))) (FULL_DECODE_TM ⟦tm⟧) ⟧ =
⟦(UPDATE_ACT_S_TM (FST (p ' (tm.state,tm.tape_h)))
                  (SND (p ' (tm.state,tm.tape_h))) (tm) )⟧`,
fs[FULL_DECODE_TM_def,FULL_ENCODE_TM_def] >> rw[]
>- (fs[STATE_TO_NUM_def,ENCODE_TM_TAPE_def] >> Cases_on `tm.tape_h` >-
    (fs[SND_SND_DECODE_TM_TAPE_FULL] >> `EVEN (2 * ENCODE tm.tape_r)` by fs[EVEN_DOUBLE] >>
    fs[FST_SND_DECODE_TM_TAPE_FULL] >> fs[UPDATE_ACT_S_TM_def] >>
    Cases_on `SND (p ' (tm.state,Z))` >> fs[] >-
      (Cases_on `tm.tape_l = []` >> fs[ENCODE_def] >> Cases_on `ENCODE tm.tape_l = 0` >> fs[] ) >-
      (Cases_on `tm.tape_r = []` >> fs[ENCODE_def] >> Cases_on `2* ENCODE tm.tape_r DIV 2 = 0` >>
      fs[])) >-
    (fs[SND_SND_DECODE_TM_TAPE_FULL]  >>  fs[EVEN_PLUS_1_thm] >> fs[UPDATE_ACT_S_TM_def] >>
      Cases_on `SND (p ' (tm.state,O))` >> fs[] >-
      (Cases_on `tm.tape_l = []` >> fs[ENCODE_def] >> Cases_on `ENCODE tm.tape_l = 0` >> fs[]) >-
      (Cases_on `tm.tape_r = []` >> fs[ENCODE_def] >>
                Cases_on `(2 * ENCODE tm.tape_r + 1) DIV 2 = 0` >> fs[]) ))
>- ( fs[UPDATE_ACT_S_TM_def] >>
   Cases_on `SND (p ' (tm.state,tm.tape_h))` >> fs[]
       >- (simp[ENCODE_TM_TAPE_def,ENCODE_DECODE_thm] >> rw[] )
       >- (simp[ENCODE_TM_TAPE_def,ENCODE_DECODE_thm] >> rw[])
       >- (Cases_on `tm.tape_l` >> fs[ENCODE_def]
          >- (simp[ENCODE_TM_TAPE_def,ENCODE_DECODE_thm])
          >- (Cases_on `h` >> simp[]
             >- (rw[]
                >- (simp[ENCODE_TM_TAPE_def,ENCODE_def])
                >- (simp[ENCODE_TM_TAPE_def,ENCODE_def] >> simp[ENCODE_DECODE_thm] ))
            >- (simp[ENCODE_TM_TAPE_def,ENCODE_DECODE_thm] ) ) )
       >- (Cases_on `tm.tape_r` >> fs[ENCODE_def]
         >- (simp[ENCODE_TM_TAPE_def,ENCODE_DECODE_thm])
         >- (Cases_on `h` >> simp[]
             >- (rw[]
                >- (simp[ENCODE_TM_TAPE_def,ENCODE_def])
                >- (simp[ENCODE_TM_TAPE_def,ENCODE_def] >> simp[ENCODE_DECODE_thm] ))
              >- (simp[ENCODE_TM_TAPE_def,ENCODE_DECODE_thm] ) ) )
) );


val UPDATE_TM_NUM_corol = Q.store_thm("UPDATE_TM_NUM_corol",
`∀s' tmn actn'. (updn [STATE_TO_NUM s'; ACT_TO_NUM actn'; tmn] =
                 ⟦UPDATE_ACT_S_TM s' actn' (FULL_DECODE_TM tmn)⟧)`,
fs[ACT_TO_NUM_LESS_4,UPDATE_TM_NUM_thm])



val lemma_11 = UPDATE_TM_ARB_Q |> Q.INST[`q` |-> `tm.prog` ]  |> SIMP_RULE(srw_ss())[tm_with_prog]


val updn_UPDATE_TAPE = Q.store_thm("updn_UPDATE_TAPE",
`((tm.state, tm.tape_h) ∈ FDOM p) ==> ((λ(s',actn). updn [STATE_TO_NUM s'; ACT_TO_NUM actn; ⟦tm⟧])
 (p ' (tm.state,tm.tape_h)) = ⟦UPDATE_TAPE (tm with prog := p)⟧)`,
rw[] >> `ACT_TO_NUM actn < 4` by fs[ACT_TO_NUM_LESS_4] >>
`(tm.state,tm.tape_h) ∈ FDOM (tm with prog := p).prog` by fs[] >>
`((tm with prog := p).state,(tm with prog := p).tape_h) ∈ FDOM (tm with prog := p).prog` by fs[] >>
`(UPDATE_ACT_S_TM (FST ((tm with prog := p).prog ' ((tm with prog := p).state,(tm with prog := p).tape_h)))
(SND ((tm with prog := p).prog ' ((tm with prog := p).state,(tm with prog := p).tape_h))) (tm with prog := p) = UPDATE_TAPE (tm with prog := p))` by  fs[UPDATE_TAPE_ACT_STATE_TM_thm] >> rfs[] >>
`ACT_TO_NUM (SND ((tm with prog := p).prog ' (tm.state,tm.tape_h))) < 4` by fs[ACT_TO_NUM_LESS_4] >>
rfs[] >>
`(updn [STATE_TO_NUM (FST ((tm with prog := p).prog ' (tm.state,tm.tape_h))); ACT_TO_NUM (SND (p ' (tm.state,tm.tape_h))); ⟦tm⟧] =
  ⟦UPDATE_ACT_S_TM (FST ((tm with prog := p).prog ' (tm.state,tm.tape_h))) (SND (p ' (tm.state,tm.tape_h))) (FULL_DECODE_TM ⟦tm⟧)⟧)` by fs[UPDATE_TM_NUM_corol] >> rfs[] >>
simp[pairTheory.UNCURRY] >>simp[ENCODED_DECODED_ENCODED_UPDATE_TM_thm,lemma_11] )

val CELL_NUM_NUM_CELL = Q.store_thm("CELL_NUM_NUM_CELL[simp]",
`CELL_NUM (NUM_CELL x) = x`,
Cases_on `x` >> fs[CELL_NUM_def])


val CELL_NUM_NUM_CELL_RW = Q.store_thm("CELL_NUM_NUM_CELL_RW",
`(NUM_CELL (CELL_NUM c) = c) ==> (NUM_CELL h <> c) ==> (h <> CELL_NUM c)`,
strip_tac >> strip_tac >> metis_tac[]  )


val NUM_STATE_CELL_NUM_LEM = Q.store_thm("NUM_STATE_CELL_NUM_LEM",
`(NUM_CELL (CELL_NUM c) = c) ==> (((STATE_TO_NUM tm.state = n) ⇒ NUM_CELL tm.tape_h ≠ c) ==>
 ((tm.state = NUM_TO_STATE n) ⇒ tm.tape_h ≠ CELL_NUM c)) `,
strip_tac >> strip_tac >> strip_tac >> ` STATE_TO_NUM tm.state = STATE_TO_NUM (NUM_TO_STATE n)`
by rfs[NUM_TO_STATE_TO_NUM] >> fs[STATE_TO_NUM_TO_STATE] >>  fs[CELL_NUM_NUM_CELL_RW] )

val EQ_SND_P_LESS_LEM = Q.store_thm("EQ_SND_P_LESS_LEM",
`(c = p ' a) ==> (∀d. (d ∈ FDOM p) ==> ( p ' d = ((p \\ a) |+ (a,c) ) ' d))`,
rw[] >> Cases_on `d=a` >> fs[] >> EVAL_TAC >> fs[] >> `d ∈ FDOM (p \\ a)` by fs[] >>
  simp[DOMSUB_FAPPLY_THM])


val EQ_SND_P_LESS = Q.store_thm("EQ_SND_P_LESS",
`( ( a  ∈ FDOM p ) ∧ (a <> b) ) ==> (( (p \\ a) ' b ) =  (p ' b ))`,
rw[] >> `∃c. c = p ' a` by fs[] >> `FDOM ((p \\ a) |+ (a,c) ) = FDOM p` by fs[] >>
`∀d. (d ∈ FDOM p) ==> (∃k. p ' d = k)` by fs[] >>
`∀d. (d ∈ FDOM p) ==> (∃k. ((p \\ a) |+ (a,c) ) ' d = k)` by fs[] >>
simp[DOMSUB_FAPPLY_THM] )



val UPDATE_W_PROG_NIN_TM = Q.store_thm("UPDATE_W_PROG_NIN_TM",
`((NUM_CELL (CELL_NUM c) = c) ∧ ((NUM_TO_STATE n,CELL_NUM c) ∈ FDOM p) ∧
  ((STATE_TO_NUM tm.state = n) ⇒ NUM_CELL tm.tape_h ≠ c))
  ⇒ (⟦UPDATE_TAPE (tm with prog := p \\ (NUM_TO_STATE n,CELL_NUM c)) ⟧ =
  ⟦UPDATE_TAPE (tm with prog := p)⟧)`,
rw[] >> simp[FULL_ENCODE_TM_def]  >>
`(tm.state = NUM_TO_STATE n) ⇒ tm.tape_h ≠ CELL_NUM c` by metis_tac[NUM_STATE_CELL_NUM_LEM] >>
`(tm.state,tm.tape_h) <> (NUM_TO_STATE n,CELL_NUM c)` by fs[] >>
rw[] >> Cases_on `((tm.state,tm.tape_h) ∈ FDOM p)` >> fs[UPDATE_TAPE_def] >> fs[EQ_SND_P_LESS] >>
Cases_on `SND (p ' (tm.state,tm.tape_h))` >> fs[] >> Cases_on `tm.tape_l = []` >> fs[] >>
Cases_on `tm.tape_r = []` >> fs[ENCODE_TM_TAPE_def] )

val tmstepf_update_equiv = Q.store_thm("tmstepf_update_equiv",
`∀p n tm. (n = ⟦tm⟧ ) ==>
        (tmstepf p n = FULL_ENCODE_TM (UPDATE_TAPE (tm with prog := p) ))`,
ho_match_mp_tac (theorem"tmstepf_ind") >> simp[OLEAST_EQ_SOME] >> rw[] >>
pop_assum (assume_tac o CONV_RULE (HO_REWR_CONV npair_lem)) >> fs[] >> simp[Once tmstepf_def] >>
Cases_on `OLEAST n. (NUM_TO_STATE (nfst n),CELL_NUM (nsnd n)) ∈ FDOM p`
>- (simp[] >> fs[containment_lem]  >> simp[UPDATE_TAPE_def] )
>- (fs[OLEAST_EQ_SOME] >> rename [`NUM_TO_STATE (nfst nc)`] >> simp[] >>
    `∃n c. nc = n *, c` by metis_tac[npair_cases] >>
    fs[UPDATE_TAPE_ACT_STATE_TM_thm,NUM_TO_CELL_TO_NUM,FULL_ENCODE_TM_STATE] >>
    `NUM_CELL (CELL_NUM c) = c` by metis_tac[CELL_NUM_LEM1,NUM_TO_CELL_TO_NUM] >> simp[] >> fs[] >>
    rfs[NUM_CELL_INJ] >>
    Cases_on `(STATE_TO_NUM tm.state = n) ∧ (NUM_CELL tm.tape_h = c)`  >> rw[]
  >- (rw[] >> simp[]  >> simp[TM_ACT_LEM_1]  >> rfs[TM_ACT_LEM_1] >>
     simp[updn_UPDATE_TAPE]  )
  >- (rw[] >> simp[]  >> simp[TM_ACT_LEM_1]  >> rfs[TM_ACT_LEM_1] >>
    `∃ a s. p ' (NUM_TO_STATE n,CELL_NUM c) = (s,a)` by metis_tac[pairTheory.pair_CASES] >>
    first_x_assum(qspecl_then[`n`,`c`,`s`,`a`] mp_tac) >> simp[] >> rw[CELL_NUM_NUM_CELL_RW] >>
    simp[ UPDATE_W_PROG_NIN_TM] )  )
 )

val nsnd0 = EVAL ``nsnd 0``


val nfst0 = EVAL ``nfst 0``


val primrec_tmstepf_form = Q.store_thm("primrec_tmstepf_form",
`∀n.  (Cn (proj 0)  [pr_cond (Cn (pr2 $*)  [Cn pr_eq [Cn (pr1 nfst) [proj 0] ;
       Cn (pr1 nfst) [K k] ];  Cn pr_eq [Cn pr_mod [Cn (pr1 nsnd) [Cn (pr1 nsnd) [proj 0]] ;twof];
       Cn (pr1 nsnd) [K k] ] ] )
      (Cn updn [K snum; K anum ; proj 0] )
      (Cn (pr1 (tmstepf q)) [proj 0] ) ] ) [n] =
      (λtmn. if (nfst tmn = nfst k) ∧ (nsnd (nsnd tmn) MOD 2 = nsnd k) then
                       updn [snum; anum; tmn]
                   else tmstepf q tmn
                 ) n`,
rw[Cn_def,FUN_EQ_THM] >> rw[pr_cond_def] )


val primrec_of_tmstepf = Q.store_thm("primrec_of_tmstepf",
`(primrec (pr1 (tmstepf q)) 1) ==> (primrec (Cn (proj 0)  [
     pr_cond (Cn (pr2 $*)  [Cn pr_eq [Cn (pr1 nfst) [proj 0] ; Cn (pr1 nfst) [K k] ];
               Cn pr_eq [Cn pr_mod [Cn (pr1 nsnd) [Cn (pr1 nsnd) [proj 0]] ;twof];
               Cn (pr1 nsnd) [K k] ] ] )
              (Cn updn [K snum; K anum ; proj 0] )
              (Cn (pr1 (tmstepf q)) [proj 0]  )
                        ] ) 1)`,
strip_tac >> SRW_TAC [][primrec_rules] >> SRW_TAC [][pr_cond_def] >>
       rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> fs[UPDATE_TM_NUM_PRIMREC] );


(*    SIMP_CONV(srw_ss())[pr_cond_def,nsnd0,nfst0] ``Cn (proj 0)  [
        pr_cond (Cn (pr2 $* )  [Cn pr_eq [Cn (pr1 nfst) [proj 0] ; Cn (pr1 nfst) [K k] ];
                               Cn pr_eq [Cn pr_mod [Cn (pr1 nsnd) [Cn (pr1 nsnd) [proj 0]] ;twof];
                                         Cn (pr1 nsnd) [K k] ] ] )
                    (Cn updn [K snum; K anum ; proj 0] )
                    (Cn (tmstepf q) [proj 0]  )
                ] []``   *)

val primrec_tmstepf = Q.store_thm ("primerec_tmstepf",
`primrec (pr1 (tmstepf p) ) 1`,
 Induct_on `CARD (FDOM p)` >- (rpt strip_tac >>
  `FDOM p = {}` by metis_tac[FDOM_FINITE,CARD_EQ_0] >> fs[FDOM_EQ_EMPTY] >>
  rw[Once tmstepf_def] >> qmatch_abbrev_tac`primrec f 1` >>
  `f = proj 0` suffices_by simp[primrec_rules] >> simp[Abbr`f`,FUN_EQ_THM] >> Cases >>
  simp[proj_def] >> rw[Once tmstepf_def]  )
    >- (rpt strip_tac >>  MATCH_MP_TAC primrec_pr1  >> rw[Once tmstepf_def] >>
      ` (OLEAST n.  (NUM_TO_STATE (nfst n),CELL_NUM (nsnd n)) ∈ FDOM p) <> NONE`
        by (DEEP_INTRO_TAC(whileTheory.OLEAST_INTRO) >> simp[] >>
            `FDOM p <> {}` by (strip_tac >> fs[]) >>
            `∃a b. (a,b) IN FDOM p`  by metis_tac[SET_CASES,pairTheory.pair_CASES,IN_INSERT]>>
            qexists_tac`STATE_TO_NUM a *, NUM_CELL b` >> simp[] ) >>
      `∃k. (OLEAST n.  (NUM_TO_STATE (nfst n),CELL_NUM (nsnd n)) ∈ FDOM p) = SOME k`
      by metis_tac[optionTheory.option_CASES] >> simp[] >> fs[OLEAST_EQ_SOME] >>
      `∃ s a. (p ' (NUM_TO_STATE (nfst k),CELL_NUM (nsnd k))) = (s,a)`
      by metis_tac[pairTheory.pair_CASES] >> simp[] >>
      `CARD (FDOM (p \\ (NUM_TO_STATE (nfst k),CELL_NUM (nsnd k)))) = v` by fs[] >>
      qabbrev_tac`q = p \\ (NUM_TO_STATE (nfst k),CELL_NUM (nsnd k))` >>
      `primrec (pr1 (tmstepf q)) 1` by fs[] >>
      `NUM_CELL (CELL_NUM (nsnd k)) = nsnd k`
      by metis_tac[npair_11,npair,CELL_NUM_LEM1,NUM_TO_CELL_TO_NUM] >> fs[] >>
      qabbrev_tac`snum = STATE_TO_NUM s` >> qabbrev_tac`anum = ACT_TO_NUM a` >>
      qexists_tac`Cn (proj 0)  [
     pr_cond (Cn (pr2 $*)  [Cn pr_eq [Cn (pr1 nfst) [proj 0] ; Cn (pr1 nfst) [K k] ];
                            Cn pr_eq [Cn pr_mod [Cn (pr1 nsnd) [Cn (pr1 nsnd) [proj 0]] ;twof];
                                      Cn (pr1 nsnd) [K k] ] ] )
                 (Cn updn [K snum; K anum ; proj 0] )
                 (Cn (pr1 (tmstepf q)) [proj 0]  )
             ] ` >> fs[primrec_of_tmstepf,primrec_tmstepf_form]
    )   )

val tm_return_def = tDefine"tm_return"`
tm_return tm = if tm.tape_h = Z then 0
               else case tm.tape_r of [] => 0
                                 | h::t  => 1 + tm_return (tm with <| tape_h := h;tape_r:=t|>)`
(WF_REL_TAC`measure (LENGTH o (λtm. tm.tape_r))` >> simp[] )



val tm_fn_def = Define`tm_fn p args = let tm0 = INITIAL_TM p args in
 OPTION_MAP (λk. tm_return (RUN k tm0)) (OLEAST n. HALTED (RUN n tm0))`

val un_nlist_def = tDefine"un_nlist"`
(un_nlist 0 = []) ∧ (un_nlist l = [nfst (l-1)] ++ (un_nlist (nsnd (l-1))) )`
(qexists_tac `$<` >> simp[] >> strip_tac >> `nsnd v <= v` by simp[nsnd_le] >>
`v < SUC v` by fs[] >> fs[])



val INITIAL_TM_NUM_def = Define`INITIAL_TM_NUM  = λn. ⟦INITIAL_TM FEMPTY (un_nlist (proj 0 n))⟧`

val RUN_NUM_def = Define`
RUN_NUM p targs = Pr (INITIAL_TM_NUM) (Cn (pr1 (tmstepf p)) [proj 1]) targs`

val tm_return_num_def = Define`
tm_return_num = Pr (Cn (pr1 nsnd) [Cn (pr1 nsnd) [proj 0]])
         (pr_cond (Cn pr_eq [Cn pr_mod [Cn pr_div [proj 2;proj 0]; twof]; zerof])
             (proj 1) (Cn (pr2 $+) [proj 1;onef] )  ) `

val _ = temp_set_fixity "*." (Infixl 600)
val _ = temp_overload_on ("*.", ``λn m. Cn (pr2 $*) [n; m]``)


val pr_exp_def = Define`
pr_exp = Cn (Pr onef ( proj 1 *. ( proj 2))) [proj 1;proj 0]`

val primrec_pr_exp = Q.store_thm(
"primrec_pr_exp[simp]",
`primrec pr_exp 2`,
 rw[pr_exp_def] >> SRW_TAC [][primrec_rules] >> SRW_TAC [][pr_cond_def] >>
  rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules])  );


val tm_log_num_def = Define`
tm_log_num  = minimise (SOME ∘ (Cn pr_eq
 [Cn pr_mod [Cn pr_div [proj 1; Cn pr_exp [twof;Cn succ [proj 0] ] ];twof ] ;zerof ] ) ) `

val primrec_tm_log_num = Q.store_thm("primrec_tm_log_num",
`primrec (Cn pr_eq [Cn pr_mod [Cn pr_div [proj 1; Cn pr_exp [twof;Cn succ [proj 0] ] ];twof ] ;
                    zerof ] )  2`,
SRW_TAC [][primrec_rules] >> SRW_TAC [][pr_cond_def] >>
rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> simp[primrec_pr_exp] )

val recfn_rulesl = CONJUNCTS recfn_rules
val recfnMin = save_thm("recfnMin", List.nth(recfn_rulesl, 5))

val recfn_tm_log_num = Q.store_thm("recfn_tm_log_num",
`recfn tm_log_num 1`,
`recfn (SOME o (Cn pr_eq [Cn pr_mod [Cn pr_div [proj 1; Cn pr_exp [twof;Cn succ [proj 0]] ];twof ] ;
    zerof ])) 2` by simp[primrec_recfn,primrec_tm_log_num] >> rw[tm_log_num_def] >>
                                       rfs[recfnMin])


val primrec_tm_ret_run = Q.store_thm("primrec_tm_ret_run",
`primrec tm_return_num 2`,
`primrec (Cn (pr1 nsnd) [Cn (pr1 nsnd) [proj 0]]) 1` by (SRW_TAC [][primrec_rules] >>
 SRW_TAC [][pr_cond_def] >> rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules])) >>
`primrec (pr_cond (Cn pr_eq [Cn pr_mod [Cn pr_div [proj 2;proj 0]; twof]; zerof])
                  (proj 1) (Cn (pr2 $+) [proj 1;onef] )) 3` by  (SRW_TAC [][primrec_rules] >>
SRW_TAC [][pr_cond_def] >> rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]))  >>
rw[tm_return_num_def,primrec_pr] )


val INITIAL_TAPE_PRES_STATE = Q.store_thm("INITIAL_TAPE_PRES_STATE[simp]",
`(INITIAL_TAPE_TM tm k).state = tm.state`,
Cases_on `k` >> rw[INITIAL_TAPE_TM_def])


val pr_neq_def = Define`
pr_neq = Cn (pr2 $+) [Cn (pr2 $-) [pr_le; cflip pr_le]; Cn (pr2 $-) [cflip pr_le; pr_le]]
`;

 val pr_neq_thm = Q.store_thm(
"pr_neq_thm",
`pr_neq [n;  m] = nB (n <> m)`,
SRW_TAC [ARITH_ss][pr_neq_def] >> Cases_on `n<=m` >> Cases_on `m<=n` >> fs[] );

val primrec_pr_neq = Q.store_thm(
"primrec_pr_neq[simp]",
`primrec pr_neq 2`,
SRW_TAC [][pr_neq_def, primrec_rules]);


val el_zero_def = Define`(el_zero 0 = 1) ∧
(el_zero (SUC n) = let t = ntl (SUC n) in napp (el_zero n) (ncons (nel t (el_zero n) + 1) 0) )`

val nlist_of_unnlist = Q.store_thm("nlist_of_unnlist[simp]",
`nlist_of (un_nlist n) = n`,
completeInduct_on `n` >> Cases_on `n` >- EVAL_TAC >> fs[un_nlist_def] >>
`nsnd n' < SUC n'` by metis_tac[nsnd_le,prim_recTheory.LESS_SUC_REFL,LESS_EQ_LESS_TRANS] >>
rw[ncons_def] >> fs[npair] )

val un_nlist_nlist_of_inv = Q.store_thm("un_nlist_nlist_of_inv[simp]",
`un_nlist (nlist_of n) = n`,
Induct_on `n`  >> fs[nlist_of_def,un_nlist_def,ncons_def] >> strip_tac >>`h ⊗ nlist_of n + 1 = SUC (h ⊗ nlist_of n)` by fs[] >>  rw[un_nlist_def] )

val ntl_nlist_unnlist = Q.store_thm("ntl_nlist_unnlist",
`ntl (SUC n) = nlist_of (TL (un_nlist (SUC n)))`,
 rw[ntl_def,un_nlist_def] )

val length_unnlist = Q.store_thm("length_unnlist",
`0 < LENGTH (un_nlist (SUC n))`,
fs[un_nlist_def])

val ntl_suc_less = Q.store_thm("ntl_suc_less",
`∀n. ntl (SUC n) <= n`,
strip_tac >> rw[ntl_def,nsnd_le])

val el_zero_corr = Q.store_thm("el_zero_corr",
`el_zero n = nlist_of (GENLIST (LENGTH o un_nlist) (n+1))`,
Induct_on `n` >> fs[el_zero_def] >- EVAL_TAC >> `ntl (SUC n) <= n` by simp[ntl_suc_less] >>
simp[ADD_CLAUSES,GENLIST,SNOC_APPEND,nel_nlist_of] >> fs[ntl_nlist_unnlist,un_nlist_nlist_of_inv]>>
fs[LENGTH_TL,length_unnlist] >> rw[nlist_of_def,nlist_of_append] >>
`1 <= LENGTH (un_nlist (SUC n))` by (`1 = SUC 0` by fs[] >> metis_tac[length_unnlist,LESS_OR]) >>
fs[SUB_ADD,ADD1] )

val nleng_def = Define `nleng n = nel n (el_zero n)`

(*  add_persistent_funs ["numpair.nlistrec_def"] *)


val nlen_reduc = Q.store_thm("nlen_reduc",
`∀n. nlen (SUC n) = nlen (ntl (SUC n)) + 1`,
strip_tac >> `SUC n <> 0` by fs[] >>`∃h t. SUC n = ncons h t ` by metis_tac[nlist_cases] >>
          rw[nlen_thm,ntl_thm])




val pr_el_zero_def = Define`
pr_el_zero = Cn (Pr (onef) (Cn (pr2 napp) [ proj 1 ;
Cn (pr2 ncons) [Cn succ [Cn (pr2 nel) [Cn (pr1 ntl) [Cn succ [proj 0]];proj 1] ];zerof] ])) [proj 0;onef]`

val primrec_pr_el_zero = Q.store_thm("primrec_pr_el_zero",
`primrec pr_el_zero 1`,
fs[pr_el_zero_def] >> rpt (irule primrec_cn >> rw[primrec_rules]) >> irule alt_Pr_rule >>
  fs[primrec_rules] >> rpt (irule primrec_cn >> rw[primrec_rules]))

val primrec_el_zero = Q.store_thm("primrec_el_zero",
`primrec (pr1 el_zero) 1`,
`(∃g. primrec g 1 ∧ ∀n. g [n] = el_zero n)` suffices_by fs[primrec_pr1] >>
 qexists_tac `pr_el_zero` >> fs[primrec_pr_el_zero] >> strip_tac >> Induct_on `n` >- EVAL_TAC >>
 rw[el_zero_def,pr_el_zero_def] >> `Pr onef (Cn (pr2 napp) [proj 1;
 Cn (pr2 ncons) [Cn succ [Cn (pr2 nel) [Cn (pr1 ntl) [Cn succ [proj 0]]; proj 1]]; zerof]]) [n; 1]= pr_el_zero [n]` by
 fs[pr_el_zero_def] >> rfs[] >> rw[] >> fs[ADD1] )

val primrec_nleng = Q.store_thm("primrec_nleng",
`primrec (pr1 nleng) 1`,
`(∃g. primrec g 1 ∧ ∀n. g [n] = nleng n)` suffices_by fs[primrec_pr1] >>
 qexists_tac`Cn (pr2 nel) [proj 0;Cn (pr1 el_zero) [proj 0]]` >> conj_tac
 >- (rpt (irule primrec_cn >> rw[primrec_rules]) >> fs[primrec_el_zero])
 >- (strip_tac >> fs[nleng_def]  )  )

val Pr_eval = prove(
``0 < m ==> (Pr b r (m :: t) = r (m - 1 :: Pr b r (m - 1 :: t) :: t))``,
STRIP_TAC THEN SIMP_TAC (srw_ss()) [Once Pr_def, SimpLHS] THEN
          Cases_on `m` THEN SRW_TAC [ARITH_ss][]);


(* Pr defs, probs use *)
val pr_log_def = Define`
pr_log = Cn (pr2 $- ) [Cn (Pr (zerof) (Cn (pr2 $+) [proj 1; Cn pr_neq [zerof;Cn pr_div [Cn (pr1 nfst) [proj 2];
         Cn pr_exp [Cn (pr1 nsnd) [proj 2];proj 0 ]]]]))
            [proj 0;Cn (pr2 npair) [proj 0;proj 1]];onef]`

val pr_tl_en_con_fun2_def = Define`
pr_tl_en_con_fun2 =
               Cn (pr2 $+) [Cn (pr2 $* )
  [Cn (pr2 $-) [ Cn pr_exp [twof;Cn (pr2 nel)
  [proj 0;proj 2 ]];onef ];
      Cn pr_exp [twof;Cn pr_log [proj 1;twof] ] ];
                                proj 1] `;

val order_flip_def = Define`
order_flip = Cn (Pr (zerof )
                (Cn (pr2 ncons) [Cn (pr2 nel) [proj 0;proj 2] ;proj 1] ))
                [Cn (pr1 nleng) [proj 0];proj 0]`;

val pr_tl_en_con_fun4_def = Define`
pr_tl_en_con_fun4 = Cn (pr2 $+) [Cn (pr2 $-)
                   [Cn pr_exp [twof;Cn (pr2 nel) [proj 0;Cn order_flip [proj 2] ]];onef ];
                    Cn (pr2 $* ) [proj 1;Cn pr_exp [twof;Cn succ
   [ Cn pr_log [Cn pr_exp [twof;Cn (pr2 nel) [proj 0;Cn order_flip [proj 2]]] ; twof]] ]]] `;

val pr_tl_en_con_def = Define`
pr_tl_en_con = Cn (pr1 DIV2) [Cn (Pr (zerof) (pr_tl_en_con_fun4)) [Cn (pr1 nleng) [proj 0];proj 0]]`;

val primrec_order_flip = Q.store_thm("primrec_order_flip",
`primrec order_flip 1`,
rw[order_flip_def] >> rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >>fs[primrec_nleng]  )

val primrec_pr_log = Q.store_thm("primrec_pr_log",
`primrec pr_log 2`,
rw[pr_log_def] >> rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> irule alt_Pr_rule >> rw[primrec_rules] >> rpt (irule primrec_cn >> rw[primrec_rules]));


val primrec_pr_tl_en_con_fun4 = Q.store_thm("primrec_pr_tl_en_con_fun4",
`primrec pr_tl_en_con_fun4 3`,
rw[pr_tl_en_con_fun4_def] >> rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> rw[primrec_rules,primrec_pr_exp,primrec_order_flip,primrec_pr_log] >> fs[primrec_nleng] );

val primrec_pr_tl_en_con = Q.store_thm("primrec_pr_tl_en_con",
`primrec pr_tl_en_con 1`,
SRW_TAC [][pr_tl_en_con_def,primrec_rules] >>
        rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules,primrec_div2,primrec_nleng]) >>
        fs[primrec_nleng] >>  irule alt_Pr_rule >> rw[primrec_pr_tl_en_con_fun4] );


(* Works up to here  *)
(* WORK IN PROGRESS SECTION   *)
val invtri_zero = Q.store_thm("invtri_zero[simp]",
`invtri 0 = 0`,
EVAL_TAC)

val ntl_zero = Q.store_thm("ntl_zero[simp]",
`ntl 0 = 0`,
EVAL_TAC)

val invtri_nzero = Q.store_thm("invtri_nzero[simp]",
`(invtri n = 0) <=> (n = 0)`,
eq_tac >> fs[] >>
       SRW_TAC [][invtri_def] >>
       Q.SPECL_THEN [`n`, `0`] MP_TAC invtri0_thm >>
       SRW_TAC [ARITH_ss][tri_def] >> `n < SUC 0` by metis_tac[SND_invtri0] >> rw[]
)

val nsnd_fun_thm = Q.store_thm("nsnd_fun_thm[simp]",
`(nsnd n = n) <=>  (n = 0)`,
eq_tac >> rw[nsnd_def]  >> Cases_on `n` >> fs[] >>
`tri (invtri (SUC n')) = 0` by  fs[SUB_EQ_EQ_0] >> `tri 0 = 0` by fs[tri_def] >>
`invtri (SUC n') = 0` by rfs[tri_11]  >>  fs[])

val nsnd_lthen = Q.store_thm("nsnd_lthen[simp]",
`∀n. (nsnd n < n)<=> (n<> 0)`,
strip_tac >> eq_tac >> fs[] >> strip_tac >> `nsnd n <= n` by fs[nsnd_le] >> `nsnd n <> n` by fs[] >> rw[])

val FUNPOW_mono = Q.store_thm("FUNPOW_mono",
`(∀n m. m <= n ==> f m <= f n) ==> (∀n m k. m <= n ==> FUNPOW f k m <= FUNPOW f k n)`,
rpt strip_tac >> Induct_on `k` >> fs[] >> fs[FUNPOW_SUC] )


(* fix or remove 
val ndrop_zero = Q.store_thm("ndrop_zero[simp]",
`(ndrop n (SUC n) = 0) <=>  (n <> 0)`,
Cases_on `n` >> rw[ndrop_def] >> fs[ndrop_FUNPOW_ntl] >>
`ntl (FUNPOW ntl n' (SUC (SUC n'))) = FUNPOW ntl (SUC n') (SUC (SUC n'))` by
metis_tac[FUNPOW_SUC,FUNPOW] >> rw[] >> pop_assum kall_tac >>
Induct_on `n'` >- (EVAL_TAC) >>
`ntl (SUC (SUC (SUC  n'))) <= SUC (SUC n')` by fs[ntl_suc_less] >> fs[FUNPOW] >> fs[Once ntl_def]>>
fs[Once ntl_def] >> `

`∀n. (λt. nsnd (t - 1)) n = nsnd (n-1)` by fs[] >>
`ntl =  (λt. nsnd (t - 1))` by metis_tac[ntl_def] >> rw[] >> rpt (pop_assum kall_tac) >>
Induct_on `n'` >- (EVAL_TAC) >>
`FUNPOW (λt. nsnd (t − 1)) (SUC n') (SUC (SUC (SUC n'))) = 0` by (fs[FUNPOW]) >>  fs[FUNPOW_SUC] >>fs[FUNPOW]

`∀n. nsnd n <= n` by fs[nsnd_le] >>`∀n.  n - 1 < SUC n` by fs[]  >>`∀n. nsnd ((SUC n)-1) < SUC n` by (rfs[]) >> )

val pr_nlen_reduc = Q.store_thm("pr_nlen_reduc",
`pr_nlen [SUC n] = pr_nlen [ntl (SUC n)] + 1`,cheat)
(`ntl (SUC n) = ndrop 1 (SUC n)` by fs[ndrop_FUNPOW_ntl] >> rw[] >> pop_assum kall_tac >>
  rw[pr_nlen_def,pr_neq_thm,Pr_thm] >> Cases_on `ndrop n (SUC n) = 0` >> fs[]
  >- (rw[Pr_eval])
  >- (Cases_on `0<n` >> fs[] >> rw[Pr_eval])
)

 

val pr_nlen_correct = Q.store_thm("pr_nlen_correct",
`∀n. pr_nlen [n] = nlen n`,
strip_tac  >> completeInduct_on `n` >> Cases_on `n` >- (EVAL_TAC) >>
          rw[nlen_reduc] >> `ntl (SUC n')  <= n'` by fs[ntl_suc_less] >> `n' < SUC n'` by fs[] >>
`ntl (SUC n')  < SUC n'` by fs[] >>
` nlen (ntl (SUC n')) = pr_nlen [ntl (SUC n')] ` by rfs[] >> pop_assum MP_TAC >>
rpt (pop_assum kall_tac) >> strip_tac >> rw[] >>pop_assum kall_tac >> fs[pr_nlen_reduc]
 )

val primrec_nlen = Q.store_thm("primrec_nlen",
`primrec (pr1 nlen) 1`,
`∃g. primrec g 1 ∧ ∀n. g [n] = nlen n` suffices_by fs[primrec_pr1] >> qexists_tac`pr_nlen` >> fs[primrec_pr_nlen,pr_nlen_correct])

val order_flip_correct = Q.store_thm("order_flip_correct[simp]",
`order_flip [nlist_of l] = nlist_of (REVERSE l)`,
  Induct_on `l` >> fs[nlist_of_def] >- (EVAL_TAC) >> strip_tac >> fs[order_flip_def] )

 can remove?
val pr_nlist_len_correct = Q.store_thm("pr_nlist_len_correct[simp]",
`pr_nlist_len [k] = LENGTH (un_nlist k)`,
`∃l. k=nlist_of l` by metis_tac[nlist_of_onto] >> simp[un_nlist_nlist_of_inv] >> pop_assum kall_tac >> Induct_on `l` >> fs[] >- (EVAL_TAC))


val nleng_corr = Q.store_thm("nleng_corr[simp]",
`nleng (nlist_of l) = LENGTH l`,
fs[nleng_def,nel_nlist_of,el_zero_corr])
 *)
open logrootTheory;

val ENCODE_TL_DIV2 = Q.store_thm("ENCODE_TL_DIV2",
`ENCODE (TL (h::t)) = DIV2 (ENCODE (h::t))`,
Cases_on `h` >> fs[ENCODE_def,DIV2_def,TWO_TIMES_DIV_TWO_thm])

val el_zero_exp = Q.store_thm("el_zero_exp",
`el_zero n = nlist_of ((GENLIST (LENGTH ∘ un_nlist) n) ++ [(LENGTH ∘ un_nlist) n])`,
`n+1 = SUC n` by fs[ADD1] >> rw[GENLIST,SNOC_APPEND,el_zero_corr] )

val el_zero_napp = Q.store_thm("el_zero_napp",
`el_zero n = napp (nlist_of (GENLIST (LENGTH ∘ un_nlist) n)) (nlist_of [(LENGTH ∘ un_nlist) n])`,
fs[nlist_of_append,el_zero_exp] )

val len_un_nlist_nsnd = Q.store_thm("len_un_nlist_nsnd",
`LENGTH (un_nlist (nsnd n)) = LENGTH (TL (un_nlist (SUC n)))`,
Cases_on `nsnd n` >> fs[un_nlist_def])

val len_un_nlist_nsnd2 = Q.store_thm("len_un_nlist_nsnd2",
`LENGTH (un_nlist (nsnd n)) = LENGTH (un_nlist (SUC n)) - 1`,
fs[len_un_nlist_nsnd,LENGTH_TL,length_unnlist])


val r_zero_def = Define`(r_zero 0 = ncons 0 0)∧
     (r_zero (SUC n) =
   let t = ntl (SUC n);r0n = r_zero n; revt = nel t r0n; res = napp revt (ncons (nhd (SUC n)) 0) in napp r0n (ncons res 0))`

val r_zero_corr = Q.store_thm("r_zero_corr",
`r_zero n = nlist_of (GENLIST (nlist_of o REVERSE o un_nlist) ( n+1))`,
Induct_on `n` >> fs[un_nlist_def,r_zero_def,ADD_CLAUSES] >>`ntl (SUC n)<= n` by fs[ntl_suc_less]>>
rw[GENLIST, SNOC_APPEND,nel_nlist_of] >> rw[nlist_of_append] >> rw[ADD1] >>`∃l. n+1 = nlist_of l`
by metis_tac[nlist_of_onto]>> rw[] >> Cases_on `l` >> fs[nlist_of_append]  )

val _ = overload_on ("order_flip" ,``pr1 (λn. nel n (r_zero n))``)

val order_flip_corr = Q.store_thm("order_flip_corr",
`order_flip [n] = nlist_of (REVERSE (un_nlist n))`,
fs[r_zero_corr,nel_nlist_of])

val un_nlist_ncons = Q.store_thm("un_nlist_ncons[simp]",
`un_nlist (ncons h t) = h::un_nlist t`,
fs[ncons_def,un_nlist_def,GSYM ADD1])

val order_flip_ncons = Q.store_thm("order_flip_ncons[simp]",
`order_flip [ncons h t] = napp (order_flip [t]) (ncons h 0)`,
 fs[order_flip_corr,nlist_of_append] )

val list_rec_comb_def = Define`(list_rec_comb c n 0 = ncons n 0)∧
     (list_rec_comb c n (SUC k) = let t = ntl (SUC k);h=nhd (SUC k); rl = list_rec_comb c n k;
     r = nel t rl in napp rl (ncons (c [h; t; r]) 0))  `

val LIST_REC_def = Define`(LIST_REC c (n:num) [] = n) ∧
     (LIST_REC c n (h::t) = c [h;nlist_of t;LIST_REC c n t])`

val list_rec_comb_corr = Q.store_thm("list_rec_comb_corr",
`list_rec_comb c n k = nlist_of (GENLIST (LIST_REC c n o un_nlist) (k+1))`,
Induct_on `k` >> fs[un_nlist_def,list_rec_comb_def,LIST_REC_def,ADD_CLAUSES] >> `ntl (SUC k)<= k` by fs[ntl_suc_less]>> rw[GENLIST, SNOC_APPEND,nel_nlist_of] >> rw[nlist_of_append] >> rw[ADD1] >>`∃l. k+1 = nlist_of l`
by metis_tac[nlist_of_onto]>> rw[] >> Cases_on `l` >> fs[nlist_of_append] >> rw[LIST_REC_def] )

val primrec_list_rec_comb = Q.store_thm("primrec_list_rec_comb",
`(primrec c 3) ==> (primrec (pr1 (list_rec_comb c n)) 1)`,
strip_tac >> irule primrec_pr1 >> qexists_tac`Pr1 (ncons n 0) (Cn (pr2 napp) [proj 1;Cn (pr2 ncons) [Cn c [Cn (pr1 nhd) [Cn succ [proj 0]];Cn (pr1 ntl) [Cn succ [proj 0]];Cn (pr2 nel) [Cn (pr1 ntl) [Cn succ [proj 0]];proj 1 ]];zerof]])` >> conj_tac >- (irule primrec_Pr1 >> rpt (irule primrec_cn >> rw[primrec_rules,primrec_napp,primrec_ncons])) >> Induct >> fs[list_rec_comb_def])

val list_num_rec_thm = Q.store_thm("list_num_rec_thm",
`∀n c.(primrec c 3)==> ∃f.(primrec f 1) ∧ (f [0] = n) ∧ (∀h t. f [ncons h t] = c [h; t; (f [t])])`,
rpt strip_tac >> qexists_tac`Cn (pr2 nel) [proj 0;Cn (pr1 (list_rec_comb c n)) [proj 0]] ` >>
rpt conj_tac >- (rpt (irule primrec_cn >> rw[primrec_rules,primrec_nel,primrec_list_rec_comb]))>>
 simp[list_rec_comb_def] >> simp[list_rec_comb_corr,nel_nlist_of,LIST_REC_def] )

val nleng_thm = new_specification("nleng_def", ["nleng"],
list_num_rec_thm |> SPECL[``0n``,``Cn succ [proj 2]``]
                 |> SIMP_RULE (srw_ss())[primrec_cn, primrec_rules])

val nrev_thm = new_specification("nrev_def", ["nrev"],
list_num_rec_thm |> SPECL[``0n``,``Cn (pr2 napp) [proj 2;Cn (pr2 ncons) [proj 0;zerof] ]``] 
                 |> SIMP_RULE (srw_ss())[primrec_cn, primrec_rules])

val concatWith_Z_thm = new_specification("concatWith_Z_def", ["concatWith_Z"],
 list_num_rec_thm |> SPECL[``0n``,``pr_cond (Cn pr_eq [proj 1;zerof])
 (proj 0) (Cn (pr2 napp) [proj 0; Cn (pr2 napp) [onef;proj 2]])``]
                 |> SIMP_RULE (srw_ss())[primrec_cn, primrec_rules])

val concatWith_Z_corr = Q.store_thm("concatWith_Z_corr",
`concatWith_Z [x] = nlist_of (concatWith [0] (MAP un_nlist (un_nlist x)))`,
completeInduct_on `x` >> `(x = 0) ∨ ∃h t. x = ncons h t` by metis_tac[nlist_cases] >>
simp[concatWith_Z_thm,un_nlist_def,concatWith_def] >> rw[] >>
simp[concatWith_Z_thm,un_nlist_def,concatWith_def] >> `t < ncons h t` by (simp[ncons_def] >>
`t = nsnd (h *, t)` by simp[] >> `nsnd (h *, t) <= h *, t` by simp[nsnd_le] >> simp[] ) >>
RES_TAC >> simp[concatWith_def] >> `∃h' t'. t = ncons h' t'` by metis_tac[nlist_cases] >>
simp[concatWith_def] >> simp[nlist_of_append,ncons_def,npair_def,tri_def,napp_ASSOC] )


(** May not need
val primrec_TL_ENCODE_concat_gen_un_nlist = Q.store_thm("primrec_TL_ENCODE_concat_gen_un_nlist",
`pr_tl_en_con = λm. if  (m=[]) ∨ (HD m = 0) then 0
                  else  ENCODE (TL (concatWith [Z] (MAP (GENLIST (K O)) (un_nlist (proj 0 m))))) `,
simp[FUN_EQ_THM] >> rw[]
  >- (Induct_on `m` >> fs[] >> EVAL_TAC)
  >- (`(m <>[]) ∧ ¬(HD m = 0)` by rfs[NOT_IMP] >> simp[pr_tl_en_con_def]>>
     `proj 0 m <> 0` by fs[proj_thm,proj_def] >> qabbrev_tac`k = proj 0 m` >> rpt strip_tac>>
     `∃k'. k = SUC k'` by metis_tac[num_CASES] >> rw[nleng_def,el_zero_corr] >> rw[nel_thm] >>
     `SUC k' +1 = SUC (k' +1)` by fs[] >>rw[] >> simp[GENLIST,nlist_of_def]>>
`k'+1 = SUC k'` by fs[ADD1] >> Q.UNDISCH_THEN `k<>0` mp_tac >>
rpt (pop_assum kall_tac) >>
     fs[nel_nlist_of]  >>
     `(LENGTH (GENLIST (LENGTH ∘ un_nlist) (SUC k'))) = (SUC k')` by fs[LENGTH_GENLIST] >>
     `EL (SUC k') (SNOC (LENGTH (un_nlist (SUC k'))) (GENLIST (LENGTH ∘ un_nlist)
      (SUC k'))) =  (LENGTH (un_nlist (SUC k')))` by
     metis_tac[EL_LENGTH_SNOC] >> rw[] >> rpt (pop_assum kall_tac) >>

     completeInduct_on ` k` >> strip_tac >> `∃l. k = nlist_of l` by metis_tac[nlist_of_onto] >>rw[]
     fs[] >> Cases_on `l` >> fs[] >> simp[CONV_RULE FUN_EQ_CONV pr_tl_en_con_fun4_def] >> 
     Cases_on `MAP (GENLIST (K O)) (un_nlist (SUC k'))` >> rw[concatWith_def] >- () >>
     Cases_on `t` >> rw[TL,concatWith_def]>>
      >>
      >>
   >> fs[ENCODE_TL_DIV2]     ) ) **)

val INITIAL_TAPE_PRES_L = Q.store_thm("INITIAL_TAPE_PRES_L[simp]",
`(INITIAL_TAPE_TM tm (h::t)).tape_l = []`,
fs[INITIAL_TAPE_TM_def])

val tape_encode_def = Define `tape_encode = pr_cond (Cn pr_eq [proj 1;zerof])
   (Cn (pr2 npair) [proj 0;Cn (pr2 $*) [twof;proj 2]])
  (Cn (pr2 npair) [proj 0;Cn succ [Cn (pr2 $* ) [twof;proj 2]]])`

val primrec_tape_encode = Q.store_thm("primrec_tape_encode[simp]",
`primrec tape_encode 3`,
fs[tape_encode_def] >> irule primrec_pr_cond >> rpt (irule primrec_cn >> rw[primrec_rules,primrec_pr_cond,primrec_pr_eq,primrec_pr_mult]))

val tape_encode_corr = Q.store_thm("tape_encode_corr",
`tape_encode [ENCODE tm.tape_l;NUM_CELL tm.tape_h;ENCODE tm.tape_r] = ENCODE_TM_TAPE tm`,
fs[tape_encode_def,ENCODE_TM_TAPE_def] >> `CELL_NUM (NUM_CELL tm.tape_h) = tm.tape_h` by
 fs[CELL_NUM_NUM_CELL]>> `CELL_NUM 0 = Z` by fs[CELL_NUM_def]>>`NUM_CELL Z = 0` by fs[NUM_CELL_def]
>>`(NUM_CELL tm.tape_h = 0) ⇔ (tm.tape_h = Z)` by metis_tac[NUM_CELL_INJ] >>rw[] )

val tape_encode_corr_sym = Q.store_thm("tape_encode_corr_sym",
`ENCODE_TM_TAPE tm = tape_encode [ENCODE tm.tape_l;NUM_CELL tm.tape_h;ENCODE tm.tape_r]`,
fs[tape_encode_corr])

val pr_INITIAL_TAPE_TM_NUM_def = Define`
pr_INITIAL_TAPE_TM_NUM = pr_cond (Cn pr_eq [proj 1;zerof]) (proj 0) (Cn (pr2 npair)
[Cn (pr1 nfst) [proj 0];Cn (pr2 npair) [Cn (pr1 nhd) [proj 1];Cn (pr1 ntl) [proj 1]] ])`

val primrec_pr_INITIAL_TAPE_TM_NUM = Q.store_thm("primrec_pr_INITIAL_TAPE_TM_NUM[simp]",
`primrec pr_INITIAL_TAPE_TM_NUM 2`,
fs[pr_INITIAL_TAPE_TM_NUM_def] >> `0<2` by fs[] >>irule primrec_pr_cond >> rpt (irule primrec_cn >> rw[primrec_rules,primrec_pr_eq,primrec_nsnd,primrec_nfst] ) >>fs[primrec_proj] )

val pr_INITIAL_TM_NUM_def = Define`
pr_INITIAL_TM_NUM = Cn (pr2 npair) [zerof;Cn tape_encode
 [Cn (pr1 nfst) [Cn pr_INITIAL_TAPE_TM_NUM [zerof;Cn concatWith_Z [proj 0]]];
  Cn (pr1 nfst) [Cn (pr1 nsnd) [Cn pr_INITIAL_TAPE_TM_NUM [zerof;Cn concatWith_Z [proj 0]]]];
  Cn (pr1 nsnd) [Cn (pr1 nsnd) [Cn pr_INITIAL_TAPE_TM_NUM [zerof;Cn concatWith_Z [proj 0]]]]]]`

val primrec_pr_INITIAL_TM_NUM = Q.store_thm("primrec_pr_INITIAL_TM_NUM[simp]",
`primrec pr_INITIAL_TM_NUM 1`,
SRW_TAC [][pr_INITIAL_TM_NUM_def,primrec_rules] >>
rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules,concatWith_Z_thm,primrec_pr_INITIAL_TAPE_TM_NUM,primrec_tape_encode,primrec_npair,primrec_ntl,primrec_nhd]))


val nfst_zero = Q.store_thm("nfst_zero[simp]", `nfst 0 = 0`, EVAL_TAC)
val nsnd_zero = Q.store_thm("nsnd_zero[simp]", `nsnd 0 = 0`, EVAL_TAC)
val nhd_zero = Q.store_thm("nfst_zero[simp]", `nhd 0 = 0`, EVAL_TAC)
val ntl_zero = Q.store_thm("nsnd_zero[simp]", `ntl 0 = 0`, EVAL_TAC)

val nhd_nlist_of = Q.store_thm("nhd_nlist_of[simp]",
`nhd (nlist_of (h::t)) = h`,
fs[nhd_thm,nlist_of_def])

val ntl_nlist_of = Q.store_thm("ntl_nlist_of[simp]",
`ntl (nlist_of (h::t)) = nlist_of t`,
fs[ntl_thm,nlist_of_def])

val tape_encode_thm = Q.store_thm("tape_encode_thm",
`tape_encode [a;b;c] = if b=0 then a *, (2* c) else a *, (SUC (2*c))`,
fs[tape_encode_def])

val tape_encode_eq = Q.store_thm("tape_encode_eq",
`(((b=0) ∨ (b=1)) ∧ ((e=0) ∨ (e=1))) ==>
                     ( (tape_encode [a;b;c] = tape_encode [d;e;f]) <=> ((a=d) ∧ (b=e) ∧(c=f)))`,
strip_tac >> eq_tac >> rw[tape_encode_thm]
         >- (CCONTR_TAC >> rfs[] >> `ODD (SUC (2* f))` by fs[ODD_DOUBLE] >> `EVEN (2*c)` by
           fs[EVEN_DOUBLE] >> rfs[EVEN_AND_ODD] >> fs[EVEN,EVEN_DOUBLE] )
         >- (CCONTR_TAC >> rfs[] >> `ODD (SUC (2* c))` by fs[ODD_DOUBLE] >> `EVEN (2*f)` by
           fs[EVEN_DOUBLE] >> rfs[EVEN_AND_ODD] >> metis_tac[EVEN_AND_ODD])  )

(* currently working on 
val primrec_INITIAL_TM_NUM = Q.store_thm("primrec_INITIAL_TM_NUM",
`primrec INITIAL_TM_NUM 1`,
`INITIAL_TM_NUM = pr_INITIAL_TM_NUM` suffices_by fs[primrec_pr_INITIAL_TM_NUM] >>
 fs[FUN_EQ_THM] >> strip_tac >>
 fs[INITIAL_TM_NUM_def,INITIAL_TM_def,un_nlist_def,INITIAL_TAPE_TM_def,FULL_ENCODE_TM_def,STATE_TO_NUM_def] >> Cases_on `(concatWith [Z] (MAP (GENLIST (K O)) (un_nlist (proj 0 x))))` >>
fs[INITIAL_TAPE_TM_def]  >>
fs[pr_INITIAL_TM_NUM_def,pr_INITIAL_TAPE_TM_NUM_def,tape_encode_corr,concatWith_Z_corr]>>
Cases_on `nlist_of (concatWith [0] (MAP un_nlist (un_nlist (proj 0 x))))` >> rw[] >-
(`tape_encode [0;0;0] = tape_encode [ENCODE [];NUM_CELL Z;ENCODE []]` by
 fs[ENCODE_def,NUM_CELL_def] >> asm_simp_tac list_ss [tape_encode_corr_sym,EQ_SYM] >> fs[] )
>- (fs[tape_encode_corr_sym,ENCODE_def] >> fs[tape_encode_eq] >> )
>- (contra)
>- (fs[tape_encode_corr_sym] >> rw[nhd_nlist_of,ENCODE_def] )
    )

val primrec_RUN_NUM = Q.store_thm("primrec_RUN_NUM",
`primrec (RUN_NUM p) 2`,
rw[RUN_NUM] >> fs[primrec_INITIAL_TM_NUM,primrec_cn,primrec_tmstepf,alt_Pr_rule])

val recfn_tm_def = Define`
recfn_tm p n = (recCn (SOME o tm_return_num)
  [recCn tm_log_num [SOME o (RUN_NUM p) ];SOME o (RUN_NUM p)])
  [minimise (SOME o
    (pr_cond (Cn pr_eq [Cn (RUN_NUM p) [proj 0];Cn (RUN_NUM p) [Cn (pr2 $+) [proj 0;onef]
                    ] ] ) ) ) n; proj 0 n]`

val recfn_tm_recfn = Q.store_thm("recfn_tm_recfn",
`recfn (recfn_tm p) 1`,
fs[primrec_tmstepf,primrec_recfn,INITIAL_TM_NUM_PR,primrec_rules] )

val main_eq_thm = Q.store_thm("main_eq_thm",
`∀p. ∃f. (recfn f 1) ∧ (∀ args. tm_fn p args = f [nlist_of args])`,
strip_tac >> qexists_tac`recfn_tm p` >- (fs[recfn_tm_recfn]) >> strip_tac >> )


*)

(*
<== Direction
Partial rec ==> ∃ tm that can simulate
Use register machines
*)






(*)
primerec (tmstepf tm) 1

∀tm ∃f ∀n

val TM_EQIV_REC_FUN = store_thm(
  "TM_EQIV_REC_FUN",
  `∀ tm. ∃f.  ∀ n. ∃ t. (recfn f 1) ∧  (ENCODE_TM_TAPE (RUN t tm (DECODE n)) = f [n]) `,
  completeInduct_on `TURING_MACHINE_P_ENCODING tm` >> EVAL_TAC >>
`recfn (recPhi o CONS i) 1` by metis_tac[prtermTheory.recfn_recPhi_applied] 
>> REPEAT strip_tac >> FULL_SIMP_TAC (srw_ss()) [] >> EXISTS_TAC `(recPhi o CONS i)`
rw[] >>

  strip_tac >> exists_tac `recPhi` >> conj_tac >> simp[]
  >-
  >-
);

val REC_FUN_EQUIV_TM = store_thm(
    "REC_FUN_EQUIV_TM",
`∀ f. ∃ tm. ∀ n.  ∃ t. (recfn f 1)  ( f[n] = DECODE_TM_TAPE (RUN t tm (ENCODE n)) )`,
    );


val UNIVERSAL_TM_EXIST = store_thm (
        "UNIVERSAL_TM_EXIST",
        `!T:TM. ?U:TM. !input:TM_input. ?u_input:TM_input. (INITIAL_TM U (u_input++input))=(INITIAL_TM T input)`,
        insert_proof_here
    );
*)


 (* Proving the other direction
    We only accept unitary input,
    This means that whenever we have 00
    we will have reached the end of and input *)

(*  Other direction
val zero_tm_def = Define`zero_tm x = ENCODE_TM_TAPE (RUN (2*(LENGTH x))  <| state := 0;
                                  prog := FEMPTY |++ [((0,Z),(2,R)); ((0,O),(1,Wr0));
                                                      ((1,Z),(0,R)); ((2,O),(3,Wr0));
                                                      ((3,O),(0,R)) ] ;
                                  tape_l := [];
                                  tape_h := Z;
                                  tape_r := [];
                                  time := 1 |> (DECODE (HD x))) `

val SUC_TM_def = Define``

val PROJ_TM_def = Define``

val COMPOSITION_TM_def = Define``

val PRIM_REC_TM_def = Define``

val MINIMISATION_TM_def = Define``

val zero_pr_tm_equiv = Q.store_thm("zero_pr_tm_equiv",
`zerof x = zero_tm x`,
fs[zero_tm_def] >> fs[RUN] >> fs[ENCODE_TM_TAPE_def])


*)

(*TO DO LATER*)

(*
val ENUMERABLE_FUN_def = Define `ENUMERABLE_FUN f = (realfn f) ∧ (∃ g. (recfn g 2) ∧
  (∀ n k. g(n,k) >= g(n,SUC(k))) ∧ (lim g k = f))`;

val COENUMERABLE_FUN_def = Define `COENUMERABLE_FUN f = (ENUMERABLE_FUN (-f))`;

val REAL_RECURSIVE_FUN_def = Define `REAL_RECURSIVE_FUN f = (realfun f) ∧ (∃ g. (recfn g 2) ∧
  (∀ x k. (abs (f(x) - g(x,k))) < (1 DIV k)))`;

val SPACE_COMPLEXITY_def = Define `SPACE_COMPLEXITY tm = ∀ l. LENGTH l `

val TIME_COMPLEXITY_def = Define `TIME_COMPLEXITY tm = `

(* Can go into P,NP,PSPACE,etc if time permits*)

val ENUMERATION_def = Define `ENUMERATION x S = if (x IN S)
                                                then (x POS LISTIZE S)
                                                else ?`;

val COMPLEXITY_1_def = Define `COMPLEXITY_1 x f =
  if (∃ p. f(p) = (ENUMERATION x S))
  then (MIN {LENGTH p | f(p) = (ENUMERATION x S)}  )
  else infinity`;

(* Invariance Theorem?*)

val ANG_BRA_def = Define `ANG_BRA x y = `;

val COND_COMPLEXITY_1_def = Define `COND_COMPLEXITY_1 x f y =
  if (∃ p. f(ANG_BRA y p) = (ENUMERATION x S))
  then (MIN {LENGTH p | f(ANG_BRA y p) = (ENUMERATION x S)}  )
  else infinity`;

val COND_COMPLEXITY_2_def = Define `COND_COMPLEXITY_2 x phi y =
  if (∃ p. phi(ANG_BRA y p) = x
  then (MIN {LENGTH p | phi(ANG_BRA y p) = x}  )
  else infinity`;

val COND_COMPLEXITY_3_def = Define `COND_COMPLEXITY_3 x y = COND_COMPLEXITY_2 x uniphi y`;

val COMPLEXITY_3_def = Define `COMPLEXITY_3 x = COND_COMPLEXITY_3 x empty_string`;

val COMPLEXITY_UPPER_BOUNDS = store_thm (
    "COMPLEXITY_UPPER_BOUNDS",
    `∃ c. ∀ x y. (COMPLEXITY_3 x <= (LENGTH x) + c) ∧ (COND_COMPLEXITY_3 x y <= (LENGTH x) + c)`,
    CHEAT)

val COMPLEXITY_EQUIV_def = Define `COMPLEXITY_EQUIV phi1 phi2 =
  ∀ x. ∃ c. (abs (phi1 x - phi2 x)) <= c`;
*)




(*
What is needed for Solomonoff Theorem
Recursive semi measure
K complexity
mu-expected value
M-probability
Def Semi-measure
Def Measure
Def Universal enumerable continuous semi-measure
Def Reference prefix machine
THM Exists a unique universal enumerable continuous semi-measure

*)


val _ = export_theory();






