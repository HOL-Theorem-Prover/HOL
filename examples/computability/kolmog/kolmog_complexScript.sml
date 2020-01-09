
open HolKernel Parse boolLib bossLib finite_mapTheory;
open recursivefnsTheory;
open prnlistTheory;
open primrecfnsTheory;
open listTheory;
open arithmeticTheory;
open numpairTheory;
open pred_setTheory;
open measureTheory;
open recfunsTheory;
open extNatTheory;
open prtermTheory;
open pred_setTheory;
open extrealTheory;
open realTheory;
open real_sigmaTheory;
open lebesgueTheory;
open transcTheory;
val _ = new_theory "kolmog_complex";
val _ =ParseExtras.tight_equality();

val _ = intLib.deprecate_int()

(*


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


(* union n=0^inf {0,1}^n *)

(*
I guess in this case out p could be a num?
In this case length = ceil log_2
and B = {0,1}
and Bstar = N (natural numbers)
and y concat x = y+ x*2^length y

OR

We could just use tapes on O and Z?
length = LENGTH
then B = {Z,O}
Bstar = union over B^n
and y concat x = y concat x
 *)

(* extended naturals, natural numbers union infinity *)


(* universal turing machine *)

(* We will use the defintion of the universal machine from Ming and Vitanyi  *)


val is_universal_tm_def = Define`is_universal_tm t <=>
                ∀i. ∀p q. (t i q <> NONE) ∧ (t i p <> NONE)==> ¬(prefix q p)∧¬(prefix p q)`







val complexity_def = Define`complexity n f x =
                       if  { p | f p = SOME (n x)} = {} then NONE
                       else SOME (MIN_SET {ℓ p | f p = SOME (n x)})`;


(** Definition 2.0.1 of Li and Vitanyi  **)
val additively_optimal_def = Define`
  additively_optimal n f C <=>
    f ∈ C ∧ ∀g. g∈C ==> ∃c. ∀x. complexity n f x <= complexity n g x + c`;


val blmunge_def = Define`
  (blmunge [] = [F;F]) ∧
  (blmunge (T::rest) = T::blmunge rest ) ∧
  (blmunge (F::rest) = F::T::blmunge rest )`


val wenc_def = Define`
  wenc n = bl2n (blmunge (n2bl n))`

val bldemunge_def = Define`
  (bldemunge m [] = (bl2n (REVERSE m),0n)) ∧
  (bldemunge m [F] = (bl2n (REVERSE m),0)) ∧
  (bldemunge m (T::t) = bldemunge (T::m) t) ∧
  (bldemunge m (F::T::t) = bldemunge (F::m) t )∧
  (bldemunge m (F::F::t) = (bl2n (REVERSE m),bl2n t ))`

val blpair_encode_def = Define`
blpair_encode x y = blmunge (n2bl x) ++ n2bl y`

val bld_lem = Q.prove(
`∀l A. bldemunge A (blmunge l ++ n2bl y) = (bl2n ( REVERSE A ++ l),y)`,
Induct >> simp[] >> Cases >> simp[bldemunge_def,blmunge_def] >>
REWRITE_TAC[GSYM APPEND_ASSOC,APPEND] )

val bldemunge_inv = Q.store_thm("bldemunge_inv",
`bldemunge [] (blpair_encode x y) = (x,y)`,
simp[blpair_encode_def,bld_lem] )

val UM_bff_def = Define`
  UM_bff n = let (x,y)= bldemunge [] (n2bl n) in Phi x y`

val pr_is_universal_def = Define`
  pr_is_universal f <=>
  recfn (rec1 f) 1 ∧
  ∃g. recfn g 1 ∧
      ∀y. ∃n. (g[y] = SOME n) ∧
              ∀x. f (bl2n (blpair_encode n x)) = Phi y x`;

val blist_of_def = Define`blist_of bl = nlist_of (MAP (λb. if b then 1 else 0) bl)`

val n2bl'_def = Define`n2bl' n = blist_of (n2bl n)`

val pr_n2bl'_def = Define`pr_n2bl' =
  WFM (λf n. if n=0 then 0
             else if EVEN n then ncons 1 (f ((n-2) DIV 2))
             else ncons 0 (f ((n-1) DIV 2)))`

val lem = Q.prove(`2*x DIV 2 = x`,metis_tac[MULT_DIV,MULT_COMM,DECIDE``0n < 2``])
val _ = augment_srw_ss[rewrites[lem]]

val lem' = Q.prove(`EVEN (n+1) ==> (n-1) DIV 2 <= n`, rw[EVEN_EXISTS] >> Cases_on `m` >>
  fs[ADD1,LEFT_ADD_DISTRIB] >> `n=2*n'+1` by simp[] >> rw[])

val lem'' = Q.prove(`~EVEN (n+1) ==> n DIV 2 <= n`, rw[GSYM ODD_EVEN,ODD_EXISTS] >>
  fs[ADD1,LEFT_ADD_DISTRIB])


val pr_n2bl'_corr = Q.store_thm("pr_n2bl'_corr",`pr_n2bl' [n] = n2bl' n`,
  simp[n2bl'_def,pr_n2bl'_def] >> completeInduct_on `n` >> simp[Once WFM_correct] >>
  simp[Once num_to_bool_list_def,SimpRHS] >> rw[blist_of_def]
    >- (fs[EVEN_EXISTS] >> Cases_on `m` >> fs[] >> rw[] >> fs[ADD1,LEFT_ADD_DISTRIB] )
    >- (fs[GSYM ODD_EVEN,ODD_EXISTS] >> rw[] >> fs[ADD1])  )

val pr_cn = List.nth (CONJUNCTS primrec_rules,3)

val primrec_pr_n2bl' = Q.store_thm("primrec_pr_n2bl'",`primrec pr_n2bl' 1`,
  simp[pr_n2bl'_def] >> irule primrec_WFM >> simp[restr_def] >> irule primrec_pr2 >>
  simp[lem',lem'']>>
  qexists_tac`pr_cond (Cn (pr1 (nB o EVEN o SUC)) [proj 0])
    (Cn (pr2 ncons) [K 1;Cn (pr2 nel) [Cn (pr_div) [Cn (pr2 $-) [proj 0;K 1];K 2];proj 1] ]  )
    (Cn (pr2 ncons) [K 0;Cn (pr2 nel) [Cn (pr_div) [proj 0;K 2];proj 1] ])` >>
  simp[pr_cond_def] >> reverse (rpt strip_tac)
    >- (simp[ADD1] >> Cases_on `(EVEN (m+1))` >>simp[]) >> irule pr_cn >> simp[primrec_rules] >>
  conj_tac >- (irule pr_cn >> simp[primrec_rules] >> irule primrec_pr1 >> simp[] >>
               qexists_tac `Cn pr_eq [Cn pr_mod [proj 0;K 2];K 1]` >>
               simp[EVEN,MOD_2, TypeBase.case_eq_of ``:bool``] >> simp[primrec_rules] )
           >- (irule pr_cn >> simp[primrec_rules])   )


val pr_bldemunge_def = Define`pr_bldemunge m = FST (bldemunge []  m) *, SND (bldemunge []  m)`

val bld_def = Define`(bld [] = (0n,0)) ∧
                     (bld [F] = (0,0)) ∧
                     (bld (T::t) = let (x,y) = bld t in (2*x+2,y)) ∧
                     (bld (F::T::t) = let (x,y) = bld t in (2*x+1,y)) ∧
                     (bld (F::F::t) = (0, bl2n t))`




val bldmunge_bld_eq = Q.store_thm("bldmunge_bld_eq",
`∀A. bldemunge A m = let (x,y) = bld m in (bl2n (REVERSE A) + x*2**(LENGTH A),y)`,
  completeInduct_on`LENGTH m` >> simp[bldemunge_def,bld_def] >> fs[PULL_FORALL] >> rw[] >>
  Cases_on`m` >> simp[bldemunge_def,bld_def] >> Cases_on `t`
    >- (Cases_on`h` >> simp[bldemunge_def,bld_def,bl2n_append] >> simp[bool_list_to_num_def] )
    >- (rename[`bldemunge _ (h1::h2::t)`] >> Cases_on `h1` >>
        simp[bldemunge_def,bld_def,bl2n_append]
        >- (Cases_on`bld (h2::t)` >> simp[EXP,RIGHT_ADD_DISTRIB,bool_list_to_num_def])
        >- (Cases_on`h2` >> simp[bld_def,bldemunge_def,bl2n_append] >> Cases_on `bld t` >>
            simp[EXP,bool_list_to_num_def]  ) ) )

val MAP_CONG' = REWRITE_RULE [GSYM AND_IMP_INTRO] MAP_CONG

val minimise_thm = Q.store_thm("minimise_thm",
`minimise f l = some n. (f (n::l) = SOME 0) ∧ (∀i. i<n ⇒ ∃m. 0<m ∧ (f (i::l) = SOME m))`,
simp[minimise_def] >> DEEP_INTRO_TAC optionTheory.some_intro >> rw[] >- (metis_tac[]) >>
SELECT_ELIM_TAC >> rw[] >> metis_tac[DECIDE``x:num <y ∨ (x=y) ∨ y<x ``,DECIDE``¬(x:num < x)``,optionTheory.SOME_11])


val bldn_def = tDefine"bldn"`
  bldn n = if n <= 1 then 0
      else if EVEN n then let xy = bldn ((n-2) DIV 2) in npair (2*nfst xy + 2) (nsnd xy)
      else let t = (n-1) DIV 2 in
             if EVEN t then let xy = bldn ((t-2) DIV 2) in npair (2*nfst xy + 1) (nsnd xy)
             else npair 0 ((t-1)DIV 2)`
(WF_REL_TAC`$<` >> reverse (rw[]) >-
(irule LESS_EQ_LESS_TRANS >> qexists_tac`n DIV 2` >> rw[DIV_LE_MONOTONE,DIV_LESS]) >>
intLib.ARITH_TAC )

val bldn_equiv_thm = Q.store_thm("bldn_equiv_thm",
`∀l. UNCURRY npair (bld l) = bldn (bl2n l)`,
ho_match_mp_tac (theorem"bld_ind") >> simp[bld_def,bool_list_to_num_def] >>rw[]
  >- (EVAL_TAC)
  >- (EVAL_TAC)
  >- (Cases_on `bld l` >> fs[] >> simp[Once bldn_def,EVEN_ADD,EVEN_MULT] >>
      metis_tac[nfst_npair,nsnd_npair] )
  >- (Cases_on `bld l` >> fs[] >> simp[Once bldn_def,EVEN_ADD,EVEN_MULT] >>
      metis_tac[nfst_npair,nsnd_npair])
  >- (simp[Once bldn_def,EVEN_ADD,EVEN_MULT])  )



val primrec_if_thm = Q.store_thm("primrec_if_thm",
`(primrec (pr2 (λm n. nB  (p m n))) 2 ∧ primrec (pr2 t) 2 ∧ primrec (pr2 e) 2) ==>
  primrec (pr2 (λm n. if p m n then t m n else e m n)) 2`,
rw[] >> irule primrec_pr2 >> qexists_tac`pr_cond (pr2 (λm n. nB (p m n))) (pr2 t) (pr2 e)` >> simp[] >> simp[pr_cond_def] >> rw[] )

val primrec_npair_thm = Q.store_thm("primrec_npair_thm",
`(primrec (pr2 t) 2 ∧ primrec (pr2 e) 2) ==>
  primrec (pr2 (λm n. npair (t m n)  (e m n))) 2`,
rw[] >> irule primrec_pr2 >> qexists_tac`Cn (pr2 npair) [(pr2 t); (pr2 e)]` >> simp[primrec_rules] )

val primrec_mult_thm = Q.store_thm("primrec_mult_thm",
`(primrec (pr2 t) 2 ∧ primrec (pr2 e) 2) ==>
  primrec (pr2 (λm n. $* (t m n)  (e m n))) 2`,
rw[] >> irule primrec_pr2 >> qexists_tac`Cn (pr2 $* ) [(pr2 t); (pr2 e)]` >> simp[primrec_rules] )

val primrec_add_thm = Q.store_thm("primrec_add_thm",
`(primrec (pr2 t) 2 ∧ primrec (pr2 e) 2) ==>
  primrec (pr2 (λm n. $+ (t m n)  (e m n))) 2`,
rw[] >> irule primrec_pr2 >> qexists_tac`Cn (pr2 $+) [(pr2 t); (pr2 e)]` >> simp[primrec_rules] )

val primrec_sub_thm = Q.store_thm("primrec_sub_thm",
`(primrec (pr2 t) 2 ∧ primrec (pr2 e) 2) ==>
  primrec (pr2 (λm n. $- (t m n)  (e m n))) 2`,
rw[] >> irule primrec_pr2 >> qexists_tac`Cn (pr2 $-) [(pr2 t); (pr2 e)]` >> simp[primrec_rules] )

val primrec_div_thm = Q.store_thm("primrec_div_thm",
`(primrec (pr2 t) 2 ∧ 0<e) ==>
  primrec (pr2 (λm n. $DIV (t m n) e)) 2`,
rw[] >> irule primrec_pr2 >> qexists_tac`Cn pr_div [(pr2 t); K e]` >> simp[primrec_rules] )

val primrec_mod_thm = Q.store_thm("primrec_mod_thm",
`(primrec (pr2 t) 2 ∧ 0<e) ==>
  primrec (pr2 (λm n. $MOD (t m n) e)) 2`,
rw[] >> irule primrec_pr2 >> qexists_tac`Cn pr_mod [(pr2 t); K e]` >> simp[primrec_rules] )

val primrec_nfst_thm = Q.store_thm("primrec_nfst_thm",
`(primrec (pr2 t) 2) ==>
  primrec (pr2 (λm n. nfst (t m n) )) 2`,
rw[] >> irule primrec_pr2 >> qexists_tac`Cn (pr1 nfst) [(pr2 t)]` >> simp[primrec_rules] )

val primrec_nsnd_thm = Q.store_thm("primrec_nsnd_thm",
`(primrec (pr2 t) 2) ==>
  primrec (pr2 (λm n. nsnd (t m n) )) 2`,
rw[] >> irule primrec_pr2 >> qexists_tac`Cn (pr1 nsnd) [(pr2 t)]` >> simp[primrec_rules] )

val primrec_nel_thm = Q.store_thm("primrec_nel_thm",
`(primrec (pr2 t) 2 ∧ primrec (pr2 e) 2) ==>
  primrec (pr2 (λm n. nel (t m n)  (e m n))) 2`,
rw[] >> irule primrec_pr2 >> qexists_tac`Cn (pr2 nel) [(pr2 t); (pr2 e)]` >> simp[primrec_rules] )

val primrec_cn = List.nth(CONJUNCTS primrec_rules,3)

val primrec_const = Q.store_thm("primrec_const",
`primrec (pr2 (λn r. k)) 2`,
irule primrec_pr2 >> simp[primrec_rules] >> qexists_tac`K k` >> rw[])

val primrec_pr2_fst = Q.store_thm("primrec_pr2_fst",
`primrec (pr2 (λx y . x)) 2`,
irule primrec_pr2 >> simp[primrec_rules] >> qexists_tac`proj 0` >> rw[primrec_rules] )

val primrec_pr2_snd = Q.store_thm("primrec_pr2_snd",
`primrec (pr2 (λx y . y)) 2`,
irule primrec_pr2 >> simp[primrec_rules] >> qexists_tac`proj 1` >> rw[primrec_rules] )

val awetac = rpt(FIRST (map ho_match_mp_tac [primrec_if_thm,primrec_npair_thm,primrec_mult_thm,primrec_add_thm,primrec_sub_thm,primrec_div_thm,primrec_mod_thm,primrec_nfst_thm,primrec_nsnd_thm,primrec_nel_thm]) >> rw[primrec_const,primrec_pr2_fst,primrec_pr2_snd])

val bldn_primrec = Q.store_thm("bldn_primrec",
`∃g. primrec g 1 ∧ ∀n. g [n] =  bldn n`,
qexists_tac`WFM (λf n. if n <= 1 then 0
      else if EVEN n then let xy = f ((n-2) DIV 2) in npair (2*nfst xy + 2) (nsnd xy)
      else let t = (n-1) DIV 2 in
             if EVEN t then let xy = f ((t-2) DIV 2) in npair (2*nfst xy + 1) (nsnd xy)
             else npair 0 ((t-1)DIV 2) )` >>
rw[] >- (irule primrec_WFM >> simp[intLib.ARITH_PROVE``(EVEN (m+1) ==> (m − 1) DIV 2 ≤ m) ∧ (¬EVEN (m+1) ∧ EVEN (m DIV 2) ==> (m DIV 2 − 2) DIV 2 ≤ m) ∧ (m+1<= 1 <=> (m=0))``,restr_def] >>
         ho_match_mp_tac primrec_if_thm >> rw[]
         >- (irule primrec_pr2 >> qexists_tac`Cn pr_eq [proj 0;zerof]` >> simp[primrec_rules])
         >- (irule primrec_pr2 >> qexists_tac`zerof` >> simp[primrec_rules])
         >- (ho_match_mp_tac primrec_if_thm >>rw[]
             >- (irule primrec_pr2 >> qexists_tac`Cn pr_eq [Cn pr_mod [Cn succ [proj 0];K 2];zerof]` >>
                 simp[] >> conj_tac >- (rpt (irule primrec_cn >> simp[primrec_rules])) >> intLib.ARITH_TAC )
             >- (awetac)
             >- (ho_match_mp_tac primrec_if_thm >>rw[] >> awetac >> irule primrec_pr2 >>
                 qexists_tac`Cn pr_eq [Cn pr_mod [Cn pr_div [proj 0;K 2];K 2];zerof]` >> simp[] >> conj_tac
                 >- (irule primrec_cn >> simp[primrec_rules]) >> intLib.ARITH_TAC ) ) )
     >- (completeInduct_on `n` >> simp[Once WFM_correct] >>
         simp[Once num_to_bool_list_def,SimpLHS] >> simp[Once bldn_def,SimpRHS] >>
         `( ¬(n ≤ 1) ==> (n − 2) DIV 2 < n)` by simp[intLib.ARITH_PROVE``( ¬(n ≤ 1) ==> (n − 2) DIV 2 < n)``]>>
         `( ¬(n ≤ 1) ==> (((n − 1) DIV 2 − 2) DIV 2 < n))` by
         simp[intLib.ARITH_PROVE``( ¬(n ≤ 1) ==> (((n − 1) DIV 2 − 2) DIV 2 < n))``]  >> rw[]  ) )

val bldn_rec = Q.store_thm("bldn_rec",
`recfn (SOME o (pr1 bldn)) 1`,
`primrec (pr1 bldn) 1` by simp[primrec_pr1,bldn_primrec]>> simp[primrec_recfn])


val universal_Phi = Q.store_thm("universal_Phi",
  `pr_is_universal (λn. let bl = n2bl n; (x,y) = bldemunge [] bl in Phi x y)`,
  simp[pr_is_universal_def] >> reverse conj_tac
    >- (simp[bldemunge_inv] >> qexists_tac `SOME o proj 0` >>
        simp[recfn_rules,bldmunge_bld_eq,bool_list_to_num_def]) >>
    REWRITE_TAC[GSYM recPhi_correct] >> irule recfn_rec1 >>
    simp[bldmunge_bld_eq,bool_list_to_num_def] >>
    `(λ(x:num,y:num). (x,y))= λx.x` by simp[FUN_EQ_THM,pairTheory.FORALL_PROD] >> simp[] >>
    qexists_tac`recCn recPhi [recCn (SOME o (pr1 nfst)) [SOME o (pr1 bldn)];recCn (SOME o (pr1 nsnd)) [SOME o (pr1 bldn)]]` >> simp[] >> rw[]
    >- (irule recfnCn >> rw[bldn_rec] >- (irule recfnCn >> rw[bldn_rec] >> simp[primrec_recfn,primrec_nfst])
        >- (irule recfnCn >> rw[bldn_rec] >> simp[primrec_recfn,primrec_nsnd]) >>
        metis_tac[(GSYM recPhi_rec2Phi),recfn_recPhi])  >>
    simp[recCn_def] >> `n = bl2n (n2bl n)` by simp[bool_num_inv] >>
    pop_assum SUBST1_TAC >> simp[GSYM bldn_equiv_thm] >> simp[pairTheory.UNCURRY]
       )

val universal_tm_def = Define`universal_tm = (λbl. let (x,y) = bldemunge [] bl in Phi x y)`

*)

val _ = export_theory();
