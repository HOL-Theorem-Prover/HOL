
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
val _ = new_theory "kolmog_complex";
val _ =ParseExtras.tight_equality();

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
val prefix_def = Define`prefix a b <=> a≼b ∧ a <> b`

val is_universal_tm_def = Define`is_universal_tm t <=>
		∀i. ∀p q. (t i q <> NONE) ∧ (t i p <> NONE)==> ¬(prefix q p)∧¬(prefix p q)`

val num_to_bool_list_def = tDefine"num_to_bool_list"`num_to_bool_list n =
		   if n=0 then []
		   else if EVEN n then T::num_to_bool_list((n-2) DIV 2)
		   else F::num_to_bool_list((n-1) DIV 2)`
(WF_REL_TAC`$<` >> rw[]>>
irule LESS_EQ_LESS_TRANS >> qexists_tac`n DIV 2` >> rw[DIV_LE_MONOTONE,DIV_LESS])

val bool_list_to_num_def = Define`
  (bool_list_to_num [] = 0n) ∧
  (bool_list_to_num (h::t) = (if h then 2 else 1)+2 * (bool_list_to_num t))`

val num_bool_inv = Q.store_thm("num_bool_inv[simp]",
  `num_to_bool_list (bool_list_to_num l) = l`,
  Induct_on `l` >> simp[Once num_to_bool_list_def,bool_list_to_num_def] >> Cases_on `h` >>
  simp[EVEN_ADD,EVEN_MULT] >> metis_tac[MULT_DIV,MULT_COMM,DECIDE ``0n<2``] )

val bool_num_inv = Q.store_thm("bool_num_inv[simp]",
`∀n. bool_list_to_num (num_to_bool_list n) = n`,
ho_match_mp_tac (theorem"num_to_bool_list_ind") >> rpt strip_tac >>
  rw[Once num_to_bool_list_def,bool_list_to_num_def]
  >- (MP_TAC(Q.INST[`n`|->`2`,`q`|->`1`,`m`|->`n`]DIV_SUB)>>fs[]>>impl_keep_tac
      >-(fs[EVEN_EXISTS])>>simp[LEFT_SUB_DISTRIB]>>Q.SPEC_THEN`2`MP_TAC DIVISION>>fs[]>>
      disch_then(Q.SPEC_THEN`n`(MP_TAC o SYM) ) >> fs[EVEN_MOD2] )
  >- (fs[GSYM ODD_EVEN,ODD_EXISTS] >>metis_tac[MULT_DIV,MULT_COMM,DECIDE ``0n<2``,ADD1] ) )


val rec1_def = Define`
  (rec1 f [] = f 0n : num option) ∧
  (rec1 f (x::t) = f x)
`;

val _ = overload_on ("ℓ",``λp. LENGTH (num_to_bool_list p) ``)

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

val _ = overload_on ("bl2n",``bool_list_to_num``)
val _ = overload_on ("n2bl",``num_to_bool_list``)

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


val bl2n_append = Q.store_thm("bl2n_append",
`∀xs ys. bl2n(xs++ys) = bl2n xs + bl2n ys *2**LENGTH xs`,
Induct_on `xs` >> simp[bool_list_to_num_def] >> simp[LEFT_ADD_DISTRIB,EXP])

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

val recfn_nil = Q.store_thm("recfn_nil",
`∀f n. recfn f n ⇒ ∀xs. LENGTH xs <= n ==> (f (xs ++ GENLIST (K 0) (n - LENGTH xs)) = f xs)`,
Induct_on `recfn` >> simp[] >> rpt strip_tac 
  >- (Cases_on `xs` >> simp[succ_def]) 
  >- (qid_spec_tac`xs` >> Induct_on `n` >> simp[proj_def] >> rw[] >> rw[] >> simp[EL_APPEND_EQN])
  >- (simp[recCn_def] >> fs[EVERY_MEM] >> COND_CASES_TAC >> fs[MEM_MAP] 
    >- (COND_CASES_TAC >-(simp[Cong MAP_CONG']) >> fs[] >> metis_tac[] ) 
    >- (metis_tac[]) )
  >- (Cases_on `xs` >> simp_tac (srw_ss ())[]
    >- (ONCE_REWRITE_TAC[recPr_def] >> Cases_on `n` >> simp[GENLIST_CONS] >> 
        last_x_assum (qspec_then `[]` mp_tac)>>simp[] ) 
    >- (fs[] >> Induct_on`h` >> simp[] 
      >- (ONCE_REWRITE_TAC[recPr_def] >> 
          last_x_assum (qspec_then `t` mp_tac)>> simp[ADD1]) >> 
        ONCE_REWRITE_TAC[recPr_def] >> simp[] >> Cases_on`recPr f f' (h::t)`>>simp[] >>
        first_x_assum(qspec_then `h::x::t`mp_tac) >> simp[ADD1] )  )
  >- (simp[minimise_thm] >> first_x_assum(qspec_then`j::xs` (mp_tac o Q.GEN`j`) )>> simp[ADD1] ))  

val recfn_not_zero = Q.store_thm("recfn_not_zero",
`∀f n. recfn f n ==> 0<n`,
Induct_on `recfn` >> rw[] >> Cases_on `gs` >> fs[])

val recfn_excess = Q.store_thm("recfn_excess",
`∀f n. recfn f n ⇒ ∀l. n <= LENGTH l ⇒ (f (TAKE n l) = f l)`,
Induct_on`recfn` >> simp[] >> rpt strip_tac
  >- (Cases_on `l` >> fs[succ_def])
  >- (simp[proj_def,EL_TAKE])
  >- (simp[recCn_def] >> fs[EVERY_MEM] >> COND_CASES_TAC >> fs[MEM_MAP]
    >- (COND_CASES_TAC >-(simp[Cong MAP_CONG']) >> fs[] >> metis_tac[])
    >- (metis_tac[]))
  >- (`2<=n` by (rpt (dxrule recfn_not_zero) >>simp[]) >> Cases_on `l` >> simp[] >> Induct_on `h` 
    >- (ONCE_REWRITE_TAC[recPr_def] >> simp[] )
    >- (ONCE_REWRITE_TAC[recPr_def] >> simp[] >> strip_tac >> 
        Cases_on `recPr f f' (h::t)` >> simp[] >> rename[`g (h::x::_) = g (h::x::t)`] >> 
        first_x_assum(qspec_then `h::x::t` mp_tac) >> simp[] )  )
  >- (simp[minimise_thm] >> first_x_assum(qspec_then`j::l` (mp_tac o Q.GEN`j`) ) >> simp[] ))

val unary_recfn_eq = Q.store_thm("unary_recfn_eq",
`recfn f 1 ∧ (∀n. f [n] = g n) ⇒ (f = rec1 g)`,
rw[FUN_EQ_THM] >> Cases_on`x` >> simp[rec1_def] 
  >- (drule_then (qspec_then `[]` mp_tac) recfn_nil >> simp[])
  >- (drule_then (qspec_then `h::t` mp_tac) recfn_excess >> simp[] )  )

val recfn_rec1 = Q.store_thm("recfn_rec1",
` (∃g. recfn g 1 ∧ ∀n. g [n] = f n) ⇒ recfn (rec1 f) 1`,
metis_tac[unary_recfn_eq])

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
rw[] >> irule primrec_pr2 >> qexists_tac`Cn (pr2 $*) [(pr2 t); (pr2 e)]` >> simp[primrec_rules] )

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

(*
(** Lemma 2.1.1 **)
(**  Use univerality of phi **)
val additively_exists = Q.store_thm("additively_exists",
`∃f. additively_optimal bool_list_to_num f {g | pr_is_universal g}`,
qexists_tac`UM_bff` >> simp[additively_optimal_def,universal_Phi] >>
rw[complexity_def] >> qexists_tac`c` >> rw[] 
>- (fs[EXTENSION] >> rename[`g n = SOME (bool_list_to_num bl)`] >> fs[pr_is_universal_def] >>
    rename[`recfn (rec1 ug) 1`,`g [_] = SOME _`] >>  
    ` ∃ui. ∀n. rec1 ug [n] = Phi ui (nlist_of [n])` by metis_tac[recfns_in_Phi] >> 
    fs[rec1_def] >> metis_tac[nfst_npair,nsnd_npair])
>- ()   )

val conditional_complexity_def  = Define`conditional_complexity phi x y =
		   if {} `

val semimeasure_def = Define`
semimeasure mu =  (mu [] <= 1:real) ∧ (∀x:bool list. (mu x >= 0) ∧
                                      (mu x >= mu (x++[F]) + mu (x++[T]) )) `

val universal_semimeasure_def = Define`
universal_semimeasure M setM =
(M IN setM) ∧
(∀mu. (mu IN setM) ==> ∃ c. c>0 ∧ ∀x:bool list. (c * (mu x) <= M x))`



(*
kolmog_complexity is the Kolmogorov complexity of a
binary string, and is a function from binary strings to naturals union infinity
*)


 *)

val _ = set_mapped_fixity{fixity = Infix(NONASSOC,450),term_name = "prefix",tok="≺"}

val prefix_refl = Q.store_thm("prefix_refl[simp]",
`¬(l ≺ l)`,
simp[prefix_def])

val prefix_free_def = Define`prefix_free (s:α list set) = ∀a b. a ∈ s ∧ b∈s ==> ¬(a≺ b)∧¬(b≺ a) `

val prefix_free_empty = Q.store_thm("prefix_free_empty[simp]",
`prefix_free ∅`,
rw[prefix_free_def])

val prefix_free_sing = Q.store_thm("prefix_free_sing[simp]",
`prefix_free {l}`,
rw[prefix_free_def])

val len_fun_def = Define`len_fun (A:bool list set) n = let strs = {s | (LENGTH s = n) ∧ s ∈ A} in EXTREAL_SUM_IMAGE (λs. Normal (2 rpow (- &(LENGTH s)))) strs`

val extreal_sum_image_finite_corr = Q.store_thm("extreal_sum_image_finite_corr",
`∀P. FINITE P ⇒ ∀f x. (∀y. (y ∈ P) ==> (f y = x)) ⇒ (SIGMA f P = &CARD P * x)`,
   REPEAT STRIP_TAC
   >> (MP_TAC o Q.SPECL [`P`]) extrealTheory.EXTREAL_SUM_IMAGE_FINITE_SAME
   >> RW_TAC std_ss []
   >> POP_ASSUM (MP_TAC o (Q.SPECL [`f`]))
   >> RW_TAC std_ss []
   >> (MP_TAC o Q.SPECL [`P`]) SET_CASES
   >> RW_TAC std_ss [] >-  rw[extrealTheory.EXTREAL_SUM_IMAGE_THM, CARD_EMPTY, extrealTheory.mul_lzero]
   >> POP_ASSUM (K ALL_TAC)
   >> POP_ASSUM MATCH_MP_TAC
   >> Q.EXISTS_TAC `x'` >> RW_TAC std_ss [IN_INSERT])


val bl2n_11 = Q.store_thm("bl2n_11[simp]",
`bl2n x = bl2n y <=> x = y`,
metis_tac[num_bool_inv])

val finite_bool_list_n = Q.store_thm("finite_bool_list_n[simp]",
`FINITE {s|LENGTH (s:bool list) = n}`,
irule (INST_TYPE[beta|->``:num``] FINITE_INJ) >> qexists_tac`bool_list_to_num` >>
          qexists_tac`count (2**(n+1)-1)` >> simp[INJ_DEF] >> qid_spec_tac`n` >> Induct_on`x`>>
          simp[bool_list_to_num_def] >> pop_assum(qspec_then`LENGTH x` MP_TAC) >>rw[] >> 
          simp[GSYM ADD1,Once EXP] >> irule (DECIDE``n<=2n ∧ b<x-1 ==> 2*b+n<2*x-1``) >> rw[ADD1])

val bool_list_card = Q.store_thm("bool_list_card[simp]",
`CARD {s | LENGTH (s:bool list) = n} = 2**n`,
Induct_on`n`>>simp[LENGTH_CONS] >> qmatch_abbrev_tac`CARD s = 2**(SUC n)`>> 
`s = IMAGE (CONS T) {s | LENGTH s = n} UNION IMAGE (CONS F) {s | LENGTH s = n}` by 
  (simp[Abbr`s`,EXTENSION,EQ_IMP_THM] >> rw[] ) >> simp[CARD_UNION_EQN,CARD_INJ_IMAGE,EXP] >> 
qmatch_abbrev_tac`(x:num)-y=x` >> `y=0`suffices_by simp[] >> simp[Abbr`y`,EXTENSION] >>Cases>>simp[]>>
metis_tac[]  )

val len_fun_eq1 = Q.store_thm("len_fun_eq1",
`SIGMA (λs. Normal (2 rpow -&LENGTH s)) {s | (LENGTH (s:bool list) = n)} = 1`,
irule EQ_TRANS >>qexists_tac`&CARD {s | LENGTH (s:bool list) = n} * Normal(2 rpow (-&n))` >> conj_tac
  >- (irule extreal_sum_image_finite_corr >> rw[])
  >- (simp[extreal_of_num_def,extreal_mul_def,GSYM realTheory.REAL_OF_NUM_POW,transcTheory.GEN_RPOW,
	   GSYM transcTheory.RPOW_ADD,transcTheory.RPOW_0 ] ))

val len_fun_le1 = Q.store_thm("len_fun_le1",
`len_fun A n <= 1`,
rw[len_fun_def] >> `{s | LENGTH s = n ∧ s ∈ A}⊆{s|LENGTH s = n}` by simp[SUBSET_DEF] >> 
`FINITE {s | LENGTH s = n ∧ s ∈ A}` by metis_tac[SUBSET_FINITE_I,finite_bool_list_n] >> 
ASSUME_TAC len_fun_eq1 >> pop_assum(SUBST1_TAC o SYM)>> irule EXTREAL_SUM_IMAGE_MONO_SET >> 
simp[finite_bool_list_n] >> rw[extreal_of_num_def,extreal_le_def] >> 
`0r < 2 `suffices_by(strip_tac >> drule transcTheory.RPOW_POS_LT >> simp[realTheory.REAL_LE_LT]) >>
simp[] )

(* Traditional bool list to num *)
val tbl2n_def = Define`tbl2n [] = 0n ∧ tbl2n (T::t) = 2*tbl2n t + 1 ∧ tbl2n (F::t) = 2*tbl2n t`

val interval_bl_def = Define`interval_bl l = (&(tbl2n l) *(2 rpow -&LENGTH l),(2 rpow -&LENGTH l))`

val disjoint_interval_def = Define`disjoint_interval ((m:real),i) (n,j) <=> 
                                   DISJOINT {r|m<=r ∧ r<m+i} {r|n<=r ∧ r<n+j}`

val disjoint_pf_lem1 = Q.store_thm("disjoint_pf_lem1",
`¬(i ≺ j) ∧ (LENGTH i < LENGTH j) ==> &tbl2n j * 2 rpow -&LENGTH j + 2 rpow -&LENGTH j < &tbl2n i * 2 rpow -&LENGTH i`,
rw[] >>  )

val disjoint_prefix_free = Q.store_thm("disjoint_prefix_free",
`prefix_free P <=> let is = IMAGE interval_bl P in ∀i1 i2. i1 ∈ is ∧ i2∈is ∧ i1<>i2 ==> disjoint_interval i1 i2`,
rw[EQ_IMP_THM] 
>- (rename[`interval_bl i = interval_bl j`] >> 
    `¬(i ≺ j) ∧ ¬(j ≺ i)∧ i<>j` by metis_tac[prefix_free_def] >> 
    fs[interval_bl_def,disjoint_interval_def,DISJOINT_DEF,EXTENSION] >> 
    rw[GSYM DISJ_ASSOC] >> rw[DECIDE``¬p∨q ⇔ p⇒q``] >> strip_tac >> 
    `LENGTH i <> LENGTH j` by (strip_tac >> fs[] >> qabbrev_tac`M = 2 rpow -&LENGTH j` >> 
      `&tbl2n i * M < &tbl2n j * M + M` by metis_tac[REAL_LET_TRANS] >>
      `&tbl2n j * M < &tbl2n i * M + M` by metis_tac[REAL_LET_TRANS] >>
      `&tbl2n i * M + M = (&tbl2n i + 1) * M` by metis_tac[REAL_ADD_RDISTRIB,REAL_MUL_LID] >>  
      `&tbl2n j * M + M = (&tbl2n j + 1) * M` by metis_tac[REAL_ADD_RDISTRIB,REAL_MUL_LID] >> fs[] >>
      `(0:real)<2` by fs[] >> `0<M` by metis_tac[transcTheory.RPOW_POS_LT]
      `((&tbl2n i) :real) < &(tbl2n j + 1)` by fs[REAL_LT_RMUL] >> 
      `((&tbl2n j):real) < &(tbl2n i + 1)` by fs[REAL_LT_RMUL] >> fs[] ) >> 
    Cases_on`LENGTH i < LENGTH j` >> rw[]
      (* We want to show that either i2^-li+2^-li < j2^-lj or j2^-lj+2^-lj<i2^-li *)
      >- (`&tbl2n j * 2 rpow -&LENGTH j + 2 rpow -&LENGTH j < &tbl2n i * 2 rpow -&LENGTH i` by 
          (simp[disjoint_pf_lem1]) >> 
          fs[] )
      >- () ) )

val kraft_ineq = Q.store_thm("kraft_ineq",
`∀P. prefix_free P <=> SIGMA (λs. Normal (2 rpow -&LENGTH s)) {s | s ∈ P} <= 1`,
Let L(x) = [x*2**-LENGTH(x) , x*2**-LENGTH(x)+2**-LENGTH(x)] >> L(x) are disjoint cus prefix free >> length of L(x) is 2**-LENGTH(x) >> L(x) subste of [0,1] for all x >> sum <= length [0,1] =1 )
 


(* Have done initial Kolmog stuff *)

val prefix_machine_def = Define`prefix_machine (U:bool list -> extnat) = 
                                ∃P. prefix_free P∧(∀x. x ∈ P <=> ∃y. U x = SOME y)`

val monotone_machine_def = Define`monotone_machine (U:bool list -> extnat) = 
                     ∀p1 p2. ∃x1 x2. (U p1 = (SOME x1)) ∧ (U p2 = (SOME x2)) ==> (p1 ≼ p2 ==> (n2bl x1 ≼ n2bl x2 ∨ n2bl x2 ≼ n2bl x1) )`

val kolmog_complexity_def = Define`kolmog_complexity x U =
                       if  { p | U p = SOME x} = {} then NONE
                       else SOME (MIN_SET {LENGTH p | U p = SOME x})`;

val prefix_kolmog_complexity_def = Define`pkolmog_complexity x U = 
                                if prefix_machine U then kolmog_complexity x U else NONE`

(* Mono def not working right now  *)
val monotone_kolmog_complexity_def = Define`mkolmog_complexity x U = 
                                if monotone_machine U then 
                                  if ∀y. { p | (U p = SOME y) ∧ (x ≼ (n2bl y)) } = {} then NONE
                                   else SOME (MIN_SET {LENGTH p |∃y. (U p = SOME y) ∧(x ≼ n2bl y)}) 
                                else NONE`

val kolmog_def = Define`kolmog x = kolmog_complexity x universal_tm`





val Tpow_def = Define`Tpow n = GENLIST (K T) n`

val Fpow_def = Define`Fpow n = GENLIST (K F) n`

val bar_def = Define`bar x = (Tpow (LENGTH x)) ++ [F] ++ x`

val bl_len_def = Define`bl_len bl = n2bl (LENGTH bl)`

val dash_def = Define`dash x = (Tpow (LENGTH (bl_len x))) ++ [F] ++ (bl_len x) ++ x`

val pair_def = Define`pair x y = (dash x) ++ y`

val cond_kolmog_complexity_def = Define`cond_kolmog_complexity x y U = 
                       if  { p | U (pair y p) = SOME x} = {} then NONE
                       else SOME (MIN_SET {LENGTH p | U (pair y p) = SOME x})`

val cond_kolmog_def = Define`cond_kolmog x y = cond_kolmog_complexity x y universal_tm`


(** up to here **)
(* In Process of proving   *)

(** Kolmog Theorems **)

(* 
val K_upper_bound = Q.store_thm("K_upper_bound",
`∃c. kolmog x <= LENGTH x + 2*log_2 LENGTH x  + c`,
)



val K_nat_upper_bound = Q.store_thm("K_nat_upper_bound",
`∀x. let n = number(x) with kolmog x <= log_2 n + 2*log_2 (log (n)) + O(1)`,
)


val K_sum_ineq = Q.store_thm("K_sum_ineq",
`sum x 2**-kolmog x <= 1`,
)

val K_lower_bound = Q.store_thm("K_lower_bound",
`For x in {1,..,N} we have ~(kolmog x >= LENGTH x) for o(N) x's`,
)

val K_code_sep = Q.store_thm("K_code_sep",
`cond_kolmog x y <= kolmog x + O(1)`,
)


val K_code_sep_2 = Q.store_thm("K_code_sep_2",
`kolmog x <= kolmog (pair x y) +O(1)`,
)


val K_concat = Q.store_thm("K_concat",
`kolmog (x++y) <= kolmog (pair x y) + O(1)`,
)


val K_concat_2 = Q.store_thm("K_concat_2",
`kolmog (pair x y) <= kolmog x + cond_kolmog x y + O(1)`,
)

val K_concat_3 = Q.store_thm("K_concat_3",
`kolmog x + cond_kolmog x y <= kolmog x + kolmog y + O(1)`,
)


val K_sym = Q.store_thm("K_sym",
`cond_kolmog x (pair y (kolmog y)) + kolmog y =+= kolmog (pair x y)`,
)

val K_sym_2 = Q.store_thm("K_sym_2",
`kolmog (pair x y) =+= kolmog (pair y x)`,
)

val K_sym_3 = Q.store_thm("K_sym_3",
`kolmog (pair y x) =+= cond_kolmog y (pair x (kolmog x)) + kolmog x`,
)


val K_recfun = Q.store_thm("K_recfun",
`recfn f ==> K(f(x)) <= K(x) + K(code(f)) + O(1)`,
)

val K_incomp = Q.store_thm("K_incomp",
`~∃p. ∀x. universal_tm p x = kolmog x`,
)

val K_coenum = Q.store_thm("K_coenum",
`∃p. let phi = universal_tm p in
 limit as t-> infinity phi x,t = kolmog x ∧ phi x,t<=phi x,t+1`,
)


*)

(** End of Kolmog section **)


(*

val leastR_def = Define`leastR R A = @a. a IN A ∧ ∀b. b IN A ==> ~R b a`

val order_def = tDefine"order"`(order A R 0 = leastR R A) ∧
                (order A R (SUC n) = leastR R (A DIFF IMAGE (λi. order A R i) (count (SUC n))))`(WF_REL_TAC`measure (SND o SND)` >> simp[])

val tmorder_def = Define`tmorder x = order {p | universal_tm p = x} `

val listlex_def = Define`(listlex [] x <=> x<>[])∧(listlex (h::t) [] <=> F)∧
                         (listlex (h1::t1) (h2::t2) <=>
			 (LENGTH t1 < LENGTH t2) ∨ ((LENGTH t1 = LENGTH t2) ∧ ((h1=h2) ∧ listlex t1 t2 ∨ ~h1 ∧ h2 )  ) )`

val listlex_length = Q.store_thm("listlex_length",
`!a b. LENGTH a < LENGTH b ==> listlex a b`,
Cases_on `a` >> simp[listlex_def] >> Cases_on `b` >> simp[listlex_def])

val listlex_length2 = Q.store_thm("listlex_length2",
`!a b. listlex a b ==> (LENGTH a <= LENGTH b)`,
Induct_on `a` >> simp[listlex_def] >> Cases_on `b` >> simp[listlex_def] >> rpt strip_tac >>
simp[])

val listlex_empty = Q.store_thm("listlex_empty[simp]",
`listlex a [] <=> F`,
Cases_on `a` >> simp[listlex_def])

val listlex_same_length = Q.store_thm("listlex_same_length",
`!B l w. (!b. B b ==> (LENGTH b = l)) ∧ B w ==> ?v. B v ∧ (!b. listlex b v ==> ~B b)`,
Induct_on `l` >> simp[] >- (rw[] >> qexists_tac`[]` >> simp[] >> metis_tac[]) >>
rw[] >> Cases_on`?hf. B' hf ∧ (HD hf = F)`
>- (fs[] >>
    `?c. B' c ∧ (HD c= F) ∧ (!d. listlex d c ==> ~B' d)`
      by (first_x_assum(qspec_then`{t|B' (F::t)}`MP_TAC) >> simp[] >>
          disch_then(qspec_then`TL hf`MP_TAC) >> Cases_on `hf` >> simp[]
          >- (res_tac >> fs[]) >> fs[] >> impl_tac
	      >- (rw[] >> res_tac>> fs[]) >>
	      rw[] >> qexists_tac`F::v` >> simp[]>> rpt strip_tac >> Cases_on`d` >> fs[]
              >- (res_tac >> fs[])
              >- (fs[listlex_def] >- (res_tac >> fs[]) >> rw[] >> metis_tac[] ))>> metis_tac[])
>- (fs[] >>first_x_assum(qspec_then`{t|B' (T::t)}`MP_TAC) >> simp[] >> Cases_on `w`
    >- (res_tac >> fs[]) >> `h = T` by metis_tac[HD] >> rw[] >>
        pop_assum(qspec_then`t`MP_TAC) >> impl_tac
	>- (rw[] >> res_tac >> fs[]) >> rw[] >> qexists_tac`T::v` >> fs[] >> Cases_on `b`
	    >- (rpt strip_tac >> res_tac >> fs[]) >> rw[listlex_def] >> strip_tac
	        >- (res_tac >> fs[])
		>- (metis_tac[])
		>- (metis_tac[HD]) ) )

val WF_listlex = Q.store_thm("WF_listlex",`WF listlex`,
simp[relationTheory.WF_DEF] >> rw[] >>
`?v. B' v ∧ !v'. B' v' ==> LENGTH v <= LENGTH v'`
  by (`WF (inv_image $< (LENGTH:bool list -> num) )` by (simp[relationTheory.WF_inv_image])>>
  fs[relationTheory.WF_DEF] >> metis_tac[NOT_LESS])>>
  qspecl_then[`{l|B' l ∧ (LENGTH l = LENGTH v)}`,`LENGTH v`,`v`] MP_TAC listlex_same_length >>
  rw[] >> qexists_tac`v'` >> rw[] >> strip_tac >> `LENGTH b <> LENGTH v` by metis_tac[] >>
  `LENGTH v' < LENGTH b` by metis_tac[LESS_OR_EQ] >>
  `listlex v' b` by metis_tac[listlex_length] >>
  metis_tac[LESS_EQUAL_ANTISYM,listlex_length2,prim_recTheory.LESS_REFL] )

val num_to_bool_list_def = tDefine"num_to_bool_list"`num_to_bool_list n =
			    if n=0 then []
			    else if EVEN n then
				T::num_to_bool_list((n-2) DIV 2)
			    else
				F::num_to_bool_list((n-1) DIV 2)`
(WF_REL_TAC `$<` >> intLib.ARITH_TAC)

val solomonoff_prior_def = Define`
solomonoff_prior x = suminf (λn. let b = num_to_bool_list n in
				     if universal_tm b = x
				     then inv(2 pow (LENGTH b))
				     else 0) `


val existence_of_universal_semimeasure = Q.store_thm("existence_of_universal_semimeasure",
`∃M. (semimeasure M) ∧ (universal_semimeasure M setX) ∧ (continous M) ∧ (lower_semicompute M)`,
qexists_tac `solomonoff_prior` >> conj_tac)

val summed_square_error_a_def = Define`summed_square_a_error mu a n =
                                       sum for (x IN Bstar:length x = n-1)
                                       (mu x) *(sqrt (cond_M a x) - sqrt (cond_mu a x))**2`

val summed_square_error_def = Define`summed_square_error mu n =
                                     sum for (a in B) summed_square_a_error mu a n`

val KL_dis_def = Define`KL_dis P Q = sum for (a in B) P(a)*log (P(a)/Q(a))`

val hellinger_dis_def = Define`hellinger_dis P Q = sum for (a in B) (sqrt(P(a)) - sqrt(Q(a)))**2`

val KL_greater_hellinger = Q.store_thm("KL_greater_hellinger",
`hellinger_dis P Q <= KL_dis P Q`,
)

val KL_M_dis_def = Define`KL_M_dis mu x = KL_dis (λy. cond_M y x) (λy. cond_mu y x)`

val sum_KL_M_dis_def = Define`sum_KL_M_dis mu n = sum for (x:length x = n-1)
                                                  (mu x) * (KL_M_dis mu x)`

val solomonoff_thm_claim_1 = Q.store_thm("solomonoff_thm_claim_1",
`(computable_measure mu) ==> summed_square_error mu n <= sum_KL_M_dis mu n`,
 )

val solomonoff_thm_claim_11 = Q.store_thm("solomonoff_thm_claim_1",
`(computable_measure mu) ==>
 sum for (n in N) summed_square_error mu n <= sum for (n in N) sum_KL_M_dis mu n`,
rw[sum_of_stuff,solomonoff_thm_claim_1] )

val solomonoff_thm_claim_2 = Q.store_thm("solomonoff_thm_claim_2",
`(computable_measure mu) ==> sum for (n in N) sum_KL_M_dis mu n <= (kolmog_complexity mu)*(log 2)`,
  )

val solomonoff_theorem = Q.store_thm("solomonoff_theorem",
`(computable_measure mu) ==>
 (sum for (n in N) summed_square_error mu n <= (kolmog_complexity mu)*(log 2) )`
rw[LESS_EQ_TRANS,solomonoff_thm_claim_11,solomonoff_thm_claim_2])
 *)

val _ = export_theory();
