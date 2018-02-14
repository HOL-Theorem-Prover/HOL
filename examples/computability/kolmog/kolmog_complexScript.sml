
open HolKernel Parse boolLib bossLib finite_mapTheory;
open recursivefnsTheory;
open prnlistTheory;
open primrecfnsTheory;
open listTheory;
open arithmeticTheory;
open numpairTheory;
open pred_setTheory;
open measureTheory;
val _ = new_theory "kolmog_complex";


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

val B_def = Define`B = {0n;1}`;


(* union n=0^inf {0,1}^n *)
val Bstar_def = Define`Bstar =univ(:bool list)`;

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

val universal_tm_def = new_constant ("universal_tm",``:bool list -> bool list option``)

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

val kolmog_complexity_def = Define`kolmog_complexity x =
                       if  { p | universal_tm p = SOME x} = {} then NONE
                       else SOME (MIN_SET {LENGTH p | universal_tm p = SOME x})`;

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

(* 

val solomonoff_prior_def = Define`
solomonoff_prior x = suminf {p | universal_tm p = x } 2**(-LENGTH p)`


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
