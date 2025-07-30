(*===========================================================================*)
(* Tricky recursive definition of list reversal. Doesn't use any other       *)
(* functions, nor extra arguments. From Joe Hurd.                            *)
(*===========================================================================*)
Theory rev
Ancestors
  prim_rec list


(*---------------------------------------------------------------------------
     The definition
  ---------------------------------------------------------------------------*)

val rev_defn = Hol_defn
  "rev"
  ‘rev [] = [] /\
   rev (x::xs) =
      case rev xs
       of [] => [x]
       | y::ys => y :: rev (x::rev ys)’;

(*---------------------------------------------------------------------------
   Instantiate and simplify the auxiliary eqns and induction theorem
  ---------------------------------------------------------------------------*)

val [rev_ind, rev_nil, rev_cons] =
  Defn.instantiate_aux rev_defn
        “measure LENGTH”
        (SIMP_RULE arith_ss [] o SRULE[]);

Overload revFn[local] = “rev_aux (measure LENGTH)”

(*---------------------------------------------------------------------------
    Size preservation
  ---------------------------------------------------------------------------*)

Theorem revFn_length_eq[local]:
  ∀L. LENGTH (revFn L) = LENGTH L
Proof
  recInduct rev_ind >> rw[]
  >- rw[rev_nil]
  >- (mp_tac rev_cons >> CASE_TAC >> gvs[])
QED

Theorem measure_length[local]:
   measure LENGTH = λx y. LENGTH x < LENGTH y
Proof
 rw[measure_thm,FUN_EQ_THM]
QED

(*---------------------------------------------------------------------------
   val rev_def =
    ⊢ rev [] = [] ∧
      rev (x::xs) = case rev xs of [] => [x] | y::ys => y::rev (x::rev ys)

   val rev_ind =
      ⊢ ∀P. P [] ∧
            (∀x xs.
               (∀y ys. rev xs = y::ys ⇒ P ys) ∧
               (∀y ys. rev xs = y::ys ⇒ P (x::rev ys)) ∧ P xs ⇒
               P (x::xs)) ⇒
            ∀v. P v: thm
  ---------------------------------------------------------------------------*)

val (def, ind) = Defn.tprove
(rev_defn,
  WF_REL_TAC ‘measure LENGTH’ >>
  rw[GSYM measure_length] >>
  rule_assum_tac $ Q.AP_TERM ‘LENGTH’ >>
  gvs [revFn_length_eq])

Theorem rev_def = def;
Theorem rev_ind = ind;

Theorem rev_eq:
  rev = REVERSE
Proof
  simp [FUN_EQ_THM] >>
  recInduct rev_ind >> rw[] >>
  simp[Once rev_def] >>
  CASE_TAC >> simp[]
QED

