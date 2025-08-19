(*---------------------------------------------------------------------------
   Conditional expressions and their normalization (Boyer and Moore).
  ---------------------------------------------------------------------------*)
Theory cond_exp
Ancestors
  arithmetic


(*---------------------------------------------------------------------------
   Datatype of conditional expressions.
  ---------------------------------------------------------------------------*)

Datatype:
  cond = A ind
       | IF cond cond cond
End

(*---------------------------------------------------------------------------
   Normalization function
 ---------------------------------------------------------------------------*)

val norm_defn = Hol_defn
  "norm"
  ‘norm (A x) = A x ∧
   norm (IF (A x) y z) = IF (A x) (norm y) (norm z) ∧
   norm (IF (IF u v w) y z) = norm (IF u (IF v y z) (IF w y z))’

(*---------------------------------------------------------------------------
   Termination, via a prim. rec measure function, due to Robert Shostak.
 ---------------------------------------------------------------------------*)

Definition Meas_def:
   Meas (A i) = 1 ∧
   Meas (IF x y z) = Meas x + (Meas x * Meas y + Meas x * Meas z)
End

Theorem Meas_positive:
   0 < Meas c
Proof
   Induct_on ‘c’ >> rw[Meas_def]
QED

val (norm_eqns,norm_ind) =
 Defn.tprove
  (norm_defn,
   WF_REL_TAC `measure Meas` >>
   rw [Meas_def,LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] >>
   rw_tac std_ss [AC ADD_ASSOC ADD_SYM, AC MULT_ASSOC MULT_SYM] >>
   metis_tac [LESS_MULT2, Meas_positive, DECIDE``!y m. 0<y ==> m < n+(y+m)``]
  );


(*---------------------------------------------------------------------------
   Another termination proof uses a lexicographic combination of
   relations. This is the version given in the Boyer-Moore book.
 ---------------------------------------------------------------------------*)

Definition Tdepth_def:
   Tdepth (A i) = 0 ∧
   Tdepth (IF x y z) = Tdepth x + 1
End

Definition Weight_def:
   Weight (A i) = 1 /\
   Weight (IF x y z) = Weight x * (Weight y + Weight z)
End

Theorem Weight_positive:
   0 < Weight c
Proof
  Induct_on ‘c’ >>
  rw [Weight_def,GSYM ADD_ASSOC, GSYM MULT_ASSOC,
     LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] >>
  metis_tac [LESS_MULT2, DECIDE ``!x y z. x < y ==> x < y + z``]
QED

val (norm_eqns,norm_ind) =
Defn.tprove
 (norm_defn,
  WF_REL_TAC `inv_image ($< LEX $<) (\x. (Weight x, Tdepth x))` >>
  rw [Weight_def,Tdepth_def, LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] >>
  metis_tac [Weight_positive]
 );

