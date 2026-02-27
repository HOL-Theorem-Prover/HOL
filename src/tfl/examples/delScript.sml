Theory del
Ancestors
  list arithmetic
Libs
  Defn TotalDefn DefnBase

val defn = Hol_defn "foo"
 ‘foo (l,n) s = if n = 0 then l else foo (s::l,n - 1) s’;

val defn = Hol_defn "bar"
 ‘bar l n s = if n = 0 then l else bar (s::l) (n - 1) s’;

(*---------------------------------------------------------------------------*)
(* foo and bar support definitions not retired, since termination proof not  *)
(* attempted above. For test, termination is proved, so its support          *)
(* definition are deleted.                                                   *)
(*---------------------------------------------------------------------------*)

Definition test_def:
  test (l,n) s = if n = 0 then l else test (s::l,n - 1) s
Termination
  WF_REL_TAC ‘measure (SND o FST)’
End

val _ = print_theory "-";

(*---------------------------------------------------------------------------*)
(* "Formally" nested function below is actually not problematic since        *)
(* no termination-relevant info passes between recursive calls. This makes   *)
(* the termination argument straightforward.                                 *)
(*---------------------------------------------------------------------------*)

Theorem termination_lemma[local]:
  list_size (g ∘ SND) plist < list_size (pair_size f g) plist + 1
Proof
  Induct_on `plist` >> rw[] >> Cases_on `h` >> simp[]
QED

Theorem termination_lemma_alt[local] =
  termination_lemma |> SRULE [combinTheory.o_DEF];

Datatype:
  exp =
    Mat (exp list) (('a list # exp) list)
  | Let ('b) exp exp
End

Definition compile_exp_def:
  (compile_exp cfg (Mat xs ps) =
     let (i, sgx, ys) = compile_exps cfg xs in
     let (j, sgp, ps2') = compile_exps cfg (MAP SND ps) in
     let ps2 = ZIP (MAP FST ps,ps2')
     in
      (ARB, sgx \/ sgp, Let (ARB) (HD ys) ARB)) /\
  (compile_exp cfg exp = (0, F, exp)) /\
  (compile_exps cfg [] = (0, F, [])) /\
  (compile_exps cfg (x::xs) =
    let (i, sgx, y) = compile_exp cfg x in
    let (j, sgy, ys) = compile_exps cfg xs in
    (MAX i j, sgx \/ sgy, y :: ys))
Termination
  WF_REL_TAC
   ‘inv_image $<
      (sum_size
         (min_pair_size (λv. 0) (exp_size (λv. 0) (λv. 0)))
         (min_pair_size (λv. 0)
            (list_size (exp_size (λv. 0) (λv. 0)))))’ >>
  rw [] >> pop_assum kall_tac >>
  irule (DECIDE “a:num < c ⇒ a < b + c”) >>
  simp[termination_lemma_alt]
End

val _ = print_theory "-";
