(* See:
     Forster, Kunze and Roth,
     "The Weak Call-by-Value 𝜆-Calculus Is Reasonable for Both Time and Space", POPL 2020
   for inspiration
*)
open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory;

val _ = new_theory "Prelims";




(* ------------------
   Decidable Predicates
   ------------------ *)
(* Not needed in HOL4 *)

(* below is the coq code *)

(* Decidable predicates. Allows to write e.g. [if Dec (x=y) then _ else _ ] in functions
and [decide (x=y)] in Proofs to do case distinctions after showing that some property is decidable, e,g, see nat_eq_dec *)

(*
Definition dec (X: Prop) : Type := {X} + {~ X}.

Existing Class dec.

Definition Dec (X: Prop) (d: dec X) : dec X := d.
Arguments Dec X {d}.

Tactic Notation "decide" constr(p) :=
  destruct (Dec p).
Tactic Notation "decide" "_" :=
  destruct (Dec _).
*)




(* ------------------
	 Natural numbers
   ------------------ *)

Theorem size_induction:
	∀f p. (∀x. ((∀y. f y < f x ⇒ p y) ⇒ p x)) ⇒ (∀x. p x)
Proof
	ntac 4 strip_tac >>
	`(∀y. f y < f x ⇒ p y)` suffices_by gs[] >>
	`∀n y. f y < n ⇒ p y` suffices_by metis_tac[] >>
	Induct_on `n` >> rw[]
QED

(*
Instance nat_le_dec (x y : nat) : dec (x <= y) :=
  le_dec x y.

Notation "'eq_dec' X" := (forall x y : X, dec (x=y)) (at level 70).
Instance nat_eq_dec :
  eq_dec nat.
Proof.
  unfold dec. decide equality.
Defined.
*)




(* ------------------
	   	 Lists
   ------------------ *)

(* Notation "| A |" := (length A) (at level 65). *)

(*Notation for lookup*)
(* Notation "A .[ n ]" := (nth_error A n) (at level 1, format "A '.[' n ]").
Notation "x '∈' A" := (In x A) (at level 70). *)

(* A .[ n ]" := (nth_error n A) *)
Definition nth_error:
	nth_error 0 (h::_) = SOME h ∧
	nth_error (SUC n) (_::t) = nth_error n t ∧
    nth_error _ _ = NONE
End

Theorem nth_error_lt_Some:
	∀n H. n < LENGTH H ⇒ ∃x. nth_error n H = SOME x
Proof
	Induct_on `n` >> rw[nth_error, EL, ADD1]
	>- (qexists_tac `EL 0 H` >> Induct_on `H` >> rw[nth_error])
    >> Induct_on `H` >> rw[nth_error, EL, ADD1] >>
    first_x_assum drule >> rw[] >> metis_tac[nth_error, EL, ADD1]
QED

Theorem nth_error_Some_lt:
	∀n H x. nth_error n H = SOME x ⇒ n < LENGTH H
Proof
	Induct_on `n` >> Induct_on `H` >> rw[nth_error, EL, ADD1]
QED

Theorem nth_error_map:
	∀n H a f. nth_error n (MAP f H) = SOME a ⇒ ∃b. nth_error n H = SOME b ∧ a = f b
Proof
	Induct_on `n` >> Induct_on `H` >> rw[nth_error]
QED

Theorem map_nth_error:
	∀n H x f. nth_error n H = SOME x ⇒ nth_error n (MAP f H) = SOME (f x)
Proof
	Induct_on `n` >> Induct_on `H` >> rw[nth_error]
QED

Theorem nth_error_NONE_lt:
	∀n H. nth_error n H = NONE ⇒ LENGTH H ≤ n
Proof
	Induct_on `n` >> Induct_on `H` >> rw[nth_error]
QED

Theorem nth_error_lt_NONE:
	∀n H. LENGTH H ≤ n ⇒ nth_error n H = NONE
Proof
	Induct_on `n` >> rw[nth_error, EL, ADD1] >>
    Induct_on `H` >> rw[nth_error, EL, ADD1] >>
    first_x_assum drule >> rw[] >> metis_tac[nth_error, EL, ADD1]
QED

Theorem nth_error_SOME_lemma:
	∀n H h t x.
		nth_error n (h::t) = SOME x ⇒
		1 <= n ⇒
		nth_error (n-1) t = SOME x
Proof
	Induct_on `n` >> rw[nth_error, EL, ADD1] >>
    Induct_on `H` >> rw[nth_error, EL, ADD1] >>
    first_x_assum drule >> rw[] >> metis_tac[nth_error, EL, ADD1]
QED

Theorem nth_error_SOME_in_H:
	∀n H x. nth_error n H = SOME x ⇒ MEM x H
Proof
	Induct_on `n` >> Induct_on `H` >> rw[nth_error]
QED

Theorem nth_error_In:
  ∀l n x.
    nth_error n l = SOME x ⇒ MEM x l
Proof
  metis_tac[nth_error_SOME_in_H]
QED

Theorem nth_error_app1:
	∀l l' n.
		n < LENGTH l ⇒
    	nth_error n (l++l') = nth_error n l
Proof
	Induct_on `n` >> rw[nth_error, EL, ADD1] >>
    Induct_on `l` >> rw[nth_error, EL, ADD1] >>
    first_x_assum drule >> rw[] >> metis_tac[nth_error, EL, ADD1]
QED

Theorem nth_error_app2:
	∀l l' n.
		LENGTH l ≤ n ⇒
    	nth_error n (l++l') = nth_error (n-LENGTH l) l'
Proof
	Induct_on `n` >> rw[nth_error, EL, ADD1] >>
    Induct_on `l` >> rw[nth_error, EL, ADD1] >>
    first_x_assum drule >> rw[] >> metis_tac[nth_error, EL, ADD1]
QED


(* https://coq.inria.fr/library/Coq.Lists.List.html#Forall *)

Inductive Forall:
	Forall P [] ∧
	∀x l. P x ∧ Forall P l ⇒ Forall P (x::l)
End

Theorem Forall_map:
	∀p f x A. Forall (λx. p (f x)) A ⇒ Forall p (MAP f A)
Proof
	ntac 4 strip_tac >> Induct_on `Forall` >> rw[Forall_rules]
QED

Theorem Forall_f1_imp_f2:
	∀f1 f2 A.
		Forall (λx. f1 x) A ⇒
		(∀x. f1 x ⇒ f2 x) ⇒
		Forall (λx. f2 x) A
Proof
	ntac 3 strip_tac >> Induct_on `Forall` >> rw[Forall_rules]
QED

Theorem Forall_forall:
    ∀P l. Forall P l ⇔ (∀x. MEM x l ⇒ P x)
Proof
	Induct_on `l` >> rw[] >>
	rw[Once Forall_cases] >> metis_tac[]
QED

Theorem Forall_MEM:
  ∀x H P. Forall P H ∧ MEM x H ⇒ P x
Proof
  Induct_on `H` >> rw[]
  >- fs[Once Forall_cases]
  >> qpat_x_assum `Forall P (h::H)` mp_tac >>
  rw[Once Forall_cases]
QED


(*
Hint Extern 4 =>
match goal with
|[ H: ?x ∈ nil |- _ ] => destruct H
end.
*)

(*Register additional simplification rules with autorewrite*)
(* Hint Rewrite <- app_assoc : list. *)

(* not needed in HOL: already embedded in the tactics *)
Theorem in_app_or:
  ∀l m a.
    MEM a (l ++ m) ⇒ MEM a l ∨ MEM a m
Proof
  Induct_on `l` >> rw[]
QED



(* ------------------
	   Relations
   ------------------ *)


(*
Definition rcomp X Y Z (R : X -> Y -> Prop) (S : Y -> Z -> Prop) : X -> Z -> Prop :=
  fun x z => exists y, R x y /\ S y z.
*)

Definition rcomp:
	rcomp R S = (λx z. ∃y. R x y ∧ S y z)
End

(*
Structure ARS :=
  {
    ARS_X :> Type ;
    ARS_R : ARS_X -> ARS_X -> Prop
  }.
Notation "(≻)" := (@ARS_R _) (at level 0).
Notation "(≻ X )" := (@ARS_R X) (at level 0).
Notation "x  ≻  x'" := (ARS_R x x') (at level 40).
*)

Definition reducible:
	reducible R x = ∃x'. R x x'
End

Definition functional:
	functional R = ∀x y y'. R x y ⇒ R x y' ⇒ y = y'
End

Definition stepFunction:
	stepFunction R f =
		∀x. case (f x) of
				SOME y => R x y
			  | NONE   => ∀y. ¬(R x y)
End

Definition computable:
	computable R = ∃f. stepFunction R f
End

Definition classical:
	classical R = ∀s. reducible R s ∨ ¬(reducible R s)
End

Theorem computable_classical:
	computable R ⇒ classical R
Proof
	rw[computable, classical, computable]
QED

(* https://coq.inria.fr/library/Coq.Lists.List.html#Forall2 *)

Inductive Forall2:
[~nil:]
	(∀R. Forall2 R [] []) ∧
[~cons:]
	(∀x y l l' R. R x y ∧ Forall2 R l l' ⇒ Forall2 R (x::l) (y::l'))
End

Theorem Forall2_impl:
	∀A B P1 P2. (∀x y. P1 x y ⇒ P2 x y) ⇒ Forall2 P1 A B ⇒ Forall2 P2 A B
Proof
	Induct_on `Forall2` >> rw[Forall2_rules]
QED

(*
Inductive terminatesOn (X : Type) (R : X -> X -> Prop) x: Prop :=
  terminatesC (wf: forall x', R x x' -> terminatesOn R x').
*)
Inductive terminatesOn:
	∀(R: 'a -> 'a -> bool) (x: 'a).
		(∀x'. R x x' ⇒ terminatesOn R x') ⇒ terminatesOn R x
End

(* R: stepping/reducing function *)
Inductive evaluates:
	(∀x. ¬reducible R x ⇒ evaluates R x x) ∧
	∀x y z. R x y ∧ evaluates R y z ⇒ evaluates R x z
End

(*
Notation "(▷)" := (@evaluates _) (at level 0).
Notation "(▷ X )" := (@evaluates X) (at level 0).*)
(* workaround to prefere "x ≻ y" over "(≻) x y"*) (*Notation "x ▷ x'" := 0. *)

(*Notation "x ▷ x'" := (@evaluates _ x x').*)

Definition normalizes:
	normalizes R x = ∃y. evaluates R x y
End

(* Fact 1.1 *)
Theorem evaluates_fun:
	∀R. functional R ⇒ functional (evaluates R)
Proof
	rw[functional] >> pop_assum mp_tac >> qid_spec_tac `y'` >> pop_assum mp_tac >>
	MAP_EVERY qid_spec_tac [`y`, `x`] >> ho_match_mp_tac evaluates_strongind >> rw[]
	>- (gvs[Once evaluates_cases] >> gvs[reducible])
	>> pop_assum (strip_assume_tac o PURE_ONCE_REWRITE_RULE[evaluates_cases])
	>- gvs[reducible]
	>> `x' = y''` by metis_tac[] >> gvs[]
QED

(* Fact 1.2 *)
Theorem normalizes_terminates:
	functional R ⇒ (∀x. normalizes R x ⇒ terminatesOn R x)
Proof
	rw[normalizes] >> qpat_x_assum (`functional R`) mp_tac >>
	pop_assum mp_tac >> MAP_EVERY qid_spec_tac [`y`, `x`] >>
	Induct_on ‘evaluates’ >> rw[] (* 2 *)
	>- (simp[Once terminatesOn_cases] >> metis_tac[reducible]) >>
	first_x_assum drule >> rw[] >> simp[Once terminatesOn_cases] >>
	metis_tac[functional]
QED

Theorem irred_evaluates_refl:
	∀ x. (∀y. ¬ R x y) ⇒ evaluates R x x
Proof
	metis_tac[evaluates_rules,reducible]
QED

(* Fact 1.3 *)
Theorem terminates_normalizes:
	computable R ⇒ ∀x. terminatesOn R x ⇒ normalizes R x
Proof
	rw[] >> qpat_x_assum (`computable R`) mp_tac >>
	pop_assum mp_tac >> qid_spec_tac `x` >>
	Induct_on `terminatesOn` >> rw[normalizes] >>
	‘computable R ⇒ ∀x'.R x x' ⇒ terminatesOn R x' ∧ ∃y. evaluates R x' y’
    	by metis_tac[] >>
	first_x_assum drule >> strip_tac >>
	qpat_x_assum ‘computable _’ mp_tac >> rw[computable,stepFunction] >>
	Cases_on ‘f x’ (* 2 *)
	>- (first_x_assum $ qspec_then ‘x’ assume_tac >> rfs[] >>
	    metis_tac[irred_evaluates_refl]) >>
	first_x_assum $ qspec_then ‘x’ assume_tac >> rfs[] >>
	first_x_assum drule >> strip_tac >> metis_tac[evaluates_rules]
QED

Theorem evaluates_irred:
	∀x y. evaluates R x y ⇒ ¬reducible R y
Proof
	Induct_on ‘evaluates’ >> rw[]
QED

(* ------------------
	      Misc
   ------------------ *)

Definition noneHolds:
	noneHolds Ps =
		case Ps of
			| [] => T
			| P::Ps => ¬P ∧ noneHolds Ps
End

Definition exactlyOneHolds:
	exactlyOneHolds Ps =
		case Ps of
			| [] => F
			| P::Ps => (P ∧ noneHolds Ps) ∨ (¬P ∧ exactlyOneHolds Ps)
End

(*

Ltac noneHoldsI :=
  lazymatch goal with
    |- noneHolds [] => now constructor
  | |- noneHolds (_::_) => split;[|noneHoldsI]
  end.

Ltac exactlyOneHoldsI n :=
  lazymatch n with
  | 1 =>  left;split;[|noneHoldsI]
  | S ?n => right;split;[|exactlyOneHoldsI n]
  end.

Ltac inv_noneHolds H :=
  lazymatch type of H with
  | noneHolds [] => clear H
  | noneHolds (_::_) => let tmp := fresh "tmp" in destruct H as [? tmp];inv_noneHolds tmp
  end.

Ltac inv_exactlyOneHolds H :=
  lazymatch type of H with
  | exactlyOneHolds [] => now inversion H
  | exactlyOneHolds (_::_) => let tmp := fresh "tmp" in destruct H as [[? tmp]|[? tmp]];[inv_noneHolds tmp|inv_exactlyOneHolds tmp]
  end.

*)

(** Nicer Notation for Option *)

(*
Notation "'try' x ':='  t 'in' u":=
  (match t with Some x => u | None => None end)
    (at level 200, right associativity).
*)

(* ------------------
     Coq.Init.Logic
   ------------------ *)

Inductive eq:
[~refl:]
  (∀x. eq x x)
End

(* -----------------------
    Coq.Classes.Morphisms
   ----------------------- *)

Definition Proper:
  Proper R m = R m m
End

Definition respectful:
  respectful R R' = (λf g. ∀x y. R x y ⇒ R' (f x) (g y))
End

(* ------------------
	      Numbers
   ------------------ *)

(*
f applied to x for n times
  f(f(....f(x))
*)
Definition it_def:
	it f n x =
		case n of
		  | 0 => x
		  | SUC n' => f (it f n' x)
End

(* ------------------
	      ARS
   ------------------ *)

(*
Takes in two arguments x z,
  exists an intermidate y such that
  R x y /\ S y z
*)
Definition rcomp:
	rcomp R S = (λx z. ∃y. R x y ∧ S y z)
End

(*
(rcomp R) applied to eq for n times
  rcomp R(rcomp R(...rcomp R eq))

In english:
  given two arguments x and z,
    pow R n x z means
      there are 'n' intermediate values 'y' such that
        x R y1, y1 R y2, ..., y(n-1) R yn, yn eq z
*)
Definition pow:
	pow R n = it (rcomp R) n eq
End

val it = EVAL ``pow (<) 3``;

Theorem pow_add:
  ∀R n m s t.
    pow R (n + m) s t ⇔ rcomp (pow R n) (pow R m) s t
Proof
  Induct_on `n` >> rw[] >> EQ_TAC
  >- (rw[pow, rcomp] >> rw[Once it_def] >>
      irule_at (Pos hd) eq_refl >> rw[])
  >- (rw[rcomp, pow] >>
      qpat_x_assum `it _ 0 _ _ _` mp_tac >>
      rw[Once it_def] >> fs[Once eq_cases])
  >- (fs[rcomp, pow] >> rw[] >>
      rw[Once it_def, rcomp] >>
      fs[ADD_CLAUSES] >>
      pop_assum mp_tac >>
      rw[Once it_def, rcomp] >> metis_tac[])
  >> fs[rcomp, pow] >> rw[] >>
   fs[ADD_CLAUSES] >>  rw[Once it_def, rcomp] >>
   qpat_x_assum `it _ (SUC n) _ _ _` mp_tac >>
   rw[Once it_def, rcomp] >>
   metis_tac[]
QED

Theorem pow_add_L:
  ∀R n m s t.
    pow R (n + m) s t ⇒ rcomp (pow R n) (pow R m) s t
Proof
  metis_tac[pow_add]
QED

Theorem pow_add_R:
  ∀R n m s t.
    rcomp (pow R n) (pow R m) s t ⇒ pow R (n + m) s t
Proof
  metis_tac[pow_add]
QED

(*
Notation "p '<=1' q" := (forall x, p x -> q x) (at level 70).
Notation "p '=1' q" := (p <=1 q /\ q <=1 p) (at level 70).
Notation "R '<=2' S" := (forall x y, R x y -> S x y) (at level 70).
Notation "R '=2' S"  := (R <=2 S /\ S <=2 R) (at level 70).
*)

Theorem rcomp_1:
  ∀R.
   ((∀x y. R x y ⇒ (pow R 1) x y) ∧ (∀x y. (pow R 1) x y ⇒ R x y))
Proof
  rw[pow]
  >- (rw[Once it_def, rcomp] >> rw[Once it_def, rcomp] >>
      qexists_tac `y` >> rw[Once eq_refl])
  >> fs[Once it_def, rcomp] >> fs[Once it_def, rcomp] >>
  fs[Once eq_cases]
QED

Theorem rcomp_1_L:
  ∀R.
   (∀x y. R x y ⇒ (pow R 1) x y)
Proof
  metis_tac[rcomp_1]
QED

Theorem rcomp_1_R:
  ∀R.
   (∀x y. (pow R 1) x y ⇒ R x y)
Proof
  metis_tac[rcomp_1]
QED

(* reduce while keeping track of the maximum size of terms *)
Inductive redWithMaxSize:
[~R:]
	(∀size step (m: num) s. m = size s ⇒ redWithMaxSize size step m s s) ∧
[~C:]
	(∀size step (s: 'a) (s': 'a) (t: 'a) (m: num) (m':num).
		step s s' ∧
		redWithMaxSize size step m' s' t ∧
		m = MAX (size s) m' ⇒
		redWithMaxSize size step m s t)
End

Theorem redWithMaxSize_ge:
  ∀size step s t m.
    redWithMaxSize size step m s t ⇒
    size s ≤ m ∧ size t ≤ m
Proof
  Induct_on `redWithMaxSize` >> rw[]
QED

Theorem redWithMaxSize_trans:
  ∀size step s t u m1 m2 m3.
    redWithMaxSize size step m1 s t ⇒
    redWithMaxSize size step m2 t u ⇒
    MAX m1 m2 = m3 ⇒
    redWithMaxSize size step m3 s u
Proof
  Induct_on `redWithMaxSize` >> rw[]
  >- (qpat_x_assum `redWithMaxSize _ _ _ _ _` mp_tac >>
      rw[Once redWithMaxSize_cases]
      >- rw[Once redWithMaxSize_cases]
      >> rw[Once redWithMaxSize_cases] >>
      drule redWithMaxSize_ge >> rw[] >>
      rw[Once MAX_DEF] >> fs[NOT_LESS] >> rw[]
      >- (rw[Once MAX_DEF] >>
          goal_assum drule >> goal_assum drule >>
          rw[MAX_DEF])
      >> metis_tac[MAX_DEF])
  >> rw[Once redWithMaxSize_cases] >>
  drule redWithMaxSize_ge >> rw[] >>
  `size s' ≤ m1'` by metis_tac[redWithMaxSize_ge] >>
  `size t ≤ m1'` by metis_tac[redWithMaxSize_ge] >>
  first_x_assum drule >> rw[] >>
  pop_assum mp_tac >> rw[Once redWithMaxSize_cases]
  >- (pop_assum mp_tac >> rw[Once MAX_DEF] >>
      fs[NOT_LESS] >>
      drule_all LESS_EQUAL_ANTISYM >>
      qpat_x_assum `size s' ≤ m2` (fn _ => all_tac) >>
      qpat_x_assum `m2 ≤ size s'` (fn _ => all_tac) >>
      rw[] >>
      `∃s'' m'.
        step s s'' ∧ redWithMaxSize size step m' s'' s' ∧
        MAX (MAX (size s) (size s')) (size s') = MAX (size s) m'` suffices_by simp[] >>
      qexistsl_tac [`s'`, `size s'`] >> rw[]
      >- rw[Once redWithMaxSize_cases]
      >> rw[Once MAX_DEF])
  >> `∃s' m'.
        step s s' ∧ redWithMaxSize size step m' s' u ∧
        MAX (MAX (size s) m1') m2 = MAX (size s) m'` suffices_by simp[] >>
  qexistsl_tac [`s'`, `MAX m1' m2`] >> rw[]
  >- (rw[Once redWithMaxSize_cases] >> metis_tac[])
  >> `MAX (MAX (size s) m1') m2 = MAX (size s) (MAX m1' m2)` suffices_by simp[] >>
  rw[MAX_ASSOC]
QED

val _ = export_theory ()