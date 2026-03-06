Theory imodal


Ancestors
  hol string

(* lecture 2 *)

(* See Alex Simpson's PhD from Edinburgh 1994. *)

(* aim is to develop an "IK", such that IK ⊢ A  iff  IFOL ⊢ ∀x. Aˣ

   where Aˣ is the standard translation of modal formula A, using
   variable x to represent the world.

   We can reason at the meta-level classically, but the semantics
   is wrt intuitionistic first order logic.
*)

Datatype:
  imform = imvar string | imconj imform imform | imdisj imform imform
         | imimp imform imform | imbot | imbox imform
End

(* new rule
    ∅ ⊢ A
  --------
    Γ ⊢ □ A

new axiom

  □ (A → B) → ( □ A → □ B)


*)

(*
        Godel translation  (IPL into modal logic)


        ⊥꙳   =   ⊥
        v꙳   =   □ v
  (A ∧ B)꙳   =  A꙳ ∧ B꙳
  (A → B)꙳   =  □ (A꙳ → B꙳)


    translation works:

    IPL ⊢ A ⇔  S4 (* reflexive, transitive *) ⊢ A꙳


IML semantics combines the preorder for valuations ≤, and a reachability R.

R and ≤ interact:

- if u R x and u ≤ v, then ∃y. v R y ∧ x ≤ y.  (diamond - forward)
- if u R x and x ≤ y, then ∃v. u ≤ v ∧ v R y   ("back")

Semantics of implication as above, (∀v. u ≤ v ⇒ if v ⊧ A then v ⊧ B)
for box:

   u ⊧ □ A   =    ∀v w. u ≤ v ∧ v R w ⇒ w ⊧ A

   u ⊧ ◇ A   =    ∃v. u R v ∧ v ⊧ A

 exercise, show ⊧ (⋄ p → □ q) → □ (p → q)

axiomatisation (Plotkin & Stirling)


  add K⋄ : □ (A → B) → (◇A → ◇B)
     n◇  : ◇⊥ → ⊥
     c◇ : ◇(A ∨ B) → (◇A ∨ ◇B)
     i◇ □ : (◇A → □ B) → □ (A → B)

  use necessitation, MP as primitive rules; no additional rules for ◇ required.

(There is another system due to Fischer-Servi.)

       We get the desired correspondence:

       IK ⊢ A  iff    ⊧ A     iff    IFOL ⊢ ∀x. Aˣ

       soundness is straightforward, for completness, prove the
       contrapositive:   ¬ ⊢ A ⇒ ¬⊧ A
*)

(* Lecture 3 *)

(* extend sequent calculus to include modalities ; design of this system
   "requires" us to be able to prove the axioms,

quickly run into great difficulty in coming up with appropriate left-side and right-side rules for the diamond and box. Approach following Simpson is a labelled sequent calculus inspired by the standard translation and a FOL sequent calculus.  Now, all formulas are labelled with their worlds, and we also build up relational-atoms encoding the R-links between the worlds.

The FOL system for LJ is used "secretly" to give us the standard translation
of the modal formulas:

    R, x ↦ y | Γ   ⇒  y : A
   ---------------------------  □-L  (y must be fresh)
           R | Γ   ⇒ x : □ A


    R, x ↦ y | Γ  => y : A
   ---------------------------  ◇-R
    R, x ↦ y | Γ   ⇒ x : ◇ A

rules on left are duals that don't erase original formulas

Note that the graph built inside R will actually be a tree with root being
the first world/label. And of course a proof is finite, so every proof will
build a finite tree.

      This helps with the interpretation of a sequent as a formula:

      R | Γ  ⇒  z: C  λˣ interprets the LHS, ρˣ interprets the whole

      λˣ (R | Γ) = ⋀ (x:A ∈ Γ) ∧
                   ⋀ (xRy ∈ R) (◇ (λʸ (R↓y | Γ)))
     where R↓y is the tree rooted at y

     ρˣ ( R | Γ  ⇒  z: C)  = λˣ(R|Γ) → C   if x = z

     otherwise let u be the next step on path from x to z,
     and
       ρˣ ( R | Γ ⇒  z : C) =  λˣ (R↓u | Γ) → □ (ρᵘ (R↓u | Γ  ⇒ z:C))

# Lecture 4:

## Soundness & Completeness (for sequent calculus system)

. ⇒  x:A ------ soundness ---->  ⊢ A
             --- simulation ---> . ⇒ A (with cut)
             --- cut-admissibility ---> . ⇒ A (back to start)

### Soundness

Use the translation and by induction on the sequent calculus rules, and
show that the analogous steps can be carried out in the core proof system ⊢.

### Simulation

Modus-ponens in the Hilbert system requires us to use cut in the
simulation-world, where we have cut as

                     R | Γ  ⇒  x:A           R | Γ, x:A  ⇒ z:C
                    -------------------------------------------
                                  R | Γ ⇒ z:C

### Cut-Elimination

Given π₁ a proof of left premise above, and π₂ a proof of the right one,
prove that R | Γ ⇒ z:C without using cut.  I.e., this is admissibility of cut.

Prove by lexicographic induction on

  (size(A), height (π₁) + height (π₂))

Cases on whether or not last rules in π₁ and π₂ apply to the x:A formula
or not.

Can be extended into "full cut-elimination" (provision of a "gadget" that
can replace all occurrences of cut in an algorithmic/mechanical way).

## A “semantic” sequent calculus  --- “fully labelled”

Inspired by observation that we have two relations (R and ≤) in the models,
but our labelled sequent calculus only has relational-atoms for the R assertions.

So, we build a new system that has x ≤ y assertions too, and these appear in
the implication and □ rules:

     R, x ≤ y, yRz | Γ  ⇒  z:A, Δ
    ---------------------------------- □ - R
                 R | Γ  ⇒  x:□ A, Δ


     R, x ≤ y | Γ, y:A   ⇒   y:B, Δ
    ------------------------------------
            R | Γ        ⇒   x:A → B, Δ


also rules that allow contexts to be enriched with new atoms corresponding
to ≤ being a partial order, and the forward and backwards confluence
requirements.

The right-hand side becomes a multiset with, e.g., the "classical" ∨-R rule;
the intuitionism is captured by the ≤ requirements on □ and → (reflecting
the fact that the Tarski-semantics is/can-be-seen-as classical).

In some sense, this is just unwinding the definition and applying all
possible consequences because there are only finitely many.

Relatively straightforward to show this is sound & complete wrt the
semantics.

# Part 5

## (proof of soundness and completeness)

## extend negtrans to modal logic

This translates from classical K to IK.

negtrans (□ A) = □ (negtrans A)

         [See : "The Proof Theory blog: ‘Brouwer meets Kripke’" ]

While it's clear that IK doesn't prove more purely propositional formulas than
the underlying IPL, curiously, IK without the axioms mentioning diamond ("iK"),
fails to prove some of the diamond-free formulas that the bigger system does.

 iK doesn't prove ¬¬ □ ¬p → □ ¬p
*)
