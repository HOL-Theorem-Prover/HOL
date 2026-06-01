# NFA to DFA

A classic result of computer science theory is that the languages
recognized by DFAs are equal to the languages recognized by NFAs. This
was first proved by Michael Rabin and Dana Scott in *Finite automata
and their decision problems*, IBM Journal of Research and Development
3(2), 114–125 (1959).  The *subset construction* forms the backbone of
their proof; it works by translating an NFA into an "equivalent" DFA.
The key insight in the construction is to make a state of the
constructed DFA embody the states the NFA could possibly be in at a
particular stage of processing the input word. The idea is
conceptually appealing but it raises a technical problem: how to
somehow arrange that the DFA state (a thing of type `:num`) *is* a set
of NFA states (a thing of type `:num -> bool`).

## Encoding subsets

Our solution to the problem is to adopt a bijective mapping that
encodes sets of NFA states as natural numbers. The DFA is then
constructed so that its states are encodings of sets of NFA
states. Thus we want two functions

```
  encode : num set -> num
  decode : num -> num set
```

such that `decode (encode s) = s`, for any `s ⊆ N.Q`. There is a
variety of ways to achieve this; we choose one that highlights a
distinctive aspect of the HOL logic, namely the *Hilbert Choice*
operator.

The Hilbert choice operator, written `@x. P x`, is syntax for
expressing the notion "pick an *x* having property *P*".  (The Hilbert
choice operator is also called the *Select* operator or also the
*Indefinite Description* operator.) The Choice operator is a way to
form a term---intended to have a given property---in a context where
the property may not in fact hold. The expectation is that, in a
later, richer, context, the property will hold, and then the term can
be reasoned with.

This may sound like preposterous gobbledygook, so let's look at our
desired encode/decode pair. First we define the encoder for an NFA `N`
by picking a function `f` that is a bijection from the powerset `POW
N.Q` of the states of `N` to a suitable set of numbers.
(Note: `count n = {m | m < n}`.)

```
Definition encode_def:
  encode N = @f. ∃b. BIJ f (POW N.Q) (count b)
End
```

In general such an `f` doesn't exist. (Why?) But it does if `N` is a
wellformed NFA, since then `N.Q` is finite and so the powerset of
states is finite. But before we get to that reasoning we are also able
to define the decoder function as the left inverse to the encoder:

```
Definition decode_def:
  decode N = LINV (encode N) (POW N.Q)
End
```

We now create a context in which an encoder exists, and then our
desired property has a compact proof:

```
Theorem codec:
  wf_nfa N ∧ s ⊆ N.Q ⇒ decode N (encode N s) = s
Proof
  strip_tac >> simp [decode_def,encode_def] >>
  SELECT_ELIM_TAC >> rw []
  >- metis_tac [FINITE_BIJ_COUNT, BIJ_SYM, wf_nfa_def, FINITE_POW] >>
  rename1 ‘BIJ f _ _’ >>
  irule LINV_DEF >> metis_tac [IN_POW,BIJ_DEF]
QED
```

We will look at this proof in detail.

### Proofs with Hilbert's Choice terms

To the initial goal we apply `strip_tac` which yields the goal

```
    0.  wf_nfa N
    1.  s ⊆ N.Q
   ------------------------------------
        decode N (encode N s) = s
```

We bravely expand the definitions of both encoder and decoder:

```
  simp [decode_def,encode_def]
```

only to be confronted by a horrible-looking goal:

```
    0.  wf_nfa N
    1.  s ⊆ N.Q
   ------------------------------------
        LINV (@f. ∃b. BIJ f (POW N.Q) (count b)) (POW N.Q)
          ((@f. ∃b. BIJ f (POW N.Q) (count b)) s) =
        s
```

The definition of `encode` has been expanded twice, so we get two
copies of the "choice" term. Although this looks daunting, there is a
useful tactic for goals with Hilbert choice terms:

```
  SELECT_ELIM_TAC
```

application of which generates a much nicer goal:

```
    0.  wf_nfa N
    1.  s ⊆ N.Q
   ------------------------------------
        (∃x b. BIJ x (POW N.Q) (count b)) ∧
        ∀x. (∃b. BIJ x (POW N.Q) (count b)) ⇒ LINV x (POW N.Q) (x s) = s
```

What has happened? We can make sense of it by looking at the theorem
that `SELECT_ELIM_TAC` automates:

```
  > SELECT_ELIM_THM;
  val it = ⊢ ∀P Q. (∃x. P x) ∧ (∀x. P x ⇒ Q x) ⇒ Q ($@ P): thm
```

This effectively reduces reasoning that a choice term `@x. P x` has
property `Q` to two properties where the choice term is no longer
present:

- showing there is a witness for property `P`

- showing that anything having property `P` also has property `Q`

Returning to the proof, we split into two goals:

```
  rw []
```

This gives

```
    0.  wf_nfa N
    1.  s ⊆ N.Q
    2.  BIJ x (POW N.Q) (count b)
   ------------------------------------
        LINV x (POW N.Q) (x s) = s

    0.  wf_nfa N
    1.  s ⊆ N.Q
   ------------------------------------
        ∃x b. BIJ x (POW N.Q) (count b)
```

The lower goal goes first. We now search for any theorem that could
help advance the proof. One can search by name or pattern; here we
search for any theorem stored under a name including both `BIJ` and
`count`. In fact the search term is `"bij~count"` since name search is
case-insensitive. (The middle `~` symbol means that order is not
relevant.) There are 4 results returned:

```
pred_setTheory.BIJ_NUM_COUNTABLE (THEOREM)
------------------------------------------
⊢ ∀s. (∃f. BIJ f 𝕌(:num) s) ⇒ countable s
[$(HOLDIR)/src/pred_set/src/pred_setScript.sml:8710]


pred_setTheory.COUNTABLE_ALT_BIJ (THEOREM)
------------------------------------------
⊢ ∀s. countable s ⇔ FINITE s ∨ BIJ (enumerate s) 𝕌(:num) s
[$(HOLDIR)/src/pred_set/src/pred_setScript.sml:8728]


pred_setTheory.FINITE_BIJ_COUNT (THEOREM)
-----------------------------------------
⊢ ∀s. FINITE s ⇒ ∃f b. BIJ f (count b) s
[$(HOLDIR)/src/pred_set/src/pred_setScript.sml:4631]


pred_setTheory.FINITE_BIJ_COUNT_EQ (THEOREM)
--------------------------------------------
⊢ ∀s. FINITE s ⇔ ∃c n. BIJ c (count n) s
[$(HOLDIR)/src/pred_set/src/pred_setScript.sml:4613]
```

The last two are both usable. Let's work with `FINITE_BIJ_COUNT`.  One
can reason as follows: "if `POW N.Q` is finite the theorem gives me a
bijection `f` from a `count` set to it. But I actually need a
bijection in the other direction, which I can get via `BIJ_SYM`". The
details of this become tedious (try it) but a call to `metis_tac`
automates the proof:

```
  metis_tac [FINITE_BIJ_COUNT, BIJ_SYM, wf_nfa_def, FINITE_POW]
```

The first conjunct is done. This leaves the goal

```
    0.  wf_nfa N
    1.  s ⊆ N.Q
    2.  BIJ x (POW N.Q) (count b)
   ------------------------------------
        LINV x (POW N.Q) (x s) = s
```

We can rename `x` to the more evocative `f` by giving a pattern:

```
  rename1 ‘BIJ f _ _’
```

This gives

```
    0.  wf_nfa N
    1.  s ⊆ N.Q
    2.  BIJ f (POW N.Q) (count b)
   ------------------------------------
        LINV f (POW N.Q) (f s) = s
```

A search with the pattern `LINV _ _ _ = _` finds two matching
candidates, one of which is perfect:

```
pred_setTheory.LINV_DEF (THEOREM)
---------------------------------
⊢ ∀f s t. INJ f s t ⇒ ∀x. x ∈ s ⇒ LINV f s (f x) = x
[$(HOLDIR)/src/pred_set/src/pred_setScript.sml:2785]
```

Backchaining with this theorem

```
  irule LINV_DEF
```

we obtain the goal

```
    0.  wf_nfa N
    1.  s ⊆ N.Q
    2.  BIJ f (POW N.Q) (count b)
   ------------------------------------
        s ∈ POW N.Q ∧ ∃t. INJ f (POW N.Q) t
```

Both conjuncts of this are direct consequences of the hypotheses
and existing facts so we appeal to `metis_tac`:

```
  metis_tac [IN_POW,BIJ_DEF]
```

This succeeds, `metis_tac` printing some progress information as it
works, and then the proof unwinds, proving intermediate goals back to
the original goal.

```
metis: r[+0+10]+0+0+0+0+0+0+0+0+1#
r[+0+10]+0+0+0+0+0+1#

Goal proved.
 [...] ⊢ s ∈ POW N.Q ∧ ∃t. INJ f (POW N.Q) t

Goal proved.
 [...] ⊢ LINV f (POW N.Q) (f s) = s

Goal proved.
 [...] ⊢ LINV x (POW N.Q) (x s) = s
val it =
   Initial goal proved.
   ⊢ wf_nfa N ∧ s ⊆ N.Q ⇒ decode N (encode N s) = s: proof
>
```

That finishes the proof.

> [!NOTE]
> Our usage of the Select operator is motivated by wanting a compact
> formulation of encoding/decoding free of algorithmic details. In HOL
> we can simply "pick a suitable bijection" and quickly derive the
> invertibility result needed. It is, however, non-constructive: a
> computable implementation would require a concrete datatype such as
> lists or trees to represent state sets.

> [!NOTE]
> Our usage of Select in this example amounts to a kind of "eliminable
> but convenient" shorthand for some messier reasoning. However the
> Select operator can do much more: the full power of the Axiom of
> Choice is available in HOL in the form of the following axiom:
>
> ```
> SELECT_AX;
> val it = ⊢ ∀P x. P x ⇒ P ($@ P): thm
> ```
>
> Although this may look odd, it can be used to derive more
> conventional presentations. See the Exercises for an example.


## The subset construction

We first establish `enc` and `dec` as abbreviations for `encode N` and
`decode N`, using the following declarations:

```
Overload "enc"[local] = “encode N”
Overload "dec"[local] = “decode N”;
```

The subset construction maps an NFA structure to a DFA structure,
using the encoder to collapse subsets to states and the decoder to
recover subsets from states.

```
Definition nfa_to_dfa_def:
  nfa_to_dfa N : 'a dfa =
    <| Q       := {enc s | s | s ⊆ N.Q};
       Sigma   := N.Sigma;
       delta   := λqs a. enc (Delta N (dec qs) a);
       initial := enc N.initial;
       final   := {enc s | s | s ⊆ N.Q ∧ s ∩ N.final ≠ ∅}
    |>
End
```

Thus the set of states of the constructed DFA is the set of encodings
of all subsets of the NFA state set. The initial state is the encoding
of the initial states of the NFA. The final states are the encodings
of any subsets of the state space of the NFA that have at least one
final state.  Finally, a computation step in the DFA takes the current
state, decodes it to a set of NFA states, runs the NFA `Delta`, and
encodes the result.

## Correctness of subset construction

The key lemma about the subset construction is the following:

```
Theorem main_lemma:
  wf_nfa (N:'a nfa) ⇒
  ∀w qset.
    EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q
    ⇒ dfa_eval (nfa_to_dfa N) (enc qset) w = enc (nfa_eval N qset w)
Proof
  disch_tac >> Induct >>
  rw [nfa_eval_def,dfa_eval_def] >>
  DEP_ASM_REWRITE_TAC [] >>
  DEP_REWRITE_TAC [codec] >>
  simp [Delta_subset]
QED
```

This expresses a commutative diagram, stating that evaluating an NFA
on its input---and encoding the resulting set of states---is equal to
the result of evaluating the DFA constructed from the NFA. The proof
is a quite straightforward induction on the input word `w`.  Things
work out well since the pattern of recursion of both `nfa_eval` and
`dfa_eval` is the same. The initial goal is

```
  wf_nfa N ⇒
  ∀w qset.
    EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒
    dfa_eval (nfa_to_dfa N) (enc qset) w = enc (nfa_eval N qset w)
```

It's important that `qset` be universally quantified since that will be
important in applying the inductive hypothesis. The proof starts by exposing the
variable to induct on (`w`), applying the induction tactic, and simplifying with the
definitions of `dfa_eval` and `nfa_eval`:

```
  disch_tac >> Induct >>
  rw [nfa_eval_def,dfa_eval_def]
```

The base case of the induction gets automatically proved, and we are
left with the inductive case:

```
    0.  wf_nfa N
    1.  ∀qset.
          EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒
          dfa_eval (nfa_to_dfa N) (enc qset) w = enc (nfa_eval N qset w)
    2.  h ∈ N.Sigma
    3.  EVERY (λa. a ∈ N.Sigma) w
    4.  qset ⊆ N.Q
   ------------------------------------
        dfa_eval (nfa_to_dfa N) (enc (Delta N (dec (enc qset)) h)) w =
        enc (nfa_eval N (Delta N qset h) w)
```

It is now time to use the inductive hypothesis (assumption `1`).  The
LHS of it, namely

```
  dfa_eval (nfa_to_dfa N) (enc qset) w
```

matches the LHS of the goal, namely

```
  dfa_eval (nfa_to_dfa N) (enc (Delta N (dec (enc qset)) h)) w
```

by instantiating the quantified variable `qset` with the term
`Delta N(dec (enc qset)) h`. Simplification will handle such
instantiations automatically, but note that assumption `1` has
two side-conditions that must be proved before the rewrite rule
can fire. The first one can be already found in the assumptions,
but the second is more stubborn.

> [!TIP]
> This exemplifies a common proof scenario: an implication in the
> assumptions, or an already-proved lemma, needs to be used in a
> proof, but that is blocked until the antecedents of the implication
> are proved. Sometimes the simplifier can automatically prove such
> side conditions but there will always be cases where automated
> side-condition provers fail. HOL4 provides a suite of *dependent
> rewriting* tactics targeted at this problem: they work by adding the
> side-conditions as new conjuncts in the goal, and thereby allow the
> rewrite rule to be applied while keeping the side-conditions as
> proof obligations.

In order to rewrite with the induction hypothesis (assumption `1`)
we invoke a dependent rewrite tactic

```
  DEP_ASM_REWRITE_TAC []
```

which includes the assumptions of the goal as possible rewrite
rules. This succeeds in rewriting the goal by the IH and returns a
goal that is a conjunction where the first conjunct is the stubborn
side-condition on the IH and the second conjunct is the transformed
goal.

```
    0.  wf_nfa N
    1.  ∀qset.
          EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒
          dfa_eval (nfa_to_dfa N) (enc qset) w = enc (nfa_eval N qset w)
    2.  h ∈ N.Sigma
    3.  EVERY (λa. a ∈ N.Sigma) w
    4.  qset ⊆ N.Q
   ------------------------------------
        Delta N (dec (enc qset)) h ⊆ N.Q ∧
        enc (nfa_eval N (Delta N (dec (enc qset)) h) w) =
        enc (nfa_eval N (Delta N qset h) w)
```

Inspecting this goal, one can see that the second conjunct is *nearly* an
instance of reflexivity. All it would take is for `dec (enc qset)` to
rewrite to `qset`, *i.e.*, simplify with `codec` from
above. In fact `codec` will simplify both conjuncts. So we apply

```
  DEP_REWRITE_TAC [codec]
```

obtaining

```
    0.  wf_nfa N
    1.  ... elided ...
    2.  h ∈ N.Sigma
    3.  EVERY (λa. a ∈ N.Sigma) w
    4.  qset ⊆ N.Q
   ------------------------------------
        (wf_nfa N ∧ qset ⊆ N.Q) ∧ Delta N qset h ⊆ N.Q
```

Now it really only remains to show `Delta qset h ⊆ N.Q.` This raises a
question: *shall I be scruffy or neat*?  A *scruffy* person might
conclude the proof with a brutal but effective use of automation:

```
  gvs [Delta_def, wf_nfa_def, SUBSET_DEF] >> metis_tac[]
```

A *neat* person might separately create a new theorem for this subproof:

```
Theorem Delta_subset:
  wf_nfa N ∧ h ∈ N.Sigma ∧ qset ⊆ N.Q
  ⇒ Delta N qset h ⊆ N.Q
Proof
  rw [SUBSET_DEF,IN_Delta] >>
  metis_tac [wf_nfa_def,SUBSET_DEF]
QED
```

and then use

```
  metis_tac [Delta_subset]
```

to finish the proof. It's a matter of personal preference (we chose
"neat"):

```
metis: r[+0+11]+0+0+0+0+0+0+0+0+0+1+0+1#

Goal proved.
 [.....] ⊢ (wf_nfa N ∧ qset ⊆ N.Q) ∧ Delta N qset h ⊆ N.Q

Goal proved.
 [.....]
⊢ Delta N (dec (enc qset)) h ⊆ N.Q ∧
  enc (nfa_eval N (Delta N (dec (enc qset)) h) w) =
  enc (nfa_eval N (Delta N qset h) w)
val it =
   Initial goal proved.
   ⊢ wf_nfa N ⇒
     ∀w qset.
       EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒
       dfa_eval (nfa_to_dfa N) (enc qset) w = enc (nfa_eval N qset w): proof
```

> [!NOTE]
> The simplifier is powerful enough to handle all the post-induction
> reasoning in this proof. Indeed, the tactic
>
> ```
>  disch_tac >>
>  Induct >>
>  rw [nfa_eval_def, dfa_eval_def, Delta_subset, codec]
> ```
>
> proves `main_lemma`. Notably, the invocations of
> `DEP_ASM_REWRITE_TAC` were, in this case, not needed since the
> simplifier could handle the necessary side-condition proofs.
>
> However, such a revision can be viewed as bad style since it
> collapses three steps: first, expanding the evaluator definitions;
> second, applying the IH; and third, applying `codec`, into one muddy
> ball of chaos that just happens to work. In small proofs, this
> collapsing of separate rewrite stages can be OK, but for larger
> proofs it can result in nigh-impenetrable maintenance problems.

## Language level equivalence

Now we tackle the language-level equivalence. This uses `main_lemma`
but we also need an alternate version where, instead of *encoding* the
results of NFA evaluation, we *decode* the results of DFA evaluation:

```
Theorem main_lemma_alt:
  wf_nfa (N:'a nfa) ∧
  EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q
  ⇒ nfa_eval N qset w = dec (dfa_eval (nfa_to_dfa N) (enc qset) w)
Proof
  strip_tac >>
  drule_all main_lemma >>
  disch_then (mp_tac o Q.AP_TERM ‘dec’) >>
  DEP_REWRITE_TAC [codec] >>
  metis_tac[nfa_eval_states]
QED
```

The proof of `main_lemma_alt` features a sometimes useful pattern of
reasoning, so let's look at it. Our goal is to apply the decoder `dec`
to both the LHS and RHS of `main_lemma` and then simplify. This can be
accomplished, with some effort, by forward inference, but it is higher
level to use tactics, and that is what we will now explain. After
`strip_tac` the goal is

```
    0.  wf_nfa N
    1.  EVERY (λa. a ∈ N.Sigma) w
    2.  qset ⊆ N.Q
   ------------------------------------
        nfa_eval N qset w = dec (dfa_eval (nfa_to_dfa N) (enc qset) w)
```

It is time to apply `main_lemma`. There are many ways to "apply" a
lemma, *e.g.*, by using it to simplify the goal, but here that's not
really possible. Instead we are going to transform the conclusion of
`main_lemma` and use that to solve the goal. First we have to get
`main_lemma` in the context of the tactic proof. The invocation

```
  drule_all main_lemma
```

uses the assumptions of the goal to satisfy the antecedents of `main_lemma`
and puts the conclusion of the theorem as an antecedent to the goal:

```
    0.  wf_nfa N
    1.  EVERY (λa. a ∈ N.Sigma) w
    2.  qset ⊆ N.Q
   ------------------------------------
        dfa_eval (nfa_to_dfa N) (enc qset) w = enc (nfa_eval N qset w) ⇒
        nfa_eval N qset w = dec (dfa_eval (nfa_to_dfa N) (enc qset) w)
```

> [!NOTE]
> This sets up a style of proof where a formula sits as an antecedent
> to the goal and is iteratively manipulated with forward inference
> steps until it becomes useable by other tactics. In this proof style
> (called "theorem continuations" by its inventor Larry Paulson) a
> goal
>
> ```
>     ...
>   ------------------------------------
>     formula ==> A
> ```
>
> will get transformed by inference rule `rule : thm -> thm` to
>
> ```
>      ...
>    ------------------------------------
>      rule (formula) ==> A
> ```
>
> This is accomplished in three steps:
>
> 1. use `ASSUME` to make `formula` into a theorem `formula |- formula`
> 1. apply `rule` to the theorem
> 1. put `rule (formula)` back into its place in the goal
>
> In the guise of SML programming, this is
>
> ```
>   disch_then (mp_tac o rule)
> ```
>
> Consult the documentation for `disch_then` and `mp_tac` for more information.

For our situation, `rule` is instantiated to```Q.AP_TERM `dec`;``` applying

```
  disch_then (mp_tac o Q.AP_TERM `dec`)
```

gives the new goal

```
    0.  wf_nfa N
    1.  EVERY (λa. a ∈ N.Sigma) w
    2.  qset ⊆ N.Q
   ------------------------------------
        dec (dfa_eval (nfa_to_dfa N) (enc qset) w) =
        dec (enc (nfa_eval N qset w)) ⇒
        nfa_eval N qset w = dec (dfa_eval (nfa_to_dfa N) (enc qset) w)
```

and we now have the conclusion of `main_lemma` where the LHS and RHS
have had `dec` applied to them (a valid step since if `x = y` then `f
x = f y`). There is an instance of `dec (enc ...)` in the goal and
it is simplified with

```
  DEP_REWRITE_TAC [codec]
```

yielding

```
    0.  wf_nfa N
    1.  EVERY (λa. a ∈ N.Sigma) w
    2.  qset ⊆ N.Q
   ------------------------------------
        (wf_nfa N ∧ nfa_eval N qset w ⊆ N.Q) ∧
        (dec (dfa_eval (nfa_to_dfa N) (enc qset) w) = nfa_eval N qset w ⇒
         nfa_eval N qset w = dec (dfa_eval (nfa_to_dfa N) (enc qset) w))

```

Invoking the simplifier

```
  simp []
```

will prove our original goal and leave a final proof obligation

```
    0.  wf_nfa N
    1.  EVERY (λa. a ∈ N.Sigma) w
    2.  qset ⊆ N.Q
   ------------------------------------
        nfa_eval N qset w ⊆ N.Q
```

There is an easy lemma, named `nfa_eval_states`, proving this in the
source. In fact, we can `undo` the call to `simp` and finish the proof
with

```
  metis_tac [nfa_eval_states]
```

We have finished `main_lemma_alt`.

### `nfa_to_dfa_correct`

Language equivalence is an exercise in expanding definitions and
applying the two versions of `main_lemma`. In full this looks like:

```
Theorem nfa_to_dfa_correct:
  wf_nfa N
  ⇒ ∀w. w ∈ dfa_lang (nfa_to_dfa N) <=> w ∈ nfa_lang N
Proof
  rw [dfa_lang_def,nfa_lang_def] >>
  rw [EQ_IMP_THM,PULL_EXISTS] THENL
  [DEP_ONCE_REWRITE_TAC [main_lemma_alt],
   DEP_ONCE_REWRITE_TAC [main_lemma]] >>
  conj_tac >>~-  (* 4 subgoals, 2 identical *)
    ([‘wf_nfa N ∧ _’],
     simp [IN_DEF] >> metis_tac [wf_nfa_def])
  >- (simp [] >> DEP_REWRITE_TAC [codec] >> simp [])
  >- (irule_at Any EQ_REFL >> simp [] >>
      irule nfa_eval_states >> simp [] >>
      reverse conj_tac >- metis_tac [wf_nfa_def] >>
      simp [IN_DEF, SF ETA_ss])
QED
```

The proof breaks the goal down into a number of cases, some of which
have identical proofs. Writing a tactic that is similar or identical
for each case would be tedious and morally repugnant, especially for
large verifications. (On the other hand, such explicitness *can* be a
virtue in maintaining proofs done with complex tactics.)

So, let's have a look. The initial goal is

```
  wf_nfa N ⇒ ∀w. w ∈ dfa_lang (nfa_to_dfa N) <=> w ∈ nfa_lang N
```
and invoking

```
  rw [dfa_lang_def,nfa_lang_def] >>
  rw [EQ_IMP_THM,PULL_EXISTS]
```

expands the definitions of *language* for DFAs and NFAs, then breaks
the equivalence into implications and normalizes the resulting goals:

```
    0.  wf_nfa N
    1.  EVERY N.Sigma w
    2.  nfa_eval N N.initial w ∩ N.final ≠ ∅
   ------------------------------------
        ∃s. dfa_eval (nfa_to_dfa N) (enc N.initial) w = enc s ∧ s ⊆ N.Q ∧
            s ∩ N.final ≠ ∅

    0.  wf_nfa N
    1.  EVERY N.Sigma w
    2.  dfa_eval (nfa_to_dfa N) (enc N.initial) w = enc s
    3.  s ⊆ N.Q
    4.  s ∩ N.final ≠ ∅
   ------------------------------------
        nfa_eval N N.initial w ∩ N.final ≠ ∅
```

In the first (bottom) case, we have a conclusion about NFA evaluation,
and we'd like to rewrite it with `main_lemma_alt`.  Contrarily, in the
second (top) case, we have a conclusion about DFA evaluation, and we'd
like to rewrite it with `main_lemma`. But, as is common, these
rewrites both have slightly stubborn side-conditions and dependent
rewriting becomes the weapon of choice.

We restart the proof

```
  restart()
```

and apply tailored dependent rewriting in each branch, using only the
single relevant rewrite for each branch. This is done via `THENL`.

> [!NOTE]
> `THENL` is an infix *tactical* that sequences tactics. It is similar
> to `THEN` (infix, typically written `>>`) except that `tac THENL
> [tac_1, ..., tac_n]` requires that `tac` creates
> *n* subgoals, and applies `tac_i` to subgoal `i`.

We accordingly use `THENL` to rewrite with `main_lemma_alt` in the
first branch and `main_lemma` in the second. Each dependent rewrite
invocation will create a conjunction and we may as well break those up
too, hence we append a `conj_tac`

```
  rw [dfa_lang_def,nfa_lang_def] >>
  rw [EQ_IMP_THM,PULL_EXISTS] THENL
  [DEP_ONCE_REWRITE_TAC [main_lemma_alt],
   DEP_ONCE_REWRITE_TAC [GSYM main_lemma]] >> conj_tac
```

which results in

```
    0.  wf_nfa N
    1.  EVERY N.Sigma w
    2.  nfa_eval N N.initial w ∩ N.final ≠ ∅
   ------------------------------------
        ∃s. enc (nfa_eval N N.initial w) = enc s ∧ s ⊆ N.Q ∧ s ∩ N.final ≠ ∅

    0.  wf_nfa N
    1.  EVERY N.Sigma w
    2.  nfa_eval N N.initial w ∩ N.final ≠ ∅
   ------------------------------------
        wf_nfa N ∧ EVERY (λa. a ∈ N.Sigma) w ∧ N.initial ⊆ N.Q

    0.  wf_nfa N
    1.  EVERY N.Sigma w
    2.  dfa_eval (nfa_to_dfa N) (enc N.initial) w = enc s
    3.  s ⊆ N.Q
    4.  s ∩ N.final ≠ ∅
   ------------------------------------
        dec (dfa_eval (nfa_to_dfa N) (enc N.initial) w) ∩ N.final ≠ ∅

    0.  wf_nfa N
    1.  EVERY N.Sigma w
    2.  dfa_eval (nfa_to_dfa N) (enc N.initial) w = enc s
    3.  s ⊆ N.Q
    4.  s ∩ N.final ≠ ∅
   ------------------------------------
        wf_nfa N ∧ EVERY (λa. a ∈ N.Sigma) w ∧ N.initial ⊆ N.Q
```

Inspecting the result, we see that the rewrites have indeed taken
place. However, every second subgoal is the same:

```
  wf_nfa N ∧ EVERY (λa. a ∈ N.Sigma) w ∧ N.initial ⊆ N.Q
```

It seems that we will have to write the same tactic twice to prove
these.  It's an admittedly simple sub-proof, but annoying, and such
repetitions become aggravating in large verifications. To address
this, there are tactics that use patterns to control the order in
which goals are tackled. The one we will use is `tac1 >>~- (pats,
tac2)`, where ```pats = [p1,...,pn]``` is a list of quotations
expressing patterns. The idea is that subgoals arising from the
application of tactic `tac1` that match `pats` will all have `tac2`
applied to them (and `tac2` should prove all of those subgoals
completely).

For our example, we will use the pattern ``` `wf_nfa N /\ _` ```. Thus
the tactic invocation under construction is

```
  tac1 >>~- ([`wf_nfa N /\ _`], tac2)
```

and we already have `tac1` (the tactic creating the 4 subgoals). It
remains to determine `tac2`. Fortunately one of the instances of the
pattern is the top goal:

```
    0.  wf_nfa N
    1.  EVERY N.Sigma w
    2.  dfa_eval (nfa_to_dfa N) (enc N.initial) w = enc s
    3.  s ⊆ N.Q
    4.  s ∩ N.final ≠ ∅
   ------------------------------------
        wf_nfa N ∧ EVERY (λa. a ∈ N.Sigma) w ∧ N.initial ⊆ N.Q
```

This isn't hard to prove:

```
  simp [IN_DEF] >> metis_tac [wf_nfa_def]
```

and so our compound tactic under construction is the following:

```
  rw [dfa_lang_def,nfa_lang_def] >>
  rw [EQ_IMP_THM,PULL_EXISTS] THENL
  [DEP_ONCE_REWRITE_TAC [main_lemma_alt],
   DEP_ONCE_REWRITE_TAC [main_lemma]] >>
  conj_tac >>~-  (* 4 subgoals, 2 identical *)
    ([‘wf_nfa N ∧ _’],
     simp [IN_DEF] >> metis_tac [wf_nfa_def])
```

Restarting the proof and applying this entire tactic, we may infer
that the subgoals matching the pattern are proved because we are left
with the final two goals:

```
    0.  wf_nfa N
    1.  EVERY N.Sigma w
    2.  nfa_eval N N.initial w ∩ N.final ≠ ∅
   ------------------------------------
        ∃s. enc (nfa_eval N N.initial w) = enc s ∧ s ⊆ N.Q ∧ s ∩ N.final ≠ ∅

    0.  wf_nfa N
    1.  EVERY N.Sigma w
    2.  dfa_eval (nfa_to_dfa N) (enc N.initial) w = enc s
    3.  s ⊆ N.Q
    4.  s ∩ N.final ≠ ∅
   ------------------------------------
        dec (dfa_eval (nfa_to_dfa N) (enc N.initial) w) ∩ N.final ≠ ∅
```

The bottom-most goal (the top goal on the stack!) can be simplified
from the assumptions, which a bit of inspection reveals will create an
opportunity for `codec` again. Putting this together into

```
  simp [] >> DEP_REWRITE_TAC [codec]
```

gives a trivial goal

```
    0.  wf_nfa N
    1.  EVERY N.Sigma w
    2.  dfa_eval (nfa_to_dfa N) (enc N.initial) w = enc s
    3.  s ⊆ N.Q
    4.  s ∩ N.final ≠ ∅
   ------------------------------------
        (wf_nfa N ∧ s ⊆ N.Q) ∧ s ∩ N.final ≠ ∅
```

so we can tack on another `simp []` to obtain the full tactic for
solving this goal:

```
  (simp [] >> DEP_REWRITE_TAC [codec] >> simp [])
```

This leaves the last of the four goals:

```
    0.  wf_nfa N
    1.  EVERY N.Sigma w
    2.  nfa_eval N N.initial w ∩ N.final ≠ ∅
   ------------------------------------
        ∃s. enc (nfa_eval N N.initial w) = enc s ∧ s ⊆ N.Q ∧ s ∩ N.final ≠ ∅
```

Proving existential goals can always be done by providing explicit
witnesses, via `qexists_tac` for example, but there are also powerful
alternatives available. For example, the witness for `s` may
be found from either (A) assumption 2 or (B) by reflexivity from the first
conjunct under the existential. The entrypoint for both of these proof
steps is `irule_at`.

1. Instantiating from assumption 2 is done via

   ```
     first_assum (irule_at Any)
   ```

   which says, roughly, "find the first assumption that first order
   unifies with one of the conjuncts underneath the existential and use
   that substitution to provide the existential witness, then remove
   that conjunct". This results in

   ```
       0.  wf_nfa N
       1.  EVERY N.Sigma w
       2.  nfa_eval N N.initial w ∩ N.final ≠ ∅
      ------------------------------------
           enc (nfa_eval N N.initial w) = enc (nfa_eval N N.initial w) ∧
           nfa_eval N N.initial w ⊆ N.Q
   ```

2. Instantiating from the first conjunct under the existential is written as

   ```
     irule_at Any EQ_REFL
   ```

   which says, roughly, "find the first conjunct under the existential
   that is an instance of reflexivity, then use that substitution to
   provide the existential witness, then remove the instantiated
   conjunct". This yields

   ```
       0.  wf_nfa N
       1.  EVERY N.Sigma w
       2.  nfa_eval N N.initial w ∩ N.final ≠ ∅
      ------------------------------------
           nfa_eval N N.initial w ⊆ N.Q ∧ nfa_eval N N.initial w ∩ N.final ≠ ∅
   ```

In either case, after simplification, one is left with the goal

```
    0.  wf_nfa N
    1.  EVERY N.Sigma w
    2.  nfa_eval N N.initial w ∩ N.final ≠ ∅
   ------------------------------------
        nfa_eval N N.initial w ⊆ N.Q
```

and this is seemingly easily proved with `nfa_eval_states`. We are
basically done. However, frustratingly,

```
  metis_tac [nfa_eval_states,wf_nfa_def]
````

will fail without providing a reason. To debug we backward chain
with `irule`:

```
  irule nfa_eval_states
```

which instantiates the theorem and replaces the goal of proving the
conclusion of the theorem by the goal of proving the antecedents:

```
    0.  wf_nfa N
    1.  EVERY N.Sigma w
    2.  nfa_eval N N.initial w ∩ N.final ≠ ∅
   ------------------------------------
        wf_nfa N ∧ EVERY (λa. a ∈ N.Sigma) w ∧ N.initial ⊆ N.Q
```

The first conjunct of the goal is in the assumptions and the third
conjunct is part of `wf_nfa_def`, which leaves the second conjunct

```
  EVERY (λa. a ∈ N.Sigma) w
```

as the culprit: assumption 1 ought to simplify it, but won't. The
problem is one of HOL's small annoyances: since predicates are used to
model sets in HOL the notion of element `a` being in set `P` can be
written either as `P a` or as `a ∈ P`: indeed it is trivial to prove
`⊢ a ∈ P ⇔ P a`. One might think, therefore, that simplifying with
this would solve the problem. But no:

```
  simp [IN_DEF]
```

yields

```
  EVERY (λa. N.Sigma a) w
```

and assumption 1 still refuses to fulfill its destiny! HOL provides an
η-reduction rule that should help

```
> ETA_THM;
val it = ⊢ ∀M. (λx. M x) = M: thm
```

but simplifying with it results in no change, for obscure reasons in
the design of the simplifier. The rewrite *can* be made to fire by
using a more primitive rewriter, but it can also be accomplished
within the standard simplifier by including a special-purpose *simpset
fragment* `ETA_ss`:

```
> ETA_ss;
val it =
   Simplification set fragment: ETA
   Conversions:
      ETA_CONV (eta reduction), keyed on pattern  “f (λx. g x)”
      ETA_CONV (eta reduction), keyed on pattern  “λx y. f x y”: ssfrag
```

Note that the first pattern in the listed conversions covers our
case. In order to add `ETA_ss` to the simplifier, we need to wrap it
with the `SF` function. In summary

```
  simp [IN_DEF, SF ETA_ss]
```

will prove the goal

```
  EVERY (λa. a ∈ N.Sigma) w
```

and complete the proof.

> [!TIP]
> The best way to avoid this scenario is to exercise consistent
> set-theory notation, especially with respect to ∈. If we had
> expressed `nfa_eval_states` as
>
> ```
>   wf_nfa N ⇒ ∀w qset. EVERY N.Sigma w ∧ qset ⊆ N.Q ⇒ nfa_eval N qset w ⊆ N.Q
> ```
>
> there would not have been any issues. Still, one sometimes runs
> into this problem, and it's important to know how to work around it.
