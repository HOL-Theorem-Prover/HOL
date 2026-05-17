# NFA to DFA

A classic result of computer science theory is that the languages
recognized by DFAs are equal to the languages recognized by NFAs. This
was first proved by Michael Rabin and Dana Scott in *Finite automata
and their decision problems*, IBM Journal of Research and Development
3(2), 114–125 (1959).  The *subset construction* forms the backbone of
their proof; it works by mapping an NFA into an "equivalent" DFA.

The key insight is to make a state of the constructed DFA embody the
states the NFA could possibly be in at a particular stage of
processing the input word. The construction is conceptually appealing
but it raises a technical problem: how to somehow arrange
that the DFA state (a thing of type `:num`) *is* a set of NFA states
(a thing of type `:num -> bool`). This cannot be accepted by the type
system of HOL.

## Encoding subsets

Our solution to the problem is to adopt a bijective mapping that
encodes sets of NFA states as natural numbers. The DFA is then
constructed so that its states are encodings of sets of NFA
states. Thus we want two functions

```
  encode : num set -> num
  decode : num -> num set
```

such that `decode (encode s) = s`. There is a variety of ways to
achieve this; we choose one that highlights a distinctive aspect of
the HOL logic, namely the *Hilbert Choice* operator.

The Hilbert choice operator, written `@x. P x`, is syntax for
expressing the notion "pick an *x* having property *P*".  (The Hilbert
choice operator is also called the *Select* operator or even the
*Indefinite description* operator.) The Choice operator is a way to
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
> Our usage of Hilbert choice in this example amounts to a
> kind of "eliminable but convenient" shorthand for some messier
> reasoning. However the Choice operator can do much more: the full
> power of the Axiom of Choice is available in HOL in the form of
> the following axiom:
>
> ```
> SELECT_AX;
> val it = ⊢ ∀P x. P x ⇒ P ($@ P): thm
> ```
>
> Although this may look odd, it can be used to derive more
> conventional presentations. See the Exercises for an example.


### Abbreviating encode/decode

We establish `enc` and `dec` as abbreviations for `encode N` and
`decode N`, using the following declarations:

```
Overload "enc"[local] = “encode N”
Overload "dec"[local] = “decode N”;
```


## The subset construction

The construction maps an NFA structure to a DFA structure, using the
encoder to collapse subsets to states and the decoder to recover
subsets from states.

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
   EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒
   enc (nfa_eval N qset w) = dfa_eval (nfa_to_dfa N) (enc qset) w
Proof
  disch_tac >> Induct >> rw [nfa_eval_def]
  >- rw [dfa_eval_def] >>
  simp [dfa_eval_def] >>
  DEP_ASM_REWRITE_TAC [] >> conj_tac
  >- metis_tac [Delta_subset] >>
  DEP_REWRITE_TAC [codec] >> simp []
QED
```

This expresses a commutative diagram, stating that evaluating an NFA
on its input---and encoding the set of states of the resulting
fringe---is equal to the result of evaluating the DFA constructed from
the NFA. The proof is a quite straightforward induction on the input
word `w`.  Things work out nicely since the pattern of recursion of
both `nfa_eval` and `dfa_eval` is the same. The initial goal is

```
  wf_nfa (N:'a nfa) ⇒
    ∀w qset.
     EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒
     enc (nfa_eval N qset w) = dfa_eval (nfa_to_dfa N) (enc qset) w
```

It's important that `qset` be universally quantified since that will be
important in applying the inductive hypothesis. The proof starts by exposing the
variable to induct on (`w`), applying the induction tactic, and simplifying with the
definition of `nfa_eval`:

```
  disch_tac >> Induct >> rw [nfa_eval_def]
```

which results in two subgoals:

```
    0.  wf_nfa N
    1.  ∀qset.
          EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒
          enc (nfa_eval N qset w) = dfa_eval (nfa_to_dfa N) (enc qset) w
    2.  h ∈ N.Sigma
    3.  EVERY (λa. a ∈ N.Sigma) w
    4.  qset ⊆ N.Q
   ------------------------------------
        enc (nfa_eval N (Delta N qset h) w) =
        dfa_eval (nfa_to_dfa N) (enc qset) (h::w)

    0.  wf_nfa N
    1.  qset ⊆ N.Q
   ------------------------------------
        enc qset = dfa_eval (nfa_to_dfa N) (enc qset) []
```

The first subgoal is the base case of the induction. It has an
application of `dfa_eval` that obviously should be reduced. Doing so

```
  rw [dfa_eval_def]
```

solves the subgoal and leaves the second subgoal; this is the
inductive step of the proof:

```
    0.  wf_nfa N
    1.  ∀qset.
          EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒
          enc (nfa_eval N qset w) = dfa_eval (nfa_to_dfa N) (enc qset) w
    2.  h ∈ N.Sigma
    3.  EVERY (λa. a ∈ N.Sigma) w
    4.  qset ⊆ N.Q
   ------------------------------------
        enc (nfa_eval N (Delta N qset h) w) =
        dfa_eval (nfa_to_dfa N) (enc qset) (h::w)
```

We should again reduce the `dfa_eval` expression:

```
  simp [dfa_eval_def]
```

which gives a clear picture of what is needed:

```
    0.  wf_nfa N
    1.  ∀qset.
          EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒
          enc (nfa_eval N qset w) = dfa_eval (nfa_to_dfa N) (enc qset) w
    2.  h ∈ N.Sigma
    3.  EVERY (λa. a ∈ N.Sigma) w
    4.  qset ⊆ N.Q
   ------------------------------------
        enc (nfa_eval N (Delta N qset h) w) =
        dfa_eval (nfa_to_dfa N) (enc (Delta N (dec (enc qset)) h)) w
```

It is now time to use the inductive hypothesis (assumption `1`).  The
LHS of it, namely

```
  enc (nfa_eval N qset w)
```

matches the LHS of the goal, namely

```
enc (nfa_eval N (Delta N qset h) w)
```

by instantiating the quantified variable `qset` with the term `Delta N
qset h`. Simplification will handle such instantiations automatically,
but note that assumption `1` has two side-conditions that must be
proved before the rewrite rule can fire. The first one can be already
found in the assumptions, but the second is more stubborn.

> [!NOTE]
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
goal. We split these

```
  conj_tac
```

which gives

```
    0.  wf_nfa N
    1.  ∀qset.
          EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒
          enc (nfa_eval N qset w) = dfa_eval (nfa_to_dfa N) (enc qset) w
    2.  h ∈ N.Sigma
    3.  EVERY (λa. a ∈ N.Sigma) w
    4.  qset ⊆ N.Q
   ------------------------------------
        dfa_eval (nfa_to_dfa N) (enc (Delta N qset h)) w =
        dfa_eval (nfa_to_dfa N) (enc (Delta N (dec (enc qset)) h)) w

    0.  wf_nfa N
    1.  ∀qset.
          EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒
          enc (nfa_eval N qset w) = dfa_eval (nfa_to_dfa N) (enc qset) w
    2.  h ∈ N.Sigma
    3.  EVERY (λa. a ∈ N.Sigma) w
    4.  qset ⊆ N.Q
   ------------------------------------
        Delta N qset h ⊆ N.Q
```

The bottom goal comprises the remaining side-condition of the IH. We
are now faced with a question: *shall I be scruffy or neat*?  A *neat*
person might create a new named theorem for this goal and cleanly
place each proof step on a separate line, as in

```
Theorem Delta_subset:
  wf_nfa N ∧ h ∈ N.Sigma ∧ qset ⊆ N.Q ⇒ Delta N qset h ⊆ N.Q
Proof
  rw [Delta_def] >>
  rw [BIGUNION_SUBSET] >>
  gvs [wf_nfa_def] >>
  first_x_assum irule >>
  metis_tac [SUBSET_DEF]
QED
```

and then use

```
  metis_tac [Delta_subset]
```

to prove the goal. Alternatively, a *scruffy* might inline the proof
with a brutal but effective use of automation:

```
  gvs [Delta_def, wf_nfa_def, SUBSET_DEF] >> metis_tac[]
```

It's a matter of personal preference. (We chose "neat" for this
proof.) Now the goal

```
    0.  wf_nfa N
    1.  ∀qset.
          EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒
          enc (nfa_eval N qset w) = dfa_eval (nfa_to_dfa N) (enc qset) w
    2.  h ∈ N.Sigma
    3.  EVERY (λa. a ∈ N.Sigma) w
    4.  qset ⊆ N.Q
   ------------------------------------
        dfa_eval (nfa_to_dfa N) (enc (Delta N qset h)) w =
        dfa_eval (nfa_to_dfa N) (enc (Delta N (dec (enc qset)) h)) w
```

remains. This is an equality with a great deal of repeated syntax on each side. In such cases
`cong_tac : int option -> tactic` can help expose the core problem to be dealt with.
Invoking

```
  cong_tac NONE
```

means "throw away common syntax as much as possible" and yields the goal

```
    0.  wf_nfa N
    1.  ∀qset.
          EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒
          enc (nfa_eval N qset w) = dfa_eval (nfa_to_dfa N) (enc qset) w
    2.  h ∈ N.Sigma
    3.  EVERY (λa. a ∈ N.Sigma) w
    4.  qset ⊆ N.Q
   ------------------------------------
        qset = dec (enc qset)
```

Now is the time to finally apply `codec`. With the abbreviating
overloads imposed above, this renders as

```
> codec;
val it = ⊢ wf_nfa N ∧ s ⊆ N.Q ⇒ dec (enc s) = s: thm
```

and

```
   simp [codec]
```

is able to prove the side-conditions and prove the goal, finishing the
proof.

```
Goal proved.
 [..] ⊢ qset = dec (enc qset)

  .
  .
  .
val it =
   Initial goal proved.
   ⊢ wf_nfa N ⇒
     ∀w qset.
       EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒
       enc (nfa_eval N qset w) = dfa_eval (nfa_to_dfa N) (enc qset) w: proof
```

## Packaging up the proof


## Language level equivalence


The `main_lemma` is used in the proof of language-level equivalence,
but we will also need a tweaked version where, instead of *encoding*
the results of NFA evaluation, we *decode* the results of DFA
evaluation: This is obtained by applying the decoder to both the LHS
and RHS of `main_lemma` and simplifying.

```
Theorem main_lemma_alt:
  wf_nfa (N:'a nfa) ∧
  EVERY (λa. a ∈ N.Sigma) w ∧
  qset ⊆ N.Q ⇒
  nfa_eval N qset w = dec (dfa_eval (nfa_to_dfa N) (enc qset) w)
Proof
  strip_tac >> drule_all main_lemma >>
  disch_then (mp_tac o Q.AP_TERM ‘dec’) >>
  DEP_REWRITE_TAC [codec] >>
  metis_tac[nfa_eval_states]
QED
```

With `main_lemma_alt` in hand, language-level correctness is an
exercise in expanding definitions and applying the two versions of
`main_lemma`:

```
Theorem nfa_to_dfa_correct:
  wf_nfa N
  ⇒ ∀w. w ∈ dfa_lang (nfa_to_dfa N) <=> w ∈ nfa_lang N
Proof
  rw [dfa_lang_def,nfa_lang_def] >>
  rw [EQ_IMP_THM,PULL_EXISTS] THENL
  [DEP_ONCE_REWRITE_TAC [main_lemma_alt],
   DEP_ONCE_REWRITE_TAC [GSYM main_lemma]] >>
  conj_tac >>~-
    ([‘wf_nfa N ∧ _’],
     simp [IN_DEF] >> metis_tac [wf_nfa_def])
  >- (simp [] >> DEP_REWRITE_TAC [codec] >> simp [])
  >- (irule_at Any EQ_REFL >> simp [] >>
      irule nfa_eval_states >>
      simp [SF ETA_ss,IN_DEF] >>
      metis_tac [wf_nfa_def])
QED
```

The proof breaks the goal down into a number of cases, some of which
have identical proofs. Writing a tactic that is similar or identical
for each case would be tedious and morally repugnant. (On the other
hand, such explicitness *can* be a virtue in maintaining proofs done
with complex tactics.)

So, let's have a look. The initial goal is

```
  wf_nfa N
  ⇒ ∀w. w ∈ dfa_lang (nfa_to_dfa N) <=> w ∈ nfa_lang N

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

In the first (bottom) case, we have an assumption about DFA evaluation
and a conclusion about NFA evaluation, so we'd like to rewrite the
conclusion with `main_lemma_alt`.  Contrarily, in the second (top)
case, we have an assumption about NFA evaluation and a conclusion
about DFA evaluation, and we'd like to rewrite the conclusion with
`main_lemma` (with LHS and RHS swapped). But, as is common, these both
have slightly stubborn side-conditions and so we would like to use
dependent rewriting.