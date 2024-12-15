---
lang: en-UK
title: HOL4 tactic cheatsheet
header-includes:
  - <link rel="preconnect" href="https://fonts.gstatic.com">
  - <link href="https://fonts.googleapis.com/css2?family=Noto+Sans:ital,wght@0,400;0,700;1,400;1,700&family=Roboto+Slab:wght@400&family=Fira+Code:wght@500&display=swap" rel="stylesheet">
---

*Adapted from [Magnus Myreen](http://www.cse.chalmers.se/~myreen/)'s [cheatsheet](http://sange.fi/~magnus/cheatsheet.txt).*
*See also [Arve Gengelbach](https://user.it.uu.se/~arvge836/)'s [tips and tricks](https://user.it.uu.se/~arvge836/holtactics.html).*

## Preliminaries

  - Join the `#hol` channel on the [CakeML Discord](https://discord.gg/a8UUs6Ce6m).

  - Learn how to interact with HOL4 using the [documentation](https://hol-theorem-prover.org/#doc).
    - For Emacs, the [short guide](https://hol-theorem-prover.org/HOL-interaction.pdf) or [complete documentation](https://hol-theorem-prover.org/hol-mode.html).
    - For Vim, the [plugin documentation](https://github.com/HOL-Theorem-Prover/HOL/blob/master/tools/editor-modes/vim/README.md).
      At first, you should use the [`vimhol.sh`](https://github.com/HOL-Theorem-Prover/HOL/blob/master/tools/editor-modes/vim/README.md#vimholsh-script) script to run side-by-side Vim and HOL4 using `tmux`.

  - Add the following to your `.hol-config.sml` (in your home directory):
    ```
    val m = Hol_pp.print_apropos;
    val f = Hol_pp.print_find;
    ```
    This allows you to use the following in your HOL4 REPL:
    - <code>m &grave;&grave;<i>pattern</i>&grave;&grave;</code> to search for theorems with subterms matching the supplied pattern.
    - <code>f "<i>string</i>"</code> to search for theorems with names matching the supplied string.

  - You can also add the following if you wish:
    ```
    local
      val pp = print o Hol_pp.data_list_to_string;
    in
      fun ff x y = DB.find y    |> DB.find_in x    |> pp;
      fun mm x y = DB.apropos y |> DB.apropos_in x |> pp;
      fun fm x y = DB.apropos y |> DB.find_in x    |> pp;
      fun mf x y = DB.find y    |> DB.apropos_in x |> pp;
    end;
    ```
    These functions combine the functionality of `m` and `f` above, allowing you to nest two searches.

  - Use <code>help "<i>string</i>"</code> in the HOL4 REPL to examine documentation for ML-level identifiers.

  - Bookmark the [HOL4 online helpdocs](https://hol-theorem-prover.org/kananaskis-14-helpdocs/help/HOLindex.html), for quick access to interactive documentation.
    This is particularly useful for discovering useful definitions in theories.

  - You can also search for constants by type, using <code>find_consts &grave;&grave;:<i>type</i>&grave;&grave;</code>.

  - Be sure to `open HolKernel boolLib bossLib BasicProvers dep_rewrite` interactively.
    Otherwise, some of the tactics below may not be in scope.

  - Remember that HOL4 exposes various useful ML bindings, including:
    - `f o g` - function composition
    - `x |> f` - function application (i.e. `f x`), useful for chaining
    - `f $ g x` - right-associative function application (i.e. `f (g x)`, as in Haskell)


## Rewriting

HOL4 has a powerful rewriting engine, and the cleanest proofs let it do the heavy lifting.
Note that a stateful set of rewrites is maintained by HOL4 - the *stateful simpset*.


### General purpose tactics

<code>simp[<i>theorems</i>]</code>
: Simplifies the goal using current assumptions, the stateful simpset, and decision procedures for the natural numbers.

<code>fs[<i>theorems</i>]</code>
: Like `simp`, but also uses newer assumptions to rewrite older ones.

<code>rfs[<i>theorems</i>]</code>
: Like `fs`, but reversed: uses older assumptions to rewrite newer ones.

<code>gs[<i>theorems</i>]</code>
: Effectively repeats `fs` and `rfs` until no further change.

<code>gvs[<i>theorems</i>]</code>
: Like `gs`, but also uses substitution to eliminate assumptions concerning equalities on variables.

<code>rw[<i>theorems</i>]</code>
: Like `simp`, but also deconstructs the goal (stripping `∀` and `==>`, and splitting conjuncts into subgoals)

<code>DEP_REWRITE_TAC[<i>theorems</i>]</code>
: Rewrites the goal using the supplied dependent rewrites, introducing dependencies as conjuncts in the goal.
  For example, given a goal `P` and a rewrite `thm = ⊢ R ==> P = Q`, `DEP_REWRITE_TAC[thm]` will transform the goal into `R /\ Q`.
  `DEP_ASM_REWRITE_TAC` is a variant which additionally uses the assumptions as rewrites.
  Note that this can loop more often than other rewriting tactics.


### More fine-grained tactics

In some cases, the general purpose tactics above do too much simplification, or can loop.
Instead, there are more precise tactics we can use.

<code>pure_rewrite_tac[<i>theorems</i>]</code>
: Rewrites the goal using only the supplied theorems (i.e. no stateful simpset rewrites).

<code>{,asm_}rewrite_tac[<i>theorems</i>]</code>
: Like `pure_rewrite_tac`, but also uses basic boolean expression rewrites.
  The `asm_rewrite_tac` variant additionally uses the assumptions as potential rewrites.

<code>once_{,asm_}rewrite_tac[<i>theorems</i>]</code>
: Like `{,asm_}rewrite_tac`, but performs a top-down descent of the goal and rewrites at most once per subtree.

<code>DEP_ONCE_REWRITE_TAC[<i>theorems</i>]</code>
: Is to `DEP_REWRITE_TAC` what `once_rewrite_tac` is to `rewrite_tac`.
  `DEP_ONCE_ASM_REWRITE_TAC` is analogous to `once_asm_rewrite_tac`.


#### Conversions

If these are still too blunt, we can use *conversions* to carry out surgical rewrites.
Conversions are functions of type `term -> thm`, such that applying a conversion to a term `t` produces a theorem `⊢ t = t'`.
These can be converted into tactics using <code>CONV_TAC <i>conversion</i></code>.
There are many conversions and conversion combinators - an exhaustive list can be found in the HOL4 documentation, mostly listed under the `Conv` structure.
Good starting points are `SCONV`, `REWRITE_CONV`, `THENC`, `RAND_CONV`, `RATOR_CONV`, `LHS_CONV`, `RHS_CONV`, `QCHANGED_CONV`, `DEPTH_CONV`, `PAT_CONV`, and `PATH_CONV`.


### Rewrite modifiers
These are used when rewriting: they modify the rewrite behaviour of the theorem to which they are applied.

<code>Once <i>theorem</i></code>
: Uses the supplied theorem at most once when rewriting.

<code>Ntimes <i>theorem int</i></code>
: Uses the supplied theorem at most the given number of times when rewriting.

<code>Excl <i>"theorem_name"</i></code><br><code>Excl <i>"conversion_name"</i></code>
: Do not use the supplied theorem/conversion when rewriting.
  This allows temporary exclusion of theorems/conversions from the stateful simpset.

<code>Simp{L,R}HS <i>theorem</i></code>
: Uses the supplied theorem to simplify on the left-/right-hand side of equalities.

<code>Req{0,D} <i>theorem</i></code>
: Requires the supplied theorem to be used a number of times, by checking the number of subterms matching the LHS of the rewrite *after* simplification.
  `Req0` requires no matching subterms after simplification, `ReqD` requires the number to have strictly decreased - otherwise, an exception is thrown.
  This is most useful for ensuring that conditional rewrites have fired.

<br>
Also commonly used when rewriting are:

<code>GSYM <i>theorem</i></code>
: Flips equalities in the conclusion of the theorem.
  This works even when the equality is nested below implications and/or `∀`-quantification.

<code>iff{LR,RL} <i>theorem</i></code>
: Turns a bi-implication into an implication, going left-to-right or right-to-left respectively.

<code>cj <i>n</i> <i>theorem</i></code>
: Returns the <code><i>n</i></code>th conjunct of the theorem, handling universal quantifiers and implications.
  For example, for `thm = ⊢ ∀ P Q R . P ==> Q /\ R`, `cj 2 thm` gives `⊢ ∀ P R . P ==> R)`.
  **NB** indexing begins at `1`.

<code>SRULE [<i>rewrites</i>] <i>theorem</i></code>
: Uses the stateful simpset and supplied rewrites to rewrite the theorem.

<code>Cong <i>theorem</i></code>
: Uses the supplied theorem as a *congruence rule* instead of a rewrite.
  Congruence rules tell the simplifier how to traverse terms, so they can be useful for rewriting within subterms.
  For example,
    using `Cong AND_CONG` allows use of each conjunct in a conjunction to rewrite the others; and
    the goal `(∀ e. MEM e l ==> f e = g e) ==> h (MAP f l) = h (MAP g l)` is solved by `simp[Cong MAP_CONG]`.

<code>oneline <i>theorem</i></code>
: Converts a definition with multiple clauses into a single clause, turning pattern-matches into `case`-expressions.
  For example, `oneline listTheory.MAP` gives `⊢ MAP f v = case v of [] => [] | h::t => f h::MAP f t`.

<code>lambdify <i>theorem</i></code>
: Converts a definition of the form `⊢ ∀ x y z. f x y z = ...` into one of the form `⊢ f = (λx y z. ...)`.

<br>
Note that the above are termed *rules* - these transform theorems to other theorems, allowing the above to be combined (e.g. `simp[Once $ GSYM thm]`).
There are many other useful rules - see the HOL4 documentation for more details.

In some cases we may wish to use a set of rewrites for simplification.
One way to do this is to use the `SF` modifier in our list of rewrites, e.g. `simp[SF CONJ_ss]`.

<code>SF <i>&lt;simpset fragment></i></code>
: Turns the simpset fragment into a theorem encapsulating its rewrite behaviour, which can be passed in a list of rewrites.

<br>
This is most useful for certain simpset fragments:

`CONJ_ss`
: Rewrites over conjuncts.
  This can deduplicate conjuncts, and use each conjunct to help simplify the others.
  For example, the goal `x = SUC n /\ if x = 0 then P else Q` transforms to `x = SUC n /\ Q` using `simp[SF CONJ_ss]`.

`SFY_ss`
: Rewrites to prove simple `∃`-quantified goals using instantiations from assumptions/rewrites.

`ETA_ss`
: Rewrites to remove eta-expansion.

`DNF_ss`
: Rewrites to convert to disjunctive normal form.

<br>
Conversely, `ExclSF` is like `Excl` above, but can be used to *exclude* a set of rewrites.

<code>ExclSF <i>"simpset fragment name"</i></code>
: Do not use the supplied simpset fragment when rewriting.
  This allows temporary exclusion of a fragment from the stateful simpset.


## Provers
In some cases, a decision procedure can save you some work.

<code>metis_tac[<i>theorems</i>]</code>
: First-order decision procedure using the supplied theorems.
  Note that this can easily loop if given too much information.

`decide_tac`
: Linear arithmetic over the natural numbers.

`intLib.COOPER_TAC`
: Like `decide_tac` but for integers.

`blastLib.BBLAST_TAC`
: Bit-blasting (i.e. SAT) for goals concerning concrete word types (i.e. `word32` and others).


## Induction
Many proofs rely on induction, and there are several ways to induct in HOL4.

`Induct`
: Inducts over the first variable in a `∀`-quantified goal, based on the type of the variable.
  For example, applying `Induct` to `∀ n : num. P n` begins induction over the natural number `n`, giving a base case `0` and a step/successor case.

<code>Induct_on &grave;<i>term</i>&grave;</code>
: Inducts over the given term, based on its type.
  This can be used similarly to `Induct` - e.g. to prove `P (n : num)` we can use <code>Induct_on &grave;n&grave;</code>.
  However, we can also induct over an inductive relation - given a relation `is_even` and a goal `is_even n`, we can use <code>Induct_on &grave;is_even&grave;</code>.

<code>... using <i>theorem</i></code>
: Used as as suffix to `Induct` or <code>Induct_on &grave;<i>term</i>&grave;</code> to specify a particular induction theorem for use.
  For example, <code>Induct_on &grave;l&grave; using SNOC_INDUCT</code> begins induction over list `l` from the tail, rather than the head (`SNOC` is the reverse of `CONS`).

<code>completeInduct_on &grave;<i>term</i>&grave;</code>
: Begins strong/complete induction on the supplied natural number.
  In other words, the inductive hypothesis is over all numbers strictly less than the goal instance.

<code>measureInduct_on &grave;<i>term</i>&grave;</code>
: Begins strong/complete induction using the supplied measure.
  This should be in the form of a measure function (one which returns a natural number) applied to an input variable which is currently free in the goal.
  For example, <code>measureInduct_on &grave;LENGTH l&grave;</code> begins induction over the length of the list `l` from the current goal.

<code>recInduct <i>theorem</i></code><br><code>ho_match_mp_tac <i>theorem</i></code>
: Induction using the supplied theorem, which usually arises from definition of a recursive function or an inductive relation.


## Case splits
It is often useful to perform case splits over the course of a proof.

`Cases`
: Case splits on the first variable in a `∀`-quantified goal.

<code>Cases_on &grave;<i>term</i>&grave;</code>
: Case splits on the supplied term.

<code>PairCases_on &grave;<i>var</i>&grave;</code>
: Given a variable `p` of a pair type, instantiates `p` to `(p0,p1,...,pn)`.
  This provides better naming than `Cases_on`, and requires fewer case splits for `n`-tuples where `n` is greater than 2.

`pairarg_tac`
: Searches the goal and assumptions for `(λ(x,y,...). body) arg`, and introduces the assumption `arg = (x,y,...)`.
  This can often provide better naming than `PairCases_on`.

`CASE_TAC`
: Case splits the smallest `case` expression in the goal.

`FULL_CASE_TAC`
: Like `CASE_TAC`, but picks the smallest `case` expression in the goal *and* assumptions.

`TOP_CASE_TAC`
: Like `CASE_TAC`, but picks the top-most `case` expression.

`every_case_tac`
: Splits every possible `case` expression.
  This can be slow and explode the number of subgoals!

`IF_CASES_TAC`
: Case splits on an `if ... then ... else ...` expression in the goal.

<code>CaseEq "<i>string</i>"</code>
: Returns a theorem of the form `(case x of ...) = v <=> ...`, where the type of `x` is given by the supplied string.
  This is intended for use with simplification, where it can help remove tautologies/absurdities in `case` expressions.

`AllCaseEqs()`
: Like `CaseEq`, but returns a conjunction of all currently-available cases theorems.
  Most commonly used as `gvs[AllCaseEqs()]`.


## Subgoal management
Maintainable and readable files require organised proofs - in particular, careful management of subgoals.

<code><i>tactic1</i> >> <i>tactic2</i></code><br><code><i>tactic1</i> &bsol;&bsol; <i>tactic2</i></code><br><code><i>tactic1</i> THEN <i>tactic2</i></code>
: Performs *`tactic1`* and then performs *`tactic2`* on all subgoals produced.

<code><i>tactic1</i> >- <i>tactic2</i></code><br><code><i>tactic1</i> THEN1 <i>tactic2</i></code>
: Performs *`tactic1`* and then uses *`tactic2`* to solve the first subgoal produced.
  This fails if the second tactic does not completely solve the subgoal.

<code>&grave;<i>term</i>&grave; by <i>tactic</i></code>
: Creates a new subgoal from the given term, and solves it with the given tactic.
  The proved subgoal is added as an assumption for the rest of the proof.

<code>qsuff_tac &grave;<i>term</i>&grave;</code>
: In some ways a dual of `by` above: attempts a "suffices by" proof.
  Adds the supplied term as an implication to the current goal, and adds the term itself as a new subgoal.

<code>&grave;<i>term</i>&grave; suffices_by <i>tactic</i></code>
: Like `qsuff_tac`, but solves the first subgoal (i.e. that the supplied term implies the goal) using the given tactic.

<code><i>tactic</i> >~ [&grave;<i>pat</i>&grave;s]</code>
: Performs *`tactic`* and then searches for the first subgoal with subterms matching the supplied patterns.
  [Renames](#renaming-and-abbreviating) these subterms to match the patterns, and brings the goal into focus as the current goal.

<code><i>tactic</i> >>~ [&grave;<i>pat</i>&grave;s]</code>
: Like `>~`, but can match/rename multiple goals and bring them all to the top of the goal-stack.

<code><i>tactic1</i> >>~- ([&grave;<i>pat</i>&grave;s], <i>tactic2</i>)</code>
: Like `>>~`, but tries to solve the matched/renamed goals using *`tactic2`*.
  This fails if any of the goals are not completely solved.

<code>rpt <i>tactic</i></code>
: Repeats the given tactic until it fails.

<code>TRY <i>tactic</i></code>
: Attempts to apply the given tactic - but if it fails, leaves the goal unchanged.
  <br>**NB** use of `TRY` is generally regarded as poor style.


## Goal deconstruction
In many cases, we may want to state exactly how the goal should be taken apart (rather than simply applying `rw[]` or similar).

`strip_tac`
: Splits a top-level conjunct into two subgoals, *or* move a top-level implication antecedent into the assumptions, *or* remove a top-level `∀`-quantified variable.
  Often `rpt strip_tac` (which repeats `strip_tac` as many times as possible) is used.

`conj_tac`
: Splits a top-level conjunct into two subgoals.

`conj_asm{1,2}_tac`
: Like `conj_tac`, but adds the first/second conjunct (respectively) as an assumption for the other subgoal.

`disj{1,2}_tac`
: Reduces a goal of the form `p \/ q` into `p` or `q` respectively.

`gen_tac`
: Removes a top-level `∀`-quantified variable.

`AP_TERM_TAC`
: Reduces a goal of the form `f x = f y` to `x = y`.

`AP_THM_TAC`
: Reduces a goal of the form `f x = g x` to `f = g`.

`MK_COMB_TAC`
: Reduces a goal of the form `f x = g y` to two subgoals, `f = g` and `x = y`.

`iff_tac`<br>`eq_tac`
: Reduces a goal of the form `P <=> Q` to two subgoals, `P ==> Q` and `Q ==> P`.

`impl_tac`
: For a goal of the form `(A ==> B) ==> C`, splits into the two subgoals `A` and `B ==> C`.
  `impl_keep_tac` is a variant which keeps `A` as an assumption in the `B ==> C` subgoal.

<code>qexists &grave;<i>term</i>&grave;</code>
: Instantiates a top-level `∃` quantifier with the supplied term.

<code>qexistsl [&grave;<i>term</i>&grave;s]</code>
: Like `qexists`, but accepts a list of terms to instantiate multiple `∃` quantifiers.

<code>qrefine &grave;<i>term</i>&grave;</code>
: Refines a top-level `∃` quantifier using the supplied term - any free variables in the term become`∃`-quantified.
  For example, for a goal `∃ n : num. if n = 0 then P n else Q n`, applying ``qrefine `SUC k` >> simp[]`` produces the goal `∃ k : num. Q (SUC k)` (where `SUC` is the successor function).

<code>qrefinel [&grave;<i>term</i>&grave;s]</code>
: Like `qrefine`, but accepts a list of terms to instantiate multiple `∃` quantifiers.
  Also can be passed underscores, to avoid refining selected `∃` quantifiers.
  For example, for a goal `n = 2 /\ c = 5 ==> ∃ a b c d. a + b = c + d`, the tactic <code>strip_tac >> qrefinel [&grave;_&grave;,&grave;SUC c&grave;,&grave;_&grave;,&grave;n + m&grave;]</code> produces the new goal `∃ a c' m. a + SUC c = c' + (n + m)` .

<code>goal_assum $ drule_at Any</code>
: For a goal of the form `∃ vars . P1 /\ ... /\ Pn` (where the `vars` may be free in the `Pi`), attempts to match the `Pi` against the assumptions.
  If a match is found for some `Pk`, the relevant `vars` are instantiated and `Pk` is removed from the goal.

<code>wlog_tac &grave;<i>term</i>&grave; [&grave;<i>variable</i>&grave;s]</code>
: Introduces the supplied term as a hypothesis that can be assumed without loss of generality, usually producing two subgoals.
  The first requires proving that no generality has been lost, i.e. if you can prove the goal equipped with the new hypothesis, then you can prove the goal as-is.
  The second is the original goal enriched with the new hypothesis.
  Any variables in the second argument to `wlog_tac` are additionally quantified over in the first subgoal.
  See <code>help "wlog_tac"</code> for examples.

## Assumption management
Managing assumptions is key to making progress in many goal states.
This involves both the introduction and selection of assumptions.

Note that when we select an assumption, we usually want to process it further.
In these cases, we use functions of type `(thm -> tactic) -> tactic` - i.e. they select an assumption (of type `thm`), apply the given function (of type `thm -> tactic`, pronounced "theorem-tactic", and abbreviated `thm_tactic`) to it, and return the resulting tactic.
These functions tend to have at least two variants: one which leaves the original assumption untouched (only operating on a copy), and one which removes the original assumption.
The latter usually have a `"_x_"` in their names.

<code>assume_tac <i>theorem</i></code>
: Introduces the supplied theorem into the assumptions.

<code>mp_tac <i>theorem</i></code>
: Introduces the supplied theorem into the goal as an implication (i.e. transforms the `goal` into <code><i>theorem</i> ==> goal</code>).

<code>disch_then <i>thm_tactic</i></code>
: Given a goal of the form `A ==> B`, strips off `A` (i.e. *discharges* it) and applies the supplied theorem-tactic to it.

<code>first_assum <i>thm_tactic</i></code><br><code>first_x_assum <i>thm_tactic</i></code>
: Applies the theorem-tactic to the first/newest assumption on which it succeeds.

<code>last_assum <i>thm_tactic</i></code><br><code>last_x_assum <i>thm_tactic</i></code>
: Applies the theorem-tactic to the last/oldest assumption on which it succeeds.

<code>pop_assum <i>thm_tactic</i></code>
: Removes the first/newest assumption and applies the theorem-tactic to it.

<code>qpat_assum &grave;<i>pat&grave; thm_tactic</i></code><br><code>qpat_x_assum &grave;<i>pat&grave; thm_tactic</i></code>
: Attempts to find an assumption matching the supplied pattern and applies the theorem-tactic to it.

<code>goal_term <i>term_tactic</i></code>
: Given <code><i>fun</i> : term -> tactic</code>, applies *`fun`* to the current goal (i.e. a `term`).
  This is useful for programmatically selecting/specialising tactics based on the goal.

<code>goal_assum <i>thm_tactic</i></code>
: Applies the given theorem-tactic to the negated goal - i.e. select the goal as a negated assumption.

<code>spose_not_then <i>thm_tactic</i></code>
: Like `goal_assum`, but geared towards proof-by-contradiction: negates the goal **and** pushes the negation inwards, before applying the given theorem-tactic to the result.
  A common usage is `spose_not_then assume_tac`.

<code>ASSUME_NAMED_TAC "<i>label</i>" <i>theorem</i></code>
: Found in `markerLib`.
  Add the theorem as an labelled assumption: `label :- theorem`.
  E.g. `pop_assum $ ASSUME_NAMED_TAC "..."`.

<code>LABEL_ASSUM "<i>label</i>" <i>thm_tactic</i></code><br><code>LABEL_X_ASSUM "<i>label</i>" <i>thm_tactic</i></code>
: Found in `markerLib`.
  Select the labelled assumption `label :- assumption` and apply <code><i>thm_tactic</i> assumption</code>.

<code>L "<i>label</i>"</code>
: Found in `markerLib`.
  When used in a stateful simplifier, produces the theorem `assumption` from labelled assumption `label :- assumption`.

<code>kall_tac</code>
: Equivalent to `K ALL_TAC`, i.e. accepts any input and leaves the goal unchanged.
  Most useful to delete assumptions, e.g. `pop_assum kall_tac` removes the most recent assumption.


## Instantiations and generalisations
It is common to require instantiation of general inductive hypotheses or lemmas to more specific forms.
In some cases, it is useful to generalise a goal in order to use a suitable induction theorem.

<code>drule <i>theorem</i></code>
: Given a theorem of the form `∀vars. P1 /\ ... /\ Pn ==> Q`, look through the assumptions (newest to oldest) to find a matching for `P1`.
  If a match is found the relevant `vars` are instantiated, and the remaining `∀vars'. P2 /\ ... /\ Pn => Q` is added as an implication to the goal.
  `rev_drule` looks through assumptions in the opposite order.

<code>drule_all <i>theorem</i></code>
: A variant of `drule` which attempts to match all the conjuncts `P1, ..., Pn`.

<code>drule_then <i>theorem thm_tactic</i></code>
: A variant of `drule` which processes the resulting instantiated theorem using a theorem-tactic, rather than adding it as an implication to the goal.

<code>irule <i>theorem</i></code>
: Attempts to convert the supplied theorem into the form `∀vars. P1 /\ ... /\ Pn ==> Q`, matches `Q` against the goal, and if successful instantiates the necessary variables to turn the goal into `∃vars'. P1 /\ ... /\ Pn`.
  This is effectively the reverse of *modus ponens*.

<code>ho_match_mp_tac <i>theorem</i></code>
: Like `irule`, but carries out higher-order matching and does not attempt to convert the input theorem.
  Wherever possible, `irule` should be used - however when the goal itself is `∀`-quantified, it may be necessary to use `ho_match_mp_tac`.

<code>qspec_then &grave;<i>tm&grave; thm_tactic thm</i></code>
: Instantiates the supplied (`∀`-quantified) theorem with the given term, and applies the theorem-tactic to the result.

<code>qspecl_then [&grave;<i>tm&grave;s] thm_tactic thm</i></code>
: Like `qspec_then`, but instantiates multiple `∀`-quantified variables.

<code>imp_res_tac <i>theorem</i></code>
: Adds add all immediate consequences of the supplied theorem to the assumptions (i.e. performs resolution).
  The theorem should be an implication or bi-implication.
  Note that this can cause an explosion in the number of assumptions.

`res_tac`
: Like `imp_res_tac`, but resolves all assumptions with each other (it takes no input theorem).
  This can easily cause an explosion in the number of assumptions.

<code>qid_spec_tac &grave;<i>variable</i>&grave;</code>
: Generalises the supplied variable in the goal (i.e. introduces a `∀` quantifier).


### Positional modifiers
There are positional variants of `irule` and `drule`.

<code>irule_at <i>position theorem</i></code>
: Applies <code>irule <i>theorem</i></code> within the goal, matching the conclusion at the position given by *`position`*.

<code>drule_at <i>position theorem</i></code>
: Applies <code>drule <i>theorem</i></code>, but attempts to match/instantiate the conjunct given by *`position`*.

<br>
The <code><i>position</i></code> is expressed as a value of type `match_position`, with values and meanings:

`Any`
: Any position which succeeds.

<code>Pat &grave;<i>pattern</i>&grave;</code>
: Any position which matches the pattern.

<code>Pos <i>fun</i></code>
: The position given by applying the supplied function (where <code><i>fun</i> : term list -> term</code>) to the list of conjuncts.
  `Pos hd`, `Pos last`, and <code>Pos $ el <i>integer</i></code> are common uses.

`Concl`
: Match against the negated conclusion, i.e. use the implication in a contrapositive way.

<br>
By way of example, given a goal `∃x y. P x /\ Q y` and a theorem `thm = ⊢ R a b ==> P b`, `irule_at Any thm` produces the goal `∃a y. R a b /\ Q y`.
`irule_at (Pos hd) thm` is equivalent in this case.


## Renaming and abbreviating
HOL4 automatically generates fresh names where necessary, e.g. for case splits and existential witnesses.
This is usually by appending apostrophes, and the resulting names become ugly.
Sometimes large terms are generated too, and these are unwieldy.

Small changes to proofs can change variable naming and large expression structure quite easily - explicitly relying on automatically-chosen variable names or the exact phrasing of large expressions can lead to brittle proofs.
Both are therefore bad style.
Instead, we can rename variables appropriately, and abbreviate large terms.

<code>rename1 &grave;<i>pattern</i>&grave;</code>
: Matches the pattern against a subterm in the goal or assumptions, and renames the subterm to match the pattern.
  For example, ``rename1 `n + _ <= foo` `` renames `a + b <= c + d` into `n + b <= foo`.
  Note that we have lost information here on the RHS.

<code>qmatch_goalsub_abbrev_tac &grave;<i>pattern</i>&grave;</code>
: Matches the pattern to a subterm in the goal, abbreviating the matching subterm to fit the pattern.
  Unlike renaming, abbreviating preserves information - assumptions are introduced which keep track of the abbreviations.

<code>qmatch_asmsub_abbrev_tac &grave;<i>pattern</i>&grave;</code>
: Like `qmatch_goalsub_abbrev_tac`, but looks for matches in the assumptions only.

<code>qabbrev_tac &grave;<i>var = term</i>&grave;</code>
: Abbreviates an exact given term to the supplied variable.

<code>qpat_abbrev_tac &grave;<i>var = pattern</i>&grave;</code>
: Matches the pattern to a subterm of the goal, and abbreviates the matching subterm to the supplied variable.

`LET_ELIM_TAC`
: Given a goal of the form `let x = e1 in e2`, abbreviates `e1` to `x` and transforms the goal to `e2`.

`unabbrev_all_tac`
: Unabbreviates all existing abbreviations.

<code>Abbr &grave;<i>var</i>&grave;</code>
: When used in a stateful simplifier, produces a rewrite theorem which unabbreviates the supplied variable.
  For example, if `x` is an abbreviation in the goal-state, using ``simp[Abbr `x`]`` will unabbreviate `x` in the goal.

<code>qx_gen_tac &grave;<i>var</i>&grave;</code>
: Like `gen_tac`, but specialises the `∀`-quantified variable using the given name.

<code>qx_choose_then &grave;<i>var</i>&grave; <i>thm_tactic thm</i></code>
: Takes the theorem supplied, which should be `∃`-quantified, and "chooses" the witness for the `∃` quantification to be the supplied variable.
  Processes the result using the supplied theorem tactic (often `mp_tac` or `assume_tac`).

<code>namedCases_on &grave;<i>tm</i>&grave; ["<i>string</i>"s]</code>
: Like `Cases_on`, but allows naming of introduced variables.
  Each string in the list corresponds to a case, and multiple names are separated by a space.
  For example, ``namedCases_on `l` ["", "head tail"]`` performs a case split on list `l`, naming the `head` and `tail` appropriately in the non-empty list case.


## Examples and common patterns
Some patterns arise very often in proofs.

  - **[Introduction and instantiation](#assumption-management) of theorems.**
    - `drule thm` - instantiates an antecedent of the theorem with an assumption.
    - `qspecl_then [...] assume_tac thm` - specialises a theorem and adds it to the assumptions.
    - `qspecl_then [...] mp_tac thm` - specialises a theorem and adds it as an implication to the goal.
  - **[Assumption selection](#assumption-management) followed by [instantiation](#instantiations-and-generalisations).**
    These patterns arise very commonly, particularly during inductive proof.
    Almost any assumption selection function can be used with almost any theorem-tactic - here are a few examples.
    - `first_x_assum drule` - instantiates the first antecedent of an implicational assumption with another assumption (taking the newest if there are multiple).
    - ``qpat_x_assum `...` $ irule_at Any`` - select the implicational assumption matching the pattern, and match its conclusion against some part of the goal.
      Remove that part of the goal, and add the (appropriately instantiated) antecedents of the assumptions to the goal.
    - `last_x_assum $ qspecl_then [...] mp_tac` - select an assumption which can be instantiated with the given variables, and add it as an implication to the goal (taking the oldest if there are multiple).
    - `pop_assum $ drule_then assume_tac` - `drule` the newest assumption, and add it back as an assumption.
    - `disch_then drule` provides a useful continuation to `drule`: takes `A` from a goal of the form `A ==> B` and effectively attempts `drule A`.
    - *and so on*
  - **[Case splits](#case-splits) followed by [simplification](#rewriting) and [renaming](#renaming-and-abbreviating).**
    Case splits introduce fresh variable names and equalities.
    Simplification can use the equalities, and renaming cleans up the fresh names.
    - ``TOP_CASE_TAC >> gvs[] >> rename1 `...` ``
    - ``Cases_on ... >> simp[] >> qmatch_goalsub_abbrev_tac `...` ``
    - *and so on*
  - **Simpler targeted [simplification](#rewriting).**
    Sometimes when `fs`, `gvs`, and so on do too much, it can be useful to select an assumption, move it to the goal as an implication, and then use `simp` instead.
    This can prevent looping rewrites between assumptions.
    E.g. ``qpat_x_assum `...` mp_tac >> simp[]``
    - We can select single assumptions to use as rewrites too:
      ``qpat_x_assum `...` $ rw o single``, leveraging the ML-level `single` function which creates a singleton list.
  - **Rewrites which don't seem to do anything.**
    Sometimes it may seem that you have an assumption which should trigger simplification in the goal on rewriting - however, it doesn't seem to be doing anything.
    Often this is due to a type mismatch - i.e. your assumption involves more general types than your goal.
    To diagnose it you can turn types annotations on using for instance `show_types:= true`.
    If this is the case, you cannot instantiate type variables once introduced into your goal-state for soundness reasons, so you must instead type-instantiate the assumption when it is introduced.
    You can use `INST_TYPE` for this, for example:<br>
    <code>assume_tac $ INST_TYPE [&grave;&grave;:'a&grave;&grave; |-> &grave;&grave;:num&grave;&grave;] listTheory.MAP</code>
