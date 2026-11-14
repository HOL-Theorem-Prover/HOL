HolyHammer by example
=====================

This directory is a guided tour of HolyHammer for HOL4 users.  It shows
what the hammer is good at, what it is not good at, and how to work with
it day to day.  All the examples are realistic goals from the standard
libraries or from small developments of the kind you would write
yourself.

HolyHammer ("hammer" for short) takes a HOL4 goal and:

  1. *selects premises*: picks a few dozen to a few hundred possibly
     relevant theorems from everything loaded (ancestor theories, the
     current theory, and theorems bound at the top level);
  2. *translates* the goal and the premises into first-order or
     higher-order TPTP problems;
  3. *runs external provers* (E, Vampire, Zipperposition) on those
     problems in parallel, with different settings in different time
     slices;
  4. *reconstructs* the proof in HOL4: the theorems a prover used are
     given to `metis_tac`, which re-proves the goal inside the logical
     kernel.

The result is an ordinary `metis_tac [...]` call that you paste into your
proof script.  The external provers are never trusted.  A hammer proof
is checked by the kernel like any other, and it adds no oracle tags.


Contents
--------

Start with `hh01`.  The library tours `hh02`-`hh06` can be read in any
order; `hh07`-`hh10` build on the lessons of the earlier files.

  * `hh01_tutorialScript.sml`: first steps.  `holyhammer` and `hh`,
    reading the output, hammering inside a proof, your own definitions
    and lemmas.
  * `hh02_arithScript.sml`: natural numbers.  Division, parity,
    divisibility, gcd, primes, powers.
  * `hh03_listScript.sml`: lists.  Append, reverse, map, filter,
    take/drop, zip, permutations, sortedness.
  * `hh04_setScript.sml`: sets and functions.  Algebra of sets, images,
    injections, cardinality.
  * `hh05_relationScript.sml`: relations.  Closures, equivalences,
    well-foundedness, confluence.
  * `hh06_realScript.sml`: real analysis.  Inequalities, absolute
    value, exp/ln, trigonometry, and a derivation in small steps.
  * `hh07_inductionScript.sml`: your own datatypes and recursive
    functions.  You do the induction, the hammer does the cases.
  * `hh08_sortingScript.sml`: case study, insertion sort.  Every lemma
    is hammered and then used by later hammer calls; one missing lemma
    makes the difference.
  * `hh09_queueScript.sml`: case study, a functional queue.  Split
    pattern matches and `case` expressions before hammering.
  * `hh10_troubleshootingScript.sml`: when the hammer fails.  False
    goals, decidable goals, failed reconstruction, set-builder notation,
    slow calls.
  * `interactive.sml`: an annotated interactive session.  Checking the
    provers, options, explicit premises with `hh_pb`, `debug_dir`.

The theory files build without any external prover:

    cd src/holyhammer/examples
    ../../../bin/Holmake

They contain the *output* of the hammer (the verified `metis_tac` calls),
not the hammer calls themselves.  Each place where the hammer was called
is marked with `(* hh *)`, for example:

    Theorem exp_sub_mul:
      a <= b ==> g ** (b - a) * g ** a = g ** b
    Proof
      (* hh *)
      metis_tac [SUB_ADD, EXP_ADD]
    QED

This is the recommended way to use any hammer (it is also the advice
of the Sledgehammer and CoqHammer manuals).  Call it interactively, then
replace the call with the proof it prints.  Hammer runs depend on
timeouts, on the machine's load, on the installed prover versions, and
on the facts that happen to be loaded.  A script that calls `hh` is
therefore slow and may stop building when any of these change.  The
printed `metis_tac` call depends only on the named theorems.


Setting up
----------

Install at least one prover.  The easiest way is

    tools/download-provers

from the root of the HOL4 checkout.  Alternatively, put `eprover` (or
`eprover-ho`), `vampire` or `zipperposition` on your `PATH`.  See
`../README` for the tested versions and for other ways of telling
HolyHammer where the binaries are.

Then, in an interactive session:

    load "holyHammer"; open holyHammer;
    holyhammer ``LENGTH (REVERSE l ++ l) = 2 * LENGTH l``;

If no prover is found, you get

    HolyHammer: no prover binary found; run tools/download-provers or
    put a supported prover binary on PATH

`interactive.sml` shows how to list the provers HolyHammer can see and
which versions they are.

To replay an example from one of the theory files, load its ancestors
and the theory itself, then call the hammer on the theorem's statement.
For instance, for `hh03_list`:

    load "holyHammer"; open holyHammer;
    load "hh03_listTheory"; open listTheory rich_listTheory sortingTheory;
    holyhammer ``MEM x (l1 ++ l2) /\ EVERY P l1 /\ EVERY P l2 ==> P x``;

The theorems of `hh03_list` itself are then visible to the hammer too.
To replay one of the theories from scratch, as the author did, step
through the script in an interactive session and use `hh` (or
`holyhammer`) wherever a proof is marked `(* hh *)`.


The two entry points
--------------------

`holyhammer : term -> thm` proves a closed statement:

    > val th = holyhammer ``MEM x l /\ EVERY P l ==> P x``;
      starting vampire slice (96 facts)
      starting e slice (128 facts)
      ...
      e slice: Theorem (0.13 s)
      proof found by e:
        metisTools.METIS_TAC [listTheory.EVERY_MEM]
      verified proof:
        metis_tac [EVERY_MEM]
      ...
    val th = ⊢ MEM x l ∧ EVERY P l ⇒ P x: thm

`hh : tactic` is the same thing as a tactic.  It attacks the current
goal *including its assumptions*:

    > g `!l1 l2. ALL_DISTINCT (l1 ++ l2) ==> DISJOINT (set l1) (set l2)`;
    > e (rpt strip_tac);
    > e hh;

How to read the output:

  * `starting <prover> slice (N facts)`: a prover was started on a
    problem containing the N best-ranked premises.  Different slices
    use different premise selectors, numbers of facts, TPTP dialects and
    prover options.  They run in parallel, one per core.
  * `<prover> slice: Theorem (t s)`: that prover claims a proof.  Other
    statuses are `Timeout`, `GaveUp`, `ResourceOut`, `CounterSatisfiable`
    (the selected premises do not imply the goal, which does not mean the
    goal is false), and `ContradictoryAxioms` (see the FAQ).
  * `proof found by <prover>:` lists *all* the facts the prover used.
  * `verified proof:` is the minimised tactic that actually re-proved
    the goal in HOL4.  **This is the line to copy into your script.**
    Facts from the current theory print as `fetch "thy" "name"`
    (`DB.fetch`).  In a script you can write plain `name` if the theorem
    is bound as an ML value (`Theorem name: ...` and `Definition
    name: ...` bind it).  Automatically generated theorems such as
    `foo_compute` or `foo_ind` are only stored, so keep the `fetch` for
    those.
  * Once a proof is verified, the remaining slices are stopped.  The last
    few `Timeout` lines are those slices being shut down.

On failure, `hh` and `holyhammer` raise `HOL_ERR`, with one of two
messages:

  * `ATPs could not find a proof`: no prover succeeded within the time
    limit (30 s by default).
  * `ATPs found proofs, but reconstruction failed for: ...`: at least one
    prover found a proof but `metis_tac` could not replay it.  The
    message lists the facts each prover used.  These are often all you
    need to finish the proof by hand; see `hh10_troubleshootingScript.sml`.


What the hammer is good at
--------------------------

Across the examples in this directory, run on a 16-core machine with the
default 30 s budget:

  * Almost every "there must be a library lemma for this" goal is
    solved in 2-10 seconds.  This includes lemmas with hard-to-guess
    names (`EXTEND_RTC_TC_RIGHT1`, `rpreserves_symmetric_RTC`,
    `HD_APPEND_NOT_NIL`, `DIVIDES_LEQ_OR_ZERO`) and variants of library
    lemmas with arguments swapped, an implication in place of an
    equivalence, or an extra assumption.
  * Goals that need a *combination* of 3-8 lemmas, especially equational
    reasoning that `simp` cannot orient (for example
    `SUC n ** 2 = n ** 2 + 2 * n + 1`, permutation lemmas, absolute-value
    estimates).
  * Induction and case-analysis *steps* in your own developments, once
    you have done the induction yourself.  The hammer finds and combines
    the definitions, the induction hypothesis and the library lemmas.

For comparison, twelve of the multi-lemma goals in these files were also
given to the standard tactics without any lemmas: `simp []`,
`metis_tac []`, `DECIDE_TAC` and `rw [] >> metis_tac []`, each with a
10-second limit.  Only three (`length_rev_append_self`,
`reverse_middle` and `card_insert_new`) were proved, all by `simp`.
The hammer proved all twelve.

What it is not good at:

  * Anything that needs induction.  The hammer never does induction;
    you have to start it.
  * Goals whose proof needs a lemma that is not in the library and is
    not a short consequence of library lemmas.  State the intermediate
    fact and hammer that first.
  * Heavy higher-order reasoning: set comprehensions, nested lambdas,
    `case` expressions.  Presimplify these away first (`hh09`, `hh10`).
  * Definitions that test equality inside `if-then-else`, such as
    `count_occ x (y::l) = (if x = y then 1 else 0) + ...`.  State the
    two branches as separate lemmas (`hh07`).
  * Arithmetic that a decision procedure does instantly.  Use
    `DECIDE_TAC`, `intLib.ARITH_TAC`, `REAL_ARITH_TAC` or `EVAL_TAC`
    instead.
  * Long chains of algebra.  In `hh06` the hammer finds the
    trigonometric facts and `REAL_ARITH_TAC` does the rearranging.


Tips for effective use
----------------------

These tips come from the Sledgehammer user's guide, Lawrence Paulson's
"Sledgehammer: some history, some tips", and the CoqHammer tutorial,
adapted to HOL4 and checked against HolyHammer on the examples in this
directory.  The file named after each tip contains a worked example.

 1. **Do the induction yourself** (`hh07`, `hh08`).  Start it with
    `Induct`, `Induct_on`, `ho_match_mp_tac` or `recInduct`, then call `hh`
    on each subgoal (`Induct_on `t` >> hh` hammers each case
    separately).  The hammer uses the induction hypotheses from the
    assumptions.

 2. **Split cases and presimplify, but not too much** (`hh09`, `hh10`).
    `Cases_on`, `rw [EXTENSION]` and `simp [defn]` are cheap and remove
    exactly the constructs (pattern matching, `case`, set-builder
    notation) that the provers and Metis handle badly.  Over-simplifying
    can hurt, though: `simp` may rewrite the goal into a shape no longer
    matched by the library lemma that would have finished it.  If a
    simplified goal fails, try hammering the original.

 3. **Look for an intermediate fact** (`hh06`, `hh08`).  If the goal
    is too far from the library, find a fact that follows from your
    assumptions and gets you closer.  Hammer that, then hammer the goal.
    In `hh08`, the hammer cannot prove that insertion preserves
    sortedness until the lemma `mem_ins` (the elements of `ins x l` are
    `x` and the elements of `l`) has been proved; after that the same
    call succeeds.
    Facts you prove interactively (`val lemma = holyhammer ...`) and
    theorems stored in the current theory are premises for later calls.

 4. **Prefer standalone lemmas to mid-proof calls** (`hh08`).  The
    CoqHammer authors recommend hammering whole lemmas rather than
    subgoals deep inside a long proof.  Irrelevant assumptions confuse
    premise selection and slow the provers down, and a named lemma can
    be reused by later hammer calls.

 5. **When reconstruction fails, use the lemma list** (`hh10`).  The
    error message names the facts the prover used.  Try `metis_tac` on a
    subset, `simp [...]`, `gvs [...]`, or a decision procedure with those
    facts.  Increasing `preplay_timeout` helps only when Metis is close.

 6. **Use the right tool** (`hh10`).  Linear arithmetic, propositional
    tautologies and ground computation are decided by `DECIDE_TAC`,
    `intLib.ARITH_TAC`, `REAL_ARITH_TAC`, `tautLib.TAUT_TAC` and
    `EVAL_TAC`, which are complete, fast and need no external prover.

 7. **Steer premise selection when you know better** (`interactive.sml`).
    `hh_pb` takes an explicit list of premises, like Sledgehammer's
    `sledgehammer (facts)`.  The `filter` option switches between the kNN
    (default for most slices), MePo, MaSh and MeSh selectors, and
    `max_facts` caps the problem size.  Sledgehammer's advice applies:
    fewer facts help when you expect a *longer* proof from a handful of
    lemmas.

 8. **Give it more time only as a last resort.**  If a proof exists in
    the selected premises, the provers usually find it in the first few
    seconds.  Doubling the time limit rarely helps as much as tips 1-3.


Options
-------

Options are set for the rest of the session with `hhConfig.hh_set`, read
with `hhConfig.hh_get`, reset with `hhConfig.hh_unset`, and listed with
`hhConfig.print_params ()`.  They can also be set permanently in
`$HOME/.hol4/hammer/config` (one `name = value` per line) or in
`$HOLDIR/etc/hammer-config`.  The ones end users are most likely to
want:

| Option            | Default                     | Meaning                   |
|-------------------|-----------------------------|---------------------------|
| `timeout`         | `30`                        | overall budget, seconds   |
| `provers`         | `e vampire zipperposition`  | which provers to schedule |
| `filter`          | (per slice)                 | `knn`, `mepo`, `mash`,    |
|                   |                             | `mesh` or `none`          |
| `max_facts`       | (per slice)                 | cap on premises per slice |
| `cores`           | `0` (all)                   | parallel prover processes |
| `minimize`        | `true`                      | minimise the `metis_tac`  |
|                   |                             | lemma list                |
| `preplay_timeout` | `1.0`                       | seconds Metis gets to     |
|                   |                             | replay a proof            |
| `cache`           | `false`                     | reuse earlier prover runs |
| `debug_dir`       | (empty)                     | keep prover output here   |

Values are checked immediately:

    > hhConfig.hh_set ("filter", "magic");
    Exception- HOL_ERR (at hhConfig.hh_set: invalid value 'magic' for
    HolyHammer option 'filter'; expected empty, knn, mepo, mash, mesh, or
    none; valid keys: ...)

`../README` documents the remaining, more technical options (TPTP
format, type encoding, lambda translation, monomorphisation).


Frequently asked questions
--------------------------

**Which facts does the hammer see?**  Every theorem in the ancestry of
the current theory, every theorem stored so far in the current theory,
and every theorem value bound at the top level of the interactive
session (`val my_lemma = ...`).  Theorems that are not loaded are
invisible.  To use `sortingTheory` you must `load "sortingTheory"` (or
list it under `Ancestors`) first.  Each slice then ranks the facts and
sends only the best N to the prover.

**Is it sound?**  Yes.  The provers only suggest which facts to use;
`metis_tac` re-proves the goal through the HOL4 kernel.  A proof the
kernel cannot check is reported as a failure.

**Is it reproducible?**  The hammer is not, but its output is: the
printed `metis_tac` call is an ordinary deterministic tactic.  Re-running
`hh` on the same goal can produce a different (equally valid) lemma
list, or fail under load, which is why scripts should not call it.

**Why did `metis_tac` with the suggested facts fail when I tried it?**
Look for `fetch "thy" "name"` in the suggestion and make sure you are in
the same theory context.  Also check that the short theorem names refer
to the same theorems in your script as in your session.  Two opened
theories can export the same name (for example `EXP_ADD` in both
`arithmeticTheory` and `transcTheory`), and `Ancestors` order decides
which one wins.  When in doubt, qualify the name.

**What does `ContradictoryAxioms` mean?**  The prover found the selected
premises inconsistent *without* using the goal.  With library theorems
this should not happen.  The usual cause is a theorem with assumptions
bound at the top level of your session, which the translation currently
treats as an unconditional fact.  For example,
`val th = TAC_PROOF (([``x < y``, ``y < z``], ``x < z + 1``), hh)` then
looks like `!x z. x < z + 1` to later hammer calls.  Reconstruction
rejects any such "proof", so soundness is not at risk, but the call is
wasted.  Discharge assumptions (`DISCH_ALL`) before binding a theorem at
the top level.

**The hammer failed.  Is my goal false?**  Not necessarily.  "ATPs could
not find a proof" only means that no proof was found from the selected
premises in the time available.  Check the goal on concrete values with
`EVAL` before investing more effort.

**Can I see the problems sent to the provers?**  Yes, with
`debug_dir` set.  Normally each call writes its TPTP problems to a
temporary directory and deletes them when it returns.  With
`hhConfig.hh_set ("debug_dir", dir)`, the problems are kept below
`dir/problems`, one subdirectory per call and inside it one per slice,
named after the prover, the premise selector, the encoding and the
number of facts; the problem is the file `atp_in`.  Each prover's raw
output is kept in `dir` itself (see `interactive.sml`).

**Why does a call take several seconds when the prover answered in
0.2 s?**  Ranking all the loaded theorems for each slice, writing the
problems and replaying the proof in Metis take time too.  Expect a few
seconds per call even for easy goals.


HolyHammer and other hammers
----------------------------

If you know a hammer from another proof assistant:

  * **Hammer the current goal.** HOL4 `e hh` (or `hh` anywhere a tactic is
    expected); Isabelle `sledgehammer`; Rocq `hammer`.
  * **Prove a closed statement.** HOL4 ``holyhammer ``t`` ``; Isabelle
    `lemma "t" sledgehammer`; Rocq `Lemma l : t. hammer.`
  * **What you paste into the script.** HOL4 `metis_tac [...]`;
    Isabelle `by (metis ...)`, `by simp`, etc.; Rocq `sauto use: ...`,
    `hauto use: ...`, etc.
  * **Use only the given facts.** HOL4 `hh_pb dir provers facts`; Isabelle
    `sledgehammer (f1 f2)`; Rocq `sauto use: f1, f2`.
  * **Time limit.** HOL4 `hhConfig.hh_set ("timeout", "60")`; Isabelle
    `sledgehammer [timeout = 60]`; Rocq `Set Hammer ATPLimit 60`.
  * **Choose provers.** HOL4 `hhConfig.hh_set ("provers", "e")`; Isabelle
    `sledgehammer [provers = e]`; Rocq `Unset Hammer Vampire` (and so on).
  * **Relevance filter.** HOL4 `hhConfig.hh_set ("filter", "mepo")`;
    Isabelle `sledgehammer [fact_filter = mepo]`; Rocq
    `Set Hammer PredictMethod`.
  * **Show the settings.** HOL4 `hhConfig.print_params ()`; Isabelle
    `sledgehammer_params`.

The relevance filters share their names and algorithms with
Sledgehammer: MePo (Meng-Paulson, symbol overlap), MaSh (machine
learning from earlier proofs) and MeSh (both combined).  HolyHammer's kNN
filter also learns from proof dependencies recorded by the HOL4 kernel.


Further reading
---------------

  * `../README`: installation, executable discovery and the complete
    option list.
  * J. C. Blanchette, *Hammering Away: A User's Guide to Sledgehammer
    for Isabelle/HOL*, `https://isabelle.in.tum.de/doc/sledgehammer.pdf`.
  * L. C. Paulson, *Sledgehammer: some history, some tips*,
    `https://lawrencecpaulson.github.io/2022/04/13/Sledgehammer.html`.
  * Ł. Czajka and C. Kaliszyk, *Hammer for Coq: Automation for
    Dependent Type Theory*, JAR 2018; tutorial and examples at
    `https://coqhammer.github.io`.
  * T. Gauthier and C. Kaliszyk, *Premise Selection and External Provers
    for HOL4*, CPP 2015.
  * J. Clune et al., *LeanHammer*, `https://cmu-l3.github.io/lean-hammer`.
