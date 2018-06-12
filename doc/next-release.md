% Release notes for HOL4, ??????

<!-- search and replace ?????? strings corresponding to release name -->
<!-- indent code within bulleted lists to column 11 -->

(Released: ??????)

We are pleased to announce the ?????? release of HOL 4.

Contents
--------

-   [New features](#new-features)
-   [Bugs fixed](#bugs-fixed)
-   [New theories](#new-theories)
-   [New tools](#new-tools)
-   [New Examples](#new-examples)
-   [Incompatibilities](#incompatibilities)

New features:
-------------

*   `Holmake` under Poly/ML (*i.e.*, for the moment only Unix-like systems (including OSX/MacOS, and Windows with Cygwin or the Linux subsystem)) now runs build scripts concurrently when targets do not depend on each other.
    The degree of parallelisation depends on the `-j` flag, and is set to 4 by default.
    Output from the build processes is logged into a `.hollogs` sub-directory rather than interleaved randomly to standard out.

*   Theory files generated from script files now load faster.
    The machinery enabling this generates `xTheory.dat` files alongside `xTheory.sig` and `xTheory.sml` files.
    Thanks to Thibault Gauthier for the work implementing this.

*   We now support monadic syntax with a `do`-notation inspired by Haskell’s.
    For example, the `mapM` function might be defined:

           Define‘(mapM f [] = return []) ∧
                  (mapM f (x::xs) =
                         do
                           y <- f x;
                           ys <- mapM f xs;
                           return (y::ys);
                         od)’;

    The HOL type system cannot support this definition in its full polymorphic generality.
    In particular, the above definition will actually be made with respect to a specific monad instance (list, option, state, reader, *etc*).
    There are API entry-points for declaring and enabling monads in the `monadsyntax` module.
    For more details see the *DESCRIPTION* manual.

*   Users can define their own colours for printing types, and free and bound variables when printing to ANSI terminals by using the `PPBackEnd.ansi_terminal` backend.
    (The default behaviour on what is called the `vt100_terminal` is to have free variables blue, bound variables green, type variables purple and type operators “blue-green”.)
    Thanks to Adam Nelson for this feature.
    Configuring colours under `emacs` is done within `emacs` by configuring faces such as `hol-bound-variable`.

*   We now support the infix `$` notation for function application from Haskell.
    For example

           f $ g x $ h y

    is a low-parenthesis way of writing `f (g x (h y))`.
    The dollar-operator is a low-precedence (tighter than infix `,` but looser than other standard operators), right-associative infix.
    This is a “parse-only technology”; the pretty-printer will always use the “traditional” syntax with parentheses as necessary and what might be viewed as an invisible infix application operator.


Bugs fixed:
-----------

*   Pretty-printing of record type declarations to TeX now works even if there are multiple types with the same name (necessarily from different theory segments) in the overall theory.

*   Pretty-printing has changed to better mesh with Poly/ML’s native printing, meaning that HOL values embedded in other values (*e.g.*, lists, records) should print better.

New theories:
-------------

*   We have promoted the theories of cardinality results for various flavours of infinite sets, and of ordinal numbers to `src` from `examples`.
    There is a minor backwards-incompatibility: references to `examples/set-theory/hol_sets` (in Holmakefile `INCLUDES` specifications for example) should simply be deleted.
    Any theory can build on these theories (`cardinalTheory`, `ordinalTheory`) simply by `open`-ing them in the relevant script file.

New tools:
----------

*   For every algebraic type, the `TypeBase` now automatically proves what we term “case-equality” rewrite theorems that have LHSes of the form

          ((case x of con1_pattern => e1 | con2_pattern => e2 ...) = v)

    For example, the case-equality theorem for the `α option` type is

          (option_CASE opt nc sc = v) ⇔
             (opt = NONE) ∧ (nc = v) ∨
             ∃x. (opt = SOME x) ∧ (sc x = v)

    where `option_CASE opt nc sc` is the general form of the term that underlies a case expression over an option value `opt`.

    These theorems can be powerful aids in simplifications (imagine for example that `v` is `T` and `nc` is `F`), so we have made it easy to include them in arguments to `simp`, `fs`, `rw` *etc*.
    The `CaseEq` function takes a string and returns the corresponding theorem, so that `CaseEq "option"` will return the theorem above.
    The `CaseEqs` function takes a list of strings so that the simplifier-argument list doesn’t need to repeat `CaseEq` invocations, and finally, `AllCaseEqs()` returns a conjunction of all the `TypeBase`’s case-equality theorems.
    Then one might write something like

           simp[AllCaseEqs(), thm1, thm2]

    for example.


New examples:
---------

*   We have resurrected Monica Nesi’s CCS example (from the days of HOL88, in `examples/CCS`), ported and extended by Chun Tian (based on HOL4’s co-induction package `Hol_coreln`).
    This includes all classical results of strong/weak bisimilarities and observation congruence, the theory of congruence for CCS, several versions of “bisimulation up to”,  “coarsest congruence contained in weak bisimilarity”, and “unique solution of equations” theorems, mainly from Robin Milner’s book, and Davide Sangiorgi’s “unique solutions of contractions” theorem published in 2017.
    There’s also a decision procedure written in SML for computing CCS transitions with the result automatically proved.

*   Speaking of HOL88, we have also recovered an old hardware example.
    This work is the verification of a version of a “toy microprocessor” that came to be called *Tamarack* (see Section 5 of the [HOL history paper](https://www.cl.cam.ac.uk/archive/mjcg/papers/HolHistory.pdf)).
    First done in a system called `LCF_LSM` by Mike Gordon (around 1983), this was then redone in HOL88 by Jeff Joyce in 1989, and these sources are now ported and available under `examples/hardware`.
    Thanks to Larry Paulson for finding the HOL88 originals, and to Ramana  Kumar and Thomas Tuerk for doing the work porting these to HOL4.

*   A theory of the basic syntax and semantics of Linear Temporal Logic formulas, along with a verified translation of such formulas into Generalised Büchi Automata *via* alternating automata (in `examples/logic/ltl`).
    This work is by Simon Jantsch.

*   A theory of Lambek calculus (categorial grammars of natural or formal languages), in `examples/formal-languages/lambek`. Ported from [Coq contribs](https://github.com/coq-contribs/lambek) by Chun Tian. c.f. "The Logic of Categorial Grammars" by Richard Moot and Christian Retoré.

* A library for regular expressions (`examples/formal-languages/regular`), including a compiler from regexps to table-driven DFAs. Proofs include standard regexp identities along with the correctness of the compiler. Also, there is a standalone tool `regexp2dfa` that generates DFAs in a variety of languages. The library also supplies (informal and formal) parsers for regexps in Python syntax. See the README for more details.

Incompatibilities:
------------------

*   We have decided that the behaviour of `irule` (*aka* `IRULE_TAC`) should not include the finishing `rpt conj_tac`.
    If users want that after the implicational theorem has been matched against, it is easy enough to add.
    See the [Github issue](https://github.com/HOL-Theorem-Prover/HOL/issues/465).

*   The behaviour of the `by` and `suffices_by` tactics has changed.
    Previously, a tactic of the form `` `term quotation` by tac`` allowed `tac` to fail to prove the sub-goal of the term quotation.
    (The result would then be two or more sub-goals, where the first few of these correspond to the state of trying to prove the term quotation after applying `tac`.)
    This is no longer the case: if `tac` does not prove the new sub-goal then the overall tactic fails.

    The old implementation of `by` is available under the name `BasicProvers.byA`, so it is possible to revert to the old behaviour with the following declaration at the head of one’s script file:

           val op by = BasicProvers.byA

    If one wanted to fix possibly broken occurrences to use the new semantics, the following Perl script might be helpful (it was used to adjust the core HOL sources):

           $/ = "\n\n";

           while (<>) {
               s/(`[^`]+`)(\s*)by(\s*)(ALL_TAC|all_tac)(\s*)(>-|THEN1)/\1 by/g;
               s/(Tactical\.)?REVERSE(\s*)\((`[^`]+`)(\s*)by(\s*)(ALL_TAC|all_tac)(\s*)\)(\s*)(THEN1|>-)(\s*)\(/\3 suffices_by\8(STRIP_TAC THEN /g;
               s/(Tactical\.)?REVERSE(\s*)\((`[^`]+`)(\s*)by(\s*)(ALL_TAC|all_tac)(\s*)\)(\s*)(THEN1|>-)(\s*)/\3 suffices_by /g;
               s/(`[^`]+`)(\s*)by(\s*)(ALL_TAC|all_tac)(\s*)/sg \1\5/g;
               print;
           }

    If the above is called `byfix.pl` (for example), then a reasonable invocation would be

           perl -i byfix.pl *Script.sml

    If one’s workflow was to write things like

           `subgoal` by ALL_TAC THEN1 (tac1 THEN tac2 THEN ...)

    and the same workflow makes

           `subgoal` by (tac1 THEN tac2 THEN ...)

    difficult (perhaps because the flow calls for cutting and pasting the `... by ALL_TAC` sub-string), we recommend

           sg `subgoal` THEN1 (tac1 THEN tac2 THEN ...)

    where ``sg `subgoal` `` has the same effect as the old `` `subgoal` by ALL_TAC``.

*   The type of the “system printer” used by user-defined pretty-printers to pass control back to the default printer has changed.
    This function now gets passed an additional parameter corresponding to whether or not the default printer should treat the term to be printed as if it were in a binding position or not.
    (This `binderp` parameter is in addition to the parameters indicating the “depth” of the printing, and the precedence gravities.)
    See the *REFERENCE* manual for more details.

*   The `PAT_ASSUM` tactics (`Tactical.PAT_ASSUM`, `Q.PAT_ASSUM` and `bossLib.qpat_assum`) have all been renamed to pick up an internal `_X_` (or `_x_`).
    Thus, the first becomes `PAT_X_ASSUM`, and the last becomes `qpat_x_assum`).
    This makes the names consistent with other theorem-tactics (*e.g.*, `first_x_assum`): the `X` (or `x`) indicates that the matching assumption is removed from the assumption list.
    Using the old names, we also now have versions that *don’t* remove the theorems from the assumption list.

    The behaviour of the quoting versions of the tactics is also slightly different: they will always respect names that occur both in the pattern and in the goal.
    Again, this is for consistency with similar functions such as `qspec_then`.
    This means, for example, that ``qpat_assum `a < b` `` will fail if the actual theorem being matched is something `c < f a`.
    (This is because the pattern and the goal share the name `a`, so that the pattern is implicitly requiring the first argument to `<` to be exactly `a`, which is not the case.)
    This example would have previously worked if there was exactly one assumption with `<`.
    The fix in cases like this is to use more underscores in one’s patterns.

*   The functions `Parse.Unicode.uoverload_on` and `Parse.Unicode.uset_fixity` have been removed because their functionality should be accessed *via* the standard `overload_on` and `set_fixity` functions.
    The “temporary” versions of these functions (*e.g.*, `Parse.Unicode.temp_uoverload_on`) have also been removed, analogously.
    The `Parse.Unicode.unicode_version` function remains, as does its temporary counterpart.

*   The simpset fragment `MOD_ss` has been added to the standard stateful simpset.
    This fragment does smart things with terms involving (natural number) `MOD`, allowing, for example, something like `((7 + y) * 100 + 5 * (z MOD 6)) MOD 6` to simplify to `((1 + y) * 4 + 5 * z) MOD 6`.
    If this breaks existing proofs in a script file, the fragment can be removed (for the rest of the execution of the script) with the command

           val _ = diminish_srw_ss ["MOD_ss"]

*   The rewrites `listTheory.TAKE_def` and `listTheory.DROP_def` have been removed from the standard stateful simpset.
    These rewrites introduce conditional expressions that are often painful to work with.
    Other more specific rewrites have been added to the simpset in their place.
    If the old behaviour is desired in a script file, the following will restore it

           val _ = augment_srw_ss
                    [rewrites [listTheory.DROP_def, listTheory.TAKE_def]]

*   The rewrite that takes `LENGTH l = 0` to `l = []` (as well as that which does the same thing to `0 = LENGTH l`) is now an automatic simplification in `srw_ss`.

*   The command-line options to the `build` tool have changed in some of their details.
    The standard usage by most users, which is to simply type `build` with no options at all, behaves as it did previously.
    For details on the options that are now handled, see the output of `build -h`.

*   The associativity and precedence level of the finite-map composition operators (of which there are three: `f_o_f`, `f_o` and `o_f`) have been changed to match that of normal function composition (infix `o`, or `∘`), which is a right-associative infix at precedence level 800.
    This level is tighter than exponentiation, multiplication and addition.
    This also matches the syntactic details for relation composition (which is written `O`, or `∘ᵣ`).
    If this causes problems within a script file, the old behaviour can be restored with, for example:

           val _ = set_fixity "o_f" (Infixl 500)

    This call will change the grammar used in all descendant theories as well; if the change is wanted only for the current script, use `temp_set_fixity` instead.

*   The tactic `ID_EX_TAC` has been moved from module `Q` to `Tactic`.

*   The tactic `Q.GENL` now processes its list of arguments (corresponding to variable names) in the same way as `GENL`.
    If one writes ``Q.GENL [`a`, `b`, `c`] th``, the result will be a theorem with conclusion `!a b c. <concl-of-th>`, rather than `!c b a. <concl-of-th>`.

*   The constant `words$word_sdiv` has been renamed to `words$word_quot` and `words$word_srem` has been renamed to `words$word_rem`.
    The constant `words$word_smod` has been moved to `integer_word$word_smod` and has been given a simpler definition.  (There is also a new constant `integer_word$word_sdiv` whose definition differs from the old `words$word_sdiv`.)

*   The `--` function for doing term-parsing (typically written as, *e.g.*, ``(--`p /\ q`--)``) has been removed so that the `--` name can be used as an infix set-difference operator.
    We have long preferred either ``Term`p /\ q` ``, or ``` ``p /\ q`` ```, or `“p /\ q”` for invoking the term-parser.

* * * * *

<div class="footer">
*[HOL4, ??????](http://hol-theorem-prover.org)*

[Release notes for the previous version](kananaskis-11.release.html)

</div>
