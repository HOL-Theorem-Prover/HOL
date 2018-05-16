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
-   [Examples](#examples)
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


Bugs fixed:
-----------

*   Pretty-printing of record type declarations to TeX now works even if there are multiple types with the same name (necessarily from different theory segments) in the overall theory.

New theories:
-------------

New tools:
----------

New examples:
---------

*   We have resurrected Monica Nesi’s CCS example (from the days of HOL88), thanks to work done by Chun Tian.

Incompatibilities:
------------------

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
    See the *Reference* manual for more details.

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
