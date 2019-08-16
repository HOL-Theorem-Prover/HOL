% Release notes for HOL4, ??????

<!-- search and replace ?????? strings corresponding to release name -->
<!-- indent code within bulleted lists to column 11 -->

(Released: ???)

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

*   We have implemented new syntaxes for `store_thm` and `save_thm`, which better satisfy the recommendation that `name1` and `name2` below should be the same:

           val name1 = store_thm("name2", tm, tac);

    Now we can remove the “code smell” by writing

           Theorem name: term-syntax
           Proof tac
           QED

    which might look like

           Theorem name:
             ∀x. P x ⇒ Q x
           Proof
             rpt strip_tac >> ...
           QED

    This latter form must have the `Proof` and `QED` keywords in column 0 in order for the lexing machinery to detect the end of the term and tactic respectively.
    Both forms map to applications of `Q.store_thm` underneath, with an ML binding also made to the appropriate name.
    Both forms allow for theorem attributes to be associated with the name, so that one can write

           Theorem ADD0[simp]: ∀x. x + 0 = x
           Proof tactic
           QED

    Finally, to replace

           val nm = save_thm(“nm”, thm_expr);

    one can now write

           Theorem nm = thm_expr

    These names can also be given attributes in the same way.

-   Relatedly, there is a similar syntax for making definitions.
    The idiom is to write

           Definition name[attrs]:
             def
           End

    Or

           Definition name[attrs]:
             def
           Termination
             tactic
           End

    The latter form maps to a call to `tDefine`; the former to `xDefine`.
    In both cases, the `name` is taken to be the name of the theorem stored to disk (it does *not* have a suffix such as `_def` appended to it), and is also the name of the local SML binding.
    The attributes given by `attrs` can be any standard attribute (such as `simp`), and/or drawn from `Definition`-specific options:

    -   the attribute `schematic` alllows the definition to be schematic;
    -   the attribute `nocompute` stops the definition from being added to the global compset used by `EVAL`
    -   the attribute `induction=iname` makes the induction theorem that is automatically derived for definitions with interesting termination be called `iname`.
        If this is omitted, the name chosen will be derived from the `name` of the definition: if `name` ends with `_def` or `_DEF`, the induction name will replace this suffix with `_ind` or `_IND` respectively; otherwise the induction name will simply be `name` with `_ind` appended.

    Whether or not the `induction=` attribute is used, the induction theorem is also made available as an SML binding under the appropriate name.
    This means that one does not need to follow one’s definition with a call to something like `DB.fetch` or `theorem` just to make the induction theorem available at the SML level.

-   Similarly, there are analogous `Inductive` and `CoInductive` syntaxes for defining inductive and coinductive relations (using `Hol_reln` and `Hol_coreln` underneath).
    The syntax is

           Inductive stem:
              quoted term material
           End

    or

           CoInductive stem:
              quoted term material
           End

    where, as above, the `Inductive`, `CoInductive` and `End` keywords must be in the leftmost column of the script file.
    The `stem` part of the syntax drives the selection of the various theorem names (*e.g.*, `stem_rules`, `stem_ind`, `stem_cases` and `stem_strongind` for inductive definitions) for both the SML environment and the exported theory.
    The actual names of new constants in the quoted term material do not affect these bindings.

-   Finally, there are new syntaxes for `Datatype` and type-abbreviation.
    Users can replace ``val _ = Datatype`...` `` with

           Datatype: ...
           End

    and `val _ = type_abbrev("name", ty)` with

           Type name = ty

    if the abbreviation should introduce pretty-printing (which would be done with `type_abbrev_pp`), the syntax is

           Type name[pp] = ty

    Note that in both `Type` forms the `ty` is a correct ML value, and may thus require quoting.
    For example, the `set` abbreviation is established with

           Type set = “:α -> bool”

-   Holmake now understands targets whose suffixes are the string `Theory` to be instructions to build all of the files associated with a theory.
    Previously, to specifically get `fooTheory` built, it was necessary to write

           Holmake fooTheory.uo

    which is not particularly intuitive.

    Thanks to Magnus Myreen for the feature suggestion.

-   Users can now remove rewrites from simpsets, adjusting the behaviour of the simplifier.
    This can be done with the `-*` operator

           SIMP_TAC (bool_ss -* [“APPEND_ASSOC”]) [] >> ...

    or with the `Excl` form in a theorem list:

           simp[Excl “APPEND_ASSOC”] >> ...

    The stateful simpset (which is behind `srw_ss()` and tactics such as `simp`, `rw` and `fs`) can also be affected more permanently by making calls to `delsimps`:

           val _ = delsimps [“APPEND_ASSOC”]

    Such a call will affect the stateful simpset for the rest of the containing script-file and in all scripts that inherit this theory.
    As is typical, there is a `temp_delsimps` that removes the rewrite for the containing script-file only.

-   Users can now require that a simplification tactic use particular rewrites.
    This is done with the `Req0` and `ReqD` special forms.
    The `Req0` form requires that the goalstate(s) pertaining after the application of the tactic have no sub-terms that match the pattern of the theorems’ left-hand sides.
    The `ReqD` form requires that the number of matching sub-terms should have decreased.
    (This latter is implicitly a requirement that the original goal *did* have some matching sub-terms.)
    We hope that both forms will be useful in creating maintainable tactics.
    See the *DESCRIPTION* manual for more details.

    Thanks to Magnus Myreen for this feature suggestion ([Github issue](https://github.com/HOL-Theorem-Prover/HOL/issues/680)).

-   The `emacs` editor mode now automatically switches new HOL sessions to the directory of the (presumably script) file where the command is invoked.
    Relatedly there is a backwards incompatibility: the commands for creating new sessions now also *always* create fresh sessions (previously, they would try to make an existing session visible if there was one running).

-   The `emacs` mode’s `M-h H` command used to try to send the whole buffer to the new HOL session when there was no region high-lighted.
    Now the behaviour is to send everything up to the cursor.
    This seems preferable: it helps when debugging to be able to have everything up to a problem-point immediately fed into a fresh session.
    (The loading of the material (whole prefix or selected region) is done “quietly”, with the interactive flag false.)

-   Holmakefiles can now refer to the new variable `DEFAULT_TARGETS` in order to generate a list of the targets in the current directory that Holmake would attempt to build by default.
    This provides an easier way to adjust makefiles than that suggested in the [release notes for Kananaskis-10](http://hol-theorem-prover.org/kananaskis-10.release.html).

-   String literals can now be injected into other types (in much the same way as numeric literals are injected into types such as `real` and `rat`).
    Either the standard double-quotes can be used, or two flavours of guillemet, allowing *e.g.*, `“‹foo bar›”`, and `“«injected-HOL-string\n»”`.
    Ambiguous situations are resolved with the standard overloading resolution machinery.
    See the *REFERENCE* manual’s description of the `add_strliteral_form` function for details.

-   The `Q.SPEC_THEN` function (also available as `qspec_then` in `bossLib`) now type-instantiates provided theorems à la `ISPEC`, and tries all possible parses of the provided quotation in order to make this work.
    The `Q.ISPEC_THEN` function is deprecated.

Bugs fixed:
-----------

*   `smlTimeout.timeout`: The thread attributes are now given which eliminates concurrency issues during TacticToe recording.
    This function now raises the exception `FunctionTimeout` instead of `Interrupt` if the argument function exceeds the time limit.

New theories:
-------------

*   `real_topologyTheory`: a rather complete theory of Elementary
    Topology in Euclidean Space, ported by Muhammad Qasim and Osman
    Hasan from HOL-light (up to 2015). The part of General Topology
    (independent of `realTheory`) is now available at
    `topologyTheory`; the old `topologyTheory` is renamed to
    `metricTheory`.

    There is a minor backwards-incompatibility: old proof scripts using
    the metric-related results in previous `topologyTheory` should now
    open `metricTheory` instead. (Thanks to Chun Tian for this work.)

*   `nlistTheory`: a development of the bijection between lists of natural numbers and natural numbers.
    Many operations on lists transfer across to the numbers in obvious ways.
    The functions demonstrating the bijection are

           listOfN : num -> num list

    and

           nlist_of : num list -> num

    This material is an extension of a basic treatment that was already part of the computability example.
    Thanks to Elliot Catt and Yiming Xu for help with this theory’s development.

*   `bisimulationTheory`: a basic theory of bisimulation (strong and weak)
    defined on general labeled transitions (of type `:'a->'b->'a->bool`),
    mostly abstracted from `examples/CCS`.
    (Thanks to James Shaker and Chun Tian for this work.)

New tools:
----------

*   HolyHammer is now able to exports HOL4 formulas to the TPTP formats: TFF0, TFF1, THF0 and THF1.
    Type encodings have been adapted from the existing FOF translation to make use of the increase in type
    expressivity provided by these different formats.

*   It is now possible to train feedforward neural networks with `mlNeuralNetwork` and tree neural networks with `mlTreeNeuralNetwork`.
    The shape of a tree neural network is described by a term, making it handy to train
    functions from terms to real numbers.

*   An implementation of Monte Carlo tree search relying on an existing policy and value is now provided in `psMCTS`.
    The policy is a function that given a particular situation returns a prior probability for each possible choice.
    The value is a function that evaluates how promising a situation is by a real number between 0 and 1.

New examples:
-------------

*   [`examples/logic/folcompactness`] A port of some material from HOL Light ([this commit](https://github.com/jrh13/hol-light/commit/013324af7ff715346383fb963d323138)), about compactness and canonical models for First Order Logic.
    This is work described in John Harrison’s [*Formalizing Basic First Order Model Theory*](https://doi.org/10.1007/BFb0055135).

    Results include

           ⊢ INFINITE 𝕌(:α) ∧ ffinsat (:α) s ⇒ satisfiable (:α) s

    and

           ⊢ INFINITE 𝕌(:α) ⇒
               (entails (:α) Γ ϕ ⇔ ∃Γ₀. FINITE Γ₀ ∧ Γ₀ ⊆ Γ ∧ entails (:α) Γ₀ ϕ)



Incompatibilities:
------------------

*   The `term` type is now declared so that it is no longer what SML refers to as an “equality type”.
    This means that SML code that attempts to use `=` or `<>` on types that include terms will now fail to compile.
    Unlike in Haskell, we cannot redefine the behaviour of equality and must accept the SML implementation’s best guess as to what equality is.
    Unfortunately, the SML equality on terms is *not* correct.
    As has long been appreciated, it distinguishes `“λx.x”` and `“λy.y”`, which is bad enough.
    However, in the standard kernel, where explicit substitutions may be present in a term representation, it can also distinguish terms that are not only semantically identical, but also even print the same.

    This incompatibility will mostly affect people writing SML code.
    If broken code is directly calling `=` on terms, the `~~` infix operator can be used instead (this is the tupled version of `aconv`).
    Similarly, `<>` can be replaced by `!~`.
    If broken code includes something like `expr <> NONE` and `expr` has type `term option`, then combinators from `Portable` for building equality tests should be used.
    In particular, the above could be rewritten to

           not (option_eq aconv expr NONE)

    It is possible that a tool will want to compare terms for exact syntactic equality up to choice of bound names.
    The `identical` function can be used for this.
    Note that we strongly believe that uses of this function will only occur in very niche cases.
    For example, it is used just twice in the distribution as of February 2019.

    There are a number of term-specific helper functions defined in `boolLib` to help in writing specific cases.
    For example

           val memt : term list -> term -> bool
           val goal_eq : (term list * term) -> (term list * term) -> bool
           val tassoc : term -> (term * ‘a) list -> ‘a
           val xtm_eq : (‘’a * term) -> (‘’a * term) -> bool

*   The `Holmake` tool now behaves with the `--qof` behaviour enabled by default.
    This means that script files which have a tactic failure occur will cause the building of the corresponding theory to fail, rather than having the build continue with the theorem “cheated”.
    We think this will be less confusing for new users.
    Experts who *do* want to have script files continue past such errors can use the `--noqof` option to enable the old behaviour.

*   When running with Poly/ML, we now require at least version 5.7.0.

*   The `type_abbrev` function now affects only the type parser.
    The pretty-printer will not use the new abbreviation when printing types.
    If the old behaviour of printing the abbreviations as well as parsing them is desired, the new entrypoint `type_abbrev_pp` should be used.

*   The `Globals.priming` reference variable has been removed.
    All priming done by the kernel is now by appending extra prime (apostrophe) characters to the names of variables.
    This also means that this is the only form of variation introduced by the `variant` function.
    However, there is also a new `numvariant` function, which makes the varying function behave as if the old `Globals.priming` was set to `SOME ""` (introduces and increments a numeric suffix).

*   We have made equality a tightly binding infix rather than a loose one.
    This means that a term like `“p = q ∧ r”` now parses differently, and means `“(p = q) ∧ r”`, rather than `“p = (q ∧ r)”`.
    For the weak binding, the “iff” alternative is probably better; thus: `“p <=> q ∧ r”` (or use the Unicode `⇔`).
    To fix a whole script file at one stroke, one can revert to the old, loosely binding equality with

           val _ = ParseExtras.temp_loose_equality()

    To fix a whole family of theories that inherit from a few ancestors, add

           val _ = ParseExtras.loose_equality()

    to the ancestral script files, and then the reversion to the old style of grammar will be inherited by all subsequent theories as well.

*   By default, goals are now printed with the trace variable `"Goalstack.print_goal_at_top"` set to false.
    This means goals now print like

            0.  p
            1.  q
           ------------------------------------
                r

    The motivation is that when goal-states are very large, the conclusion (which we assume is the most important part of the state) runs no risk of disappearing off the top of the screen.
    We also believe that having the conclusion and most recent assumption at the bottom of the screen is easier for human eyes to track.
    The trace variable can be changed back to the old behaviour with:

           val _ = set_trace "Goalstack.print_goal_at_top" 1;

    This instruction can be put into script files, or (better) put into your `~/.hol-config.sml` file so that all interactive sessions are automatically adjusted.

*   This is arguably also a bug-fix: it is now impossible to rebind a theorem to a name that was associated with a definition, and have the new theorem silently be added to the `EVAL` compset for future theories’ benefit.
    In other words, it was previously possible to do

           val _ = Define`foo x = x + 1`;
           EVAL “foo 6”;     (* returns ⊢ foo 6 = 7 *)

           val _ = Q.save_thm (“foo_def”, thm);

    and have the effect be that `thm` goes into `EVAL`’s compset in descendent theories.

    Now, when this happens, the change to the persistent compset is dropped.
    If the user wants the new `foo_def` to appear in the `EVAL`-compset in future theories, they must change the call to `save_thm` to use the name `"foo_def[compute]"`.
    Now, as before, the old `foo_def` cannot be seen by future theories at all, and so certainly will not be in the `EVAL`-compset.

*   In some circumstances, the function definition machinery would create a theorem called `foo_def_compute`.
    (Such theorems would be rewrites for functions that were defined using the `SUC` constructor, and would be useful for rewriting with numeral arguments.)
    Now, such theorems are called `foo_compute`.
    As before, such theorems are automatically added to `EVAL`’s built-in compset.

*   The global toggle `allow_schema_definition` has turned into a feedback trace variable.
    Users typically use the `DefineSchema` entrypoint and can continue to do so.
    Users can also pass the `schematic` attribute with the new `Definition` syntax (see above).
    Programmers should change uses of `with_flag` to `Feedback.trace`.

*   The theorem `MEM_DROP` in `listTheory` has been restated as

           MEM x (DROP n ls) ⇔ ∃m. m + n < LENGTH ls ∧ x = EL (m + n) ls

    The identically named `MEM_DROP` in `rich_listTheory` has been deleted because it is subsumed by `MEM_DROP_IMP` in `rich_listTheory`, which states

           MEM x (DROP n ls) ⇒ MEM x ls

*   The `drule` family of tactics (and the underlying `mp_then`) now generalise the implicational theorem argument (with `GEN_ALL`) before looking for instantiations.
    If the old behaviour is desired, where free variables are fixed, replacing `drule` with `FREEZE_THEN drule` will stop generalisation of all the implicational theorem’s variables.
    Unfortunately, this may then prevent the matching from occurring at all.
    In this situation (where some free variables need to be instantiated to make the match go through and the remainder have to be appear as new “local constants” serendipitously linking up with existing free variables in the goal, or if there are type variables that need to be instantiated), `drule` may need to be replaced with

           drule_then (qspecl_then [‘a’, ‘b’,...] mp_tac)

    where `‘a’`, `‘b’` *etc.* respecialise the original theorem.

    Alternatively, there is a more involved code that more robustly reimplements the old behaviour [available as part of the CakeML project](https://github.com/CakeML/cakeml/blob/349c6adc73366d9c689a0c8bd11d85c75fd0f71b/misc/preamble.sml#L534-L572).

* * * * *

<div class="footer">
*[HOL4, ??????](http://hol-theorem-prover.org)*

[Release notes for the previous version](kananaskis-12.release.html)

</div>
