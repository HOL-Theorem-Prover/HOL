% Release notes for HOL4, Kananaskis-10

<!-- search and replace ?????? strings corresponding to release name -->
<!-- indent code within bulleted lists to column 11 -->

(Released: 10 November 2014)

We are pleased to announce the Kananaskis-10 release of HOL 4.

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

* Our *TUTORIAL* and *LOGIC* manuals are now available in Italian translations.  Work on the *DESCRIPTION* manual is also far advanced. Many, many thanks to Domenico Masini for doing this work.

* The abbreviation tactics (`Q.ABBREV_TAC` and others) now handle abstractions as abbreviations better.  In particular, if one sets up an abstraction as an abbreviation (*e.g.*, ``Q.ABBREV_TAC `f = (λn. 2 * n + 10)` ``), then the simplifier will find and replace instances not just of the abstraction itself (the old behaviour), but also instances of applications of the abstraction to arguments.  For example, given the abbreviation for `f` above, the simplifier would turn a goal such as `2 * (z + 1) + 10 < 100` into `f (z + 1) < 100`.

* The `MAX_SET` function in `pred_setTheory` is now defined (to have value `0`) on the empty set.

* There is an alternative syntax for specifying datatypes.  Instead of the `Hol_datatype` entry-point, one can also use `Datatype`, which takes a slightly different syntax, inspired by Haskell.  This does away with the use of the (somewhat confusing) `of` and `=>` tokens.

    For example, one would define a simple type of binary tree with

           Datatype`tree = Lf num | Node tree tree`

    If the arguments to a constructor are not just simple types (expressible as single tokens), then they need to be enclosed in parentheses.  For example:

           Datatype`mytype = Constr mytype ('a -> bool) | BaseCase`

    The `Hol_datatype` entry-point can continue to be used.  However, the LaTeX output of `EmitTeX` uses the new format, and the various `DATATYPE` constructors used in the `EmitML` module take quotations in the new format, rather than the old.

* The arithmetic decision procedure for natural numbers will now prove slightly more goals by doing case-splits on boolean sub-terms that are not in the Presburger subset.  This means that goals such as

           0 < y ⇒ x < x + (if P then y else y + 1)

    are now provable.

* The Vim mode for HOL now supports multiple simultaneous sessions. See its `README` for details.

* Many of the standard libraries now provide an `add_X_compset : compset -> unit` (*e.g.*, `add_pred_set_compset`) to ease building of custom call-by-name evaluation conversions that don't, like `EVAL`, include everything in `the_compset()`.

* `Holmake` has a new function, `wildcard` which allows expansion of “glob” patterns (*e.g.*, `*Script.sml`) into lists of matching filenames.

* The standard pretty-printer now annotates constants with their types as well as variables.  (Note that these annotations are typically only visible by using mouse-over tooltips in the emacs mode.)  The annotation also includes the constant’s real name, in the form `thy$name`, making overloads easier to tell apart.

    For example, this means that it is possible to have integers, reals and numbers all in scope, to write something like `MAP (+)`, and to then see what constants are involved by using the mouse.  (See [Github issue #39](https://github.com/HOL-Theorem-Prover/HOL/issues/39).)

*   Unicode is handled slightly better on Windows systems.  By default, the pretty-printer avoids printing with Unicode characters there, but can still parse Unicode input successfully.  This is important because many of the examples distributed with HOL use Unicode characters in their scripts (nothing in `src/` does).  This behaviour can be adjusted by toggling the `PP.avoid_unicode` trace.  On Windows this trace is initialised to true; elsewhere it is initialised to false.

Bugs fixed:
-----------

* `Holmake` was unnecessarily quiet when it compiled certain SML files.

* The “munging” code for turning HOL into LaTeX now does a better job of rendering data type definition theorems.  (This change is independent of the new underlying syntax described earlier.)

* Pretty-printers added to the system with `add_user_printer` weren’t having terms-to-be-printed tested against the supplied patterns (except by the gross approximation provided by the built-in term-net structure).  Thanks to Ramana Kumar for the [bug report](https://github.com/mn200/HOL/issues/172).

* Character literals weren’t pretty-printing to LaTeX.  We also improved the handling of string literals.  Thanks to Ramana Kumar for the [bug reports](http://github.com/HOL-Theorem-Prover/HOL/issues/190).

* Piotr Trojanek found and fixed many documentation bugs in our various manuals.

* The `remove_rules_for_term` and `temp_remove_rules_for_term` functions tended to remove rules for binders as well as the desired rules.

New theories:
-------------

* A theory of “list ranges” (`listRangeTheory`).  A range is a term written `[ lo ..< hi ]`, meaning the list consisting of the (natural) numbers from `lo` up to, but not including, `hi`.  The theory comes with some basic and obvious theorems, such as

           MEM i [lo ..< hi] ⇔ lo ≤ i ∧ i < hi

    and

           LENGTH [lo ..< hi] = hi - lo

* A new development in `src/floating-point`, which is a reworking of the theories in  `src/float`. Key differences are listed below.

    1. The data representation:

        - The old `ieeeTheory` uses a pair ` ``:num # num`` ` to represent the exponent and fraction widths and a triple ` ``:num # num # num`` ` to represent sign, exponent and fraction values.

        - The new `binary_ieeeTheory` makes use of HOL records and bit-vectors. The floating-point type ` ``:(α, β) float`` ` has values of the form

                  <| Sign : word1; Exponent : β word; Significand : α word |>

            The fraction and exponent widths are now constrained by the type, which facilitates type-checking and avoids having to pass size arguments to operations.

    2. The new development now supports standard bit-vector encoding schemes. The theory `machine_ieeeTheory` defines floating-point operations over 16-bit, 32-bit and 64-bit values. For example, the 16-bit floating point operations are defined by mapping to and from the type ``:(10, 5) float``, which is given the type abbreviation ``:half``. Theories for other sizes can be built using `machine_ieeeLib.mk_fp_encoding`.

    3. There is now syntax support via the structures `binary_ieeeSyntax` and `machine_ieeeSyntax`.

    4. Ground term evaluation is now supported for most operations. This can be enabled by loading `binary_ieeeLib`.

    5. The full development does not build under Moscow&nbsp;ML&nbsp;2.01, as it makes use of the `IEEEReal` and `PackRealBig` basis structures.

* A theory of “simple Patricia trees” (`sptreeTheory`). This theory implements a type `α sptree`, which is a finite map from natural numbers to values of type `α`.  (This type is not really a Patricia tree at all; for those, see the other theories in `src/patricia`.) Values of type `α sptree` feature efficient lookup, insertion, deletion and union (efficient when evaluated with `EVAL` or simplified).  Though there is a efficient (linear-time) fold operation, it does not iterate over the key-value pairs in key-order.

New tools:
----------

- New libraries `enumLib` and `fmapalLib` provide representations in `pred_set` and finite map types of enumerated constant sets and maps as minimum-depth binary search trees. A suitable total order on the set elements (map arguments) must be supplied, with a conversion for evaluating it; assistance with this is provided. The primary objective has been an `IN_CONV`, and a similar `FAPPLY_CONV`, operating with a logarithmic number of comparisons, but additional operations such as `UNION_CONV`, `INTER_CONV`, and `FUPDATE_CONV` are included and have reasonable asymptotic running times. A conversion `TC_CONV` implements Warshall’s algorithm for transitive closure of a binary relation (treated as a set-valued finite map).


Examples:
---------

- The `miniml` example has been removed. This work has evolved into the [CakeML project](http://cakeml.org).  That project’s `git` repository contains all of the material that was once in the HOL distribution, and, given its continuing evolution, much more besides.


Incompatibilities:
------------------

- In `relationTheory`, the theorems `TC_CASES1` and `TC_CASES2` have been renamed to `TC_CASES1_E` and `TC_CASES2_E` respectively, where the `_E` suffix indicates that these are elimination rules.  In other words, these theorems are of the form `TC R x y ⇒ ...`.  This has been done so that new equivalences can be introduced under the old names.  For example, `TC_CASES1` now states

           TC R x z ⇔ R x z ∨ ∃y. R x y ∧ TC R y z

    This change makes the naming consistent with similar theorems `RTC_CASES1` and `RTC_CASES2` about the reflexive and transitive closure.

- A theorem stating

           ⊢ ¬(0 < n) ⇔ (n = 0)

    (for `n` a natural number) has been added to the automatic rewrites used by `SRW_TAC` and `srw_ss()`.

- Some new automatic rewrites from `pred_setTheory`:

    * `⊢ DISJOINT (x INSERT s) t ⇔ DISJOINT s t ∧ x ∉ t`  (and the version of this with `DISJOINT s (x INSERT t)` as the l.h.s.)
    * `⊢ ∀f s. INJ f ∅ s`
    * `⊢ ∀f s. INJ f s ∅ ⇔ (s = ∅)`

- The `add_binder` and `temp_add_binder` entry-points in `Parse` have been removed.  They are subsumed by `set_fixity <name> Binder` and `temp_set_fixity <name> Binder` respectively.  In addition, `add_binder` was broken, creating an unloadable theory on export.

- There is a new automatic rewrite from `oneTheory`:

           ⊢ ∀v:one. v = ()

    stating that every value in the type `one` (analogue of SML’s `unit` type) is equal to the designated value `()`.

- Constants that print to the TeX backend as symbolic identifiers (*e.g.*, non-alphanumeric tokens like `+`, `**`) are now annotated there with the `\HOLSymConst` command rather than `\HOLConst`.  The default behaviour of `\HOLSymConst` (defined in `holtexbasic.sty`) is to do nothing.

-   If
    * `Holmake` is called in a directory with a `Holmakefile`, **and**
    * that `Holmakefile` has at least one explicit target, **and**
    * `Holmake` is called with no command-line targets,

    **then:** `Holmake` will attempt to build *only* the first target in that `Holmakefile`. We believe that this will cause problems in only a relatively small number of scenarios. The advantage of this change is that it makes `Holmake` easier to control from a `Holmakefile`. It also makes `Holmake`’s behaviour rather more like that of normal `make`.

    One scenario, among others, where this change may cause problems is where Poly/ML users have set up a rule to create a HOL heap. The fix is to prepend something like the following to your `Holmakefile`:

           THYFILES = $(patsubst %Script.sml,%Theory.uo,$(wildcard *.sml))
           TARGETS = $(patsubst %.sml,%.uo,$(THYFILES))

           all: $(TARGETS) ...
           .PHONY: all

    so that `all` becomes the first target of the `Holmakefile`.  Any previous targets, such as HOL heaps, should be inserted where the `...` occurs above.

    Note that `Holmakefile`s that only include variable declarations such as `OPTIONS = ...`, `INCLUDES = ...`, and `HOLHEAP = ...` don’t have any targets at all, so that `Holmake`’s behaviour in such files’ directories will not change.


* * * * *

<div class="footer">
*[HOL4, Kananaskis-10](http://hol.sourceforge.net)*

[Release notes for the previous version](kananaskis-9.release.html)

</div>
