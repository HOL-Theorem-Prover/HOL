% Release notes for HOL4, ??????

<!-- search and replace ?????? strings corresponding to release name -->
<!-- indent code within bulleted lists to column 11 -->

(Released: xxxxxx)

We are pleased to announce the ????? release of HOL4.

Contents
--------

-   [New features](#new-features)
-   [Bugs fixed](#bugs-fixed)
-   [New theories](#new-theories)
-   [New tools](#new-tools)
-   [New examples](#new-examples)
-   [Incompatibilities](#incompatibilities)
-   [Deprecations](#deprecations)

New features
------------
-   `Theory` syntax now supports disabling the generation of documentation in `<thyname>Theory.sig` by following the theory name with the `[no_sig_docs]` annotation.
    Files that use this feature do not need to mention `Feedback.set_trace "TheoryPP.include_docs" 0` anymore.

-   Lists and finite-map updates (previously achieved with `LUPDATE v i l` and `fm |+ (k,v)` syntax) can now be written with a syntax using the “maps to” arrow and special bracket delimiters.
    For `LUPDATE v i l`, one can write `l❲i ↦ v❳`, and for `fm |+ (k,v)`, one can write `fm⟨k ↦ v⟩`.
    Moreover, such updates can be chained into lists of updates between the brackets.
    For example, `fm⟨k1 ↦ v1; k2 ↦ v2⟩` represents `fm |+ (k2,v2) |+ (k1,v1)`.

    Finally, the corresponding application/selection terms can be written with the brackets around the key values: `fm⟨k⟩` for `fm ’ k`, and `l❲i❳` for `EL i l`.
    The old syntax continues to work in both cases, but the new forms are preferred when terms are printed.

Bugs fixed
----------

-   Three kernel bugs (github issues [#1838](https://github.com/HOL-Theorem-Prover/HOL/issues/1838), [#1839](https://github.com/HOL-Theorem-Prover/HOL/issues/1839), and [#1840](https://github.com/HOL-Theorem-Prover/HOL/issues/1840)) in CV-compute were fixed.
    Thanks to Ramana Kumar for finding these!

New theories
------------

New tools
---------

New examples
------------

-   The LaTeX munging technology has a tutorial document in the `examples/latex-generation` directory.

Incompatibilities
-----------------

-   The return types of `parse_term.mk_prec_matrix`, `type_grammar.parse_map`, `type_grammar.privileged_abbrevs`
    have been changed to return maps of type HOLdict instead of Binarymap.

-   `Preterm.eq` has been replaced with `Preterm.veq` which returns `true` if and only if the two arguments are variables with the same names and types.

-   We have implemented a new policy forbidding theory names from being SML or HOL keywords (*e.g.,* `case`, `while`, `of`, …, `Theorem`, `Theory`, `Definition`, …).
    The theories `while` and `functor` have been renamed to `While` and `category_functor`, respectively, in accordance with this.

-   The `examples/fun-op-sem` directory has been renamed `examples/pl-semantics`.

-   The `examples/balanced_bst` directory has been renamed `examples/data-structures/balanced_bst`;
    the script file `examples/zipper/zipperScript.sml` has been moved to `examples/data-structures`;
    the script file `examples/balanced_bst/AVL_treeScript.sml` has been moved to a directory of its own at `examples/data-structures/AVL_tree`.

-   The left-hand side of `LIST_REL_MAP2` has been changed from `LIST_REL (\a b. R a b) l1 (MAP f l2)` to
    `LIST_REL R l1 (MAP f l2)`. We do not expect this to break proof scripts, but document this change here just in case.

-   A few theorems (ended with `'`) in `real_sigmaTheory` are renamed to avoid naming conflicts
    with `realaxTheory`, or to better reflect their nature (see the table below for details.)
    In particular, users are recommended to *not* directly open `realaxTheory` (an intermediate
    theory for constructing real numbers), in which all useful theorems should be also covered by
   `realTheory` (under same or different theorem names).
  
|  Old name       | New name           | Statements                                    |
| --------------- | ------------------ | --------------------------------------------- |
| `REAL_LE_SUP'`  | `REAL_LE_SUP2`     | `!s a b y. y IN s /\ a <= y /\ (!x. x IN s ==> x <= b) ==> a <= sup s` |
| `REAL_LE_MUL'`  | `REAL_LE_MUL_NEG`  | `!x y. x <= 0 /\ y <= 0 ==> 0 <= x * y`       |
| `REAL_LT_MUL'`  | `REAL_LT_MUL_NEG`  | `!x y. x < 0 /\ y < 0 ==> 0 < x * y`          |
| `REAL_LT_LMUL'` | `REAL_LT_LMUL_NEG` | `!x y z. x < 0 ==> (x * y < x * z <=> z < y)` | 
| `REAL_LT_RMUL'` | `REAL_LT_RMUL_NEG` | `!x y z. z < 0 ==> (x * z < y * z <=> y < x)` |

-   For better compatibility with HOL Light (making code-porting easier), arithmetic theory’s `GREATER_EQ` theorem (stating *m ≥ n ⇔ n ≤ m*) is now also available in that theory under the name `GE`.

-   The function `Parse.remove_user_printer` now returns `unit`.


Deprecations
------------

-   `Triviality` has been deprecated and may be removed in the future.
    Please update theorems of the form `Triviality foo` and `Triviality foo[..]` to
    `Theorem foo[local]` and `Theorem foo[local,..]` respectively to avoid future breakage.

* * * * *

<div class="footer">
*[HOL4, ?????](http://hol-theorem-prover.org)*

[Release notes for the previous version](trindemossen-2.release.html)

</div>
