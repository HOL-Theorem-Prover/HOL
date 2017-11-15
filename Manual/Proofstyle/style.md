% Writing Large Proofs

The following describes how to write large proofs in HOL4.
It pays particular attention to writing proofs so that they are robust and easy to maintain.
It also “pushes” a particular proof style in terms of aspects such as

* tactic selection
* indentation
* naming

These aspects are less important, and can be varied, but do result in consistent documents that are easy to work with.

# The Problem

Bad proofs are a maintenance nightmare.
For better or worse, maintenance of HOL4 proofs involves interactive replay of proof scripts and a lot of cut-and-paste (for all that this is probably ameliorated through editor-support).

# Basic Commandments

*   **Don’t try to be too smart**. Overly tricky proofs are hard for future readers to debug.
    Things that probably count as “too smart” include

    -   Handling too many cases with one linear stretch of tactic.
        Clearly this is a matter of degree.
        Starting a proof with something like

            Induct >> simp[] >> rpt strip_tac >> tac1 >> tac2

        is probably pretty reasonable.
        On the other hand, a long chain that handles multiple cases all at once, perhaps with tricky uses of `TRY`, is extremely hard to debug, because there is no indication from the text where the replayer should expect to see particular sub-goals get resolved.

        It is possible that `TRY` chains where the first thing in the `TRY`-ed tactic is a `rename` tactic or similar, and where the tactic then completely solves those cases, can be handled reasonably: the use of `rename` makes it clear what sub-goals are expected to be worked over.

    -   Factoring with tactics rather than theorems.
        It can occasionally be tempting to define a big repeated tactic in the following way

            val mytac = tac1 >> tac2 >> .... >>

            val result = store_thm("result",
              ``...``,
              ... >| [
                ... mytac ... ,
                ... mytac ...
              ]

        Again, this is a matter of degree.
        But, if `mytac` is very large, stepping through it is typically going to be very painful.
        It’s better in this sort of situation to strive to capture the logic of the situation in a theorem.

*   **Don’t ignore parser warnings** In particular, if there is a message about multiple possible overloading resolutions, make very sure you understand why this is, and then make *even more sure* that there is no way that the parser’s choice of resolution can possibly change.

*   **Don’t rely on generated names** This is so important that it has a section to itself below.

# Superficial Aesthetic Rules

1. Prefer the lower-case versions of tactics.
   This means `rpt strip_tac` instead of `REPEAT STRIP_TAC`.

2. Limit to 80 columns

2. Use indentation. Don’t put goals *or* tactics onto one long line (see above), and when breaking lines, do it in logically sensible places.
   The HOL pretty-printer does a reasonable indentation job with terms; follow its style.
   For example

    *    Indent after forall-blocks. Thus

            ∀x y z.
               R x y ==> Q (f x) z

2.   **Don’t use TABs** Indentation with TABs depends on editor settings for it effect. TABs are only permissible in (Hol)makefiles.

2.  Use two-space indentation

3.  Put the `THEN` connective at the end of the line.
    Thus:

        tac1 >> tac2 >> tac3 >> tac4 >>
        tac5 >> tac6 >> ...

    Putting the connective at the start of the line just makes it harder to see the semantically interesting material (the tactic) as one’s eye scans from left to right.

# More Important Layout Rules

1.  Indent tactics underneath `THENL` (or `>|`)
    Thus

        tac >| [
          tac1a >> tac1b >> ...,
          tac2a >> tac2b >> ...
        ]

    This makes it obvious to the reader that a case-split occurs.

5.  Separate large successive tactics in `THENL` blocks with empty lines or comma lines.
    Thus (illustrating both approaches):

        tac >| [
          tac1a >> tac1b >>
          tac1c >> tac1d,

          tac2a >> tac2b >>
          tac2c >> tac2d
          ,
          tac3a >> tac3b >>
          tac3c >> tac3d
        ]

    This is important because it makes it easy for the replayer to find where the tactic blocks are, which is a prerequisite to cutting and pasting.

6.  With large multi-way branching, prefer `>-` (or `THEN1`) to `>|`.
    *   Because one cannot cut-and-paste into the middle of `>-` blocks, it is reasonable to highlight their presence by putting the `>-` at the start of the line:

            tac1 >> tac2 >> tac3
            >- ( (* case 1 *) tac4 >> tac5 >> tac6 >>
                tac7) >>
            ... rest of proof ...

    *   To make it easier to cut-and-paste over multiple sub-goals, whether from the start, or within a proof, split large conjunctive goals up one conjunct at a time:

            tac >> conj_tac
            >- ((* conj 1 *) ... tactics
                ...) >> conj_tac
            >- ((* conj 2 *) ... tactics
                ...) >> conj_tac
            >- ((* conj 3 *) ... tactics
                ...) >> conj_tac
            >- ...

        Given this, it is possible to cut-and-paste from the start of the tactic to any of the sub-goals in one fell swoop, and to then move from a completed sub-goal to any of the subsequent sub-goals, again by just selecting one region of text to feed to the HOL process.

7.  Use a semicolon at the end of every declaration. Rationale: if an exception is raised when running the file interactively, previous successful bindings are kept.

# Handling (Generated) Names
  HOL's scheme for generating names may change in future versions.
  Therefore it makes sense to carefully rename variables that have been generated by HOL and should be used in a proof script.
  Take the proof goal:

    0. a = P b1 b2 b3
    1. P b1 b2 b3
    2.  ...
    ###############
     Q a b1 e

  Assume that the names ```b1 b2 b3``` have been generated by HOL4.
  To change their names one can simply write

    rename1 `a = P b c d`

This will change the goal into

    0. a = P b c d
    1. P b c d
    2.  ...
    ###############
     Q a b e

Patterns can be used as placeholders for sub-terms that should not be renamed, e.g. ```rename1 `_ = P b c d` ```.
Furthermore note that HOL4 will not capture any of the already existing variables.

    0. a = P b1 b2 b3
    1. P b1 b2 b3
    2. P b c d
    3.  ...
    ###############
    Q a b1 e

Applying ```rename1 a = P b c d``` will fail since this would make the values ```b1 b2 b3``` indistinguishable from ```b c d```.

# Concrete Tips

- Don’t `open` modules in the middle of files.
  Move all `open` declarations to the top of your script file.
  This means that all libraries that the non-interactive session loads before script execution will also be loaded when the user interactively replays the session.

- Don’t use `local-in-end` except on very small scales.
  Large `local` blocks are very hard to cut-and-paste into.
