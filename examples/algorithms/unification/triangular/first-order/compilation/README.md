# Motivation

Unify is a painful function to deal with, even once defined, because of the annoying side condition on the input substitution map.  This parameter is usually `s` (for σ), and the condition is `wfs s`. These occur not only with `unify`, but also in the functions that `unify` calls.

These side-conditions are often present in the correctness statements, which is fine, but sometimes ‘contaminate’ the theorems characterising the functions as well, and these recursion equations are how we'd like to present the function to other tools for the purpose of compilation.

If the equations are not recursive, then they will be of the form

    wfs s ==> f s args = ...

and so we can define an `f’` that repeats the above without the side-condition, and then we compile `f’`, retaining a correctness statement that says

    wfs s ==> f’ s args = f s args

In a recursive setting, honesty forces one to write

     f s args = if wfs s then .... f s’ args’ ....
                else ARB

and a naive translation ends up creating a function that repeatedly checks `wfs s` with every recursive call, even though we have established elsewhere that this is not necessary.

The second issue to deal with is the fact that the substitution maps are finite maps, and we’d prefer to have these be something more concrete when compiling. So, the basic strategy is to first replace these with sptrees. Doing this “automatically” with the transfer code creates another side condition on these values (that they be well-formed), but one more component to the side condition that will be being eliminated anyway is no big deal.

## Call-Graph to Consider

    unify ----> walk ----> vwalk
            |               ^
            |               |
            `-> oc ---------’

The `walk` function is not recursive, but the other three all are. (We’re  eliminating the `ext_s_check` function before starting this process.)

## Naming Schemes

The core functions are above.  After conversion to sptrees the names are the same with a leading ‘s’ (`sunify`, `svwalk` etc). When these functions are made tail-recursive without guards, the ultimate functions have the ‘s’ replaced with a ‘t’.

## Basic Strategy

1.  First use `transferLib` to eliminate the finite map.
    This is done in rmfmapScript.sml, producing `sunify` *et al.*
    The nice characterisations have names `sunify_thm`, `soc_thm` etc.

2.  Make recursive functions tail-recursive. (See below) This is not needed for svwalk, which is already tail-recursive.

3.  Remove tail-recursive guard, creating ‘t’ forms. The recursive characterisation of `f` has name `t<f>_thm`; the statement that this is correct (of form `sidecond ==> s<f> args = t<f> args’`) is `t<f>_correct`.

4.  Hand off to cv_compute.

## Conversion to Tail-Recursion

1. Define a continuation based version:

           kf_def |- kf args k = cwc (f args) k

2. Convert that to a nice version (using `contify_CONV` and custom simplification), `kf_thm`.

3. Use contification to make the continuation parameter concrete. For our examples, the cont type will be a list of some form. This is “interpreted” by a function of form `apply_<f>kont`. Through some magic this then turns into the main entry-point, creating a work-list function version of the original with name `k<f>wl`. (There are two of these in our example: `kunifywl` and `kocwl`.)
