## `Hol_defn`

``` hol4
bossLib.Hol_defn : string -> term quotation -> defn
```

------------------------------------------------------------------------

General-purpose function definition facility.

`Hol_defn` allows one to define functions, recursive functions in
particular, while deferring termination issues. `Hol_defn` should be
used when `Define` or `xDefine` fails, or when the context required by
`Define` or `xDefine` is too much.

`Hol_defn` takes the same arguments as `xDefine`.

`Hol_defn s q` automatically constructs termination constraints for the
function specified by `q`, defines the function, derives the specified
equations, and proves an induction theorem. All these results are
packaged up in the returned `defn` value. The `defn` type is best
thought of as an intermediate step in the process of deriving the
unconstrained equations and induction theorem for the function.

The termination conditions constructed by `Hol_defn` are for a function
that takes a single tuple as an argument. This is an artifact of the way
that recursive functions are modelled.

A prettyprinter, which prints out a summary of the known information on
the results of `Hol_defn`, has been installed in the interactive system.

`Hol_defn` may be found in `bossLib` and also in `Defn`.

### Failure

`Hol_defn s q` fails if `s` is not an alphanumeric identifier.

`Hol_defn s q` fails if `q` fails to parse or typecheck.

`Hol_defn` may extract unsatisfiable termination conditions when asked
to define a higher-order recursion involving a higher-order function
that the termination condition extraction mechanism of `Hol_defn` is
unaware of.

### Example

Here we attempt to define a quick-sort function `qsort`:

``` hol4
   - Hol_defn "qsort"
         `(qsort ___ [] = []) /\
          (qsort ord (x::rst) =
             APPEND (qsort ord (FILTER ($~ o ord x) rst))
               (x :: qsort ord (FILTER (ord x) rst)))`;

   <<HOL message: inventing new type variable names: 'a>>
   > val it =
       HOL function definition (recursive)

       Equation(s) :
        [...]
       |- (qsort v0 [] = []) /\
          (qsort ord (x::rst) =
           APPEND (qsort ord (FILTER ($~ o ord x) rst))
             (x::qsort ord (FILTER (ord x) rst)))

       Induction :
        [...]
       |- !P.
            (!v0. P v0 []) /\
            (!ord x rst.
               P ord (FILTER ($~ o ord x) rst) /\
               P ord (FILTER (ord x) rst) ==> P ord (x::rst))
              ==> !v v1. P v v1

       Termination conditions :
         0. WF R
         1. !rst x ord. R (ord,FILTER ($~ o ord x) rst) (ord,x::rst)
         2. !rst x ord. R (ord,FILTER (ord x) rst) (ord,x::rst)
```

In the following we give an example of how to use `Hol_defn` to define a
nested recursion. In processing this definition, an auxiliary function
`N_aux` is defined. The termination conditions of `N` are phrased in
terms of `N_aux` for technical reasons.

``` hol4
   - Hol_defn "ninety1"
       `N x = if x>100 then x-10
                       else N(N(x+11))`;

   > val it =
       HOL function definition (nested recursion)

       Equation(s) :
        [...] |- N x = (if x > 100 then x - 10 else N (N (x + 11)))

       Induction :
        [...]
       |- !P.
            (!x. (~(x > 100) ==> P (x + 11)) /\
                 (~(x > 100) ==> P (N (x + 11))) ==> P x)
            ==>
             !v. P v

       Termination conditions :
         0. WF R
         1. !x. ~(x > 100) ==> R (x + 11) x
         2. !x. ~(x > 100) ==> R (N_aux R (x + 11)) x
```

### Comments

An invocation of `Hol_defn` is usually the first step in a multi-step
process that ends with unconstrained recursion equations for a function,
along with an induction theorem. `Hol_defn` is used to construct the
function and synthesize its termination conditions; next, one invokes
`tgoal` to set up a goal to prove termination of the function. The
termination proof usually starts with an invocation of `WF_REL_TAC`.
After the proof is over, the desired recursion equations and induction
theorem are available for further use.

It is occasionally important to understand, at least in part, how
`Hol_defn` constructs termination constraints. In some cases, it is
necessary for users to influence this process in order to have correct
termination constraints extracted. The process is driven by so-called
congruence theorems for particular HOL constants. For example, suppose
we were interested in defining a 'destructor-style' version of the
factorial function over natural numbers:

``` hol4
   fact n = if n=0 then 1 else n * fact (n-1).
```

In the absence of a congruence theorem for the 'if-then-else' construct,
`Hol_defn` would extract the termination constraints

``` hol4
   0. WF R
   1. !n. R (n - 1) n
```

which are unprovable, because the context of the recursive call has not
been taken account of. This example is in fact not a problem for HOL,
since the following congruence theorem is known to `Hol_defn`:

``` hol4
   |- !b b' x x' y y'.
         (b = b') /\
         (b' ==> (x = x')) /\
         (~b' ==> (y = y')) ==>
         ((if b then x else y) = (if b' then x' else y'))
```

This theorem is interpreted by `Hol_defn` as an ordered sequence of
instructions to follow when the termination condition extractor hits an
'if-then-else'. The theorem is read as follows:

``` hol4
   When an instance `if B then X else Y` is encountered while the
   extractor traverses the function definition, do the following:

     1. Go into B and extract termination conditions TCs(B) from
        any recursive calls in it. This returns a theorem
        TCs(B) |- B = B'.

     2. Assume B' and extract termination conditions from any
        recursive calls in X. This returns a theorem
        TCs(X) |- X = X'. Each element of TCs(X) will have
        the form "B' ==> M".

     3. Assume ~B' and extract termination conditions from any
        recursive calls in Y. This returns a theorem
        TCs(Y) |- Y = Y'. Each element of TCs(Y) will have
        the form "~B' ==> M".

     4. By equality reasoning with (1), (2), and (3), derive

            TCs(B) u TCs(X) u TCs(Y)
             |-
            (if B then X else Y) = (if B' then X' else Y')

     5. Replace "if B then X else Y" by "if B' then X' else Y'".
```

The accumulated termination conditions are propagated until the
extraction process finishes, and appear as hypotheses in the final
result. In our example, context is properly accounted for in recursive
calls under either branch of an 'if-then-else'. Thus the extracted
termination conditions for `fact` are

``` hol4
   0. WF R
   1. !n. ~(n = 0) ==> R (n - 1) n
```

and are easy to prove.

Now we discuss congruence theorems for higher-order functions. A
'higher-order' recursion is one in which a higher-order function is used
to apply the recursive function to arguments. In order for the correct
termination conditions to be proved for such a recursion, congruence
rules for the higher order function must be known to the termination
condition extraction mechanism. Congruence rules for common higher-order
functions, e.g., `MAP`, `EVERY`, and `EXISTS` for lists, are already
known to the mechanism. However, at times, one must manually prove and
install a congruence theorem for a higher-order function.

For example, suppose we define a higher-order function `SIGMA` for
summing the results of a function in a list. We then use `SIGMA` in the
definition of a function for summing the results of a function in an
arbitrarily (finitely) branching tree.

``` hol4
   - Define `(SIGMA f [] = 0) /\
             (SIGMA f (h::t) = f h + SIGMA f t)`;


   - Hol_datatype `ltree = Node of 'a => ltree list`;
   > val it = () : unit

   - Defn.Hol_defn
        "ltree_sigma"     (* higher order recursion *)
        `ltree_sigma f (Node v tl) = f v + SIGMA (ltree_sigma f) tl`;

   > val it =
     HOL function definition (recursive)

       Equation(s) :
        [..] |- ltree_sigma f (Node v tl)
                  = f v + SIGMA (\a. ltree_sigma f a) tl

       Induction :
        [..] |- !P. (!f v tl. (!a. P f a) ==> P f (Node v tl))
                    ==> !v v1. P v v1

       Termination conditions :
         0. WF R
         1. !tl v f a. R (f,a) (f,Node v tl) : defn
```

The termination conditions for `ltree_sigma` seem to require finding a
well-founded relation `R` such that the pair `(f,a)` is `R`-less than
`(f, Node v tl)`. However, this is a hopeless task, since there is no
relation between `a` and `Node v tl`, besides the fact that they are
both `ltree`s. The termination condition extractor has not performed
properly, because it didn't know a congruence rule for `SIGMA`. Such a
congruence theorem is the following:

``` hol4
   SIGMA_CONG =
    |- !l1 l2 f g.
         (l1=l2) /\ (!x. MEM x l2 ==> (f x = g x)) ==>
         (SIGMA f l1 = SIGMA g l2)
```

Once `Hol_defn` has been told about this theorem, via `write_congs`, the
termination conditions extracted for the definition are provable, since
`a` is a proper subterm of `Node v tl`.

``` hol4
   - local open DefnBase
     in
     val _ = write_congs (SIGMA_CONG::read_congs())
     end;

   - Defn.Hol_defn
        "ltree_sigma"
        `ltree_sigma f (Node v tl) = f v + SIGMA (ltree_sigma f) tl`;

   > val it =
       HOL function definition (recursive)

       Equation(s) :  ...  (* as before *)
       Induction :    ...  (* as before *)

       Termination conditions :
         0. WF R
         1. !v f tl a. MEM a tl ==> R (f,a) (f,Node v tl)
```

One final point : for every HOL datatype defined by application of
`Hol_datatype`, a congruence theorem is automatically proved for the
'case' constant for that type, and stored in the `TypeBase`. For
example, the following congruence theorem for `num_case` is stored in
the `TypeBase`:

``` hol4
    |- !f' f b' b M' M.
         (M = M') /\
         ((M' = 0) ==> (b = b')) /\
         (!n. (M' = SUC n) ==> (f n = f' n))
        ==>
         (num_case b f M = num_case b' f' M')
```

This allows the contexts of recursive calls in branches of 'case'
expressions to be tracked.

### See also

[`Defn.tgoal`](#Defn.tgoal), [`Defn.tprove`](#Defn.tprove),
[`bossLib.WF_REL_TAC`](#bossLib.WF_REL_TAC),
[`bossLib.Define`](#bossLib.Define),
[`bossLib.xDefine`](#bossLib.xDefine),
[`bossLib.Hol_datatype`](#bossLib.Hol_datatype)
