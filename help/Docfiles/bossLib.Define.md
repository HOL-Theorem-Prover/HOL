## `Define`

``` hol4
bossLib.Define : term quotation -> thm
```

------------------------------------------------------------------------

General-purpose function definition facility.

`Define` takes a high-level specification of a HOL function, and
attempts to define the function in the logic. If this attempt is
successful, the specification is derived from the definition. The
derived specification is returned to the user, and also stored in the
current theory. `Define` may be used to define abbreviations, recursive
functions, and mutually recursive functions. An induction theorem may be
stored in the current theory as a by-product of `Define`'s activity.
This induction theorem follows the recursion structure of the function,
and may be useful when proving properties of the function.

`Define` takes as input a quotation representing a conjunction of
equations. The specified function(s) may be phrased using ML-style
pattern-matching. A call `` Define `<spec>` `` should conform with the
following grammar:

``` hol4
       spec ::= <eqn>
            |   (<eqn>) /\ <spec>

        eqn ::= <alphanumeric> <pat> ... <pat> = <term>


        pat ::= <variable>
            |   <wildcard>
            |   <cname>                          (* 0-ary constructor *)
            |   (<cname>_n <pat>_1 ... <pat>_n)  (* constructor appl. *)

      cname ::= <alphanumeric> | <symbolic>

   wildcard ::= _
            |   _<wildcard>
```

When processing the specification of a recursive function, `Define` must
perform a termination proof. It automatically constructs termination
conditions for the function, and invokes a termination prover in an
attempt to prove the termination conditions.

If the function is primitive recursive, in the sense that it exactly
follows the recursion pattern of a previously declared HOL datatype,
then this proof always succeeds, and `Define` stores the derived
equations in the current theory segment. Otherwise, the function is not
an instance of primitive recursion, and the termination prover may
succeed or fail.

If it succeeds, then `Define` stores the specified equations in the
current theory segment. An induction theorem customized for the defined
function is also stored in the current segment. Note, however, that an
induction theorem is not stored for primitive recursive functions, since
that theorem would be identical to the induction theorem resulting from
the declaration of the datatype.

If the termination proof fails, then `Define` fails.

In general, `Define` attempts to derive exactly the specified
conjunction of equations. However, the rich syntax of patterns allows
some ambiguity. For example, the input

``` hol4
    Define `(f 0 _ = 1)
      /\    (f _ 0 = 2)`
```

is ambiguous at `f 0 0`: should the result be `1` or `2`? The system
attempts to resolve this ambiguity in the same way as compilers and
interpreters for functional languages. Namely, a conjunction of
equations is treated as being processed left-conjunct first, followed by
processing the right conjunct. Therefore, in the example above, the
right-hand side of the first clause is taken as the value of `f 0 0`. In
the implementation, ambiguities arising from such overlapping patterns
are systematically translated away in a pre-processing step.

Another case of vagueness in patterns is shown above: the specification
is 'incomplete' since it does not tell us how `f` should behave when
applied to two non-zero arguments: e.g., `f (SUC m) (SUC n)`. In the
implementation, such missing clauses are filled in, and have the value
`ARB`. This 'pattern-completion' step is a way of turning descriptions
of partial functions into total functions suitable for HOL. However,
since the user has not completely specified the function, the system
takes that as a hint that the user is not interested in using the
function at the missing-but-filled-in clauses, and so such clauses are
dropped from the final theorem.

In summary, `Define` will derive the unambiguous and complete equations

``` hol4
     |- (f 0 (SUC v4) = 1) /\
        (f 0 0 = 1) /\
        (f (SUC v2) 0 = 2)
        (f (SUC v2) (SUC v4) = ARB)
```

from the above ambiguous and incomplete equations. The odd-looking
variable names are due to the pre-processing steps described above. The
above result is only an intermediate value: in the final result returned
by `Define`, the last equation is droppped:

``` hol4
     |- (f 0 (SUC v4) = 1) /\
        (f 0 0 = 1) /\
        (f (SUC v2) 0 = 2)
```

`Define` automatically generates names with which to store the
definition and, (if it exists) the associated induction theorem, in the
current theory. The name for storing the definition is built by
concatenating the name of the function with the value of the reference
variable `Defn.def_suffix`. The name for storing the induction theorem
is built by concatenating the name of the function with the value of the
reference variable `Defn.ind_suffix`. For mutually recursive functions,
where there is a choice of names, the name of the function in the first
clause is taken.

Since the names used to store elements in the current theory segment are
transformed into ML bindings after the theory is exported, it is
required that every invocation of `Define` generates names that will be
valid ML identifiers. For this reason, `Define` requires alphanumeric
function names. If one wishes to define symbolic identifiers, the ML
function `xDefine` should be used.

### Failure

`Define` fails if its input fails to parse and typecheck.

`Define` fails if the name of the function being defined is not
alphanumeric.

`Define` fails if there are more free variables on the right hand sides
of the recursion equations than the left.

`Define` fails if it cannot prove the termination of the specified
recursive function. In that case, one has to embark on the following
multi-step process in order to get the same effect as if `Define` had
succeeded: (1) construct the function and synthesize its termination
conditions with `Hol_defn`; (2) set up a goal to prove the termination
conditions with `tgoal`; (3) interactively prove the termination
conditions, starting with an invocation of `WF_REL_TAC`; and (4) package
everything up with an invocation of `tDefine`.

### Example

We will give a number of examples that display the range of functions
that may be defined with `Define`. First, we have a recursive function
that uses "destructors" in the recursive call. Since `fact` is not
primitive recursive, an induction theorem for `fact` is generated and
stored in the current theory.

``` hol4
   Define `fact x = if x = 0 then 1 else x * fact(x-1)`;

   Equations stored under "fact_def".
   Induction stored under "fact_ind".
   > val it = |- fact x = (if x = 0 then 1 else x * fact (x - 1)) : thm

   - DB.fetch "-" "fact_ind";

   > val it =
     |- !P. (!x. (~(x = 0) ==> P (x - 1)) ==> P x) ==> !v. P v : thm
```

Next we have a recursive function with relatively complex
pattern-matching. We omit to examine the generated induction theorem.

``` hol4
   Define `(flatten  []           = [])
      /\   (flatten ([]::rst)     = flatten rst)
      /\   (flatten ((h::t)::rst) = h::flatten(t::rst))`

   <<HOL message: inventing new type variable names: 'a>>

   Equations stored under "flatten_def".
   Induction stored under "flatten_ind".

   > val it =
       |- (flatten [] = []) /\
          (flatten ([]::rst) = flatten rst) /\
          (flatten ((h::t)::rst) = h::flatten (t::rst)) : thm
```

Next we define a curried recursive function, which uses wildcard
expansion and pattern-matching pre-processing.

``` hol4
   Define `(min (SUC x) (SUC y) = min x y + 1)
      /\   (min  ____    ____   = 0)`;

   Equations stored under "min_def".
   Induction stored under "min_ind".

   > val it =
       |- (min (SUC x) (SUC y) = min x y + 1) /\
          (min (SUC v2) 0 = 0) /\
          (min 0 v1 = 0) : thm
```

Next we make a primitive recursive definition. Note that no induction
theorem is generated in this case.

``` hol4
   Define `(filter P [] = [])
     /\    (filter P (h::t) = if P h then h::filter P t else filter P t)`;

   <<HOL message: inventing new type variable names: 'a>>
   Definition has been stored under "filter_def".

   > val it =
      |- (!P. filter P [] = []) /\
         !P h t. filter P (h::t) =
                  (if P h then h::filter P t else filter P t) : thm
```

`Define` may also be used to define mutually recursive functions. For
example, we can define a datatype of propositions and a function for
putting a proposition into negation normal form as follows. First we
define a datatype for boolean formulae (`prop`):

``` hol4
   - Hol_datatype
       `prop = VAR of 'a
             | NOT of prop
             | AND of prop => prop
             | OR  of prop => prop`;

   > val it = () : unit
```

Then two mutually recursive functions `nnfpos` and `nnfneg` are defined:

``` hol4
   - Define
        `(nnfpos (VAR x)   = VAR x)
    /\   (nnfpos (NOT p)   = nnfneg p)
    /\   (nnfpos (AND p q) = AND (nnfpos p) (nnfpos q))
    /\   (nnfpos (OR p q)  = OR  (nnfpos p) (nnfpos q))

    /\   (nnfneg (VAR x)   = NOT (VAR x))
    /\   (nnfneg (NOT p)   = nnfpos p)
    /\   (nnfneg (AND p q) = OR  (nnfneg p) (nnfneg q))
    /\   (nnfneg (OR p q)  = AND (nnfneg p) (nnfneg q))`;
```

The system returns:

``` hol4
   <<HOL message: inventing new type variable names: 'a>>

   Equations stored under "nnfpos_def".
   Induction stored under "nnfpos_ind".

   > val it =
       |- (nnfpos (VAR x) = VAR x) /\
          (nnfpos (NOT p) = nnfneg p) /\
          (nnfpos (AND p q) = AND (nnfpos p) (nnfpos q)) /\
          (nnfpos (OR p q) = OR (nnfpos p) (nnfpos q)) /\
          (nnfneg (VAR x) = NOT (VAR x)) /\
          (nnfneg (NOT p) = nnfpos p) /\
          (nnfneg (AND p q) = OR (nnfneg p) (nnfneg q)) /\
          (nnfneg (OR p q) = AND (nnfneg p) (nnfneg q)) : thm
```

`Define` may also be used to define non-recursive functions.

``` hol4
   Define `f x (y,z) = (x + 1 = y DIV z)`;

   Definition has been stored under "f_def".

   > val it = |- !x y z. f x (y,z) = (x + 1 = y DIV z) : thm
```

`Define` may also be used to define non-recursive functions with complex
pattern-matching. The pattern-matching pre-processing of `Define` can be
convenient for this purpose, but can also generate a large number of
equations. For example:

``` hol4
   Define `(g (0,_,_,_,_) = 1) /\
           (g (_,0,_,_,_) = 2) /\
           (g (_,_,0,_,_) = 3) /\
           (g (_,_,_,0,_) = 4) /\
           (g (_,_,_,_,0) = 5)`
```

yields a definition with thirty-one clauses.

### Comments

In an `eqn`, no variable can occur more than once on the left hand side
of the equation.

In HOL, constructors are curried functions, unlike in ML. When used in a
pattern, a constructor must be fully applied to its arguments.

Also unlike ML, a pattern variable in a clause of a definition is not
distinct from occurrences of that variable in other clauses.

`Define` translates a wildcard into a new variable, which is named to be
different from any other variable in the function definition. As in ML,
wildcards are not allowed to occur on the right hand side of any clause
in the definition.

An induction theorem generated in the course of processing an invocation
of `Define` can be applied by `recInduct`.

Invoking `Define` on a conjunction of non-recursive clauses having
complex pattern-matching will result in an induction theorem being
stored. This theorem may be useful for case analysis, and can be applied
by `recInduct`.

`Define` takes a 'quotation' as an argument. Some might think that the
input to `Define` should instead be a term. However, some important
pre-processing happens in `Define` that would not be possible if the
input was a term.

`Define` is a mechanization of a well-founded recursion theorem
(`relationTheory.WFREC_COROLLARY`).

`Define` currently has a rather weak termination prover. For example, it
always fails to prove the termination of nested recursive functions.

`bossLib.Define` is most commonly used. `TotalDefn.Define` is identical
to `bossLib.Define`, except that the `TotalDefn` structure comes with
less baggage---it depends only on `numLib` and `pairLib`.

`Define` automatically adds the definition it makes into the hidden
'compset' accessed by `EVAL` and `EVAL_TAC`.

### See also

[`bossLib.tDefine`](#bossLib.tDefine),
[`bossLib.xDefine`](#bossLib.xDefine),
[`TotalDefn.DefineSchema`](#TotalDefn.DefineSchema),
[`bossLib.Hol_defn`](#bossLib.Hol_defn), [`Defn.tgoal`](#Defn.tgoal),
[`Defn.tprove`](#Defn.tprove),
[`bossLib.WF_REL_TAC`](#bossLib.WF_REL_TAC),
[`bossLib.recInduct`](#bossLib.recInduct),
[`bossLib.EVAL`](#bossLib.EVAL), [`bossLib.EVAL_TAC`](#bossLib.EVAL_TAC)
