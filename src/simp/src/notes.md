# Note on the Simplifier Code

## Important Types

**simpset**

:   (From `simpLib`.)
    Typically built by bundling *fragments* together, but is actually a collection of four important components:

    -   `mk_rewrs` function.
        This processes “arbitrary” user-provided theorems to turn them into proper rewrites.

    -   `net` a higher-order term-net containing simplifier-conversions

    -   `dprocs` a list of “decision procedures” (lower priority routines), which are *reducer*s.

    -   `travrules`, a *travrules* value

**ssfrag** (a ‘simpset fragment’)

:   (From `simpLib`.)
    A collection of user-provided data that gets pushed into *simpset*s.
    Includes rewrites, conversions, congruences, AC rewrites, decision procedures, relation-simplification data and an optional `filter`, which is used to adjust the simpset `mk_rewrs` function.

**reducer**

:   (From `Traverse`.)
    A bundled piece of code/data that is capable of producing theorems relating input terms to fresh “outputs”.
    Each reducer has its own notion of “context”, values to which clients can add theorems.
    (These contexts are implemented with exceptions to give existential types.)
    Such added theorems may be goal assumptions, or provided by congruence rules.

    Each reducer has an `apply` function, which is passed a context, a `solver` for handling side conditions, a `stack` of already attempted side conditions, a continuation `conv`, a `relation` field and an input term.
    The `apply` function is expected to return a theorem of the form

        |- input  R   output

    where `R` might be as given in the `relation` field.

    Arithmetic decision procedures are `reducer`s.
    Their context is the list of theorems that they believe to be relevant (*i.e.*, Presburger terms), and they ignore all of the information provided by `apply` except the context.

    Reducers don’t depend on anything else in the simplification code base (though their `conv` and `solver`  continuations will call back into simplifier code).

**preorder**

:   (From `Travrules`.)
    A preorder encodes information enough to identify a relation (type `'a -> 'a -> bool`) as something that is reflexive and transitive.
    The preorder stores the constant of the particular relation, and two functions to implement transitivity and reflexivity.
    The former takes two theorems as input, while the latter takes both the argument to the relation and a relation term itself, which, if polymorphic, must have been instantiated so that it can be applied to the argument.
    For the equality case, this data is thus (`min$=`, `TRANS` and (essentially) `REFL`).

**travrules**

:   (From `Travrules`.)
    Embodies a list of *preorders* and two lists of *congprocs*: the “standard congprocs” (`congprocs`), and the “weakening congprocs” (`weakenprocs`).
    The “default” travrules value is `EQ_tr`, and contains the equality preorder, and the equality congproc as a standard congproc.
    (I.e., it has no weakening congprocs.)

    The travrules is a static piece of information for guiding simplification.
    The dynamic data that is maintained during simplification (containing context values, the relation currently being used and the context’s free variables) is a `trav_state`, which is private to module `Traverse`.

    Each simpset contains a list of `travrules` values.

**congproc**

:   (From `Opening`.)
    A congproc is a function that will set up recursive simplification of an input term.
    With the exception of the core equality congruences (`MK_COMB` and `ABS`) these are all built with the function `CONGPROC`.
    In addition to the term, the congproc is passed a record of important data containing

    -   `depther`: a function which will be applied to subterms to produce simplified sub-terms
    -   `solver`: used to handle side-conditions in congruence rules
    -   `relation`: identifies the relation we’re using
    -   `freevars`: the free variables of the context, which may be relevant if descending under a binder

    `congproc` values are stored in `travrules`.

## Important Functions

`SIMP_QCONV`

:   (From `simpLib`.)
    Calls `TRAVERSE` after building initial context values for all of the embedded reducers (giving a trav_state)

`TRAVERSE`

:   (From `Traverse`.)
    Implements the logic of the simplifier’s traversal of terms.
    In particular, this is where the preorder/top-down nature of the simplifier wrt its equality rewrites is decided, because of the way it begins with

        repeat high_priority then descend ...

    The `high_priority` stuff here is to do fire the equality reducer.
    Descent is then the recursive simplification of sub-terms.
    The `...` portion is where decision procedures get to fire, and where weakenprocs get a chance to fire.
    These effectively see the term in bottom-up fashion as a result.

`CONGPROC`

:   (From `Opening`.)
    This builds a *congproc* given a `congrule` theorem and a general notion of reflexivity in the function `refl`.
    It’s important that `refl` be able to generate reflexivity theorems for multiple relations at once: this allows different relations to appear in the assumptions of `congrule`; the conclusion might want to draw conclusions about equality even as one of the assumptions is about another relation again (as happens in weakening congruences).

    One problem here is that reprocessing of assumptions can unnecessarily descend into terms that have already been processed once.
    For example, in the rule for conditional expressions, we have

        p = p’ ==> (p’ ==> t = t’) ==> (~p’ ==> e = e’) ==>
        (COND p t e = COND p’ t’ e’)

    and the reprocess flag will be set to true for the `~p’` assumption (it’s not just a variable).
    Sure, if negation descends over a disjunction or similar, this is an important thing to do (though the `mk_cond_rewr` could presumably do it too), but if nothing simplifies at the top level, it’s painful to have to descend into `p’` again.
