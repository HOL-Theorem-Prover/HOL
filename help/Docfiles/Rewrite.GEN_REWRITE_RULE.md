## `GEN_REWRITE_RULE` {#Rewrite.GEN_REWRITE_RULE}


```
GEN_REWRITE_RULE : ((conv -> conv) -> rewrites -> thm list -> thm -> thm)
```



Rewrites a theorem, selecting terms according to a user-specified strategy.


Rewriting in HOL is based on the use of equational theorems as left-to-right
replacements on the subterms of an object theorem.  This replacement is
mediated by the use of `REWR_CONV`, which finds matches between left-hand
sides of given equations in a term and applies the substitution.

Equations used in rewriting are obtained from the theorem lists given as
arguments to the function. These are at first transformed into a form suitable
for rewriting. Conjunctions are separated into individual rewrites. Theorems
with conclusions of the form `"~t"` are transformed into the corresponding
equations `"t = F"`. Theorems `"t"` which are not equations are cast as
equations of form `"t = T"`.

If a theorem is used to rewrite the object theorem, its assumptions
are added to the assumptions of the returned theorem, unless they are
alpha-convertible to existing assumptions.  The matching involved uses
variable instantiation. Thus, all free variables are generalized, and
terms are instantiated before substitution. Theorems may have
universally quantified variables.

The theorems with which rewriting is done are divided
into two groups, to facilitate implementing other rewriting tools.
However, they are considered in an order-independent fashion. (That
is, the ordering is an implementation detail which is not specified.)

The search strategy for finding matching subterms is the first
argument to the rule. Matching and substitution may occur at any
level of the term, according to the specified search strategy: the
whole term, or starting from any subterm. The search strategy also
specifies the depth of the search: recursively up to an arbitrary
depth until no matches occur, once over the selected subterm, or any
more complex scheme.

### Failure

`GEN_REWRITE_RULE` fails if the search strategy fails. It may also
cause a non-terminating sequence of rewrites, depending on the search
strategy used.


This rule is used in the system to implement all other rewriting
rules, and may provide a user with a method to fine-tune rewriting of
theorems.

### Example

Suppose we have a theorem of the form:
    
       thm = |- (1 + 2) + 3 = (3 + 1) + 2
    
and we would like to rewrite the left-hand side with the
theorem `ADD_SYM` without changing the right hand side. This can be
done by using:
    
       GEN_REWRITE_RULE (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [ADD_SYM] mythm
    
Other rules, such as `ONCE_REWRITE_RULE`, would match and
substitute on both sides, which would not be the desirable result.

As another example, `REWRITE_RULE` could be implemented as
    
        GEN_REWRITE_RULE TOP_DEPTH_CONV (implicit_rewrites())
    
which specifies that matches should be searched recursively
starting from the whole term of the theorem, and `implicit_rewrites` must
be added to the user defined set of theorems employed in rewriting.

### See also

[`Rewrite.ASM_REWRITE_RULE`](#Rewrite.ASM_REWRITE_RULE), [`Rewrite.FILTER_ASM_REWRITE_RULE`](#Rewrite.FILTER_ASM_REWRITE_RULE), [`Rewrite.ONCE_REWRITE_RULE`](#Rewrite.ONCE_REWRITE_RULE), [`Rewrite.PURE_REWRITE_RULE`](#Rewrite.PURE_REWRITE_RULE), [`Conv.REWR_CONV`](#Conv.REWR_CONV), [`Rewrite.REWRITE_RULE`](#Rewrite.REWRITE_RULE)

