## `MATCH_MP`

``` hol4
Drule.MATCH_MP : thm -> thm -> thm
```

------------------------------------------------------------------------

Modus Ponens inference rule with automatic matching.

When applied to theorems `A1 |- !x1...xn. t1 ==> t2` and `A2 |- t1'`,
the inference rule `MATCH_MP` matches `t1` to `t1'` by instantiating
free or universally quantified variables in the first theorem (only),
and returns a theorem `A1 u A2 |- !xa..xk. t2'`, where `t2'` is a
correspondingly instantiated version of `t2`. Polymorphic types are also
instantiated if necessary.

Variables free in the consequent but not the antecedent of the first
argument theorem will be replaced by variants if this is necessary to
maintain the full generality of the theorem, and any which were
universally quantified over in the first argument theorem will be
universally quantified over in the result, and in the same order.

``` hol4
    A1 |- !x1..xn. t1 ==> t2   A2 |- t1'
   --------------------------------------  MATCH_MP
          A1 u A2 |- !xa..xk. t2'
```

As with `MP` and the underlying syntactic function `dest_imp`, negated
terms (of the form `~p`) are treated as if they were implications from
the argument of the negation to falsity.

### Failure

Fails unless the first theorem is a (possibly repeatedly universally
quantified) implication (in the sense of `dest_imp`) whose antecedent
can be instantiated to match the conclusion of the second theorem,
without instantiating any variables which are free in `A1`, the first
theorem's assumption list.

### Example

In this example, automatic renaming occurs to maintain the most general
form of the theorem, and the variant corresponding to `z` is universally
quantified over, since it was universally quantified over in the first
argument theorem.

``` hol4
   - val ith = (GENL [Term `x:num`, Term `z:num`]
                  o DISCH_ALL
                  o AP_TERM (Term `$+ (w + z)`))
               (ASSUME (Term `x:num = y`));
   > val ith = |- !x z. (x = y) ==> (w + z + x = w + z + y) : thm

   - val th = ASSUME (Term `w:num = z`);
   > val th = [w = z] |- w = z : thm

   - MATCH_MP ith th;
   > val it =  [w = z] |- !z'. w' + z' + w = w' + z' + z : thm
```

### See also

[`boolSyntax.dest_imp`](#boolSyntax.dest_imp),
[`Thm.EQ_MP`](#Thm.EQ_MP),
[`Tactic.MATCH_MP_TAC`](#Tactic.MATCH_MP_TAC), [`Thm.MP`](#Thm.MP),
[`Tactic.MP_TAC`](#Tactic.MP_TAC),
[`ConseqConv.CONSEQ_REWRITE_CONV`](#ConseqConv.CONSEQ_REWRITE_CONV)
