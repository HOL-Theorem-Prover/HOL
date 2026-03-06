## `DISJUNCTS_AC`

``` hol4
Drule.DISJUNCTS_AC : term * term -> thm
```

------------------------------------------------------------------------

Prove equivalence under idempotence, symmetry and associativity of
disjunction.

`DISJUNCTS_AC` takes a pair of terms `(t1, t2)` and proves `|- t1 = t2`
if `t1` and `t2` are equivalent up to idempotence, symmetry and
associativity of disjunction. That is, if `t1` and `t2` are two
(different) arbitrarily-nested disjunctions of the same set of terms,
then `DISJUNCTS_AC (t1,t2)` returns `|- t1 = t2`. Otherwise, it fails.

### Failure

Fails if `t1` and `t2` are not equivalent, as described above.

### Example

``` hol4
- DISJUNCTS_AC (Term `(P \/ Q) \/ R`, Term `R \/ (Q \/ R) \/ P`);
> val it = |- (P \/ Q) \/ R = R \/ (Q \/ R) \/ P : thm
```

Used to reorder a disjunction. First sort the disjuncts in a term `t1`
into the desired order (e.g., lexicographic order, for normalization) to
get a new term `t2`, then call `DISJUNCTS_AC(t1,t2)`.

### See also

[`Drule.CONJUNCTS_AC`](#Drule.CONJUNCTS_AC)
