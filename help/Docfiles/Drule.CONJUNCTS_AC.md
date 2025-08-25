## `CONJUNCTS_AC`

``` hol4
Drule.CONJUNCTS_AC : term * term -> thm
```

------------------------------------------------------------------------

Prove equivalence under idempotence, symmetry and associativity of
conjunction.

`CONJUNCTS_AC` takes a pair of terms `(t1, t2)` and proves `|- t1 = t2`
if `t1` and `t2` are equivalent up to idempotence, symmetry and
associativity of conjunction. That is, if `t1` and `t2` are two
(different) arbitrarily-nested conjunctions of the same set of terms,
then `CONJUNCTS_AC (t1,t2)` returns `|- t1 = t2`. Otherwise, it fails.

### Failure

Fails if `t1` and `t2` are not equivalent, as described above.

### Example

``` hol4
- CONJUNCTS_AC (Term `(P /\ Q) /\ R`, Term `R /\ (Q /\ R) /\ P`);
> val it = |- (P /\ Q) /\ R = R /\ (Q /\ R) /\ P : thm
```

Used to reorder a conjunction. First sort the conjuncts in a term `t1`
into the desired order (e.g., lexicographic order, for normalization) to
get a new term `t2`, then call `CONJUNCTS_AC(t1,t2)`.

### See also

[`Drule.DISJUNCTS_AC`](#Drule.DISJUNCTS_AC)
