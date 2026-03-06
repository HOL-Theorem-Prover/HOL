## `INSTANCE_T_CONV`

``` hol4
Arith.INSTANCE_T_CONV : ((term -> term list) -> conv -> conv)
```

------------------------------------------------------------------------

Function which allows a proof procedure to work on substitution
instances of terms that are in the domain of the procedure.

This function generalises a conversion that is used to prove formulae
true. It does this by first replacing any syntactically unacceptable
subterms with variables. It then attempts to prove the resulting
generalised formula and if successful it re-instantiates the variables.

The first argument should be a function which computes a list of
subterms of a term which are syntactically unacceptable to the proof
procedure. This function should include in its result any variables that
do not appear in other subterms returned. The second argument is the
proof procedure to be generalised; this should be a conversion which
when successful returns an equation between the argument formula and `T`
(true).

### Failure

Fails if either of the applications of the argument functions fail, or
if the conversion does not return an equation of the correct form.

### Example

``` hol4
#FORALL_ARITH_CONV "!f m (n:num). (m < (f n)) ==> (m <= (f n))";;
evaluation failed     FORALL_ARITH_CONV -- formula not in the allowed subset

#INSTANCE_T_CONV non_presburger_subterms FORALL_ARITH_CONV
# "!f m (n:num). (m < (f n)) ==> (m <= (f n))";;
|- (!f m n. m < (f n) ==> m <= (f n)) = T
```
