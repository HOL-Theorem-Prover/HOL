## `Cong`

``` hol4
simpLib.Cong : thm -> thm
```

------------------------------------------------------------------------

Marks a theorem as a congruence rule for the simplifier.

The `Cong` function marks (or "tags") a theorem so that when passed to
the simplifier, it is not used as a rewrite, but rather as a congruence
rule. This is a simpler way of adding a congruence rule to the
simplifier than using the underlying `SSFRAG` function.

### Failure

Never fails. On the other hand, `Cong` does not check that the theorem
passed as an argument is a valid congruence rule, and invalid congruence
rules may have unpredictable effects on the behaviour of the simplifier.

### Example

``` hol4
   - SIMP_CONV pure_ss [] ``!x::P. x IN P /\ Q x``;
   <<HOL message: inventing new type variable names: 'a>>
   ! Uncaught exception:
   ! UNCHANGED
   - RES_FORALL_CONG;
   > val it =
       |- (P = Q) ==>
          (!x. x IN Q ==> (f x = g x)) ==>
          (RES_FORALL P f = RES_FORALL Q g) : thm
   - SIMP_CONV pure_ss [Cong RES_FORALL_CONG] ``!x::P. x IN P ``;
   <<HOL message: inventing new type variable names: 'a>>
   > val it = |- (!x::P. x IN P /\ Q x) = !x::P. T /\ Q x : thm
```

(Note that `RES_FORALL_CONG` is already included in `bool_ss` and all
simpsets built on it.)

### See also

[`simpLib.SSFRAG`](#simpLib.SSFRAG)
