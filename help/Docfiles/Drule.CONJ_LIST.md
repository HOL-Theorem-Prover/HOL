## `CONJ_LIST`

``` hol4
Drule.CONJ_LIST : (int -> thm -> thm list)
```

------------------------------------------------------------------------

Extracts a list of conjuncts from a theorem (non-flattening version).

`CONJ_LIST` is the proper inverse of `LIST_CONJ`. Unlike `CONJUNCTS`
which recursively splits as many conjunctions as possible both to the
left and to the right, `CONJ_LIST` splits the top-level conjunction and
then splits (recursively) only the right conjunct. The integer argument
is required because the term `tn` may itself be a conjunction. A list of
`n` theorems is returned.

``` hol4
    A |- t1 /\ (t2 /\ ( ... /\ tn)...)
   ------------------------------------  CONJ_LIST n (A |- t1 /\ ... /\ tn)
    A |- t1   A |- t2   ...   A |- tn
```

### Failure

Fails if the integer argument (`n`) is less than one, or if the input
theorem has less than `n` conjuncts.

### Example

Suppose the identifier `th` is bound to the theorem:

``` hol4
   A |- (x /\ y) /\ z /\ w
```

Here are some applications of `CONJ_LIST` to `th`:

``` hol4
   - CONJ_LIST 0 th;
   ! Uncaught exception:
   ! HOL_ERR

   - CONJ_LIST 1 th;
   > val it = [[A] |- (x /\ y) /\ z /\ w] : thm list

   - CONJ_LIST 2 th;
   > val it = [ [A] |- x /\ y,  [A] |- z /\ w] : thm list

   - CONJ_LIST 3 th;
   > val it = [ [A] |- x /\ y,  [A] |- z,  [A] |- w] : thm list

   - CONJ_LIST 4 th;
   ! Uncaught exception:
   ! HOL_ERR
```

### See also

[`Drule.BODY_CONJUNCTS`](#Drule.BODY_CONJUNCTS),
[`Drule.LIST_CONJ`](#Drule.LIST_CONJ),
[`Drule.CONJUNCTS`](#Drule.CONJUNCTS), [`Thm.CONJ`](#Thm.CONJ),
[`Thm.CONJUNCT1`](#Thm.CONJUNCT1), [`Thm.CONJUNCT2`](#Thm.CONJUNCT2),
[`Drule.CONJ_PAIR`](#Drule.CONJ_PAIR)
