## `Induct`

``` hol4
bossLib.Induct : tactic
```

------------------------------------------------------------------------

Performs structural induction over the type of the goal's outermost
universally quantified variable.

Given a universally quantified goal, `Induct` attempts to perform an
induction based on the type of the leading universally quantified
variable. The induction theorem to be used is looked up in the
`TypeBase` database, which holds useful facts about the system's defined
types. `Induct` may also be used to reason about mutually recursive
types.

### Failure

`Induct` fails if the goal is not universally quantified, or if the type
of the variable universally quantified does not have an induction
theorem in the `TypeBase` database.

### Example

If attempting to prove

``` hol4
   !list. LENGTH (REVERSE list) = LENGTH list
```

one can apply `Induct` to begin a proof by induction on `list`.

``` hol4
   - e Induct;
```

This results in the base and step cases of the induction as new goals.

``` hol4
   ?- LENGTH (REVERSE []) = LENGTH []

   LENGTH (REVERSE list) = LENGTH list
   ?- !h. LENGTH (REVERSE (h::list)) = LENGTH (h::list)
```

The same tactic can be used for induction over numbers. For example
expanding the goal

``` hol4
   ?- !n. n > 2 ==> !x y z. ~(x EXP n + y EXP n = z EXP n)
```

with `Induct` yields the two goals

``` hol4
   ?- 0 > 2 ==> !x y z. ~(x EXP 0 + y EXP 0 = z EXP 0)

   n > 2 ==> !x y z. ~(x EXP n + y EXP n = z EXP n)
   ?- SUC n > 2 ==> !x y z. ~(x EXP SUC n + y EXP SUC n = z EXP SUC n)
```

`Induct` can also be used to perform induction on mutually recursive
types. For example, given the datatype

``` hol4
   Hol_datatype
       `exp = VAR of string                (* variables *)
            | IF  of bexp => exp => exp    (* conditional *)
            | APP of string => exp list    (* function application *)
         ;
       bexp = EQ  of exp => exp            (* boolean expressions *)
            | LEQ of exp => exp
            | AND of bexp => bexp
            | OR  of bexp => bexp
            | NOT of bexp`
```

one can use `Induct` to prove that all objects of type `exp` and `bexp`
are of a non-zero size. (Recall that size definitions are automatically
defined for datatypes.) Typically, mutually recursive types lead to
mutually recursive induction schemes having multiple predicates. The
scheme for the above definition has 3 predicates: `P0`, `P1`, and `P2`,
which respectively range over expressions, boolean expressions, and
lists of expressions.

``` hol4
   |- !P0 P1 P2.
        (!a. P0 (VAR a)) /\
        (!b e e0. P1 b /\ P0 e /\ P0 e0 ==> P0 (IF b e e0)) /\
        (!l. P2 l ==> !b. P0 (APP b l)) /\
        (!e e0. P0 e /\ P0 e0 ==> P1 (EQ e e0)) /\
        (!e e0. P0 e /\ P0 e0 ==> P1 (LEQ e e0)) /\
        (!b b0. P1 b /\ P1 b0 ==> P1 (AND b b0)) /\
        (!b b0. P1 b /\ P1 b0 ==> P1 (OR b b0)) /\
        (!b. P1 b ==> P1 (NOT b)) /\
        P2 [] /\
        (!e l. P0 e /\ P2 l ==> P2 (e::l))
          ==>
        (!e. P0 e) /\ (!b. P1 b) /\ !l. P2 l
```

Invoking `Induct` on a goal such as

``` hol4
   !e. 0 < exp_size e
```

yields the three subgoals

``` hol4
   ?- !s. 0 < exp_size (APP s l)


   [ 0 < exp_size e, 0 < exp_size e' ] ?- 0 < exp_size (IF b e e')

   ?- !s. 0 < exp_size (VAR s)
```

In this case, `P1` and `P2` have been vacuously instantiated in the
application of `Induct`, since it detects that only `P0` is needed.
However, it is also possible to use `Induct` to start the proofs of

``` hol4
    (!e. 0 < exp_size e) /\ (!b. 0 < bexp_size b)
```

and

``` hol4
    (!e. 0 < exp_size e) /\
    (!b. 0 < bexp_size b) /\
    (!list. 0 < exp1_size list)
```

### See also

[`bossLib.Induct_on`](#bossLib.Induct_on),
[`bossLib.completeInduct_on`](#bossLib.completeInduct_on),
[`bossLib.measureInduct_on`](#bossLib.measureInduct_on),
[`Prim_rec.INDUCT_THEN`](#Prim_rec.INDUCT_THEN),
[`bossLib.Cases`](#bossLib.Cases),
[`bossLib.Hol_datatype`](#bossLib.Hol_datatype),
[`proofManagerLib.g`](#proofManagerLib.g),
[`proofManagerLib.e`](#proofManagerLib.e)
