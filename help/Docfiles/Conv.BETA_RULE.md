## `BETA_RULE`

``` hol4
Conv.BETA_RULE : (thm -> thm)
```

------------------------------------------------------------------------

Beta-reduces all the beta-redexes in the conclusion of a theorem.

When applied to a theorem `A |- t`, the inference rule `BETA_RULE`
beta-reduces all beta-redexes, at any depth, in the conclusion `t`.
Variables are renamed where necessary to avoid free variable capture.

``` hol4
    A |- ....((\x. s1) s2)....
   ----------------------------  BETA_RULE
      A |- ....(s1[s2/x])....
```

### Failure

Never fails, but will have no effect if there are no beta-redexes.

### Example

The following example is a simple reduction which illustrates variable
renaming:

``` hol4
   - Globals.show_assums := true;
   val it = () : unit

   - local val tm = Parse.Term `f = ((\x y. x + y) y)`
     in
     val x = ASSUME tm
     end;
   val x = [f = (\x y. x + y)y] |- f = (\x y. x + y)y : thm

   - BETA_RULE x;
   val it = [f = (\x y. x + y)y] |- f = (\y'. y + y') : thm
```

### See also

[`Thm.BETA_CONV`](#Thm.BETA_CONV),
[`Tactic.BETA_TAC`](#Tactic.BETA_TAC),
[`PairedLambda.PAIRED_BETA_CONV`](#PairedLambda.PAIRED_BETA_CONV),
[`Drule.RIGHT_BETA`](#Drule.RIGHT_BETA)
