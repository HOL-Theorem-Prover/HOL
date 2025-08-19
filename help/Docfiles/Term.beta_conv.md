## `beta_conv`

``` hol4
Term.beta_conv : term -> term
```

------------------------------------------------------------------------

Performs one step of beta-reduction.

Beta-reduction is one of the primitive operations in the lambda
calculus. A step of beta-reduction may be performed by `beta_conv M`,
where `M` is the application of a lambda abstraction to an argument,
i.e., has the form `((\v.N) P)`. The beta-reduction occurs by
systematically replacing every free occurrence of `v` in `N` by `P`.

Care is taken so that no free variable of `P` becomes captured in this
process.

### Failure

If `M` is not the application of an abstraction to an argument.

### Example

``` hol4
- beta_conv (mk_comb (Term `\(x:'a) (y:'b). x`, Term `(P:bool -> 'a) Q`));
> val it = `\y. P Q` : term

- beta_conv (mk_comb (Term `\(x:'a) (y:'b) (y':'b). x`, Term `y:'a`));
> val it = `\y'. y` : term
```

### Comments

More complex strategies for coding up full beta-reduction can be coded
up in ML. The `conversions` of Larry Paulson support this activity as
inference steps.

For programming derived rules of inference.

### See also

[`Thm.BETA_CONV`](#Thm.BETA_CONV),
[`Drule.RIGHT_BETA`](#Drule.RIGHT_BETA),
[`Drule.LIST_BETA_CONV`](#Drule.LIST_BETA_CONV),
[`Drule.RIGHT_LIST_BETA`](#Drule.RIGHT_LIST_BETA),
[`Conv.DEPTH_CONV`](#Conv.DEPTH_CONV),
[`Conv.TOP_DEPTH_CONV`](#Conv.TOP_DEPTH_CONV),
[`Conv.REDEPTH_CONV`](#Conv.REDEPTH_CONV)
