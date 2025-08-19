## `EXISTENCE`

``` hol4
Conv.EXISTENCE : (thm -> thm)
```

------------------------------------------------------------------------

Deduces existence from unique existence.

When applied to a theorem with a unique-existentially quantified
conclusion, `EXISTENCE` returns the same theorem with normal existential
quantification over the same variable.

``` hol4
    A |- ?!x. p
   -------------  EXISTENCE
    A |- ?x. p
```

### Failure

Fails unless the conclusion of the theorem is unique-existentially
quantified.

### See also

[`Conv.EXISTS_UNIQUE_CONV`](#Conv.EXISTS_UNIQUE_CONV)
