## `EXISTS_EQ___CONSEQ_CONV`

``` hol4
ConseqConv.EXISTS_EQ___CONSEQ_CONV : conseq_conv
```

------------------------------------------------------------------------

Given a term of the form `(?x. P x) = (?x. Q x)` this consequence
conversion returns the theorem
`|- (!x. (P x = Q x)) ==> ((?x. P x) = (?x. Q x))`.

### See also

[`ConseqConv.conseq_conv`](#ConseqConv.conseq_conv)
