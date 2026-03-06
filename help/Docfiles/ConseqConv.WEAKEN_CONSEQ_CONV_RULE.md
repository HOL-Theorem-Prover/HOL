## `WEAKEN_CONSEQ_CONV_RULE`

``` hol4
ConseqConv.WEAKEN_CONSEQ_CONV_RULE : (directed_conseq_conv -> thm -> thm)
```

------------------------------------------------------------------------

Tries to weaken the conclusion of a theorem consisting of an
implication.

Given a theorem of the form `|- A ==> C` and a directed consequence
conversion `c` a call of `WEAKEN_CONSEQ_CONV_RULE c thm` tries to weaken
`C` to a predicate `wC` using `c`. If it succeeds it returns the theorem
`|- A ==> wC`.

### See also

[`ConseqConv.STRENGTHEN_CONSEQ_CONV_RULE`](#ConseqConv.STRENGTHEN_CONSEQ_CONV_RULE)
