## `n2w_INTRO_TAC`

``` hol4
wordsLib.n2w_INTRO_TAC : int -> tactic
```

------------------------------------------------------------------------

The tactic `n2w_INTRO_TAC i` attempts to recast finite problems (over
`num`) of the form `m = n`, `m < n` and `m <= n` into problems over
bit-vectors of size `i`.

### Example

Given the goal:

``` hol4
?- w2n (a: word4) + w2n (b: word4) < 32
```

applying

``` hol4
e (wordsLib.n2w_INTRO_TAC 6)
```

gives the new goal

``` hol4
[ w2n a < 16, w2n b < 16 ] ?- w2w a + w2w b <+ 32w
```

This goal can be solved using `blastLib.BBLAST_TAC`. Any word length
strictly greater than five would have sufficed here; it is generally
best to pick as small a word size as is necessary.

### See also

[`blastLib.BBLAST_CONV`](#blastLib.BBLAST_CONV)
