## `BBLAST_CONV`

``` hol4
blastLib.BBLAST_CONV : conv
```

------------------------------------------------------------------------

Bit-blasting conversion for words.

This conversion expands bit-vector terms into Boolean propositions. It
goes beyond the functionality of `wordsLib.WORD_BIT_EQ_CONV` by handling
addition, subtraction and orderings. Consequently, this conversion can
automatically handle small, but tricky, bit-vector goals that
`wordsLib.WORD_DECIDE` cannot handle. Obviously bit-blasting is a brute
force approach, so this conversion should be used with care. It will
only work well for smallish word sizes and when there is only and
handful of additions around. It is also "eager" -- additions are
expanded out even when not strictly necessary. For example, in

``` hol4
(a + b) <+ c /\ c <+ d ==> (a + b) <+ d:word32
```

the sum `a + b` is expanded. Users may be able to achieve speed-ups by
first introducing abbreviations and then proving general forms, e.g.

``` hol4
x <+ c /\ c <+ d ==> x <+ d:word32
```

The conversion handles most operators, however, the following are not
covered / interpreted:

-- Type variables for word lengths, i.e. terms of type `:'a word`.

-- General multiplication, i.e. `w1 * w2`. Multiplication by a literal
is okay, although this may introduce many additions.

-- Bit-field selections with non-literal bounds,
e.g. `(expr1 -- expr2) w`.

-- Shifting by non-literal amounts, e.g. `w << expr`.

-- `n2w expr` and `w2n w`. Also `w2s`, `s2w`, `w2l` and `l2w`.

-- `word_div`, `word_sdiv`, `word_mod` and `word_log2`.

### Example

Word orderings are handled:

``` hol4
- blastLib.BBLAST_CONV ``!a b. ~word_msb a /\ ~word_msb b ==> (a <+ b = a < b:word32)``;
val it =
   |- (!a b. ~word_msb a /\ ~word_msb b ==> (a <+ b <=> a < b)) <=> T
   : thm
```

In some cases the result will be a proposition over bit values:

``` hol4
- blastLib.BBLAST_CONV ``!a. (a + 1w:word8) ' 1``;
val it =
   |- (!a. (a + 1w) ' 1) <=> !a. a ' 1 <=> ~a ' 0
   : thm
```

This conversion is especially useful where "logical" and "arithmetic"
bit-vector operations are combined:

``` hol4
- blastLib.BBLAST_CONV ``!a. ((((((a:word8) * 16w) + 0x10w)) && 0xF0w) >>> 4) = (3 -- 0) (a + 1w)``;
val it =
   |- (!a. (a * 16w + 16w && 240w) >>> 4 = (3 -- 0) (a + 1w)) <=> T
   : thm
```

### See also

[`wordsLib.WORD_ss`](#wordsLib.WORD_ss),
[`wordsLib.WORD_ARITH_CONV`](#wordsLib.WORD_ARITH_CONV),
[`wordsLib.WORD_LOGIC_CONV`](#wordsLib.WORD_LOGIC_CONV),
[`wordsLib.WORD_MUL_LSL_CONV`](#wordsLib.WORD_MUL_LSL_CONV),
[`wordsLib.WORD_BIT_EQ_CONV`](#wordsLib.WORD_BIT_EQ_CONV),
[`wordsLib.WORD_EVAL_CONV`](#wordsLib.WORD_EVAL_CONV),
[`wordsLib.WORD_CONV`](#wordsLib.WORD_CONV)
