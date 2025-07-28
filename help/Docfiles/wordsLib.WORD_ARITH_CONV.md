## `WORD_ARITH_CONV` {#wordsLib.WORD_ARITH_CONV}


```
WORD_ARITH_CONV : conv
```



Conversion based on `WORD_ARITH_ss` and `WORD_ARITH_EQ_ss`.


The conversion `WORD_ARITH_CONV` converts word arithmetic expressions into a
canonical form.

### Example

`WORD_ARITH_CONV` fixes the sign of equalities.
    
    - SIMP_CONV (std_ss++WORD_ARITH_ss++WORD_ARITH_EQ_ss) [] “$- a = b : 'a word”
    > val it = |- ($- a = b) = ($- 1w * a + $- 1w * b = 0w) : thm
    
    - WORD_ARITH_CONV “$- a = b : 'a word”
    > val it = |- ($- a = b) = (a + b = 0w) : thm
    

### Comments

The fragment `WORD_ARITH_EQ_ss` and conversion `WORD_CONV` do not adjust the
sign of equalities.

### See also

[`wordsLib.WORD_ARITH_ss`](#wordsLib.WORD_ARITH_ss), [`wordsLib.WORD_ARITH_EQ_ss`](#wordsLib.WORD_ARITH_EQ_ss), [`wordsLib.WORD_LOGIC_CONV`](#wordsLib.WORD_LOGIC_CONV), [`wordsLib.WORD_MUL_LSL_CONV`](#wordsLib.WORD_MUL_LSL_CONV), [`wordsLib.WORD_CONV`](#wordsLib.WORD_CONV), [`wordsLib.WORD_BIT_EQ_CONV`](#wordsLib.WORD_BIT_EQ_CONV), [`wordsLib.WORD_EVAL_CONV`](#wordsLib.WORD_EVAL_CONV)

