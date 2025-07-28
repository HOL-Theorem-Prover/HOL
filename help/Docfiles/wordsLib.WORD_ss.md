## `WORD_ss` {#wordsLib.WORD_ss}


```
WORD_ss : ssfrag
```



Simplification fragment for words.


The fragment `WORD_ss` contains `BIT_ss`, `SIZES_ss`, `WORD_LOGIC_ss`,
`WORD_ARITH_ss` and `WORD_SHIFT_ss`.  It also performs ground term evaluation.

### Example

    
    - SIMP_CONV (pure_ss++WORD_ss) [] “BIT i 42”
    > val it = |- BIT i 42 = i IN {1; 3; 5} : thm
    
    - SIMP_CONV (pure_ss++WORD_ss) [] “dimword(:42)”
    > val it = |- dimword (:42) = 4398046511104 : thm
    
    - SIMP_CONV (pure_ss++WORD_ss) [] “((a #<< 2 #>> 2 + a) && $- 1w) - a”
    <<HOL message: inventing new type variable names: 'a>>
    > val it = |- (a #<< 2 #>> 2 + a && $- 1w) - a = a : thm
    
    - SIMP_CONV (pure_ss++WORD_ss) [] “(4 -- 2) ($- 1w : word8)”
    > val it = |- (4 -- 2) ($- 1w) = 7w : thm
    

### Comments

The `WORD_ss` fragment does not include `WORD_ARITH_EQ_ss`, `WORD_BIT_EQ_ss`,
`WORD_EXTRACT_ss` or `WORD_MUL_LSL_ss`.  These extra fragments have more
specialised applications.

### See also

[`wordsLib.WORD_CONV`](#wordsLib.WORD_CONV), [`fcpLib.FCP_ss`](#fcpLib.FCP_ss), [`wordsLib.BIT_ss`](#wordsLib.BIT_ss), [`wordsLib.SIZES_ss`](#wordsLib.SIZES_ss), [`wordsLib.WORD_ARITH_ss`](#wordsLib.WORD_ARITH_ss), [`wordsLib.WORD_LOGIC_ss`](#wordsLib.WORD_LOGIC_ss), [`wordsLib.WORD_ARITH_EQ_ss`](#wordsLib.WORD_ARITH_EQ_ss), [`wordsLib.WORD_BIT_EQ_ss`](#wordsLib.WORD_BIT_EQ_ss), [`wordsLib.WORD_SHIFT_ss`](#wordsLib.WORD_SHIFT_ss), [`wordsLib.WORD_EXTRACT_ss`](#wordsLib.WORD_EXTRACT_ss), [`wordsLib.WORD_MUL_LSL_ss`](#wordsLib.WORD_MUL_LSL_ss)

