## `RED_CONV`

``` hol4
reduceLib.RED_CONV : conv
```

------------------------------------------------------------------------

Performs arithmetic or boolean reduction at top level if possible.

The conversion `RED_CONV` attempts to apply, at the top level only, one
of the following conversions from the `reduce` library (only one can
succeed):

``` hol4
   ADD_CONV  AND_CONV  BEQ_CONV  COND_CONV
   DIV_CONV  EXP_CONV   GE_CONV    GT_CONV
   IMP_CONV   LE_CONV   LT_CONV   MOD_CONV
   MUL_CONV  NEQ_CONV  NOT_CONV    OR_CONV
   PRE_CONV  SBC_CONV  SUC_CONV
```

### Failure

Fails if none of the above conversions are applicable at top level.

### Example

``` hol4
#RED_CONV "(2=3) = F";;
|- ((2 = 3) = F) = ~(2 = 3)

#RED_CONV "15 DIV 13";;
|- 15 DIV 13 = 1

#RED_CONV "100 + 100";;
|- 100 + 100 = 200

#RED_CONV "0 + x";;
evaluation failed     RED_CONV
```

### See also

[`reduceLib.REDUCE_CONV`](#reduceLib.REDUCE_CONV),
[`reduceLib.REDUCE_RULE`](#reduceLib.REDUCE_RULE),
[`reduceLib.REDUCE_TAC`](#reduceLib.REDUCE_TAC)
