## `all_consts` {#Term.all_consts}


```
all_consts : unit -> term list
```



All known constants in the current theory.


An invocation `all_consts` returns a list of all declared constants
in the current theory, i.e., all constants in the current theory segment
and in its ancestry.

### Failure

Never fails.

### Example

    
    - all_consts();
    > val it =
        [`transitive`, `CONS`, `RES_ABSTRACT`, `COND`, `OPTION_MAP`, `FCONS`,
         `FACT`, `&`, `RPROD`, `mk_list`, `ZIP`, `IS_NUM_REP`, `ABS_sum`, `SUM`,
         `SUC`, `OPTION_JOIN`, `REP_sum`, `RTC`, `SND`, `RES_SELECT`, `THE`,
         `APPEND`, `option_REP`, `PRE`, `ABS_num`, `PRIM_REC`, `EXISTS`, `REP_num`,
         `approx`, `case`, `CONSTR`, `[]`, `$MOD`, `ODD`, `MIN`, `case`, `MEM`,
         `ISR`, `MAX`, `$LEX`, `ISO`, `case_arrow__magic`, `ISL`, `LET`, `MAP`,
         `INR`, `INL`, `$EXP`, `FST`, `case`, `mk_rec`, `IS_SOME`, `$DIV`, `ARB`,
         `option_ABS`, `wellfounded`, `iiSUC`, `SIMP_REC_REL`, `RES_FORALL`,
         `$==>`, `MK_PAIR`, `ZBOT`, `IS_NONE`, `TYPE_DEFINITION`, `case`,
         `dest_rec`, `IS_PAIR`, `ONE_ONE`, `case`, `RES_EXISTS_UNIQUE`, `NUMRIGHT`,
         `NUMPAIR`, `FILTER`, `BOTTOM`, `SOME`, `reflexive`, `EMPTY_REL`,
         `REVERSE`, `ABS_prod`, `NUMERAL_BIT2`, `NUMERAL_BIT1`, `FRONT`, `OUTR`,
         `OUTL`, `SIMP_REC`, `measure`, `NUMLEFT`, `REP_prod`, `list1`, `list0`,
         `NULL`, `ONTO`, `EVERY`, `inv_image`, `list_size`, `NONE`, `ALT_ZERO`,
         `case__magic`, `UNCURRY`, `UNZIP`, `FOLDR`, `FOLDL`, `iBIT_cases`,
         `NUMERAL`, `ZRECSPACE`, `iZ`, `case`, `iSUB`, `iSQR`, `ZCONSTR`, `WFREC`,
         `WF`, `$\/`, `TL`, `TC`, `RC`, `case_split__magic`, `$IN`, `NUMSUM`, `HD`,
         `EL`, `MAP2`, `CURRY`, `RES_EXISTS`, `LAST`, `NUMSND`, `()`, `$>=`, `$<=`,
         `INJP`, `INJN`, `INJF`, `$?!`, `INJA`, `$/\`, `IS_SUM_REP`, `RESTRICT`,
         `iDUB`, `$##`, `FUNPOW`, `NUMFST`, `EVEN`, `SUC_REP`, `$~`, `dest_list`,
         `$o`, `FNIL`, `W`, `the_fun`, `T`, `S`, `LENGTH`, `PRIM_REC_FUN`, `K`,
         `I`, `F`, `combin$C`, `$@`, `$?`, `$>`, `$=`, `$<`, `ZERO_REP`, `0`, `$-`,
         `$,`, `FLAT`, `$+`, `$*`, `$!`] : term list
    



### See also

[`Parse.term_grammar`](#Parse.term_grammar)

