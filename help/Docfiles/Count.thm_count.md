## `thm_count` {#Count.thm_count}


```
thm_count :
     unit ->
     {ASSUME : int, REFL : int, BETA_CONV : int, SUBST : int,
      ABS : int, DISCH : int, MP : int, INST_TYPE : int,
      MK_COMB : int, AP_TERM : int, AP_THM : int, ALPHA : int,
      ETA_CONV : int, SYM : int, TRANS : int, EQ_MP : int,
      EQ_IMP_RULE : int, INST : int, SPEC : int, GEN : int,
      EXISTS : int, CHOOSE : int, CONJ : int, CONJUNCT1 : int,
      CONJUNCT2 : int, DISJ1 : int, DISJ2 : int, DISJ_CASES : int,
      NOT_INTRO : int, NOT_ELIM : int, CCONTR : int, GEN_ABS : int,
      definition : int, axiom : int, from_disk : int, oracle :int,
      total :int }
```



Returns the current value of the theorem counter.


If enabled, HOL maintains a counter which is incremented every time a
primitive inference is performed (or an axiom or definition set up). A
call to `thm_count()` returns the current value of this counter.
Inference counting needs to be enabled with the call
`Count.counting_thms true`.  Counting can be turned off by calling
`counting_thms false`.

The default is for inference counting not to be enabled.

### Failure

Never fails.

### See also

[`Count.apply`](#Count.apply)

