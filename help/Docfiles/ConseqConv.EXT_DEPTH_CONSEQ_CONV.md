## `EXT_DEPTH_CONSEQ_CONV` {#ConseqConv.EXT_DEPTH_CONSEQ_CONV}


```
EXT_DEPTH_CONSEQ_CONV : conseq_conv_congruence list ->
                        depth_conseq_conv_cache_opt -> int option ->
                        bool ->
                        (bool * int option * (thm list -> directed_conseq_conv)) list ->
                        thm list ->
                        directed_conseq_conv
```



The general depth consequence conversion of which
`DEPTH_CONSEQ_CONV`, `REDEPTH_CONSEQ_CONV`, `ONCE_DEPTH_CONSEQ_CONV` etc
are just instantiations.


`DEPTH_CONSEQ_CONV` and similar conversions are able to apply a
consequence conversion by breaking down the structure of a term using
lemmata about `/\`, `\/`, `~`, `==>`, `if-then-else` and quantification.
While doing so, these conversions collect various amounts of context information.
`EXT_DEPTH_CONSEQ_CONV` `congruence_list` `cache_opt` `step_opt`
`redepth` `convL` `context` is the function used by these other
depth conversions. For this purpose, the

`cache_opt` determines which cache to use: `NONE` means no caching; a standard
cache that stores everything is configured by
`CONSEQ_CONV_default_cache_opt`.

The number of steps taken is determined by `step_opt`. `NONE` means
arbitrarily many; `SOME n` means at most n. `ONCE_DEPTH_CONSEQ_CONV`
for example uses `SOME 1`. The parameter `redepth` determines whether
modified terms should be revisited and `convL` is a basically a list
of directed consequence conversions of the conversions that should be
applied at subpositions. Its entries consist of a flag, whether to
apply the conversion before or after descending into subterms; the
weight (i.e. the number of counted steps) for the conversion, and a
function from the context (a list of theorems) to the conversion.
`context` provides additional context that might be used.

The first parameter `congruence_list` is a list of congruence functions that
determine how to break down terms. Each element of this list has to be
a function `congruence context sys dir t` which returns a pair of the
number of performed steps and a resulting theorem. `sys` is a callback
that allows to apply the depth conversion recursively to
subterms. `context` represents the context that can be used. If you ignore the
slightly different return type, the congruence is otherwise a directed consequence
conversion. If the congruence can’t be applied, it should either fail
or raise an `UNCHANGED` exception. The callback `sys` gets the number
of already performed steps, a direction and a term. It then returns a
accumulated number of steps and a thm option. It never fails. The
number of steps is used to abort if the maximum number of globally
allowed steps has been reached. The first call of `sys` should get
`0`, then the accumulated number has to be passed. The congruence
should return the finally accumulated number of steps.

### See also

[`ConseqConv.DEPTH_CONSEQ_CONV`](#ConseqConv.DEPTH_CONSEQ_CONV), [`ConseqConv.REDEPTH_CONSEQ_CONV`](#ConseqConv.REDEPTH_CONSEQ_CONV), [`ConseqConv.ONCE_DEPTH_CONSEQ_CONV`](#ConseqConv.ONCE_DEPTH_CONSEQ_CONV), [`ConseqConv.NUM_DEPTH_CONSEQ_CONV`](#ConseqConv.NUM_DEPTH_CONSEQ_CONV)

