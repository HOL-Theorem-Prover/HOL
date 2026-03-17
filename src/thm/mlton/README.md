# Building HOL kernel modules with MLton

MLton must be invoked with `-default-type intinf` so that the default
`int` type is `IntInf.int`, matching the assumption made throughout
the HOL codebase.

For example:

    mlton -default-type intinf thm-stdknl.mlb

or for the experimental kernel:

    mlton -default-type intinf thm-expk.mlb
