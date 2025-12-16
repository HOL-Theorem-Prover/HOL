## `SIMPLE_QUANT_INSTANTIATE_CONV`

``` hol4
quantHeuristicsLib.SIMPLE_QUANT_INSTANTIATE_CONV : conv
```

------------------------------------------------------------------------

A conversion for instantiating quantifiers. In contrast to
`quantHeuristicsLib.QUANT_INSTANTIATE_CONV` it only searches for gap
guesses without free variables. As a result, it is much less powerful,
but also much faster than `quantHeuristicsLib.QUANT_INSTANTIATE_CONV`.

### Failure

If no instantiation could be found.

### Example

``` hol4
> SIMPLE_QUANT_INSTANTIATE_CONV ``?x. P x /\ (x = 5)``
|- (?x. P x /\ (x = 5)) <=> P 5 /\ (5 = 5):

> SIMPLE_QUANT_INSTANTIATE_CONV ``!x. (x = 5) ==> P x``
|- (!x. (x = 5) ==> P x) <=> (5 = 5) ==> P 5:

> SIMPLE_QUANT_INSTANTIATE_CONV ``!x. Q x ==> !z. Z z /\ (x = 5) ==> P x z``
|- (!x. Q x ==> !z. Z z /\ (x = 5) ==> P x z) <=>
   Q 5 ==> !z. Z z /\ (5 = 5) ==> P 5 z:

> SIMPLE_QUANT_INSTANTIATE_CONV ``!x. ((3, x, y) = zxy) ==> P x``
|- (!x. ((3,x,y) = zxy) ==> P x) <=>
   ((3,FST (SND zxy),y) = zxy) ==> P (FST (SND zxy)):

> SIMPLE_QUANT_INSTANTIATE_CONV ``some x. (x = 2) /\ P x``
|- (some x. (x = 2) /\ P x) = if (2 = 2) /\ P 2 then SOME 2 else NONE:

> SIMPLE_QUANT_INSTANTIATE_CONV ``?x1 x2 x3. P x1 x2 /\ (x2::x1::l = 3::(f x3)::l')``
|- (?x1 x2 x3. P x1 x2 /\ (x2::x1::l = 3::f x3::l')) <=>
   ?x2 x3. P (f x3) x2 /\ (x2::f x3::l = 3::f x3::l'):
```

### See also

[`quantHeuristicsLib.QUANT_INSTANTIATE_CONV`](#quantHeuristicsLib.QUANT_INSTANTIATE_CONV),
[`unwind.UNWIND_EXISTS_CONV`](#unwind.UNWIND_EXISTS_CONV),
[`unwind.UNWIND_FORALL_CONV`](#unwind.UNWIND_FORALL_CONV),
[`quantHeuristicsLib.SIMPLE_QUANT_INST_ss`](#quantHeuristicsLib.SIMPLE_QUANT_INST_ss),
[`bossLib.SQI_ss`](#bossLib.SQI_ss)
