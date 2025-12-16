## `listItems`

``` hol4
computeLib.listItems : compset -> ((string * string) * transform list) list
```

------------------------------------------------------------------------

List elements in compset

The function `listItems` expects a simplification set and returns a
listing of its elements, in the form of an association list mapping
constant names to the transformations that can be performed on
applications of that constant. For a given constant, more than one
transformation can be attached.

### Example

``` hol4
   > val compset = computeLib.bool_compset()
   val compset = <compset> : computeLib.compset

   > computeLib.listItems compset;
   val it =
      [(("/\\", "bool"),
        [RRules
          [|- $/\ F = (\t. F),
           |- $/\ T = (\t. t)],
         RRules
          [|- !t. t /\ t <=> t,
           |- !t. t /\ F <=> F,
           |- !t. t /\ T <=> t]]),
       (("=", "min"),
        [RRules
          [|- $<=> F = (\t. ~t),
           |- $<=> T = (\t. t)],
         RRules
          [|- !x. (x = x) <=> T],
         RRules
          [|- !t. (t <=> F) <=> ~t,
           |- !t. (t <=> T) <=> t]]),
       (("==>", "min"),
        [RRules
          [|- $==> F = (\t. T),
           |- $==> T = (\t. t)],
         RRules
          [|- !t. t ==> F <=> ~t,
           |- !t. t ==> t <=> T,
           |- !t. t ==> T <=> T]]),
       (("COND", "bool"),
        [RRules
          [|- COND F = (\t1 t2. t2),
           |- COND T = (\t1 t2. t1)],
         RRules
          [|- !t b. (if b then t else t) = t]]),
       (("F", "bool"), []),
       (("LET", "bool"),
        [RRules
          [|- !x f. LET f x = f x]]),
       (("T", "bool"), []),
       (("\\/", "bool"),
        [RRules
          [|- $\/ F = (\t. t),
           |- $\/ T = (\t. T)],
         RRules
          [|- !t. t \/ t <=> t,
           |- !t. t \/ F <=> t,
           |- !t. t \/ T <=> T]]),
       (("literal_case", "bool"),
        [RRules
          [|- !x f. literal_case f x = f x]]),
       (("~", "bool"),
        [RRules
          [|- ~F <=> T,
           |- ~T <=> F,
           |- !t. ~~t <=> t]])]
     : ((string * string) * transform list) list
```

### Failure

Should never fail.

### See also

[`computeLib.bool_compset`](#computeLib.bool_compset),
[`bossLib.EVAL`](#bossLib.EVAL),
[`computeLib.transform`](#computeLib.transform)
