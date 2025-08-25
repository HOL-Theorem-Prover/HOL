## `unmapped`

``` hol4
computeLib.unmapped : compset -> (string * string) list
```

------------------------------------------------------------------------

List unmapped elements in compset

The function `unmapped` takes a `compset` value and returns a listing of
the elements of the compset that have no transformation attached to
them.

### Example

The listing omits constructors, but can include constants that
effectively act as constructors for rewrites in the compset.

``` hol4
   > val compset = reduceLib.num_compset();
   val compset = <compset>: computeLib.compset

   > computeLib.unmapped compset;
   val it =
     [("BIT1", "arithmetic"), 
      ("BIT2", "arithmetic"),
      ("ZERO", "arithmetic")]
     : (string * string) list
```

### Example

In the following example, a function is added to a compset without also
adding functions that get "called" by it:

``` hol4
   > load "sortingTheory";
   val it = (): unit

  > sortingTheory.QSORT_DEF;
  val it =
     |- (!ord. QSORT ord [] = []) /\
        !t ord h.
          QSORT ord (h::t) =
           (let (l1,l2) = PARTITION (\y. ord y h) t
           in
           QSORT ord l1 ++ [h] ++ QSORT ord l2) : thm

   > val () = computeLib.add_thms [sortingTheory.QSORT_DEF] compset;

   > computeLib.unmapped compset;
   val it =
      [("APPEND", "list"), 
       ("BIT1", "arithmetic"), 
       ("BIT2", "arithmetic"),
       ("PARTITION", "sorting"), 
       ("UNCURRY", "pair"), 
       ("ZERO", "arithmetic")]
   :(string * string) list
```

### Comments

Intended to support the construction of large compsets, where it is
often unclear what functions and conversions still need to be added in
order to make applications of `EVAL_CONV` terminate.

### Failure

Never fails.

### See also

[`bossLib.EVAL`](#bossLib.EVAL),
[`computeLib.listItems`](#computeLib.listItems)
