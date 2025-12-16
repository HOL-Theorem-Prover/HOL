## `thy`

``` hol4
DB.thy : string -> data list
```

------------------------------------------------------------------------

Return the contents of a theory.

An invocation `DB.thy s` returns the contents of the specified theory
segment `s` in a list of `(thy,name),(thm,class)` tuples. In a tuple,
`(thy,name)` designate the theory and the name given to the object in
the theory. The `thm` element is the named object, and `class` its
classification (one of `Thm` (theorem), `Axm` (axiom), or `Def`
(definition)).

Case distinctions are ignored when determining the segment. The current
segment may be specified, either by the distinguished literal `"-"`, or
by the name given when creating the segment with `new_theory`.

### Failure

Never fails, but will return an empty list when `s` does not designate a
currently loaded theory segment.

### Example

``` hol4
- DB.thy "pair";
> val it =
    [(("pair", "ABS_PAIR_THM"), (|- !x. ?q r. x = (q,r), Db.Thm)),
     (("pair", "ABS_REP_prod"),
      (|- (!a. ABS_prod (REP_prod a) = a) /\
          !r. IS_PAIR r = (REP_prod (ABS_prod r) = r), Db.Def)),
     (("pair", "CLOSED_PAIR_EQ"),
      (|- !x y a b. ((x,y) = (a,b)) = (x = a) /\ (y = b), Db.Thm)),
         .
         .
         .
```

### See also

[`DB.class`](#DB.class), [`DB.data`](#DB.data),
[`DB.listDB`](#DB.listDB), [`DB.theorems`](#DB.theorems),
[`DB.match`](#DB.match), [`Theory.new_theory`](#Theory.new_theory)
