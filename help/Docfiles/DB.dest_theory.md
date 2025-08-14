## `dest_theory`

``` hol4
DB.dest_theory : string -> theory
```

------------------------------------------------------------------------

Return the contents of a theory.

An invocation `dest_theory s` returns a structure

``` hol4
   THEORY(s,{types, consts, parents, axioms, definitions, theorems})
```

where `types` is a list of `(string,int)` pairs that contains all the
type operators declared in `s`, `consts` is a list of
`(string,hol_type)` pairs enumerating all the term constants declared in
`s`, `parents` is a list of strings denoting the parents of `s`,
`axioms` is a list of `(string,thm)` pairs denoting the axioms asserted
in `s`, `definitions` is a list of `(string,thm)` pairs denoting the
definitions of `s`, and `theorems` is a list of `(string,thm)` pairs
denoting the theorems proved and stored in `s`.

The call `dest_theory "-"` may be used to access the contents of the
current theory.

### Failure

If `s` is not the name of a loaded theory.

### Example

``` hol4
- dest_theory "option";
> val it =
    Theory: option

    Parents:
        sum
        one

    Type constants:
        option 1

    Term constants:
        option_case    :'b -> ('a -> 'b) -> 'a option -> 'b
        NONE    :'a option
        SOME    :'a -> 'a option
        IS_NONE    :'a option -> bool
        option_ABS    :'a + one -> 'a option
        IS_SOME    :'a option -> bool
        option_REP    :'a option -> 'a + one
        THE    :'a option -> 'a
        OPTION_JOIN    :'a option option -> 'a option
        OPTION_MAP    :('a -> 'b) -> 'a option -> 'b option

    Definitions:
        option_TY_DEF  |- ?rep. TYPE_DEFINITION (\x. T) rep
        option_REP_ABS_DEF
        |- (!a. option_ABS (option_REP a) = a) /\
           !r. (\x. T) r = (option_REP (option_ABS r) = r)
        SOME_DEF  |- !x. SOME x = option_ABS (INL x)
        NONE_DEF  |- NONE = option_ABS (INR ())
        option_case_def
        |- (!u f. case u f NONE = u) /\ !u f x. case u f (SOME x) = f x
        OPTION_MAP_DEF
        |- (!f x. OPTION_MAP f (SOME x) = SOME (f x)) /\
           !f. OPTION_MAP f NONE = NONE
        IS_SOME_DEF  |- (!x. IS_SOME (SOME x) = T) /\ (IS_SOME NONE = F)
        IS_NONE_DEF  |- (!x. IS_NONE (SOME x) = F) /\ (IS_NONE NONE = T)
        THE_DEF  |- !x. THE (SOME x) = x
        OPTION_JOIN_DEF
        |- (OPTION_JOIN NONE = NONE) /\ !x. OPTION_JOIN (SOME x) = x

    Theorems:
        option_Axiom  |- !e f. ?fn. (!x. fn (SOME x) = f x) /\ (fn NONE = e)
        option_induction  |- !P. P NONE /\ (!a. P (SOME a)) ==> !x. P x
        SOME_11  |- !x y. (SOME x = SOME y) = (x = y)
        NOT_NONE_SOME  |- !x. ~(NONE = SOME x)
        NOT_SOME_NONE  |- !x. ~(SOME x = NONE)
        option_nchotomy  |- !opt. (opt = NONE) \/ ?x. opt = SOME x
        option_CLAUSES
        |- (!x y. (SOME x = SOME y) = (x = y)) /\ (!x. THE (SOME x) = x) /\
           (!x. ~(NONE = SOME x)) /\ (!x. ~(SOME x = NONE)) /\
           (!x. IS_SOME (SOME x) = T) /\ (IS_SOME NONE = F) /\
           (!x. IS_NONE x = (x = NONE)) /\ (!x. ~IS_SOME x = (x = NONE)) /\
           (!x. IS_SOME x ==> (SOME (THE x) = x)) /\
           (!x. case NONE SOME x = x) /\ (!x. case x SOME x = x) /\
           (!x. IS_NONE x ==> (case e f x = e)) /\
           (!x. IS_SOME x ==> (case e f x = f (THE x))) /\
           (!x. IS_SOME x ==> (case e SOME x = x)) /\
           (!u f. case u f NONE = u) /\ (!u f x. case u f (SOME x) = f x) /\
           (!f x. OPTION_MAP f (SOME x) = SOME (f x)) /\
           (!f. OPTION_MAP f NONE = NONE) /\ (OPTION_JOIN NONE = NONE) /\
           !x. OPTION_JOIN (SOME x) = x
        option_case_compute
        |- case e f x = (if IS_SOME x then f (THE x) else e)
        OPTION_MAP_EQ_SOME
        |- !f x y. (OPTION_MAP f x = SOME y) = ?z. (x = SOME z) /\ (y = f z)
        OPTION_MAP_EQ_NONE  |- !f x. (OPTION_MAP f x = NONE) = (x = NONE)
        OPTION_JOIN_EQ_SOME
        |- !x y. (OPTION_JOIN x = SOME y) = (x = SOME (SOME y))
        option_case_cong
        |- !M M' u f.
             (M = M') /\ ((M' = NONE) ==> (u = u')) /\
             (!x. (M' = SOME x) ==> (f x = f' x)) ==>
             (case u f M = case u' f' M')
  : theory
```

### Comments

A prettyprinter is installed for the type `theory`, but the contents may
still be accessed via pattern matching.

### See also

[`Hol_pp.print_theory`](#Hol_pp.print_theory)
