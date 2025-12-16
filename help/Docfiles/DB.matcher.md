## `matcher`

``` hol4
DB.matcher : (term -> term -> 'a) -> string list -> term -> data list
```

------------------------------------------------------------------------

All theory elements matching a given term.

An invocation `matcher pm [thy1,...,thyn] M` collects all elements of
the theory segments `thy1`,...,`thyn` that have a subterm `N` such that
`pm M` does not fail (raise an exception) when applied to `N`. Thus
`matcher` potentially traverses all subterms of all theorems in all the
listed theories in its search for 'matches'.

If the list of theory segments is empty, then all currently loaded
segments are examined. The string `"-"` may be used to designate the
current theory segment.

### Failure

Never fails, but may return an empty list.

### Example

``` hol4
- DB.matcher match_term ["relation"] (Term `P \/ Q`);
> val it =
    [(("relation", "RC_def"), (|- !R x y. RC R x y = (x = y) \/ R x y, Def)),
     (("relation", "RTC_CASES1"),
      (|- !R x y. RTC R x y = (x = y) \/ ?u. R x u /\ RTC R u y, Thm)),
     (("relation", "RTC_CASES2"),
      (|- !R x y. RTC R x y = (x = y) \/ ?u. RTC R x u /\ R u y, Thm)),
     (("relation", "RTC_TC_RC"),
      (|- !R x y. RTC R x y ==> RC R x y \/ TC R x y, Thm)),
     (("relation", "TC_CASES1"),
      (|- !R x z. TC R x z ==> R x z \/ ?y. R x y /\ TC R y z, Thm)),
     (("relation", "TC_CASES2"),
      (|- !R x z. TC R x z ==> R x z \/ ?y. TC R x y /\ R y z, Thm))] :
  ((string * string) * (thm * class)) list

- DB.matcher (ho_match_term [] empty_varset) [] (Term `?x. P x \/ Q x`);
<<HOL message: inventing new type variable names: 'a>>
> val it =
    [(("arithmetic", "ODD_OR_EVEN"),
      (|- !n. ?m. (n = SUC (SUC 0) * m) \/ (n = SUC (SUC 0) * m + 1), Thm)),
     (("bool", "EXISTS_OR_THM"),
      (|- !P Q. (?x. P x \/ Q x) = (?x. P x) \/ ?x. Q x, Thm)),
     (("bool", "LEFT_OR_EXISTS_THM"),
      (|- !P Q. (?x. P x) \/ Q = ?x. P x \/ Q, Thm)),
     (("bool", "RIGHT_OR_EXISTS_THM"),
      (|- !P Q. P \/ (?x. Q x) = ?x. P \/ Q x, Thm)),
     (("sum", "IS_SUM_REP"),
      (|- !f.
            IS_SUM_REP f =
            ?v1 v2.
              (f = (\b x y. (x = v1) /\ b)) \/ (f = (\b x y. (y = v2) /\ ~b)),
       Def))] : ((string * string) * (thm * class)) list
```

### Comments

Usually, `pm` will be a pattern-matcher, but it need not be.

### See also

[`DB.match`](#DB.match), [`DB.apropos`](#DB.apropos),
[`DB.matchp`](#DB.matchp), [`DB.find`](#DB.find),
[`holyHammer.hh`](#holyHammer.hh)
