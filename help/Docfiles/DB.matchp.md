## `matchp`

``` hol4
DB.matchp : (thm -> bool) -> string list -> data list
```

------------------------------------------------------------------------

All theory elements satisfying a predicate.

An invocation `matchp P [thy1,...,thyn]` collects all elements of the
theory segments `thy1`,...,`thyn` that `P` holds of. If the list of
theory segments is empty, then all currently loaded segments are
examined. The string `"-"` may be used to designate the current theory
segment.

### Failure

Fails if `P` fails when applied to a theorem in one of the theories
being searched.

### Example

The following query returns all unconditional rewrite rules in the
theory `pair`.

``` hol4
- matchp (is_eq o snd o strip_forall o concl) ["pair"];
> val it =
    [(("pair", "CLOSED_PAIR_EQ"),
      (|- !x y a b. ((x,y) = (a,b)) = (x = a) /\ (y = b), Thm)),
     (("pair", "COMMA_DEF"), (|- !x y. (x,y) = ABS_prod (MK_PAIR x y), Def)),
     (("pair", "CURRY_DEF"), (|- !f x y. CURRY f x y = f (x,y), Def)),
     (("pair", "CURRY_ONE_ONE_THM"), (|- (CURRY f = CURRY g) = (f = g), Thm)),
     (("pair", "CURRY_UNCURRY_THM"), (|- !f. CURRY (UNCURRY f) = f, Thm)),
     (("pair", "ELIM_PEXISTS"),
      (|- (?p. P (FST p) (SND p)) = ?p1 p2. P p1 p2, Thm)),
     (("pair", "ELIM_PFORALL"),
      (|- (!p. P (FST p) (SND p)) = !p1 p2. P p1 p2, Thm)),
     (("pair", "ELIM_UNCURRY"),
      (|- !f. UNCURRY f = (\x. f (FST x) (SND x)), Thm)),
     (("pair", "EXISTS_PROD"), (|- (?p. P p) = ?p_1 p_2. P (p_1,p_2), Thm)),
     (("pair", "FORALL_PROD"), (|- (!p. P p) = !p_1 p_2. P (p_1,p_2), Thm)),
     (("pair", "FST"), (|- !x y. FST (x,y) = x, Thm)),
     (("pair", "IS_PAIR_DEF"),
      (|- !P. IS_PAIR P = ?x y. P = MK_PAIR x y, Def)),
     (("pair", "LAMBDA_PROD"),
      (|- !P. (\p. P p) = (\(p1,p2). P (p1,p2)), Thm)),
     (("pair", "LET2_RAND"),
      (|- !P M N. P (let (x,y) = M in N x y) = (let (x,y) = M in P (N x y)),
       Thm)),
     (("pair", "LET2_RATOR"),
      (|- !M N b. (let (x,y) = M in N x y) b = (let (x,y) = M in N x y b),
       Thm)),
     (("pair", "LEX_DEF"),
      (|- !R1 R2. R1 LEX R2 = (\(s,t) (u,v). R1 s u \/ (s = u) /\ R2 t v),
       Def)),
     (("pair", "MK_PAIR_DEF"),
      (|- !x y. MK_PAIR x y = (\a b. (a = x) /\ (b = y)), Def)),
     (("pair", "PAIR"), (|- !x. (FST x,SND x) = x, Def)),
     (("pair", "pair_case_def"), (|- case = UNCURRY, Def)),
     (("pair", "pair_case_thm"), (|- case f (x,y) = f x y, Thm)),
     (("pair", "PAIR_EQ"), (|- ((x,y) = (a,b)) = (x = a) /\ (y = b), Thm)),
     (("pair", "PAIR_MAP"),
      (|- !f g p. (f ## g) p = (f (FST p),g (SND p)), Def)),
     (("pair", "PAIR_MAP_THM"),
      (|- !f g x y. (f ## g) (x,y) = (f x,g y), Thm)),
     (("pair", "PEXISTS_THM"), (|- !P. (?x y. P x y) = ?(x,y). P x y, Thm)),
     (("pair", "PFORALL_THM"), (|- !P. (!x y. P x y) = !(x,y). P x y, Thm)),
     (("pair", "RPROD_DEF"),
      (|- !R1 R2. RPROD R1 R2 = (\(s,t) (u,v). R1 s u /\ R2 t v), Def)),
     (("pair", "SND"), (|- !x y. SND (x,y) = y, Thm)),
     (("pair", "UNCURRY"), (|- !f v. UNCURRY f v = f (FST v) (SND v), Def)),
     (("pair", "UNCURRY_CURRY_THM"), (|- !f. UNCURRY (CURRY f) = f, Thm)),
     (("pair", "UNCURRY_DEF"), (|- !f x y. UNCURRY f (x,y) = f x y, Thm)),
     (("pair", "UNCURRY_ONE_ONE_THM"),
      (|- (UNCURRY f = UNCURRY g) = (f = g), Thm)),
     (("pair", "UNCURRY_VAR"),
      (|- !f v. UNCURRY f v = f (FST v) (SND v), Thm))]
 : ((string * string) * (thm * class)) list
```

### See also

[`DB.match`](#DB.match), [`DB.matcher`](#DB.matcher),
[`DB.apropos`](#DB.apropos), [`DB.find`](#DB.find),
[`holyHammer.hh`](#holyHammer.hh)
