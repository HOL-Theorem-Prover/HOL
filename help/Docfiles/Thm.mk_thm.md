## `mk_thm`

``` hol4
Thm.mk_thm : term list * term -> thm
```

------------------------------------------------------------------------

Creates an arbitrary theorem (dangerous!).

The function `mk_thm` can be used to construct an arbitrary theorem. It
is applied to a pair consisting of the desired assumption list (possibly
empty) and conclusion. All the terms therein should be of type `bool`.

``` hol4
   mk_thm([a1,...,an],c) = ({a1,...,an} |- c)
```

`mk_thm` is an application of `mk_oracle_thm`, and every application of
it tags the resulting theorem with `MK_THM`.

### Failure

Fails unless all the terms provided for assumptions and conclusion are
of type `bool`.

### Example

The following shows how to create a simple contradiction:

``` hol4
   - val falsity = mk_thm([],boolSyntax.F);
   > val falsity = |- F : thm

   - Globals.show_tags := true;
   > val it = () : unit

   - falsity;
   > val it = [oracles: MK_THM] [axioms: ] [] |- F : thm
```

### Comments

Although `mk_thm` can be useful for experimentation or temporarily
plugging gaps, its use should be avoided if at all possible in important
proofs, because it can be used to create theorems leading to
contradictions. The example above is a trivial case, but it is all too
easy to create a contradiction by asserting 'obviously sound' theorems.

All theorems which are likely to be needed can be derived using only
HOL's inbuilt axioms and primitive inference rules, which are provably
sound (see the DESCRIPTION). Basing all proofs, normally via derived
rules and tactics, on just these axioms and inference rules gives proofs
which are (apart from bugs in HOL or the underlying system) completely
secure. This is one of the great strengths of HOL, and it is foolish to
sacrifice it to save a little work.

Because of the way tags are propagated during proof, a theorem proved
with the aid of `mk_thm` is detectable by examining its tag.

### See also

[`Theory.new_axiom`](#Theory.new_axiom),
[`Thm.mk_oracle_thm`](#Thm.mk_oracle_thm), [`Thm.tag`](#Thm.tag),
[`Globals.show_tags`](#Globals.show_tags)
