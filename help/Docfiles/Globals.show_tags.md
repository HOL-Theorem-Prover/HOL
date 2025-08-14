## `show_tags`

``` hol4
Globals.show_tags : bool ref
```

------------------------------------------------------------------------

Flag for controlling display of tags in theorem prettyprinter.

The flag `show_tags` controls the display of values of type `thm`. When
set to `true`, the tag attached to a theorem will be printed when the
theorem is printed. When set to `false`, no indication of the presence
or absence of a tag will be displayed.

### Example

``` hol4
- show_tags := false;
> val it = () : unit

- pairTheory.PAIR_MAP_THM;
> val it = |- !f g x y. (f ## g) (x,y) = (f x,g y) : thm

- mk_thm ([],F);
> val it = |- F : thm

- show_tags := true;
> val it = () : unit

- pairTheory.PAIR_MAP_THM;
> val it = [oracles: ] [axioms: ] [] |- !f g x y. (f ## g) (x,y) = (f x,g y)
    : thm

- mk_thm ([],F);
> val it = [oracles: MK_THM] [axioms: ] [] |- F : thm
```

### Comments

The initial value of `show_tags` is `false`.

### See also

[`Thm.tag`](#Thm.tag), [`Thm.mk_oracle_thm`](#Thm.mk_oracle_thm),
[`Thm.mk_thm`](#Thm.mk_thm)
