## `read`

``` hol4
Tag.read : string -> tag
```

------------------------------------------------------------------------

Make a tag suitable for use by `mk_oracle_thm`.

In order to construct a tag usable by `mk_oracle_thm`, one uses `read`,
which takes a string and makes it into a tag.

### Failure

The string must be an alphanumeric, i.e., start with an alphabetic
character and thereafter consist only of alphabetic or numeric
characters.

### Example

``` hol4
- Tag.read "Shamboozled";
> val it = Kerneltypes.TAG(["Shamboozled"], []) : tag
```

### See also

[`Thm.mk_oracle_thm`](#Thm.mk_oracle_thm), [`Thm.tag`](#Thm.tag)
