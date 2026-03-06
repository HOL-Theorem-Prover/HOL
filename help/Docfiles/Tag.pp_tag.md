## `pp_tag`

``` hol4
Tag.pp_tag : tag Parse.pprinter
```

------------------------------------------------------------------------

Prettyprinter for tags.

An invocation `pp_tag t` will produce a pretty representation for tag
`t`. Such a pretty-printer can be used to produce outputs, or return
strings, or to combine with other pretty representations to create
compound values.

### Failure

Never fails.

### Example

``` hol4
> show_tags := true;
val it = () : unit

> Portable.pprint Tag.pp_tag (Tag.read "fooble");
[oracles: fooble] [axioms: ]
val it = (): unit
```
