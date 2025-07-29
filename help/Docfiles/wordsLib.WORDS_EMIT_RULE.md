## `WORDS_EMIT_RULE`

``` hol4
wordsLib.WORDS_EMIT_RULE : rule
```

------------------------------------------------------------------------

For use with `EmitML.emitML`.

When using `EmitML.emitML` the rule `WORDS_EMIT_RULE` should be applied
to all definitions containing word operations. The rule introduces type
annotated word operations and it also handles word equality and case
statements.

### Example

``` hol4
- val example_def = Define ‘example (w:1 word) = case w of 0w -> 1w:word8 || _ -> sw2sw w’;
Definition has been stored under "example_def".
> val example_def = |- !w. example w = case w of 0w -> 1w || v -> sw2sw w : thm
- WORDS_EMIT_RULE example_def
> val it =
    |- !w.
         example w =
         case word_eq w (n2w_itself (0,(:unit))) of
            T -> n2w_itself (1,(:8))
         || F -> sw2sw_itself (:8) w : thm
```

### Comments

Before using `EmitML.emitML` the references `type_pp.pp_num_types` and
`type_pp.pp_array_types` should both be set to `false`. In addition type
abbreviations can be disabled with `disable_tyabbrev_printing` or
alternatively they must be handled by adding an appropriate signature
entry. For example:

``` hol4
- “:word8”
> val it = “:bool[8]” : hol_type
- type_pp.pp_array_types := false;
> val it = () : unit
- type_pp.pp_num_types := false;
> val it = () : unit
- disable_tyabbrev_printing "word8";
> val it = () : unit
- “:word8”;
> val it = “:unit bit0 bit0 bit0 word” : hol_type
```

If the type abbreviation is not disabled then add the entry

``` hol4
  EmitML.MLSIG "type word8 = wordsML.word8"
```
