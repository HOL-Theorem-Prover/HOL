## `remove_rules_for_term`

``` hol4
Parse.remove_rules_for_term : string -> unit
```

------------------------------------------------------------------------

Removes parsing/pretty-printing rules from the global grammar.

Calling `remove_rules_for_term s` removes all those rules (if any) in
the global grammar that are for the term `s`. The string specifies the
name of the term that the rule is for, not a token that may happen to be
used in concrete syntax for the term.

### Failure

Never fails.

### Example

The universal quantifier can have its special binder status removed
using this function:

``` hol4
   - val t = Term`!x. P x /\ ~Q x`;
   <<HOL message: inventing new type variable names: 'a.>>
   > val t = `!x. P x /\ ~Q x` : term
   - remove_rules_for_term "!";
   > val it = () : unit
   - t;
   > val it = `! (\x. P x /\ ~Q x)` : term
```

Similarly, one can remove the two rules for conditional expressions and
see the raw syntax as follows:

``` hol4
   - val t = Term`if p then q else r`;
   <<HOL message: inventing new type variable names: 'a.>>
   > val t = `if p then q else r` : term
   - remove_rules_for_term "COND";
   > val it = () : unit
   - t;
   > val it = `COND p q r` : term
```

### Comments

There is a companion `temp_remove_rules_for_term` function, which has
the same effect on the global grammar, but which does not cause this
effect to persist when the current theory is exported.

### See also

[`Parse.remove_termtok`](#Parse.remove_termtok)
