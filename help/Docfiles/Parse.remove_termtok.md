## `remove_termtok` {#Parse.remove_termtok}


```
remove_termtok : {term_name : string, tok : string} -> unit
```



Removes a rule from the global grammar.


The `remove_termtok` removes parsing/printing rules from the global
grammar.  Rules to be removed are those that are for the term with the
given name (`term_name`) and which include the string `tok` as part of
their concrete representation.  If multiple rules satisfy this
criterion, they are all removed.  If none match, the grammar is not
changed.

### Failure

Never fails.

### Example

If one wished to revert to the traditional HOL syntax for conditional
expressions, this would be achievable as follows:
    
       - remove_termtok {term_name = "COND", tok = "if"};
       > val it = () : unit
    
       - Term`if p then q else r`;
       <<HOL message: inventing new type variable names: 'a, 'b, 'c, 'd, 'e, 'f.>>
       > val it = `if p then q else r` : term
    
       - Term`p => q | r`;
       <<HOL message: inventing new type variable names: 'a.>>
       > val it = `COND p q r` : term
    
The first invocation of the parser above demonstrates that once the
rule for the `if-then-else` syntax has been removed, a string that
used to parse as a conditional expression then parses as a big
function application (the function `if` applied to five arguments).

The fact that the pretty-printer does not print the term using the
old-style syntax, even after the `if-then-else` rule has been removed,
is due to the fact that the corresponding rule in the grammar does not
have its preferred flag set.  This can be accomplished with
`prefer_form_with_tok` as follows:
    
       - prefer_form_with_tok {term_name = "COND", tok = "=>"};
       > val it = () : unit
    
       - Term`p => q | r`;
       <<HOL message: inventing new type variable names: 'a.>>
       > val it = `p => q | r` : term
    




Used to modify the global parsing/pretty-printing grammar by removing
a rule, possibly as a prelude to adding another rule which would
otherwise clash.

### Comments

As with other functions in the `Parse` structure, there is a companion
`temp_remove_termtok` function, which has the same effect on the global
grammar, but which does not cause this effect to persist when the
current theory is exported.

The specification of a rule by `term_name` and one of its tokens is
not perfect, but seems adequate in practice.

### See also

[`Parse.remove_rules_for_term`](#Parse.remove_rules_for_term), [`Parse.prefer_form_with_tok`](#Parse.prefer_form_with_tok)

