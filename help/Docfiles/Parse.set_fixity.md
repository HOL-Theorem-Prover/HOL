## `set_fixity` {#Parse.set_fixity}


```
set_fixity : string -> fixity -> unit
```



Allows the fixity of tokens to be updated.


The `set_fixity` function is used to change the fixity of single
tokens.  It implements this functionality rather crudely.  When called
on to set the fixity of `t` to `f`, it removes all rules mentioning
`t` from the global (term) grammar, and then adds a new rule to the
grammar.  The new rule maps occurrences of `t` with the given fixity
to terms of the same name.

### Failure

This function fails if the new fixity causes a clash with existing
rules, as happens if the precedence level of the specified fixity is
already taken by rules using a fixity of a different type.  Even if
the application of `set_fixity` succeeds, it may cause the next
subsequent application of the `Term` parsing function to complain
about precedence conflicts in the operator precedence matrix.  These
problems may cause the parser to behave oddly on terms involving the
token whose fixity was set.  Excessive parentheses will usually cure
even these problems.

### Example

After a new constant is defined, `set_fixity` can be used to give it
an appropriate parse status:
    
       - val thm = Psyntax.new_recursive_definition
                      prim_recTheory.num_Axiom "f"
                      (Term`(f 0 n = n) /\ (f (SUC n) m = SUC (SUC (f n m)))`);
       > val thm =
           |- (!n. f 0 n = n) /\ !n m. f (SUC n) m = SUC (SUC (f n m))
           : thm
       - set_fixity "f" (Infixl 500);
       > val it = () : unit
       - thm;
       > val it =
           |- (!n. 0 f n = n) /\ !n m. SUC n f m = SUC (SUC (n f m)) : thm
    
The same function can be used to alter the fixities of existing
constants:
    
       - val t = Term`2 + 3 + 4 - 6`;
       > val t = `2 + 3 + 4 - 6` : term
       - set_fixity "+" (Infixr 501);
       > val it = () : unit
       - t;
       > val it = `(2 + 3) + 4 - 6` : term
       - dest_comb (Term`3 - 1 + 2`);
       > val it = (`$- 3`, `1 + 2`) : term * term
    



### Comments

This function is of no use if multiple-token rules (such as those for
conditional expressions) are desired, or if the token does not
correspond to the name of the constant or variable that is to be
produced.  (For the latter case, use `set_mapped_fixity`.)

As with other functions in the `Parse` structure, there is a companion
`temp_set_fixity` function, which has the same effect on the global
grammar, but which does not cause this effect to persist when the
current theory is exported.

### See also

[`Parse.add_rule`](#Parse.add_rule), [`Parse.add_infix`](#Parse.add_infix), [`Parse.remove_rules_for_term`](#Parse.remove_rules_for_term), [`Parse.remove_termtok`](#Parse.remove_termtok), [`Parse.set_mapped_fixity`](#Parse.set_mapped_fixity)

