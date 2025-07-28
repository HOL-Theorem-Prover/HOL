## `overload_on` {#Parse.overload_on}


```
Parse.overload_on : string * term -> unit
```



Establishes a term as one of the overloading possibilities for a string.


Calling `overload_on(name,tm)` establishes `tm` as a possible
resolution of the overloaded `name`.  The call to `overload_on` also
ensures that `tm` is the first in the list of possible resolutions
chosen when a string might be parsed into a term in more than one way,
and this is the only effect if this combination is already recorded as
a possible overloading.

When printing, this call causes `tm` to be seen as the operator
`name`.  The string `name` may prompt further pretty-printing if it is
involved in any of the relevant grammar’s rules for concrete syntax.

If `tm` is an abstraction, then the parser will perform
beta-reductions if the term is the function part of a redex position.

### Failure

Never fails.

### Example

We define the equivalent of intersection over predicates:
    
       - val inter = new_definition("inter", Term`inter p q x = p x /\ q x`);
       <<HOL message: inventing new type variable names: 'a.>>
       > val inter = |- !p q x. inter p q x = p x /\ q x : thm
    
We overload on our new intersection constant, and can
be sure that in ambiguous situations, it will be preferred:
    
       - overload_on ("/\\", Term`inter`);
       <<HOL message: inventing new type variable names: 'a.>>
       > val it = () : unit
       - Term`p /\ q`;
       <<HOL message: more than one resolution of overloading was possible.>>
       <<HOL message: inventing new type variable names: 'a.>>
       > val it = `p /\ q` : term
       - type_of it;
       > val it = `:'a -> bool` : hol_type
    
Note that the original constant is considered overloaded to
itself, so that our one call to `overload_on` now allows for two
possibilities whenever the identifier `/\` is seen.  In order to make
normal conjunction the preferred choice, we can call `overload_on`
with the original constant:
    
       - overload_on ("/\\", Term`bool$/\`);
       > val it = () : unit
       - Term`p /\ q`;
       <<HOL message: more than one resolution of overloading was possible.>>
       > val it = `p /\ q` : term
       - type_of it;
       > val it = `:bool` : hol_type
    
Note that in order to specify the original conjunction
constant, we used the qualified identifier syntax, with the `$`.  If
we’d used just `/\`, the overloading would have ensured that this was
parsed as `inter`.  Instead of the qualified identifier syntax, we
could have also constrained the type of conjunction explicitly so that
the original constant would be the only possibility.  Thus:
    
       - overload_on ("/\\", Term`/\ :bool->bool->bool`);
       > val it = () : unit
    
The ability to overload to abstractions allows the use of simple
symbols for “complicated” effects, without needing to actually
define new constants.
    
       - overload_on ("|<", Term`\x y. ~(x < y)`);
       > val it = () : unit
    
       - set_fixity "|<" (Infix(NONASSOC, 450));
       > val it = () : unit
    
       - val t = Term`p |< q`;
       > val t = `p |< q` : term
    
       - dest_neg t;
       > Val it = `p < q` : term
    
This facility is used to provide symbols for “is-not-equal” (`<>`),
and “is-not-a-member” (`NOTIN`).

### Comments

Overloading with abandon can lead to input that is very hard to make
sense of, and so should be used with caution.  There is a temporary
version of this function: `temp_overload_on`.

### See also

[`Parse.clear_overloads_on`](#Parse.clear_overloads_on), [`Parse.set_fixity`](#Parse.set_fixity)

