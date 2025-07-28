## `constants` {#Theory.constants}


```
constants : string -> term list
```



Returns a list of the constants defined in a named theory.


The call
    
       constants thy
    
where `thy` is an ancestor theory (the special string `"-"`
means the current theory), returns a list of all the constants in
that theory.

### Failure

Fails if the named theory does not exist, or is not an ancestor of the
current theory.

### Example

    
    - load "combinTheory";
    > val it = () : unit
    
    - constants "combin";
    > val it = [`$o`, `W`, `S`, `K`, `I`, `combin$C`] : term list
    

### See also

[`Theory.types`](#Theory.types), [`Theory.current_axioms`](#Theory.current_axioms), [`Theory.current_definitions`](#Theory.current_definitions), [`Theory.current_theorems`](#Theory.current_theorems)

