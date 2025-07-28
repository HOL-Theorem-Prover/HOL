## `dest_res_exists` {#res_quanTools.dest_res_exists}


```
dest_res_exists : (term -> (term # term # term))
```



Breaks apart a restricted existentially quantified term into
the quantified variable, predicate and body.


`dest_res_exists` is a term destructor for restricted existential
quantification:
    
       dest_res_exists "?var::P. t"
    
returns `("var","P","t")`.

### Failure

Fails with `dest_res_exists` if the term is not a restricted
existential quantification.

### See also

[`res_quanTools.mk_res_exists`](#res_quanTools.mk_res_exists), [`res_quanTools.is_res_exists`](#res_quanTools.is_res_exists), [`res_quanTools.strip_res_exists`](#res_quanTools.strip_res_exists)

