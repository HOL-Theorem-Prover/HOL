## `with_exn` {#Lib.with_exn}


```
with_exn : ('a -> 'b) -> 'a -> exn -> 'b
```



Apply a function to an argument, raising supplied exception on failure.


An evaluation of `with_exn f x e` applies function `f` to
argument `x`. If that computation finishes with `y`, then `y` is
the result. Otherwise, `f x` raised an exception, and the exception
`e` is raised instead. However, if `f x` raises the `Interrupt`
exception, then `with_exn f x e` results in the `Interrupt` exception
being raised.

### Failure

When `f x` fails or is interrupted.

### Example

    
    - with_exn dest_comb (Term`\x. x /\ y`) (Fail "My kingdom for a horse");
    ! Uncaught exception:
    ! Fail  "My kingdom for a horse"
    
    - with_exn (fn _ => raise Interrupt) 1 (Fail "My kingdom for a horse");
    > Interrupted.
    



### Comments

Often `with_exn` can be used to clean up programming where lots of
exceptions may be handled. For example, taking apart a compound term of
a certain desired form may fail at several places, but a uniform error
message is desired.
    
       local val expected = mk_HOL_ERR "" "dest_quant" "expected !v.M or ?v.M"
       in
       fun dest_quant tm =
         let val (q,body) = with_exn dest_comb tm expected
             val (p as (v,M)) = with_exn dest_abs body expected
         in
            if q = universal orelse q = existential
              then p
              else raise expected
         end
       end
    



### See also

[`Feedback.wrap_exn`](#Feedback.wrap_exn), [`Lib.assert_exn`](#Lib.assert_exn), [`Lib.assert`](#Lib.assert)

