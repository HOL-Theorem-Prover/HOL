## `for_se` {#Lib.for_se}


```
for_se : int -> int -> (int -> unit) -> unit
```



Side-effecting ‘for’ loops.


An application `for_se b t f` is equal to `(f b; f (b+1); ...; f t)`.
If `b` is greater than `t`, then `for_se b t f` does no evaluation,
in particular `f b` is not evaluated.

### Failure

If `f i` fails for `b <= i <= t`.

### Example

    
    - let val A = Array.array(26,#" ")
      in
         for_se 0 25 (fn i => Array.update(A,i, Char.chr (i+97)))
       ; for_se 0 25 (print o Char.toString o curry Array.sub A)
       ; print "\n"
      end;
    
    abcdefghijklmnopqrstuvwxyz
    > val it = () : unit
    



### See also

[`Lib.for`](#Lib.for)

