## `reset`

``` hol4
Lib.reset : ('a,'b) istream -> ('a,'b) istream
```

------------------------------------------------------------------------

Restart an istream.

An application `reset istrm` replaces the current state of `istrm` with
the value supplied when `istrm` was constructed.

### Failure

Never fails.

### Example

``` hol4
- reset(next(next
    (mk_istream (fn x => x+1) 0 (concat "gsym" o int_to_string))));
> val it = <istream> : (int, string) istream

- state it;
> val it = "gsym0" : string
```

### Comments

Perhaps the type of `reset` should be `('a,'b) istream -> unit`.

### See also

[`Lib.mk_istream`](#Lib.mk_istream), [`Lib.next`](#Lib.next),
[`Lib.state`](#Lib.state)
