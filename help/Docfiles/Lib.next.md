## `next`

``` hol4
Lib.next : ('a,'b) istream -> ('a,'b) istream
```

------------------------------------------------------------------------

Move to the next element in the stream.

An application `next istrm` moves to the next element in the stream.

### Failure

If the transition function supplied when building the stream fails on
the current state.

### Example

``` hol4
- val istrm = mk_istream (fn x => x+1) 0 (concat "gsym" o int_to_string);
> val it = <istream> : (int, string) istream

- next istrm;
> val it = <istream> : (int, string) istream
```

### Comments

Perhaps the type of `next` should be `('a,'b) istream -> unit`.

### See also

[`Lib.mk_istream`](#Lib.mk_istream), [`Lib.state`](#Lib.state),
[`Lib.reset`](#Lib.reset)
