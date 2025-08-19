## `state`

``` hol4
Lib.state : ('a,'b) istream -> 'b
```

------------------------------------------------------------------------

Project the state of an istream.

An application `state istrm` yields the value of the current state of
`istrm`.

### Failure

If the projection function supplied when building the stream fails on
the current element of the state.

### Example

``` hol4
- val istrm = mk_istream (fn x => x+1) 0 (concat "gsym" o int_to_string);
> val it = <istream> : (int, string) istream

- state istrm;
> val it = "gsym0" : string

- next (next istrm);
> val it = <istream> : (int, string) istream

- state istrm;
> val it = "gsym2" : string
```

### See also

[`Lib.mk_istream`](#Lib.mk_istream), [`Lib.next`](#Lib.next),
[`Lib.reset`](#Lib.reset)
