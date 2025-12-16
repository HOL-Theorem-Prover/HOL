## `syntax_fns`

``` hol4
HolKernel.syntax_fns : {dest: term -> exn -> term -> 'a, make: term -> 'b -> term, n: int} -> string -> string ->
             term * ('b -> term) * (term -> 'a) * (term -> bool)
```

------------------------------------------------------------------------

Helps in providing syntax support for theory constants.

`syntax_fns syntax thy name` returns a 4-tuple, consisting of: a term, a
term destructor function, a term constructor function and a term
recogniser function. These provide syntax support for operation `name`
from theory `thy`. The record argument `syntax` consists of
`dest: term -> exn -> term -> 'a` and `make: term -> 'b -> term`
functions, together with an "expected arity" value `n`. Through a
sequence of instantiations, the `syntax_fns` function can be used to
quickly and reliably write a `thySyntax.sml` file.

### Example

To provide syntax support for unary operations from the theory `num`,
one can use the following function:

``` hol4
> val num1 = HolKernel.syntax_fns {n = 1, make = HolKernel.mk_monop, dest = HolKernel.dest_monop} "num";
val num1 = fn:
   string -> term * (term -> term) * (term -> term) * (term -> bool)
```

The following call then provides support for the `SUC` constant:

``` hol4
> val (suc_tm, mk_suc, dest_suc, is_suc) = num1 "SUC";
val dest_suc = fn: term -> term
val is_suc = fn: term -> bool
val mk_suc = fn: term -> term
val suc_tm = ``SUC``: term
```

A `SUC` term can be constructed with

``` hol4
> val tm = mk_suc ``4n``;
val tm = ``SUC 4``: term
```

The resulting term `tm` can be identified and destructed as follows:

``` hol4
> is_suc tm;
val it = true: bool
> val v = dest_suc tm;
val v = ``4``: term
```

A standard error message is raised when `dest_suc` fails, e.g.

``` hol4
> is_suc ``SUC``;
val it = false: bool
> val v = dest_suc ``SUC``;
Exception-
   HOL_ERR
     {message = "", origin_function = "dest_SUC", origin_structure =
     "numSyntax"} raised
```

The value `n` in the call to `syntax_fns` acts purely as a sanity check.
For example, the following fails because `SUC` is not a binary
operation:

``` hol4
> HolKernel.syntax_fns {n = 2, make = HolKernel.mk_binop, dest = HolKernel.dest_binop} "num" "SUC";
Exception-
   HOL_ERR
     {message = "bad number of arguments", origin_function = "systax_fns",
       origin_structure = "numSyntax"} raised
```

Typically, the `dest` and `make` functions will be complementary (with
type variables `'a` and `'b` being the same), however this need not be
the case. Advanced uses of `syntax_fns` can take types into
consideration. For example, the constant `bitstring$v2w` with type
`bitstring->'a word` is supported as follows:

``` hol4
> val tm = bitstringSyntax.mk_v2w (``l:bitstring``, ``:32``);
val tm = ``v2w l``: term
> type_of tm;
val it = ``:word32``: hol_type
> bitstringSyntax.dest_v2w tm;
val it = (``l``, ``:32``): term * hol_type
```

This is implemented as follows:

``` hol4
val (v2w_tm, mk_v2w, dest_v2w, is_v2w) =
   HolKernel.syntax_fns
     {n = 1,
      dest = fn tm1 => fn e => fn w => (HolKernel.dest_monop tm1 e w, wordsSyntax.dim_of w),
      make = fn tm => fn (v, ty) => Term.mk_comb (Term.inst [Type.alpha |-> ty] tm, v)}
     "bitstring" "v2w"
```
