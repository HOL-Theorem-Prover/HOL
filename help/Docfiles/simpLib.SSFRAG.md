## `SSFRAG`

``` hol4
simpLib.SSFRAG : { ac : (thm * thm) list,
           congs  : thm list,
           convs  : {conv  : (term list -> conv) -> term list -> conv,
                     key   : (term list * term) option,
                     name  : string,
                     trace : int} list,
           dprocs : Traverse.reducer list,
           filter : (controlled_thm -> controlled_thm list) option,
           name   : string option,
           rewrs  : thm list } -> ssfrag
```

------------------------------------------------------------------------

Constructs `ssfrag` values.

The `ssfrag` type is the way in which simplification components are
packaged up and made available to the simplifier (though `ssfrag` values
must first be turned into simpsets, either by addition to an existing
simpset, or with the `mk_simpset` function).

The big record type passed to `SSFRAG` as an argument has seven fields.
Here we describe each in turn.

The `ac` field is a list of "AC theorem" pairs. Each such pair is the
pair of theorems stating that a given binary function is associative and
commutative. The theorems can be given in either order, can present the
associativity theorem in either direction, and can be generalised to any
extent.

The `congs` field is a list of congruence theorems justifying the
addition of theorems to simplification contexts. For example, the
congruence theorem for implication is

``` hol4
   |- (P = P') ==> (P' ==> (Q = Q')) ==> (P ==> Q = P' ==> Q')
```

This theorem encodes a rewriting strategy. The consequent of the chain
of implications is the form of term in question, where the appropriate
components have been rewritten. Then, in left-to-right order, the
various antecedents of the implication specify the rewriting strategy
which gives rise to the consequent. In this example, `P` is first
simplified to `P'` without any additional context, then, using `P'` as
additional context, simplification of `Q` proceeds, producing `Q'`.
Another example is a rule for conjunction:

``` hol4
   |- (P ==> (Q = Q')) ==> (Q' ==> (P = P')) ==> ((P /\ Q) = (P' /\ Q'))
```

Here `P` is assumed while `Q` is simplified to `Q'`. Then, `Q'` is
assumed while `P` is simplified to `P'`. If an antecedent doesn't
involve the relation in question (here, equality) then it is treated as
a side-condition, and the simplifier will be recursively invoked to try
and solve it.

Higher-order congruence rules are also possible. These provide a method
for dealing with bound variables. The following is a rule for the
restricted universal quantifier, for example:

``` hol4
   |- (P = Q) ==> (!v. v IN Q ==> (f v = g v)) ==>
      (RES_FORALL P f = RES_FORALL Q g)
```

(If `f` is an abstraction, `\x. t`, then `RES_FORALL P f` is
pretty-printed as `!x::P. t`) Terms in the conclusions of higher-order
congruence rules that might be abstractions (such as `f` above) should
be kept as variables, rather than written out as abstractions. In other
words, the conclusion of the congruence rule above should not be written
as

``` hol4
   RES_FORALL P (\v. f v) = RES_FORALL Q (\v. g v)
```

The `convs` field is a list of conversions that the simplifier will
apply. Each conversion added to an `ssfrag` value is done so in a record
consisting of four fields.

The `conv` field of this subsidiary record type includes the value of
the conversion itself. When the simplifier applies the conversion it is
actually passed two extra arguments (as the type indicates). The first
is a solver function that can be used to recursively do side-condition
solving, and the second is a stack of side-conditions that have been
accumulated to date. Many conversions will typically ignore these
arguments (as in the example below).

The `key` field of the subsidiary record type is an optional pattern,
specifying the places where the conversion should be applied. If the
value is `NONE`, then the conversion will be applied to all sub-terms.
If the value is `SOME(lcs, t)`, then the term `t` is used as a pattern
specifying those terms to which the conversion should be applied.
Further, the list `lcs` (which must be a list of variables), specifies
those variables in `t` which shouldn't be generalised against; they are
effectively local constants. Note, however, that the types in the
pattern term `t` will not be used to eliminate possible matches, so that
if a match is desired with a particular type instantiation of a term,
then the conversion will need to reject the input itself. The `name` and
`trace` fields are only relevant to the debugging facilities of the
simplifier.

The `dprocs` field of the record passed to `SSFRAG` is where decision
procedures can be specified. Documentation describing the construction
and use of values of type `reducer` is available in the DESCRIPTION.

The `filter` field of the record is an optional function, which, if
present, is composed with the standard simplifier's function for
generating rewrites from theorems, and replaces that function. The
version of this present in `bool_ss` and its descendents will, for
example, turn `|- P /\ Q` into `|- P` and `|- Q`, and `|- ~(t1 = t2)`
into `|- (t1 = t2) = F` and `|- (t2 = t1) = F`.

The `controlled_thm` type is defined in the module `BoundedRewrites`,
and pairs a theorem with a bound, which is either the value `UNBOUNDED`
or the constructor `BOUNDED` applied to an integer reference. The
reference is used to limit the number of times a rewrite may be applied.
The filter gets information as to whether and how a rewrite is bounded
as this can affect its decision on whether or not to include a rewrite
at all (if it looks as if it will loop, and the bound is `UNBOUNDED`, it
should be dropped, but it may choose to keep it if there is bound
present).

The `rewrs` field of the record is a list of rewrite theorems that are
to be applied.

The `name` field of the record is an optional name for the simpset
fragment that is used when it, and simpsets that it becomes part of are
pretty-printed.

### Failure

Never fails. Failure to provide theorems of just the right form may
cause later application of simplification functions to fail,
documentation to the contrary notwithstanding.

### Example

Given a conversion `MUL_CONV` to calculate multiplications, the
following illustrates how this can be added to a simpset:

``` hol4
   - val ssd = SSFRAG {ac = [], congs = [],
                        convs = [{conv = K (K MUL_CONV),
                                  key= SOME ([], Term`x * y`),
                                  name = "MUL_CONV",
                                  trace = 2}],
                        dprocs = [], filter = NONE, rewrs = []};
   > val ssd =
       SSFRAG{ac = [], congs = [],
               convs =
                 [{conv = fn, key = SOME([], `x * y`), name = "MUL_CONV",
                   trace = 2}], dprocs = [], filter = NONE, rewrs = []}
       : ssfrag
   - SIMP_CONV bool_ss [] (Term`3 * 4`);
   > val it = |- 3 * 4 = 3 * 4 : thm
   - SIMP_CONV (bool_ss ++ ssd) [] (Term`3 * 4`);
   > val it = |- 3 * 4 = 12 : thm
```

Given the theorems `ADD_SYM` and `ADD_ASSOC` from `arithmeticTheory`, we
can construct a normaliser for additive terms.

``` hol4
   - val ssd2 = SSFRAG {ac = [(SPEC_ALL ADD_ASSOC, SPEC_ALL ADD_SYM)],
                         congs = [], convs = [], dprocs = [],
                         filter = NONE, rewrs = []};
   > val ssd2 =
       SSFRAG{ac = [(|- m + n + p = (m + n) + p, |- m + n = n + m)],
               congs = [], convs = [], dprocs = [], filter = NONE,
               rewrs = []}
       : ssfrag
   - SIMP_CONV (bool_ss ++ ssd2) [] (Term`(y + 3) + x + 4`);
     (* note that the printing of + in this example is that of a
        right associative operator.*)
   > val it = |- (y + 3) + x + 4 = 3 + 4 + x + y : thm
```

### See also

[`simpLib.++`](#simpLib..KAL),
[`boolSimps.bool_ss`](#boolSimps.bool_ss),
[`simpLib.Cong`](#simpLib.Cong),
[`simpLib.mk_simpset`](#simpLib.mk_simpset),
[`simpLib.rewrites`](#simpLib.rewrites),
[`simpLib.SIMP_CONV`](#simpLib.SIMP_CONV)
