## `associate_restriction`

``` hol4
Parse.associate_restriction : (string * string) -> unit
```

------------------------------------------------------------------------

Associates a restriction semantics with a binder.

If `B` is a binder and `RES_B` a constant then

``` hol4
   associate_restriction("B", "RES_B")
```

will cause the parser and pretty-printer to support:

``` hol4
               ---- parse ---->
   Bv::P. B                       RES_B  P (\v. B)
              <---- print ----
```

Anything can be written between the binder and `"::"` that could be
written between the binder and `"."` in the old notation. See the
examples below.

The following associations are predefined:

``` hol4
   \v::P. B    <---->   RES_ABSTRACT P (\v. B)
   !v::P. B    <---->   RES_FORALL   P (\v. B)
   ?v::P. B    <---->   RES_EXISTS   P (\v. B)
   @v::P. B    <---->   RES_SELECT   P (\v. B)
```

Where the constants `RES_FORALL`, `RES_EXISTS` and `RES_SELECT` are
defined in the theory `bool`, such that :

``` hol4
   |- RES_FORALL P B   =  !x:'a. P x ==> B x

   |- RES_EXISTS P B   =  ?x:'a. P x /\ B x

   |- RES_SELECT P B   =  @x:'a. P x /\ B x
```

The constant `RES_ABSTRACT` has the following characterisation

``` hol4
   |- (!p m x. x IN p ==> (RES_ABSTRACT p m x = m x)) /\
      !p m1 m2.
        (!x. x IN p ==> (m1 x = m2 x)) ==>
        (RES_ABSTRACT p m1 = RES_ABSTRACT p m2)
```

### Failure

Never fails.

### Example

``` hol4
- new_binder_definition("DURING", ``DURING(p:num#num->bool) = $!p``);
> val it = |- !p. $DURING p = $! p : thm

- ``DURING x::(m,n). p x``;
<<HOL warning: parse_term.parse_term: on line 2, characters 4-23:
parse_term: No restricted quantifier associated with DURING>>

[...]

- new_definition("RES_DURING",
                 ``RES_DURING(m,n)p = !x. m<=x /\ x<=n ==> p x``);
> val it = |- !m n p. RES_DURING (m,n) p = !x. m <= x /\ x <= n ==> p x : thm

- associate_restriction("DURING","RES_DURING");
> val it = () : unit

- ``DURING x::(m,n). p x``;
> val it = ``DURING x::(m,n). p x`` : term

- dest_comb it;
> val it = (``RES_DURING (m,n)``, ``\x. p x``) : term * term
```
