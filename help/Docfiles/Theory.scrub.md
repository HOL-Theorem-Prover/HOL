## `scrub`

``` hol4
Theory.scrub : unit -> unit
```

------------------------------------------------------------------------

Remove all out-of-date elements from the current theory segment.

An invocation `scrub()` goes through the current theory segment and
removes all out-of-date elements.

### Failure

Never fails.

### Example

In the following, we define a concrete type and examine the current
theory segment to see what consequences of this definition have been
stored there. Then we delete the type, which turns all those
consequences into garbage. An query, like `current_theorems`, shows that
this garbage is not collected automatically. A manual invocation of
`scrub` is necessary to show the true state of play.

``` hol4
   - Hol_datatype `foo = A | B of 'a`;
   <<HOL message: Defined type: "foo">>
   > val it = () : unit

   - current_theorems();
   > val it =
       [("foo_induction", |- !P. P A /\ (!a. P (B a)) ==> !f. P f),
        ("foo_Axiom", |- !f0 f1. ?fn. (fn A = f0) /\ !a. fn (B a) = f1 a),
        ("foo_nchotomy", |- !f. (f = A) \/ ?a. f = B a),
        ("foo_case_cong",
         |- !M M' v f.
              (M = M') /\ ((M' = A) ==> (v = v')) /\
              (!a. (M' = B a) ==> (f a = f' a)) ==>
              (case v f M = case v' f' M')),
        ("foo_distinct", |- !a. ~(A = B a)),
        ("foo_11", |- !a a'. (B a = B a') = (a = a'))] : (string * thm) list

   - delete_type "foo";
   > val it = () : unit

   - current_theorems();
   > val it =
       [("foo_induction", |- !P. P A /\ (!a. P (B a)) ==> !f. P f),
        ("foo_Axiom", |- !f0 f1. ?fn. (fn A = f0) /\ !a. fn (B a) = f1 a),
        ("foo_nchotomy", |- !f. (f = A) \/ ?a. f = B a),
        ("foo_case_cong",
         |- !M M' v f.
              (M = M') /\ ((M' = A) ==> (v = v')) /\
              (!a. (M' = B a) ==> (f a = f' a)) ==>
              (case v f M = case v' f' M')),
        ("foo_distinct", |- !a. ~(A = B a)),
        ("foo_11", |- !a a'. (B a = B a') = (a = a'))] : (string * thm) list

   - scrub();
   > val it = () : unit

   - current_theorems();
   > val it = [] : (string * thm) list
```

When `export_theory` is called, it uses `scrub` to prepare the current
segment for export. Users can also call `scrub` to find out what setting
they are really working in.

### See also

[`Theory.uptodate_type`](#Theory.uptodate_type),
[`Theory.uptodate_term`](#Theory.uptodate_term),
[`Theory.uptodate_thm`](#Theory.uptodate_thm),
[`Theory.delete_type`](#Theory.delete_type),
[`Theory.delete_const`](#Theory.delete_const)
