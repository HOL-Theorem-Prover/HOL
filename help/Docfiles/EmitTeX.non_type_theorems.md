## `non_type_theorems`

``` hol4
EmitTeX.non_type_theorems : string -> (string * thm) list
```

------------------------------------------------------------------------

A versions of `theorems` that attempts to filter out theorems created by
`Hol_datatype`.

An invocation `non_type_theorems thy`, where `thy` is the name of a
currently loaded theory segment, will return a list of the theorems
stored in that theory. Axioms and definitions are excluded. Each theorem
is paired with its name in the result.

### Failure

Never fails. If `thy` is not the name of a currently loaded theory
segment, the empty list is returned.

### Example

``` hol4
- new_theory "example";
<<HOL message: Created theory "example">>
> val it = () : unit
- val _ = Hol_datatype `example = First | Second`;
<<HOL message: Defined type: "example">>
- val example_def = Define
    `(example First = Second) /\ (example Second = First)`;
Definition has been stored under "example_def".
> val example_def = |- (example First = Second) /\ (example Second = First) :
  thm
- save_thm("example_thm",
   METIS_PROVE [example_def, theorem "example_nchotomy"]
     ``!x. example (example x) = x``);
metis: r[+0+5]+0+0+0+0+6+2+2+1+0+1+1#
> val it = |- !x. example (example x) = x : thm

- theorems "example";
> val it =
    [("num2example_example2num", |- !a. num2example (example2num a) = a),
     ("example2num_num2example",
      |- !r. r < 2 = (example2num (num2example r) = r)),
     ("num2example_11",
      |- !r r'.
           r < 2 ==> r' < 2 ==> ((num2example r = num2example r') = (r = r'))),
     ("example2num_11", |- !a a'. (example2num a = example2num a') = (a = a')),
     ("num2example_ONTO", |- !a. ?r. (a = num2example r) /\ r < 2),
     ("example2num_ONTO", |- !r. r < 2 = ?a. r = example2num a),
     ("num2example_thm",
      |- (num2example 0 = First) /\ (num2example 1 = Second)),
     ("example2num_thm",
      |- (example2num First = 0) /\ (example2num Second = 1)),
     ("example_EQ_example",
      |- !a a'. (a = a') = (example2num a = example2num a')),
     ("example_case_def",
      |- (!v0 v1. (case First of First -> v0 || Second -> v1) = v0) /\
         !v0 v1. (case Second of First -> v0 || Second -> v1) = v1),
     ("datatype_example", |- DATATYPE (example First Second)),
     ("example_distinct", |- ~(First = Second)),
     ("example_case_cong",
      |- !M M' v0 v1.
           (M = M') /\ ((M' = First) ==> (v0 = v0')) /\
           ((M' = Second) ==> (v1 = v1')) ==>
           ((case M of First -> v0 || Second -> v1) =
            case M' of First -> v0' || Second -> v1')),
     ("example_nchotomy", |- !a. (a = First) \/ (a = Second)),
     ("example_Axiom", |- !x0 x1. ?f. (f First = x0) /\ (f Second = x1)),
     ("example_induction", |- !P. P First /\ P Second ==> !a. P a),
     ("example_thm", |- !x. example (example x) = x)] : (string * thm) list

- EmitTeX.non_type_theorems "example";
> val it = [("example_thm", |- !x. example (example x) = x)] :
  (string * thm) list
```

### See also

[`DB.theorems`](#DB.theorems),
[`bossLib.Hol_datatype`](#bossLib.Hol_datatype)
