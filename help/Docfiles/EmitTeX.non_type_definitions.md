## `non_type_definitions` {#EmitTeX.non_type_definitions}


```
non_type_definitions : string -> (string * thm) list
```



A versions of `definitions` that attempts to filter out definitions created by `Hol_datatype`.


An invocation `non_type_definitions thy`, where `thy` is the name of a currently
loaded theory segment, will return a list of the definitions stored in
that theory. Each definition is paired with its name in the result.

### Failure

Never fails. If `thy` is not the name of a currently loaded theory segment,
the empty list is returned.

### Example

    
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
    
    - definitions "example";
    > val it =
        [("example_TY_DEF", |- ?rep. TYPE_DEFINITION (\n. n < 2) rep),
         ("example_BIJ",
          |- (!a. num2example (example2num a) = a) /\
             !r. (\n. n < 2) r = (example2num (num2example r) = r)),
         ("First", |- First = num2example 0),
         ("Second", |- Second = num2example 1),
         ("example_size_def", |- !x. example_size x = 0),
         ("example_case",
          |- !v0 v1 x.
               (case x of First -> v0 || Second -> v1) =
               (\m. (if m = 0 then v0 else v1)) (example2num x)),
         ("example_def", |- (example First = Second) /\ (example Second = First))]
         : (string * thm) list
    
    - EmitTeX.non_type_definitions "example";
    > val it =
        [("example_def", |- (example First = Second) /\ (example Second = First))]
         : (string * thm) list
    

### See also

[`DB.definitions`](#DB.definitions), [`bossLib.Hol_datatype`](#bossLib.Hol_datatype)

