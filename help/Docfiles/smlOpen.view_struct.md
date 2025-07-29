## `view_struct`

``` hol4
smlOpen.view_struct : string -> (string list * string list * string list * string list)
```

------------------------------------------------------------------------

Shows SML identifiers included in a structure (or substructure) `s`.

The first field contains values, the second exceptions (i.e Match), the
third constructions (i.e SOME) and the fourth substructures. This output
is computed by inspecting PolyML.globalNameSpace () in an external HOL4
environment.

### Failure

Fails if the structure `s` cannot be loaded by a script in the directory
`src/AI/sml_inspection/open`.

### Example

``` hol4
- load "smlOpen"; open smlOpen;
(* output omitted *)
> val it = () : unit

- view_struct "Math";
val it =
   (["sin", "sinh", "cos", "tan", "cosh", "e", "asin", "tanh", "atan2", "ln",
     "acos", "log10", "pi", "sqrt", "atan", "exp", "pow"], [], [], []):
   string list * string list * string list * string list

(* viewing substructures is also possible *)
- view_struct "HolKernel.Definition";
val it =
   (["new_definition", "new_specification", "gen_new_specification",
     "new_definition_hook", "new_type_definition"], [], [], []):
   string list * string list * string list * string list
```

### Comments

Including a Holmakefile in the directory `src/AI/sml_inspection/open`
with the line `INCLUDES = path-to-your-structure` should remove the
requirement for the structure to be in sigobj.

### See also

[`smlExecute.quse_string`](#smlExecute.quse_string),
[`smlExecScripts.exec_script`](#smlExecScripts.exec_script)
