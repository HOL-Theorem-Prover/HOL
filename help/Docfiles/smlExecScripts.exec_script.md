## `exec_script`

``` hol4
smlExecScripts.exec_script : string -> unit
```

------------------------------------------------------------------------

Execute the script given in the file `f`.

The script is executed only for its side effects. The execution standard
out is redirected to
`src/AI/sml_inspection/buildheap/buildheap_yourscript` where yourscript
is the basename of `f` without extension. This file is worth expecting
to debug uncaught errors.

### Failure

Never fails.

### Example

``` hol4
- load "aiLib"; open aiLib;
- load "smlExecScripts"; open smlExecScripts;
(* output omitted *)
> val it = () : unit

val dir = HOLDIR ^ "/src/AI/sml_inspection"; (* user can choose *)
val scriptin = dir ^ "/script.sml";
val scriptout = dir ^ "/script-out";
(* output omitted *)

- writel scriptin
  ["load \"aiLib\"; open aiLib;",
   String.concatWith " " ["writel", mlquote scriptout, "[\"hello world!\"]"]];
> val it = (): unit

- exec_script scriptin;
> val it = (): unit

- readl "script-out";
> val it = ["hello world!"]: string list
```

### Comments

An Holmakefile might be placed in the same directory as the script to
help `exec_script` (`heapname`,`genscriptdep`) figure out the
dependencies of the script. For example, a Holmakefile might include the
line `INCLUDES = path-to-your-dependency`.

### See also

[`smlOpen.view_struct`](#smlOpen.view_struct),
[`smlExecute.quse_string`](#smlExecute.quse_string),
[`smlParallel.parmap_queue_extern`](#smlParallel.parmap_queue_extern)
