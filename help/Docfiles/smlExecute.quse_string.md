## `quse_string`

``` hol4
smlExecute.quse_string : string -> bool
```

------------------------------------------------------------------------

Calls the PolyML.compiler on some SML code `c`.

The compiler is called after `c` has been unquoted. Returns false if a
failure occurs during parsing or execution and true otherwise.

### Failure

Never fails.

### Example

``` hol4
load "smlExecute"; open smlExecute;
(* output omitted *)
> val it = () : unit

- quse_string "val x = 2";
> val x = 2: int
> val it = true: bool
- x;
> val it = 2: int

- quse_string "val _ : int = 2.0";
> poly: : error: Pattern and expression have incompatible types.
  (* output omitted *)
> val it = false: bool

- val glob = ref 0.0;
> val glob = ref 0.0: int ref
- quse_string "val _ = glob := Math.pi";
> val it = true: bool
- !glob;
> val it = 3.141592654: real
```

### Comments

The compiler runs in the context of the current PolyML namespace and
modifies it.

### See also

[`smlOpen.view_struct`](#smlOpen.view_struct),
[`smlExecScripts.exec_script`](#smlExecScripts.exec_script)
