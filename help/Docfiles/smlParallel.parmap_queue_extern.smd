## `paramap_queue_extern`

``` hol4
smlParallel.parmap_queue_extern :
  int -> ('a,'b,'c) extspec -> 'a -> 'b list -> 'c list)
```

------------------------------------------------------------------------

Run a function `#function` with parameter `'a` in parallel on a list of
arguments `'b list`.

The first argument of `parmap_queue_extern` precises the number of
cores. To be efficient, each of worker is executed on its own process.
Thus, I/O functions for parameter, argument list and result need to be
specfied in the structure `extspec`. The communications files are stored
under the directory `#parallel_dir`. As soon as a worker is available, a
new job is started on the next argument of the list. Since the workers
are executing from a script, it is possible to execute arbitrary
side-effect code before running `#function` by specifing
`#reflect_globals`. The directory where the signature containing
`extspec` is located has to be given in `#self_dir` and its full sml
identifier in `#self` (see Example).

### Failure

Never fails but can produce uncaught exceptions causing the main thread
to be stuck in a loop. See `buildheap_` files in subdirectories of
`#parallel_dir` for observing the standard out of `#function`.

### Example

``` hol4
(*
(* in foo.sml *)
val doublespec : (unit,int,int) extspec =
  {
  self_dir = change "directory where foo.sig is located",
  self = "foo.doublespec",
  parallel_dir = default_parallel_dir,
  reflect_globals = "()",
  function = let fun f _ (x:int) = 2 * x in f end,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = let fun f file arg = writel file [its arg] in f end,
  read_arg = let fun f file =
     string_to_int (singleton_of_list (readl file)) in f end,
  write_result = let fun f file r = writel file [its r] in f end,
  read_result = let fun f file = string_to_int (hd (readl_rm file)) in f end
  }

(* in foo.sig *)
val doublespec : (unit,int,int) extspec
*)

- load "smlParallel"; open smlParallel; load "foo"; open foo;
(* output omitted *)
> val it = (): unit

- parmap_queue_extern 2 doublespec () [1,2,3];
(* output omitted *)
> val it = [2, 4, 6]: int list
```

### Comments

If a user requires shared memory between workers, it is possible to rely
on smlParallel.parmap_queue (or Parmap.parmap). However, in general it
is quite difficult to obtain a significant speed-up when calling
smlParallel.parmap_queue (or Parmap.parmap). One reason is that the
threads need to be stopped temporarily during garbage collection.

### See also

[`smlExecScripts.exec_script`](#smlExecScripts.exec_script)
