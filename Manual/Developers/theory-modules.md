# Theory value modules

Loading a theory from source compiles its generated `FooTheory.sig` and
`FooTheory.sml`, reads `FooTheory.dat`, rebuilds every type, term and
theorem in it, and registers the theory: its place in the theory graph,
its types and constants in the kernel, its theorems in `DB`, and its
theory data. On Poly/ML runtimes with dependent modules, the loader can
save what a source load built in a module, and later loads in any
process started from the same saved state install it instead, repeating
only the registration.

## Canonical kernel ids

A kernel id is a name and an epoch. Constants defined in a session get
epochs from a process-wide counter, so the same constant can have
different ids in two processes, depending on what each did before.
Types and constants of a theory read from disk instead get a fixed
canonical epoch the first time their name is inserted in the process
(`KernelSig.insert_sealed_type` and `insert_sealed_const`: 0 for types,
-1 for constants); the counter only produces positive epochs. A loaded
theory's ids therefore depend only on its `.dat`, not on what else was
loaded or in what order.

The loader records which theories are canonical: those in the saved
state, and theories loaded with canonical ids whose parents are all
canonical. A theory defined in the session is not, and neither is a
theory loaded on top of one. Terms and theorems built while loading a
canonical theory mean the same thing in every process that shares the
saved state and has loaded the theory's ancestors, whatever the order.

A name gets each canonical epoch at most once per process, whatever
`Context.restore` or a direct update of the kernel tables does: the
sets of names that have had them are private to `KernelSig`. So two
different types or constants never share an id.
Loaded theories are sealed as before, so they cannot be loaded again.

## What a module holds

A module holds a theory's theorem values, its signature, and its data
as decoded from its `.dat` (`TheoryReader.decoded`): its parents,
types, constants, theorems, sharing tables and theory data. It depends
only on the saved state. Values shared with other theories, such as
their constants, are copied into it. The signature is the one
`export_theory` prints for the theory's theorems (`TheoryPP.pp_sig`),
compiled from that text, so every value it declares is a theorem; no
`FooTheory.sig` is read.

A later `Meta.load "FooTheory"` installs the signature where the source
loader compiles `FooTheory.sig`, loads the parents and other
dependencies listed in `FooTheory.uo` as usual, then replaces compiling
`FooTheory.sml` with the same registration steps in the same order
(`TheoryReader.register_decoded`, `Theory.record_metadata`,
`Theory.load_complete`) and only then binds the structure. Load hooks
and theory data run exactly as for a source load. The theory is linked
into the graph under the hash `FooTheory.sml` names, as a source load
does; build tools may write a hash there other than the `.dat`'s
SHA-1.

A module is used only when the theory's parents are canonical, the
other theories' types and constants its `.dat` refers to have the same
arities and principal types as when it was decoded
(`TheoryReader.refs_current`), the structures the generated source
refers to are bound as when it was saved, the kernel is `stdknl` or
`expknl`, and `TheoryReader.load_thydata_fn` has its default value.
Otherwise the theory is loaded from source.

## Loader interface

A build tool enables modules after starting from its base state:

```sml
val enabled = Meta.configureTheoryModuleCache
  {directory = "/path/to/cache", base_state = "/path/to/bin/hol.state"};
```

It returns `false` when the runtime lacks dependent modules, the base
state is not in the process's saved-state hierarchy, or the directory is
unusable; loads then stay on source.

A process that loads a theory from source then writes the theory's
module, if the theory is canonical, under a lock that makes concurrent
loaders skip it. It writes at most `!Meta.theoryModuleWriteLimit`
modules (8 by default; 0 makes the directory read-only to it): each
save scans everything the process has loaded, so one process writing
hundreds of modules costs time quadratic in their number. Loads in
ancestor order write the most shared theories first.

A directory that the processes reading it must not write, such as a
store shared by sandboxed builds, is filled by a trusted process that
runs none of a project's code:

```sml
val written = Meta.writeTheoryModules
  {theories = ["/path/to/ATheory.sml", "/path/to/BTheory.sml"],
   directory = "/path/to/cache", output = "/path/to/new-modules",
   base_state = "/path/to/bin/hol.state", limit = 8};
```

`theories` lists a load set's generated theory files in load order. For
each, it reads the theory name and hash from `FooTheory.sml` as text,
then registers the theory's types and constants from its module in
`directory`, or decodes its `.dat`. It runs no generated code, library
or load hook, and binds no theorems or theory data. It saves the
modules of up to `limit` decoded theories to `output` and stops; the
caller moves them into `directory`.

## Cache entries

A module's file name is the saved state's id, the theory name and the
SHA-1 of the `.dat` file it was decoded from:
`<state id>-<theory>-<sha1>.pmo`. Files appear by rename, so a reader
never sees a partial one. The `.dat` digest fixes the theory's own data
and its parents' hashes; the module's recorded references cover what
it takes from other theories. A missing module, or one that fails a
check (corrupt, another state, other references), is loaded from
source, and the loader replaces a failed one. Once registration has
started, errors propagate without retrying from source.

Modules are runtime-specific local files, separate from the portable
`.dat`, `.sig` and `.sml` outputs. The directory can be deleted when no
load is writing to it.
