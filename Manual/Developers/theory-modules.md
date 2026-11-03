# Compiled theory initializers

Loading generated theory source both compiles ML code and installs logical
state. Reusing initialized theorem values from another process would skip
registration and could retain that process's kernel identities. The Poly/ML
loader can instead cache compiled initializer code and execute its setup in
each consumer.

## Generated source

On Poly/ML, each generated `FooTheory.sml` declares a functor named `FooTheory`,
then applies it to produce the existing `FooTheory` structure. Functor and
structure names occupy separate ML namespaces. The functor takes the current `.dat`
path and reads the theory data when applied. Its result contains the same
public theorem bindings as the existing generated signature.
Moscow ML retains its existing generated structure format.

Dependency opens remain outside the functor, so dependency discovery and
loading retain their ordinary order. The marked initializer body uses
qualified core structures and no theorem values from its parents. Its
application performs theory registration, metadata installation and load hooks
on every load.

## Loader interface

On Poly/ML, a build tool can enable the cache after loading its base HOL state:

```sml
val enabled = Meta.configureTheoryModuleCache
  {directory = "/path/to/cache", base_state = "/path/to/bin/hol.state"};
```

The named base state must already be in the process's saved-state hierarchy.
The function returns `false` if the runtime lacks dependent-module support,
the base is absent, or the cache directory cannot be used. Ordinary
`Meta.load` calls then continue using the source loader. Custom `Meta.loadPlan`
callbacks are unaffected.

An enabled loader saves compiled initializers after source loads. A build tool
can also call `Meta.produceTheoryModule "FooTheory.sml"` immediately after
export. This compiles the marked initializer without applying it, because
loading the exported theory again would attempt to reopen a sealed kernel
segment. Production does nothing when the cache is disabled.

## Cache compatibility

The source contents and exact base saved-state identity select a module.
Checksums are verified before native module loading. A cached initializer also
carries the core ML bindings it was compiled against; changing one makes the
loader use source instead. Missing, corrupt or incompatible modules cause
source loading and regeneration. An exception during initialization propagates
without retrying, because load hooks may already have had effects.

Modules contain compiled functor metadata and depend only on the designated
base state. They do not contain initialized theory values or load additional
parents themselves. Build tools should keep these runtime-specific files
separate from portable `.dat`, `.sig` and `.sml` outputs. The cache directory
may be deleted when no production is in progress; later loads reconstruct it.
