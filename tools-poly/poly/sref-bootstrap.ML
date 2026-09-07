(* Sref, and the interrupt-safe locking it is built on, made available
   at bootstrap.

   Why here: `LSPExtension` and `lsp/server.ML` are `use`d by
   poly-init2.ML and so are compiled into `bin/hol` by polyc, before any
   of src/portableML's Holmake-built modules exist.  Both hold state that
   a pool worker and the compile thread reach at the same time, and a
   plain `ref` is the wrong thing to hold it in.

   A hand-rolled `Thread.Mutex.lock`/`unlock` would also be the wrong
   thing.  HOL cancels a compile, and the pool cancels a proof, by
   interrupting the thread; `Multithreading.synchronized` runs its
   critical section under `Thread_Attributes.uninterruptible` and
   releases the lock on the exception path, so an interrupt cannot
   strand the lock held.  That is the property worth importing.

   The chain closes quickly -- Sref -> Multithreading -> {Thread_Data,
   Exn}, Thread_Data -> {Exn, Thread_Attributes}, Exn -> nothing -- and
   each file carries its own signature.

   `ConcIsaLib` is the rebinding `Multithreading` is written against,
   and the same four files in the same order are how
   `src/portableML/rawtheory/mktool.ML` bootstraps them.  Only
   `Multithreading` wants it: `Exn`, `Thread_Attributes` and
   `Thread_Data` all want the outer `Thread`, which is why it brackets
   one file rather than the group.  It is undone afterwards, because
   `lsp/server.ML` opens `Thread` and expects the structure Poly/ML
   provides -- `ConcIsaLib` does not put it back.

   As with LSPExtension, what is loaded here is baked into `bin/hol` and
   is a *different* structure from the heap's copy, so values of these
   types must not cross between baked-in code and the sources the LSP
   `QUse.use`s at run time.  `Exn.Interrupt` is declared as an alias of
   `Thread.Thread.Interrupt`, so interrupt identity survives the split;
   `Exn.ERROR`, `Exn.EXCEPTIONS` and the `Exn.result` datatype do not. *)

val _ = use "../src/portableML/poly/Exn.sig";
val _ = use "../src/portableML/poly/Exn.sml";
val _ = use "../src/portableML/poly/Thread_Attributes.sml";
val _ = use "../src/portableML/poly/Thread_Data.sml";

structure PolyThread = Thread;
val _ = use "../src/portableML/poly/ConcIsaLib.sml";

val _ = use "../src/portableML/poly/Multithreading.sml";

structure Thread = PolyThread;

val _ = use "../src/portableML/poly/concurrent/Sref.sig";
val _ = use "../src/portableML/poly/concurrent/Sref.sml";
