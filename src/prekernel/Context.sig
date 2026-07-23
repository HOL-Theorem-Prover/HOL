signature Context =
sig

  (* The unified prover-state container: a snapshotable value bundling the
     kernel signatures (baked in as typed fields for fast access from Term
     and Type) plus an extensible UniversalType-indexed dictionary of
     session-local slots for everything else.

     The live cell is not exposed — callers reach the current context
     through `snapshot` and mutate it through the helpers below, which
     coordinate on an internal RW-lock so `restore` is properly fenced. *)
  type t

  (* Snapshot semantics: `snapshot()` reads the current context as an
     immutable value; `restore` replaces the live context with a captured
     one.  Restore is silent — no TheoryDelta events fire — so any state
     that needs to travel with the context must live in the context.

     `restore` is a **non-logical** operation.  It rewinds the bindings
     inside the kernel signatures and every `Data` slot, but it does
     NOT rewind the process-global kernelid allocation clock (see
     `KernelSig`'s `alloc_counter`).  A `restore` followed by a fresh
     `new_definition` therefore mints a *new* constant whose kernelid
     differs from any pre-restore id of the same name — the old
     constant is reported as retired by `uptodate_id`.  This is the
     invariant `Term.same_const` / `id_compare` rely on.  Do NOT use
     `restore` as a scoping mechanism to reintroduce a name at an
     earlier epoch; see issue #2025 for the exploit that motivated
     the design.

     Locking (see Context.sml for the full story):
       - `snapshot` is lock-free: `t` is immutable, so the caller keeps
         a consistent view even if writers race with them afterwards.
       - `restore` takes the write side of an internal RW-lock, so it is
         serialised against every in-flight `Data.write` / `Data.modify`
         (which take the read side).  Concurrent `Data.write` /
         `Data.modify` calls on different slots proceed in parallel.
       - Do NOT call `restore` from inside a `Data.modify` callback —
         a thread holding the read side would block waiting for itself
         to release. *)
  val snapshot : unit -> t
  val restore  : t -> unit

  (* Whole-context mutators.  Both take the RW-lock's read side so
     `restore` won't interleave.  `f` runs under the internal Sref
     mutex, so nested `update` / `gen_update` inside `f` deadlocks;
     for cross-slot patterns use `Data.modify` instead. *)
  val update     : (t -> t) -> unit
  val gen_update : (t -> t * 'a) -> 'a

  (* Baked-in kernel-signature access.  Fast typed reads for Term/Type. *)
  val termsig  : t -> Type_dtype.holty KernelSig.symboltable
  val typesig  : t -> int KernelSig.symboltable

  val map_termsig
      : (Type_dtype.holty KernelSig.symboltable ->
         Type_dtype.holty KernelSig.symboltable) -> t -> t
  val map_typesig
      : (int KernelSig.symboltable -> int KernelSig.symboltable) -> t -> t

  (* Extensible session-local registry.  Each `new` mints a fresh
     UniversalType witness and returns a typed slot handle; the handle's
     `get`/`put`/`update` operate on the context's session-data dict.
     Slots are session-local — not serialized to `.dat`; use
     `LoadableThyData.new` for persistent theory-data. *)
  structure Data : sig
    type 'a slot
    val new    : {name : string, empty : 'a, pp : 'a -> string} -> 'a slot

    (* Pure combinators against a supplied context value. *)
    val get    : 'a slot -> t -> 'a
    val put    : 'a slot -> 'a -> t -> t
    val update : 'a slot -> ('a -> 'a) -> t -> t

    (* Direct-on-live-context mutators.  Both take the RW-lock's read
       side (fencing `restore`); `modify` additionally holds a per-slot
       mutex (serialising same-slot writers).  `f` in `modify` runs
       outside the internal Sref mutex but inside the per-slot mutex —
       do not reacquire the same slot from within `f` (same-slot
       recursion deadlocks; different-slot cross-callbacks are fine). *)
    val write  : 'a slot -> 'a -> unit
    val modify : 'a slot -> ('a -> 'a) -> unit

    (* Convenience one-liner for the common `local val slot = new {...}
       in fun x () = get slot (snapshot()); val put_x = write slot;
       val upd_x = modify slot end` boilerplate. *)
    val register :
        {name : string, empty : 'a, pp : 'a -> string} ->
        {get : unit -> 'a, write : 'a -> unit, modify : ('a -> 'a) -> unit}

    (* Lib.with_flag-style save-set-restore on a slot: writes `v`, runs
       `f x`, restores the previous value (also on exception). *)
    val with_slot_value : 'a slot -> 'a -> ('b -> 'c) -> 'b -> 'c
  end

end
