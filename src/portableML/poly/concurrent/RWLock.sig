signature RWLock =
sig

  (* A reader-writer lock.  Many readers may hold the lock concurrently;
     writers get exclusive access.  Waiting writers get preference over
     new readers, so a stream of readers cannot starve a writer.

     Same-thread re-entry: acquiring a second read-lock while already
     holding one succeeds (readers are unrestricted while no writer is
     waiting).  Attempting to take the write-lock while holding either
     kind of lock will deadlock — the design assumes the write-locked
     operation (typically Context.restore) is not called inside a
     read-locked one. *)

  type t
  val new          : string -> t

  val read_locked  : t -> (unit -> 'a) -> 'a
  val write_locked : t -> (unit -> 'a) -> 'a

end
