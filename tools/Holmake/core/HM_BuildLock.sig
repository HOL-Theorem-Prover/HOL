signature HM_BuildLock =
sig

  type lockhandle

  (* a no-op lock handle; release does nothing *)
  val nolock : lockhandle

  (* acquire {dir, key, warn, diag} - acquire an exclusive lock for the
     given build target. Creates dir/.hol/locks/key.lock if necessary.
     Blocks until the lock is available. On failure (e.g., unsupported
     filesystem), warns and returns a dummy handle.

     `diag` is invoked with short trace messages around the acquire,
     and again at release time; the lockhandle closes over it so
     release(lh) doesn't need it re-passed.  Typically wire diag to
     the caller's Holmake `-d` diag so lock contention shows up in
     debug output. *)
  val acquire : {dir: string, key: string, warn: string -> unit,
                 diag: string -> unit} -> lockhandle

  (* release lh - release a previously acquired lock *)
  val release : lockhandle -> unit

  (* is_real lh - true if the lock is a real fcntl lock (not a dummy) *)
  val is_real : lockhandle -> bool

end
