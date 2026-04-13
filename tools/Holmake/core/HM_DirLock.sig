signature HM_DirLock =
sig

  type lockhandle

  (* acquire {dir, warn} - acquire an exclusive lock for the given directory.
     Creates .hol/holmake.lock in dir if necessary. Blocks until the lock
     is available. On failure (e.g., unsupported filesystem), warns and
     returns a dummy handle. *)
  val acquire : {dir: string, warn: string -> unit} -> lockhandle

  (* release lh - release a previously acquired lock *)
  val release : lockhandle -> unit

  (* is_real lh - true if the lock is a real fcntl lock (not a dummy) *)
  val is_real : lockhandle -> bool

end
