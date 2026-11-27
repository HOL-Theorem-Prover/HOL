signature hhCache =
sig
  type key_parts =
    {prover : string, version : string option, argv : string list,
     problem : string}

  (* key_of parts: the cache key of a prover run, a SHA-1 of the prover,
     its version, its arguments with the problem path replaced by the
     SHA-1 of the problem file, and that SHA-1.  key_of_digest takes that
     SHA-1 as given, to share it across requests for an immutable
     problem file. *)
  val key_of_digest : string -> key_parts -> string
  val key_of : key_parts -> string
  (* Unless the cache option is set, these do nothing; I/O errors are
     ignored.  lookup refreshes the modification time of the entry it
     reads and removes one it cannot read.  prune, past cache_max_entries
     entries, removes the least recently used down to 90% of that. *)
  val lookup : hhConfig.hh_options -> string -> hhProver.run_result option
  val store : hhConfig.hh_options -> string -> hhProver.run_result -> unit
  val prune : hhConfig.hh_options -> unit
end
