signature HostName =
sig

  (* Return the machine's hostname; "" if it can't be determined.
     Implemented per ML system: Poly/ML and mlton use
     Posix.ProcEnv.uname's "nodename" entry, Moscow ML shells out via
     Mosml.run "hostname". *)
  val get : unit -> string

end
