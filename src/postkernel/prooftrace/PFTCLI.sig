signature PFTCLI = sig

  (* Convert traces, emit the Candle preamble, or merge selected exports.
     Arguments use the syntax printed by --help. *)
  val main : string list -> unit

end
