signature qfilter_util =
sig

  val processArgs : bool * bool * bool -> string list ->
                    TextIO.instream * TextIO.outstream * bool * bool *
                    (unit -> unit)

end
