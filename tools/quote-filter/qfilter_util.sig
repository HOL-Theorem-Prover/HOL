signature qfilter_util =
sig

  val processArgs : bool * bool * bool -> string list ->
                    {instrm: TextIO.instream,
                     outstrm : TextIO.outstream,
                     interactive: bool,
                     quotefixp : bool,
                     closefn : unit -> unit,
                     infilename : string
                    }

end
