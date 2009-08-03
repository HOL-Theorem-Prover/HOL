signature TextIO =
sig
  type instream
  type outstream
  val stdOut : outstream
  val stdErr : outstream
  val openIn : string -> instream
  val closeIn : instream -> unit

  val inputLine : instream -> string option
  val output : outstream * string -> unit
end


structure TextIO :> TextIO =
struct
  open TextIO
  fun inputLine s =
      case TextIO.inputLine s of
        "" => NONE
      | s => SOME s
end
