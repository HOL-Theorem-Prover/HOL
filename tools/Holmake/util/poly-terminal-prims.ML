structure terminal_primitives :> terminal_primitives =
struct

(* thanks to Rob Arthan for this function *)
fun strmIsTTY (outstream : TextIO.outstream) =
  let
    val (wr as TextPrimIO.WR{ioDesc,...},buf) =
	TextIO.StreamIO.getWriter(TextIO.getOutstream outstream);
    val _ =
        TextIO.setOutstream (outstream, TextIO.StreamIO.mkOutstream(wr, buf))
  in
    case ioDesc of
	NONE => false
      | SOME desc => (OS.IO.kind desc = OS.IO.Kind.tty)
  end

fun TERM_isANSI () =
    case OS.Process.getEnv "TERM" of
        NONE => false
      | SOME t =>
          String.isPrefix "xterm" t orelse
          String.isPrefix "screen" t orelse
          String.isPrefix "tmux" t orelse
          t = "eterm-color"

end
