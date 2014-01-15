fun die s =
    (TextIO.output(TextIO.stdErr, s ^ "\n");
     TextIO.flushOut TextIO.stdErr;
     OS.Process.exit OS.Process.failure)

fun usage() =
    die ("Usage:\n  " ^ CommandLine.name() ^ " file1 file2")

fun openIn s =
    BinIO.openIn s handle IO.Io _ => die ("Bad file: "^s)

fun main() = let
  val (file1, file2) =
      case CommandLine.arguments() of
          [f1, f2] => (f1, f2)
        | _ => usage()
  val is1 = openIn file1
  val is2 = openIn file2
  fun recurse () = let
    val i1 = BinIO.inputN(is1, 1024)
             handle IO.Io _ => die "File 1 had I/O error"
    val i2 = BinIO.inputN(is2, 1024)
             handle IO.Io _ => die "File 2 had I/O error"
  in
    if i1 = i2 then
      if Word8Vector.length i1 > 0 then recurse()
      else OS.Process.exit OS.Process.success
    else OS.Process.exit OS.Process.failure
  end
in
  recurse()
end
