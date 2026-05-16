(* Verifies the property HM_CacheFetch.copy relies on: when
   Systeml.clone_cmd is configured, invoking it stages a file with an
   independent inode (so a downstream setTime doesn't bleed back to
   the source through hardlink-style metadata sharing). *)

open testutils

val () = tprint "Systeml.clone_cmd matches the platform"
val () =
    case (Systeml.OS, Systeml.clone_cmd) of
        ("macosx", SOME _) => OK ()
      | ("linux",  SOME _) => OK ()
      | ("winNT",  NONE)   => OK ()
      | (other,    _)      => die ("unexpected: OS=" ^ other)

val () =
    case Systeml.clone_cmd of
        NONE => ()  (* nothing else to test on this platform *)
      | SOME cmd =>
        let
          val () = tprint ("clone_cmd \"" ^ cmd ^ "\" yields fresh inode")
          val tmp = OS.FileSys.tmpName ()
          val src = tmp ^ ".src"
          val dst = tmp ^ ".dst"
          fun cleanup () =
              (OS.FileSys.remove src handle _ => ();
               OS.FileSys.remove dst handle _ => ())
          val () = cleanup ()
          val outstr = BinIO.openOut src
          val () = BinIO.output (outstr, Byte.stringToBytes "hello\n")
          val () = BinIO.closeOut outstr
          val cmd_line =
              cmd ^ " " ^ Systeml.protect src ^ " " ^ Systeml.protect dst
          val () =
              if OS.Process.isSuccess (OS.Process.system cmd_line) then ()
              else (cleanup (); die ("clone_cmd failed: " ^ cmd_line))
          val src_ino = Posix.FileSys.ST.ino (Posix.FileSys.stat src)
          val dst_ino = Posix.FileSys.ST.ino (Posix.FileSys.stat dst)
        in
          if SysWord.compare (Posix.FileSys.inoToWord src_ino,
                              Posix.FileSys.inoToWord dst_ino) = EQUAL
          then (cleanup (); die "clone produced a shared inode")
          else (cleanup (); OK ())
        end
