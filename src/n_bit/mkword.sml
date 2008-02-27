fun UseErr() =
(print("Usage: " ^ CommandLine.name() ^ " [-sys] [-MLdir p] n\n");
                OS.Process.exit OS.Process.failure);

(* --------------------------------------------------------------------- *)

val (sys_inst,sn,MLdir) =
  case CommandLine.arguments()
   of ["-MLdir",p,"-sys",sn] => (true,sn,p)
    | [sn,"-MLdir",p,"-sys"] => (true,sn,p)
    | [sn,"-sys","-MLdir",p] => (true,sn,p)
    | ["-MLdir",p,sn]        => (false,sn,p)
    | [sn,"-MLdir",p]        => (false,sn,p)
    | [sn]                   => (false,sn,!Globals.emitMLDir)
    | otherwise              => UseErr()

val n = valOf (Int.fromString sn) handle _ => UseErr()

(* --------------------------------------------------------------------- *)

structure word = wordFunctor (val bits = n
                              val MLdir = MLdir)

(* --------------------------------------------------------------------- *)

open wordUtil;

fun bincopy file path =  (* Dead simple file copy - binary version *)
 let open BinIO
     val (istrm,ostrm) = (openIn file, openOut path)
     fun loop() =
       case input1 istrm
        of SOME ch => (output1(ostrm,ch) ; loop())
         | NONE    => (closeIn istrm; flushOut ostrm; closeOut ostrm)
  in loop()
  end;

(* f is either bincopy or copy *)
fun update_copy src dest = let
  val t0 = FileSys.modTime src
in
  bincopy src dest;
  FileSys.setTime(dest, SOME t0)
end

(* --------------------------------------------------------------------- *)

val SIGOBJ_DIR = fullPath [Systeml.HOLDIR,"sigobj"];
val MOSMLC = fullPath [Systeml.MOSMLDIR,"mosmlc"];

val thy_file = "word" ^ sn ^ "Theory";
val lib_file = "word" ^ sn ^ "Lib";

fun failonerror f x = if f x = OS.Process.success then ()
                      else OS.Process.exit OS.Process.failure

val _ =
    failonerror
      Systeml.systeml
      [MOSMLC, "-q", "-c", "-I", SIGOBJ_DIR, "Overlay.ui", thy_file^ ".sig"];

val _ =
    failonerror
      Systeml.systeml
      [MOSMLC, "-q", "-c", "-I", SIGOBJ_DIR, "Overlay.ui", thy_file ^ ".sml"];

(* --------------------------------------------------------------------- *)

val _ =
  let open TextIO
      val ostrm = openOut(lib_file ^ ".sml")
  in (output(ostrm,
      "structure " ^ lib_file ^ " = wordFunctorLib(structure wordTheory = " ^ thy_file ^ ");") ;
      flushOut ostrm ; closeOut ostrm)
  end;

val _ =
    failonerror
      Systeml.systeml
      [MOSMLC, "-q", "-c", "-I", SIGOBJ_DIR, "Overlay.ui",
       "wordFunctorLib.ui", lib_file ^ ".sml"];

(* --------------------------------------------------------------------- *)

val _ = if sys_inst then
    (update_copy (thy_file ^ ".sig") (fullPath [SIGOBJ_DIR,thy_file ^ ".sig"]) ;
     update_copy (thy_file ^ ".ui") (fullPath [SIGOBJ_DIR,thy_file ^ ".ui"]) ;
     update_copy (thy_file ^ ".uo") (fullPath [SIGOBJ_DIR,thy_file ^ ".uo"]) ;
     update_copy (lib_file ^ ".ui") (fullPath [SIGOBJ_DIR,lib_file ^ ".ui"]) ;
     update_copy (lib_file ^ ".uo") (fullPath [SIGOBJ_DIR,lib_file ^ ".uo"]))
  else ();
