(* this is an -*- sml -*- file *)

(* Copied from Moscow ML source *)
structure Mosml = struct
datatype runresult =
    Success of string
  | Failure of string
fun run cmd args inp =
    let fun catenate xs =
	    String.concat (List.foldr (fn (s, res) => s :: " " :: res) [] xs)
	fun write filename s =
	    let open BinIO
		val os = openOut filename
	    in output(os, s); closeOut os end
	fun read filename =
	    let open BinIO
		val is  = openIn filename
		val res = inputAll is
	    in closeIn is; res end
	val infile  = OS.FileSys.tmpName ()
	val outfile = OS.FileSys.tmpName ()
    in let
	val _ = write infile (Byte.stringToBytes inp)
	val cmdline =
	    (* This should work for Bourne sh, POSIX sh, ksh, bash: *)
	    catenate (cmd :: List.@(args, ["<", infile, "1>", outfile,
					   "2>&1"]))
	    (* This works for bash, csh and tcsh: *)
	    (* catenate (cmd :: List.@(args, ["<", infile, "&>", outfile])) *)
	val status = OS.Process.system cmdline
	val result = if OS.Process.isSuccess status then
			 Success (Byte.bytesToString (read outfile))
		     else
			 ((Failure (Byte.bytesToString (read outfile)))
			  handle IO.Io _ => Failure (cmd ^ ": command failed"))
    in
	(OS.FileSys.remove infile)  handle OS.SysErr _ => ();
	(OS.FileSys.remove outfile) handle OS.SysErr _ => ();
	result
    end
handle e =>
((OS.FileSys.remove infile)  handle OS.SysErr _ => ();
 (OS.FileSys.remove outfile) handle OS.SysErr _ => ();
 raise e)
end
end;

val _ = use "poly/Binarymap.sig";
val _ = use "poly/Binarymap.sml";
val _ = use "poly/Binaryset.sig";
val _ = use "poly/Binaryset.sml";
val _ = use "poly/Listsort.sig";
val _ = use "poly/Listsort.sml";
val _ = use "poly/holpathdb.sig";
val _ = use "poly/holpathdb.sml";
