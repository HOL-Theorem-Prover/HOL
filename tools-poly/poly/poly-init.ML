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
	val _ = write infile (Byte.stringToBytes inp)
	val outfile = OS.FileSys.tmpName ()
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
end;
open Mosml;

structure OS :> OS = struct
  open OS;
  structure Path = struct
    open Path;

    (* PolyML's mkCanonical appears broken.  mkCanonical "/x/y/../z" gives
       "/x/y/z".  Here is the Moscow ML implementation of mkCanonical and
       things that rely on it *)
    
    fun mkCanonical p =
    let val {isAbs, vol, arcs} = fromString p 
        fun backup []          = if isAbs then [] else [parentArc]
          | backup (".."::res) = parentArc :: parentArc :: res
          | backup ( _ :: res) = res
        fun reduce arcs = 
            let fun h []         []  = if isAbs then [""] else [currentArc]
                  | h []         res = res
                  | h (""::ar)   res = h ar res
                  | h ("."::ar)  res = h ar res
                  | h (".."::ar) res = h ar (backup res)
                  | h (a1::ar)   res = h ar (a1 :: res)
            in h arcs [] end
    in
        toString {isAbs=isAbs, vol=vol, arcs=List.rev (reduce arcs)}
    end;

    local

    fun parentize []      = []
      | parentize (_::ar) = parentArc :: parentize ar;
    in

    fun mkRelative {path=p1, relativeTo=p2} =
        case (fromString p1, fromString (mkCanonical p2)) of
            (_ ,                {isAbs=false,...}) => raise Path
          | ({isAbs=false,...}, _                ) => p1
          | ({vol=vol1, arcs=arcs1,...}, {vol=vol2, arcs=arcs2, ...}) =>
                let fun h [] [] = ["."]
                      | h a1 [] = a1
                      | h [] a2 = parentize a2
                      | h (a1 as (a11::a1r)) (a2 as (a21::a2r)) =
                        if a11=a21 then h a1r a2r
                        else parentize a2 @ (if arcs1 = [""] then [] else a1)
                in
                    if vol1 <> vol2 then raise Path 
                    else toString {isAbs=false, vol="", arcs=h arcs1 arcs2}
                end;


    fun mkAbsolute {path=p1, relativeTo=p2} =
        if isRelative p2 then raise Path
        else if isAbsolute p1 then p1
        else mkCanonical(concat(p2, p1));

    fun isCanonical p = mkCanonical p = p;
    end;
  end;
end;

val _ = use "poly/Binarymap.sig";
val _ = use "poly/Binarymap.sml";
val _ = use "poly/Binaryset.sig";
val _ = use "poly/Binaryset.sml";
val _ = use "poly/Listsort.sig";
val _ = use "poly/Listsort.sml";
