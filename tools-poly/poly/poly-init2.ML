(* this is an -*- sml -*- file *)
val _ = use "poly/poly-init.ML";

val _ = use "../tools/Holmake/Systeml.sig";
val _ = use "Holmake/Systeml.sml";

local

  fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
               TextIO.flushOut TextIO.stdErr;
               raise Fail s)

  fun warn s = (TextIO.output(TextIO.stdErr, "WARNING: " ^ s ^ "\n");
                TextIO.flushOut TextIO.stdErr)

  val redirected_files = ["mlibOmegaint.sml"];

  (* used to stand for "has double quote", but the same analysis is necessary
     even for files that contain single quotes because of the special
     treatment that the filter gives to things like `s1 ^ s2`
  *)
  fun try_remove f = ((OS.FileSys.remove f) handle OS.SysErr _ => ());
  fun has_dq file =
      let
        val istrm = TextIO.openIn file
        fun loop() =
            case TextIO.input1 istrm of
              NONE => false
            | SOME #"`" => true
            | SOME c => Char.ord c > 127 orelse loop()
      in
        loop() before TextIO.closeIn istrm
      end handle IO.Io _ => false
  infix ++
  fun p1 ++ p2 = OS.Path.concat (p1, p2)
  open Systeml
  fun unquote_to file1 file2 =
      systeml [HOLDIR ++ "bin" ++ "unquote", file1, file2];


structure FS = OS.FileSys

fun quse s = let
  fun mkHOLMK () =
      if FS.access (".HOLMK", [FS.A_READ, FS.A_EXEC]) andalso FS.isDir ".HOLMK"
      then true
      else
        (FS.mkDir ".HOLMK"; true)
        handle OS.SysErr (msg, _) =>
               (warn ("Couldn't make .HOLMK directory in " ^
                      FS.getDir() ^ ": " ^ msg);
                false)
  fun holtemp s =
    if mkHOLMK() then OS.Path.concat(".HOLMK", OS.Path.file s)
    else OS.FileSys.tmpName()

  val _ = if FS.access (s, [FS.A_READ]) then ()
          else die ("Use: non-existent file "^s)
in
  if has_dq s then let
      val filename = holtemp s
    in
      (if OS.Process.isSuccess (unquote_to s filename) then
         (PolyML.use filename; FS.remove filename)
       else die ("Failed to handle quotations in file: "^s^"\n"))
      handle e => (try_remove filename; raise e)
    end
  else PolyML.use s
end handle OS.Path.Path => die ("Path exception in quse "^s)

fun myuse f =
  let val op ++ = OS.Path.concat
      val file = OS.Path.file f
      val pd = !PolyML.Compiler.printDepth
  in
    PolyML.print_depth 0;
    ((if List.exists (fn f => f = file) redirected_files then
        quse (Systeml.HOLDIR ++ "tools-poly" ++ "poly" ++ "redirects" ++ file)
      else
        quse f)
     handle e => (PolyML.print_depth pd; raise e));
    PolyML.print_depth pd
  end handle OS.Path.Path => die ("Path exception in myuse "^f)

val loadPath : string list ref = ref [];

val loadedMods = ref (Binaryset.empty String.compare);
val _ =
    loadedMods := Binaryset.addList (!loadedMods,
              ["Real", "Int", "List", "Binaryset", "Binarymap","Listsort"])

fun findUo modPath [] = NONE
  | findUo modPath (search::rest) =
      let val path =
         OS.Path.mkAbsolute
           {path = modPath, relativeTo = OS.Path.mkAbsolute
                                           {path=search,
                                            relativeTo = OS.FileSys.getDir ()}};
      in
        if OS.FileSys.access (path, []) then
          SOME path
        else
          findUo modPath rest
      end;

fun loadUo uo modName =
let val i = TextIO.openIn uo
    val files =
      String.tokens (fn c => c = #"\n") (TextIO.inputAll i)
    val _ = TextIO.closeIn i
    fun loadOne f =
      (case OS.Path.ext f of
         SOME "sml" => myuse f
       | SOME "sig" => myuse f
       | _ => load f) handle OS.Path.InvalidArc => die ("Invalid arc exception in loading "^f)
                           | OS.Path.Path => die ("Path exception in loading "^f)
                           | OS.SysErr(msg,_) => die ("System error '"^msg^"' in loading "^f)
in
  List.app loadOne files
end
and load modPath =
let val modName = OS.Path.file modPath;
    fun l ext =
      case findUo (modPath ^ ext) ("."::(!loadPath)) of
        NONE => die ("Cannot find file " ^ modPath ^ ext)
      | SOME uo => loadUo uo modName;
in
  if Binaryset.member (!loadedMods, modName) then
    ()
  else
    (loadedMods := Binaryset.add (!loadedMods, modName);
     (l ".ui"; l ".uo")
     handle e =>
       (loadedMods := Binaryset.delete (!loadedMods, modName);
        raise e))
end;

in

  structure Meta = struct
    val load = load;
    val loadPath = loadPath;
    fun loaded () = Binaryset.listItems (!loadedMods);
    fun fakeload s =
        loadedMods := Binaryset.add(!loadedMods,s)
  end;

open Meta;

end;


structure PolyWord8 = Word8;
(* awfulness to make the environment look like Moscow ML's *)

(* In Poly/ML "before" is 'a * 'b -> 'a and General.before is 'a * unit -> 'a.
   The Basis library says both should be 'a * unit -> 'a, but in Moscow ML,
   before is 'a * 'b -> 'a too.  Ick. *)

structure Word8 = struct
  open PolyWord8;
  fun toLargeWord w =
    Word.fromLargeWord (PolyWord8.toLargeWord w);
end;

structure Path = OS.Path;
structure Process = OS.Process;
structure FileSys = OS.FileSys;

exception Interrupt = SML90.Interrupt;
exception Io = IO.Io;
exception SysErr = OS.SysErr;
