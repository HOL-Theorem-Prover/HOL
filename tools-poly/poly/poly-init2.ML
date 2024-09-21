(* this is an -*- sml -*- file *)
val _ = use "poly/poly-init.ML";

val _ = use "../tools/Holmake/Systeml.sig";
val _ = use "Holmake/Systeml.sml"

val _ = use "../tools/Holmake/AttributeSyntax.sig";
val _ = use "../tools/Holmake/AttributeSyntax.sml";
val _ = use "../tools/Holmake/QuoteFilter.sml";
val _ = use "../tools/Holmake/HM_SimpleBuffer.sig";
val _ = use "../tools/Holmake/HM_SimpleBuffer.sml";
val _ = use "../tools/Holmake/HOLFS_dtype.sml";
val _ = use "../tools/Holmake/HFS_NameMunge.sig";
val _ = use "../tools/Holmake/poly/HFS_NameMunge.sml";
val _ = use "../tools/Holmake/HOLFS_dtype.sml";
val _ = use "../tools/Holmake/HOLFileSys.sig";
val _ = use "../tools/Holmake/HOLFileSys.sml";
val _ = use "../tools/Holmake/QFRead.sig";
val _ = use "../tools/Holmake/QFRead.sml";
val _ = use "poly/quse.sig";
val _ = use "poly/quse.sml";

local

  fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
               TextIO.flushOut TextIO.stdErr;
               raise Fail s)

  fun warn s = (TextIO.output(TextIO.stdErr, "WARNING: " ^ s ^ "\n");
                TextIO.flushOut TextIO.stdErr)

  val meta_debug = ref false

  fun MDBG s = if !meta_debug then
                 TextIO.print("META_DEBUG: " ^ s() ^ "\n")
               else ()

  infix ++
  fun p1 ++ p2 = OS.Path.concat (p1, p2)
  open Systeml

structure HFS = HOLFileSys

val loadpathdb =
    ref (Binarymap.mkDict String.compare : (string,string) Binarymap.dict)

fun quse s = let
  val _ = if HFS.access (s, [HFS.A_READ]) then ()
          else die ("Use: non-existent file "^s)
  val _ = MDBG (fn _ => "Call quse " ^ s)
  val full = OS.Path.mkCanonical
               (OS.Path.mkAbsolute{path = s, relativeTo = HFS.getDir()})
in
  QUse.use s ;
  loadpathdb := Binarymap.insert(!loadpathdb,OS.Path.file full,OS.Path.dir full)
end handle OS.Path.Path => die ("Path exception in quse "^s)
             | e => (TextIO.output(TextIO.stdErr,
                                   "error in quse " ^ s ^ " : " ^
                                   General.exnMessage e ^ "\n");
                     TextIO.flushOut TextIO.stdErr;
                     PolyML.Exception.reraise e)

fun myuse f =
  let val op ++ = OS.Path.concat
      val file = OS.Path.file f
      val pd = !PolyML.Compiler.printDepth
  in
    PolyML.print_depth 0;
    (quse f handle e => (PolyML.print_depth pd; PolyML.Exception.reraise e));
    PolyML.print_depth pd
  end handle OS.Path.Path => die ("Path exception in myuse "^f)

val loadPath : string list ref = ref [OS.Path.concat(HOLDIR, "sigobj")];

val loadedMods = ref (Binaryset.empty String.compare);
val _ =
    loadedMods := Binaryset.addList (!loadedMods,
              ["Real", "Int", "List", "Binaryset", "Binarymap", "Listsort",
               "Array", "Array2", "Vector"])

fun findUo modPath [] = NONE
  | findUo modPath (search::rest) =
      let val path =
         OS.Path.mkAbsolute
           {path = modPath,
            relativeTo = OS.Path.mkAbsolute
                           {path=search, relativeTo = HFS.getDir ()}};
      in
        if HFS.access (path, []) then
          SOME path
        else
          findUo modPath rest
      end;

val _ = holpathdb.extend_db {vname = "HOLDIR", path = Systeml.HOLDIR}

fun loadUo ps uo =
  let
    val i = HFS.openIn uo
    val files =
      String.tokens (fn c => c = #"\n") (HFS.inputAll i)
    val _ = HFS.closeIn i
    fun str f = ">" ^ f ^ "< -- " ^ String.concatWith " -- " ps
    fun loadOne f =
      (case OS.Path.ext f of
         SOME "sml" => myuse (holpathdb.subst_pathvars f)
       | SOME "sig" => myuse (holpathdb.subst_pathvars f)
       | _ => load (uo::ps) f)
      handle
        OS.Path.InvalidArc => die ("Invalid arc exception in loading "^str f)
      | OS.Path.Path => die ("Path exception in loading "^str f)
      | OS.SysErr(msg,_) => die ("System error '"^msg^"' in loading "^str f)
  in
    List.app loadOne files
  end
and load ps modPath =
  let
    val _ = MDBG (fn _ => "Call load " ^ modPath)
    val modPath = holpathdb.subst_pathvars modPath
    val modName = OS.Path.file modPath
    fun l ext =
      case findUo (modPath ^ ext) ("."::(!loadPath)) of
          NONE => die ("Cannot find file " ^ modPath ^ ext)
        | SOME uo => loadUo ps uo
  in
    if Binaryset.member (!loadedMods, modName) then
      ()
    else
      (loadedMods := Binaryset.add (!loadedMods, modName);
       (l ".ui"; l ".uo")
       handle e =>
              (loadedMods := Binaryset.delete (!loadedMods, modName);
               PolyML.Exception.reraise e))
  end handle e => (TextIO.output(TextIO.stdErr,
                                 "error in load " ^ modPath ^ " : " ^
                                 General.exnMessage e ^ "\n");
                   TextIO.flushOut TextIO.stdErr;
                   PolyML.Exception.reraise e)
in

  structure Meta = struct
    val meta_debug = meta_debug
    val load = load []
    val loadPath = loadPath;
    fun loaded () = Binaryset.listItems (!loadedMods);
    fun fakeload s =
        loadedMods := Binaryset.add(!loadedMods,s)
    fun findMod modname = findUo (modname ^ ".uo") ("." :: !loadPath)
    fun fileDirMap () = !loadpathdb
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
structure FileSys = HOLFileSys;

exception Interrupt = SML90.Interrupt;
exception Io = IO.Io;
exception SysErr = OS.SysErr;
