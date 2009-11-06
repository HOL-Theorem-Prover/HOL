(* this is an -*- sml -*- file *)
val _ = use "poly/poly-init.ML";

val _ = use "Holmake/Systeml.sig";
val _ = use "Holmake/Systeml.sml";
val _ = use "Holmake/internal_functions.sig";
val _ = use "Holmake/internal_functions.sml";
val _ = use "Holmake/Holmake_types.sig";
val _ = use "Holmake/Holmake_types.sml";
val _ = use "Holmake/ReadHMF.sig";
val _ = use "Holmake/ReadHMF.sml";

local

  val redirected_files =
    ["Portable.sml", "mlibPortable.sml", "mlibOmegaint.sml"];

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
            | SOME _ => loop()
      in
        loop() before TextIO.closeIn istrm
      end handle IO.Io _ => false
  infix ++
  fun p1 ++ p2 = OS.Path.concat (p1, p2)
  open Systeml
  fun unquote_to file1 file2 =
      systeml [HOLDIR ++ "bin" ++ "unquote", file1, file2];

fun quse s = let
  val _ = if OS.FileSys.access (s, [OS.FileSys.A_READ]) then ()
          else let
              val msg = "Use: non-existent file "^s
            in
              TextIO.output(TextIO.stdErr, msg ^ "\n");
              raise Fail msg
            end
in
  if has_dq s then let
      val filename = OS.FileSys.tmpName()
    in
      (if OS.Process.isSuccess (unquote_to s filename) then
         (PolyML.use filename; OS.FileSys.remove filename)
       else (TextIO.output(TextIO.stdOut,
                           ("Failed to translate file: "^s^"\n"));
             raise Fail "use"))
      handle e => (try_remove filename; raise e)
    end
  else PolyML.use s
end

fun myuse f =
  let val op ^ = OS.Path.concat
      val file = OS.Path.file f
      val pd = !PolyML.Compiler.printDepth
  in
    PolyML.print_depth 0;
    ((if List.exists (fn f => f = file) redirected_files then
        quse (Systeml.HOLDIR ^ "tools-poly" ^ "poly" ^ "redirects" ^ file)
      else
        quse f)
     handle e => (PolyML.print_depth pd; raise e));
    PolyML.print_depth pd
  end;

val loadPath : string list ref = ref [];

val loadedMods = ref (Binaryset.empty String.compare);
val _ = loadedMods := Binaryset.addList (!loadedMods,
                                         ["Real", "Int", "List"])

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
let val i = TextIO.openIn uo;
    val files =
      String.tokens (fn c => List.exists (fn c' => c = c')
                                         (String.explode " \n"))
                    (TextIO.inputAll i);
    fun loadOne f =
      ((*print (modName ^ "\n");*)
       case OS.Path.ext f of
         SOME "sml" => myuse f
       | SOME "sig" => myuse f
       | _ => load f);
in
  List.app loadOne files
end
and load modPath =
let val modName = OS.Path.file modPath;
    fun l ext =
      case findUo (modPath ^ ext) ("."::(!loadPath)) of
        NONE => raise (Fail ("Cannot find file " ^ modPath ^ ext))
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
  end;

open Meta;

end;


structure PolyWord8 = Word8;
structure PolyTimer = Timer;
(* awfulness to make the environment look like Moscow ML's *)

(* In Poly/ML "before" is 'a * 'b -> 'a and General.before is 'a * unit -> 'a.
   The Basis library says both should be 'a * unit -> 'a, but in Moscow ML,
   before is 'a * 'b -> 'a too.  Ick. *)

structure Word8 = struct
  open PolyWord8;
  fun toLargeWord w =
    Word.fromLargeWord (PolyWord8.toLargeWord w);
end;

structure Timer = struct
  open PolyTimer;
  fun checkCPUTimer t =
     let val {usr=usr, sys=sys} = PolyTimer.checkCPUTimer t;
         val gc = PolyTimer.checkGCTime t;
     in
       {usr=usr, sys=sys, gc=gc}
     end;
end;

structure PreProcess = OS.Process;
structure Path = OS.Path;
structure Process = OS.Process;
structure FileSys = OS.FileSys;

exception Interrupt = SML90.Interrupt;
exception Io = IO.Io;
exception SysErr = OS.SysErr;

val _ = use "poly/Dynarray.sig";
val _ = use "poly/Dynarray.sml";
val _ = use "poly/MD5.sig";
val _ = use "poly/MD5.sml";
val _ = use "poly/Susp.sig";
val _ = use "poly/Susp.sml";
val _ = use "poly/Random.sig";
val _ = use "poly/Random.sml";
val _ = use "poly/Intset.sig";
val _ = use "poly/Intset.sml";
val _ = use "poly/Intmap.sig";
val _ = use "poly/Intmap.sml";
