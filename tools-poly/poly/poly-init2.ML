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

val _ = use "poly/PP.sig";
val _ = use "poly/PP.sml";

local

  val redirected_files =
    ["Portable.sig", "Portable.sml", "mlibPortable.sml", "mlibOmegaint.sml",
     "OmegaMLShadow.sml"];

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

fun quse s =
  if has_dq s then
    let
      val filename = OS.FileSys.tmpName()
    in
      (if OS.Process.isSuccess (unquote_to s filename) then
         (PolyML.use filename; OS.FileSys.remove filename)
       else (TextIO.output(TextIO.stdOut,
                           ("Failed to translate file: "^s^"\n"));
             raise Fail "use"))
        handle e => (try_remove filename; raise e)
    end
  else PolyML.use s;

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


structure PolyGeneral = General;
structure PolyArray = Array;
structure PolySubstring = Substring;
structure PolyWord8Vector = Word8Vector;
structure PolyVector = Vector;
structure PolyWord8 = Word8;
structure PolyOS = OS;
structure PolyTextIO = TextIO;
structure PolyTimer = Timer;
(* awfulness to make the environment look like Moscow ML's *)

(* In Poly/ML "before" is 'a * 'b -> 'a and General.before is 'a * unit -> 'a.
   The Basis library says both should be 'a * unit -> 'a, but in Moscow ML,
   before is 'a * 'b -> 'a too.  Ick. *)
structure General = struct
  open PolyGeneral;
  type ppstream = PP.ppstream;
end;
type ppstream = General.ppstream;
structure Array = struct
  open PolyArray;
  fun extract (a, i, jopt) =
    ArraySlice.vector(ArraySlice.slice(a,i,jopt));
  fun copyVec {di,dst,len,src,si} =
    let val v = VectorSlice.vector(VectorSlice.slice(src,si,len));
    in
      PolyArray.copyVec {di = di, dst = dst, src = v}
    end;
  fun foldli a b (c, 0, NONE) = PolyArray.foldli a b c
    | foldli a b (c, d, e) = Vector.foldli a b (extract (c, d, e));
end;

structure Vector = struct
  open PolyVector;
  fun mapi a (c, 0, NONE) = PolyVector.mapi a c
    | mapi a (c, d, e) = VectorSlice.mapi a (VectorSlice.slice (c, d, e));
  fun foldri a b (c, 0, NONE) = PolyVector.foldri a b c
    | foldri a b (c, d, e) = VectorSlice.foldri a b (VectorSlice.slice (c, d, e));
  fun foldli a b (c, 0, NONE) = PolyVector.foldli a b c
    | foldli a b (c, d, e) = VectorSlice.foldli a b (VectorSlice.slice (c, d, e));
  fun appi a (c, 0, NONE) = PolyVector.appi a c
    | appi a (c, d, e) = VectorSlice.appi a (VectorSlice.slice (c, d, e));
  fun extract (c, d, e) =
    VectorSlice.vector (VectorSlice.slice (c, d, e))
end;

structure Word8Vector = struct
  open PolyWord8Vector;
  local
    open Word8VectorSlice;
  in
    fun mapi f (v,i,jopt) = PolyWord8Vector.mapi f (vector(slice(v,i,jopt)));
    fun foldri f b (v,i,jopt) =
      PolyWord8Vector.foldri f b (vector(slice(v,i,jopt)));
  end;
end;

structure Word8 = struct
  open PolyWord8;
  fun toLargeWord w =
    Word.fromLargeWord (PolyWord8.toLargeWord w);
end;

structure OS = struct
  open PolyOS;
  structure Path = struct
    open PolyOS.Path;
    fun mkAbsolute (a,b) = PolyOS.Path.mkAbsolute {path=a, relativeTo=b};
  end;
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
