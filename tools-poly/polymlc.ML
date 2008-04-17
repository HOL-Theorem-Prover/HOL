use "Holmake/Systeml.sig";
use "Holmake/Systeml.sml";

fun normPath s = OS.Path.toString(OS.Path.fromString s)
fun itstrings f [] = raise Fail "itstrings: empty list"
  | itstrings f [x] = x
  | itstrings f (h::t) = f h (itstrings f t);
fun fullPath slist = normPath
   (itstrings (fn chunk => fn path => OS.Path.concat (chunk,path)) slist);

fun fixPath findOverlay p =
  if findOverlay andalso OS.Path.base (OS.Path.file p) = "Overlay" then
    fullPath [Systeml.HOLDIR, "sigobj", "Overlay.uo"]
  else
    OS.Path.mkAbsolute {path=p, relativeTo=OS.FileSys.getDir ()}

(*
fun getDeps file =
  let val depsin = TextIO.openIn (fullPath [OS.Path.dir file, ".HOLMK", 
                                            OS.Path.file file ^ ".d"])
      val deps = 
        List.map (fixPath false)
                 (List.tl (String.tokens (fn c => 
                                            List.exists (fn c' => c = c') 
                                                        (String.explode " \n")) 
                                         (TextIO.inputAll depsin)))
      val _ = TextIO.closeIn depsin
  in
    deps
  end
  handle _ => []
*)

fun compile file deps q includes =
raise (Fail "Shouldn't be here")
(*
  let (*val _ = print ("compiling: " ^ file)*)
      val deps = getDeps file @ (List.map (fixPath true) deps)
      val suff = case OS.Path.ext file of
                   SOME "sig" => ".ui"
                 | SOME "sml" => ".uo"
      val sigfile = OS.Path.base file ^ ".sig"
      val uifile = OS.Path.base file ^ ".ui"
      val out = TextIO.openOut (OS.Path.base file ^ suff)
  in
    List.app (fn f => TextIO.output (out, f ^ "\n")) deps;
    TextIO.output (out, fixPath false file ^ "\n");
    TextIO.closeOut out;
    if OS.FileSys.access (sigfile, []) then
      ()
    else
      TextIO.closeOut (TextIO.openOut uifile)
  end
*)

fun link result files includes =
  let val out = TextIO.openOut result
  in
    TextIO.output (out, "local\n");
    TextIO.output (out, "val pd = PolyML.get_print_depth();\n");
    TextIO.output (out, "val _ = PolyML.print_depth 0;\n");
    TextIO.output (out, "val dir = OS.FileSys.getDir();\n");
    TextIO.output (out, "val _ = OS.FileSys.chDir \"" ^
                        String.toString Systeml.HOLDIR ^ 
                        "/tools-poly/\";\n");
    TextIO.output (out, "in\n");
    TextIO.output (out, "val _ = use \"poly/poly-init2.ML\";\n");
    TextIO.output (out, "val _ = OS.FileSys.chDir dir;\n");
    TextIO.output (out, "val _ = PolyML.print_depth pd;\n");
    TextIO.output (out, "end;\n");
    TextIO.output (out, "val _ = List.map load [" ^ 
                        String.concatWith "," 
                                          (List.map (fn f => "\"" ^ OS.Path.base (fixPath false f) ^ "\"")
                                                    files) ^
                        "];\n");
    TextIO.closeOut out 
  end

fun polymlc arglist =
  let val c = ref false
      val q = ref false
      val toplevel = ref false
      val obj = ref NONE
      val I = ref []
      val files = ref []
      fun process_args [] = ()
        | process_args ("-c"::rest) =
            (c := true;
             process_args rest)
        | process_args ("-q"::rest) =
            (q := true;
             process_args rest)
        | process_args ("-toplevel"::rest) =
            (toplevel := true;
             process_args rest)
        | process_args ("-o"::arg::rest) =
            (obj := SOME arg;
             process_args rest)
        | process_args ("-I"::arg::rest) =
            (I := arg::(!I);
             process_args rest)
        | process_args (file::rest) =
            (files := file::(!files);
             process_args rest)
  in
    process_args arglist;
    if !c then
      compile (List.hd (!files)) (List.rev (List.tl (!files))) (!q)
              (List.rev (!I))
    else if Option.isSome (!obj) then
      link (Option.valOf (!obj)) (List.rev (!files)) (List.rev (!I))
    else
      ()
  end

fun main () = 
  ((*print (String.concatWith " " (CommandLine.arguments()));
   print "\n";*)
   polymlc (CommandLine.arguments ()));
   

PolyML.export("polymlc", main);
