structure BuildHeap_EXE_Compile =
struct

fun withtemp_file {stem: string, extension: string} (k : string -> unit) =
  let
    fun gen i =
      let
        val stem = stem ^ Int.toString i
        val fname = OS.Path.joinBaseExt{base = stem, ext = SOME extension}
      in
        if OS.FileSys.access(fname, [OS.FileSys.A_READ]) then gen (i + 1)
        else (k fname; OS.FileSys.remove fname)
      end
  in
    gen 0
  end


fun gen_ml_compile_file {functionname, mlfilename, objfilename, execname} k =
  let
    val out = TextIO.openOut mlfilename
    fun p s = TextIO.output(out, s ^ "\n")
  in
    p ("PolyML.print_depth ~1;");
    p ("PolyML.shareCommonData PolyML.rootFunction;");
    p ("PolyML.export(\"" ^ String.toString objfilename ^ "\", " ^
       functionname ^");");
    p ("val _ = BuildHeap_EXE_Compile.res := "^
       "Systeml.systeml ([\"cc\", \"-o\", \"" ^ execname ^ "\", \"" ^
       String.toString objfilename ^ "\"] @ Systeml.POLY_LDFLAGS);");
    TextIO.closeOut out;
    k ()
  end

val res = ref OS.Process.success

fun exe_compile {fnname: string, output_exe: string} =
  let
    val output_stem = OS.Path.file output_exe
    fun withobj_and_ml obj ml =
      gen_ml_compile_file {functionname = fnname,
                           mlfilename = ml,
                           objfilename = obj,
                           execname = output_exe}
                          (fn () => PolyML.use ml)
    fun withobj obj =
      withtemp_file {stem = "poly-mk" ^ output_stem, extension = "ML"}
                    (withobj_and_ml obj)
  in
    withtemp_file {stem = output_stem, extension = "o"} withobj ;
    OS.Process.exit (!res)
  end

end (* struct *)
