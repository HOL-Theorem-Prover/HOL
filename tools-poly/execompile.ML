structure BuildHeap_EXE_Compile :
sig
  val exe_compile : {fnname: string, output_exe: string, keep_temp_files: bool}
                      ->
                    'a
end =
struct

fun quietremove f = OS.FileSys.remove f handle SysErr _ => ()

fun withtemp_file {stem, extension, keep_file} (k : string -> 'a) : 'a =
  let
    fun gen i =
      let
        val stem = stem ^ Int.toString i
        val fname = OS.Path.joinBaseExt{base = stem, ext = SOME extension}
      in
        if OS.FileSys.access(fname, [OS.FileSys.A_READ]) then gen (i + 1)
        else
          k fname
            before (if keep_file then () else quietremove fname)
      end
  in
    gen 0
  end

fun compile {functionname, objfilename, execname} =
  let
    val old_print_depth = !PolyML.Compiler.printDepth
    val codestream = TextIO.openString ("val () = " ^ functionname ^ " ()")
    val () = PolyML.print_depth ~1;
    val function = PolyML.compiler (fn () => TextIO.input1 codestream, [])
  in
    PolyML.shareCommonData PolyML.rootFunction;
    PolyML.export (objfilename, function);
    Systeml.systeml (["cc", "-o", execname, objfilename] @ Systeml.POLY_LDFLAGS)
      before PolyML.print_depth old_print_depth
  end

fun exe_compile {fnname: string, output_exe: string, keep_temp_files: bool} =
  let
    val output_stem = OS.Path.file output_exe
    fun withobj obj =
      compile {functionname = fnname, objfilename = obj, execname = output_exe}

    val res = withtemp_file {stem = output_stem, extension = "o",
                             keep_file = keep_temp_files}
                            withobj
  in
    OS.Process.exit res
  end

end (* struct *)
