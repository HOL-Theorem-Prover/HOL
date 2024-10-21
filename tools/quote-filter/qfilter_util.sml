structure qfilter_util :> qfilter_util =
struct

open OS.Process
fun nothing() = ()
fun open_files intp infn outfn =
    let
      open TextIO
      val is = TextIO.openIn infn
               handle OS.SysErr _ =>
                      (output(stdErr, "Error opening "^infn^"\n");
                       exit failure)
      val (os,cb) =
          let val strm = TextIO.openOut outfn
                         handle IO.Io {cause = OS.SysErr (_, eo), ...} =>
                                (case eo of
                                     SOME e => output(stdErr, OS.errorMsg e)
                                   | NONE => ();
                                 exit failure)
              fun closeboth() = (TextIO.closeIn is; TextIO.closeOut strm)
              val wrap = intp andalso String.isSuffix "Script.sml" outfn
              val cb = if wrap then (fn () => (TextIO.output(strm, " end");
                                               closeboth()))
                       else closeboth
              val base = OS.Path.file outfn
          in
            if wrap then
              TextIO.output(strm, "structure " ^
                                  String.substring(base, 0, size base - 4) ^
                                  " = struct ")
            else ();
            (strm, cb)
          end
    in
      {instrm = is, outstrm = os, interactive = intp, quotefixp = false,
       closefn = cb, infilename = infn}
    end

fun usage strm status =
    (TextIO.output(strm,
                   "Usage:\n  " ^ CommandLine.name() ^
                   " [-i] <inputfile> <outputfile> | -h | -n | --quotefix\n\n\
                   \With two files:\n\
                   \   -i : use \"interactive\" mode, and wrap *Script.sml \
                   \with structure decl\n\n\
                   \Other options occur as sole arguments:\n\
                   \   -h : show this message\n\
                   \   -n : don't use \"interactive\" mode\n\
                   \   --quotefix : filter to replace ` with Unicode quotes\n");
     exit status)

fun badusage() = usage TextIO.stdErr failure
fun processArgs (nonp, intp, qfixp) args =
    case args of
        [] => if intp then badusage()
              else if qfixp then
                {instrm = TextIO.stdIn,
                 outstrm = TextIO.stdOut,
                 interactive = false,
                 quotefixp = qfixp,
                 closefn = nothing,
                 infilename = ""}
              else
                {instrm = TextIO.stdIn,
                 outstrm = TextIO.stdOut,
                 interactive = true,
                 quotefixp = false,
                 closefn = nothing,
                 infilename = ""}
      | ["-h"] => usage TextIO.stdOut success
      | "-h" :: _ => badusage()
      | "-i" :: rest => if nonp orelse qfixp then badusage()
                        else processArgs (false, true, false) rest
      | "-n"::rest =>
           if intp orelse qfixp then badusage()
           else processArgs (true, false, false) rest
      | "--quotefix"::rest =>
           if intp orelse nonp then badusage()
           else processArgs (false, false, true) rest
      | [ifile, ofile] => if qfixp orelse nonp then badusage()
                          else open_files intp ifile ofile
      | _ => badusage()

end (* struct *)
