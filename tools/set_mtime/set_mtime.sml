fun warn (qf,df) s =
  (if qf then () else TextIO.output(TextIO.stdErr, s ^ "\n");
   if df then OS.Process.exit OS.Process.failure else ())

fun die qf s =
  (warn (qf, false) s; OS.Process.exit OS.Process.failure)

fun usage () =
  "Usage:\n  " ^ CommandLine.name() ^
  " [-dqh] file_to_change file1 .. filen\n\n\
  \    -d       Any warning causes failure\n\
  \    -h       Show this message\n\
  \    -q       Make output quiet\n\n\
  \  Must provide file_to_change and >=1 other file to take mtime from\n"

fun process_file_args (qf,df,acc) changefile args =
  case args of
      [] => (qf,df,changefile,List.rev acc)
    | a :: rest => process_file_args (qf,df,a::acc) changefile rest

fun process_args (qf0,df0) args =
  case args of
      [] => die qf0 (usage())
    | "-q" :: rest => process_args (true, df0) args
    | "-d" :: rest => process_args (qf0, true) args
    | "-h" :: _ => (TextIO.output(TextIO.stdOut, usage());
                    OS.Process.exit OS.Process.success)
    | [_] => die qf0 (usage())
    | f :: rest => process_file_args (qf0, df0, []) f rest

fun time_max (t1, t2) = if Time.<(t1,t2) then t2 else t1

fun maxtime flags (fname, t0) =
  time_max (OS.FileSys.modTime fname, t0)
  handle OS.SysErr _ =>
         (warn flags ("File "^fname^" caused excption on modTime call"); t0)

fun main() =
  let
    val (qf,df,changefile,args) =
        process_args (false,false) (CommandLine.arguments())
    val t = List.foldl (maxtime (qf,df)) Time.zeroTime args
  in
    OS.FileSys.setTime(changefile, SOME t)
      handle e => (die qf
                       ("Setting time on "^changefile^" caused exn: "^
                        General.exnMessage e))
  end
