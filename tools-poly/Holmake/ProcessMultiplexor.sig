signature ProcessMultiplexor =
sig

  type 'a job = {tag : string,
                 command : string * string list,
                 update : 'a * bool -> 'a}
  type jobkey = Posix.ProcEnv.pid * string
  type exit_status = Posix.Process.exit_status
  type 'a workprovider = { initial : 'a, genjob : 'a -> ('a job * 'a) option }
  type 'a worklist

  datatype strmtype = OUT | ERR
  datatype monitor_message =
           Output of jobkey * Time.time * strmtype * string
         | NothingSeen of jobkey * {delay: Time.time, total_elapsed : Time.time}
         | Terminated of jobkey * exit_status * Time.time
         | EOF of jobkey * strmtype * Time.time
         | StartJob of jobkey
  datatype client_cmd = Kill of jobkey | KillAll
  type monitor = monitor_message -> client_cmd option
  val text_monitor : monitor

  val new_worklist : {worklimit : int, provider : 'a workprovider} ->
                     'a worklist

  val do_work : ('a worklist * monitor) -> 'a
  val shell_commands : monitor -> string list * int ->
                       (string * bool) list

end
