signature ProcessMultiplexor =
sig

  type command = {executable: string, nm_args : string list, env : string list}
  type 'a job = {tag : string, command : command, update : 'a * bool -> 'a}
  type jobkey = Posix.ProcEnv.pid * string
  type exit_status = Posix.Process.exit_status
  datatype 'a genjob_result =
           NoMoreJobs of 'a | NewJob of ('a job * 'a) | GiveUpAndDie of 'a
  type 'a workprovider = { initial : 'a, genjob : 'a -> 'a genjob_result }
  type 'a worklist

  datatype strmtype = OUT | ERR
  datatype monitor_message =
           Output of jobkey * Time.time * strmtype * string
         | NothingSeen of jobkey * {delay: Time.time, total_elapsed : Time.time}
         | Terminated of jobkey * exit_status * Time.time
         | MonitorKilled of jobkey * Time.time
         | EOF of jobkey * strmtype * Time.time
         | StartJob of jobkey
  datatype client_cmd = Kill of jobkey | KillAll
  type monitor = monitor_message -> client_cmd option
  val text_monitor : monitor

  val new_worklist : {worklimit : int, provider : 'a workprovider} ->
                     'a worklist

  val do_work : ('a worklist * monitor) -> 'a
  val mk_shell_command : {cline: string, extra_env: string list} -> command
  val shell_commands : monitor -> string list * int ->
                       (string * bool) list

end
