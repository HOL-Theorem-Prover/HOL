signature ProcessMultiplexor =
sig

  type command = {executable: string, nm_args : string list, env : string list}
  type 'a job = {tag : string, command : command,
                 update : 'a * bool * Time.time -> 'a * string option,
                 try_cache : unit -> bool,
                 dir : string,
                 ignore_error : bool}
    (* update returns the new shared state plus an optional marker
       that ProcessMultiplexor forwards to the monitor as part of
       the Terminated message, so the monitor can include it in
       the per-completion display. *)
  type jobkey = Posix.ProcEnv.pid * {tag : string, dir : string}
  val jobkey_compare : jobkey * jobkey -> order
  val jobkey_toString : jobkey -> string

  type exit_status = Posix.Process.exit_status
  datatype 'a genjob_result =
           NoMoreJobs of 'a | NewJob of ('a job * 'a) | GiveUpAndDie of 'a
  (* Live scheduler view handed to `genjob' on each fill cycle.
     A record so future fields can be added without churning
     callers. *)
  type sched_ctxt = { jobs_running : int }
  type 'a workprovider =
       { initial : 'a, genjob : sched_ctxt -> 'a -> 'a genjob_result }
  type 'a worklist

  datatype strmtype = OUT | ERR
  datatype monitor_message =
           Output of jobkey * Time.time * strmtype * string
         | NothingSeen of jobkey * {delay: Time.time, total_elapsed : Time.time}
         | Terminated of jobkey * exit_status * Time.time * string option
         | MonitorKilled of jobkey * Time.time
         | EOF of jobkey * strmtype * Time.time
         | StartJob of jobkey * {dir:string, ignore_error:bool}
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
