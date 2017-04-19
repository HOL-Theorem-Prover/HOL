structure ProcessMultiplexor : ProcessMultiplexor =
struct

  infix |>
  fun x |> f = f x
  fun K x y = x

  fun assoc1 k [] = NONE
    | assoc1 k ((p as (k',v))::rest) = if k = k' then SOME p else assoc1 k rest

  type pid = Posix.ProcEnv.pid
  val pidToWord  = Posix.Process.pidToWord
  type exit_status = Posix.Process.exit_status

  type command = {executable: string, nm_args : string list, env : string list}
  type 'a job = {tag : string, command : command, update : 'a * bool -> 'a}
  datatype 'a genjob_result =
           NoMoreJobs of 'a | NewJob of ('a job * 'a) | GiveUpAndDie of 'a
  type 'a workprovider = { initial : 'a, genjob : 'a -> 'a genjob_result }

  type 'a working_job = {
    tag : string,
    command : command,
    update : 'a * bool -> 'a,
    starttime : Time.time,
    lastevent : Time.time,
    out : TextIO.instream,
    err : TextIO.instream,
    outeof : bool,
    erreof : bool,
    pid : pid
  }
  type jobkey = pid * string
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

  local
    open FunctionalRecordUpdate
    fun makeUpdateWJ z = makeUpdate10 z (* 10 fields *)
    fun makeUpdateWL z = makeUpdate4 z (* 4 fields *)
  in
    fun updateWJ z = let
      fun from tag command update starttime lastevent out err
               outeof erreof pid =
          {tag = tag, command = command, update = update, starttime = starttime,
           lastevent = lastevent, out = out, err = err, outeof = outeof,
           erreof = erreof, pid = pid}
      fun from' pid erreof outeof err out lastevent starttime update command
                tag =
          {tag = tag, command = command, update = update, starttime = starttime,
           lastevent = lastevent, out = out, err = err, outeof = outeof,
           erreof = erreof, pid = pid}
      fun to f {tag, command, update, starttime, lastevent, out,
                err, outeof, erreof, pid} =
        f  tag command update starttime lastevent out err
           outeof erreof pid
    in
      makeUpdateWJ (from, from', to)
    end z
    fun updateWL z = let
      fun from current_jobs current_state worklimit genjob =
        {current_state = current_state, current_jobs = current_jobs,
         worklimit = worklimit, genjob = genjob}
      fun from' genjob worklimit current_state current_jobs =
        {current_state = current_state, current_jobs = current_jobs,
         worklimit = worklimit, genjob = genjob}
      fun to f {current_state, current_jobs, worklimit, genjob} =
        f current_jobs current_state worklimit genjob
    in
      makeUpdateWL (from, from', to)
    end z

    val U = U
    val $$ = $$
  end

  fun touch (wj : 'a working_job) : 'a working_job =
    updateWJ wj (U #lastevent (Time.now())) $$

  fun mkTIO_instream fd =
  let
    open Posix.IO
    val (flags,_) = getfl fd
    val rdr = mkTextReader { fd = fd, name = "", initBlkMode = true }
  in
    TextIO.mkInstream (TextIO.StreamIO.mkInstream (rdr, ""))
  end

  fun jobkey_compare((p1,s1), (p2,s2)) =
    case SysWord.compare(pidToWord p1, pidToWord p2) of
        EQUAL => String.compare(s1,s2)
      | x => x
  fun wjkey ({tag,pid,...} : 'a working_job) = (pid,tag)
  fun wjk_member x [] = false
    | wjk_member x (h::t) = jobkey_compare(x,h) = EQUAL orelse wjk_member x t

  type 'a worklist = {
    current_jobs : (jobkey, 'a working_job) Binarymap.dict,
    current_state : 'a,
    worklimit : int,
    genjob : 'a -> 'a genjob_result
  }

  fun inStreamInPoll (strm : TextIO.instream) =
    let
      val (rd as TextPrimIO.RD{ioDesc,...}, buf) =
          TextIO.StreamIO.getReader(TextIO.getInstream strm)
      val _ =
          TextIO.setInstream (strm, TextIO.StreamIO.mkInstream(rd,buf))
    in
      case ioDesc of
          NONE => raise Fail "Can't poll instream"
        | SOME d => OS.IO.pollIn (valOf (OS.IO.pollDesc d))
                    handle Option => raise Fail "Can't poll instream"
    end

  fun workjob_polls (wj : 'a working_job) =
    [(inStreamInPoll (#out wj), (OUT, wj)),
     (inStreamInPoll (#err wj), (ERR, wj))]

  fun worklist_polls (wl : 'a worklist) =
    Binarymap.foldl (fn (_, wj, acc) => workjob_polls wj @ acc) []
                    (#current_jobs wl)

  fun new_worklist {worklimit : int,provider : 'a workprovider} : 'a worklist =
    {current_jobs = Binarymap.mkDict jobkey_compare,
     genjob = #genjob provider,
     current_state = #initial provider,
     worklimit = worklimit}

  fun fupdjob k f (wl : 'a worklist) : 'a worklist =
    let
      val cj = #current_jobs wl
      val cj' = Binarymap.insert(cj, k, f (Binarymap.peek(cj, k)))
    in
      updateWL wl (U #current_jobs cj') $$
    end
  fun cjs_addjob (wj : 'a working_job) d = Binarymap.insert(d, wjkey wj, wj)
  fun addjob (wj:'a working_job) = fupdjob (wjkey wj) (fn _ => wj)

  fun updstate s (wl : 'a worklist) : 'a worklist =
    updateWL wl (U #current_state s) $$

  fun start_job (j : 'a job) : 'a working_job =
    let
      open Posix.Process Posix.IO
      val {tag, command, update} = j
      val {executable,env,nm_args} = command
      val {infd=outinfd, outfd = outoutfd} = pipe()
      val {infd=errinfd, outfd = erroutfd} = pipe()
      val {infd=ininfd,  outfd = inoutfd} = pipe()
    in
      case fork() of
          NONE =>
          let
            val () = dup2 {old = outoutfd, new = Posix.FileSys.stdout}
            val () = dup2 {old = erroutfd, new = Posix.FileSys.stderr}
            val () = dup2 {old = ininfd, new = Posix.FileSys.stdin}
            val () =
                List.app close [errinfd, erroutfd, outinfd, outoutfd,
                                ininfd, inoutfd]
          in
            exece(executable,nm_args,env)
          end
        | SOME pid =>
          let
            val out = mkTIO_instream outinfd
            val err = mkTIO_instream errinfd
            val () = List.app close [outoutfd, erroutfd, ininfd, inoutfd]
          in
            {
              tag = tag,
              command = command,
              update = update,
              out = out, outeof = false,
              err = err, erreof = false,
              pid = pid,
              starttime = Time.now(),
              lastevent = Time.now()
            }
          end
    end

  fun mk_shell_command {cline,extra_env} : command =
    {executable = "/bin/sh", nm_args = ["/bin/sh", "-c", cline],
     env = extra_env @ Posix.ProcEnv.environ()}
  fun simple_shell s = mk_shell_command {cline = s, extra_env = []}
  fun shellcommand s =
    let
      open Posix.Process
      val j :int job = {tag = s, command = simple_shell s, update = K 0}
      val wj = start_job j
      fun read pfx acc strm k =
        case TextIO.inputLine strm of
            NONE => k acc
          | SOME s => read pfx ((pfx^s)::acc) strm k
    in
      read "" [] (#out wj) (fn a => read "ERR: " a (#err wj) List.rev) before
      ignore (waitpid (W_CHILD (#pid wj), []))
    end

  fun markeof0 chan (wj : 'a working_job) : 'a working_job =
    case chan of
        OUT => updateWJ wj (U #outeof true) $$
      | ERR => updateWJ wj (U #erreof true) $$

  fun markeof chan wj = wj |> markeof0 chan |> touch

  fun chan_name OUT = "OUT"
    | chan_name ERR = "ERR"

  fun fill_workq monitorfn (acc as (cmds, wl : 'a worklist)) =
    let
      val {current_jobs,current_state,genjob,...} = wl
    in
      if Binarymap.numItems(#current_jobs wl) >= #worklimit wl then acc
      else
        case genjob current_state of
            NoMoreJobs s' => (cmds, updstate s' wl)
          | NewJob (job, state') =>
            let
              val wj = start_job job
              val cmds' = case monitorfn (StartJob (wjkey wj)) of
                              NONE => cmds
                            | SOME c => c::cmds
            in
              fill_workq monitorfn
                         (cmds', wl |> addjob wj |> updstate state')
            end
          | GiveUpAndDie s' => (KillAll :: cmds, updstate s' wl)
    end

  fun text_monitor m =
    let
      open Posix.Process
      fun p0 tag t msg killp =
        (print (tag ^ "(" ^ Time.toString t ^ ")  " ^ msg ^ "\n");
         killp)
      fun p tag t msg = p0 tag t msg NONE
    in
      case m of
          Output((pid,tag), t, chan, s) =>
            p tag t ("["^chan_name chan^"]: " ^ s)
        | NothingSeen ((pid,tag), {delay,total_elapsed}) =>
            p tag total_elapsed ("delayed " ^ Time.toString delay)
        | Terminated((pid,tag), st, t) =>
          p0 tag t ("exited " ^ (if st = W_EXITED then "OK" else "FAILED"))
             (if st = W_EXITED then NONE else SOME KillAll)
        | MonitorKilled((pid,tag), t) => p tag t "monitor-killed"
        | EOF ((pid,tag), chan, t) =>
            p tag t ("EOF on " ^ chan_name chan)
        | StartJob (pid,tag) => p tag (Time.fromSeconds 0) "beginning"
    end

  fun wjstrm ERR (wj:'a working_job) = #err wj
    | wjstrm OUT wj = #out wj

  fun killjob mfn (jk:jobkey) wl =
    let
      open Posix.Process
      val cjs = #current_jobs wl
      val job = Binarymap.find (cjs, jk)
      val pid = #pid job
      val state = #update job (#current_state wl, false)
    in
      kill (K_PROC pid, Posix.Signal.kill);
      waitpid(W_CHILD pid, []);
      ignore (mfn (MonitorKilled(jk,Time.-(Time.now(),#starttime job))));
      updateWL wl
               (U #current_state state)
               (U #current_jobs (#1 (Binarymap.remove(cjs, jk)))) $$
    end

  fun killall mfn (wl : 'a worklist) =
    Binarymap.foldl (fn (k,_,acc) => killjob mfn k acc)
                    wl
                    (#current_jobs wl)

  fun execute_cmds mfn cmds wl =
    case cmds of
        [] => wl
      | KillAll :: rest =>
          wl |> killall mfn
             |> (fn wl => updateWL wl (U #genjob NoMoreJobs) $$)
             |> execute_cmds mfn rest
      | Kill jk :: rest =>
          wl |> killjob mfn jk |> execute_cmds mfn rest

  fun elapsed wj = Time.-(Time.now(), #starttime wj)

  fun do_work (wl0 : 'a worklist, monitorfn) =
    let
      open Posix.Process
      val (cmds, wl1) = fill_workq monitorfn ([], wl0)
      fun monitor msg (acc as (cmds, wl)) =
        case monitorfn msg of
            NONE => acc
          | SOME c => (c::cmds, wl)
      fun nothing wj (cmds, wl) =
        let
          val msg =
              NothingSeen (wjkey wj, {delay = Time.-(Time.now(), #lastevent wj),
                                      total_elapsed = elapsed wj})
        in
          monitor msg (cmds, addjob wj wl)
        end
      fun exitstatus wj status (cs, wl) =
        let
          val msg = Terminated (wjkey wj, status, elapsed wj)
          val newstate = #update wj (#current_state wl, status = W_EXITED)
        in
          monitor msg (cs, updateWL wl (U #current_state newstate) $$)
        end
      fun eof wj chan (cmds, wl) =
        monitor (EOF (wjkey wj, chan, elapsed wj))
                (cmds, addjob (markeof chan wj) wl)
      fun is_neweof wj chan =
        case chan of
            ERR => not (#erreof wj)
          | OUT => not (#outeof wj)
      fun dowait didio (k (* key *), wj, acc as (cmds,wl)) =
        if wjk_member k didio then (cmds, addjob wj wl)
        else
          case waitpid_nh(W_CHILD (#pid wj), []) of
              NONE => nothing wj acc
            | SOME (_, status) => exitstatus wj status acc

      fun workloop didio (cmds, wl) =
        let
          val empty_jobs = Binarymap.mkDict jobkey_compare
        in
          Binarymap.foldl (dowait didio)
                          (cmds, updateWL wl (U #current_jobs empty_jobs) $$)
                          (#current_jobs wl)
        end

      fun loop (cmds, wl : 'a worklist) : 'a =
        if Binarymap.numItems (#current_jobs wl) = 0 then #current_state wl
        else
          let
            val polls = worklist_polls wl
            val active =
                OS.IO.poll(map #1 polls, SOME (Time.fromMilliseconds 100))
            fun foldthis (pi, (acc as (cmds, wl),didio)) =
              let
                val pd = OS.IO.infoToPollDesc pi
              in
                case assoc1 pd polls of
                    NONE => raise Fail "Couldn't find poll-data in assoc1"
                  | SOME (_, (chan, wj)) =>
                    let
                      val s = TextIO.input (wjstrm chan wj)
                      val didio' = wjkey wj :: didio
                    in
                      if size s = 0 then
                        if is_neweof wj chan then (eof wj chan acc, didio')
                        else (acc,didio)
                      else
                        let
                          val msg = Output(wjkey wj, elapsed wj, chan, s)
                        in
                          (monitor msg (cmds, addjob (touch wj) wl), didio')
                        end
                    end
              end
            val ((cmds, wl), didio) =
                List.foldl foldthis ((cmds,wl), []) active
            val (cmds, wl) = workloop didio (cmds, wl)
            val wl = execute_cmds monitorfn cmds wl
          in
            loop (fill_workq monitorfn ([], wl))
          end
    in
      loop (cmds, wl1)
    end

  fun fupdAlist k f [] = raise Fail "updAlist: No element with given key"
    | fupdAlist k f ((k',v') :: rest) =
      if k=k' then (k,f v') :: rest
      else (k',v') :: fupdAlist k f rest
  fun findUpd P f k [] = k (NONE, [])
    | findUpd P f k (x::xs) =
      if P x then k (SOME (f x), f x :: xs)
      else findUpd P f (fn (res, l) => k (res, x::l)) xs


  fun shell_commands m (cmds0, n) =
    let
      datatype stat = Waiting | Running | Done of bool
      val (cmds00, _) =
          List.foldl
            (fn (c, (cs, n)) => ((str (chr n), (c, Waiting))::cs, n + 1))
            ([], 65)
            cmds0
      val cmds = List.rev cmds00
      fun genjob clist =
        let
          val (cdata, l) = findUpd (fn (_, (_, s)) => s = Waiting)
                                   (fn (k, (c, _)) => (k, (c, Running)))
                                   (fn x => x)
                                   clist
        in
          case cdata of
              NONE => NoMoreJobs clist
            | SOME (t, (c, _)) =>
              let
                fun upd(clist, b) = fupdAlist t (fn (c,_) => (c,Done b)) clist
              in
                NewJob ({tag = t, command = simple_shell c, update = upd}, l)
              end
        end
      val wl =
          new_worklist {
            provider = {initial = cmds, genjob = genjob},
            worklimit = n
          }
      val cs = do_work(wl,m)
    in
      List.mapPartial (fn (k,(c,st)) =>
                          case st of
                              Done b => SOME (c,b)
                            | _ => NONE)
                      cs
    end


end
