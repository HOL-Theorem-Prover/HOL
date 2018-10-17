(*  Title:      Pure/Concurrent/future.ML
    Author:     Makarius

Value-oriented parallel execution via futures and promises.
*)

signature FUTURE =
sig
  type task = Task_Queue.task
  type group = Task_Queue.group
  val new_group: group option -> group
  val worker_task: unit -> task option
  val worker_group: unit -> group option
  val the_worker_group: unit -> group
  val worker_subgroup: unit -> group
  type 'a future
  val task_of: 'a future -> task
  val peek: 'a future -> 'a Exn.result option
  val is_finished: 'a future -> bool
  val interruptible_task: ('a -> 'b) -> 'a -> 'b
  val cancel_group: group -> unit
  val cancel: 'a future -> unit
  type params = {name: string, group: group option, deps: task list, pri: int, interrupts: bool}
  val default_params: params
  val forks: params -> (unit -> 'a) list -> 'a future list
  val fork: (unit -> 'a) -> 'a future
  val join_results: 'a future list -> 'a Exn.result list
  val join_result: 'a future -> 'a Exn.result
  val joins: 'a future list -> 'a list
  val join: 'a future -> 'a
  val forked_results: {name: string, deps: Task_Queue.task list} ->
    (unit -> 'a) list -> 'a Exn.result list
  val task_context: string -> group -> ('a -> 'b) -> 'a -> 'b
  val value_result: 'a Exn.result -> 'a future
  val value: 'a -> 'a future
  val cond_forks: params -> (unit -> 'a) list -> 'a future list
  val map: ('a -> 'b) -> 'a future -> 'b future
  val promise_name: string -> (unit -> unit) -> 'a future
  val promise: (unit -> unit) -> 'a future
  val fulfill_result: 'a future -> 'a Exn.result -> unit
  val fulfill: 'a future -> 'a -> unit
  val relevant : 'a list -> bool
  val snapshot: group list -> task list
  val shutdown: unit -> unit
end;

structure Future: FUTURE =
struct

open Portable

(** future values **)

type task = Task_Queue.task;
type group = Task_Queue.group;
val new_group = Task_Queue.new_group;


(* identifiers *)

local
  val worker_task_var = Thread_Data.var () : task Thread_Data.var;
in
  fun worker_task () = Thread_Data.get worker_task_var;
  fun setmp_worker_task task f x = Thread_Data.setmp worker_task_var (SOME task) f x;
end;

val worker_group = Option.map Task_Queue.group_of_task o worker_task;

fun the_worker_group () =
  (case worker_group () of
    SOME group => group
  | NONE => raise Fail "Missing worker thread context");

fun worker_subgroup () = new_group (worker_group ());

fun worker_joining e =
  (case worker_task () of
    NONE => e ()
  | SOME task => Task_Queue.joining task e);

fun worker_waiting deps e =
  (case worker_task () of
    NONE => e ()
  | SOME task => Task_Queue.waiting task deps e);


(* datatype future *)

type 'a result = 'a Exn.result Single_Assignment.var;

datatype 'a future =
  Value of 'a Exn.result |
  Future of
   {promised: bool,
    task: task,
    result: 'a result};

fun task_of (Value _) = Task_Queue.dummy_task
  | task_of (Future {task, ...}) = task;

fun peek (Value res) = SOME res
  | peek (Future {result, ...}) = Single_Assignment.peek result;

fun is_finished x = isSome (peek x);

(** scheduling **)

(* synchronization *)

val scheduler_event = ConditionVar.conditionVar ();
val work_available = ConditionVar.conditionVar ();
val work_finished = ConditionVar.conditionVar ();

local
  val lock = Mutex.mutex ();
in

fun SYNCHRONIZED name = Multithreading.synchronized name lock;

fun wait cond = (*requires SYNCHRONIZED*)
  Multithreading.sync_wait NONE cond lock;

fun wait_timeout timeout cond = (*requires SYNCHRONIZED*)
  Multithreading.sync_wait (SOME (Time.now () + timeout)) cond lock;

fun signal cond = (*requires SYNCHRONIZED*)
  ConditionVar.signal cond;

fun broadcast cond = (*requires SYNCHRONIZED*)
  ConditionVar.broadcast cond;

end;


(* global state *)

val queue = Unsynchronized.ref Task_Queue.empty;
val next = Unsynchronized.ref 0;
val scheduler = Unsynchronized.ref (NONE: Thread.thread option);
val canceled = Unsynchronized.ref ([]: group list);
val do_shutdown = Unsynchronized.ref false;
val max_workers = Unsynchronized.ref 0;
val max_active = Unsynchronized.ref 0;

val status_ticks = Unsynchronized.ref 0;
val last_round = Unsynchronized.ref Time.zeroTime;
val next_round = Time.fromReal 0.05;

datatype worker_state = Working | Waiting | Sleeping;
val workers = Unsynchronized.ref ([]: (Thread.thread * worker_state Unsynchronized.ref) list);

fun count_workers state = (*requires SYNCHRONIZED*)
  foldl' (fn (_, state_ref) => fn i => if ! state_ref = state then i + 1 else i)
         (! workers) 0



(* cancellation primitives *)

fun cancel_now group = (*requires SYNCHRONIZED*)
  let
    val running = Task_Queue.cancel (! queue) group;
    val _ = running |> List.app (fn thread =>
      if Standard_Thread.is_self thread then ()
      else Standard_Thread.interrupt_unsynchronized thread);
  in running end;

fun cancel_all () = (*requires SYNCHRONIZED*)
  let
    val (groups, threads) = Task_Queue.cancel_all (! queue);
    val _ = List.app Standard_Thread.interrupt_unsynchronized threads;
  in groups end;

fun cancel_later group = (*requires SYNCHRONIZED*)
 (Unsynchronized.change canceled (op_insert (curry Task_Queue.eq_group) group);
  broadcast scheduler_event);

fun interruptible_task f x =
  Thread_Attributes.with_attributes
    (if isSome (worker_task ())
     then Thread_Attributes.private_interrupts
     else Thread_Attributes.public_interrupts)
    (fn _ => f x)
  before Thread_Attributes.expose_interrupt ();


(* worker threads *)

fun worker_exec (task, jobs) =
  let
    val group = Task_Queue.group_of_task task;
    val valid = not (Task_Queue.is_canceled group);
    val ok =
      Task_Queue.running task (fn () =>
        setmp_worker_task task (fn () =>
          foldl' (fn job => fn ok => job valid andalso ok) jobs true) ());
(*    val _ =
      if ! Multithreading.trace >= 2 then
        Output.try_protocol_message (Markup.task_statistics :: Task_Queue.task_statistics task) []
      else ();
*)
    val _ = SYNCHRONIZED "finish" (fn () =>
      let
        val maximal = Unsynchronized.change_result queue (Task_Queue.finish task);
        val test = Exn.capture Thread_Attributes.expose_interrupt ();
        val _ =
          if ok andalso not (Exn.is_interrupt_exn test) then ()
          else if null (cancel_now group) then ()
          else cancel_later group;
        val _ = broadcast work_finished;
        val _ = if maximal then () else signal work_available;
      in () end);
  in () end;

fun worker_wait worker_state cond = (*requires SYNCHRONIZED*)
  (case AList.lookup Thread.equal (! workers) (Thread.self ()) of
    SOME state => Unsynchronized.setmp state worker_state wait cond
  | NONE => wait cond);

fun worker_next () = (*requires SYNCHRONIZED*)
  if length (! workers) > ! max_workers then
    (Unsynchronized.change workers (AList.delete Thread.equal (Thread.self ()));
     signal work_available;
     NONE)
  else
    let val urgent_only = count_workers Working > ! max_active in
      (case Unsynchronized.change_result queue (Task_Queue.dequeue (Thread.self ()) urgent_only) of
        NONE => (worker_wait Sleeping work_available; worker_next ())
      | some => (signal work_available; some))
    end;

fun worker_loop name =
  (case SYNCHRONIZED name (fn () => worker_next ()) of
    NONE => ()
  | SOME work => (worker_exec work; worker_loop name));

val threads_stack_limit = 0.25 (* should be user-config option *)
fun worker_start name = (*requires SYNCHRONIZED*)
  let
    val threads_stack_limit =
      Real.floor (threads_stack_limit * 1024.0 * 1024.0 * 1024.0);
    val stack_limit = if threads_stack_limit <= 0 then NONE else SOME threads_stack_limit;
    val worker =
      Standard_Thread.fork {name = "worker", stack_limit = stack_limit, interrupts = false}
        (fn () => worker_loop name);
  in Unsynchronized.change workers (cons (worker, Unsynchronized.ref Working)) end
  handle Fail msg => Multithreading.tracing 0 (fn () => "SCHEDULER: " ^ msg);


(* scheduler *)

fun scheduler_next () = (*requires SYNCHRONIZED*)
  let
    val now = Time.now ();
    val tick = ! last_round + next_round <= now;
    val _ = if tick then last_round := now else ();


    (* runtime status *)

    val _ =
      if tick then Unsynchronized.change status_ticks (fn i => i + 1) else ();
    (*
    val _ =
      if tick andalso ! status_ticks mod (if ! Multithreading.trace >= 1 then 2 else 10) = 0
      then report_status () else ();
      *)

    val _ =
      if not tick orelse List.all (Thread.isActive o #1) (! workers) then ()
      else
        let
          val (alive, dead) = List.partition (Thread.isActive o #1) (! workers);
          val _ = workers := alive;
        in
          Multithreading.tracing 0 (fn () =>
            "SCHEDULER: disposed " ^ Int.toString (length dead) ^
            " dead worker threads")
        end;


    (* worker pool adjustments *)

    val max_active0 = ! max_active;
    val max_workers0 = ! max_workers;

    val m =
      if ! do_shutdown andalso Task_Queue.all_passive (! queue) then 0
      else Multithreading.max_threads ();
    val _ = max_active := m;
    val _ = max_workers := 2 * m;

    val missing = ! max_workers - length (! workers);
    val _ =
      if missing > 0 then
        funpow missing (fn () =>
          ignore (worker_start
                    ("worker " ^ Int.toString (Unsynchronized.inc next)))) ()
      else ();

    val _ =
      if ! max_active = max_active0 andalso ! max_workers = max_workers0 then ()
      else signal work_available;


    (* canceled groups *)

    val _ =
      if null (! canceled) then ()
      else
       (Multithreading.tracing 1 (fn () =>
          Int.toString (length (! canceled)) ^ " canceled groups");
        Unsynchronized.change canceled (filter_out (null o cancel_now));
        signal work_available);


    (* delay loop *)

    val _ = Exn.release (wait_timeout next_round scheduler_event);


    (* shutdown *)

    val continue = not (! do_shutdown andalso null (! workers));
    val _ = if continue then () else ((* report_status (); *)scheduler := NONE)

    val _ = broadcast scheduler_event;
  in continue end
  handle exn =>
    if Exn.is_interrupt exn then
     (Multithreading.tracing 1 (fn () => "SCHEDULER: Interrupt");
      List.app cancel_later (cancel_all ());
      signal work_available; true)
    else Exn.reraise exn;

fun scheduler_loop () =
 (while
    Thread_Attributes.with_attributes
      (Thread_Attributes.sync_interrupts Thread_Attributes.public_interrupts)
      (fn _ => SYNCHRONIZED "scheduler" (fn () => scheduler_next ()))
  do (); last_round := Time.zeroTime);

fun scheduler_active () = (*requires SYNCHRONIZED*)
  (case ! scheduler of NONE => false | SOME thread => Thread.isActive thread);

fun scheduler_check () = (*requires SYNCHRONIZED*)
 (do_shutdown := false;
  if scheduler_active () then ()
  else
    scheduler :=
      SOME (Standard_Thread.fork {name = "scheduler", stack_limit = NONE, interrupts = false}
        scheduler_loop));



(** futures **)

(* cancel *)

fun cancel_group_unsynchronized group = (*requires SYNCHRONIZED*)
  let
    val _ = if null (cancel_now group) then () else cancel_later group;
    val _ = signal work_available;
    val _ = scheduler_check ();
  in () end;

fun cancel_group group =
  SYNCHRONIZED "cancel_group" (fn () => cancel_group_unsynchronized group);

fun cancel x = cancel_group (Task_Queue.group_of_task (task_of x));


(* results *)

fun assign_result group result res =
  let
    val _ = Single_Assignment.assign result res
      handle exn as Fail _ =>
        (case Single_Assignment.peek result of
          SOME (Exn.Exn e) => Exn.reraise (if Exn.is_interrupt e then e else exn)
        | _ => Exn.reraise exn);
    val ok =
      (case valOf (Single_Assignment.peek result) of
        Exn.Exn exn =>
          (SYNCHRONIZED "cancel" (fn () => Task_Queue.cancel_group group exn); false)
      | Exn.Res _ => true);
  in ok end;


(* future jobs *)

fun future_job group atts (e: unit -> 'a) =
  let
    val result = Single_Assignment.var "future" : 'a result;
    fun job ok =
      let
        val res =
          if ok then
            Exn.capture (fn () =>
              Thread_Attributes.with_attributes atts (fn _ => e ())) ()
          else Exn.interrupt_exn;
      in
        assign_result group result res
      end;
  in (result, job) end;


(* fork *)

type params = {name: string, group: group option, deps: task list, pri: int, interrupts: bool};
val default_params: params = {name = "", group = NONE, deps = [], pri = 0, interrupts = true};

fun forks ({name, group, deps, pri, interrupts}: params) es =
  if null es then []
  else
    let
      val grp =
        (case group of
          NONE => worker_subgroup ()
        | SOME grp => grp);
      fun enqueue e queue =
        let
          val atts =
            if interrupts
            then Thread_Attributes.private_interrupts
            else Thread_Attributes.no_interrupts;
          val (result, job) = future_job grp atts e;
          val (task, queue') = Task_Queue.enqueue name grp deps pri job queue;
          val future = Future {promised = false, task = task, result = result};
        in (future, queue') end;
    in
      SYNCHRONIZED "enqueue" (fn () =>
        let
          val (queue', futures) =
              foldl_map (fn (q,e) => swap $ enqueue e q) (! queue, es)
          val _ = queue := queue';
          val minimal = List.all (not o Task_Queue.known_task queue') deps;
          val _ = if minimal then signal work_available else ();
          val _ = scheduler_check ();
        in futures end)
    end;

fun fork e =
  (singleton o forks) {name = "fork", group = NONE, deps = [], pri = 0, interrupts = true} e;


(* join *)

fun get_result x =
  (case peek x of
    NONE => Exn.Exn (Fail "Unfinished future")
  | SOME res =>
      if Exn.is_interrupt_exn res then
        (case Task_Queue.group_status (Task_Queue.group_of_task (task_of x)) of
          [] => res
        | exns => Exn.Exn (Par_Exn.make exns))
      else res);

local

fun join_next atts deps = (*requires SYNCHRONIZED*)
  if null deps then NONE
  else
    (case Unsynchronized.change_result queue (Task_Queue.dequeue_deps (Thread.self ()) deps) of
      (NONE, []) => NONE
    | (NONE, deps') =>
       (worker_waiting deps' (fn () =>
          Thread_Attributes.with_attributes atts (fn _ =>
            Exn.release (worker_wait Waiting work_finished)));
        join_next atts deps')
    | (SOME work, deps') => SOME (work, deps'));

fun join_loop atts deps =
  (case SYNCHRONIZED "join" (fn () => join_next atts deps) of
    NONE => ()
  | SOME (work, deps') => (worker_joining (fn () => worker_exec work); join_loop atts deps'));

in

fun join_results xs =
  let
    val _ =
      if List.all is_finished xs then ()
      else if isSome (worker_task ()) then
        Thread_Attributes.with_attributes Thread_Attributes.no_interrupts
          (fn orig_atts => join_loop orig_atts (map task_of xs))
      else
        xs |> List.app
          (fn Value _ => ()
            | Future {result, ...} => ignore (Single_Assignment.await result));
  in map get_result xs end;

end;

fun join_result x = singleton join_results x;
fun joins xs = Par_Exn.release_all (join_results xs);
fun join x = Exn.release (join_result x);


(* forked results: nested parallel evaluation *)

fun forked_results {name, deps} es =
  Thread_Attributes.uninterruptible (fn restore_attributes => fn () =>
    let
      val (group, pri) =
        (case worker_task () of
          SOME task =>
            (new_group (SOME (Task_Queue.group_of_task task)), Task_Queue.pri_of_task task)
        | NONE => (new_group NONE, 0));
      val futures =
        forks {name = name, group = SOME group, deps = deps, pri = pri, interrupts = true} es;
    in
      restore_attributes join_results futures
        handle exn => (if Exn.is_interrupt exn then cancel_group group else (); Exn.reraise exn)
    end) ();


(* task context for running thread *)

fun task_context name group f x =
  Thread_Attributes.with_attributes Thread_Attributes.no_interrupts (fn orig_atts =>
    let
      val (result, job) = future_job group orig_atts (fn () => f x);
      val task =
        SYNCHRONIZED "enroll" (fn () =>
          Unsynchronized.change_result queue (Task_Queue.enroll (Thread.self ()) name group));
      val _ = worker_exec (task, [job]);
    in
      (case Single_Assignment.peek result of
        NONE => raise Fail "Missing task context result"
      | SOME res => Exn.release res)
    end);

fun enabled () =
  let
    val threads = Multithreading.max_threads ()
  in
    threads > 1 andalso
    SYNCHRONIZED "enabled" (fn () => Task_Queue.total_jobs (! queue) < threads)
  end

val relevant = (fn [] => false | [_] => false | _ => enabled ());

(* fast-path operations -- bypass task queue if possible *)

fun value_result (res: 'a Exn.result) =
  let
    val task = Task_Queue.dummy_task
    val group = Task_Queue.group_of_task task
    val result = Single_Assignment.var "value" : 'a result
    val _ = assign_result group result res
  in Future {promised = false, task = task, result = result} end;

fun value x = value_result (Exn.Res x);

fun cond_forks args es =
  if Multithreading.enabled () then forks args es
  else map (fn e => value_result (Exn.interruptible_capture e ())) es;

fun map_future f x =
  if is_finished x then value_result (Exn.interruptible_capture (f o join) x)
  else
    let
      val task = task_of x;
      val group = Task_Queue.group_of_task task;
      val (result, job) =
        future_job group Thread_Attributes.private_interrupts (fn () => f (join x));

      val extended = SYNCHRONIZED "extend" (fn () =>
        (case Task_Queue.extend task job (! queue) of
          SOME queue' => (queue := queue'; true)
        | NONE => false));
    in
      if extended then Future {promised = false, task = task, result = result}
      else
        (singleton o cond_forks)
          {name = "map_future", group = SOME group, deps = [task],
            pri = Task_Queue.pri_of_task task, interrupts = true}
          (fn () => f (join x))
    end;


(* promised futures -- fulfilled by external means *)

fun promise_name name abort : 'a future =
  let
    val group = worker_subgroup ();
    val result = Single_Assignment.var "promise" : 'a result;
    fun assign () = assign_result group result Exn.interrupt_exn
      handle Fail _ => true
        | exn =>
            if Exn.is_interrupt exn
            then raise Fail "Concurrent attempt to fulfill promise"
            else Exn.reraise exn;
    fun job () =
      Thread_Attributes.with_attributes Thread_Attributes.no_interrupts
        (fn _ => Exn.release (Exn.capture assign () before abort ()));
    val task = SYNCHRONIZED "enqueue_passive" (fn () =>
      Unsynchronized.change_result queue (Task_Queue.enqueue_passive group name job));
  in Future {promised = true, task = task, result = result} end;

fun promise abort = promise_name "passive" abort;

fun fulfill_result (Future {promised = true, task, result}) res =
      let
        val group = Task_Queue.group_of_task task;
        fun job ok =
          assign_result group result (if ok then res else Exn.interrupt_exn)
        val _ =
          Thread_Attributes.with_attributes Thread_Attributes.no_interrupts (fn _ =>
            let
              val passive_job =
                SYNCHRONIZED "fulfill_result" (fn () =>
                  Unsynchronized.change_result queue
                    (Task_Queue.dequeue_passive (Thread.self ()) task));
            in
              (case passive_job of
                SOME true => worker_exec (task, [job])
              | SOME false => ()
              | NONE => ignore (job (not (Task_Queue.is_canceled group))))
            end);
        val _ =
          if isSome (Single_Assignment.peek result) then ()
          else worker_waiting [task] (fn () => ignore (Single_Assignment.await result));
      in () end
  | fulfill_result _ _ = raise Fail "Not a promised future";

fun fulfill x res = fulfill_result x (Exn.Res res);


(* snapshot: current tasks of groups *)

fun snapshot groups =
  SYNCHRONIZED "snapshot" (fn () =>
    Task_Queue.group_tasks (! queue) groups);


(* shutdown *)

fun shutdown () =
  if isSome (worker_task ()) then
    raise Fail "Cannot shutdown while running as worker thread"
  else
    SYNCHRONIZED "shutdown" (fn () =>
      while scheduler_active () do
       (do_shutdown := true;
        Multithreading.tracing 1 (fn () => "SHUTDOWN: wait");
        wait scheduler_event));


(*final declarations of this structure!*)
val map = map_future;

end;

(* type 'a future = 'a Future.future; *)
