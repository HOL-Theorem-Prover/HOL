(*  Title:      Pure/Concurrent/task_queue.ML
    Author:     Makarius

Ordered queue of grouped tasks.
*)

signature TASK_QUEUE =
sig
  type group
  val new_group: group option -> group
  val group_id: group -> int
  val eq_group: group * group -> bool
  val cancel_group: group -> exn -> unit
  val is_canceled: group -> bool
  val group_status: group -> exn list
  val str_of_group: group -> string
  val str_of_groups: group -> string
  val urgent_pri: int
  type task
  val dummy_task: task
  val group_of_task: task -> group
  val name_of_task: task -> string
  val pri_of_task: task -> int
  val str_of_task: task -> string
  val str_of_task_groups: task -> string
  val running: task -> (unit -> 'a) -> 'a
  val joining: task -> (unit -> 'a) -> 'a
  val waiting: task -> task list -> (unit -> 'a) -> 'a
  type queue
  val empty: queue
  val group_tasks: queue -> group list -> task list
  val known_task: queue -> task -> bool
  val all_passive: queue -> bool
  val total_jobs : queue -> int
  val status: queue -> {ready: int, pending: int, running: int, passive: int, urgent: int}
  val cancel: queue -> group -> Thread.thread list
  val cancel_all: queue -> group list * Thread.thread list
  val finish: task -> queue -> bool * queue
  val enroll: Thread.thread -> string -> group -> queue -> task * queue
  val enqueue_passive: group -> string -> (unit -> bool) -> queue -> task * queue
  val enqueue: string -> group -> task list -> int -> (bool -> bool) -> queue -> task * queue
  val extend: task -> (bool -> bool) -> queue -> queue option
  val dequeue_passive: Thread.thread -> task -> queue -> bool option * queue
  val dequeue: Thread.thread -> bool -> queue -> (task * (bool -> bool) list) option * queue
  val dequeue_deps: Thread.thread -> task list -> queue ->
    (((task * (bool -> bool) list) option * task list) * queue)
end;

structure Task_Queue: TASK_QUEUE =
struct

open Portable

val new_id = Counter.make ();

(** nested groups of tasks **)

(* groups *)

abstype group = Group of
 {parent: group option,
  id: int,
  status: exn option Synchronized.var}
with

fun make_group (parent, id, status) = Group {parent = parent, id = id, status = status};

fun new_group parent = make_group (parent, new_id (), Synchronized.var "group_status" NONE);

fun group_id (Group {id, ...}) = id;
fun eq_group (group1, group2) = group_id group1 = group_id group2;

fun fold_groups f (g as Group {parent = NONE, ...}) a = f g a
  | fold_groups f (g as Group {parent = SOME group, ...}) a = fold_groups f group (f g a);


(* group status *)

fun cancel_group (Group {status, ...}) exn =
  Synchronized.change status
    (fn exns => SOME (Par_Exn.make (exn :: the_list exns)));

fun is_canceled (Group {parent, status, ...}) =
  isSome (Synchronized.value status) orelse
  (case parent of NONE => false | SOME group => is_canceled group);

fun group_status (Group {parent, status, ...}) =
  the_list (Synchronized.value status) @
    (case parent of NONE => [] | SOME group => group_status group);

fun str_of_group group =
  (is_canceled group ? enclose "(" ")") (Int.toString (group_id group));

fun str_of_groups group =
  String.concatWith "/" (map str_of_group (rev (fold_groups cons group [])));

end;


(* tasks *)

val urgent_pri = 1000;

type timing = Time.time * Time.time * string list;  (*run, wait, wait dependencies*)

val timing_start = (Time.zeroTime, Time.zeroTime, []): timing;

fun new_timing () =
  if ! Multithreading.trace < 2 then NONE
  else SOME (Synchronized.var "timing" timing_start);

abstype task = Task of
 {group: group,
  name: string,
  id: int,
  pri: int option,
  timing: timing Synchronized.var option}
with

val dummy_task =
  Task {group = new_group NONE, name = "", id = 0, pri = NONE, timing = NONE};

fun new_task group name pri =
  Task {group = group, name = name, id = new_id (), pri = pri, timing = new_timing ()};

fun group_of_task (Task {group, ...}) = group;
fun name_of_task (Task {name, ...}) = name;
fun pri_of_task (Task {pri, ...}) = the_default 0 pri;

fun str_of_task (Task {name, id, ...}) =
  if name = "" then Int.toString id else Int.toString id ^ " (" ^ name ^ ")";

fun str_of_task_groups task = str_of_task task ^ " in " ^ str_of_groups (group_of_task task);

fun update_timing update (Task {timing, ...}) e =
  Thread_Attributes.uninterruptible (fn restore_attributes => fn () =>
    let
      val start = Time.now ();
      val result = Exn.capture (restore_attributes e) ();
      val t = Time.now () - start;
      val _ = (case timing of NONE => () | SOME var => Synchronized.change var (update t));
    in Exn.release result end) ();

fun task_ord (Task{id=id1, pri=pri1, ...},Task{id = id2, pri = pri2, ...}) =
    pair_compare (flip_cmp (option_compare Int.compare), Int.compare)
                 ((pri1, id1), (pri2, id2))
end;

structure TaskKEY = struct
  type key = task
  val ord = task_ord
  fun pp t = PolyML.prettyRepresentation(t,~1)
end
structure Tasks = Table(TaskKEY);
structure Task_Graph = Graph(TaskKEY);


(* timing *)

fun running task =
  update_timing (fn t => fn (a, b, ds) => (a + t, b, ds)) task;

fun joining task =
  update_timing (fn t => fn (a, b, ds) => (a - t, b, ds)) task;

fun waiting task deps =
  update_timing (fn t => fn (a, b, ds) =>
    (a - t, b + t,
      if ! Multithreading.trace > 0
      then foldl' (op_insert equal o name_of_task) deps ds else ds)) task;



(** queue of jobs and groups **)

(* known group members *)

type groups = unit Tasks.table Inttab.table;

fun get_tasks (groups: groups) gid =
  the_default Tasks.empty (Inttab.lookup groups gid);

fun add_task (gid, task) groups =
  Inttab.update (gid, Tasks.update (task, ()) (get_tasks groups gid)) groups;

fun del_task (gid, task) groups =
  let val tasks = Tasks.delete_safe task (get_tasks groups gid) in
    if Tasks.is_empty tasks then Inttab.delete_safe gid groups
    else Inttab.update (gid, tasks) groups
  end;


(* job dependency graph *)

datatype job =
  Job of (bool -> bool) list |
  Running of Thread.thread |
  Passive of unit -> bool;

type jobs = job Task_Graph.T;

fun get_job (jobs: jobs) task = Task_Graph.get_node jobs task;
fun set_job task job (jobs: jobs) = Task_Graph.map_node task (K job) jobs;

fun add_job task dep (jobs: jobs) =
  Task_Graph.add_edge (dep, task) jobs handle Task_Graph.UNDEF _ => jobs;


(* queue *)

datatype queue = Queue of {groups: groups, jobs: jobs, urgent: int, total : int};

fun make_queue groups jobs urgent total =
  Queue {groups = groups, jobs = jobs, urgent = urgent, total = total};
val empty = make_queue Inttab.empty Task_Graph.empty 0 0;

fun group_tasks (Queue {groups, ...}) gs =
  foldl' (fn g => fn tasks =>
             Tasks.merge equal (tasks, get_tasks groups (group_id g)))
         gs Tasks.empty
         |> Tasks.keys;

fun known_task (Queue {jobs, ...}) task = can (Task_Graph.get_entry jobs) task;


(* job status *)

fun ready_job (task, (Job list, (deps, _))) =
      if Task_Graph.Keys.is_empty deps then SOME (task, rev list) else NONE
  | ready_job (task, (Passive abort, (deps, _))) =
      if Task_Graph.Keys.is_empty deps andalso is_canceled (group_of_task task)
      then SOME (task, [fn _ => abort ()])
      else NONE
  | ready_job _ = NONE;

fun ready_job_urgent false = ready_job
  | ready_job_urgent true = (fn entry as (task, _) =>
      if pri_of_task task >= urgent_pri then ready_job entry else NONE);

fun active_job (task, (Running _, _)) = SOME (task, [])
  | active_job arg = ready_job arg;

fun all_passive (Queue {jobs, ...}) =
  not (isSome (Task_Graph.get_first active_job jobs))


(* queue status *)
fun total_jobs (Queue {total,...}) = total

fun status (Queue {jobs, urgent, ...}) =
  let
    val (x, y, z, w) =
      Task_Graph.fold (fn (_, (job, (deps, _))) => fn (x, y, z, w) =>
          (case job of
            Job _ => if Task_Graph.Keys.is_empty deps then (x + 1, y, z, w) else (x, y + 1, z, w)
          | Running _ => (x, y, z + 1, w)
          | Passive _ => (x, y, z, w + 1)))
        jobs (0, 0, 0, 0);
  in {ready = x, pending = y, running = z, passive = w, urgent = urgent} end;



(** task queue operations **)

(* cancel -- peers and sub-groups *)

fun cancel (Queue {groups, jobs, ...}) group =
  let
    val _ = cancel_group group Exn.Interrupt;
    val running =
      Tasks.fold
        (fn (task, _) => (
           case get_job jobs task of
               Running thread => op_insert (curry Thread.equal) thread
             | _ => I)
        )
        (get_tasks groups (group_id group)) []
  in running end;

fun cancel_all (Queue {jobs, ...}) =
  let
    fun cancel_job (task, (job, _)) (groups, running) =
      let
        val group = group_of_task task;
        val _ = cancel_group group Exn.Interrupt;
      in
        case job of
            Running t => (op_insert (curry eq_group) group groups,
                          op_insert (curry Thread.equal) t running)
         | _ => (groups, running)
      end;
    val running = Task_Graph.fold cancel_job jobs ([], []);
  in running end;


(* finish *)

fun finish task (Queue {groups, jobs, urgent, total}) =
  let
    val group = group_of_task task;
    val groups' = fold_groups (fn g => del_task (group_id g, task)) group groups;
    val jobs' = Task_Graph.del_node task jobs;
    val maximal = Task_Graph.is_maximal jobs task;
    val total' = total - 1
  in (maximal, make_queue groups' jobs' urgent total') end;


(* enroll *)

fun enroll thread name group (Queue {groups, jobs, urgent, total}) =
  let
    val task = new_task group name NONE;
    val groups' = fold_groups (fn g => add_task (group_id g, task)) group groups;
    val jobs' = jobs |> Task_Graph.new_node (task, Running thread);
    val total' = total + 1
  in (task, make_queue groups' jobs' urgent total') end;


(* enqueue *)

fun enqueue_passive group name abort (Queue {groups, jobs, urgent, total}) =
  let
    val task = new_task group name NONE;
    val groups' = fold_groups (fn g => add_task (group_id g, task)) group groups;
    val jobs' = jobs |> Task_Graph.new_node (task, Passive abort);
    val total' = total + 1
  in (task, make_queue groups' jobs' urgent total') end;

fun enqueue name group deps pri job (Queue {groups, jobs, urgent, total}) =
  let
    val task = new_task group name (SOME pri);
    val groups' = fold_groups (fn g => add_task (group_id g, task)) group groups;
    val jobs' = jobs
      |> Task_Graph.new_node (task, Job [job])
      |> foldl' (add_job task) deps;
    val urgent' = if pri >= urgent_pri then urgent + 1 else urgent;
    val total' = total + 1
  in (task, make_queue groups' jobs' urgent' total) end;

fun extend task job (Queue {groups, jobs, urgent, total}) =
  case Portable.total (get_job jobs) task of
    SOME (Job list) =>
      SOME (make_queue groups (set_job task (Job (job :: list)) jobs)
                       urgent total)
   | _ => NONE


(* dequeue *)

fun dequeue_passive thread task (queue as Queue {groups, jobs, urgent, total}) =
  case Portable.total (get_job jobs) task of
    SOME (Passive _) =>
      let val jobs' = set_job task (Running thread) jobs
      in (SOME true, make_queue groups jobs' urgent total) end
  | SOME _ => (SOME false, queue)
  | NONE => (NONE, queue)

fun dequeue thread urgent_only (queue as Queue {groups, jobs, urgent, total}) =
  if not urgent_only orelse urgent > 0 then
    (case Task_Graph.get_first (ready_job_urgent urgent_only) jobs of
      SOME (result as (task, _)) =>
        let
          val jobs' = set_job task (Running thread) jobs;
          val urgent' = if pri_of_task task >= urgent_pri then urgent - 1 else urgent;
        in (SOME result, make_queue groups jobs' urgent' total) end
    | NONE => (NONE, queue))
  else (NONE, queue);


(* dequeue wrt. dynamic dependencies *)

fun dequeue_deps thread deps (queue as Queue {groups, jobs, urgent, total}) =
  let
    fun ready [] rest = (NONE, rev rest)
      | ready (task :: tasks) rest =
          (case Portable.total (Task_Graph.get_entry jobs) task of
            NONE => ready tasks rest
          | SOME (_, entry) =>
              (case ready_job (task, entry) of
                NONE => ready tasks (task :: rest)
              | some => (some, foldl' cons rest tasks)));

    fun ready_dep _ [] = NONE
      | ready_dep seen (task :: tasks) =
          if Tasks.defined seen task then ready_dep seen tasks
          else
            let val entry as (_, (ds, _)) = #2 (Task_Graph.get_entry jobs task) in
              (case ready_job (task, entry) of
                NONE => ready_dep (Tasks.update (task, ()) seen) (Task_Graph.Keys.dest ds @ tasks)
              | some => some)
            end;

    fun result (res as (task, _)) deps' =
      let
        val jobs' = set_job task (Running thread) jobs;
        val urgent' = if pri_of_task task >= urgent_pri then urgent - 1 else urgent;
      in ((SOME res, deps'), make_queue groups jobs' urgent' total) end;
  in
    (case ready deps [] of
      (SOME res, deps') => result res deps'
    | (NONE, deps') =>
        (case ready_dep Tasks.empty deps' of
          SOME res => result res deps'
        | NONE => ((NONE, deps'), queue)))
  end;

end;
