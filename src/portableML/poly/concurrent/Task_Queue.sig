signature Task_Queue =
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
