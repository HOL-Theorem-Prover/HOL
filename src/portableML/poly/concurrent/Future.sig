signature Future =
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
  type params = {name: string, group: group option, deps: task list,
                 pri: int, interrupts: bool}
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
  val snapshot: group list -> task list
  val shutdown: unit -> unit
end;
