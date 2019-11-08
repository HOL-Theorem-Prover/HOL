(*  Title:      Pure/Concurrent/event_timer.ML
    Author:     Makarius

Initiate event after given point in time.

Note: events are run as synchronized action within a dedicated thread
and should finish quickly without further ado.
*)

signature EVENT_TIMER =
sig
  eqtype request
  val request: Time.time -> (unit -> unit) -> request
  val cancel: request -> bool
  val future: Time.time -> unit Future.future
  val shutdown: unit -> unit
end;

structure Event_Timer:> EVENT_TIMER =
struct

open Portable
(* type request *)

val request_counter = Counter.make ();
datatype request = Request of int;
fun new_request () = Request (request_counter ());


(* type requests *)

structure Requests = Table(
            type key = Time.time
            val ord = Time.compare
            fun pp t = HOLPP.add_string (Time.toString t)
          );
type requests = (request * (unit -> unit)) list Requests.table;

fun add_request time entry (requests: requests) =
  Requests.cons_list (time, entry) requests;

fun del_request req (requests: requests) =
  let
    val old_request =
      requests |> Requests.get_first (fn (key, entries) =>
        entries |> get_first (fn entry => if fst entry = req then SOME (key, entry) else NONE));
  in
    (case old_request of
      NONE => (false, requests)
    | SOME old => (true, Requests.remove_list (fst_eq equal) old requests))
  end;

fun next_request_time (requests: requests) =
  Option.map fst (Requests.min requests);

fun next_request_event t0 (requests: requests) =
  (case Requests.min requests of
    NONE => NONE
  | SOME (time, entries) =>
      if t0 < time then NONE
      else
        let
          val (rest, (_, event)) = front_last entries;
          val requests' =
            if null rest then Requests.delete time requests
            else Requests.update (time, rest) requests;
        in SOME (event, requests') end);


(* global state *)

datatype status = Normal | Shutdown_Req | Shutdown_Ack;

datatype state =
  State of {requests: requests, status: status, manager: Thread.thread option};

fun make_state (requests, status, manager) =
  State {requests = requests, status = status, manager = manager};

val normal_state = make_state (Requests.empty, Normal, NONE);
val shutdown_ack_state = make_state (Requests.empty, Shutdown_Ack, NONE);

fun is_shutdown s (State {requests, status, manager}) =
  Requests.is_empty requests andalso status = s andalso not (isSome manager);

fun is_shutdown_req (State {requests, status, ...}) =
  Requests.is_empty requests andalso status = Shutdown_Req;

val state = Synchronized.var "Event_Timer.state" normal_state;


(* manager thread *)

fun manager_loop () =
  if Synchronized.timed_access state
    (fn State {requests, ...} => next_request_time requests)
    (fn st as State {requests, status, manager} =>
      (case next_request_event (Time.now ()) requests of
        SOME (event, requests') =>
          let
            val _ = Exn.capture event ();
            val state' = make_state (requests', status, manager);
          in SOME (true, state') end
      | NONE =>
          if is_shutdown_req st
          then SOME (false, shutdown_ack_state)
          else NONE)) <> SOME false
  then manager_loop () else ();

fun manager_check manager =
  if isSome manager andalso Thread.isActive (valOf manager) then manager
  else
    SOME (Standard_Thread.fork {name = "event_timer", stack_limit = NONE,
                                interrupts = false}
      manager_loop);

fun shutdown () =
  Thread_Attributes.uninterruptible (fn restore_attributes => fn () =>
    if Synchronized.change_result state (fn st as State {requests, manager, ...} =>
      if is_shutdown Normal st then (false, st)
      else if is_shutdown Shutdown_Ack st orelse is_shutdown_req st then
        raise Fail "Concurrent attempt to shutdown event timer"
      else (true, make_state (requests, Shutdown_Req, manager_check manager)))
    then
      restore_attributes (fn () =>
        Synchronized.guarded_access state
          (fn st => if is_shutdown Shutdown_Ack st then SOME ((), normal_state) else NONE)) ()
      handle exn =>
        if Exn.is_interrupt exn then
          Synchronized.change state (fn State {requests, manager, ...} =>
            make_state (requests, Normal, manager))
        else ()
    else ()) ();


(* main operations *)

fun request time event =
  Synchronized.change_result state (fn State {requests, status, manager} =>
    let
      val req = new_request ();
      val requests' = add_request time (req, event) requests;
      val manager' = manager_check manager;
    in (req, make_state (requests', status, manager')) end);

fun cancel req =
  Synchronized.change_result state (fn State {requests, status, manager} =>
    let
      val (canceled, requests') = del_request req requests;
      val manager' = manager_check manager;
    in (canceled, make_state (requests', status, manager')) end);

val future = Thread_Attributes.uninterruptible (fn _ => fn time =>
  let
    val req: request Single_Assignment.var = Single_Assignment.var "request"
    fun abort () = ignore (cancel (Single_Assignment.await req))
    val promise: unit Future.future = Future.promise_name "event_timer" abort
    val _ = Single_Assignment.assign req (request time (Future.fulfill promise))
  in
    promise
  end);

end;
