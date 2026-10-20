signature Refute_Session = sig
  (* One Refute call: a view of the context captured at its entry, which
     every thread working for the call reads instead of the live context,
     plus the call's own state changes, committed at its exit. *)
  type t

  (* Runs [f ()] with a fresh session over [ctxt] bound on this thread.  On
     every exit path, commits each state the call changed, unless a pin
     answers this thread's reads (the [BasicProvers.srw_ss] precedent). *)
  val run : Context.t -> (unit -> 'a) -> 'a

  (* The session bound on this thread; [bind] hands it to a worker. *)
  val current : unit -> t option
  val bind : t option -> ('a -> 'b) -> 'a -> 'b

  (* HolRefute state in a [Context.Data] slot.  A [local_state] is never
     committed: it lives exactly as long as one call. *)
  type 'a state
  val state : string -> 'a -> 'a state
  val local_state : string -> 'a -> 'a state

  (* The bound session's view, or the live context outside any call. *)
  val context : unit -> Context.t
  val read : 'a state -> 'a

  (* Every change of a state is serialized with the others, and its
     callback may read any state but must not change the one it changes. *)

  (* A change derived by the running call.  Seen by the rest of the call,
     and committed at its exit only if no other change reached the live
     value in between; a lost commit costs recomputation, never
     correctness.  Outside a call it changes the live context directly,
     except under a pin. *)
  val update : 'a state -> ('a -> 'a) -> unit

  (* [update] that also returns a result. *)
  val transact : 'a state -> ('a -> 'b * 'a) -> 'b

  (* An authoritative change (a registration, a theory event): applied to
     the live context and to the bound session's view.  Every other
     running call's changes to the state are then dropped at its commit. *)
  val publish : 'a state -> ('a -> 'a) -> unit
end
