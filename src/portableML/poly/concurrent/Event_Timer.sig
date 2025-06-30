signature Event_Timer =
sig
  eqtype request
  val request: Time.time -> (unit -> unit) -> request
  val cancel: request -> bool
  val future: Time.time -> unit Future.future
  val shutdown: unit -> unit
end;
