structure RWLock :> RWLock =
struct

  (* state:
       0    idle
       n>0  n readers hold the lock
       ~1   a writer holds the lock
     waiting_writers: writers currently blocked in acquire; new readers
       stall while this is positive so writers don't starve. *)
  type t = {
    name            : string,
    mutex           : Mutex.mutex,
    cond            : ConditionVar.conditionVar,
    state           : int ref,
    waiting_writers : int ref
  }

  fun new name : t =
      {name = name,
       mutex = Mutex.mutex (),
       cond = ConditionVar.conditionVar (),
       state = ref 0,
       waiting_writers = ref 0}

  fun acquire_read ({name, mutex, cond, state, waiting_writers} : t) =
      Multithreading.synchronized (name ^ ".acquire_read") mutex (fn () =>
        let fun wait () =
              if !state < 0 orelse !waiting_writers > 0 then
                (ConditionVar.wait (cond, mutex); wait ())
              else
                state := !state + 1
        in wait () end)

  fun release_read ({name, mutex, cond, state, ...} : t) =
      Multithreading.synchronized (name ^ ".release_read") mutex (fn () =>
        (state := !state - 1;
         if !state = 0 then ConditionVar.broadcast cond else ()))

  fun read_locked lk body =
      let val () = acquire_read lk
          val r = Exn.capture body ()
      in release_read lk; Exn.release r end

  fun acquire_write ({name, mutex, cond, state, waiting_writers} : t) =
      Multithreading.synchronized (name ^ ".acquire_write") mutex (fn () =>
        (waiting_writers := !waiting_writers + 1;
         let fun wait () =
               if !state <> 0 then
                 (ConditionVar.wait (cond, mutex); wait ())
               else
                 (waiting_writers := !waiting_writers - 1;
                  state := ~1)
         in wait () end))

  fun release_write ({name, mutex, cond, state, ...} : t) =
      Multithreading.synchronized (name ^ ".release_write") mutex (fn () =>
        (state := 0; ConditionVar.broadcast cond))

  fun write_locked lk body =
      let val () = acquire_write lk
          val r = Exn.capture body ()
      in release_write lk; Exn.release r end

end
