structure rwlock :> rwlock =
struct

type 'a t = { readers : int Sref.t,
              writer_mutex : Mutex.mutex,
              state : 'a }

fun new v = { readers = Sref.new 0,
              writer_mutex = Mutex.mutex(),
              state = v }

fun read (rwl : 'a t) f = let
  val _ =
      Sref.update (#readers rwl) (
        fn i => (
          if i = 0 then Mutex.lock (#writer_mutex rwl)
          else () ;
          i + 1
        )
      )
  val result = Exn.capture f (#state rwl)
in
  Sref.update (#readers rwl) (
    fn i => (
      if i = 1 then Mutex.unlock (#writer_mutex rwl)
      else ();
      i - 1
    )
  );
  Exn.release result
end

fun write (rwl : 'a t) (f : 'a -> unit) = let
  val _ = Mutex.lock (#writer_mutex rwl)
  val u_or_exn = Exn.capture f (#state rwl)
in
  Mutex.unlock (#writer_mutex rwl);
  Exn.release u_or_exn
end

end
