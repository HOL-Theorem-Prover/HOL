structure Refute_Session :> Refute_Session =
struct
  (* [epoch] changes with every change that reaches the live context, so an
     equal epoch in a view means the live value is the one the view
     started from. *)
  type 'a cell = {epoch : unit ref, value : 'a}

  type t =
    {view : Context.t Synchronized.var,
     changed : (unit ref * (unit -> unit)) list Synchronized.var}

  datatype 'a state = State of
    {name : string,
     slot : 'a cell Context.Data.slot,
     lock : Mutex.mutex,
     id : unit ref,
     committed : bool}

  val active : t Thread_Data.var = Thread_Data.var ()

  fun current () = Thread_Data.get active

  fun bind session f x = Thread_Data.setmp active session f x

  fun make committed name empty =
    State {name = name,
           slot = Context.Data.new
             {name = "Refute." ^ name,
              empty = {epoch = ref (), value = empty},
              pp = fn _ => "<Refute." ^ name ^ ">"},
           lock = Mutex.mutex (),
           id = ref (),
           committed = committed}

  fun state name empty = make true name empty
  fun local_state name empty = make false name empty

  fun synchronized (State {name, lock, ...}) f =
    Multithreading.synchronized ("Refute." ^ name) lock f

  fun cell_in (State {slot, ...}) ctxt = Context.Data.get slot ctxt

  fun read st =
    case current () of
        SOME {view, ...} => #value (cell_in st (Synchronized.value view))
      | NONE => #value (cell_in st (Context.snapshot ()))

  (* The caller holds the state's lock, so no other change of the state
     comes between its read of the view and this store.  Only the store
     runs under the view's lock: a callback run there could read no
     state. *)
  fun store_view ({view, ...} : t) (State {slot, ...}) cell =
    Synchronized.change view (Context.Data.put slot cell)

  fun commit (session : t) (st as State {slot, ...}) () =
    let val mine = cell_in st (Synchronized.value (#view session))
    in
      synchronized st (fn () =>
        Context.Data.modify slot (fn live =>
          if #epoch live = #epoch mine then
            {epoch = ref (), value = #value mine}
          else live))
    end

  fun note_changed (session : t) (st as State {id, committed, ...}) =
    if not committed then ()
    else
      Synchronized.change (#changed session) (fn changed =>
        if List.exists (fn (other, _) => other = id) changed then changed
        else (id, commit session st) :: changed)

  (* The caller holds the state's lock. *)
  fun change (st as State {slot, ...}) f =
    case current () of
        SOME session =>
          let
            val {epoch, value} =
              cell_in st (Synchronized.value (#view session))
          in
            store_view session st {epoch = epoch, value = f value};
            note_changed session st
          end
      | NONE =>
          if Context.is_pinned () then ()
          else
            Context.Data.modify slot (fn {value, ...} =>
              {epoch = ref (), value = f value})

  fun update st f = synchronized st (fn () => change st f)

  fun transact st f =
    synchronized st (fn () =>
      let val (result, value) = f (read st)
      in change st (fn _ => value); result end)

  fun publish (st as State {slot, ...}) f =
    synchronized st (fn () =>
      let
        val epoch = ref ()
        val previous = ref epoch
        val _ = Context.Data.modify slot (fn {epoch = old, value} =>
          (previous := old; {epoch = epoch, value = f value}))
      in
        case current () of
            NONE => ()
          | SOME session =>
              let
                val {epoch = mine, value} =
                  cell_in st (Synchronized.value (#view session))
              in
                store_view session st
                  {epoch = if mine = !previous then epoch else ref (),
                   value = f value}
              end
      end)

  fun run ctxt f =
    let
      val session : t =
        {view = Synchronized.var "Refute session" ctxt,
         changed = Synchronized.var "Refute session changes" []}
      val result = Exn.capture (bind (SOME session) f) ()
      val _ =
        if Context.is_pinned () then ()
        else
          Thread_Attributes.uninterruptible (fn _ => fn () =>
            List.app (fn (_, commit) => commit ())
              (rev (Synchronized.value (#changed session)))) ()
    in
      Exn.release result
    end
end
