structure Context :> Context =
struct

  val ERR = Feedback.mk_HOL_ERR "Context"


  (* ---------------------------------------------------------------------
       Locking model

       Reads (`snapshot`, `Data.get`): lock-free.  `t` is immutable, so
       a caller observing `Sref.value ctx` keeps a consistent view.

       Writes (`Data.write`, `Data.modify`, `update`, `gen_update`):
       hold `ctx_rwlock` on the read side and swap `ctx` atomically at
       the tail end.  Different-slot writers proceed concurrently.
       `Data.modify` additionally serialises same-slot writers via a
       per-slot `Lock.t`; the user callback runs under that Lock but
       *outside* `ctx`'s Sref mutex, so cross-slot callbacks (e.g.
       TypeBase.write → BasicProvers' registered update_fn → simp
       fullmake) don't deadlock on the shared Sref mutex.  Same-slot
       recursion inside `Data.modify`'s callback does deadlock —
       callers must not do it.

       `restore ctx'`: write side of `ctx_rwlock`.  Exclusive; waits
       for in-flight writers and blocks new ones.  Must not be called
       from inside a `Data.modify` callback (the calling thread holds
       the read side and would wait for itself).

       Why the `ctx` Sref mutex still exists once we have per-slot
       locks: `session_data` is a persistent Symtab, so a slot write is
       "read old pointer, compute new pointer, replace".  Two writers
       on different slots would each derive from the same old pointer
       and one would clobber the other's key.  The Sref mutex
       linearises that tail-end pointer swap.
     --------------------------------------------------------------------- *)

  type t = {
    termsig      : Type_dtype.holty KernelSig.symboltable,
    typesig      : int KernelSig.symboltable,
    current_thy  : string option,
    session_data : UniversalType.t Symtab.table
  }

  fun termsig      ({termsig,...} : t)      = termsig
  fun typesig      ({typesig,...} : t)      = typesig
  fun current_thy  ({current_thy,...} : t)  = current_thy
  fun session_data ({session_data,...} : t) = session_data

  fun map_termsig f {termsig, typesig, current_thy, session_data} =
      {termsig = f termsig, typesig = typesig,
       current_thy = current_thy, session_data = session_data}
  fun map_typesig f {termsig, typesig, current_thy, session_data} =
      {termsig = termsig, typesig = f typesig,
       current_thy = current_thy, session_data = session_data}
  fun map_current_thy f {termsig, typesig, current_thy, session_data} =
      {termsig = termsig, typesig = typesig,
       current_thy = f current_thy, session_data = session_data}
  fun map_session_data f {termsig, typesig, current_thy, session_data} =
      {termsig = termsig, typesig = typesig,
       current_thy = current_thy, session_data = f session_data}

  val initial : t = {
    termsig      = KernelSig.empty_table,
    typesig      = KernelSig.empty_table,
    current_thy  = NONE,
    session_data = Symtab.empty
  }

  val ctx : t Sref.t = Sref.new initial

  val ctx_rwlock : RWLock.t = RWLock.new "Context.ctx"

  (* A proof is a function of the context it is given.  Code reached
     while one is running that reads the ambient context instead had a
     context in scope and dropped it, so `snapshot` reports when called
     inside the dynamic extent that `TAC_PROOF` marks.  Reads at
     declaration level are the ambient wrappers doing their job and are
     not reported.

     The extent is per-thread: a worker proving on its own thread must
     not see another's.  `ThreadLocal.get` is NONE on a fresh thread,
     which reads as depth zero --- right for a thread that is not
     proving, and harmless for one that is, since its own TAC_PROOF
     sets the depth before any tactic runs. *)
  local
    val depth : int ThreadLocal.t = ThreadLocal.new ()
    fun get () = case ThreadLocal.get depth of NONE => 0 | SOME n => n
    fun set n = ThreadLocal.set (depth, n)
    (* 0 silent, 1 one report per theory, 2 every read, 3 error.  Level 1
       is the default: the reports are a style ratchet, and one marker per
       theory log says which theories still offend without the volume ---
       there are 611k reads to report across a core build, which costs
       about a tenth of the build's heaviest theory and buries its log. *)
    val action = ref 1
    val _ = Feedback.register_trace ("ambient context inside proof", action, 3)
    val reported : string list ref = ref []
    fun thyname () =
        case #current_thy (Sref.value ctx) of
            NONE => "<no current theory>"
          | SOME s => s
    fun report () =
        let val thy = thyname ()
            (* built only where it is used: at level 1 the common case is
               a theory already reported, and this fires per read *)
            fun msg () = "ambient context read while a proof was running (in " ^
                         thy ^ ")"
            fun warn () = Feedback.HOL_WARNING "Context" "snapshot" (msg ())
        in
          case !action of
              1 => if Lib.mem thy (!reported) then ()
                   else (reported := thy :: !reported; warn ())
            | 2 => warn ()
            | _ => raise ERR "snapshot" (msg ())
        end
  in
    fun in_proof f x =
        let val n = get ()
            val () = set (n + 1)
            val r = f x handle e => (set n; raise e)
        in
          set n; r
        end
    fun snapshot () =
        (if !action > 0 andalso get () > 0 then report () else ();
         Sref.value ctx)
  end

  fun restore  c  =
      RWLock.write_locked ctx_rwlock (fn () => Sref.update ctx (fn _ => c))

  fun update f =
      RWLock.read_locked ctx_rwlock (fn () => Sref.update ctx f)
  fun gen_update f =
      RWLock.read_locked ctx_rwlock (fn () => Sref.gen_update ctx f)

  structure Data =
  struct
    (* A slot carries the name it lives under in the session-data dict,
       the UniversalType wrap/unwrap closures produced by embed(), the
       empty value used when the slot has never been populated in the
       current context, and a per-slot Lock that serialises `modify`
       against itself. *)
    type 'a slot = {
      name   : string,
      lock   : Lock.t,
      wrap   : 'a -> UniversalType.t,
      unwrap : UniversalType.t -> 'a option,
      empty  : 'a,
      pp     : 'a -> string
    }

    (* Registration installs the empty seed into session_data under
       `name`, so duplicate `new` calls with the same name fail loudly
       instead of silently minting a shadow slot whose reads would
       later crash (valOf on a NONE unwrap from a foreign embed pair). *)
    fun new {name, empty, pp} =
        let val (wrap, unwrap) = UniversalType.embed ()
            val () = Sref.update ctx (fn c =>
                if Symtab.defined (session_data c) name then
                  raise ERR "Data.new"
                            ("slot with name \"" ^ name ^ "\" already exists")
                else
                  map_session_data (Symtab.update (name, wrap empty)) c)
        in {name = name,
            lock = Lock.new ("Context.slot." ^ name),
            wrap = wrap, unwrap = unwrap,
            empty = empty, pp = pp}
        end

    fun get (slot : 'a slot) (c : t) =
        case Symtab.lookup (session_data c) (#name slot) of
            NONE   => #empty slot
          | SOME u => valOf (#unwrap slot u)

    fun put (slot : 'a slot) v c =
        map_session_data (Symtab.update (#name slot, #wrap slot v)) c

    fun update (slot : 'a slot) f c =
        put slot (f (get slot c)) c

    fun write slot v =
        RWLock.read_locked ctx_rwlock (fn () =>
          Sref.update ctx (put slot v))

    fun modify slot f =
        RWLock.read_locked ctx_rwlock (fn () =>
          Lock.synchronized (#lock slot) (fn () =>
            let val new = f (get slot (Sref.value ctx))
            in Sref.update ctx (put slot new) end))

    fun with_slot_value slot v f x =
        let val old = get slot (Sref.value ctx)
            val () = write slot v
            val r = f x handle e => (write slot old; raise e)
            val () = write slot old
        in r end
  end

end
