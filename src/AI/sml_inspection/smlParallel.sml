(* ========================================================================  *)
(* FILE          : smlParallel.sml                                           *)
(* DESCRIPTION   : Internal (shared memory) and external                     *)
(* (starting new buildheap process) parallel calls                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure smlParallel :> smlParallel =
struct

open HolKernel Abbrev boolLib aiLib

val ERR = mk_HOL_ERR "smlParallel"

(* -------------------------------------------------------------------------
   Force usage of a thread even when using one core
   ------------------------------------------------------------------------- *)

val use_thread_flag = ref false

(* -------------------------------------------------------------------------
   Capturing and releasing exceptions
   ------------------------------------------------------------------------- *)

datatype 'a result = Res of 'a | Exn of exn;

fun capture f x = Res (f x) handle e => Exn e

fun release (Res y) = y
  | release (Exn x) = raise x

fun is_res (Res y) = true
  | is_res (Exn x) = false

fun is_exn (Res y) = false
  | is_exn (Exn x) = true

val attrib = [Thread.InterruptState Thread.InterruptAsynch, Thread.EnableBroadcastInterrupt true]

(* -------------------------------------------------------------------------
   Simplest parmap (probably the same behavior as Parmap.parmap)
   ------------------------------------------------------------------------- *)

fun parmap_exact ncores forg lorg =
  if length lorg <> ncores then raise ERR "parmap_exact" "" else
  if ncores = 1 andalso not (!use_thread_flag) then map forg lorg else
  let
    val ain = Vector.fromList (List.map ref lorg)
    val aout = Vector.fromList (List.map (fn _ => ref NONE) lorg)
    fun process pi =
      let
        val inref = Vector.sub (ain,pi)
        val outref = Vector.sub (aout,pi)
      in
        outref := SOME (capture forg (!inref))
      end
    fun fork_on pi = Thread.fork (fn () => process pi, attrib)
    val threadl = map fork_on (List.tabulate (ncores,I))
    fun loop () =
      (if exists Thread.isActive threadl then loop () else ())
  in
    loop ();
    map (release o valOf o !) (vector_to_list aout)
  end

(* -------------------------------------------------------------------------
   Regrouping input in batches before giving it to parmap_exact.
   ------------------------------------------------------------------------- *)

fun parmap_batch ncores f l =
  if ncores = 1 andalso not (!use_thread_flag)
  then map f l
  else List.concat (parmap_exact ncores (map f) (cut_n ncores l))


(* -------------------------------------------------------------------------
   The function parmap_gen start n threads, and generate a parmap function
   relying on this threads and a function to close this threads.
   This makes repeated calls of parmap f on different lists faster.
   Otherwise it behaves like parmap_batch.
   ------------------------------------------------------------------------- *)

fun parmap_gen ncore =
  if ncore = 1 andalso not (!use_thread_flag)
  then (fn f => (fn l => map f l), fn () => ()) else
  let
    val endflag = ref false
    val inv = Vector.tabulate (ncore, fn _ => ref NONE)
    val outv = Vector.tabulate (ncore, fn _ => ref NONE)
    val endv = Vector.tabulate (ncore, fn _ => ref false)
    val waitv = Vector.tabulate (ncore, fn _ => ref false)
    val f_ref = ref NONE
      fun reset_outv () =
       let fun init_one pi =
         let val outref = Vector.sub (outv,pi) in outref := NONE end
       in
         ignore (List.tabulate (ncore, init_one))
       end
    fun process pi =
      if !endflag then
        let val endref = Vector.sub (endv,pi) in endref := true end
      else
      let val inref = Vector.sub (inv,pi) in
        case !inref of
          NONE => process pi
        | SOME x =>
          let val outref = Vector.sub (outv,pi) in
            inref := NONE; outref := SOME (map (valOf (!f_ref)) x);
            process pi
          end
      end
    fun fork_on pi = Thread.fork (fn () => process pi, attrib)
    val threadl = List.tabulate (ncore,fork_on)
    fun wait_resultl () =
      if Vector.all (isSome o !) outv then () else wait_resultl ()
    fun parmap_loc f l =
      let
        val _ = f_ref := SOME f
        val _ = reset_outv ()
        val inv_loc = Vector.fromList (cut_n ncore l)
        fun assign pi =
          let val inref = Vector.sub (inv,pi) in
            inref := SOME (Vector.sub (inv_loc,pi))
          end
        val _ = List.tabulate (ncore, assign)
        val _ = wait_resultl ()
        val ll = vector_to_list (Vector.map (valOf o !) outv)
      in
        reset_outv (); List.concat ll
      end
    fun wait_close () =
      if exists Thread.isActive threadl then wait_close () else ()
    fun close_threadl () = (endflag := true; wait_close ())
  in
    (parmap_loc, close_threadl)
  end

(* -------------------------------------------------------------------------
   Smart allocation of inputs to waiting threads
   ------------------------------------------------------------------------- *)

fun parmap_queue_err ncores forg lorg =
  let
    val end_flag = ref false
    (* input *)
    val sizeorg = length lorg
    val lin = List.tabulate (ncores,(fn x => (x, ref NONE)))
    val din = dnew Int.compare lin
    fun fi xi x = (x,xi)
    val queue = ref (mapi fi lorg)
    (* update process inputs *)
    fun update_from_queue lineref =
      if null (!queue) then ()
      else (lineref := SOME (hd (!queue)); queue := tl (!queue))
    fun is_refnone x = (not o isSome o ! o snd) x
    fun dispatcher () =
      app (update_from_queue o snd) (filter is_refnone lin)
    (* output *)
    val lout = List.tabulate (ncores,(fn x => (x, ref [])))
    val dout = dnew Int.compare lout
    val lcount = List.tabulate (ncores,(fn x => (x, ref 0)))
    val dcount = dnew Int.compare lcount
    (* process *)
    fun process pi =
      if !end_flag then () else
      let val inref = dfind pi din in
        case !inref of
          NONE => process pi
        | SOME (x,xi) =>
          let
            val oldl = dfind pi dout
            val oldn = dfind pi dcount
            val y = capture forg x
          in
            oldl := (y,xi) :: (!oldl);
            incr oldn;
            inref := NONE;
            process pi
          end
      end
    fun fork_on pi = Thread.fork (fn () => process pi, attrib)
    val threadl = map fork_on (List.tabulate (ncores,I))
    fun loop () =
      (
      dispatcher ();
      if null (!queue) andalso sum_int (map (! o snd) lcount) >= sizeorg
      then end_flag := true
      else loop ()
      )
    fun wait_close () =
      if exists Thread.isActive threadl then wait_close () else ()
    fun compare_imin (a,b) = Int.compare (snd a, snd b)
  in
    loop ();
    wait_close ();
    map fst (dict_sort compare_imin (List.concat (map (! o snd) lout)))
  end

fun parmap_queue ncores f l =
  if ncores = 1 andalso not (!use_thread_flag)
  then map f l
  else map release (parmap_queue_err ncores f l)

fun parapp_queue ncores f l = ignore (parmap_queue ncores f l)

(* -------------------------------------------------------------------------
   Specification of the external parmap
   ------------------------------------------------------------------------- *)

type ('a,'b,'c) extspec =
  {
  self: string,
  parallel_dir : string,
  reflect_globals : unit -> string,
  function : 'a -> 'b -> 'c,
  write_param : string -> 'a -> unit,
  read_param : string -> 'a,
  write_arg : string -> 'b -> unit,
  read_arg : string -> 'b,
  write_result : string ->'c -> unit,
  read_result : string -> 'c
  }

(* -------------------------------------------------------------------------
   Directories as channels
   ------------------------------------------------------------------------- *)

fun mini_sleep () = OS.Process.sleep (Time.fromReal 0.01)

val default_parallel_dir = HOLDIR ^ "/src/AI/sml_inspection/parallel"
fun wid_dir pd wid = pd ^ "/" ^ its wid
fun widin_file pd wid = wid_dir pd wid ^ "/in"
fun widarg_file pd wid = wid_dir pd wid ^ "/arg"
fun widout_file pd wid = wid_dir pd wid ^ "/out"
fun widscript_file pd wid = wid_dir pd wid ^ "/script" ^ its wid ^ ".sml"
fun param_file pd = pd ^ "/param"
fun result_file pd wid = wid_dir pd wid ^ "/result"

(* -------------------------------------------------------------------------
   Worker
   ------------------------------------------------------------------------- *)

fun worker_listen pd wid f =
  if exists_file (widin_file pd wid) then
    let val s = hd (readl_rm (widin_file pd wid)) in
      if s = "stop" then () else
        (f (); worker_listen pd wid f)
    end
  else (mini_sleep (); worker_listen pd wid f)

(* -------------------------------------------------------------------------
   Closing workers and gathering results
   ------------------------------------------------------------------------- *)

fun boss_stop_workers pd threadl =
  let
    val ncore = length threadl
    val _ = print_endline ("stop " ^ its ncore ^ " workers")
    fun send_stop wid = writel_atomic (widin_file pd wid) ["stop"]
    fun loop threadl =
      (if exists Thread.isActive threadl
       then (mini_sleep (); loop threadl)
       else ())
  in
    app send_stop (List.tabulate (ncore,I));
    loop threadl;
    print_endline ("  " ^ its ncore ^ " workers stopped")
  end

fun boss_end pd threadl completedl =
  let
    val ncore = length threadl
    val _ = boss_stop_workers pd threadl
    val l = dict_sort compare_imin (map swap completedl)
  in
    map fst l
  end

(* -------------------------------------------------------------------------
   Boss sends workers jobs and collects the results
   ------------------------------------------------------------------------- *)

fun stat_jobs (pendingl,freewidl,runningl,completedl) =
  print_endline
    ("target: " ^ its (length pendingl) ^ " "  ^
       its (length runningl) ^ " " ^ its (length completedl) ^
     " free core: " ^ String.concatWith " " (map its freewidl))

fun send_job pd arglv warg (wid,job) =
  (
  print_endline ("  send job " ^ its job ^ " to worker " ^ its wid);
  warg (widarg_file pd wid) (Vector.sub (arglv,job));
  writel_atomic (widin_file pd wid) [its job]
  )

fun boss_send pd threadl rr arglv warg (pendingl,runningl,completedl) =
  let
    fun is_running x = mem x (map fst runningl)
    val widl = List.tabulate (length threadl,I)
    val freewidl = filter (not o is_running) widl
    val _ = stat_jobs (pendingl,freewidl,runningl,completedl)
    val njob = Int.min (length freewidl, length pendingl)
    val (jobl,pendingl_new) = part_n njob pendingl
    val runningl_new = combine (first_n njob freewidl, jobl)
  in
    app (send_job pd arglv warg) runningl_new;
    boss_collect pd threadl rr arglv warg
      (pendingl_new, runningl_new @ runningl, completedl)
  end

and boss_collect pd threadl rr arglv warg (pendingl,runningl,completedl) =
  if null pendingl andalso null runningl
    then boss_end pd threadl completedl
  else
  let
    fun f (wid,job) =
      if not (exists_file (widout_file pd wid)) then NONE else
      (
      print_endline ("  completed job " ^ its job ^ " by worker " ^ its wid);
      remove_file (widout_file pd wid);
      SOME (rr wid)
      )
    fun forget_wid ((wid,job),ro) = (job, valOf ro)
    val (al,bl) = partition (isSome o snd) (map_assoc f runningl)
    val runningl_new = map fst bl
    val completedl_new = map forget_wid al
    val prc_new = (pendingl,runningl_new,completedl_new @ completedl)
  in
    if null completedl_new orelse null pendingl then
      (mini_sleep (); boss_collect pd threadl rr arglv warg prc_new)
    else boss_send pd threadl rr arglv warg prc_new
  end

(* -------------------------------------------------------------------------
   Starting threads and external calls
   ------------------------------------------------------------------------- *)

fun boss_start_worker pd code_of wid =
  (
  writel (widscript_file pd wid) (code_of wid);
  smlOpen.run_buildheap (wid_dir pd wid) false (widscript_file pd wid)
  )

val attrib = [Thread.InterruptState Thread.InterruptAsynch,
  Thread.EnableBroadcastInterrupt true]

fun boss_wait_upl pd widl =
  let fun is_up wid = hd (readl (widout_file pd wid)) = "up"
                      handle Io _ => false
  in
    if all is_up widl
    then app (remove_file o (widout_file pd)) widl
    else (mini_sleep (); boss_wait_upl pd widl)
  end

fun clean_parallel_dirs pd widl =
  let fun f wid =
    (mkDir_err (wid_dir pd wid);
     app remove_file [widin_file pd wid, widout_file pd wid])
  in
    mkDir_err pd; app f widl
  end

fun worker_start wid es =
  let
    val pd = #parallel_dir es
    val param = #read_param es (param_file pd)
    fun f () =
      let
        val arg = (#read_arg es) (widarg_file pd wid)
        val r = (#function es) param arg
      in
        (#write_result es) (result_file pd wid) r;
        writel_atomic (widout_file pd wid) ["done"]
      end
  in
    writel_atomic (widout_file pd wid) ["up"];
    worker_listen pd wid f
  end

fun code_of_extspec es wid =
  let val s = #self es in
    [
    "open smlParallel;",
    "val _ = " ^ #reflect_globals es () ^ ";",
    "worker_start " ^ its wid ^ " " ^ s ^ ";"
    ]
  end

val attrib = [Thread.InterruptState Thread.InterruptAsynch,
  Thread.EnableBroadcastInterrupt true]

fun parmap_queue_extern ncore es param argl =
  let
    val widl = List.tabulate (ncore,I)
    val pd = #parallel_dir es
    val _ = clean_parallel_dirs pd widl
    val _ = print_endline "writing parameters"
    val _ = #write_param es (param_file pd) param
    val warg = #write_arg es
    fun rr wid = #read_result es (result_file pd wid)
    val arglv = Vector.fromList argl
    val pendingl = List.tabulate (Vector.length arglv,I)
    val _ = print_endline ("start " ^ its ncore ^ " workers")
    fun fork wid = Thread.fork (fn () =>
      boss_start_worker pd (code_of_extspec es) wid, attrib)
    val threadl = map fork widl
  in
    boss_wait_upl pd widl;
    print_endline ("  " ^ its ncore ^ " workers started");
    boss_send pd threadl rr arglv warg (pendingl,[],[])
  end

(* -------------------------------------------------------------------------
   Example
   ------------------------------------------------------------------------- *)

val idspec : (unit,int,int) extspec =
  {
  self = "smlParallel.idspec",
  parallel_dir = default_parallel_dir,
  reflect_globals = fn () => "()",
  function = let fun f _ (x:int) = x in f end,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_arg = let fun f file arg = writel file [its arg] in f end,
  read_arg = let fun f file =
     string_to_int (singleton_of_list (readl file)) in f end,
  write_result = let fun f file r = writel file [its r] in f end,
  read_result = let fun f file = string_to_int (hd (readl_rm file)) in f end
  }

(*
load "smlParallel"; open smlParallel;
val l1 = List.tabulate (100,I);
val l2 = parmap_queue_extern 2 idspec () l1;
*)

end
