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
   External parmap
   ------------------------------------------------------------------------- *)

fun mini_sleep () = OS.Process.sleep (Time.fromReal 0.01)

val parallel_dir = ref (HOLDIR ^ "/src/AI/sml_inspection/parallel")
fun wid_dir wid = (!parallel_dir) ^ "/" ^ its wid
fun widin_file wid = wid_dir wid ^ "/in"
fun widout_file wid = wid_dir wid ^ "/out"
fun widscript_file wid = wid_dir wid ^ "/script" ^ its wid ^ ".sml"

fun param_file () = !parallel_dir ^ "/param"
fun argl_file () = !parallel_dir ^ "/argl"
fun result_file wid = wid_dir wid ^ "/result"

fun profile_file wid = wid_dir wid ^ "/profile"

fun write_profile wid =
  (
  writel (profile_file wid) [PolyML.makestring (Profile.results ())]
  )

(* -------------------------------------------------------------------------
   Worker
   ------------------------------------------------------------------------- *)

fun worker_process wid (f,l) job =
  (f wid (List.nth (l,job)); worker_listen wid (f,l))
and worker_listen wid fl =
  if exists_file (widin_file wid) then
    let val s = hd (readl_rm (widin_file wid)) in
      if s = "stop" then () else
        worker_process wid fl (string_to_int s)
    end
  else (mini_sleep (); worker_listen wid fl)

(* -------------------------------------------------------------------------
   Closing workers and gathering results
   ------------------------------------------------------------------------- *)

fun boss_stop_workers threadl =
  let
    val ncore = length threadl
    val _ = print_endline ("stop " ^ its ncore ^ " workers")
    fun send_stop wid = writel_atomic (widin_file wid) ["stop"]
    fun loop threadl =
      (if exists Thread.isActive threadl
       then (mini_sleep (); loop threadl)
       else ())
  in
    app send_stop (List.tabulate (ncore,I));
    loop threadl;
    print_endline ("  " ^ its ncore ^ " workers stopped")
  end

fun boss_end threadl completedl =
  let
    val ncore = length threadl
    val _ = boss_stop_workers threadl
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

fun send_job (wid,job) =
  (
  print_endline ("  send job " ^ its job ^ " to worker " ^ its wid);
  writel_atomic (widin_file wid) [its job]
  )

fun boss_send threadl rr (pendingl,runningl,completedl) =
  let
    fun is_running x = mem x (map fst runningl)
    val widl = List.tabulate (length threadl,I)
    val freewidl = filter (not o is_running) widl
    val _ = stat_jobs (pendingl,freewidl,runningl,completedl)
    val njob = Int.min (length freewidl, length pendingl)
    val (jobl,pendingl_new) = part_n njob pendingl
    val runningl_new = combine (first_n njob freewidl, jobl)
  in
    app send_job runningl_new;
    boss_collect threadl rr
      (pendingl_new, runningl_new @ runningl, completedl)
  end

and boss_collect threadl rr (pendingl,runningl,completedl) =
  if null pendingl andalso null runningl
    then boss_end threadl completedl
  else
  let
    fun f (wid,job) =
      if not (exists_file (widout_file wid)) then NONE else
      (
      print_endline ("  completed job " ^ its job ^ " by worker " ^ its wid);
      remove_file (widout_file wid);
      SOME (rr wid)
      )
    fun forget_wid ((wid,job),ro) = (job, valOf ro)
    val (al,bl) = partition (isSome o snd) (map_assoc f runningl)
    val runningl_new = map fst bl
    val completedl_new = map forget_wid al
    val rrc_new = (pendingl,runningl_new,completedl_new @ completedl)
  in
    if null completedl_new orelse null pendingl then
      (mini_sleep (); boss_collect threadl rr rrc_new)
    else boss_send threadl rr rrc_new
  end

(* -------------------------------------------------------------------------
   Specification of the external parallel run
   ------------------------------------------------------------------------- *)

type ('a,'b,'c) extspec =
  {
  self: string,
  reflect_globals : unit -> string,
  function : 'a -> 'b -> 'c,
  write_param : string -> 'a -> unit,
  read_param : string -> 'a,
  write_argl : string -> 'b list -> unit,
  read_argl : string -> 'b list,
  write_result : string ->'c -> unit,
  read_result : string -> 'c
  }

(* -------------------------------------------------------------------------
   Starting threads and external calls
   ------------------------------------------------------------------------- *)

fun boss_start_worker code_of wid =
  (
  writel (widscript_file wid) (code_of wid);
  smlOpen.run_buildheap false 
    (SOME (widscript_file wid ^ ".out")) (widscript_file wid);
  remove_file (widscript_file wid);
  remove_file (widscript_file wid ^ ".out")
  )

val attrib = [Thread.InterruptState Thread.InterruptAsynch,
  Thread.EnableBroadcastInterrupt true]

fun boss_wait_upl widl =
  let fun is_up wid = hd (readl (widout_file wid)) = "up"
                      handle Io _ => false
  in
    if all is_up widl
    then app (remove_file o widout_file) widl
    else (mini_sleep (); boss_wait_upl widl)
  end

fun clean_parallel_dirs widl =
  let fun f wid =
    (mkDir_err (wid_dir wid);
     app remove_file [widin_file wid, widout_file wid])
  in
    mkDir_err (!parallel_dir); app f widl
  end

fun worker_start wid (extspec: ('a,'b,'c) extspec) =
  let
    val param = #read_param extspec (param_file ())
    val argl = #read_argl extspec (argl_file ())
    fun f wid arg =
      let val r = #function extspec param arg in
        #write_result extspec (result_file wid) r;
        writel_atomic (widout_file wid) ["done"]
      end
  in
    writel_atomic (widout_file wid) ["up"];
    worker_listen wid (f,argl)
  end

fun code_of_extspec extspec wid =
  let val s = #self extspec in
    [
    "open smlParallel;",
    "val _ = parallel_dir := " ^ quote (!parallel_dir) ^ ";",
    "val _ = " ^ #reflect_globals extspec () ^ ";",
    "worker_start " ^ its wid ^ " " ^ s ^ ";"
    ]
  end

val attrib = [Thread.InterruptState Thread.InterruptAsynch,
  Thread.EnableBroadcastInterrupt true]

fun parmap_queue_extern ncore extspec param argl =
  let
    val widl = List.tabulate (ncore,I)
    val _ = clean_parallel_dirs widl
    val _ = #write_param extspec (param_file ()) param
    val _ = #write_argl extspec (argl_file ()) argl
    val _ = print_endline ("start " ^ its ncore ^ " workers")
    fun fork wid = Thread.fork (fn () =>
      boss_start_worker (code_of_extspec extspec) wid, attrib)
    val threadl = map fork widl
    val pendingl = List.tabulate (length argl,I)
    fun rr wid = #read_result extspec (result_file wid)
  in
    boss_wait_upl widl;
    print_endline ("  " ^ its ncore ^ " workers started");
    boss_send threadl rr (pendingl,[],[])
  end

(* -------------------------------------------------------------------------
   Example
   ------------------------------------------------------------------------- *)

val idspec : (unit,int,int) extspec =
  {
  self = "smlParallel.idspec",
  reflect_globals = fn () => "()",
  function = let fun f _ (x:int) = x in f end,
  write_param = let fun f _ () = () in f end,
  read_param = let fun f _ = () in f end,
  write_argl = let fun f file argl = writel file (map its argl) in f end,
  read_argl = let fun f file = map string_to_int (readl file) in f end,
  write_result = let fun f file r = writel file [its r] in f end,
  read_result = let fun f file = string_to_int (hd (readl_rm file)) in f end
  }

(*
load "smlParallel"; open smlParallel;
val l1 = List.tabulate (100,I);
val l2 = parmap_queue_extern 2 idspec () l1;
*)

end
