(* ========================================================================  *)
(* FILE          : smlParallel.sml                                           *)
(* DESCRIPTION   : Internal (shared memory) and external                     *)
(* (starting new buildheap process) parallel calls                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure smlParallel :> smlParallel =
struct

open HolKernel Abbrev boolLib aiLib

val ERR = mk_HOL_ERR "smlParallel"

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

val use_thread_flag = ref false

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
   The function parmap_gen start n threads, and generate a parmap function
   relying on this threads and a function to close this threads.
   This makes repeated calls of parmap f on different lists faster.
   Otherwise it behaves like parmap_batch.
   ------------------------------------------------------------------------- *)

fun parmap_gen ncore =
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

(*
load "smlParallel"; open smlParallel;
load "Profile"; open Profile;

fun add1 x  = 1 + x;
fun test1 () =
  let
    val (parmap_loc, close_threadl) = parmap_gen 2;
    val _ = List.tabulate (1000, fn x => parmap_loc add1 [0,1]);
    val _ = close_threadl ()
  in
    ()
  end
fun test2 () = ignore (List.tabulate (1000, fn _ => parmap_queue 2 I [1,2]));

reset_all ();
profile "test1" test1 ();
profile "test2" test2 ();
results ();
*)
(* -------------------------------------------------------------------------
   To avoid spinning too much.
   Smaller value do not decrease the waiting time.
   ------------------------------------------------------------------------- *)

fun mini_sleep () = OS.Process.sleep (Time.fromReal 0.01)

(* -------------------------------------------------------------------------
   External messages passing through files
   ------------------------------------------------------------------------- *)

val parallel_dir = ref (HOLDIR ^ "/src/AI/sml_inspection/parallel")
fun writel_atomic file sl =
  (writel (file ^ "_temp") sl;
   OS.FileSys.rename {old = file ^ "_temp", new=file})
fun readl_rm file =
  let val sl = readl file in OS.FileSys.remove file; sl end

fun wid_dir wid = (!parallel_dir) ^ "/" ^ its wid
fun widin_file wid = wid_dir wid ^ "/in"
fun widout_file wid = wid_dir wid ^ "/out"
fun widscript_file wid = wid_dir wid ^ "/script" ^ its wid ^ ".sml"

fun result_file (wid,job) = wid_dir wid ^ "/result" ^ its job
fun argl_file () = !parallel_dir ^ "/argl"

(* -------------------------------------------------------------------------
   Each worker has a copy of the list.
   Workers are given the index of element to process in the list.
   ------------------------------------------------------------------------- *)

fun worker_process wid (f,l) job =
  (f (wid,job) (List.nth (l,job)); worker_listen wid (f,l))
and worker_listen wid fl =
  if exists_file (widin_file wid)
  then
    let val s = hd (readl_rm (widin_file wid)) in
      if s = "stop" then () else worker_process wid fl (string_to_int s)
    end
  else (mini_sleep (); worker_listen wid fl)

fun worker_start wid fl =
  (writel_atomic (widout_file wid) ["up"]; worker_listen wid fl)

(* -------------------------------------------------------------------------
   Closing workers and gathering results
   ------------------------------------------------------------------------- *)

fun boss_stop_workers threadl =
  let
    val ncore = length threadl
    fun send_stop wid = writel_atomic (widin_file wid) ["stop"]
    fun loop threadl =
      (if exists Thread.isActive threadl
       then (mini_sleep (); loop threadl)
       else ())
  in
    app send_stop (List.tabulate (ncore,I));
    loop threadl
  end

fun boss_end threadl completedl =
  let
    val ncore = length threadl
    val _ = print_endline ("stop " ^ its ncore ^ " workers")
    val _ = boss_stop_workers threadl
    val _ = print_endline ("  " ^ its ncore ^ " workers stopped")
    val l = dict_sort compare_imin (map swap completedl)
    val jobs = String.concatWith " " (map (its o snd) l)
    val _ = print_endline ("  completed jobs: " ^ jobs)
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
  if exists_file (widin_file wid)
  then raise ERR "send_job" ""
  else
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
      SOME (rr (wid,job))
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
   Starting threads and external calls
   ------------------------------------------------------------------------- *)

fun boss_start_worker code_of wid =
  (
  writel (widscript_file wid) (code_of wid);
  smlOpen.run_buildheap false (widscript_file wid);
  remove_file (widscript_file wid)
  )

val attrib = [Thread.InterruptState Thread.InterruptAsynch, Thread.EnableBroadcastInterrupt true]


fun boss_wait_upl widl =
  let fun is_up wid = hd (readl (widout_file wid)) = "up"
                      handle Io _ => false
  in
    if all is_up widl
    then app (remove_file o widout_file) widl
    else (mini_sleep (); boss_wait_upl widl)
  end

fun clean_parallel_dirs widl=
  let fun f wid =
    (mkDir_err (wid_dir wid);
     app remove_file [widin_file wid, widout_file wid])
  in
    mkDir_err (!parallel_dir); app f widl
  end

fun parmap_queue_extern ncore code_of (write_state,write_argl) rr argl =
  let
    val widl = List.tabulate (ncore,I) (* workers *)
    val _ = clean_parallel_dirs widl
    val _ = (write_state (); write_argl argl)
    val _ = print_endline ("start " ^ its ncore ^ " workers")
    fun fork wid = Thread.fork (fn () =>
      boss_start_worker code_of wid, attrib)
    val threadl = map fork widl
    val pendingl = List.tabulate (length argl,I) (* jobs *)
  in
    boss_wait_upl widl;
    print_endline ("  " ^ its ncore ^ " workers started");
    boss_send threadl rr (pendingl,[],[])
  end

fun standard_code_of (s_state,s_argl,s_f) wid =
  [
  "open smlParallel;",
  "val _ = parallel_dir := " ^ quote (!parallel_dir) ^ ";",
  "val state = " ^ s_state ^ ";",
  "val argl = " ^ s_argl ^ ";",
  "fun f (wid,job) arg =",
  "  (" ^ s_f ^ " state (wid,job) arg;",
  "   writel_atomic (widout_file wid) [\"done\"]);",
  "worker_start " ^ (its wid) ^ " (f,argl);"
  ]

(* -------------------------------------------------------------------------
   Example
   ------------------------------------------------------------------------- *)

fun id_parallel ncore argl =
  let
    fun write_state () = ()
    fun write_argl l = writel (argl_file ()) (map its argl)
    fun read_result (wid,job) = 
      string_to_int (hd (readl_rm (result_file (wid,job))))
    val s_state = "()";
    val s_argl = "List.map Lib.string_to_int (aiLib.readl (argl_file ()))";
    val s_f = ("let fun f _ widjob arg = " ^ 
      "aiLib.writel (result_file widjob) [aiLib.its arg] in f end");
    fun code_of wid = standard_code_of (s_state,s_argl,s_f) wid;
  in
    parmap_queue_extern ncore code_of (write_state,write_argl) 
      read_result argl
  end


end
