
(*
load "tttUnfold";
open tttUnfold;
aiLib.debug_flag := true;
ttt_record ();

ttt_rewrite_thy "ConseqConv";
ttt_record_thy "ConseqConv";



*)
(* =========================================================================
   Evaluation (to move to tttTest)
   ========================================================================= *)
(*
(* Evaluated theorems *)
val ttt_evprove_flag  = ref false
val ttt_evlet_flag    = ref false

val one_in_option = ref NONE
val one_in_counter = ref 0
fun one_in_n () = case !one_in_option of
    NONE => true
  | SOME (offset,freq) =>
    let val b = (!one_in_counter) mod freq = offset in
      (incr one_in_counter; b)
    end

val evaluation_filter = ref (fn s:string => true)

(*
fun debug_eval_status r =
  case r of
    ProofError     => debug "Error: debug_eval_status"
  | ProofSaturated => debug "Proof status: Saturated"
  | ProofTimeOut   => debug "Proof status: Time Out"
  | Proof s        => debug ("Proof found: " ^ s)

fun eval_tactictoe goal =
  (
  mkDir_err ttt_proof_dir;
  report_data ();
  init_tactictoe ();
  debug_eval_status (hide_out main_tactictoe goal)
  )
*)

(* ---------------------------------------------------------------------------
   Evaluation (todo: rewriting should be done first before everything
   in the parallel version)
   -------------------------------------------------------------------------- *)

fun ttt_eval_thy thy =
  (
  ttt_eval_flag := true;
  ttt_rewrite_thy thy;
  ttt_record_thy thy;
  ttt_eval_flag := false
  )

fun ttt_eval_parallel n thyl = parallel_thy ttt_eval_thy n thyl

fun eprover_eval_thy thy =
  (
  eprover_eval_flag := true;
  ttt_record_flag := false;
  ttt_rewrite_thy thy;
  ttt_record_thy thy;
  ttt_record_flag := true
  )

fun parallel_thy f n thyl =
  let
    val thyll = split_thyl n thyl
    fun rec_fork x = Thread.fork (fn () => app f x, [])
    val threadl = map rec_fork thyll
    fun loop () =
      (
      OS.Process.sleep (Time.fromReal 1.0);
      if exists Thread.isActive threadl
      then loop ()
      else print_endline "Parallel call ended"
      )
  in
    loop ()
  end

(* ---------------------------------------------------------------------------
   Split theories in a reasonable manner for parallel calls.
   -------------------------------------------------------------------------- *)

fun split_n_aux i n nl =
  if i >= 0
  then filter (fn x => (fst x) mod n = i) nl :: split_n_aux (i-1) n nl
  else []

fun split_n n l =
  let
    val ll = split_n_aux (n-1) n (number_list 0 l)
  in
    rev (map (map snd) ll)
  end

fun compare_fstint ((a,_),(b,_)) = Int.compare (a,b)

fun split_thyl_aux l2 l1 = case l1 of
    []     => l2
  | a :: newl1 => 
    let 
      val l2' = dict_sort compare_fstint l2
      val (n,l) = hd l2'
      val newl2 = (n + length (DB.thms a), a :: l) :: (tl l2')
    in
      split_thyl_aux newl2 newl1
    end

fun mk_list n a = 
  if n <= 0 then [] else a :: mk_list (n-1) a

fun split_thyl n thyl = 
  if n <= 0 then raise ERR "split_thyl" "" else
  let 
    fun test x = not (mem x ["bool","min"]) 
    val l1  = sort_thyl thyl 
      handle _ => (debug "Warning: split_thyl"; thyl)
    val l1' = filter test l1
    val l2  = mk_list n (0,[])
    val result = split_thyl_aux l2 l1'
  in
    map (rev o snd) result
  end


fun eprover_eval_parallel n thyl = parallel_thy eprover_eval_thy n thyl


  (* evaluation *)
  val ttt_eval_thy: string -> unit
  val eprover_eval_thy: string -> unit
  val ttt_eval_parallel: int -> string list -> unit
  val eprover_eval_parallel: int -> string list -> unit
*)
