(* ===================================================================== *)
(* FILE          : hhReconstruct.sml                                     *)
(* DESCRIPTION   : Reconstruct a proof from the lemmas given by an ATP   *)
(*                 and minimize them. Can only be used after a call of   *)
(*                 write_hh_thyl that initializes the dictionary         *)
(*                 of theorems' names.                                   *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure hhReconstruct :> hhReconstruct =
struct

open HolKernel boolLib Dep Tag hhWriter

val ERR = mk_HOL_ERR "hhReconstruct"

(*---------------------------------------------------------------------------
   Reading the ATP file.
 ----------------------------------------------------------------------------*)

fun readl path =
  let
    val file = TextIO.openIn path
    fun loop file = case TextIO.inputLine file of
        SOME line => line :: loop file
      | NONE => []
    val l1 = loop file
    fun rm_last_char s = String.substring (s,0,String.size s - 1)
    fun is_empty s = s = ""
    val l2 = map rm_last_char l1 (* removing end line *)
    val l3 = filter (not o is_empty) l2
  in
    (TextIO.closeIn file; l3)
  end

fun read_status path = hd (readl path) handle _ => "Unknown"

(*---------------------------------------------------------------------------
   Timed Metis
 ----------------------------------------------------------------------------*)

fun time_metis thml conjecture time =
  let
    val oldlimit = !mlibMetis.limit
    val oldtracelevel = !mlibUseful.trace_level
    val thm =
      (
      metisTools.limit := {time = SOME time, infs = NONE};
      mlibUseful.trace_level := 0;
      metisTools.METIS_PROVE thml conjecture
      )
  in
    (metisTools.limit := oldlimit; mlibUseful.trace_level := oldtracelevel; thm)
  end

(*---------------------------------------------------------------------------
   Minimization. Can be turned off by minimize_flag if it takes too much time.
 ----------------------------------------------------------------------------*)

val minimize_flag = ref true

fun minimize_loop l1 l2 cj =
  if null l2 then l1 else
    if can (time_metis (map snd (l1 @ tl l2)) cj) 2.0
    then minimize_loop l1 (tl l2) cj
    else minimize_loop (hd l2 :: l1) (tl l2) cj

fun minimize l cj =
  (
  print "Minimization ...\n";
  if can (time_metis (map snd l) cj) 2.0
  then minimize_loop [] l cj
  else l
  )

(*---------------------------------------------------------------------------
   Reconstruction and printing (depends on DB.fetch)
 ----------------------------------------------------------------------------*)

exception Status of string

val ppstrm_stdout =
  PP.mk_ppstream {consumer = fn s => TextIO.output(TextIO.stdOut, s),
                  linewidth = 80,
                  flush = fn () => TextIO.flushOut TextIO.stdOut}


fun depid_of_thm thm = depid_of (dep_of (tag thm))
fun has_depid (name,thm) = can depid_of_thm thm

fun pp_lemmas ppstrm lemmas =
  let
    open Portable
    val {add_string,add_break,begin_block,
         end_block,add_newline,flush_ppstream,...} =
        with_ppstream ppstrm
    fun pp_l_aux g L = case L of
        []     => ()
      | [a]    => g a
      | a :: m => (g a; add_string ","; add_break(1,0); pp_l_aux g m)
    fun pp_l f l =
      (begin_block INCONSISTENT 0;
         add_string "[";
         begin_block INCONSISTENT 0;
           pp_l_aux f l;
         end_block();
         add_string "]";
       end_block())
    fun pp_lemma (name,thm) =
      let val (thy,_) = depid_of (dep_of (tag thm)) in
        add_string (String.concatWith " " ["fetch", quote thy, quote name])
      end
  in
    begin_block INCONSISTENT 0;
    add_string "val lemmas = ";
    pp_l pp_lemma lemmas;
    add_string ";";
    end_block();
    flush_ppstream()
  end

fun reprove thml axl cj =
  let
    (* reserved theorems are not required by Metis *)
    val axl1 = filter (fn x => not (mem x reserved_names_escaped)) axl
    val didl = map (fn x => Redblackmap.find (!readhh_names,x)) axl1
    val l1   = map (fn x => ("",x)) thml @ map thm_of_depid didl
    val l2   = if !minimize_flag then minimize l1 cj else l1
    (* hacky way of removing user given theorems *)
    val l3   = filter (fn (name,_) => name <> "") l2
  in
    pp_lemmas ppstrm_stdout l3;
    print "\n";
    ignore (time_metis (map snd l2) cj 30.0)
  end

fun reconstruct thml (atp_status,atp_out) conjecture =
  let val s = read_status atp_status in
    if s = "Theorem"
    then reprove thml (readl atp_out) conjecture
    else raise Status s
  end

fun reconstructl thml atpfilel conjecture =
  let
    fun process (atp_status,atp_out) =
      let val s = read_status atp_status in
        if s = "Theorem" then (s, readl atp_out) else (s, [])
      end
    val processedl = map process atpfilel
    val proofl = filter (fn (x,_) => x = "Theorem") processedl
  in
   (* If no proof is found, *)
   if null proofl
    then
      let
        val status_list = map fst processedl
        val s = if all (fn x => x = "Unknown") status_list
                then "Unknown"
                else hd (filter (fn x => x <> "Unknown") status_list)
      in
        raise Status s
      end
   (* else take the one that use the less lemmas. *)
   else
      let
        fun compare_list l1 l2 = length l1 > length l2
        val axl = hd (sort compare_list (map snd proofl))
      in
        reprove thml axl conjecture
      end
  end


end
