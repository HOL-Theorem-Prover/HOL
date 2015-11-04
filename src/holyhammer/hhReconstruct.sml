(* ===================================================================== *)
(* FILE          : hhReconstruct.sml                                     *)
(* DESCRIPTION   : Reconstruct a proof from the lemmas given by an ATP   *)
(*                 and minimize them.                                    *)
(*                 of theorems' names.                                   *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure hhReconstruct :> hhReconstruct =
struct

open HolKernel boolLib Dep Tag hhWriter

val ERR = mk_HOL_ERR "hhReconstruct"

(*---------------------------------------------------------------------------
   Unescaping and extracting theorem and theory name.
 ----------------------------------------------------------------------------*)

fun remove_white_spaces s =
  let
    val cl = String.explode s
    val cl' = filter (not o Char.isSpace) cl
  in
    String.implode cl'
  end

(* Assumes the term was single quoted before *)
fun unsquotify s =
  if String.size s >= 2
  then String.substring (s, 1, String.size s - 2)
  else raise ERR "unsquotify" ""

fun map_half b f l = case l of
    [] => []
  | a :: m => if b then f a :: map_half false f m
              else a :: map_half true f m

fun hh_unescape s =
  let
    val sl = String.fields (fn c => c = #"#") s
    fun f s = case s of
       "hash"   => "#"
      |"slash"  => "/"
      |"quote"  => "\""
      |"squote" => "'"
      | _       => raise ERR "hh_unescape" ""
  in
    String.concat (map_half false f sl)
  end

fun split_name s = case String.fields (fn c => c = #"/") s of
    [_,thy,name] => (thy,name)
  | _       => raise ERR "split_name" ""

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

fun read_status atp_status =
  remove_white_spaces (hd (readl atp_status)) handle _ => "Unknown"

fun read_lemmas atp_out =
  let
    val l = readl atp_out
    val l' = filter (fn x => not (mem x reserved_names_escaped)) l
  in
    map (split_name o hh_unescape o unsquotify) l'
  end

fun atp_lemmas (atp_status,atp_out) =
  let val s = read_status atp_status in
    if s = "Theorem"
    then (s, (read_lemmas atp_out))
    else (s, [])
  end

exception Status of string

fun atp_lemmas_exn (atp_status,atp_out) =
  let val s = read_status atp_status in
    if s = "Theorem"
    then (read_lemmas atp_out)
    else raise Status s
  end

(*---------------------------------------------------------------------------
   Pretty-printing for lemmas.
 ----------------------------------------------------------------------------*)

val ppstrm_stdout =
  PP.mk_ppstream {consumer = fn s => TextIO.output(TextIO.stdOut, s),
                  linewidth = 80,
                  flush = fn () => TextIO.flushOut TextIO.stdOut}

fun pp_lemmas_aux ppstrm lemmas =
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
    fun pp_lemma (thy,name) =
      add_string (String.concatWith " " ["fetch", quote thy, quote name])
  in
    begin_block INCONSISTENT 0;
    add_string "val lemmas = ";
    pp_l pp_lemma lemmas;
    add_string ";";
    end_block();
    flush_ppstream()
  end

fun pp_lemmas lemmas = (pp_lemmas_aux ppstrm_stdout lemmas; print "\n")

(*---------------------------------------------------------------------------
   Timed Metis.
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

fun minimize_lemmas_loop l1 l2 cj =
  if null l2 then l1 else
    if can (time_metis (map snd (l1 @ tl l2)) cj) 2.0
    then minimize_lemmas_loop l1 (tl l2) cj
    else minimize_lemmas_loop (hd l2 :: l1) (tl l2) cj

fun minimize_lemmas lemmas cj =
  let val l = map (fn (thy,nm) => ((thy,nm), fetch thy nm)) lemmas in
    if can (time_metis (map snd l) cj) 2.0
    then (
         print "Minimization ...\n";
         pp_lemmas (map fst (minimize_lemmas_loop [] l cj))
         )
    else pp_lemmas lemmas
  end

(*---------------------------------------------------------------------------
   Reconstruction.
 ----------------------------------------------------------------------------*)

fun reconstruct (atp_status,atp_out) cj =
  let val lemmas = atp_lemmas_exn (atp_status,atp_out) in
    if !minimize_flag then minimize_lemmas lemmas cj else pp_lemmas lemmas
  end

fun reconstructl atpfilel cj =
  let
    val lemmasl = map atp_lemmas atpfilel
    val proofl = filter (fn (x,_) => x = "Theorem") lemmasl
  in
   (* If no proof is found, find a not "Unknown" message *)
   if null proofl
   then
     let val s = if all (fn x => x = "Unknown") (map fst lemmasl)
                 then "Unknown"
                 else hd (filter (fn x => x <> "Unknown") (map fst lemmasl))
     in
       raise Status s
     end
   (* else take the one that uses the less lemmas. *)
   else
      let
        fun cmp l1 l2 = length l1 < length l2
        val lemmas = hd (sort cmp (map snd proofl))
      in
        if !minimize_flag then minimize_lemmas lemmas cj else pp_lemmas lemmas
      end
  end


end
