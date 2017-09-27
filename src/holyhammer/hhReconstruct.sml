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

open HolKernel boolLib Dep Tag hhsTools hhWriter

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

(* Assumes the theorem name was single quoted before 
   which always happen except for reserved names *)
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
    val sl = String.fields (fn c => c = #"|") s
    fun f s = 
      let val n = string_to_int s in
        Char.toString (Char.chr n)
      end
  in
    String.concat (map_half false f sl)
  end

fun split_name s = case String.fields (fn c => c = #".") s of
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

(* removing reserverd names: use a similar
   escaping than the holyhammer fof writer *)
fun reserved_escape name =
  let fun is_alphanumeric s =
    let val l = String.explode s in
      all (fn x => Char.isAlphaNum x orelse x = #"_") l
    end
  in
  if is_alphanumeric name andalso Char.isLower (hd (String.explode name))
  then name
  else "'" ^ name ^ "'"
  end

val reserved_names_escaped = map reserved_escape reserved_names

fun read_lemmas atp_out =
  let
    val l = readl atp_out
    val l' = filter (fn x => not (mem x reserved_names_escaped)) l
  in
    map (split_name o hh_unescape o unsquotify) l'
  end

fun get_lemmas (atp_status,atp_out) =
  let val s = read_status atp_status in
    if s = "Theorem"
    then SOME (read_lemmas atp_out)
    else NONE
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
      if thy = current_theory () 
      then add_string 
             (String.concatWith " " ["DB.fetch", quote thy, quote name])
      else add_string (thy ^ "Theory." ^ name)
  in
    begin_block INCONSISTENT 0;
    add_string "val lemmas = ";
    pp_l pp_lemma lemmas;
    add_string ";";
    end_block();
    flush_ppstream()
  end

fun pp_lemmas lemmas = (pp_lemmas_aux ppstrm_stdout lemmas; print "\n")

fun stac_of_lemmas l cj =
  let 
    val g = ([],cj)
    val (gl,_) = metisTools.METIS_TAC (map snd l) g
    fun f (thy,name) =
      if thy = current_theory () 
      then (String.concatWith " " ["DB.fetch", quote thy, quote name])
      else (thy ^ "Theory." ^ name) 
    val stac = 
      "metisTools.METIS_TAC [" ^ String.concatWith ", " (map (f o fst) l) ^ "]"
  in
    hhsMinimize.pretty_stac stac g gl
  end
    
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

fun minimize_lemmas l cj =
  if can (time_metis (map snd l) cj) 2.0
  then (
       print "Minimization...\n";
       let 
         val l1 = minimize_lemmas_loop [] l cj
         val stac = 
           hhsRedirect.hide_in_file (hhsTools.hhs_code_dir ^ "/hh_pretty")
           (stac_of_lemmas l1) cj;
       in
         print_endline stac;  
         metisTools.METIS_TAC (map snd l1)
       end
       )
  else (
       print "Metis could not find a proof in less than 2 seconds. \n";
       pp_lemmas (map fst l);
       FAIL_TAC "holyhammer: minimization"
       )

(*---------------------------------------------------------------------------
   Reconstruction.
 ----------------------------------------------------------------------------*)

fun reconstruct (atp_status,atp_out) cj =
  let val olemmas = get_lemmas (atp_status,atp_out) in
    case olemmas of 
      NONE => (print_endline "holyhammer: time out"; 
               FAIL_TAC "holyhammer: time out")
    | SOME lemmas =>
    let
      val l = map (fn (thy,nm) => ((thy,nm), fetch thy nm)) lemmas
    in
      if !minimize_flag 
      then minimize_lemmas l cj
      else (pp_lemmas lemmas; metisTools.METIS_TAC (map snd l))
    end
  end

fun string_of_lemma (thy,name) =
  if thy = current_theory () 
  then String.concatWith " " ["DB.fetch", quote thy, quote name]
  else thy ^ "Theory." ^ name

fun reconstruct_stac (atp_status,atp_out) cj =
  let val olemmas = get_lemmas (atp_status,atp_out) in
    case olemmas of 
      NONE => NONE
    | SOME lemmas =>
    let val l = map string_of_lemma lemmas in
      SOME ("metisTools.METIS_TAC [" ^ String.concatWith ", " l ^ "]")
    end
  end  

end
