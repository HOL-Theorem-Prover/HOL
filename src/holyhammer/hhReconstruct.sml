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

open HolKernel boolLib Dep Tag tttTools tttExec hhWriter

val ERR = mk_HOL_ERR "hhReconstruct"

val reconstruct_flag = ref true

val lemmas_ref = ref NONE
val status_ref = ref false
val rec_ref = ref false

(*---------------------------------------------------------------------------
   Unescaping and extracting theorem and theory name. (OLD)
 ----------------------------------------------------------------------------*)

(* TODO: use String.translate *)
fun remove_white_spaces s =
  let
    val cl = String.explode s
    val cl' = filter (not o Char.isSpace) cl
  in
    String.implode cl'
  end

fun unsquotify s =
  if String.size s >= 2 andalso 
     String.sub (s, 0) = #"'" andalso
     String.sub (s, String.size s - 1) = #"'"
  then String.substring (s, 1, String.size s - 2)
  else raise ERR "unsquotify" "" 

(* Assumes the theorem name was single quoted before
   which always happen except for reserved names *)

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

(* TODO: names of theorems should be standardized with tactictoe convention *)
fun split_name s = case String.fields (fn c => c = #".") s of
    [_,thy,name] => (thy,name)
  | _       => raise ERR "split_name" ""


(*---------------------------------------------------------------------------
   Reading the ATP file.
 ----------------------------------------------------------------------------*)

fun read_status atp_status =
  remove_white_spaces (hd (readl atp_status)) 
  handle _ => "Unknown" (* TODO: reraise Interrupt *)

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

fun not_reserved_new s = String.isPrefix "thm." s

fun is_dot c = (c = #".")

fun get_lemmas (atp_status,atp_out) =
  let
    val s = read_status atp_status 
  in
    if s = "Theorem"
    then (status_ref := true; SOME (read_lemmas atp_out))
    else NONE
  end

(*---------------------------------------------------------------------------
   Reading the ATP file. (NEW)
 ----------------------------------------------------------------------------*)

fun read_lemmas_new atp_out =
  let
    val l1 = readl atp_out
    val l2 = map hhTptp.unescape l1
    val l3 = filter not_reserved_new l2
    fun f s =
      let 
        val sl1 = String.fields is_dot s 
        val sl2 = tl (butlast sl1)
      in
        String.concatWith "." sl2
      end
    val l4 = mk_fast_set String.compare (map f l3)
  in
    map (split_string "Theory.") l4
  end

fun get_lemmas_new (atp_status,atp_out) =
  let val s = read_status atp_status in
    if s = "Theorem"
    then (status_ref := true; SOME (read_lemmas_new atp_out))
    else NONE
  end

(*---------------------------------------------------------------------------
   Minimization and pretty-printing.
   TODO: Timeout is very short and can not be modified yet.
 ----------------------------------------------------------------------------*)

fun string_of_lemma (thy,name) =
  if thy = namespace_tag
    then name
  else if thy = current_theory ()
    then String.concatWith " " ["DB.fetch", quote thy, quote name]
  else thy ^ "Theory." ^ name

fun mk_metiscall lemmas =
  let val l = map string_of_lemma lemmas in
    "metisTools.METIS_TAC [" ^
    String.concatWith " , " l ^ "]"
  end

fun hh_minimize lemmas g =
  if not (!reconstruct_flag) 
  then (print_endline (mk_metiscall lemmas); 
        raise ERR "hh_minimize" "reconstruction off")
  else
    let
      val stac = mk_metiscall lemmas
      val newstac = hide_out (tttMinimize.minimize_stac 1.0 stac g) []
      val tac = hide_out tactic_of_sml newstac
    in
      print_endline newstac;
      case hide_out (app_tac 1.0 tac) g of
        SOME _ => (rec_ref := true; tac)
      | NONE   => raise ERR "hh_minimize" "reconstruction failed"
    end

(*---------------------------------------------------------------------------
   Reconstruction.
 ----------------------------------------------------------------------------*)

fun concat_lemma (a,b) = a ^ "Theory." ^ b
fun concat_lemmas ol = case ol of
    NONE => NONE
  | SOME l => SOME (map concat_lemma l)


fun reconstruct (atp_status,atp_out) g =
  let 
    val _ = lemmas_ref := NONE
    val _ = status_ref := false
    val _ = rec_ref := false
    val olemmas = get_lemmas (atp_status,atp_out) 
    val _ = lemmas_ref := concat_lemmas olemmas
  in
    case olemmas of
      NONE => raise ERR "reconstruct" "holyhammer failed to prove the goal"
    | SOME lemmas => hh_minimize lemmas g
  end
   
fun reconstruct_stac (atp_status,atp_out) g =
  let 
    val olemmas = get_lemmas (atp_status,atp_out) 
  in
    case olemmas of
      NONE => NONE
    | SOME lemmas => SOME (mk_metiscall lemmas)
  end

(*---------------------------------------------------------------------------
   Reconstruction. (NEW)
 ----------------------------------------------------------------------------*)

fun reconstruct_new (atp_status,atp_out) g =
  let 
    val _ = lemmas_ref := NONE
    val _ = status_ref := false
    val _ = rec_ref := false
    val olemmas = get_lemmas_new (atp_status,atp_out) 
    val _ = lemmas_ref := concat_lemmas olemmas
  in
    case olemmas of
      NONE => raise ERR "reconstruct" "holyhammer failed to prove the goal"
    | SOME lemmas => hh_minimize lemmas g
  end


end
