(* ===================================================================== *)
(* FILE          : hhReconstruct.sml                                     *)
(* DESCRIPTION   : Reconstruct a proof from the lemmas given by an ATP   *)
(*                 and minimize them.                                    *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure hhReconstruct :> hhReconstruct =
struct

open HolKernel Dep Tag boolLib anotherLib smlExecute smlTimeout smlRedirect
  mlDataThm psMinimize

val ERR = mk_HOL_ERR "hhReconstruct"

(* --------------------------------------------------------------------------
   Settings
   -------------------------------------------------------------------------- *)

val reconstruct_flag = ref true
val minimization_timeout = ref 1.0
val reconstruction_timeout = ref 1.0

(* --------------------------------------------------------------------------
   ATP output
   -------------------------------------------------------------------------- *)

fun remove_white_spaces s =
  let fun f c = if Char.isSpace c then "" else Char.toString c in
    String.translate f s
  end

fun not_reserved s = String.isPrefix "thm." s
fun is_dot c = c = #"."

fun read_status atp_status =
  remove_white_spaces (hd (readl atp_status)) 
  handle Interrupt => raise Interrupt
       | _         => "Unknown"

fun read_lemmas atp_out =
  let
    val l = filter not_reserved (map unescape (readl atp_out))
    fun f s = String.concatWith "." (tl (butlast (String.fields is_dot s)))
  in
    mk_string_set (map f l)
  end

fun get_lemmas (atp_status,atp_out) =
  if read_status atp_status = "Theorem"
  then SOME (read_lemmas atp_out)
  else NONE

(*----------------------------------------------------------------------------
   Minimization and pretty-printing
 -----------------------------------------------------------------------------*)

fun hh_reconstruct lemmas g =
  if not (!reconstruct_flag) 
  then (print_endline (mk_metis_call lemmas); 
        raise ERR "hh_minimize" "reconstruction off")
  else
    let
      val stac = mk_metis_call lemmas
      val t1 = !minimization_timeout
      val t2 = !reconstruction_timeout
      val newstac = hide_out (psMinimize.minimize_stac t1 stac g) []
      val tac = hide_out tactic_of_sml newstac
    in
      case hide_out (timeout_tactic t2 tac) g of
        SOME _ => (newstac,tac)
      | NONE   => raise ERR "hh_reconstruct" "reconstruction failed"
    end

end
