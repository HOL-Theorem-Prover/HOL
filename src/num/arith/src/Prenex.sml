(*****************************************************************************)
(* FILE          : prenex.sml                                                *)
(* DESCRIPTION   : Putting formulae in Prenex Normal Form                    *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 19th June 1992                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 16th February 1993                                        *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 16th February 1993                                        *)
(*****************************************************************************)

structure Prenex :> Prenex =
struct
  open HolKernel boolLib Arbint RJBConv;

  infix ORELSEC;


(* Bindings from Conv structure *)

val TOP_DEPTH_CONV = Conv.TOP_DEPTH_CONV;
val EQ_IMP_THM = boolTheory.EQ_IMP_THM;
val NOT_EXISTS_CONV = Conv.NOT_EXISTS_CONV
val NOT_FORALL_CONV = Conv.NOT_FORALL_CONV
val RIGHT_AND_EXISTS_CONV = Conv.RIGHT_AND_EXISTS_CONV
val LEFT_AND_EXISTS_CONV = Conv.LEFT_AND_EXISTS_CONV
val RIGHT_AND_FORALL_CONV = Conv.RIGHT_AND_FORALL_CONV
val LEFT_AND_FORALL_CONV = Conv.LEFT_AND_FORALL_CONV
val AND_EXISTS_CONV = Conv.AND_EXISTS_CONV
val AND_FORALL_CONV = Conv.AND_FORALL_CONV
val LEFT_OR_FORALL_CONV = Conv.LEFT_OR_FORALL_CONV
val RIGHT_OR_FORALL_CONV = Conv.RIGHT_OR_FORALL_CONV
val OR_FORALL_CONV = Conv.OR_FORALL_CONV
val LEFT_OR_EXISTS_CONV = Conv.LEFT_OR_EXISTS_CONV
val RIGHT_OR_EXISTS_CONV = Conv.RIGHT_OR_EXISTS_CONV
val OR_EXISTS_CONV = Conv.OR_EXISTS_CONV
val RIGHT_IMP_FORALL_CONV = Conv.RIGHT_IMP_FORALL_CONV
val LEFT_IMP_FORALL_CONV = Conv.LEFT_IMP_FORALL_CONV
val LEFT_IMP_EXISTS_CONV = Conv.LEFT_IMP_EXISTS_CONV
val RIGHT_IMP_EXISTS_CONV = Conv.RIGHT_IMP_EXISTS_CONV

fun failwith function = raise HOL_ERR{origin_structure = "Prenex",
                                      origin_function = function,
                                      message = ""};

(*---------------------------------------------------------------------------*)
(* QUANT_EQ_IMP_CONV : conv                                                  *)
(*---------------------------------------------------------------------------*)

fun QUANT_EQ_IMP_CONV tm =
 (let val (lhs,rhs) = dest_eq tm
  in  if (is_forall lhs) orelse (is_exists lhs) orelse
         (is_forall rhs) orelse (is_exists rhs)
      then SPECL [lhs,rhs] EQ_IMP_THM
      else failwith "fail"
  end
 ) handle (HOL_ERR _) => failwith "QUANT_EQ_IMP_CONV";

(*---------------------------------------------------------------------------*)
(* is_prenex : term -> bool                                                  *)
(*---------------------------------------------------------------------------*)

fun is_prenex tm =
   let fun contains_quant tm =
          if (is_forall tm) orelse (is_exists tm)
          then true
          else (let val (f,x) = dest_comb tm
                in  (contains_quant f) orelse (contains_quant x)
                end)
               handle _ => (contains_quant (body tm))
               handle _ => false
   in  is_prenex (snd (dest_forall tm)) handle _ =>
       is_prenex (snd (dest_exists tm)) handle _ =>
       not (contains_quant tm)
   end;

(*---------------------------------------------------------------------------*)
(* PRENEX_CONV : conv                                                        *)
(*---------------------------------------------------------------------------*)

fun PRENEX_CONV tm =
 if (is_prenex tm)
 then ALL_CONV tm
 else
 TOP_DEPTH_CONV
  (fn tm =>
   if (is_neg tm) then (NOT_FORALL_CONV ORELSEC NOT_EXISTS_CONV) tm
   else if (is_conj tm) then
      (AND_FORALL_CONV ORELSEC
       LEFT_AND_FORALL_CONV ORELSEC RIGHT_AND_FORALL_CONV ORELSEC
       AND_EXISTS_CONV ORELSEC
       LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV) tm
   else if (is_disj tm) then
      (OR_FORALL_CONV ORELSEC
       LEFT_OR_FORALL_CONV ORELSEC RIGHT_OR_FORALL_CONV ORELSEC
       OR_EXISTS_CONV ORELSEC
       LEFT_OR_EXISTS_CONV ORELSEC RIGHT_OR_EXISTS_CONV) tm
   else if (is_imp tm) then
      (LEFT_IMP_FORALL_CONV ORELSEC RIGHT_IMP_FORALL_CONV ORELSEC
       LEFT_IMP_EXISTS_CONV ORELSEC RIGHT_IMP_EXISTS_CONV) tm
   else if (is_eq tm) then QUANT_EQ_IMP_CONV tm
   else failwith "fail")
 tm;

end
