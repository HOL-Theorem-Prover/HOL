(*****************************************************************************)
(* FILE          : sub_and_cond.sml                                          *)
(* DESCRIPTION   : Elimination of subtraction from natural number formulae   *)
(*                 and elimination of conditionals.                          *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 9th April 1992                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 16th February 1993                                        *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 16th November 1995                                        *)
(*****************************************************************************)

structure Sub_and_cond :> Sub_and_cond =
struct
  open Arbint HolKernel Parse boolLib RJBConv Thm_convs Rsyntax;

val COND_ABS       = boolTheory.COND_ABS;
val TOP_DEPTH_CONV = Conv.TOP_DEPTH_CONV;

infix THENC ORELSEC |->;

fun failwith function =
   raise HOL_ERR{origin_structure = "Sub_and_cond",
                 origin_function = function,
                 message = ""};


(*---------------------------------------------------------------------------*)
(* COND_ABS_CONV : conv                                                      *)
(*---------------------------------------------------------------------------*)

fun COND_ABS_CONV tm =
 (let val {Bvar=v,Body=bdy} = dest_abs tm
      val {cond,larm=x,rarm=y} = Rsyntax.dest_cond bdy
      val _ = assert (not o equal Type.bool o type_of) x
      val b = assert (not o Lib.mem v o free_vars) cond
      val xf = mk_abs{Bvar=v,Body=x}
      and yf = mk_abs{Bvar=v,Body=y}
      val th1 = INST_TYPE [alpha |-> type_of v, beta |-> type_of x] COND_ABS
      val th2 = SPECL [b,xf,yf] th1
  in  CONV_RULE (RATOR_CONV (RAND_CONV (ABS_CONV
         (RATOR_CONV (RAND_CONV BETA_CONV) THENC RAND_CONV BETA_CONV) THENC
         ALPHA_CONV v))) th2
  end
 ) handle (HOL_ERR _) => failwith "COND_ABS_CONV";

(*---------------------------------------------------------------------------*)
(* SUB_AND_COND_ELIM_CONV : conv                                             *)
(*                                                                           *)
(* Subtraction cannot be eliminated without eliminating conditionals that    *)
(* enclose the subtraction operator. This function is not as delicate as it  *)
(* could be: it eliminates all conditionals in arithmetic formulae as well   *)
(* as eliminating natural number subtraction.                                *)
(*                                                                           *)
(* Care has to be taken with the conditional lifting theorems because they   *)
(* can loop if they try to move a conditional past another conditional, e.g. *)
(*                                                                           *)
(*    b1 => x | (b2 => y | z)                                                *)
(*                                                                           *)
(* Note also that these theorems are specialised for natural numbers. This   *)
(* prevents them from pulling the conditionals higher up the term than       *)
(* necessary prior to elimination.                                           *)
(*                                                                           *)
(* Also eliminates the predecessor function, PRE.                            *)
(*---------------------------------------------------------------------------*)

val SUB_AND_COND_ELIM_CONV =
 let fun op_of_app tm = op_of_app (rator tm) handle _ => tm
 in
 fn tm =>
 TOP_DEPTH_CONV
  (SUB_NORM_CONV ORELSEC
   COND_EXPAND_CONV ORELSEC
   NUM_COND_RATOR_CONV ORELSEC
   (fn tm => if ((#Name (dest_const (op_of_app tm)) = "COND")
                 handle _ => false)
             then failwith "fail"
             else NUM_COND_RAND_CONV tm) ORELSEC
   COND_ABS_CONV
  )
 tm
 end;

(*---------------------------------------------------------------------------*)
(* COND_ELIM_CONV : conv                                                     *)
(*                                                                           *)
(* This function eliminates all conditionals in a term that it can. If the   *)
(* term is a formula, only an abstraction can prevent the elimination, e.g.: *)
(*                                                                           *)
(*    COND_ELIM_CONV `(\m. (m = 0) => 0 | (m - 1)) (SUC n) = n` --->         *)
(*    |- ((\m. ((m = 0) => 0 | m - 1))(SUC n) = n) =                         *)
(*       ((\m. ((m = 0) => 0 | m - 1))(SUC n) = n)                           *)
(*                                                                           *)
(* Care has to be taken with the conditional lifting theorems because they   *)
(* can loop if they try to move a conditional past another conditional, e.g. *)
(*                                                                           *)
(*    b1 => x | (b2 => y | z)                                                *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

val COND_ELIM_CONV =
 let fun op_of_app tm = op_of_app (rator tm) handle _ => tm
 in
 fn tm =>
 TOP_DEPTH_CONV
  (COND_EXPAND_CONV ORELSEC
   COND_RATOR_CONV ORELSEC
   (fn tm => if ((#Name (dest_const (op_of_app tm)) = "COND")
                 handle HOL_ERR _ => false)
             then failwith "fail"
             else COND_RAND_CONV tm) ORELSEC
   COND_ABS_CONV
  )
 tm
 end;

end
