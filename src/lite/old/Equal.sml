(* ===================================================================== 
* FILE          : $Id$
* Basic equality reasoning including conversionals. 
* ===================================================================== *)


structure Equal :> Equal =
struct

open LiteLib HolKernel Drule Conv;
open Psyntax; (* always a good idea to put this last in the "open" sequence. *)

type term  = Term.term
type thm   = Thm.thm
type conv  = Abbrev.conv;


infix 5 |->;

val _ = Lib.say "Developing tools for equality reasoning...";

(* ------------------------------------------------------------------------- 
 * General syntax for binary operators (monomorphic constructor only).       
 *
 * Nb. strip_binop strips only on the right, binops strips both
 * left and right (alal conjuncts and disjuncts).
 * ------------------------------------------------------------------------- *)

type typ = hol_type;
val bool_tycid = "bool";
val fun_tycid = "fun";
	
infixr -->;
val bool_ty = Type.bool
val mk_fun_ty = op -->;
val dest_fun_ty = Type.dom_rng;
val is_fun_ty = Lib.can dest_fun_ty;

fun mk_binop opr (l,r) = 
    list_mk_comb(opr,[l,r])
    handle HOL_ERR _ => failwith "mk_binop"
fun list_mk_binop opr = end_itlist (Lib.curry (mk_binop opr));

fun dest_binop opr tm =
    let val (Rator,rhs) = dest_comb tm
	val (opr',lhs) = dest_comb Rator
    in
	if opr = opr' then (lhs,rhs)
	else fail()
    end
handle HOL_ERR _ => failwith "dest_binop";

fun strip_binop opr =
    let val dest = dest_binop opr
	fun strip tm = 
	    let val (l,r) = dest tm
		val (str,rm) = strip r
	    in (l::str,rm)
	    end
  	    handle HOL_ERR _ => ([],tm)
    in strip
    end;
    
fun binops opr =
    let val dest = dest_binop opr
	fun strip tm = 
	    let val (l,r) = dest tm
	    in (strip l)@(strip r)
	    end
  	    handle HOL_ERR _ => [tm]
    in strip
    end;
fun is_binop opr = Lib.can (dest_binop opr)

val is_imp = is_binop (--`$==>`--);
val dest_imp = dest_binop (--`$==>`--);
val strip_imp = splitlist dest_imp;
    
(* ------------------------------------------------------------------------- *)
(* Grabbing left operand of a binary operator (or something coextensive!)    *)
(* ------------------------------------------------------------------------- *)

val lhand = rand o rator;;

(* ------------------------------------------------------------------------- *)
(* Like mk_comb, but instantiates type variables in rator if necessary.      *)
(* ------------------------------------------------------------------------- *)

fun mk_icomb(tm1,tm2) =
  let val ty = Lib.fst(dest_fun_ty(type_of tm1))
      val tyins = match_type ty (type_of tm2) 
  in mk_comb(inst tyins tm1,tm2)
  end;;

(* ------------------------------------------------------------------------- *)
(* Instantiates types for constant c and iteratively makes combination.      *)
(* ------------------------------------------------------------------------- *)

fun list_mk_icomb tm1 args = rev_itlist (Lib.C (Lib.curry mk_icomb)) args tm1;;



(* ------------------------------------------------------------------------- *)
(* Rule allowing easy instantiation of polymorphic proformas.                *)
(* ------------------------------------------------------------------------- *)

fun PINST tyin tmin =
    let val inst_fn = inst tyin 
(* 	val tmin' = map (fn p => (inst_fn (redex p) |-> (residue p))) tmin *)
 	val tmin' = map (fn (N,u) => (N, inst_fn u)) tmin 
	val iterm_fn = INST tmin'
	and itype_fn = INST_TYPE tyin
    in fn th => iterm_fn (itype_fn th)
	handle HOL_ERR _ => failwith "PINST"
    end;;

(* ------------------------------------------------------------------------- *)
(* Really basic stuff for equality.                                          *)
(* ------------------------------------------------------------------------- *)

fun MK_BINOP oper (lth,rth) = MK_COMB(AP_TERM oper lth,rth);;

(* ------------------------------------------------------------------------- *)
(* Combinators for sequencing, trying, repeating etc. conversions.           *)
(* ------------------------------------------------------------------------- *)

infix THENC;;
fun op THENC (conv1,conv2) t =
    let val th1 = conv1 t 
	val th2 = conv2 (rhs(concl th1)) 
    in TRANS th1 th2
    end;;


infix ORELSEC;;
fun op ORELSEC (conv1,conv2) t =
    conv1 t handle Interrupt => raise Interrupt | _ => conv2 t;;


fun FIRST_CONV l tm = end_foldr (op ORELSEC) l tm
    handle Interrupt => raise Interrupt | _ => failwith "FIRST_CONV";

fun EVERY_CONV l = foldr (op THENC) ALL_CONV l;

fun REPEATC conv t =
    ((conv THENC (REPEATC conv)) ORELSEC ALL_CONV) t;

fun CHANGED_CONV conv tm =
    let val th = conv tm 
	val (l,r) = Psyntax.dest_eq (concl th) 
    in if aconv l r then failwith "CHANGED_CONV" else th 
    end;

fun TRY_CONV conv = conv ORELSEC ALL_CONV;;

(* ------------------------------------------------------------------------- *)
(* Subterm conversions.                                                      *)
(* ------------------------------------------------------------------------- *)

fun RATOR_CONV conv tm =
    let val (l,r) = dest_comb tm in AP_THM (conv l) r end;

fun RAND_CONV conv tm =
    let val (l,r) = dest_comb tm in AP_TERM l (conv r) end;

val LAND_CONV = RATOR_CONV o RAND_CONV;;

fun COMB2_CONV lconv rconv tm = 
    let val (l,r) = dest_comb tm in MK_COMB(lconv l,rconv r) end;;

val COMB_CONV = W COMB2_CONV;;

(* horribly inefficient - could be very efficient now we're in
hol90 with dB terms.  Sigh. DRS *)

(* val vsubst = subst;
   val vfree_in = free_in;
*)

fun alpha v tm =
  let val (v0,bod) = dest_abs tm
               handle HOL_ERR _ => failwith "alpha: Not an abstraction"
  in if (v = v0) then tm else
      if is_var v andalso (type_of v = type_of v0)
	  andalso not (Lib.mem v (free_vars bod))
	  then mk_abs(v,Rsyntax.subst[{redex=v0, residue=v}] bod)
      else failwith "alpha: Invalid new variable"
  end;;


fun ABS_CONV conv tm =
   let val (v,bod) = dest_abs tm
       val th = conv bod 
   in ABS v th
       handle Interrupt => raise Interrupt 
            | _ => 
	   let val gv = genvar(type_of v) 
	       val gbod = Rsyntax.subst[{redex=v,residue=gv}] bod 
	       val th1 = ABS gv (conv gbod) 
	       val tm1 = concl th1 
	       val (l,r) = Psyntax.dest_eq tm1  (* Why Psyntax? *)
	       val v' = variant (Lib.union (free_vars l) (free_vars r)) v 
	       val l' = alpha v' l and r' = alpha v' r 
	       val th2 = ALPHA tm1 (mk_eq(l',r')) 
	   in EQ_MP th2 th1
	   end
   end;;


fun BINDER_CONV conv tm =
  ABS_CONV conv tm
  handle Interrupt => raise Interrupt | _ => RAND_CONV(ABS_CONV conv) tm;;

fun SUB_CONV conv tm = 
    if is_comb tm then (COMB_CONV conv tm) 
    else if is_abs tm then (ABS_CONV conv tm) 
	 else REFL tm;;

fun BINOP_CONV oper conv tm =
    let val (l,r) = dest_binop oper tm 
	val lth = conv l
	and rth = conv r in
	    MK_COMB(AP_TERM oper lth,rth)
    end;;

val BODY_CONV =
    let fun dest_quant tm =
	let val (q,atm) = dest_comb tm 
	    val (v,bod) = dest_abs atm 
	in ((q,v),bod) 
	end
	val strip_quant = splitlist dest_quant 
    in fn conv => fn tm =>
	let val (quants,bod) = strip_quant tm 
	in itlist (fn (q,v) => fn th => AP_TERM q (ABS v th)) quants (conv bod)
	end
    end;;

(* ------------------------------------------------------------------------- *)
(* Faster depth conversions using failure rather than returning a REFL.      *)
(* ------------------------------------------------------------------------- *)

infix THENQC;
fun op THENQC (conv1,conv2) tm =
    let val th1 = conv1 tm in
	let val th2 = conv2(rhs(concl th1)) in TRANS th1 th2 end
    handle Interrupt => raise Interrupt | _ => th1
    end
handle Interrupt => raise Interrupt | _ => conv2 tm;;


infix THENCQC;
fun op THENCQC (conv1,conv2) tm =
  let val th1 = conv1 tm 
  in let val th2 = conv2(rhs(concl th1)) 
     in TRANS th1 th2
     end
 handle Interrupt => raise Interrupt
     | _ => th1
  end


fun REPEATQC conv tm =
   (conv THENCQC (REPEATQC conv)) tm;;

fun COMB2_QCONV conv1 conv2 tm =
  let val (l,r) = dest_comb tm 
  in let val th1 = conv1 l 
     in let val th2 = conv2 r 
	in MK_COMB(th1,th2) 
	end
        handle Interrupt => raise Interrupt
	     | _ => AP_THM th1 r
     end
     handle Interrupt => raise Interrupt 
	  | _ => AP_TERM l (conv2 r)
  end;

val COMB_QCONV = W COMB2_QCONV;;

fun SUB_QCONV conv tm =
  if is_abs tm then ABS_CONV conv tm
  else COMB_QCONV conv tm;;

fun ONCE_DEPTH_QCONV conv tm =
  (conv ORELSEC (SUB_QCONV (ONCE_DEPTH_QCONV conv))) tm;;

fun DEPTH_QCONV conv tm =
   ((SUB_QCONV (DEPTH_QCONV conv)) THENQC
    (REPEATQC conv)) tm;;

fun REDEPTH_QCONV conv tm =
   ((SUB_QCONV (REDEPTH_QCONV conv)) THENQC
    (conv THENCQC (REDEPTH_QCONV conv))) tm;;

fun TOP_DEPTH_QCONV conv tm =
   ((REPEATQC conv) THENQC
    ((SUB_QCONV (TOP_DEPTH_QCONV conv)) THENCQC
     (conv THENCQC (TOP_DEPTH_QCONV conv)))) tm;;

fun TOP_SWEEP_QCONV conv tm =
  ((REPEATQC conv) THENQC
   (SUB_QCONV (TOP_SWEEP_QCONV conv))) tm;;

(* ------------------------------------------------------------------------- *)
(* Standard conversions.                                                     *)
(* ------------------------------------------------------------------------- *)

fun ONCE_DEPTH_CONV c = TRY_CONV (ONCE_DEPTH_QCONV c)
and DEPTH_CONV c = TRY_CONV (DEPTH_QCONV c)
and REDEPTH_CONV c = TRY_CONV (REDEPTH_QCONV c)
and TOP_DEPTH_CONV c = TRY_CONV (TOP_DEPTH_QCONV c)
and TOP_SWEEP_CONV c = TRY_CONV (TOP_SWEEP_QCONV c);;
(* ------------------------------------------------------------------------- *)
(* Apply at leaves of op-tree; NB any failures at leaves cause failure.      *)
(* ------------------------------------------------------------------------- *)

fun DEPTH_BINOP_CONV oper conv tm =
  let exception DEST_BINOP 
      val (l,r) = dest_binop oper tm handle HOL_ERR _ => raise DEST_BINOP
      val lth = DEPTH_BINOP_CONV oper conv l
      and rth = DEPTH_BINOP_CONV oper conv r
  in MK_COMB(AP_TERM oper lth,rth)
  end
  handle DEST_BINOP => conv tm;;


(* ------------------------------------------------------------------------- *)
(* Single bottom-up pass, starting at the topmost success!                   *)
(* ------------------------------------------------------------------------- *)

fun SINGLE_DEPTH_CONV conv tm =
    conv tm
    handle Interrupt => raise Interrupt 
	 | _ => (SUB_CONV (SINGLE_DEPTH_CONV conv) THENC (TRY_CONV conv)) tm;;

(* ------------------------------------------------------------------------- *)
(* Symmetry conversion.                                                      *)
(* ------------------------------------------------------------------------- *)

fun SYM_CONV tm =
    let val th1 = SYM(ASSUME tm) 
	val tm' = concl th1 
	val th2 = SYM(ASSUME tm') 
    in IMP_ANTISYM_RULE (DISCH tm th1) (DISCH tm' th2)
    end
handle Interrupt => raise Interrupt | _ => failwith "SYM_CONV";;

(* ------------------------------------------------------------------------- *)
(* Conversion to a rule.                                                     *)
(* ------------------------------------------------------------------------- *)

fun CONV_RULE conv th =
    EQ_MP (conv(concl th)) th;;

(* ------------------------------------------------------------------------- *)
(* Substitution conversion.                                                  *)
(* ------------------------------------------------------------------------- *)

fun SUBS_CONV ths tm =
  if null ths then REFL tm else
      let val lefts = map (lhs o concl) ths 
	  val gvs = map (genvar o type_of) lefts 
	  val pat = subst (map2 (fn N => fn gv => (gv,N)) lefts gvs) tm 
	  val abs = list_mk_abs(gvs,pat) 
	  fun f y x = CONV_RULE (RAND_CONV BETA_CONV THENC LAND_CONV BETA_CONV)
	      (MK_COMB(x,y))
      in rev_itlist f ths (REFL abs)
	  handle Interrupt => raise Interrupt | _ => failwith "SUBS_CONV"
      end;

(* ------------------------------------------------------------------------- *)
(* Get a few rules.                                                          *)
(* ------------------------------------------------------------------------- *)

val BETA_RULE = CONV_RULE(REDEPTH_CONV BETA_CONV);;

val GSYM = CONV_RULE(ONCE_DEPTH_CONV SYM_CONV);;

fun SUBS ths = CONV_RULE (SUBS_CONV ths);;




(*-----------------------------------------------------------------------*)
(* MK_ABS_CONV - Abstract a term by a variable                           *)
(* MK_ABSL_CONV - Abstract a term by a set of variables                  *)
(*                                                                       *)
(* [DRS 96.01.28]                                                        *)
(*-----------------------------------------------------------------------*)

fun MK_ABS_CONV var tm = 
    if (is_comb tm andalso rand tm = var 
        andalso not (free_in var (rator tm)))
	then REFL tm
    else 
	let val rhs = mk_abs(var,tm)
	    val newrhs = mk_comb(rhs,var)
	in SYM (BETA_CONV newrhs)
	end;
	
fun MK_ABSL_CONV vars tm = 
    let val rhs = list_mk_abs (vars,tm)
	val newrhs = list_mk_comb(rhs,vars)
	val thm1 = foldr (fn (_,conv) => (RATOR_CONV conv) THENC BETA_CONV) ALL_CONV vars newrhs
    in SYM thm1
    end;
       
val RIGHT_BETAS =
  rev_itlist (fn a => CONV_RULE (RAND_CONV BETA_CONV) o Lib.C AP_THM a);;



fun name_of_const tm = Lib.fst (dest_const tm);

val MK_CONJ =
  let val andtm = (--`$/\`--) in
  fn eq1 => fn eq2 => MK_COMB(AP_TERM andtm eq1,eq2)
  end ;;

val MK_DISJ =
  let val ortm = (--`$\/`--) in
  fn eq1 => fn eq2 => MK_COMB(AP_TERM ortm eq1,eq2)
  end;;

val MK_FORALL =
  let val aty = (==`:'a`==) in
  fn v => fn th =>
    let val atm = mk_const("!",(type_of v --> bool_ty) --> bool_ty) in
  AP_TERM atm (ABS v th) end end;;

val MK_EXISTS =
  let val aty = (==`:'a`==) in
  fn v => fn th =>
    let val atm = mk_const("?",(type_of v --> bool_ty) --> bool_ty) in
  AP_TERM atm (ABS v th) end end;;


fun SIMPLE_DISJ_CASES th1 th2 =
  DISJ_CASES (ASSUME(mk_disj(hd(hyp th1),hd(hyp th2)))) th1 th2;;


fun SIMPLE_CHOOSE v th =
  CHOOSE(v,ASSUME (mk_exists(v,hd(hyp th)))) th;;

val _ = Lib.say "done!\n";

end (* struct *)


