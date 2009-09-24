(*===================================================================== *)
(* FILE          : ConseqConv.sml                                        *)
(* DESCRIPTION   : Infrastructure for 'Consequence Conversions'.         *)
(*		   A ConseqConv is a conversion that turns a term        *)
(*		   t into a theorem of the form "t' ==> t"               *)
(*                                                                       *)
(* AUTHORS       : Thomas Tuerk                                          *)
(* DATE          : July 3, 2008                                          *)
(* ===================================================================== *)


structure ConseqConv :> ConseqConv =
struct

(*
quietdec := true;
*)

open HolKernel Parse boolLib Drule;

(*
quietdec := false;
*)



(*---------------------------------------------------------------------------
 * generalise a variable in an implication of ==>
 *
 *   A |- t1 v ==> t2 v
 * ---------------------------------------------
 *   A |- (!v. t1 v) ==> (!v. t2 v)
 *
 *---------------------------------------------------------------------------*)

fun GEN_IMP v thm =
  let
     val thm1 = GEN v thm;
     val thm2 = HO_MATCH_MP MONO_ALL thm1;
  in
     thm2
  end;

fun LIST_GEN_IMP vL thm =
   foldr (uncurry GEN_IMP) thm vL


(*---------------------------------------------------------------------------
 * Introduces EXISTS on both sides of an implication
 *
 *   A |- t1 v ==> t2 v
 * ---------------------------------------------
 *   A |- (?v. t1 v) ==> (?v. t2 v)
 *
 *---------------------------------------------------------------------------*)
fun EXISTS_INTRO_IMP v thm =
  let
     val thm1 = GEN v thm;
     val thm2 = HO_MATCH_MP boolTheory.MONO_EXISTS thm1;
  in
     thm2
  end;

fun LIST_EXISTS_INTRO_IMP vL thm =
   foldr (uncurry EXISTS_INTRO_IMP) thm vL


(*---------------------------------------------------------------------------
 * REFL for implications
 *
 * REFL_CONSEQ_CONV t = (t ==> t)
 *---------------------------------------------------------------------------*)
fun REFL_CONSEQ_CONV t = DISCH t (ASSUME t);


(*---------------------------------------------------------------------------
 * generalises a thm body and as well the ASSUMPTIONS
 *
 *   A |- body
 * ---------------------------------------------
 *   (!v. A) |- !v. body
 *
 *---------------------------------------------------------------------------*)

fun GEN_ASSUM v thm =
  let
    val assums = filter (fn t => mem v (free_vars t)) (hyp thm);
    val thm2 = foldl (fn (t,thm) => DISCH t thm) thm assums;
    val thm3 = GEN v thm2;
    val thm4 = foldl (fn (_,thm) => UNDISCH (HO_MATCH_MP MONO_ALL thm))
                     thm3 assums;
  in
    thm4
  end




(*Introduces allquantification for all free variables*)
val SPEC_ALL_TAC:tactic = fn (asm,t) =>
let
   val asm_vars = FVL asm empty_tmset;
   val t_vars = FVL [t] empty_tmset;
   val free_vars = HOLset.difference (t_vars,asm_vars);

   val free_varsL = HOLset.listItems free_vars;
in
   ([(asm,list_mk_forall (free_varsL,t))],
    fn thmL => (SPECL free_varsL (hd thmL)))
end;







(*---------------------------------------------------------------------------
 * A normal conversion converts a term t to a theorem of
 * the form t = t'. In contrast a CONSEQ_CONV converts it to
 * a theorem of the form t' ==> t, i.e. it tries to strengthen a boolean expression
 *---------------------------------------------------------------------------*)



(*---------------------------------------------------------------------------
 * Converts a conversion returning theorems of the form
 *    t' ==> t, t = t' or t
 * to a CONSEQ_CONV. Also some checks are performed that the resulting
 * theorem is really of the form t' ==> t with t being the original input
 * and t' not being equal to t
 *---------------------------------------------------------------------------*)

datatype CONSEQ_CONV_direction =
         CONSEQ_CONV_STRENGTHEN_direction
       | CONSEQ_CONV_WEAKEN_direction
       | CONSEQ_CONV_UNKNOWN_direction;


type conseq_conv = term -> thm;
type directed_conseq_conv = CONSEQ_CONV_direction -> conseq_conv;


(*---------------------------------------------------------------------------
 - Test cases
 ----------------------------------------------------------------------------

val t = ``x > 5``;
val thm1 = prove (``x > 6 ==> x > 5``, DECIDE_TAC);
val thm2 = prove (``x > 5 ==> x > 4``, DECIDE_TAC);
val thm3 = prove (``(x > 5) = (x >= 6)``, DECIDE_TAC);
val thm4 = prove (``(x > 5) = (x > 5)``, DECIDE_TAC);



CONSEQ_CONV_WRAPPER___CONVERT_RESULT CONSEQ_CONV_STRENGTHEN_direction thm1 t
CONSEQ_CONV_WRAPPER___CONVERT_RESULT CONSEQ_CONV_WEAKEN_direction thm1 t
CONSEQ_CONV_WRAPPER___CONVERT_RESULT CONSEQ_CONV_UNKNOWN_direction thm1 t

CONSEQ_CONV_WRAPPER___CONVERT_RESULT CONSEQ_CONV_STRENGTHEN_direction thm2 t
CONSEQ_CONV_WRAPPER___CONVERT_RESULT CONSEQ_CONV_WEAKEN_direction thm2 t
CONSEQ_CONV_WRAPPER___CONVERT_RESULT CONSEQ_CONV_UNKNOWN_direction thm2 t

CONSEQ_CONV_WRAPPER___CONVERT_RESULT CONSEQ_CONV_STRENGTHEN_direction thm3 t
CONSEQ_CONV_WRAPPER___CONVERT_RESULT CONSEQ_CONV_WEAKEN_direction thm3 t
CONSEQ_CONV_WRAPPER___CONVERT_RESULT CONSEQ_CONV_UNKNOWN_direction thm3 t

CONSEQ_CONV_WRAPPER___CONVERT_RESULT CONSEQ_CONV_STRENGTHEN_direction thm4 t
CONSEQ_CONV_WRAPPER___CONVERT_RESULT CONSEQ_CONV_WEAKEN_direction thm4 t
CONSEQ_CONV_WRAPPER___CONVERT_RESULT CONSEQ_CONV_UNKNOWN_direction thm4 t


 ----------------------------------------------------------------------------*)

fun CONSEQ_CONV_WRAPPER___CONVERT_RESULT dir thm t =
let
   val thm_term = concl thm;
in
   if (aconv thm_term t) then
      CONSEQ_CONV_WRAPPER___CONVERT_RESULT dir (EQT_INTRO thm) t
   else if (is_imp_only thm_term) then
      let
	 val (t1, t2) = dest_imp thm_term;
	 val _ = if (aconv t1 t2) then raise UNCHANGED else ();

	 val g' = if (aconv t2 t) then CONSEQ_CONV_STRENGTHEN_direction else
                  if (aconv t1 t) then CONSEQ_CONV_WEAKEN_direction else
		  raise UNCHANGED;
         val g'' = if (dir = CONSEQ_CONV_UNKNOWN_direction) then g' else dir;
	 val _ = if not (g' = g'') then raise UNCHANGED else ();
      in
         (g'', thm)
      end
   else if (is_eq thm_term) then
      (dir,
        if ((lhs thm_term = t) andalso not (rhs thm_term = t)) then
           if (dir = CONSEQ_CONV_UNKNOWN_direction) then
              thm
           else if (dir = CONSEQ_CONV_STRENGTHEN_direction) then
              snd (EQ_IMP_RULE thm)
           else
              fst (EQ_IMP_RULE thm)
        else raise UNCHANGED)
   else
      raise UNCHANGED
end;


fun CONSEQ_CONV_WRAPPER conv dir t =
let
   val _ = if (type_of t = bool) then () else raise UNCHANGED;
   val thm = conv dir t;
in
   snd (CONSEQ_CONV_WRAPPER___CONVERT_RESULT dir thm t)
end;


fun CHANGED_CHECK_CONSEQ_CONV conv t =
    let
       val thm = conv t;
       val (t1,t2) = dest_imp (concl thm) handle HOL_ERR _ =>
                     dest_eq (concl thm);
       val _ = if (aconv t1 t2) then raise UNCHANGED else ();
    in
       thm
    end;

fun OPT_CHANGED_CHECK_CONSEQ_CONV opt_conv =
    CHANGED_CHECK_CONSEQ_CONV (fn t =>
       let
           val thm_opt = opt_conv t;
       in
          if (isSome thm_opt) then valOf thm_opt else raise UNCHANGED
       end);


(*like CHANGED_CONV*)
fun QCHANGED_CONSEQ_CONV conv t =
    conv t handle UNCHANGED => raise mk_HOL_ERR "bool" "ConseqConv" "QCHANGED_CONSEQ_CONV"

fun CHANGED_CONSEQ_CONV conv =
    QCHANGED_CONSEQ_CONV (CHANGED_CHECK_CONSEQ_CONV conv)


(*like ORELSEC*)
fun ORELSE_CONSEQ_CONV (c1:conv) c2 t =
    ((c1 t handle HOL_ERR _ => raise UNCHANGED) handle UNCHANGED =>
     (c2 t handle HOL_ERR _ => raise UNCHANGED));


(*like FIRST_CONV*)
fun FIRST_CONSEQ_CONV [] t = raise UNCHANGED
  | FIRST_CONSEQ_CONV ((c1:conv)::L) t =
    ORELSE_CONSEQ_CONV c1 (FIRST_CONSEQ_CONV L) t;




fun CONSEQ_CONV___GET_SIMPLIFIED_TERM thm t =
   if (concl thm = t) then T else
   let
      val (t1,t2) = dest_imp (concl thm) handle HOL_ERR _ =>
                    dest_eq (concl thm);
   in
      if (aconv t1 t) then t2 else t1
   end;


fun CONSEQ_CONV___GET_DIRECTION thm t =
   if (concl thm = t) then CONSEQ_CONV_UNKNOWN_direction else
   if (is_eq (concl thm)) then CONSEQ_CONV_UNKNOWN_direction else
   let
      val (t1,t2) = dest_imp (concl thm);
   in
      if (aconv t1 t) andalso (aconv t2 t) then CONSEQ_CONV_UNKNOWN_direction else
      if (aconv t2 t) then CONSEQ_CONV_STRENGTHEN_direction else
      if (aconv t1 t) then CONSEQ_CONV_WEAKEN_direction else
      raise UNCHANGED
   end;



(*---------------------------------------------------------------------------
 - Test cases
 ----------------------------------------------------------------------------

val t1 = ``x > 5``;
val t2 = ``x > 3``;
val t3 = ``x > 4``;

val thm1 = prove (``x > 5 ==> x > 4``, DECIDE_TAC);
val thm2 = prove (``x > 4 ==> x > 3``, DECIDE_TAC);

val thm3 = prove (``(x > 4) = (x >= 5)``, DECIDE_TAC);
val thm4 = prove (``(x >= 5) = (5 <= x)``, DECIDE_TAC);


val thm1 = prove (``X ==> T``, REWRITE_TAC[]);
val thm2 = prove (``T ==> T``, REWRITE_TAC[]);
val t1 = ``X:bool``

val thm1 =  prove (``(?r:'b. P (z:'a)) <=> P z``, PROVE_TAC[]);
val thm2 =  prove (``P (z:'a) ==> P z``, PROVE_TAC[]);
val t = ``(?r:'b. P (z:'a))``

THEN_CONSEQ_CONV___combine thm1 thm2 t



THEN_CONSEQ_CONV___combine thm1 thm2 t1
THEN_CONSEQ_CONV___combine thm2 thm1 t2

THEN_CONSEQ_CONV___combine thm1 thm3 t1
THEN_CONSEQ_CONV___combine thm3 thm4 t3

 ----------------------------------------------------------------------------*)

fun is_refl_imp t =
let
   val (l1,l2) = dest_imp_only t;
in
  (aconv l1 l2)
end handle HOL_ERR _ => false;

fun is_refl_eq t =
let
   val (l1,l2) = dest_eq t;
in
  (aconv l1 l2)
end handle HOL_ERR _ => false;

fun is_refl_imp_eq t = is_refl_imp t orelse is_refl_eq t;


fun THEN_CONSEQ_CONV___combine thm1 thm2 t =
  if (is_refl_imp_eq (concl thm1)) then thm2
  else if (is_refl_imp_eq (concl thm2)) then thm1
  else if (concl thm1 = t) then THEN_CONSEQ_CONV___combine (EQT_INTRO thm1) thm2 t
  else if (is_eq (concl thm1)) andalso (rhs (concl thm1) = (concl thm2)) then
     THEN_CONSEQ_CONV___combine thm1 (EQT_INTRO thm2) t
  else if (is_eq (concl thm1)) andalso (is_eq (concl thm2)) then
     TRANS thm1 thm2
  else
     let
        val d1 = CONSEQ_CONV___GET_DIRECTION thm1 t;
        val t2 = CONSEQ_CONV___GET_SIMPLIFIED_TERM thm1 t;
        val d2 = if not (d1 = CONSEQ_CONV_UNKNOWN_direction) then d1 else
		 CONSEQ_CONV___GET_DIRECTION thm2 t2;

        val thm1_imp = snd (CONSEQ_CONV_WRAPPER___CONVERT_RESULT d2 thm1 t)
                       handle UNCHANGED => REFL_CONSEQ_CONV t;
        val thm2_imp = snd (CONSEQ_CONV_WRAPPER___CONVERT_RESULT d2 thm2 t2)
                       handle UNCHANGED => REFL_CONSEQ_CONV t2;
     in
        if (d2 = CONSEQ_CONV_STRENGTHEN_direction) then
	    IMP_TRANS thm2_imp thm1_imp
        else
	    IMP_TRANS thm1_imp thm2_imp
     end



(*like THENC*)
fun THEN_CONSEQ_CONV (c1:conv) c2 t =
    let
       val thm0_opt = SOME (c1 t) handle HOL_ERR _ => NONE
                                        | UNCHANGED => NONE

       val t2 = if (isSome thm0_opt) then CONSEQ_CONV___GET_SIMPLIFIED_TERM (valOf thm0_opt) t else t;

       val thm1_opt = SOME (c2 t2) handle HOL_ERR _ => NONE
                                        | UNCHANGED => NONE
    in
       if (isSome thm0_opt) andalso (isSome thm1_opt) then
         THEN_CONSEQ_CONV___combine (valOf thm0_opt) (valOf thm1_opt) t else
       if (isSome thm0_opt) then valOf thm0_opt else
       if (isSome thm1_opt) then valOf thm1_opt else
       raise UNCHANGED
    end;


fun EVERY_CONSEQ_CONV [] t = raise UNCHANGED
  | EVERY_CONSEQ_CONV ((c1:conv)::L) t =
    THEN_CONSEQ_CONV c1 (EVERY_CONSEQ_CONV L) t;




fun CONSEQ_CONV___APPLY_CONV_RULE thm t conv =
let
   val r = CONSEQ_CONV___GET_SIMPLIFIED_TERM thm t;
   val r_thm = conv r;
in
   THEN_CONSEQ_CONV___combine thm r_thm t
end;




local
   val forall_eq_thm = prove (``(!s:'a. (P s = Q s)) ==> ((!s. P s) = (!s. Q s))``,
		              STRIP_TAC THEN ASM_REWRITE_TAC[]);

   val exists_eq_thm = prove (``(!s:'a. (P s = Q s)) ==> ((?s. P s) = (?s. Q s))``,
		              STRIP_TAC THEN ASM_REWRITE_TAC[]);

in
   val FORALL_EQ___CONSEQ_CONV = HO_PART_MATCH (snd o dest_imp) forall_eq_thm;
   val EXISTS_EQ___CONSEQ_CONV = HO_PART_MATCH (snd o dest_imp) exists_eq_thm;



   (*Like QUANT_CONV for CONSEQ_CONVS. Explicit versions
     for FORALL and EXISTS are exported, since they have
     to be handeled separately anyhow.*)

   fun FORALL_CONSEQ_CONV conv t =
      let
         val (var, body) = dest_forall t;
         val thm_body = conv body;
         val thm = GEN var thm_body;
         val thm2 = if (is_eq (concl thm_body)) then
			forall_eq_thm
		    else boolTheory.MONO_ALL;
         val thm3 = HO_MATCH_MP thm2 thm;
      in
         thm3
      end;

   fun EXISTS_CONSEQ_CONV conv t =
      let
         val (var, body) = dest_exists t;
         val thm_body = conv body;
         val thm = GEN var thm_body;
         val thm2 = if (is_eq (concl thm_body)) then
		       exists_eq_thm
		    else boolTheory.MONO_EXISTS;
         val thm3 = HO_MATCH_MP thm2 thm;
      in
         thm3
      end;

end








fun QUANT_CONSEQ_CONV conv t =
    if (is_forall t) then
       FORALL_CONSEQ_CONV conv t
    else if (is_exists t) then
       EXISTS_CONSEQ_CONV conv t
    else
       NO_CONV t;


local
   val true_imp = prove (``!t. t ==> T``, REWRITE_TAC[]);
   val false_imp = prove (``!t. F ==> t``, REWRITE_TAC[]);
in

   fun TRUE_CONSEQ_CONV t = SPEC t true_imp;
   fun FALSE_CONSEQ_CONV t = SPEC t false_imp;

   fun TRUE_FALSE_REFL_CONSEQ_CONV CONSEQ_CONV_STRENGTHEN_direction = FALSE_CONSEQ_CONV
     | TRUE_FALSE_REFL_CONSEQ_CONV CONSEQ_CONV_WEAKEN_direction = TRUE_CONSEQ_CONV
     | TRUE_FALSE_REFL_CONSEQ_CONV CONSEQ_CONV_UNKNOWN_direction = REFL
end;



(*Like DEPTH_CONV for CONSEQ_CONVS. The conversion
  may generate theorems containing assumptions. These
  assumptions are propagated to the top level*)


fun CONSEQ_CONV_DIRECTION_NEGATE CONSEQ_CONV_UNKNOWN_direction = CONSEQ_CONV_UNKNOWN_direction
  | CONSEQ_CONV_DIRECTION_NEGATE CONSEQ_CONV_STRENGTHEN_direction = CONSEQ_CONV_WEAKEN_direction
  | CONSEQ_CONV_DIRECTION_NEGATE CONSEQ_CONV_WEAKEN_direction = CONSEQ_CONV_STRENGTHEN_direction;



(******************************************************************************)
(* conseq_conv_congruences are used for moving consequence conversions        *)
(* through boolean terms. They get a system callback and a term.              *)
(*                                                                            *)
(* Given the number of already performed step, a direction and a term t       *)
(* sys n t will return the number of steps it performed and a theorem option. *)
(* If this option is NULL, nothing could be done (and the returned number of  *)
(* steps is 0). Otherwise thm_opt is a theorem of the form                    *)
(* |- t ==> t' or |- t' ==> t                                                 *)
(*                                                                            *)
(* The congruence itself get's a term t and is supposed to return a           *)
(* similar theorem option. Moreover, it has to add up all the steps done by   *)
(* calling sys and return this sum.                                           *)
(******************************************************************************)


type conseq_conv_congruence_syscall = 
   int -> CONSEQ_CONV_direction -> term -> (int * thm option)

type conseq_conv_congruence = 
   conseq_conv_congruence_syscall ->
   CONSEQ_CONV_direction -> term -> (int * thm)


fun conseq_conv_congruence_EXPAND_THM_OPT (thm_opt,t) =
  if isSome thm_opt then valOf thm_opt else REFL_CONSEQ_CONV t


(* 
   val sys:conseq_conv_congruence_syscall =
      fn n => K (K ((n+1), NONE));

   val dir = CONSEQ_CONV_STRENGTHEN_direction
   val t = ``b1 /\ b2``;
CONSEQ_CONV_CONGRUENCE___conj sys dir t

*)

fun CONSEQ_CONV_CONGRUENCE___conj sys dir t =
  let
     (* split t, if it fails, that's OK *)
     val (b1,b2) = dest_conj t;

     (* call recursively on subterms *)
     val (n1, thm1_opt) = sys 0  dir b1; 
     val (n2, thm2_opt) = sys n1 dir b2;
     (* if both calls did not change a thing, then abort *)
     val _ = if (isSome thm1_opt) orelse (isSome thm2_opt) then () else raise UNCHANGED;

     (* if necessary create new trivial theorems of the form "t ==> t" *)
     val thm1 = conseq_conv_congruence_EXPAND_THM_OPT (thm1_opt, b1);        
     val thm2 = conseq_conv_congruence_EXPAND_THM_OPT (thm2_opt, b2);        

     (* create combined theorem *)
     val thm3 = MATCH_MP MONO_AND (CONJ thm1 thm2)
  in
     (n2, thm3)
  end


fun CONSEQ_CONV_CONGRUENCE___disj (sys:conseq_conv_congruence_syscall) dir t =
  let
     val (b1,b2) = dest_disj t;
     val (n1, thm1_opt) = sys 0  dir b1;
     val (n2, thm2_opt) = sys n1 dir b2;
     val _ = if (isSome thm1_opt) orelse (isSome thm2_opt) then () else raise UNCHANGED;

     val thm1 = conseq_conv_congruence_EXPAND_THM_OPT (thm1_opt, b1);        
     val thm2 = conseq_conv_congruence_EXPAND_THM_OPT (thm2_opt, b2);        

     val thm3 = MATCH_MP MONO_OR (CONJ thm1 thm2)
  in
     (n2, thm3)
  end


fun CONSEQ_CONV_CONGRUENCE___imp (sys:conseq_conv_congruence_syscall) dir t =
  let
     val (b1,b2) = dest_imp_only t;
     val (n1, thm1_opt) = sys 0  (CONSEQ_CONV_DIRECTION_NEGATE dir) b1;
     val (n2, thm2_opt) = sys n1 dir b2;
     val _ = if (isSome thm1_opt) orelse (isSome thm2_opt) then () else raise UNCHANGED;

     val thm1 = conseq_conv_congruence_EXPAND_THM_OPT (thm1_opt, b1);        
     val thm2 = conseq_conv_congruence_EXPAND_THM_OPT (thm2_opt, b2);        

     val thm3 = MATCH_MP MONO_IMP (CONJ thm1 thm2)
  in
     (n2, thm3)
  end;


fun CONSEQ_CONV_CONGRUENCE___neg (sys:conseq_conv_congruence_syscall) dir t =
  let
     val b1 = dest_neg t;
     val (n1, thm1_opt) = sys 0  (CONSEQ_CONV_DIRECTION_NEGATE dir) b1;
     val _ = if (isSome thm1_opt) then () else raise UNCHANGED;

     val thm2 = MATCH_MP MONO_NOT (valOf thm1_opt)
  in
     (n1, thm2)
  end


fun CONSEQ_CONV_CONGRUENCE___forall (sys:conseq_conv_congruence_syscall) dir t =
  let
     val (v, b1) = dest_forall t;
     val (n1, thm1_opt) = sys 0 dir b1;
     val _ = if (isSome thm1_opt) then () else raise UNCHANGED;

     val thm2 = HO_MATCH_MP MONO_ALL (GEN_ASSUM v (valOf thm1_opt))
  in
     (n1, thm2)
  end



fun CONSEQ_CONV_CONGRUENCE___exists (sys:conseq_conv_congruence_syscall) dir t =
  let
     val (v, b1) = dest_exists t;
     val (n1, thm1_opt) = sys 0 dir b1;
     val _ = if (isSome thm1_opt) then () else raise UNCHANGED;

     val thm2 =HO_MATCH_MP boolTheory.MONO_EXISTS (GEN_ASSUM v (valOf thm1_opt))
  in
     (n1, thm2)
  end



val CONSEQ_CONV_CONGRUENCE___basic_list = [
   CONSEQ_CONV_CONGRUENCE___conj,
   CONSEQ_CONV_CONGRUENCE___disj,
   CONSEQ_CONV_CONGRUENCE___neg,
   CONSEQ_CONV_CONGRUENCE___imp,
   CONSEQ_CONV_CONGRUENCE___forall,
   CONSEQ_CONV_CONGRUENCE___exists]




fun step_opt_sub NONE n = NONE
  | step_opt_sub (SOME m) n = SOME (m - n)

fun step_opt_done NONE n = false
  | step_opt_done (SOME m) n = (m <= n);

(*
   some test data for debugging 

val congruence_list = CONSEQ_CONV_CONGRUENCE___basic_list

fun my_conv t = 
   if (aconv t ``xxx:bool``) then
      mk_thm ([], ``xxx /\ xxx ==> xxx``)
   else
      Feedback.fail()

val step_opt = SOME 2;
val redepth = true
val conv = (K my_conv)

val t = ``xxx:bool``
val n = 0
val dir = CONSEQ_CONV_STRENGTHEN_direction

*)

fun DEPTH_CONSEQ_CONV_num congruence_list n step_opt dir redepth convL t =
  if (dir = CONSEQ_CONV_UNKNOWN_direction) then 
       Feedback.failwith "DEPTH_CONSEQ_CONV does not support CONSEQ_CONV_UNKNOWN_direction!" else 
  if (step_opt_done step_opt n) then (n, NONE) else
  let
     (*define the call back and the recursive call*)
     fun sys m dir t =
        (DEPTH_CONSEQ_CONV_num congruence_list m
           (step_opt_sub step_opt n) dir redepth convL t) 
        handle UNCHANGED => (0, NONE)
             | HOL_ERR _ => (0, NONE);

     fun rec_call n thm = if (not redepth) then (n, SOME thm) else
         let
            val t2 = CONSEQ_CONV___GET_SIMPLIFIED_TERM thm t
            val (n2, thm2_opt) = sys n dir t2
            val _ = if (isSome thm2_opt) then () else raise UNCHANGED;
             
            val thm3 = THEN_CONSEQ_CONV___combine thm (valOf thm2_opt) t;
        in
           (n+n2, SOME thm3)
        end handle UNCHANGED => (n, SOME thm)
                 | HOL_ERR _ => (n, SOME thm)

     (*put all the congruences in a list and the main conversion at first pos*)
     fun conv_trans c dir t = 
        (1, CONSEQ_CONV_WRAPPER c dir t)
     val fL = (map conv_trans convL)@(map (fn c => c sys) congruence_list)

     fun check_fun f =
       let
          val (n2, thm) = f dir t handle UNCHANGED => Feedback.fail();
       in
          (n+n2, thm)
       end;

     val (n3, thm) = tryfind check_fun fL;
     val (n4, thm_opt2) = rec_call n3 thm
  in
    (n4, thm_opt2)
  end handle HOL_ERR _ => (n, NONE);



fun EXT_DEPTH_CONSEQ_CONV congruence_list step_opt redepth convL dir =
 OPT_CHANGED_CHECK_CONSEQ_CONV (fn t =>
   if (type_of t = bool) then
      (snd (DEPTH_CONSEQ_CONV_num congruence_list 0 step_opt dir redepth convL t))
   else raise UNCHANGED);


fun DEPTH_CONSEQ_CONV conv =
  EXT_DEPTH_CONSEQ_CONV CONSEQ_CONV_CONGRUENCE___basic_list NONE false [conv]


fun REDEPTH_CONSEQ_CONV conv =
  EXT_DEPTH_CONSEQ_CONV CONSEQ_CONV_CONGRUENCE___basic_list NONE true [conv]

fun NUM_DEPTH_CONSEQ_CONV conv n =
  EXT_DEPTH_CONSEQ_CONV CONSEQ_CONV_CONGRUENCE___basic_list (SOME n) false [conv]

fun NUM_REDEPTH_CONSEQ_CONV conv n =
  EXT_DEPTH_CONSEQ_CONV CONSEQ_CONV_CONGRUENCE___basic_list (SOME n) true [conv]

fun ONCE_DEPTH_CONSEQ_CONV conv = NUM_DEPTH_CONSEQ_CONV conv 1


(*A tactic that strengthens a boolean goal*)
fun CONSEQ_CONV_TAC conv (asm,t) =
    ((HO_MATCH_MP_TAC ((CHANGED_CONSEQ_CONV (conv CONSEQ_CONV_STRENGTHEN_direction)) t)
     THEN TRY (ACCEPT_TAC TRUTH)) (asm,t) handle UNCHANGED =>
     ALL_TAC (asm,t))

fun DEPTH_CONSEQ_CONV_TAC conv =
    CONSEQ_CONV_TAC (DEPTH_CONSEQ_CONV conv)

fun REDEPTH_CONSEQ_CONV_TAC conv =
    CONSEQ_CONV_TAC (REDEPTH_CONSEQ_CONV conv)

fun ONCE_DEPTH_CONSEQ_CONV_TAC conv =
    CONSEQ_CONV_TAC (ONCE_DEPTH_CONSEQ_CONV conv)



fun STRENGTHEN_CONSEQ_CONV conv dir =
    if dir = CONSEQ_CONV_WEAKEN_direction then raise UNCHANGED else conv;

fun WEAKEN_CONSEQ_CONV conv dir =
    if dir = CONSEQ_CONV_STRENGTHEN_direction then raise UNCHANGED else conv;






fun DEPTH_STRENGTHEN_CONSEQ_CONV conv =
    DEPTH_CONSEQ_CONV (K conv) CONSEQ_CONV_STRENGTHEN_direction;


fun REDEPTH_STRENGTHEN_CONSEQ_CONV conv =
    REDEPTH_CONSEQ_CONV (K conv) CONSEQ_CONV_STRENGTHEN_direction;







(*---------------------------------------------------------------------------
 * if conv ``A`` = |- (A' ==> A) then
 * STRENGTHEN_CONSEQ_CONV_RULE ``(A ==> B)`` = |- (A' ==> B)
 *---------------------------------------------------------------------------*)

fun STRENGTHEN_CONSEQ_CONV_RULE conv thm = let
   val (imp_term,_) = dest_imp (concl thm);
   val imp_thm = conv CONSEQ_CONV_STRENGTHEN_direction imp_term;
  in
   IMP_TRANS imp_thm thm
  end




(*---------------------------------------------------------------------------
 * if conv ``A`` = |- (A' ==> A) then
 * WEAKEN_CONSEQ_CONV_RULE ``(A ==> B)`` = |- (A' ==> B)
 *---------------------------------------------------------------------------*)

fun WEAKEN_CONSEQ_CONV_RULE conv thm = let
   val (_, imp_term) = dest_imp (concl thm);
   val imp_thm = conv CONSEQ_CONV_WEAKEN_direction imp_term;
  in
   IMP_TRANS thm imp_thm
  end












(*---------------------------------------------------------------------------
 * A kind of REWRITE conversion for implications.
 *
 * CONSEQ_REWR_CONV thm takes thms of either the form
 * "|- a ==> c", "|- c = a" or "|- c"
 *
 * c is handled exactly as "c = T"
 *
 * If the thm is an equation, a "normal" rewrite is attempted. Otherwise,
 * CONDSEQ_REWR_CONV tries to match c or a with the input t and then returns a theorem
 * "|- (instantiated a) ==> t" or "|- t ==> (instantiated c)". Which ones happens
 * depends on the value of strengten.
 *---------------------------------------------------------------------------*)

fun CONSEQ_REWR_CONV___with_match ho strengten thm =
  if (is_imp_only (concl thm)) then
     ((if ho then HO_PART_MATCH else PART_MATCH) ((if strengten then snd else fst) o dest_imp) thm,
      ((if strengten then snd else fst) o dest_imp o concl) thm)
  else
     if (is_eq (concl thm)) then
        (PART_MATCH lhs thm,
         (lhs o concl) thm)
     else
        (EQT_INTRO o PART_MATCH I thm,
	 concl thm)


fun CONSEQ_REWR_CONV strengten thm =
    fst (CONSEQ_REWR_CONV___with_match false strengten thm);


(*---------------------------------------------------------------------------
 * His one does multiple rewrites, can handle theorems that
 * contain alquantification and multiple conjuncted rewrite rules and
 * goes down into subterms.
 *---------------------------------------------------------------------------*)

fun CONSEQ_TOP_REWRITE_CONV___EQT_EQF_INTRO thm =
   if (is_eq (concl thm) andalso (type_of (lhs (concl thm)) = bool)) then thm else
   if (is_imp (concl thm)) then thm else
   if (is_neg (concl thm)) then EQF_INTRO thm else
   EQT_INTRO thm;

fun IMP_EXISTS_PRECOND_CANON thm =
   let val th = GEN_ALL thm
       val tm = concl th;
       val (avs,bod) = strip_forall tm
       val (ant,conseq) = dest_imp_only bod
       val th1 = SPECL avs (ASSUME tm)
       val th2 = UNDISCH th1
       val evs = filter(fn v => free_in v ant andalso not(free_in v conseq)) avs
       val th3 = itlist SIMPLE_CHOOSE evs (DISCH tm th2)
       val tm3 = Lib.trye hd(hyp th3)
   in MP (DISCH tm (DISCH tm3 (UNDISCH th3))) th end
   handle HOL_ERR _ => thm;


fun IMP_FORALL_CONCLUSION_CANON thm =
   let val th = GEN_ALL thm
       val tm = concl th;
       val (avs,bod) = strip_forall tm
       val (ant,conseq) = dest_imp_only bod
       val th1 = SPECL avs (ASSUME tm)
       val th2 = UNDISCH th1
       val evs = filter(fn v => not(free_in v ant) andalso free_in v conseq) avs
       val th3 = GENL evs th2
       val th4 = DISCH ant th3;
       val th5 = DISCH tm th4;
       val th6 = MP th5 th
   in th6 end
   handle HOL_ERR _ => thm;


fun IMP_QUANT_CANON thm =
   let val th = GEN_ALL thm
       val tm = concl th;
       val (avs,bod) = strip_forall tm
       val (ant,conseq) = dest_imp_only bod
       val th1 = SPECL avs (ASSUME tm)
       val th2 = UNDISCH th1
       val evs = filter(fn v => not(free_in v ant) andalso free_in v conseq) avs
       val evs2 = filter(fn v => free_in v ant andalso not(free_in v conseq)) avs
       val th3 = GENL evs th2
       val th4 = itlist SIMPLE_CHOOSE evs2 (DISCH tm th3)
       val tm4 = Lib.trye hd(hyp th4)

       val th5 = UNDISCH th4;
       val th6 = DISCH tm4 th5;
       val th7 = DISCH tm th6;
       val th8 = MP th7 th
   in th8 end
   handle HOL_ERR _ => thm;




fun CONSEQ_TOP_REWRITE_CONV___PREPARE_STRENGTHEN_THMS thmL =
let
   val thmL1 = map IMP_EXISTS_PRECOND_CANON thmL;
in
   thmL1
end;


fun CONSEQ_TOP_REWRITE_CONV___PREPARE_WEAKEN_THMS thmL =
let
   val thmL1 = map IMP_FORALL_CONCLUSION_CANON thmL;
in
   thmL1
end;

(* val thm0 = prove (``(SUC 1 = 2) = (2 = 2)``, DECIDE_TAC)
   val t = ``X ==> (SUC 1 = 2)``
   val (both_thmL,strengthen_thmL,weaken_thmL) = ([thm0], [], []);
   val ho = false
   val thmL = (append strengthen_thmL both_thmL)
*)
fun CONSEQ_TOP_REWRITE_CONV___ho_opt ho (both_thmL,strengthen_thmL,weaken_thmL) =
   let
     fun prepare_general_thmL thmL =
           let
               val thmL1 = flatten (map BODY_CONJUNCTS thmL);
	       val thmL2 = map (CONV_RULE (TRY_CONV (REDEPTH_CONV LEFT_IMP_EXISTS_CONV))) thmL1;
	       val thmL3 = map (CONV_RULE (REDEPTH_CONV RIGHT_IMP_FORALL_CONV)) thmL2;
	       val thmL4 = map SPEC_ALL thmL3
           in
	       map CONSEQ_TOP_REWRITE_CONV___EQT_EQF_INTRO thmL4
           end;
     val thmL_st = CONSEQ_TOP_REWRITE_CONV___PREPARE_STRENGTHEN_THMS
		       (prepare_general_thmL (append strengthen_thmL both_thmL));
     val thmL_we = CONSEQ_TOP_REWRITE_CONV___PREPARE_WEAKEN_THMS
		       (prepare_general_thmL (append weaken_thmL both_thmL));


     val net_st = foldr (fn ((conv,t),net) => Net.insert (t,conv) net) Net.empty
         (map (CONSEQ_REWR_CONV___with_match ho true) thmL_st);
     val net_we = foldr (fn ((conv,t),net) => Net.insert (t,conv) net) Net.empty
         (map (CONSEQ_REWR_CONV___with_match ho false) thmL_we);
   in
     (fn dir => fn t =>
        let
	  val convL = if (dir = CONSEQ_CONV_STRENGTHEN_direction) then
			  Net.match t net_st
	    	      else if (dir = CONSEQ_CONV_WEAKEN_direction) then
			  Net.match t net_we
                      else
			  append (Net.match t net_st) (Net.match t net_we);

	in
          FIRST_CONSEQ_CONV convL t
	end)
   end;



val CONSEQ_TOP_REWRITE_CONV = CONSEQ_TOP_REWRITE_CONV___ho_opt false;
val CONSEQ_HO_TOP_REWRITE_CONV = CONSEQ_TOP_REWRITE_CONV___ho_opt true;


fun CONSEQ_REWRITE_CONV thmLs dir =
    REDEPTH_CONSEQ_CONV (CONSEQ_TOP_REWRITE_CONV thmLs) dir;

fun CONSEQ_REWRITE_TAC thmLs =
    CONSEQ_CONV_TAC (CONSEQ_REWRITE_CONV thmLs);

fun ONCE_CONSEQ_REWRITE_TAC thmLs =
    ONCE_DEPTH_CONSEQ_CONV_TAC (CONSEQ_TOP_REWRITE_CONV thmLs);

fun CONSEQ_HO_REWRITE_CONV thmLs dir =
   REDEPTH_CONSEQ_CONV (CONSEQ_HO_TOP_REWRITE_CONV thmLs) dir

fun CONSEQ_HO_REWRITE_TAC thmLs =
    CONSEQ_CONV_TAC (CONSEQ_HO_REWRITE_CONV thmLs);

fun ONCE_CONSEQ_HO_REWRITE_TAC thmLs =
    ONCE_DEPTH_CONSEQ_CONV_TAC (CONSEQ_HO_TOP_REWRITE_CONV thmLs)



fun EXT_CONSEQ_REWRITE_CONV___ho_opt ho convL thmL thmLs dir =
   REDEPTH_CONSEQ_CONV (fn dir' => 
      ORELSE_CONSEQ_CONV (CONSEQ_TOP_REWRITE_CONV___ho_opt ho thmLs dir') 
      (FIRST_CONV (map CHANGED_CONV ((REWRITE_CONV thmL)::convL)))) dir;


val EXT_CONSEQ_REWRITE_CONV = EXT_CONSEQ_REWRITE_CONV___ho_opt false;
fun EXT_CONSEQ_REWRITE_TAC convL thmL thmLs =
    CONSEQ_CONV_TAC (EXT_CONSEQ_REWRITE_CONV convL thmL thmLs);

val EXT_CONSEQ_HO_REWRITE_CONV = EXT_CONSEQ_REWRITE_CONV___ho_opt true;
fun EXT_CONSEQ_HO_REWRITE_TAC convL thmL thmLs =
    CONSEQ_CONV_TAC (EXT_CONSEQ_HO_REWRITE_CONV convL thmL thmLs);



(*
fun CONSEQ_SIMP_CONV impThmL ss eqThmL dir =
   DEPTH_CONSEQ_CONV (fn d => ORELSE_CONSEQ_CONV (CONSEQ_TOP_REWRITE_CONV impThmL d)
		                        (SIMP_CONV ss eqThmL)) dir
*)


(*---------------------------------------------------------------------------
 * EXAMPLES

Some theorems about finite maps.

open pred_setTheory;
open finite_mapTheory;

val rewrite_every_thm =
prove (``FEVERY P FEMPTY /\
         ((FEVERY P f /\ P (x,y)) ==>
          FEVERY P (f |+ (x,y)))``,

SIMP_TAC std_ss [FEVERY_DEF, FDOM_FEMPTY,
		 NOT_IN_EMPTY, FAPPLY_FUPDATE_THM,
		 FDOM_FUPDATE, IN_INSERT] THEN
METIS_TAC[]);


val FEXISTS_DEF = Define `!P f. FEXISTS P f = ?x. x IN FDOM f /\ P (x,f ' x)`;

val rewrite_exists_thm =
prove (``(~(FEXISTS P FEMPTY)) /\
         ((FEXISTS P (f |+ (x,y))) ==>
         (FEXISTS P f \/ P (x,y)))
          ``,


SIMP_TAC std_ss [FEXISTS_DEF, FDOM_FEMPTY,
		 NOT_IN_EMPTY, FAPPLY_FUPDATE_THM,
		 FDOM_FUPDATE, IN_INSERT] THEN
METIS_TAC[]);



You can use the FEVERY-theorem to strengthen expressions:

CONSEQ_REWRITE_CONV ([],[rewrite_every_thm],[]) CONSEQ_CONV_STRENGTHEN_direction
   ``FEVERY P (g |+ (3, x) |+ (7,z))``

This should result in:

val it =
    |- (FEVERY P g /\ P (3,x)) /\ P (7,z) ==> FEVERY P (g |+ (3,x) |+ (7,z)) :
  thm


It works in substructures as well

CONSEQ_REWRITE_CONV ([], [rewrite_every_thm],[]) CONSEQ_CONV_STRENGTHEN_direction 
   ``!g. ?x. Q (g, x) /\ FEVERY P (g |+ (3, x) |+ (7,z)) \/ (z = 12)``

> val it =
    |- (!g.
          ?x. Q (g,x) /\ (FEVERY P g /\ P (3,x)) /\ P (7,z) \/ (z = 12)) ==>
       !g. ?x. Q (g,x) /\ FEVERY P (g |+ (3,x) |+ (7,z)) \/ (z = 12) : thm


You can use the FEXISTS-theorem to weaken them:

CONSEQ_REWRITE_CONV ([], [], [rewrite_exists_thm]) CONSEQ_CONV_WEAKEN_direction ``FEXISTS P (g |+ (3, x) |+ (7,z))``

> val it =
    |- FEXISTS P (g |+ (3,x) |+ (7,z)) ==>
       (FEXISTS P g \/ P (3,x)) \/ P (7,z) : thm



Whether to weaken or strengthen subterms is figured out by their position

CONSEQ_REWRITE_CONV ([rewrite_exists_thm,rewrite_every_thm],[],[]) CONSEQ_CONV_WEAKEN_direction
   ``FEVERY P (g |+ (3, x) |+ (7,z)) ==> FEXISTS P (g |+ (3, x) |+ (7,z))``


> val it =
    |- (FEVERY P (g |+ (3,x) |+ (7,z)) ==>
        FEXISTS P (g |+ (3,x) |+ (7,z))) ==>
       (FEVERY P g /\ P (3,x)) /\ P (7,z) ==>
       (FEXISTS P g \/ P (3,x)) \/ P (7,z) : thm
(not a useful theorem, ... :-(()


However, you can mark some theorem for just beeing used for strengthening / or weakening.
The first list contains theorems used for both, then a list of ones used only
for strengthening follows and finally one just for weakening.

*)

end
