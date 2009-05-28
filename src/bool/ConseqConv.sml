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


fun CONSEQ_CONV_WRAPPER dir conv t =
let
   val _ = if (type_of t = bool) then () else raise UNCHANGED;
   val thm = conv dir t;   
in
   CONSEQ_CONV_WRAPPER___CONVERT_RESULT dir thm t
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
       val thm0_opt = (SOME (c1 t) handle HOL_ERR _ => raise UNCHANGED) handle UNCHANGED => NONE;

       val t2 = if (isSome thm0_opt) then CONSEQ_CONV___GET_SIMPLIFIED_TERM (valOf thm0_opt) t else t;

       val thm1_opt = (SOME (c2 t2) handle HOL_ERR _ => raise UNCHANGED) handle UNCHANGED => NONE;
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


fun step_opt_sub NONE n = NONE
  | step_opt_sub (SOME m) n = SOME (m - n);


(*---------------------------------------------------------------------------
 - Test cases
 ----------------------------------------------------------------------------

val step_opt = NONE;
val dir = CONSEQ_CONV_UNKNOWN_direction;
val top = false
val conv = K FALSE_CONSEQ_CONV;

val t = ``~Y:bool``;

 ----------------------------------------------------------------------------*)
    
val DEPTH_CONSEQ_CONV_debug = ref 0;
val _ = register_trace("DEPTH_CONSEQ_CONV", DEPTH_CONSEQ_CONV_debug, 3);


fun guarded_say r n tf =
  if (!r >= n) then say (tf ()) else ();


fun prefix_string 0 = ""
  | prefix_string n = " "^(prefix_string (n-1));


fun DEPTH_CONSEQ_CONV_say n l t = guarded_say DEPTH_CONSEQ_CONV_debug n
    (fn () =>
        ((prefix_string (if (!DEPTH_CONSEQ_CONV_debug = 1) then 0 else l))^"DEPTH_CONSEQ_CONV "^(Int.toString n)^": "^(t ())^"\n"));

(*
val tref = ref NONE;
val tref2 = ref NONE;
val (t, t2, thm, thm2) = valOf (!tref)

val (l,step_opt,dir,top,conv,t) = valOf (!tref2)

*)

fun DEPTH_CONSEQ_CONV_num l step_opt dir top redepth conv t = 
  let
     val top_string = if top then "TOP " else "SUB ";
     val _ = DEPTH_CONSEQ_CONV_say 2 l (fn () => ("Trying "^top_string^" ``"^term_to_string t^"``"));

     fun CONVERT_THM_OPT (thm_opt,t) =
         if isSome thm_opt then valOf thm_opt else REFL_CONSEQ_CONV t

     fun DEPTH_CONSEQ_CONV_num___REC_CALL l step_opt dir top redepth conv thm_opt n t =
        ((let
           val t2 = if isSome thm_opt then
                       CONSEQ_CONV___GET_SIMPLIFIED_TERM (valOf thm_opt) t
                    else
		       t;

 	   val (n2, d2, thm2_opt) = DEPTH_CONSEQ_CONV_num l (step_opt_sub step_opt n) dir top redepth conv t2;

           val _ = DEPTH_CONSEQ_CONV_say 4 l (fn () => (
                   if isSome thm2_opt then
                      ("Trying REC ``"^term_to_string t2^
                       "`` results in "^ (thm_to_string (valOf thm2_opt)))
                   else
                      ("Trying REC ``"^term_to_string t2^
                       "`` - UNCHANGED")));
            
           val (m,thm3_opt) = if (aconv t t2) then (n2,thm2_opt) else 
                              if (not (isSome thm2_opt)) then
				  (n, thm_opt)
                              else   
                          	  (n2+n, SOME (THEN_CONSEQ_CONV___combine (valOf thm_opt) (valOf thm2_opt) t));

           val _ = DEPTH_CONSEQ_CONV_say 2 l (fn () => (
                   if isSome thm3_opt then
                       ("Result "^(thm_to_string (valOf thm3_opt)))
                   else
                       "UNCHANGED"));
        in
           (m, d2, thm3_opt)
        end handle HOL_ERR _ => (DEPTH_CONSEQ_CONV_say 2 l (fn () => ("UNCHANGED")); (0, dir, NONE)))
            handle UNCHANGED => (DEPTH_CONSEQ_CONV_say 2 l (fn () => ("UNCHANGED")); (0, dir, NONE)))
  in

  if (step_opt = SOME 0) then
     (0, dir, NONE)
  else if ((not top) andalso is_conj t) then
     let
	 val (b1,b2) = dest_conj t;
         val (n1, d1, thm1_opt) = DEPTH_CONSEQ_CONV_num (l+1) step_opt dir top redepth conv b1;
         val (n2, d2, thm2_opt) = DEPTH_CONSEQ_CONV_num (l+1) (step_opt_sub step_opt n1) d1 top redepth conv b2;
          
	 val thm3_opt = if (isSome thm1_opt) orelse (isSome thm2_opt) then
                          SOME (MATCH_MP MONO_AND (CONJ (CONVERT_THM_OPT (thm1_opt,b1)) (CONVERT_THM_OPT (thm2_opt,b2))))
                        else NONE;
     in
        DEPTH_CONSEQ_CONV_num___REC_CALL l step_opt d2 true redepth conv thm3_opt (n1+n2) t
     end
   else if ((not top) andalso is_disj t) then
     let
	 val (b1,b2) = dest_disj t;
         val (n1, d1, thm1_opt) = DEPTH_CONSEQ_CONV_num (l+1) step_opt dir top redepth conv b1;
         val (n2, d2, thm2_opt) = DEPTH_CONSEQ_CONV_num (l+1) (step_opt_sub step_opt n1) d1 top redepth conv b2;

	 val thm3_opt = if (isSome thm1_opt) orelse (isSome thm2_opt) then
                          SOME (MATCH_MP MONO_OR (CONJ (CONVERT_THM_OPT (thm1_opt,b1)) (CONVERT_THM_OPT (thm2_opt,b2))))
                        else NONE;
     in
        DEPTH_CONSEQ_CONV_num___REC_CALL l step_opt d2 true redepth conv thm3_opt (n1+n2) t
     end
   else if ((not top) andalso is_imp_only t) then
     let
	 val (b1,b2) = dest_imp t;
         val (n1, d1, thm1_opt) = DEPTH_CONSEQ_CONV_num (l+1) step_opt (CONSEQ_CONV_DIRECTION_NEGATE dir) top redepth conv b1;
         val (n2, d2, thm2_opt) = DEPTH_CONSEQ_CONV_num (l+1) (step_opt_sub step_opt n1) (CONSEQ_CONV_DIRECTION_NEGATE d1) top redepth conv b2;

	 val thm3_opt = if (isSome thm1_opt) orelse (isSome thm2_opt) then
                          SOME (MATCH_MP MONO_IMP (CONJ (CONVERT_THM_OPT (thm1_opt,b1)) (CONVERT_THM_OPT (thm2_opt,b2))))
                        else NONE;
     in
        DEPTH_CONSEQ_CONV_num___REC_CALL l step_opt d2 true redepth conv thm3_opt (n1+n2) t
     end
   else if ((not top) andalso is_neg t) then
     let
	 val b1 = dest_neg t;
         val (n1, d1, thm1_opt) = DEPTH_CONSEQ_CONV_num (l+1) step_opt (CONSEQ_CONV_DIRECTION_NEGATE dir) top redepth conv b1;
         val d2 = CONSEQ_CONV_DIRECTION_NEGATE d1;

	 val thm3_opt = if isSome thm1_opt then
                           SOME (MATCH_MP MONO_NOT (valOf thm1_opt))
                        else
                           NONE
     in
        DEPTH_CONSEQ_CONV_num___REC_CALL l step_opt d2 true redepth conv thm3_opt n1 t
     end
   else if ((not top) andalso is_forall t) then
     let
        val (var, body) = dest_forall t;
	val (n1, d1, thm_body_opt) = DEPTH_CONSEQ_CONV_num (l+1) step_opt dir top redepth conv body;


        val thm_opt = if (isSome thm_body_opt) then
                         SOME (HO_MATCH_MP MONO_ALL (GEN_ASSUM var (valOf thm_body_opt)))
		      else NONE
     in
        DEPTH_CONSEQ_CONV_num___REC_CALL l step_opt d1 true redepth conv thm_opt n1 t
     end
   else if ((not top) andalso is_exists t) then
     let
        val (var, body) = dest_exists t;
	val (n1, d1, thm_body_opt) = DEPTH_CONSEQ_CONV_num (l+1) step_opt dir top redepth conv body;
        val thm_opt = if (isSome thm_body_opt) then
                         SOME (HO_MATCH_MP boolTheory.MONO_EXISTS 
                            (GEN_ASSUM var (valOf thm_body_opt)))
                      else NONE
     in
        DEPTH_CONSEQ_CONV_num___REC_CALL l step_opt d1 true redepth conv thm_opt n1 t
     end
   else 
     ((let
         val _ = DEPTH_CONSEQ_CONV_say 3 l (fn () => ("Trying CONV ``"^term_to_string t^"``"));
	 val (d1, thm1) = CONSEQ_CONV_WRAPPER dir conv t;
         val (d2, thm2) = if d1 = CONSEQ_CONV_UNKNOWN_direction then
			     (DEPTH_CONSEQ_CONV_say 3 l (fn () => ("Guessed direction strengthen!"));
                              (CONSEQ_CONV_STRENGTHEN_direction,          
                               snd (EQ_IMP_RULE thm1)))
                          else (d1, thm1);
         val _ = DEPTH_CONSEQ_CONV_say 1 l (fn () => ("``"^term_to_string t^"`` became "^(thm_to_string thm2)));
     in
        if (redepth) then
            DEPTH_CONSEQ_CONV_num___REC_CALL l step_opt d1 false true conv (SOME thm2) 1 t
        else
	    (1, d2, SOME thm2)
     end handle HOL_ERR _ => (DEPTH_CONSEQ_CONV_say 2 l (K "No Result!");(0, dir, NONE)))
         handle UNCHANGED => (DEPTH_CONSEQ_CONV_say 2 l (K "No Result!");(0, dir, NONE)))
end;




fun DEPTH_CONSEQ_CONV conv dir  = 
 OPT_CHANGED_CHECK_CONSEQ_CONV (fn t => 
   if (type_of t = bool) then 
      (#3 (DEPTH_CONSEQ_CONV_num 0 NONE dir false false conv t))
   else raise UNCHANGED)


fun REDEPTH_CONSEQ_CONV conv dir  = 
 OPT_CHANGED_CHECK_CONSEQ_CONV (fn t => 
   if (type_of t = bool) then 
      (#3 (DEPTH_CONSEQ_CONV_num 0 NONE dir false true conv t))
   else raise UNCHANGED)

fun NUM_DEPTH_CONSEQ_CONV conv n dir = 
   OPT_CHANGED_CHECK_CONSEQ_CONV (fn t => 
     if (type_of t = bool) then 
       (#3 (DEPTH_CONSEQ_CONV_num 0 (SOME n) dir false false conv t))
     else raise UNCHANGED)


fun NUM_REDEPTH_CONSEQ_CONV conv n dir = 
   OPT_CHANGED_CHECK_CONSEQ_CONV (fn t => 
     if (type_of t = bool) then 
       (#3 (DEPTH_CONSEQ_CONV_num 0 (SOME n) dir false true conv t))
     else raise UNCHANGED)

fun ONCE_DEPTH_CONSEQ_CONV conv = NUM_DEPTH_CONSEQ_CONV conv 1;



(*---------------------------------------------------------------------------
 * Takes the assumptions returned by a CONSEQ_CONV,
 * tries to simplify them recursively with the same CONSEQ_CONV and
 * add the results to the assumptions. Assumptions in preserve_hyps are 
 * not simplified. 
 *---------------------------------------------------------------------------*)

fun CONJ_ASSUMPTIONS_CONSEQ_CONV conv preserve_hyp_pred dir t =
let
    val thm = conv dir t;
    val new_hyps = filter (fn t => not (preserve_hyp_pred t)) (hyp thm);
    val hyp_thms = map (fn h => 
                       ((SOME (CONJ_ASSUMPTIONS_CONSEQ_CONV conv preserve_hyp_pred CONSEQ_CONV_STRENGTHEN_direction h))
		        handle HOL_ERR _ => NONE) 
                        handle UNCHANGED => NONE) new_hyps;

    val hyp_thms2 = filter (fn thm_opt => (isSome thm_opt andalso
					   let val (l,r) = dest_imp (concl (valOf thm_opt)) in (not (l = r)) end handle HOL_ERR _ => false)) hyp_thms; 
    val hyp_thms3 = map (UNDISCH o valOf) hyp_thms2; 

    val thm2 = foldr (fn (thm1,thm2) => PROVE_HYP thm1 thm2) thm hyp_thms3;


    val new_hyps2 = filter (fn t => not (preserve_hyp_pred t)) (hyp thm2);
    val thm3 = foldr (fn (t,thm) => SUBST_MATCH (SPEC_ALL AND_IMP_INTRO) (DISCH t thm)) thm2 (new_hyps2);
    val thm4 = CONV_RULE (RATOR_CONV (REWRITE_CONV [])) thm3
in
    thm4
end;


fun CONJ_ASSUMPTIONS_DEPTH_CONSEQ_CONV conv =
    CONJ_ASSUMPTIONS_CONSEQ_CONV (DEPTH_CONSEQ_CONV conv) (K false)

fun CONJ_ASSUMPTIONS_REDEPTH_CONSEQ_CONV conv =
    CONJ_ASSUMPTIONS_CONSEQ_CONV (REDEPTH_CONSEQ_CONV conv) (K false)


(*A tactic that strengthens a boolean goal*)
fun CONSEQ_CONV_TAC conv (asm,t) = 
    HO_MATCH_MP_TAC ((CHANGED_CONSEQ_CONV (conv CONSEQ_CONV_STRENGTHEN_direction)) t) (asm,t) handle UNCHANGED =>
    ALL_TAC (asm,t)


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

CONSEQ_REWRITE_CONV ([rewrite_every_thm],[],[]) CONSEQ_CONV_STRENGTHEN_direction 
   ``FEVERY P (g |+ (3, x) |+ (7,z))``

This should result in:

val it =
    |- (FEVERY P g /\ P (3,x)) /\ P (7,z) ==> FEVERY P (g |+ (3,x) |+ (7,z)) :
  thm


It works in substructures as well

CONSEQ_REWRITE_CONV ([rewrite_every_thm],[],[]) CONSEQ_CONV_STRENGTHEN_direction ``!g. ?x. Q (g, x) /\ FEVERY P (g |+ (3, x) |+ (7,z)) \/ (z = 12)``

> val it =
    |- (!g.
          ?x. Q (g,x) /\ (FEVERY P g /\ P (3,x)) /\ P (7,z) \/ (z = 12)) ==>
       !g. ?x. Q (g,x) /\ FEVERY P (g |+ (3,x) |+ (7,z)) \/ (z = 12) : thm


You can use the FEXISTS-theorem to weaken them:

CONSEQ_REWRITE_CONV ([rewrite_exists_thm],[],[]) CONSEQ_CONV_WEAKEN_direction ``FEXISTS P (g |+ (3, x) |+ (7,z))``

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



The parameter CONSEQ_CONV_UNKNOWN_direction can be used to let the system figure out,
what to do:

CONSEQ_REWRITE_CONV [rewrite_exists_thm,rewrite_every_thm] CONSEQ_CONV_UNKNOWN_direction 
   ``FEVERY P (g |+ (3, x) |+ (7,z)) ==> FEXISTS P (g |+ (3, x) |+ (7,z))``


*)

end
