open bossLib abstraction;

local
open HolKernel Parse basicHol90Lib
in

(* My stuffs: adding implicit arguments to preterms and bossLib.Define *)


local open parse_term in

fun impl_of x =
  map AQ (assoc x (!impl_param_cstr)) handle HOL_ERR _ => []


val add_ip =
  let fun add_ip (c as VAR s) =
            foldl (fn (v,pt) => COMB(pt,v)) c (impl_of s)
  	| add_ip (COMB(Rator,Rand)) = COMB(add_ip Rator, add_ip Rand)
  	| add_ip (ABS(vs,body)) = ABS(vs, add_ip body)
  	| add_ip (TYPED(pt,ty)) = TYPED(add_ip pt ,ty)
  	| add_ip pt = pt
  in add_ip
  end
end;

(*-------*)
(*
fun import {Inst=inst} lthm =
  map (C (foldl (uncurry (C MATCH_MP))) inst) lthm
;
*)
(*-------*)

fun add_parameter v =
  let val _ = dest_var v in
  fv_ass := v :: !fv_ass
  end;


fun set_assums asl =
  (curr_assums := asl;
   fv_ass := free_varsl asl)
;

fun add_assums asl =
  (curr_assums := rev asl @ !curr_assums;
   fv_ass := subtract (free_varsl asl) (!fv_ass) @ !fv_ass)
;

fun asm_prove (cl,tac) = TAC_PROOF((!curr_assums,cl), tac);

fun select_disch (h,th) =
  if op_mem (curry Portable.pointer_eq) h (hyp th) then DISCH h th
  else th;


(* Only the variables appearing in the discharged hypothese should
 * be generalized.
 *)
fun gen_assums thm =
  GENL (!fv_ass) (foldr select_disch thm (!curr_assums));


fun asm_save_thm(x,thm) =
  Theory.save_thm(x,gen_assums thm);


fun asm_store_thm(x,cl,tac) =
  let val thm = asm_prove(cl,tac) in
  asm_save_thm(x,thm); thm
  end;




fun Term q = let
    val pt = parse_preTerm q
    val pt' = add_ip pt
    val prfns = SOME(term_to_string, type_to_string)
  in
    Preterm.typecheck prfns (resolve_names pt')
  end

fun --q _ = Term q;


fun Define q =
  let val tm = --q--
      val tm' = abstraction.param_eq (head tm) tm
  in bossLib.Define [ANTIQUOTE tm']
  end;

(*
fun gg flist = set_goal(!curr_assums,--flist--);
fun g0 flist = set_goal(!curr_assums,flist);
*)

end;
