structure abs_tools =
struct

open abstraction;

open HolKernel Parse boolLib

(* My stuffs: adding implicit arguments to preterms and TotalDefn.Define *)


local open Absyn in

val add_ip =
  let fun add_ip (c as IDENT(locn,s)) = foldl (fn (v,pt) => APP(locn,pt,v)) c (impl_of s)
        | add_ip (c as QIDENT (locn,t,n)) = 
             foldl (fn (v,pt) => APP(locn(*TODO:not quite*),pt,v)) c (impl_of n)
  	| add_ip (APP(locn,Rator,Rand)) = APP(locn, add_ip Rator, add_ip Rand)
  	| add_ip (LAM(locn,vs,body))    = LAM(locn, vs, add_ip body)
  	| add_ip (TYPED(locn,pt,ty))    = TYPED(locn, add_ip pt ,ty)
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

fun asm_prove (cl,tac) = TAC_PROOF((get_assums(),cl), tac);

fun asm_save_thm(x,thm) =
  Theory.save_thm(x,gen_assums thm);


fun asm_store_thm(x,cl,tac) =
  let val thm = asm_prove(cl,tac) in
  asm_save_thm(x,thm); thm
  end;


fun Term q = let
    val pt = Parse.Absyn q
    val pt' = add_ip pt
    val prfns = SOME(term_to_string, type_to_string)
  in
    Preterm.typecheck prfns (absyn_to_preterm pt')
  end

fun --q _ = Term q;


fun Define q =
  let val tm = --q--
      val tm' = abstraction.param_eq tm
  in TotalDefn.Define [ANTIQUOTE tm']
  end;

(*
fun gg flist = set_goal(get_assums(),--flist--);
fun g0 flist = set_goal(get_assums(),flist);
*)

end
