open abstraction;

local
open HolKernel Parse basicHol90Lib
in

(* My stuffs: adding implicit arguments to preterms and TotalDefn.Define *)


local open parse_term in

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

fun asm_prove (cl,tac) = TAC_PROOF((get_assums(),cl), tac);

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
      val tm' = abstraction.param_eq tm
  in TotalDefn.Define [ANTIQUOTE tm']
  end;

(*
fun gg flist = set_goal(get_assums(),--flist--);
fun g0 flist = set_goal(get_assums(),flist);
*)

end;
