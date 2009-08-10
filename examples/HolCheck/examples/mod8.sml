
(********************************************************************************************************)
(* mod-8 counter: starts from 0 (i.e. ~v0 /\ ~v1 /\ ~v2) and counts up to 7, then loops back to 0 and   *)
(* starts over.                                                                                         *)
(*                                                                                                      *)
(* Toy example for HolCheck. Also used in the online reference.                                         *)
(********************************************************************************************************)

structure mod8 = struct

local

    open Globals HolKernel Parse pairSyntax bossLib boolSyntax Rewrite
    open holCheckLib mod16Theory

in

fun mk_mod8 () = (* return HolCheck model for mod8 counter tha can be passed to holCheck *)
    let
	(* transition system : note we expand the xor def since HolCheck needs pure propositional formulas *)
	val TS = List.map (I ## (rhs o concl o (fn tm => REWRITE_CONV [xor_def] tm handle Conv.UNCHANGED => REFL tm)))
			  [("v0",``(v0'=~v0)``),("v1",``v1' = xor v0 v1``),("v2",``v2' = xor (v0 /\ v1) v2``)]
	val S0 = ``~v0 /\ ~v1 /\ ~v2`` (* initial states *)
	val ric = true (* TS is synchronous *)
	val state = mk_state S0 TS
	val ctlf = ("ef_msb_high",``C_EF (C_BOOL (B_PROP ^(pairSyntax.mk_pabs(state,``v2:bool``))))``) (* msb goes high eventually *)
    in  ((set_init S0) o (set_trans TS) o (set_flag_ric ric) o (set_name "mod8") o (set_state state) o  (set_props [ctlf])) empty_model end


(*
Usage example (start hol including the HolCheck/examples directory, using the -I command line option) :

val _ = app load ["holCheckLib","mod8"];
val mod8 = mod8.mk_mod8();
val mod8' = holCheckLib.holCheck mod8;
val mod8'' = holCheckLib.prove_model mod8';
val res = modelTools.get_results mod8'';
*)
end
end
