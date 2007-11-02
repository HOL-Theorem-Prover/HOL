

structure holCheckTools =
struct
local 

open Globals HolKernel Parse
open pairSyntax
open ctlSyntax muSyntax ctl2muTools commonTools

val dpfx = "hct_"

in

fun find_aps f = HOLset.listItems(HOLset.addList(HOLset.empty Term.compare,
						 List.map rand ((ctlSyntax.find_BPROPs f)@(muSyntax.find_APs f))))

(*FIXME: we need to be smarter about extracting ap's 
         e.g. currently for 2x2 ttt, m, ~m and ~~m become three abs vars, whereas the concrete ks had only m *)
fun mk_abs_APs' f state = 
    let val _ = dbgTools.DEN dpfx "maA'"(*DBG*)
	val is_mu = ((String.compare(fst(dest_type(type_of f)),"mu"))=EQUAL)
	val muf = if is_mu then f else ctl2muTools.ctl2mu f
	val prop_tms = prop_subtmset muf 1
	val ap = List.map (fn p => prop2ap p state) prop_tms (*FIXME: don't use abstraction if number of AP's is too high *)
	val aps = List.map mu_AP ap
	val _ = List.app (fn (p,a) => (dbgTools.DTM (dpfx^"mA'_p") p;dbgTools.DTM (dpfx^"mA'_a") a)) (ListPair.zip(prop_tms,ap)) 
	val apsubs = mk_subst prop_tms aps (* used to convert formulas in fl to use the new APs *)
	val _ = List.app (dbgTools.DTM (dpfx^"maA'_ap")) ap
	val _ = dbgTools.DEX dpfx "maA'"(*DBG*)
    in (ap,apsubs) end 

(* find all the atomic propositions in the list of properties in fl *)
(* note we need to provide special provision in mk_abs_APs' for logics other than mu-calculus *)
(* return NONE if the number of atomic propositions is >= number of concrete state vars since abs won't help in that case*)
fun mk_abs_APs fl state = 
    let val _ = dbgTools.DEN (dpfx^"_maA") (*DBG*)
	val _ = profTools.bgt (dpfx^"maA") (*PRF*)
	val (apl,apsubs) = (List.concat##List.concat) (ListPair.unzip (List.map (fn f => mk_abs_APs' (snd f) state) fl))
	val apl = HOLset.listItems (HOLset.addList(HOLset.empty Term.compare,apl))
	val cl = List.length (strip_pair state)
	val al = List.length apl
	val _ = dbgTools.DNM (dpfx^"_maA_cnum") cl (*DBG*)
	val _ = dbgTools.DNM (dpfx^"_maA_anum") al (*DBG*)
	val _ = dbgTools.DEN (dpfx^"_maA") (*DBG*)
	val _ = profTools.ent (dpfx^"maA") (*PRF*)
    in (if al >= cl then NONE else SOME apl,apsubs) end	

						    
end
end

