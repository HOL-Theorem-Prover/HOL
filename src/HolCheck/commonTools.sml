
(* miscellaneous useful stuff that doesn't fit in anywhere else *)
structure commonTools = 
struct 

local

open Globals HolKernel Parse goalstackLib Feedback

open bossLib;
open pairTheory;
open pred_setTheory;
open pred_setLib;
open stringLib;
open simpLib;
open pairSyntax;
open pairLib;
open PrimitiveBddRules;
open DerivedBddRules;
open Binarymap;
open PairRules;
open pairTools;
open boolSyntax;
open Drule;
open Tactical;
open Conv;
open Rewrite;
open Tactic;
open boolTheory;
open stringTheory;
open stringBinTree;
open boolSimps;
open pureSimps;
open numLib
open lazyTools
open sumSyntax
open sumTheory

val dpfx = "comt_"

in

fun pair_map f (x,y) = (f x,f y)

(*********** math **************)

fun ilog2 n = if n=1 then 1 else Real.floor(((Math.ln (Real.fromInt(n)))/(Math.ln 2.0))+1.0); (* NOTE:this is NOT log_2 *)

fun log2 n = Math.ln n / Math.ln 2.0

(* taken from Mike's HOL history paper. Attributed to C. Strachey. *)
fun cartprod L = List.foldr (fn (k,z) => List.foldr (fn (x,y) => List.foldr (fn (p,q) => (x::p)::q) y z) [] k) [[]] L

(************ HOL **************)

fun tsimps ty = let val {convs,rewrs} = TypeBase.simpls_of ty in rewrs end;

(* make abbrev def: make definition where the lhs is just a constant name and rhs is closed term with no free_vars *)
fun mk_adf nm rhs = 
let val x = mk_var("x",type_of rhs )
in new_specification(nm^"_def",[nm],EXISTS (mk_exists(x,mk_eq(x,rhs))(*``?x. x = ^rhs``*),rhs) (REFL rhs)) end

fun LIST_ACCEPT_TAC l (asl,w) = 
    let val th = hd(List.filter (aconv w o concl) l)
    in ACCEPT_TAC th (asl,w) end

(************ strings ************)

(* replace all spaces in s with underscores *)
fun despace s = implode (List.map (fn c => if Char.compare(c,#" ")=EQUAL then #"_" else c) (explode s))

(*********** lists **************)

(* given a list [a,b,c,d,...], return the list [(a,b),(b,c),(c,d)...]*)
fun threadlist (h1::h2::t) = (h1,h2)::(threadlist (h2::t))
| threadlist [h] = []
| threadlist [] = []

(* just discovered this is already present as Lib.split_after (though not sure if that behaves exactly like this) *)
fun split_list [] n =  ([],[])
  | split_list (h::t) n = let val (M,N)=split_list (t) (n-1)
			  in if (n>0) then (h::M,N) else (M,h::N) end

fun listmax l = List.foldl (fn (i,m) => if m<i then i else m) (Option.valOf Int.minInt) l

fun list2map (h::t) = Binarymap.insert(list2map t, (fst h), (snd h))
|   list2map [] = Binarymap.mkDict String.compare;

fun list2imap (h::t) = insert(list2imap t, (fst h), (snd h))
|   list2imap [] = mkDict Int.compare;

fun listkeyfind (h::t) k cf = if (cf(k,fst h)=EQUAL) then snd h else listkeyfind t k cf
| listkeyfind [] _ _ = Raise NotFound 

(* chop up a list into lists of length n, though the last list will just take up the slack *)
fun multi_part n l = if (List.length l) <= n then [l] 
		     else let val (bf,af) = split_list l n
			  in bf::(multi_part n af) end

(*********** terms **************)

fun mk_subst red res = (map2 (curry op|->) red res) 

fun dest_subst {redex,residue} = (redex,residue)

val mk_var = Term.mk_var;

val land = rand o rator

fun mk_bool_var v = mk_var(v,``:bool``);

fun mk_primed_bool_var v = mk_bool_var (v^"'");

fun is_bool_var v = is_var v andalso (Type.compare(type_of v,bool)=EQUAL)

fun is_T tm = Term.compare(tm,T)=EQUAL

fun is_F tm = Term.compare(tm,F)=EQUAL

fun is_prop_tm tm = 
    if is_neg tm
    then is_prop_tm (rand tm)
    else 
	if is_conj tm orelse is_imp tm orelse is_disj tm orelse is_cond tm orelse is_eq tm
	then is_prop_tm (land tm) andalso is_prop_tm (rand tm)
	else 
	    if (is_forall tm) 
	    then let val (v,t) = dest_forall tm
		 in is_bool_var v andalso is_prop_tm t end
	    else 
		if is_exists tm
		then let val (v,t) = dest_exists tm
		     in is_bool_var v andalso is_prop_tm t end
		else is_T tm orelse is_F tm orelse is_bool_var tm

fun term_to_string2 t = with_flag (show_types,false) term_to_string t;

fun prime v = mk_var((term_to_string2 v)^"'",type_of v)

fun is_prime v = (Char.compare(List.last(explode(term_to_string v)),#"'")=EQUAL) 

fun unprime v = if is_prime v then mk_var(implode(butlast(explode(term_to_string2 v))),type_of v) else v

fun list_mk_disj2 [] = F
    | list_mk_disj2 l = list_mk_disj l

fun list_mk_conj2 [] = T
    | list_mk_conj2 l = list_mk_conj l

(* break apart all top-level conjunctions *) 
fun list_dest_conj t = if (is_conj t) then (if (is_conj(fst (dest_conj t))) then list_dest_conj(fst (dest_conj t)) 
					    else [fst (dest_conj t)])@
                                           (if (is_conj(snd (dest_conj t))) then list_dest_conj(snd (dest_conj t)) 
					    else [snd (dest_conj t)])
		       else [t];

(* assume t=(c,f1,f2) is a nested conditional, return a list of all the conditions *)
fun depth_dest_cond_aux (c,f1,f2) = 
    let val l1 = if (is_cond f1) then depth_dest_cond_aux (dest_cond f1) else []
	val l2 = if (is_cond f2) then depth_dest_cond_aux (dest_cond f2) else []
    in c::(l1@l2) end

fun depth_dest_cond t = if is_cond t then depth_dest_cond_aux (dest_cond t) else [t]

fun list_dest_cond_aux (c,f1,f2) = if is_cond f2 then (c,f1)::(list_dest_cond_aux (dest_cond f2)) else [(c,f1)]

(* destroy linear nested conditional, returning (test,true branch) pairs (the last false branch is dropped) *)
fun list_dest_cond t = if is_cond t then list_dest_cond_aux (dest_cond t) else []

fun gen_dest_cond_aux (c,f1,f2) = 
    let val l1 = if (is_cond f1) then gen_dest_cond_aux (dest_cond f1) else [([],f1)]
	val l2 = if (is_cond f2) then gen_dest_cond_aux (dest_cond f2) else [([],f2)]
    in (List.map (fn (l,v) => (c::l,v)) l1)@(List.map (fn (l,v) => (l,v)) l2) end

(* destroy general conditional, returning (list of tests,value) pairs *)
fun gen_dest_cond t = if is_cond t then gen_dest_cond_aux (dest_cond t) else []

(* my own version of ELIM_TULPED_QUANT_CONV *)

(* vacuous quantification. Will fail if v is free in tm *)
fun MK_VACUOUS_QUANT_CONV mk_quant v tm = 
    let val t2 = mk_quant(v,tm)
    in prove(mk_eq(tm,t2),REWRITE_TAC []) end (* FIXME: stop being lazy and make this quicker *)

(* push outermost quantifier inwards n times through same quants. Will fail if there aren't enough quants or if they are not the same *)
fun PUSH_QUANT_CONV swap_quant_conv n = 
    if n=0 then REFL else swap_quant_conv THENC QUANT_CONV (PUSH_QUANT_CONV swap_quant_conv (n-1))

(* my own version of pairTools.ELIM_TUPLED_QUANT_CONV that fixes the "impreciseness" (see comments in pairTools) *)
(* also fixes a crash if the target term is of the form ``\quant <varstruct> othervars. body``. Now works if othervars are present *)
(* also leaves non-paired quants unchanged rather than crashing *)
local 
  val is_uncurry_tm  = same_const pairSyntax.uncurry_tm
  val is_universal   = same_const boolSyntax.universal
  val is_existential = same_const boolSyntax.existential
  val CONV = fn n => EVERY_CONV (List.tabulate(n,fn n => Ho_Rewrite.PURE_ONCE_REWRITE_CONV [pairTheory.ELIM_UNCURRY])) THENC
				DEPTH_CONV BETA_CONV THENC
				Ho_Rewrite.PURE_REWRITE_CONV [pairTheory.ELIM_PEXISTS,pairTheory.ELIM_PFORALL]

  fun dest_tupled_quant tm =
    case total dest_comb tm
     of NONE => NONE
      | SOME(f,x) =>
        if is_comb x andalso is_uncurry_tm (rator x)
        then if is_existential f then SOME (strip_exists, list_mk_exists, pairSyntax.dest_pexists,
					    fn v => fn n => CONV_RULE (RHS_CONV ((MK_VACUOUS_QUANT_CONV mk_exists v) 
										     THENC (PUSH_QUANT_CONV SWAP_EXISTS_CONV n)))) else
             if is_universal f   then SOME (strip_forall, list_mk_forall, pairSyntax.dest_pforall,
					    fn v => fn n => CONV_RULE (RHS_CONV ((MK_VACUOUS_QUANT_CONV mk_forall v) 
										     THENC (PUSH_QUANT_CONV SWAP_VARS_CONV n)))) 
             else NONE
        else NONE
in

fun ELIM_TUPLED_QUANT_CONV tm =
    if not (is_pair (fst ((if is_pforall tm then dest_pforall else dest_pexists) tm))) then REFL tm 
    else case dest_tupled_quant tm
	  of NONE => raise Fail "TUPLED_QUANT_CONV"
	   | SOME (strip_quant, list_mk_quant, dest_pquant,thm_rule) => 
	     let val (tmq,tmbody) = dest_pquant tm
		 val V = strip_pair tmq
		 val thm = CONV ((List.length V)-1) tm
		 val bodyvarset = Binaryset.addList(Binaryset.empty Term.compare, free_vars tmbody)
		 val Vset = Binaryset.addList(Binaryset.empty Term.compare, V)
		 val rside = rhs(concl thm)
		 val ((W,W'),body) = ((fn l => split_list l (List.length V)) ## I) (strip_quant rside)
	     in TRANS thm (ALPHA rside (list_mk_quant(V@W', subst(map2 (curry op|->) W V) body))) 
	     end	
end

fun lzELIM_TUPLED_QUANT_CONV tm =
    let val ia = is_pforall tm
        val (bv,bod) = if ia then dest_pforall tm else dest_pexists tm
    in mk_lthm (fn _ => (mk_eq(tm,if ia then list_mk_forall(spine_pair bv,bod) else list_mk_exists(spine_pair bv,bod)),
			 (fn _ => ELIM_TUPLED_QUANT_CONV tm))) 
	       (fn _ => ELIM_TUPLED_QUANT_CONV tm) end

(*********** sums **************)

fun mk_sum_component_aux n i s = 
    if (i=0) then sumSyntax.mk_inl(s,mk_vartype("'a"^(int_to_string i))) 
    else if (i=1 andalso n=2) then sumSyntax.mk_inr(s,mk_vartype("'a"^(int_to_string i))) 
    else sumSyntax.mk_inr(mk_sum_component_aux (n-1) (i-1) s,mk_vartype("'a"^(int_to_string i))) 

(* returns s tagged with INL's and INR's so that its type is the i'th component of the sum ty_0+ty_1+...+ty_(n-1) *)
fun mk_sum_component ty i s = 
    if ((List.length (sumSyntax.strip_sum ty)) = 1) then s
    else let val tys = sumSyntax.strip_sum ty
	     val n = List.length tys
	     val res = mk_sum_component_aux n i s
	     val tysp = split_after i tys
	     val stl = if (i=(n-1)) then [] else [(sumSyntax.list_mk_sum o List.tl) (snd tysp)] 
             val nl = if i = (n-1) then List.tabulate(n-1,fn n => n +1) else List.tabulate(n-(n-i)+1,I)   
	 in inst (List.map (fn (j,t) => mk_vartype("'a"^(int_to_string j)) |-> t) 
			   (ListPair.zip(List.rev nl,(fst tysp)@stl))) res 
	 end

(* returns s:(ty_0+ty_1+...+ty_(n-1)) tagged with OUTL's and OUTR's to strip away the sum type 
 assuming s is the i'th component in the sum *)
fun dest_sum_component styl n i s =
    let val _ = dbgTools.DEN dpfx "dsc" (*DBG*)
	val _ = dbgTools.DTM (dpfx^"dsc_s") s
	val _ = List.app (dbgTools.DTY (dpfx^"dsc_styl")) styl
	val res = 
	    if (n=1) then s (* there is only one component *)
	    else if (i = 0) then mk_comb(inst [alpha |-> List.hd styl,beta |-> list_mk_sum (List.tl styl)] outl_tm,s)
	    else if (i = 1 andalso n = 2) then mk_comb(inst [alpha |-> List.hd styl,beta |-> list_mk_sum (List.tl styl)] outr_tm,s)
	    else dest_sum_component (List.tl styl) (n-1) (i-1) (mk_comb(inst [alpha |-> List.hd styl,
									      beta |->list_mk_sum (List.tl styl)] outr_tm,s))
	val _ = dbgTools.DEX dpfx "dsc" (*DBG*)
    in res end

fun isIN t = let val s = term_to_string2 t in String.compare(s,"INL")=EQUAL orelse String.compare(s,"INR")=EQUAL end

(* t is a term that is 1..several applications of INL/INR to some value x. Return x *) 
fun strip_in t = 
    if is_comb t 
    then let val (a,b) = dest_comb t
	 in if isIN a then strip_in b else t end
    else t

end
end