

(* miscellaneous useful stuff that doesn't fit in anywhere else *)
structure holCheckTools =
struct

local

open Globals HolKernel Parse goalstackLib;

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
open numLib;

in

val dbgall = false

val mk_var = Term.mk_var;

fun mk_bool_var v = mk_var(v,``:bool``);

fun mk_primed_bool_var v = mk_bool_var (v^"'");

fun term_to_string2 t = with_flag (show_types,false) term_to_string t;

fun prime v = mk_var((term_to_string2 v)^"'",type_of v)

fun is_prime v = (Char.compare(List.last(explode(term_to_string v)),#"'")=EQUAL) 

fun unprime v = if is_prime v then mk_var(implode(butlast(explode(term_to_string2 v))),type_of v) else v

fun listmax l = List.foldl (fn (i,m) => if m<i then i else m) (Option.valOf Int.minInt) l

fun showVector v s f= let
    val _ = Vector.appi (fn (ix,el) => print("("^(int_to_string ix)^","^(term_to_string2(f el))^")")) (v,0,NONE)
    in print("("^s^")\n") end

datatype DMT = TM of term | TH of thm | ST of string | NM of int | TY of hol_type | BD of bdd

fun DMSG (TM t) v = if v then let val _ = print_term t val _ = print "\n" in () end else ()
|   DMSG (TH t) v = if v then let val _ = print_thm t val _ = print "\n" in () end else ()
|   DMSG (TY t) v = if v then let val _ = print_type t val _ = print "\n" in () end else ()
|   DMSG (ST s) v = if v then let val _ = print s val _ = print "\n" in () end else ()
|   DMSG (BD b) v = if v then let val _ = bdd.printset b val _ = print "\n" in () end else ()
|   DMSG (NM i) v = if v then let val _ = print (int_to_string i) val _ = print "\n" in () end else ()

fun list2map (h::t) = Binarymap.insert(list2map t, (fst h), (snd h))
|   list2map [] = Binarymap.mkDict String.compare;

fun list2imap (h::t) = insert(list2imap t, (fst h), (snd h))
|   list2imap [] = mkDict Int.compare;

fun listkeyfind (h::t) k cf = if (cf(k,fst h)=EQUAL) then snd h else listkeyfind t k cf
| listkeyfind [] _ _ = Raise NotFound 

fun ilog2 n = if n=1 then 1 else Real.floor(((Math.ln (Real.fromInt(n)))/(Math.ln 2.0))+1.0); (* NOTE:this is NOT log_2 *)

fun log2 n = Math.ln n / Math.ln 2.0

fun mk_subst red res = (map2 (curry op|->) red res) (*List.map (fn (v,v') => v |-> v') (ListPair.zip(red,res));*)

fun tsimps ty = let val {convs,rewrs} = TypeBase.simpls_of ty in rewrs end;

(* taken from Mike's HOL history paper. Attributed to C. Strachey. *)
fun cartprod L = List.foldr (fn (k,z) => List.foldr (fn (x,y) => List.foldr (fn (p,q) => (x::p)::q) y z) [] k) [[]] L

(* take a state and return it with all vars primed *)
fun mk_primed_state s = 
    let val l = strip_pair s
    in list_mk_pair (List.map (fn v => mk_var((term_to_string2 v)^"'",type_of v)) l) end


(* given a list [a,b,c,d,...], return the list [(a,b),(b,c),(c,d)...]*)
fun threadlist (h1::h2::t) = (h1,h2)::(threadlist (h2::t))
| threadlist [h] = []
| threadlist [] = []

(* just discovered this is already present as Lib.split_after (though not sure if that behaves exactly like this) *)
fun split_list [] n =  ([],[])
  | split_list (h::t) n = let val (M,N)=split_list (t) (n-1)
			  in if (n>0) then (h::M,N) else (M,h::N) end

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
		 (*val thm = snd (if not (Binaryset.equal(Vset,bodyvarset)) andalso not (Binaryset.isSubset(Vset,bodyvarset))
				      then  List.foldl (fn (v,(n,thm)) => 
							   if (Binaryset.member(bodyvarset,v)) then (n+1,thm)
							   else (n+1,thm_rule v n thm))
						       (0,thm) V
				      else (0,thm))*)
		 val rside = rhs(concl thm)
		 val ((W,W'),body) = ((fn l => split_list l (List.length V)) ## I) (strip_quant rside)
	     in TRANS thm (ALPHA rside (list_mk_quant(V@W', subst(map2 (curry op|->) W V) body))) 
	     end	
end

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

end
end

