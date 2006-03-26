 
(* miscellaneous useful stuff that doesn't fit in anywhere else *)
structure satCommonTools = 
struct 

local

open Globals HolKernel Parse goalstackLib Feedback

open Binarymap boolSyntax Drule Tactical Conv Rewrite Tactic boolTheory satTheory Term numSyntax

in

fun bool_to_int b = if b then 1 else 0

fun pair_map f (x,y) = (f x,f y)

(*********** math **************)

fun ilog2 n = if n=1 then 1 else Real.floor(((Math.ln (Real.fromInt(n)))/(Math.ln 2.0))+1.0); (* NOTE:this is NOT log_2 *)

fun log2 n = Math.ln n / Math.ln 2.0

(* taken from Mike's HOL history paper. Attributed to C. Strachey. *)
fun cartprod L = List.foldr (fn (k,z) => List.foldr (fn (x,y) => List.foldr (fn (p,q) => (x::p)::q) y z) [] k) [[]] L

fun fromMLnum n = mk_numeral(Arbnum.fromInt n);

fun fromHOLnum n = Arbnum.toInt(dest_numeral n)

(************ strings ************)

(* replace all spaces in s with underscores *)
fun despace s = implode (List.map (fn c => if Char.compare(c,#" ")=EQUAL then #"_" else c) (explode s))

fun prm s = s^"'"

(*********** vectors ************)
fun vbs cf v x si ei = 
if si=ei then if cf(Vector.sub(v,si),x)=EQUAL then SOME si else NONE
else let val mid = si+((ei-si) div 2)
     in case cf(x,Vector.sub(v,mid)) of
	    EQUAL => SOME mid
	  | LESS => vbs cf v x si mid
	  | GREATER => vbs cf v x (mid+1) ei
     end  

(* vector binary search *)
(*assume v is sorted wrt cf, return SOME i if v[i]=x, NONE if x is not in v *)
fun vecbs cf v e = vbs cf v e 0 (Vector.length v - 1)

(*********** arrays ************)
fun abs' cf a x si ei = 
if si>ei then NONE
else if si=ei then if cf(Array.sub(a,si),x)=EQUAL then SOME si else NONE
else let val mid = si+((ei-si) div 2)
     in case cf(x,Array.sub(a,mid)) of
	    EQUAL => SOME mid
	  | LESS => abs' cf a x si mid
	  | GREATER => abs' cf a x (mid+1) ei
     end  

(* array binary search *)
(*assume a is sorted wrt cf, return SOME i if a[i]=x, NONE if x is not in a *)
fun arrbs cf a e = abs' cf a e 0 (Array.length a - 1)

fun arrbsi cf a si ei e =  abs' cf a e si ei
(*********** lists **************)

(* find index of term e in list l *)
fun list_find_idx l e = 
    let val (n,f) = List.foldl (fn (v,(n,found)) => 
				   if found 
				   then (n,true) 
				   else 
				       if Term.compare(v,e)=EQUAL 
				       then (n+1,true) 
				       else (n+1,false))
			       (~1,false) l
    in if f then SOME n else NONE end

(* given a list [a,b,c,d,...], return the list [(a,b),(b,c),(c,d)...]*)
fun threadlist (h1::h2::t) = (h1,h2)::(threadlist (h2::t))
| threadlist [h] = []
| threadlist [] = []

(* given a list [a,b,c...] and a list [1,2,3...], return [a,1,b,2,...] *)
(* both lists should be same length, otherwise exception *)
fun interleave (h1::t1) (h2::t2) = h1::h2::(interleave t1 t2)
|   interleave []       []       = []
|   interleave l1       l2       = failwith ("Match exception in commonTools.interleave")

(* just discovered this is already present as Lib.split_after (though not sure if that behaves exactly like this) *)
fun split_list [] n =  ([],[])
  | split_list (h::t) n = let val (M,N)=split_list (t) (n-1)
			  in if (n>0) then (h::M,N) else (M,h::N) end

fun listmax l = List.foldl (fn (i,m) => if m<i then i else m) (Option.valOf Int.minInt) l

fun listMin mx cf l = 
    List.foldl (fn (i,mn) => 
		case cf(i,mn) of 
		   EQUAL => mn
		 | LESS => i
		 | GREATER => mn) 
    mx l

fun listmap cf (h::t) = Binarymap.insert(listmap cf t, (fst h), (snd h))
|   listmap cf [] = Binarymap.mkDict cf;

fun list2set cf (h::t) = Binaryset.add(list2set cf t,h)
|   list2set cf [] = Binaryset.empty cf;

fun list2imap l = listmap Int.compare l

fun list2map l = listmap String.compare l

fun listkeyfind (h::t) k cf = if (cf(k,fst h)=EQUAL) then snd h else listkeyfind t k cf
| listkeyfind [] _ _ = Raise NotFound 

(* chop up a list into lists of length n, though the last list will just take up the slack *)
fun multi_part n l = if (List.length l) <= n then [l] 
		     else let val (bf,af) = split_list l n
			  in bf::(multi_part n af) end

(* remove duplicates from list l, under comparison function cf *)
(* at amortized n lg n this is much better than quadratic Lib.mk_set *)
fun undup cf l = HOLset.listItems(HOLset.addList(HOLset.empty cf,l))

(* this is better than listSyntax.mk_list because it figures out the type by itself*)
fun fMl ty (h::t) = listSyntax.mk_cons(h,fMl ty t)
|   fMl ty [] = listSyntax.mk_nil ty

fun fromMLlist (h::t) = fMl (type_of h) (h::t)
| fromMLlist [] = listSyntax.mk_nil alpha

(* l is sorted under cf. return l' where e has been inserted into l st l' is sorted under cf as well*)
fun list_fit cf e l = 
    let val (b,a) = List.partition (fn x => cf(x,e)=LESS) l
    in (b@[e]@a) end

(* l is sorted under cf. return n st (list_fit cf e l)[n]=e *)
fun list_fit_idx cf e l = 
    let val (b,a) = List.partition (fn x => cf(x,e)=LESS) l
    in List.length b end

(*********** terms **************)

fun mk_subst red res = (map2 (curry op|->) red res) 

fun dest_subst {redex,residue} = (redex,residue)

val mk_var = Term.mk_var;

val land = rand o rator

fun setify cf l = HOLset.listItems(HOLset.addList(HOLset.empty cf,l))

fun mk_bool_var v = mk_var(v,bool);

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

fun is_prime v =  (Char.compare(List.last(explode(term_to_string2 v)),#"'")=EQUAL)

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


(************ HOL **************)

fun tsimps ty = let val {convs,rewrs} = TypeBase.simpls_of ty in rewrs end;

fun get_ss_rewrs ss = 
let val simpLib.SSFRAG{rewrs,ac,congs,convs,dprocs,filter} = ss in rewrs end

(* make abbrev def: make definition where the lhs is just a constant name and rhs is closed term with no free_vars *)
fun mk_adf nm rhs = 
let val x = mk_var("x",type_of rhs )
in new_specification(nm^"_def",[nm],EXISTS (mk_exists(x,mk_eq(x,rhs)),rhs) (REFL rhs)) end

fun LIST_ACCEPT_TAC l (asl,w) = 
    let val th = hd(List.filter (aconv w o concl) l)
    in ACCEPT_TAC th (asl,w) end

fun ERC lt tm =
    if is_comb lt 
	then let val ((ltl,ltr),(tml,tmr)) = pair_map dest_comb (lt,tm)
	     in (ERC ltl tml)@(ERC ltr tmr) end
    else 
	if is_var lt
	    then [lt |-> tm]
	else []

(* easier REWR_CONV for act.merge et al, which assumes that the supplied theorem is ground and quantifier free, 
   so type instantiation and free/bound var checks are not needed *)
(* no restrictions on the term argument *)
fun EREWR_CONV th tm = 
    let (*val th0 = SPEC_ALL th*)
	val lt = lhs(concl th)
	val il = ERC lt tm
    in INST il th end

(* the iCONV's allow me to neatly pass along a number in addition to the theorem  *)
fun iCONV_RULE iconv th = 
    let val (th',i) = iconv(concl th) handle UNCHANGED => (th,0)
    in (EQ_MP th' th,i) end

fun iRAND_CONV iconv t = 
    let val (t0,t1) = dest_comb t
	val (th,i) = iconv t1
    in (AP_TERM t0 th,i) end

infix iTHENC

fun (iconv1 iTHENC iconv2) t = 
    let	val (th1,i1) = iconv1 t handle UNCHANGED => (REFL t,0)
	val (th2,i2) = iconv2 (rhs (concl th1)) handle UNCHANGED => (REFL (rhs(concl th1)),i1) 
    in (TRANS th1 th2,i1+i2) end 

fun iALL_CONV t = (ALL_CONV t,0)

fun iREWR_CONV th t = (EREWR_CONV th t,0)

fun iREWR_CONV1 th t = (EREWR_CONV th t,~1)

fun iREWR_CONV2 th t = (EREWR_CONV th t,~2)

end
end
