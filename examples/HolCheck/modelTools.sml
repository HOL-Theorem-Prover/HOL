
(* this contains all info about the model, including the properties to be checked, and th eventual results *)
(* the main reason for having this as an opaque type is to give holCheck a clean and stable signature *)
(* otherwise there is no pressing reason to not allow users to modify models directly *)
(* FIXME: allow a get_ks type ability at least*)
structure modelTools :> modelTools =
struct

local

open Globals HolKernel Parse
open PrimitiveBddRules pairSyntax
open internalCacheTools commonTools muSyntax

in

open Abbrev

type ic = internalCacheTools.ic
type term_bdd = PrimitiveBddRules.term_bdd
type model = {init:  term option,
	      trans: (string * term) list option,
	      ric:   bool option,
	      name:  string option,
	      vord:  string list option,
	      state: term option,
	      props: (string*term) list option,
	      results: (term_bdd * thm option * term list option) list option,
	      ic:internalCacheTools.ic option,
	      flags: {abs:bool}}

val empty_model = {init=NONE,trans=NONE,ric=NONE,name=NONE,vord=NONE,state=NONE,props=NONE,results=NONE,ic=NONE,
		   flags={abs=true}}

(* getters *)

fun get_name (m:model) = #name(m)
fun get_init (m:model) = valOf (#init(m))
fun get_trans (m:model) = valOf (#trans(m))
fun get_flag_ric (m:model) = valOf (#ric(m))
fun get_vord (m:model) = #vord(m)
fun get_state (m:model) = #state(m)
fun get_props (m:model) = valOf (#props(m))
fun get_results (m:model) = #results(m)
fun get_ic (m:model) = #ic(m)

fun get_flag_abs (m:model) = #abs (#flags m) (*if true, hc will try to do abstraction if possible and worthwhile; otherwise no abs *)

(* setters *)
fun set_name nm (m:model) =
    (if Lexis.allowed_term_constant nm then () else failwith ("modelTools.set_name: name must be a legal HOL constant name");
    {init= #init(m),trans= #trans(m),ric= #ric(m),name= SOME nm,vord= #vord(m),
     state= #state(m),props= #props(m),results= #results(m),ic= #ic(m),flags = #flags(m)})

fun set_init i (m:model) =
    (if is_prop_tm i then () else  failwith ("modelTools.set_init: non-propositional term (contains non-T/F bool constants?)");
    {init= SOME i,trans= #trans(m),ric= #ric(m),name= #name(m),vord= #vord(m),
     state= #state(m),props= #props(m),results= #results(m),ic= #ic(m),flags = #flags(m)})

fun set_flag_ric r (m:model)  =
    {init= #init(m),trans= #trans(m),ric= SOME r,name= #name(m),vord= #vord(m),
     state= #state(m),props= #props(m),results= #results(m),ic= #ic(m),flags = #flags(m)}

fun set_vord v (m:model)  = (* no point in any vetting here since it is easy to get around *)
    {init= #init(m),trans= #trans(m),ric= #ric(m),name= #name(m),vord= SOME v,
     state= #state(m),props= #props(m),results= #results(m),ic= #ic(m),flags = #flags(m)}

fun set_state s (m:model)  = (* no point in any vetting here since it is easy to get around *)
    {init= #init(m),trans= #trans(m),ric= #ric(m),name= #name(m),vord= #vord(m),
     state= SOME s,props= #props(m),results= #results(m),ic= #ic(m),flags = #flags(m)}

fun set_trans t (m:model)  =
    (let val (nm,R) = ListPair.unzip t
	 val nms = HOLset.addList(HOLset.empty String.compare,nm)
     in
	 if List.foldl (fn (t,v) => is_prop_tm t andalso v) true R
	 then
	     if (HOLset.numItems nms=List.length t)
	     then
		 if not (HOLset.member(nms,".")) orelse List.length t=1
		 then
		     if List.length t>0
		     then ()
		     else failwith ("modelTools.set_trans: no transitions specified")
		 else failwith ("modelTools.set_trans: non-singleton transition list contains \".\" as transition label")
	     else failwith ("modelTools.set_trans: transition labels are not unique")
	 else  failwith ("modelTools.set_trans: non-propositional term") end;
    {init= #init(m),trans= SOME t,ric= #ric(m),name= #name(m),vord= #vord(m),
     state= #state(m),props= #props(m),results= #results(m),ic= #ic(m),flags = #flags(m)})

fun set_props p (m:model)  =
    (let val (nm,fl) = ListPair.unzip p
	 val nms = HOLset.addList(HOLset.empty String.compare,nm)
	 val aps = List.concat (List.map holCheckTools.find_aps fl)
     in if (HOLset.numItems nms=List.length p)
	     then if List.length p>0
		  then
		      if List.foldl (fn (t,v) => Lexis.allowed_term_constant t andalso v) true nm
		      then if null aps orelse List.foldl (fn (f,v) => is_pabs f andalso v) true aps
			   then if null aps orelse List.foldl (fn ((s,p),v) => is_bool_var p andalso v) true (List.map dest_pabs aps)
				then if null aps orelse fst(List.foldl (fn ((s,p),(v,st)) => (Term.compare(s,st)=EQUAL andalso v,st))
						       (true,fst (dest_pabs (hd aps))) (List.map dest_pabs aps))
				     then ()
				     else failwith ("modelTools.set_props: different state tuples used in atomic propositions")
				else failwith ("modelTools.set_props: atomic proposition value must be a boolean variable")
			   else failwith ("modelTools.set_props: atomic proposition is not a paired abstraction")
		      else  failwith ("modelTools.set_props: property names must be legal HOL constant names")
		  else failwith ("modelTools.set_props: no properties specified")
	else failwith ("modelTools.set_props: property names are not unique") end;
    {init= #init(m),trans= #trans(m),ric= #ric(m),name= #name(m),vord= #vord(m),
     state= #state(m),props= SOME p,results= #results(m),ic= #ic(m),flags = #flags(m)})

fun set_results res (m:model)  =
    {init= #init(m),trans= #trans(m),ric= #ric(m),name= #name(m),vord= #vord(m),
     state= #state(m),props= #props(m),results = SOME res,ic= #ic(m),flags = #flags(m)}

fun set_ic ic (m:model)  =
    {init= #init(m),trans= #trans(m),ric= #ric(m),name= #name(m),vord= #vord(m),
     state= #state(m),props= #props(m),results= #results(m) ,ic=SOME ic,flags = #flags(m)}

fun set_flag_abs abs (m:model) =
    {init= #init(m),trans= #trans(m),ric= #ric(m),name= #name(m),vord= #vord(m),
     state= #state(m),props= #props(m),results= #results(m) ,ic= #ic(m),
     flags={abs=abs}}

fun add_trans t (m:model) = (*FIXME: expose this (need more infrastructure to handle invalidation of results since model has changed) *)
    let val t' = #trans(m)
    in if isSome t'
       then {init= #init(m),trans= SOME (t::(valOf t')),ric= #ric(m),name= #name(m),vord= #vord(m),
	     state= #state(m),props= #props(m),results= #results(m),ic= #ic(m),flags = #flags(m)}
       else {init= #init(m),trans= SOME [t],ric= #ric(m),name= #name(m),vord= #vord(m),
	     state= #state(m),props= #props(m),results= #results(m),ic= #ic(m),flags = #flags(m)}
    end

fun add_prop p (m:model)  =
    let val p' = #props(m)
    in if isSome p'
       then {init= #init(m),trans=  #trans(m),ric= #ric(m),name= #name(m),vord= #vord(m),
	     state= #state(m),props= SOME (p::(valOf p')),results= #results(m),ic= #ic(m),flags = #flags(m)}
       else {init= #init(m),trans=  #trans(m),ric= #ric(m),name= #name(m),vord= #vord(m),
	     state= #state(m),props= SOME [p],results= #results(m),ic= #ic(m),flags = #flags(m)}
    end

(* destruction (does not return flags) *)

fun dest_model m = (get_init m,get_trans m,get_flag_ric m,get_name m,get_vord m,
		    get_state m,get_props m,get_results m,get_ic m)

(* unlazify *)

fun prove_model (m:model) =
    let val res = get_results m
    in if isSome res
       then set_results (List.map (fn r => if isSome (#2 r)
					   then let val (tb,th,tr) = r
						in (lazyTools.prove_ltb tb,SOME (lazyTools.prove_lthm (valOf th)),tr) end
					   else r)
				  (valOf res)) m
       else m
    end

end
end
