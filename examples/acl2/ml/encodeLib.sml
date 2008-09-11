structure encodeLib :> encodeLib =
struct 

open Thm Term Type boolSyntax Parse Conv Rewrite Drule 
open Tactic Tactical pairLib numLib polytypicLib
open Binarymap List Lib
open boolTheory pairTheory listTheory combinTheory

open bossLib metisLib;

(*****************************************************************************)
(* construct_bottom_value : (hol_type -> bool) -> term -> hol_type -> term   *)
(*     Given a predicate to indicate stopping, and a stop term, constructs   *)
(*     the first non-recursive constructor of the type given.                *)
(*                                                                           *)
(*     Eg. construct_bottom_value (curry op= bool) F                         *)
(*                   ``:bool # (bool + bool)`` = ``(F,INL F)``               *)
(*                                                                           *)
(* target_bottom_value : hol_type -> term -> hol_type -> term                *)
(*     Constructs the term using 'ARB' values, then replaces them with the   *)
(*     given term once complete.                                             *)
(*                                                                           *)
(*     Eg. target_bottom_value bool F ``:'a # ('b + 'c)`` = ``(F,INL F)``    *)
(*                                                                           *)
(*****************************************************************************)

local
exception Bottom;
fun tryfind b f [] = if b then raise Bottom else raise Empty
  | tryfind b f (x::xs) = 
  (f x) handle Empty => tryfind b f xs
     	     | Bottom => tryfind true f xs
fun match term t = inst (match_type (snd (strip_fun (type_of term))) t) term
fun construct_bottom_value_n 0 p xvar _ = raise Bottom
  | construct_bottom_value_n n p xvar t = 
    if p t then match xvar t
       else let val cs = [match (get_source_function_const t "bottom-cons") t]
       	    	         handle _ => (constructors_of t handle e => [])
            in  tryfind false
       	    	(fn c => full_beta (list_mk_comb(c,
			map (construct_bottom_value_n (n - 1) p xvar) 
			(fst (strip_fun (type_of c))))))  cs
            end
fun itdeep f n = f n handle Bottom => itdeep f (n + 1)
fun check value t = 
    if type_of value = t then value
       else raise (mkDebugExn "construct_bottom_value"
       	    ("Constructed a term of type: " ^ type_to_string (type_of value) ^ 
	     "\nwhen a value of type: " ^ type_to_string t ^ 
	     "\nshould have been returned!!"))
in
fun construct_bottom_value p xvar t = 
    check (itdeep (fn n => construct_bottom_value_n n p xvar t) 0
           handle Empty => raise (mkStandardExn "construct_bottom_value"
    	        ("Could not find bottom values for all sub-types of "
	         ^ type_to_string t))
                | e => wrapException "construct_bottom_value" e) t
end;

fun target_bottom_value target bottom_target t = 
let val b1 = construct_bottom_value is_vartype (mk_arb alpha) t
    val arbs = HolKernel.find_terms is_arb b1
    val types = mk_set (map type_of arbs)
    val b2 = inst (map (fn t => t |-> target) types) b1
in
    subst [mk_arb target |-> bottom_target] b2  
end

(*****************************************************************************)
(* set_bottom_value : hol_type -> term -> unit                               *)
(*    Set the bottom value for the type given, this is only required for     *)
(*    non-recursive types.                                                   *)
(*                                                                           *)
(*****************************************************************************)

fun set_bottom_value t term =
   add_source_function_precise 
       t "bottom-cons" 
       {const = term, definition = TRUTH,induction = NONE}
   handle e => wrapException "set_bottom_value" e

(*****************************************************************************)
(* Generation of the encoding functions                                      *)
(*                                                                           *)
(* get_encode_type, get_decode_type, get_detect_type, get_fix_type           *)
(*                   : hol_type -> hol_type -> hol_type                      *)
(* get_map_type, get_all_type                                                *)
(*                   : hol_type -> hol_type                                  *)
(* mk_encode_var, mk_decode_var, mk_detect_var, mk_fix_var                   *)
(*                   : hol_type -> hol_type -> term                          *)
(* mk_map_var, mk_all_var                                                    *)
(*                   : hol_type -> term                                      *)
(*     Returns the type of an encoding, decoding, detecting or mapping       *)
(*     constant, and makes a variable for a prospective constant             *)
(*                                                                           *)
(* mk_encode_term        : hol_type -> hol_type -> term                      *)
(*     Makes a full encoding term for the translation given:                 *)
(*     Single constructor: enc (C a0 a1) = P enc0 enc1 (a0,a1)               *)
(*     Label constructors: enc Cn = nat n                                    *)
(*     Otherwise         : enc (Ci a0 a1) = P nat (P enc0 enc1) (i,a0,a1)    *)
(*                                                                           *)
(* mk_decode_term        : hol_type -> hol_type -> term                      *)
(*     Makes a full decoding term for the translation given:                 *)
(*     Single constructor: dec x = let (a,b) = D dec0 dec1 x in (C a b)      *)
(*     Label constructors: dec x = if dnat x = 0 then C0 else ....           *)
(*     Otherwise         : dec x =                                           *)
(*                             let (l,r) = D dnat I x                        *)
(*                             in  if l = 0 then                             *)
(*                                    let (a,b) = D dec0 dec1 r in (C a b)   *)
(*                                 else map dec0 dec1 (C nil nil)            *)
(*                                                                           *)
(* mk_detect_term        : hol_type -> hol_type -> term                      *)
(*     Makes a full decoding term for the translation given:                 *)
(*     Single constructor: dec x = P dec0 dec1 x                             *)
(*     Label constructors: dec x = bool (dnat x = 0 \/ ... \/ dnat x = n)    *)
(*     Otherwise         : dec x =                                           *)
(*                             bool (                                        *)
(*                                dbool (P dnat (K (bool T)) x)              *)
(*                             /\ let (l,r) = D dnat I x                     *)
(*                                in  (l = 0) /\ dbool (P det0 det1 r)       *)
(*                                    \/  ...)                               *)
(*                                                                           *)
(* mk_map_term           : hol_type -> term                                  *)
(*     Makes a full map function for the given type:                         *)
(*     Label constructors: map Li = Li                                       *)
(*     Otherwise         : map (C a0 .. an) = (map0 # .. # mapn) (a0,..,an)  *)
(*                                                                           *)
(* mk_all_term           : hol_type -> term                                  *)
(*     Makes a full all function for the given type:                         *)
(*     Label constructors: all Li = T                                        *)
(*     Otherwise         : all (C a0 .. an) = (all0 # .. # alln) (a0,..,an)  *) 
(*                                                                           *)
(* mk_fix_term          : hol_type -> hol_type -> term                       *)
(*     Single constructor: fix x = TP fix0 (TP ... fixn) .. ) x              *)
(*     Label constructors: fix x = x                                         *)
(*     Otherwise         : fix x =                                           *)
(*                             let (l,r) = D dnat I x                        *)
(*                             in  if l = 0 then                             *)
(*                                    pair nat I (TP fix0 (TP .. fixn) ) r   *) 
(*                                 else enc fix0 fix1 (C nil nil)            *)
(*                                                                           *)
(* get_encode_function, get_decode_function, get_detect_function,            *)
(* get_fix_function     : hol_type -> hol_type -> term                       *)
(* get_map_function      : hol_type -> term                                  *)
(*     Gets a fully instantiated term to translate the type                  *)
(*                                                                           *)
(* ENCODE_CONV, DECODE_CONV, DETECT_CONV, FIX_CONV : hol_type -> term -> thm *)
(*     Given the target type, each conv rewrites to convert a term given to  *)
(*     it by mk_..._term to a form suitable for split_function.              *)
(*                                                                           *)
(* CONSOLIDATE_CONV : (term -> term) -> term -> thm                          *)
(*     Given a conjunction of functions with instantiated bottom values, ie  *)
(*     of the form:                                                          *)
(*        f0 x = if .. then .. else B0 /\                                    *)
(*                  ...                                                      *)
(*        fn x = if .. then .. else Bn                                       *)
(*     Where B0...Bn may contain references to f0...fn and continually       *)
(*     rewrites with each definition to get B0'...Bn' that don't contain     *)
(*     references to f0 ... fn. Only works for 'decode' and 'fix'!           *)
(*                                                                           *)
(*                                                                           *)
(* mk_encodes, mk_decodes, mk_detects, mk_fixs : hol_type -> hol_type-> unit *)
(* mk_maps, mk_alls : hol_type -> unit                                       *)
(*     Generate the functions given. Shouldn't really be used, as it doesn't *)
(*     use the generator system, and will hence fail if functions are        *)
(*     missing.                                                              *)
(*                                                                           *)
(*****************************************************************************)

local
fun get_gen_type opr target t = 
	foldr (fn (x,t) => (opr (x,target)) --> t) (opr (t,target))
		(if is_vartype t then [] else snd (dest_type t))
in
fun get_encode_type target t = get_gen_type op--> target t 
		handle e => wrapException "get_encode_type" e
fun get_decode_type target t = get_gen_type (uncurry (C (curry op-->))) target t 
		handle e => wrapException "get_decode_type" e
fun get_detect_type target t = get_gen_type (fn (_,a) => a --> bool) target t
		handle e => wrapException "get_detect_type" e
fun get_map_type t = 
let	val tyvars = type_vars t
	fun gentvar t = (mk_vartype o curry op^ "'map_" o get_type_string) t
	val new_vars = map gentvar tyvars
	val t' = type_subst (map2 (curry op|->) tyvars new_vars) t
in
	foldr (fn ((x,y),t) => (x --> y) --> t) (t --> t')
		(if is_vartype t then [] else zip (snd (dest_type t)) (snd (dest_type t')))
end
fun get_all_type t = get_gen_type (fn (a,_) => a --> bool) t t
fun get_fix_type target t = get_gen_type (fn (_,_) => target --> target) target t
		handle e => wrapException "get_fix_type" e
end

local
fun mk_encode_string t = "encode" ^ (get_type_string t)
fun mk_decode_string t = "decode" ^ (get_type_string t)
fun mk_detect_string t = "detect" ^ (get_type_string t)
fun mk_map_string t    = "map"    ^ (get_type_string t)
fun mk_fix_string t = "fix" ^ (get_type_string t)
fun mk_all_string t = "all" ^ (get_type_string t)
fun mk_fix_string t = "fix" ^ (get_type_string t)
in
fun mk_encode_var target t = 
	mk_var(mk_encode_string t,get_encode_type target t)
	handle e => wrapException "mk_encode_var" e
fun mk_decode_var target t = 
	mk_var(mk_decode_string t,get_decode_type target t)
	handle e => wrapException "mk_decode_var" e
fun mk_detect_var target t = 
	mk_var(mk_detect_string t,get_detect_type target t)
	handle e => wrapException "mk_detect_var" e
fun mk_map_var t = 
	mk_var(mk_map_string t,get_map_type t)
	handle e => wrapException "mk_map_var" e
fun mk_fix_var target t = 
	mk_var(mk_fix_string t,get_fix_type target t)
	handle e => wrapException "mk_fix_var" e
fun mk_all_var t = 
	mk_var(mk_all_string t,get_all_type t)
	handle e => wrapException "mk_all_var" e
fun mk_fix_var target t = 
	mk_var(mk_fix_string t,get_fix_type target t)
	handle e => wrapException "mk_fix_var" e
end

local
fun new_const NONE const t = const
  | new_const (SOME match) const t = 
    safe_inst (match_type (match (type_of const)) t) const
in
fun get_encode_const target t = 
    if 	t = target 
    	then mk_const("I",t --> target)
    	else new_const (SOME (last o fst o strip_fun))
    	     	       (get_coding_function_const target t "encode") t
    handle e => wrapException "get_encode_const" e
fun get_decode_const target t = 
    if t = target 
       then mk_const("I",target --> t)
       else new_const (SOME (snd o strip_fun))
    	 	      (get_coding_function_const target t "decode") t
    handle e => wrapException "get_decode_const" e;
fun get_map_const t = 
    new_const (SOME (last o fst o strip_fun)) 
    	      (get_source_function_const t "map") t
    handle e => wrapException "get_map_const" e;
fun get_fix_const target t = 
    if t = target 
       then mk_const("I",target --> t)
       else new_const NONE
       	    	      (get_coding_function_const target t "fix") t
   handle e => wrapException "get_fix_const" e;
fun get_all_const t = 
    new_const (SOME (last o fst o strip_fun)) 
    	      (get_source_function_const t "all") t
    handle e => wrapException "get_all_const" e;
fun get_detect_const target t = 
    if t = target 
       then mk_comb(mk_const("K",bool --> target --> bool),T)
       else new_const NONE (get_coding_function_const target t "detect") t
    handle e => wrapException "get_detect_const" e
end

local
fun fix_base basetype term = 
let val types = set_diff (type_vars_in_term term) (type_vars basetype)
in  inst (map (fn x => x |-> gen_tyvar()) types) term
end;
fun imk_comb (main,p) = 
    mk_comb(inst (match_type (fst (dom_rng (type_of main))) (type_of p)) main,p)
val is_the_value_type = can (match_type (type_of boolSyntax.the_value))
fun typevars_lr t = 
    if is_vartype t then [t]
       else flatten (map typevars_lr (snd (dest_type t)));
fun mk_the_value t = 
    inst (match_type (type_of the_value) (mk_type("itself",[t]))) the_value;
fun get_function fconst fexists mvar t = 
let val basetype = (most_precise_type fexists t) 
    	handle _ => (if is_vartype t then t else base_type t)
    val base = fconst basetype handle _ => mvar t
    val params = set_diff (typevars_lr basetype) [t]
    val match = match_type basetype t
    val param_list = map (type_subst match) params
    val insted = inst match (fix_base basetype base)
 in
    if not (is_vartype t)
       then foldl (fn (a,t) => 
    	    	  imk_comb(t,get_function fconst fexists mvar a) handle _ => 
		  imk_comb(t,mk_the_value a) handle _ => t)
    	  insted param_list
       else base
end
in
fun get_encode_function target t = 
    get_function (get_encode_const target)
    		 (C (exists_coding_function_precise target) "encode")
		 (mk_encode_var target) t
	handle e => wrapException "get_encode_function" e
fun get_decode_function target t = 
    get_function (get_decode_const target)
    		 (C (exists_coding_function_precise target) "decode")
		 (mk_decode_var target) t
	handle e => wrapException "get_decode_function" e
fun get_detect_function target t = 
    get_function (get_detect_const target)
    		 (C (exists_coding_function_precise target) "detect")
		 (mk_detect_var target) t
	handle e => wrapException "get_detect_function" e
fun get_map_function t = 
    get_function get_map_const
    		 (C exists_source_function_precise "map")
		 mk_map_var t
	handle e => wrapException "get_map_function" e
fun get_fix_function target t = 
    get_function (get_fix_const target)
    		 (C (exists_coding_function_precise target) "fix")
		 (mk_fix_var target) t
    handle e => wrapException "get_fix_function" e
fun get_all_function t = 
     get_function get_all_const
    		 (C exists_source_function_precise "all")
		 mk_all_var t
	handle e => wrapException "get_all_function" e
end

local
fun mk_detect_constructor_ns rest target C = 
let	val (list,_) = strip_fun (type_of C)
	val vars = map (mk_var o (implode o base26 ## I)) (enumerate 0 list)
in
	mk_comb(get_detect_function target (list_mk_prod list),rest)
end
fun mk_detect_constructor rest target C T = 
	if can dom_rng (type_of C) then mk_detect_constructor_ns rest target C else T
fun mk_detect_res_term label rest target t constructors T = 
	list_mk_cond 
		(map (fn (a,b) => (mk_eq(label,numLib.term_of_int a),
			mk_detect_constructor rest target b T)) (enumerate 0 constructors))
		F
fun mk_detect_term_label (p,x) target t constructors = 
let	val dnat = get_decode_function target num
	val rnat = get_detect_function target num
in
	mk_forall(x,mk_eq(mk_comb(get_detect_function target t,x),
		mk_cond(mk_comb(rnat,x),
			mk_detect_res_term (mk_comb(dnat,x)) x target t constructors T,
			F)))
end
fun mk_detect_term_all (p,x) target t constructors = 
let	val dnat = get_detect_function target num
	val label = mk_var("l",num)
	val rest = mk_var("r",target)
	val null = mk_comb(get_encode_function target bool,F)
in
	list_mk_forall(snd (strip_comb (get_detect_function target t)),
		mk_forall(x,mk_eq(mk_comb(get_detect_function target t,x),
		mk_cond(p,pairSyntax.mk_anylet (
				[(mk_pair(label,rest),mk_comb(get_decode_function target (mk_prod(num,target)),x))],
				mk_detect_res_term label rest target t constructors (mk_eq(rest,null))),
			F))))
end
fun mk_detect_term_single (p,x) target t constructor = 
let	val t' = (mk_type o (I ## map (K target)) o dest_type) t
	val p = get_detect_function target t'
in
	list_mk_forall(snd (strip_comb (get_detect_function target t)),
		mk_forall(x,mk_eq(mk_comb(get_detect_function target t,x),mk_detect_constructor x target constructor T)))
end
in
fun mk_detect_term target t = 
let	val t' = base_type t  handle e => wrapException "mk_detect_term" e
	val constructors = constructors_of t'  handle e => wrapException "mk_detect_term" e
	val x = mk_var("x",target)
	val p = mk_comb(get_detect_function target (mk_prod(num,target)),x)
in
	if 	all (not o can dom_rng o type_of) constructors
	then	mk_detect_term_label (p,x) target t' constructors
		handle e => wrapException "mk_detect_term (label)" e
	else	if 	length constructors = 1
		then 	mk_detect_term_single (p,x) target t' (hd constructors) 
			handle e => wrapException "mk_detect_term (single)" e
		else	mk_detect_term_all (p,x) target t' constructors
			handle e => wrapException "mk_detect_term" e
end
end

local
fun full_bottom_value target bottom_target t = 
let val bottom = target_bottom_value target bottom_target t
    val mapf = get_map_const t
    val decodef = get_decode_function target t
    val map_function = list_imk_comb(mapf,snd (strip_comb decodef))
    val bottom' = inst (match_type (type_of bottom)
    		       		(fst (dom_rng (type_of map_function)))) bottom
in
    mk_comb(map_function,bottom')    		       		   
end handle e => wrapException "full_bottom_value" e
fun mk_decode_constructor_ns rest target C = 
let	val (list,_) = strip_fun (type_of C)
	val vars = map (mk_var o (implode o base26 ## I)) (enumerate 0 list)
in
	pairSyntax.mk_anylet (
		[(list_mk_pair vars,mk_comb(get_decode_function target (list_mk_prod list),rest))],
		(list_mk_comb(C,vars)))
end
fun mk_decode_constructor rest target C = 
	if can dom_rng (type_of C) then mk_decode_constructor_ns rest target C else C
fun mk_decode_res_term label rest target t constructors bottom = 
	list_mk_cond 
		(map (fn (a,b) => (mk_eq(label,numLib.term_of_int a),
			mk_decode_constructor rest target b)) (enumerate 0 constructors))
		bottom
fun mk_decode_term_label (p,x) target t constructors = 
let	val dnat = get_decode_function target num
	val rnat = get_detect_function target num
	val bottom = hd constructors
in
	mk_forall(x,mk_eq(mk_comb(get_decode_function target t,x),
		mk_cond(mk_comb(rnat,x),
			mk_decode_res_term (mk_comb(dnat,x)) x target t constructors bottom,
			hd (constructors))))
end
fun mk_decode_term_all (p,x) target t constructors = 
let	val dnat = get_decode_function target num
	val label = mk_var("l",num)
	val rest = mk_var("r",target)
	val bottom = full_bottom_value target (#bottom(get_translation_scheme target)) t
in
	list_mk_forall(snd (strip_comb (get_decode_function target t)),
		mk_forall(x,mk_eq(mk_comb(get_decode_function target t,x),
		mk_cond(p,pairSyntax.mk_anylet (
				[(mk_pair(label,rest),mk_comb(get_decode_function target (mk_prod(num,target)),x))],
				mk_decode_res_term label rest target t constructors bottom),
			bottom))))
end
fun mk_decode_term_single (p,x) target t constructor = 
let	val t' = (mk_type o (I ## map (K target)) o dest_type) t
	val p = get_detect_function target t'
in
	list_mk_forall(snd (strip_comb (get_decode_function target t)),
		mk_forall(x,mk_eq(mk_comb(get_decode_function target t,x),
		mk_cond(mk_comb(p,x),
			mk_decode_constructor x target constructor,
			full_bottom_value target (#bottom(get_translation_scheme target)) t))))
end
in
fun mk_decode_term target t = 
let	val t' = base_type t  handle e => wrapException "mk_decode_term" e
	val constructors = constructors_of t'  handle e => wrapException "mk_decode_term" e
	val x = mk_var("x",target)
	val p = mk_comb(get_detect_function target (mk_prod(num,target)),x)
in
	if 	all (not o can dom_rng o type_of) constructors
	then	mk_decode_term_label (p,x) target t' constructors
		handle e => wrapException "mk_decode_term (label)" e
	else	if 	length constructors = 1
		then 	mk_decode_term_single (p,x) target t' (hd constructors) 
			handle e => wrapException "mk_decode_term (single)" e
		else	mk_decode_term_all (p,x) target t' constructors
			handle e => wrapException "mk_decode_term" e
end
end

local
fun mk_fix_constructor_ns all target C = 
let	val (list,_) = strip_fun (type_of C)
	val vars = map (mk_var o (implode o base26 ## I)) (enumerate 0 list)
in
	mk_comb(get_fix_function target (list_mk_prod (num::list)),all)
end
fun mk_fix_constructor all target dead n C = 
	if can dom_rng (type_of C) 
		then mk_fix_constructor_ns all target C 
		else mk_comb(get_encode_function target (mk_prod(num,bool)),
			mk_pair(numLib.term_of_int n,F))
fun mk_fix_res_term label all target constructors dead bottom = 
	list_mk_cond 
		(map (fn (a,b) => (mk_eq(label,numLib.term_of_int a),
			mk_fix_constructor all target dead a b)) (enumerate 0 constructors))
		bottom
fun mk_fix_term_label x target t constructors = 
let	val dnat = get_decode_function target num
	val rnat = get_detect_function target num
	val enat = get_encode_function target num
in
	mk_forall(x,mk_eq(mk_comb(get_fix_function target t,x),
		mk_cond(mk_comb(rnat,x),
			list_mk_cond (map (fn (a,b) => (mk_eq(mk_comb(dnat,x),numLib.term_of_int a),x)) (enumerate 0 constructors))
					(mk_comb(enat,zero_tm)),
			mk_comb(get_encode_function target num,zero_tm))))
end
fun mk_fix_term_all (p,x) target t constructors dead = 
let val dnat = get_fix_function target num
    val label = mk_var("l",num)
    val rest = mk_var("r",target)
    val t' = (mk_type o (I ## map (K target)) o dest_type) t
    val instit = inst (map (fn v => v |-> target) (type_vars t))
    val enc1 = instit (get_encode_function target t)
    val enc2 = subst (map (fn v => instit (get_encode_function target v) |-> 
    	       	     	      get_fix_function target v) (type_vars t)) enc1
    val bottom = rimk_comb(enc2,target_bottom_value target dead t)
in
    list_mk_forall(snd (strip_comb (get_fix_function target t)),
        mk_forall(x,mk_eq(mk_comb(get_fix_function target t,x),
	    mk_cond(p,pairSyntax.mk_anylet (
	        [(mk_pair(label,rest),
		  mk_comb(get_decode_function target (mk_prod(num,target)),x))],
		  mk_fix_res_term label x target constructors dead bottom),
		  bottom))))
end
fun mk_fix_term_single x target t constructor dead = 
let val t' = (mk_type o (I ## map (K target)) o dest_type) t
    val p = get_detect_function target t'
    val instit = inst (map (fn v => v |-> target) (type_vars t))
    val enc1 = instit (get_encode_function target t)
    val enc2 = subst (map (fn v => 
    	       	     	  instit (get_encode_function target v) |-> 
			  get_fix_function target v) (type_vars t)) enc1
    val bottom = rimk_comb(enc2,target_bottom_value target dead t)
    val list = fst (strip_fun (type_of constructor))
in
    list_mk_forall(snd (strip_comb (get_fix_function target t)),
        mk_forall(x,mk_eq(mk_comb(get_fix_function target t,x),
	    mk_cond(mk_comb(p,x),
	        mk_comb(get_fix_function target (list_mk_prod list),x),
		    bottom))))
end
in
fun mk_fix_term target t = 
let val t' = base_type t  handle e => wrapException "mk_fix_term" e
    val constructors = constructors_of t'
    	handle e => wrapException "mk_fix_term" e
    val x = mk_var("x",target)
    val p = mk_comb(get_detect_function target (mk_prod(num,target)),x)
    val dead = #bottom (get_translation_scheme target)
in
    if all (not o can dom_rng o type_of) constructors
       then mk_fix_term_label x target t' constructors
       	    handle e => wrapException "mk_fix_term (label)" e
       else if length constructors = 1
       	       then mk_fix_term_single x target t' (hd constructors) dead
		    handle e => wrapException "mk_fix_term (single)" e
               else mk_fix_term_all (p,x) target t' constructors dead
		    handle e => wrapException "mk_fix_term" e
end
end

local
fun mk_avar (n,t) = (mk_var ("a_" ^ Int.toString n,t),t)
fun single_pair num target t cnst = 
let val ts = fst (strip_fun (type_of cnst))
    val tvs = map mk_avar (enumerate 0 ts)
    val (vars,types) = 
    	unzip (case num
  	      of NONE => tvs
  	      |  SOME x => (case tvs
    	      	      	    of [] => [(numLib.term_of_int x,``:num``),
			              (``F``,``:bool``)]
    		            |  list => (numLib.term_of_int x,``:num``)::list))
in
    list_mk_forall(map fst tvs,
    list_mk_forall(map (get_encode_function target) (snd (dest_type t)),
        mk_eq(mk_comb(get_encode_function target t,
	              list_mk_comb(cnst,map fst tvs)),
              if vars = []
	      	 then mk_comb(get_encode_function ``:num`` target,``0n``)
  		 else (mk_comb(get_encode_function target
		                  (pairLib.list_mk_prod types),
			       pairLib.list_mk_pair vars)))))
end
fun mk_encode_term_single target t cnst = single_pair NONE target t cnst
fun mk_encode_term_label target t cnsts = 
let val num = get_encode_function target ``:num``
    val func = get_encode_function target t
in
    list_mk_conj (map (fn (n,c) => 
    		 mk_eq(mk_comb(func,c),mk_comb(num,numLib.term_of_int n)))
		 (enumerate 0 cnsts))
end
fun mk_encode_term_all target t cnsts =
    list_mk_conj (map (fn (n,c) => single_pair (SOME n) target t c)
    		 (enumerate 0 cnsts))
in
fun mk_encode_term target t = 
let val t' = base_type t handle e => wrapException "mk_encode_term" e
    val constructors = constructors_of t'
     handle e => wrapException "mk_encode_term" e
in
    if all (not o can dom_rng o type_of) constructors 
       then mk_encode_term_label target t' constructors 
            handle e => wrapException "mk_encode_term (label)" e
       else if length constructors = 1
               then mk_encode_term_single target t' (hd constructors) 
             handle e => wrapException "mk_encode_term (single)" e
               else mk_encode_term_all target t' constructors
             handle e => wrapException "mk_encode_term" e
end
end;

fun mk_map_term t = 
let val cs = constructors_of t
    val args = map (fn c => map (fn (n,t) => 
		mk_var(implode (base26 n),t)) 
		(enumerate 0 (fst (strip_fun (type_of c))))) cs
    val combs = map2 (curry list_mk_comb) cs args
    val func = get_map_function t
    val funs = snd (strip_comb func)
    fun imk_eq (a,b) = mk_eq(a,inst (match_type (type_of b) (type_of a)) b)
in
    list_mk_conj (map (fn c => list_mk_forall(funs,
		list_mk_forall(snd (strip_comb c),imk_eq(mk_comb(func,c),
		((list_imk_comb o (I ## map (fn a => 
			mk_comb(get_map_function (type_of a),a)))) 
			(strip_comb c))))))
		combs) 
end handle e => wrapException "mk_map_term" e

fun mk_all_term t = 
let	val cs = constructors_of t
	val args =  map (fn c => map (fn (n,t) => 
		mk_var(implode (base26 n),t)) (enumerate 0 (fst (strip_fun (type_of c))))) cs
	val combs = map2 (curry list_mk_comb) cs args
	val func = get_all_function t
	val funs = snd (strip_comb func)
in
	list_mk_conj (map2 (fn a => fn c => list_mk_forall(funs,
			list_mk_forall(a,mk_eq(mk_comb(func,c),
				case a of 
				[] => T
				| a => mk_comb(get_all_function (list_mk_prod(map type_of a)),list_mk_pair a)))))
	args combs) 
end	handle e => wrapException "mk_all_term" e

fun ENCODE_CONV pair_thm term = 
let	val _ = type_trace 2 "->ENCODE_CONV\n"
	val fa_pairs = if (!debug) then 
			bucket_alist (zip	(map (repeat rator o lhs o snd o strip_forall) (strip_conj term))
						(map (type_of o rand o rhs o snd o strip_forall) (strip_conj term))) 
			handle _ => []
			else []
	val t = mk_prod(numLib.num,alpha)
	val _ = case (total (first (fn (a,b) => exists (can (match_type t)) b andalso 
			exists (not o can (match_type t)) b)) fa_pairs)
		of SOME (fname,_) => raise (mkDebugExn "ENCODE_CONV" 
					("Function clause: " ^ term_to_string fname ^ 
					 " converts to a mixture of labelled pairs and non-labelled pairs"))
		|  NONE => ()
	fun drop_all term = ((REWR_CONV pair_thm THENC RAND_CONV drop_all) ORELSEC ALL_CONV) term
in
	EVERY_CONJ_CONV (STRIP_QUANT_CONV (RAND_CONV drop_all)) term
	handle UNCHANGED => REFL term handle e => wrapException "PAIR_CONV (encode)" e
end;

local
fun rws l = RATOR_CONV (RATOR_CONV (RAND_CONV (REWRITE_CONV l)))
fun DC target term = 
let	val r = rhs term
	val pair_def = get_coding_function_def target (mk_prod(alpha,beta)) "detect"
	val (p,a,b) = dest_cond r handle e => raise UNCHANGED
	val (left,right) = dest_eq (snd (strip_forall (concl pair_def)))
	val (xp,_,_) = dest_cond right
in
	if can (match_term left) p then
		let 	val thm1 = rws [ASSUME xp,pair_def,COND_EXPAND] (rhs term);
			val thm2 = (rws [ASSUME (mk_neg xp),pair_def,COND_EXPAND] THENC PURE_REWRITE_CONV [COND_CLAUSES]) (rhs term);
		in
			AP_TERM (rator term) (SYM (RIGHT_CONV_RULE (REWR_CONV COND_ID) (MATCH_MP COND_CONG (LIST_CONJ [REFL xp,DISCH_ALL (SYM thm1),DISCH_ALL (SYM thm2)]))))
		end
	else	REFL term
end handle UNCHANGED => REFL term | e => wrapException "DC" e
fun SC target term = 
let	val (p,a,b) = dest_cond (rhs term)
	val pair_def = get_coding_function_def target (mk_prod(alpha,beta)) "decode"
	val pthm = PURE_REWRITE_RULE [COND_CLAUSES,ASSUME p] (PART_MATCH (rand o rator o rator o rhs) pair_def p)
in
	AP_TERM (rator term) (MATCH_MP COND_CONG (LIST_CONJ 
		[REFL p,DISCH p (RATOR_CONV (RAND_CONV (RAND_CONV (REWR_CONV pthm) THENC PURE_REWRITE_CONV [I_THM] THENC pairLib.let_CONV)) a),DISCH (mk_neg p) (REFL b)]))
end handle e => NO_CONV term
fun FIXC target term = 
let	val (p,a,b) = dest_cond (rhs term)
	val pair_def = get_coding_function_def target (mk_prod(alpha,beta)) "fix"
	val pthm = REWRITE_RULE [I_THM] (PART_MATCH (rator o lhs) (PURE_REWRITE_RULE [COND_CLAUSES,ASSUME p] (PART_MATCH (rand o rator o rator o rhs) pair_def p))
				(get_fix_function target (mk_prod(num,alpha))))
in
	AP_TERM (rator term) (MATCH_MP COND_CONG (LIST_CONJ 
		[REFL p,DISCH p (PURE_REWRITE_CONV [pthm] a),DISCH (mk_neg p) (REFL b)]))
end
in
fun DETECT_CONV target term = 
	(type_trace 2 "->DETECT_CONV\n" ; 
	EVERY_CONJ_CONV (STRIP_QUANT_CONV (DC target THENC TRY_CONV (SC target))) term handle e => wrapException "DETECT_CONV" e)
fun DECODE_CONV target term = 
	(type_trace 2 "->DECODE_CONV\n" ; 
	EVERY_CONJ_CONV (STRIP_QUANT_CONV (DC target THENC TRY_CONV (SC target))) term handle e => wrapException "DECODE_CONV" e)
fun FIX_CONV target term = 
	(type_trace 2 "->FIX_CONV\n" ; 
	EVERY_CONJ_CONV (STRIP_QUANT_CONV (DC target THENC TRY_CONV (SC target) THENC REWRITE_CONV [K_THM] THENC TRY_CONV (FIXC target))) term handle e => wrapException "FIX_CONV" e)
end;

fun mk_encodes target t = 
let	val _ = if exists_coding_function target t "encode" then
		raise (mkStandardExn "mk_encodes" 
			("Encoder function for translation: " ^ type_to_string t ^ " --> " ^ type_to_string target ^ 
			 " already exists.")) else ()
	val _ = type_trace 1 
		("Generating encoding function for: " ^ type_to_string t ^ " --> " ^ type_to_string target ^ "\n")
in
	mk_coding_functions 
			"encode"
			(mk_encode_term target)
			(get_encode_function target)
			(ENCODE_CONV (get_coding_function_def target (mk_prod(alpha,beta)) "encode"))
			REFL
			target
			(base_type t) handle e => wrapException "mk_encodes" e
end;

val CONSOLIDATE_CONV_data = ref (NONE:((term -> term) * term) option);

local
val PTAC = HO_MATCH_MP_TAC (METIS_PROVE [] ``(A = B) /\ (C = D) ==> (P A C = P B D)``) THEN CONJ_TAC;
fun AP_TAC funcs (ag as (assums,goal)) = 
	if (C mem funcs o repeat rator o lhs) goal orelse (C mem funcs o repeat rator o rhs) goal then ALL_TAC ag else 
		(TRY ((AP_TERM_TAC ORELSE AP_THM_TAC ORELSE PTAC) THEN AP_TAC funcs)) ag
in
fun CONSOLIDATE_CONV rfix function =
let 	val _ = type_trace 2 "->CONSOLIDATE_CONV\n"
	val _ = CONSOLIDATE_CONV_data := SOME (rfix,function)
	val clauses = strip_conj function
	val ends = map ((fn (a,b,c) => c) o dest_cond o rhs o snd o strip_forall) clauses
	val target = (type_of o rand o lhs o snd o strip_forall o hd) clauses
	val dead_thm = #bottom_thm (get_translation_scheme target)
	val subs = (mk_type o (I ## map (fn a => if a = target then gen_tyvar() else a)) o dest_type)
	val ts = (mk_prod(num,target))::mk_set (filter (not o is_vartype) 
		(flatten (mapfilter (map snd o reachable_graph (uncurried_subtypes) o subs o type_of o rfix) ends)))
	val maps = map (fn x => (generate_source_function "map" (base_type x) ; C get_source_function_def "map" x)) ts
	val encs = map (fn x => (generate_coding_function target "encode" (base_type x) ; 
				get_coding_function_def target x "encode")) ts
	val decs = flatten (map CONJUNCTS (mapfilter (C (get_coding_function_def target) "decode") ts))
	val fixs = map (REWRITE_RULE encs) (flatten (map CONJUNCTS (mapfilter (C (get_coding_function_def target) "fix") ts)))
	val deads = dead_thm::mapfilter (generate_coding_theorem target "detect_dead" o base_type) ts;
	val hos = map ASSUME clauses
	val results = map (fn term => REPEATC (CHANGED_CONV (REWRITE_CONV maps THENC REWRITE_CONV encs THENC 
				ONCE_REWRITE_CONV decs THENC ONCE_REWRITE_CONV fixs
				THENC ONCE_REWRITE_CONV hos THENC REWRITE_CONV deads)) term 
				handle UNCHANGED => REFL term) ends
	val full = ONCE_DEPTH_CONV (FIRST_CONV (map REWR_CONV results)) function
	val funcs = map (repeat rator o lhs o snd o strip_forall) (clauses @ map concl decs @ map concl fixs);
in
	prove(concl full,
	REWRITE_TAC encs THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
	REPEAT (
		FIRST [FIRST_ASSUM (CONV_TAC o LAND_CONV o REWR_CONV),CONV_TAC (LAND_CONV (FIRST_CONV (map REWR_CONV (fixs @ decs)))),ALL_TAC] THEN 
		FIRST [FIRST_ASSUM (CONV_TAC o RAND_CONV o REWR_CONV),CONV_TAC (RAND_CONV (FIRST_CONV (map REWR_CONV (fixs @ decs)))),ALL_TAC] THEN 
		TRY (MATCH_MP_TAC COND_CONG THEN REPEAT STRIP_TAC) THEN REWRITE_TAC deads THEN AP_TAC funcs THEN
		REWRITE_TAC maps THEN REWRITE_TAC encs THEN REWRITE_TAC (dead_thm::deads) THEN REWRITE_TAC (mapfilter TypeBase.one_one_of ts) THEN REPEAT CONJ_TAC))
end	handle e => wrapException "CONSOLIDATE_CONV" e
end

fun mk_decodes target t = 
let	val _ = if exists_coding_function target t "decode" then
		raise (mkStandardExn "mk_decodes" 
			("Decoder function for translation: " ^ type_to_string t ^ " --> " ^ type_to_string target ^ 
			 " already exists.")) else ()
	val _ = type_trace 1 
		("Generating decoding function for: " ^ type_to_string t ^ " --> " ^ type_to_string target ^ "\n")
in
	mk_target_functions 
			"decode"
			(mk_decode_term target)
			(get_decode_function target)
			(DECODE_CONV target)
			(CONSOLIDATE_CONV rand)
			target
			(base_type t) handle e => wrapException "mk_decodes" e
end;

fun mk_detects target t = 
let	val _ = if exists_coding_function target t "detect" then
		raise (mkStandardExn "mk_detects" 
			("Detector function for translation: " ^ type_to_string t ^ " --> " ^ type_to_string target ^ 
			 " already exists.")) else ()
	val _ = type_trace 1 
		("Generating detecting function for: " ^ type_to_string t ^ " --> " ^ type_to_string target ^ "\n")
in
	mk_target_functions 
			"detect"
			(mk_detect_term target)
			(get_detect_function target)
			(DETECT_CONV target)
			REFL
			target
			(base_type t) handle e => wrapException "mk_detects" e
end;

fun mk_maps t = 
let	val _ = if exists_source_function t "map" then
		raise (mkStandardExn "mk_maps" 
			("Map function for type: " ^ type_to_string t ^ " already exists.")) else ()
	val _ = type_trace 1 
		("Generating map function for: " ^ type_to_string t ^ "\n")
in
	mk_source_functions 
			"map"
			mk_map_term
			get_map_function
			REFL
			REFL
			(base_type t)
end;

fun mk_alls t = 
let	val _ = if exists_source_function t "all" then
		raise (mkStandardExn "mk_alls" 
			("All function for type: " ^ type_to_string t ^ " already exists.")) else ()
	val _ = type_trace 1 
		("Generating all function for: " ^ type_to_string t ^ "\n")
in
	mk_source_functions 
			"all"
			mk_all_term
			get_all_function
			(fn x => (EVERY_CONJ_CONV (STRIP_QUANT_CONV (RAND_CONV 
				(PURE_REWRITE_CONV [get_source_function_def (mk_prod(alpha,beta)) "all"])))) x 
				handle UNCHANGED => REFL x)
			REFL
			(base_type t)
end;

fun mk_fixs target t = 
let	val _ = if exists_coding_function target t "fix" then
		raise (mkStandardExn "mk_fixs" 
			("fix function for translation: " ^ type_to_string t ^ " --> " ^ type_to_string target ^ 
			 " already exists.")) else ()
	val _ = type_trace 1 
		("Generating fix function for: " ^ type_to_string t ^ " --> " ^ type_to_string target ^ "\n")
in
	mk_target_functions 
			"fix"
			(mk_fix_term target)
			(get_fix_function target)
			(FIX_CONV target)
			(CONSOLIDATE_CONV rand)
			target
			(base_type t) handle e => wrapException "mk_fixs" e
end;

(*****************************************************************************)
(* Generate conclusions for the various goals to be proven:                  *)
(*                                                                           *)
(* mk_encode_decode_map_conc  : hol_type -> hol_type -> term                 *)
(* mk_encode_detect_all_conc  : hol_type -> hol_type -> term                 *)
(* mk_decode_encode_fix_conc  : hol_type -> hol_type -> term                 *)
(* mk_encode_map_encode_conc  : hol_type -> hol_type -> term                 *)
(* mk_map_compose_conc        : hol_type -> term                             *)
(* mk_map_id_conc             : hol_type -> term                             *)
(* mk_all_id_conc             : hol_type -> term                             *)
(* mk_fix_id_conc             : hol_type -> hol_type -> term                 *)
(* mk_general_detect_conc     : hol_type -> hol_type -> term                 *)
(*                                                                           *)
(* mk_encode_decode_conc      : hol_type -> hol_type -> term                 *)
(* mk_decode_encode_conc      : hol_type -> hol_type -> term                 *)
(* mk_encode_detect_conc      : hol_type -> hol_type -> term                 *)
(*                                                                           *)
(*                                                                           *)
(*     Make the conclusions for the various theorems:                        *)
(*     ?- (decode f o encode g) = map (f o g)                                *)
(*     ?- (encode f o decode g) = fix (f o g)                                *)
(*     ?- (detect f o encode g) = all (f o g)                                *)
(*                                                                           *)
(*     ?- (encode f o map g) = encode (f o g)                                *)
(*     ?- (map f o map g) = map (f o g)                                      *)
(*                                                                           *)
(*     ?- map I = I                                                          *)
(*     ?- all (K T) = K T                                                    *)
(*     ?- (!x. f x = x) ==> (!x. fix f x = x)                                *)
(*                                                                           *)
(*     ?- !x. detect f g x ==> detect (K T) (K T) x                          *)
(*                                                                           *)
(*     ?- (!x. f (g x) = x) ==> !x. decode f (encode g x) = x                *)
(*     ?- (!x. p x ==> g (f x) = x) ==>                                      *)
(*                    !x. detect p x ==> encode g (decode f x) = x           *)
(*     ?- (!x. p (g x)) ==> !x. detect p (encode g x)                        *)
(*                                                                           *)
(*****************************************************************************)

fun get_hfuns term = 
    if is_comb term
       then flatten (map get_hfuns (op:: (strip_comb term))) 
       else [term];

fun type_vars_avoiding_itself function t =
    set_diff (type_vars t)
    	     (map (hd o snd o dest_type o type_of)
    	     (filter (can (match_term the_value)) (get_hfuns function)));

fun check_function gf t = 
let val term = gf t
    val hfuns = get_hfuns term
    val vars = filter is_var hfuns
    val values = filter (polymorphic o type_of) 
    	       	 	(filter (can (match_term the_value)) hfuns)
in
    if length (mk_set (vars @ values)) > length (type_vars t)
       then raise (mkDebugExn "check_function"
       	    	  ("The function term: " ^ term_to_string term ^ 
		  "\ncontains free-variables not derived from the type: " ^ 
		  type_to_string t))
       else term
end;

local
fun wrap e = wrapException "mk_encode_decode_map_conc" e
fun err s = raise (mkDebugExn "mk_encode_decode_map_conc"
("Unable to correctly instantiate type variables in " ^ s ^ " function"))
in
fun mk_encode_decode_map_conc target t = 
let val enc = check_function (get_encode_function target) t handle e => wrap e
    val dec = check_function (get_decode_function target) t handle e => wrap e
    val map_term = check_function get_map_function t  handle e => wrap e
    val safe_map_term = inst (map (fn v => v |-> gen_tyvar()) 
    		      	     	  (type_vars_in_term map_term)) map_term;
    val tvs = type_vars_avoiding_itself enc t
    val values = set_diff (type_vars t) tvs

    fun inst_from term start types = 
    	inst (map (fn (a,b) => 
	     	  b |-> mk_vartype (String.implode(#"'" :: base26 (a + start))))
		  (enumerate 0 types)) term;
    val enc' = inst_from (inst_from enc 0 tvs) (length tvs) values
    	       handle e => err "encode"
    val dec' = inst_from (inst_from dec (length tvs + length values) tvs)
    	       		 (length tvs) values handle e => err "decode"    
    val map' = inst (match_type (type_of safe_map_term) 
    	       	    		(fst (dom_rng (type_of enc')) --> 
				 snd (dom_rng (type_of dec')))) 
			safe_map_term handle e => err "map";

    val enc_vars = free_vars_lr enc'
    val dec_vars = free_vars_lr dec'
    val sub = map2 (curry op|->) 
    	      	   (free_vars_lr map') 
    	      	   (map2 (curry combinSyntax.mk_o) dec_vars enc_vars) 
	      handle e => wrap e
in
    list_mk_forall(enc_vars,
    list_mk_forall(dec_vars,mk_eq(combinSyntax.mk_o(dec',enc'),subst sub map')))
    handle e => wrap e
end
end

local
fun w s e = wrapException s e
fun mk_ring_conc left func1 func2 = 
let val sub = map2 (curry op|->) 
		   (free_vars_lr (if left then func1 else func2))
		   (map2 (curry combinSyntax.mk_o) (free_vars_lr func1) (free_vars_lr func2)) handle e => w "mk_ring_conc" e
	val tsubs = map (fn {redex,residue} => match_type (type_of redex) (type_of residue)) sub 
		handle e => w "mk_ring_conc" e
	val ins = C (foldl (uncurry inst)) tsubs  handle e => w "mk_ring_conc" e
	val sub' = map (fn {redex,residue} => ins redex |-> residue) sub  handle e => w "mk_ring_conc" e
in
	list_mk_forall(free_vars_lr func1,
	list_mk_forall(free_vars_lr func2,
		mk_eq((curry combinSyntax.mk_o) func1 func2,subst sub' (ins (if left then func1 else func2)))))
		 handle e => w "mk_ring_conc" e
end
in
fun mk_encode_map_encode_conc target t = 
let	val encf = check_function (get_encode_function target) t handle e => w "mk_encode_map_encode_conc" e
	val mapf = check_function get_map_function t handle e => w "mk_encode_map_encode_conc" e
	val encf' = inst (match_type (fst (dom_rng (type_of encf))) (snd (dom_rng (type_of mapf)))) encf
			 handle e => w "mk_encode_map_encode_conc" e
in
	mk_ring_conc true encf' mapf  handle e => w "mk_encode_map_encode_conc" e
end
fun mk_map_compose_conc t =
let	val map1 = check_function get_map_function t handle e => w "mk_map_compose_conc" e
	val map2 = inst (map (fn x => x |-> (mk_vartype o curry op^ "'map" o get_type_string) x)
			(type_vars (type_of map1))) map1 handle e => w "mk_map_compose_conc" e
	val map1' = inst (match_type (snd (dom_rng (type_of map1))) (fst (dom_rng (type_of map2)))) map1
			 handle e => w "mk_encode_map_encode_conc" e
in
	mk_ring_conc false map2 map1' handle e => w "mk_encode_map_encode_conc" e
end
end;

fun mk_decode_encode_fix_conc target t = 
let	val enc = check_function (get_encode_function target) t
	val dec = check_function (get_decode_function target) t
	val fix = check_function (get_fix_function target) t
	
	val enc_vars = free_vars_lr enc
	val dec_vars = free_vars_lr dec
	val sub = map2 (curry op|->) (free_vars_lr fix) (map2 (curry combinSyntax.mk_o) enc_vars dec_vars)
in
	list_mk_forall(enc_vars,
	list_mk_forall(dec_vars,
	mk_eq((curry combinSyntax.mk_o) enc dec,subst sub fix)))
end

fun mk_encode_detect_all_conc target t =
let	val enc = check_function (get_encode_function target) t
	val det = check_function (get_detect_function target) t
	val all = check_function get_all_function t
	val dbool = get_decode_function target bool

	val enc_vars = free_vars_lr enc
	val det_vars = free_vars_lr det
	val sub = map2 (curry op|->) (free_vars_lr all) (map2 (curry combinSyntax.mk_o) det_vars enc_vars)
in
	list_mk_forall(det_vars,
	list_mk_forall(enc_vars,mk_eq((curry combinSyntax.mk_o) det enc,subst sub all)))
end;
	
fun mk_map_id_conc t = 
let	val map_term = check_function get_map_function t
	val fvs = free_vars map_term
	val ty_sub = map (fn fv => snd (dom_rng (type_of fv)) |-> fst (dom_rng (type_of fv))) fvs
	val map' = inst ty_sub map_term
	val dub = fn t => fst (dom_rng t) --> fst (dom_rng t)
	val tm_sub = map (fn fv => (mk_var o (I ## dub) o dest_var) fv |-> mk_const("I",dub (type_of fv))) fvs
in
	mk_eq(subst tm_sub map',mk_const("I",type_of map'))
end

fun mk_all_id_conc t = 
let	val all_term = check_function get_all_function t
	val fvs = free_vars all_term
	fun mk_all_id t = mk_comb(mk_const("K",bool --> (t --> bool)),T)
in	mk_eq(subst (map (fn x => x |-> 
		mk_all_id (fst (dom_rng (type_of x)))) fvs) all_term,
		mk_all_id t)
end

fun mk_fix_id_conc target t = 
let val fix_term = check_function (get_fix_function target) t
    val det_term = check_function (get_detect_function target) t
    val tvs = type_vars_avoiding_itself fix_term t
    val hyps = map (mk_fix_id_conc target) (set_diff tvs [t])
    val x = mk_var("x",target)
    val e = mk_forall(x,mk_imp(mk_comb(det_term,x),
			mk_eq(mk_comb(fix_term,x),x)))
in
    if null hyps then e
    else mk_imp(list_mk_conj hyps,e)
end;

fun mk_general_detect_conc target t = 
let val p1 = check_function (get_detect_function target) t
    val t' = type_subst (map (fn v => v |-> target) 
    	     		     (type_vars_avoiding_itself p1 t)) t
    val p2 = check_function (get_detect_function target) t'
    val xvar = mk_var("x",target)
in
    mk_forall(xvar,
    list_mk_forall(free_vars p1,mk_imp(mk_comb(p1,xvar),mk_comb(p2,xvar))))
end;

local
fun wrap e = wrapException "mk_encode_decode_conc" e
in
fun mk_encode_decode_conc target t = 
let val encode = check_function (get_encode_function target) t
    	       	 handle e => wrap e
    val decode = check_function (get_decode_function target) t
    	       	 handle e => wrap e
    val var = mk_var("x",t)
    val conc = mk_forall(var,mk_eq(mk_comb(decode,mk_comb(encode,var)),var))
    	     handle e => wrap e
    val tvs = type_vars_avoiding_itself encode t
    val ante = map (snd o dest_imp o snd o strip_forall o 
    	       	   mk_encode_decode_conc target) (set_diff tvs [t])
in
    list_mk_forall(map (get_encode_function target) tvs,
    list_mk_forall(map (get_decode_function target) tvs,
    if is_vartype t then mk_imp(conc,conc) else
    if null ante then conc else mk_imp(list_mk_conj ante,conc)))
       handle e => wrap e
end
end

local 
fun wrap e = wrapException "mk_decode_encode_conc" e
in
fun mk_decode_encode_conc target t = 
let val encode = check_function (get_encode_function target) t
    	       	 handle e => wrap e
    val detect = check_function (get_detect_function target) t
    	       	 handle e => wrap e
    val decode = check_function (get_decode_function target) t
    	       	 handle e => wrap e
    val var = mk_var("x",target)
    val conc = mk_forall(var,mk_imp(mk_comb(detect,var),
			mk_eq(mk_comb(encode,mk_comb(decode,var)),var)))
			handle e => wrap e
    val tvs = type_vars_avoiding_itself encode t
    val ante = map (snd o dest_imp o snd o strip_forall o 
    	     mk_decode_encode_conc target) (set_diff tvs [t])
in
    list_mk_forall(map (get_encode_function target) tvs,
    list_mk_forall(map (get_decode_function target) tvs,
    list_mk_forall(map (get_detect_function target) tvs,
    if is_vartype t then mk_imp(conc,conc) else
    if null ante then conc else mk_imp(list_mk_conj ante,conc))))
       handle e => wrap e
end
end

local
fun wrap e = wrapException "mk_encode_detect_conc" e
in
fun mk_encode_detect_conc target t = 
let val encode = check_function (get_encode_function target) t
    	       	 handle e => wrap e
    val detect = check_function (get_detect_function target) t
    	       	 handle e => wrap e
    val var = mk_var("x",t)
    val conc = mk_forall(var,mk_comb(detect,mk_comb(encode,var)))
    	       handle e => wrap e
    val tvs = type_vars_avoiding_itself encode t
    val ante = map (snd o dest_imp o snd o strip_forall o 
    	       	   mk_encode_detect_conc target) (set_diff tvs [t])
in
    list_mk_forall(map (get_encode_function target) tvs,
    list_mk_forall(map (get_detect_function target) tvs,
    if is_vartype t then mk_imp(conc,conc) else
    if null ante then conc else mk_imp(list_mk_conj ante,conc))) 
	handle e => wrap e
end
end

(*****************************************************************************)
(* Rules to generate instantiated theorems from base-type theorems:          *)
(*                                                                           *)
(* FULL_ENCODE_DECODE_MAP_THM : hol_type -> hol_type -> thm                  *)
(* FULL_ENCODE_DETECT_ALL_THM : hol_type -> hol_type -> thm                  *)
(* FULL_ENCODE_MAP_ENCODE_THM : hol_type -> hol_type -> thm                  *)
(* FULL_DECODE_ENCODE_FIX_THM : hol_type -> hol_type -> thm                  *)
(* FULL_MAP_COMPOSE_THM : hol_type -> hol_type -> thm                        *)
(*     Create the theorem, eg:                                               *)
(*            |- map map o encode encode = encode encode                     *)
(*     from:                                                                 *)
(*            |- !f g. map f o encode g = encode (f o g)                     *)
(*     and    |- map o encode = encode                                       *)
(*                                                                           *)
(* FULL_MAP_ID_THM : hol_type -> thm                                         *)
(* FULL_ALL_ID_THM : hol_type -> thm                                         *)
(*     Create the theorem, eg:                                               *)
(*            |- map (map I) (map I) = I                                     *)
(*     from:  |- map I I = I    |- map I = I    |- map I = I                 *)
(*                                                                           *)
(* FULL_FIX_ID_THM : hol_type -> hol_type -> thm                             *)
(*     Create the theorem, eg:                                               *)
(*            |- fix fix x = x                                               *)
(*     from:  |- (!x. f x = x) ==> (!x. fix f x = x)     |- !x. fix x = x    *)
(*                                                                           *)
(*                                                                           *)
(* FULL_ENCODE_DECODE_THM : hol_type -> hol_type -> thm                      *)
(*     Create the theorem, eg:                                               *)
(*            |- !x. decode decode (encode encode x) = x                     *)
(*                                                                           *)
(* FULL_DECODE_ENCODE_THM : hol_type -> hol_type -> thm                      *)
(*     Create the theorem, eg:                                               *)
(*            |- !x. detect detect x ==> encode encode (decode decode x) = x)*)
(*                                                                           *)
(* FULL_ENCODE_DETECT_THM : hol_type -> hol_type -> thm                      *)
(*     Create the theorem, eg:                                               *)
(*            |- !x. detect detect (encode encode x)                         *)
(*                                                                           *)
(*****************************************************************************)

fun wrap_full s t e = 
    wrapException (s ^ "(" ^ type_to_string t ^ ")") e

fun get_sub_types basetype t = 
    filter (not o is_vartype) 
	   (map #residue (match_type basetype t)) 

local
fun EMPTY_RING gconc name target t thms = 
let val conc = gconc target t
in  
    EQT_ELIM (REWRITE_CONV thms conc)
end 
fun RING_MATCH_THM gconc name target t =
let val basetype = if t = target then t else 
    		   most_precise_type 
    		   (C (exists_coding_theorem_precise target) name) t
		   handle _ => t
    val thm = SPEC_ALL (generate_coding_theorem target name basetype)
    val conc = gconc target t
    val thm' = PART_MATCH lhs thm (lhs (snd (strip_forall conc)))
    val sub_thms = map (RING_MATCH_THM gconc name target)
    		       (get_sub_types basetype t)
in
    RIGHT_CONV_RULE (PURE_REWRITE_CONV sub_thms) thm'
end;
fun CHECK_RING gconc name target t thms = 
    if null (type_vars t)
       then (EMPTY_RING gconc name target t thms handle _ => 
       	     RING_MATCH_THM gconc name target t)
       else RING_MATCH_THM gconc name target t
in
fun FULL_ENCODE_DECODE_MAP_THM target t =
    if target = t
       then CONJUNCT1 (ISPEC (mk_const("I",target --> target)) I_o_ID)
       else RING_MATCH_THM mk_encode_decode_map_conc
       	    		   "encode_decode_map" target t
	    handle e => wrap_full "FULL_ENCODE_DECODE_MAP_THM" t e
fun FULL_ENCODE_DETECT_ALL_THM target t = 
    if target = t
       then CONJUNCT2 (ISPEC 
       	    	      (mk_comb(mk_const("K",bool --> target --> bool),T))
		      I_o_ID)       	    	      	     
       else RING_MATCH_THM mk_encode_detect_all_conc 
       	    		   "encode_detect_all" target t
	handle e => wrap_full "FULL_ENCODE_DETECT_ALL_THM" t e
fun FULL_ENCODE_MAP_ENCODE_THM target t =
    if target = t
       then FULL_ENCODE_DECODE_MAP_THM target t
       else
	CHECK_RING mk_encode_map_encode_conc "encode_map_encode" target t
		   [I_o_ID]
	handle e => wrap_full "FULL_ENCODE_MAP_ENCODE_THM" t e
fun FULL_DECODE_ENCODE_FIX_THM target t = 
    if target = t
       then FULL_ENCODE_DECODE_MAP_THM target t
       else
	RING_MATCH_THM mk_decode_encode_fix_conc "decode_encode_fix" target t;
end

fun FULL_MAP_COMPOSE_THM t =
let val basetype = most_precise_type 
    		   (C exists_source_theorem_precise "map_compose") t
		   handle e => t;
    val thm = SPEC_ALL (generate_source_theorem "map_compose" basetype)
    val conc = mk_map_compose_conc t
    val thm' = PART_MATCH lhs thm (lhs (snd (strip_forall conc)))
    val sub_thms = map FULL_MAP_COMPOSE_THM 
    		       (get_sub_types basetype t)
in
    RIGHT_CONV_RULE (PURE_REWRITE_CONV sub_thms) thm'
end handle e => wrap_full "FULL_MAP_COMPOSE_THM" t e

local
fun FMIDT getf t tname ename mk_const mk_conc = 
let val basetype = most_precise_type (C exists_source_theorem_precise tname) t
    		   handle _ => t
    val thm = SPEC_ALL (generate_source_theorem tname basetype)
    val thm' = INST_TYPE (match_type (fst (dom_rng 
                     (type_of (lhs (concl thm))))) t) thm
    val left = lhs (concl thm')
    val subtypes = get_sub_types basetype t
    val sub_thms = map (fn x => 
             if is_vartype x 
             	then NONE 
            	else SOME (FMIDT' getf x tname ename mk_const mk_conc)) 
     	     subtypes

    val conc = mk_conc t
    val thm1 = RAND_CONV (REWR_CONV (GSYM thm)) conc
    val sub_thms_filtered = 
    	filter (fn x => (not o op= o dest_eq o concl o valOf) x
	       	     	handle _ => true) sub_thms
    val thm2 = RIGHT_CONV_RULE 
    	           (REWRITE_CONV (mapfilter Option.valOf sub_thms_filtered)) 
		   thm1
in
    CONV_RULE bool_EQ_CONV thm2
end handle e => wrap_full ename t e
and FMIDT' getf t tname ename mk_const mk_conc =
    if can (match_term (mk_const(alpha --> alpha))) (getf t)
       then REFL (getf t)
       else FMIDT getf t tname ename mk_const mk_conc
in
fun FULL_MAP_ID_THM t = 
    FMIDT' (check_function get_map_function) t "map_id" "FULL_MAP_ID_THM"
    	   (curry mk_const "I") mk_map_id_conc
fun FULL_ALL_ID_THM t = 
    FMIDT' (check_function get_all_function) t "all_id" "FULL_ALL_ID_THM"
    	   (fn t => mk_comb(mk_const("K",bool --> fst (dom_rng t) --> bool),T))
	   mk_all_id_conc
end

fun FULL_FIX_ID_THM target t = 
let fun wrap e = wrap_full "FULL_FIX_ID_THM" t e
    val basetype = if target = t then t else 
    		   most_precise_type
    		   (C (exists_coding_theorem_precise target) "fix_id") t
		   handle _ => t
    val thm = generate_coding_theorem target "fix_id" basetype
    	      handle e => wrap e
    fun mimp_only tm = if is_imp_only tm then snd (dest_imp tm) else tm
    val conc = mk_fix_id_conc target t
    	      handle e => wrap e
    val values = filter (can (match_term the_value)) 
    	       	 	(snd (strip_comb (lhs (snd (strip_imp (snd 
			     (strip_forall (mimp_only (snd 
			     (strip_forall conc))))))))))
    	      handle e => wrap e
    val value_types = map (hd o snd o dest_type o type_of) values
    	      handle e => wrap e
    val tvs = set_diff (type_vars t) value_types
    val sub_thms = map (UNDISCH_ALL o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] o 
    		        FULL_FIX_ID_THM target) 
		       (get_sub_types basetype t)
    	      handle e => wrap e
    val thm' = INST_TY_TERM
    	       (match_term (mimp_only (concl thm)) (mimp_only conc)) thm
    	      handle e => wrap e
    val disch_set = map (mk_fix_id_conc target) tvs
    	      handle e => wrap e
in
    PURE_REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC] 
         (foldr (uncurry DISCH) (foldl (uncurry PROVE_HYP)
	 	(UNDISCH_ALL (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] thm'))
		sub_thms) disch_set)
    	      handle e => wrap e
end;

local
val conv1 = STRIP_QUANT_CONV (RAND_CONV (REWR_CONV (GSYM I_THM)) THENC 
    	    LAND_CONV (REWR_CONV (GSYM o_THM))) THENC
	    REWR_CONV (GSYM FUN_EQ_THM)
val conv2 = REWR_CONV FUN_EQ_THM THENC 
    	    STRIP_QUANT_CONV (RAND_CONV (REWR_CONV I_THM) THENC 
	    LAND_CONV (REWR_CONV o_THM))
fun FEDT target t = 
let fun wrap e = wrap_full "FULL_ENCODE_DECODE_THM" t e
    val ename = "FULL_ENCODE_DECODE_THM" ^ type_to_string t
    val thm1 = generate_coding_theorem target "encode_decode_map" t 
    	       handle e => wrap e
    val thm1_safe = 
    	INST_TYPE (map (fn v => v |-> gen_tyvar())
		       (type_vars_in_term (concl thm1))) thm1
    val thm2 = generate_source_theorem "map_id" t handle e => wrap e
    val tvs = type_vars_avoiding_itself (get_encode_function target t) t
    val antes = map (CONV_RULE conv1 o ASSUME o snd o dest_imp o 
    	      	    snd o strip_forall o mk_encode_decode_conc target)
				tvs handle e =>
                raise (mkDebugExn ename
		      ("mk_encode_decode_conc returned invalid conclusion for" ^
                       " type variable: " ^ type_to_string t))
    val thm2a = PURE_REWRITE_RULE (map SYM antes) thm2 handle e => wrap e
    fun instit f thm = INST_TYPE (match_type (f (concl thm)) t) thm
    val thm1a = instit (snd o dom_rng o type_of o lhs) 
    	      	       (instit (fst o dom_rng o type_of o lhs)
		       (SPEC_ALL thm1_safe))
    val thm3 = TRANS thm1a thm2a handle e => 
    	       raise (mkDebugExn ename
	 ("Generated encode_decode_map and map_id theorems do not match:\n" ^ 
			thm_to_string thm1a ^ "\n" ^ thm_to_string thm2a))
    val thm4 = CONV_RULE conv2 thm3 handle e => wrap e

    val (vs,conc) = strip_forall (mk_encode_decode_conc target t)
    		    handle e => wrap e
    val (vars,list) = if is_imp_only conc 
    		      	 then (vs,strip_conj (fst (dest_imp conc))) else ([],[])
    val result = PURE_REWRITE_RULE [AND_IMP_INTRO] 
    	       	     (foldr (uncurry DISCH) thm4 list)
in
    if null (hyp result) then GENL vars result else
       raise (mkDebugExn ename
		"Hypothesis remain in conclusion of theorem!")
end
in
fun FULL_ENCODE_DECODE_THM target t = 
    if target = t then
       CONV_RULE bool_EQ_CONV (REWRITE_CONV [combinTheory.I_THM]
       		 (mk_encode_decode_conc target t))
    else if is_vartype t 
    	    then DECIDE (mk_encode_decode_conc target t) else FEDT target t
end;

local
fun wrap e = wrapException "FULL_DECODE_ENCODE_THM" e
fun FDET target t = 
let	val thm1 = generate_coding_theorem target "decode_encode_fix" t handle e => wrap e
	val thm2 = generate_coding_theorem target "fix_id" t handle e => wrap e
	
	val thm1a = CONV_RULE (STRIP_QUANT_CONV (REWR_CONV FUN_EQ_THM THENC 
				STRIP_QUANT_CONV (LAND_CONV (REWR_CONV o_THM)))) thm1;
	val v1 = (lhs o snd o dest_imp_only o snd o strip_forall o snd o dest_imp_only)
	val v2 = (lhs o snd o dest_imp_only)
	val thm2a = 	PART_MATCH v1 thm2 (rhs (snd (strip_forall (concl thm1a)))) handle e => 
			PART_MATCH v2 thm2 (rhs (snd (strip_forall (concl thm1a))))

	val thm2b = CONV_RULE (LAND_CONV (EVERY_CONJ_CONV (STRIP_QUANT_CONV
			(RAND_CONV (LAND_CONV (REWR_CONV o_THM)))))) thm2a handle e => thm2a
	val thm2c = 	UNDISCH (SPEC_ALL (UNDISCH_CONJ thm2b)) handle e => 
			UNDISCH (SPEC_ALL thm2b)

	val thm3 = GEN (rhs (concl thm2c)) (DISCH (first (not o is_forall) (hyp thm2c)) (TRANS (SPEC_ALL thm1a) thm2c))
	
	val conc = mk_decode_encode_conc target t
	val list = if is_imp_only (snd (strip_forall (snd (dest_imp_only (snd (strip_forall conc))))))
			then strip_conj (fst (dest_imp_only (snd (strip_forall conc)))) else []
	val r = DISCH_LIST_CONJ list thm3
in
	if null (hyp r) then r else
		raise (mkDebugExn "FULL_DECODE_ENCODE_THM"
			"Hypothesis remain in resultant theorem, mismatch between mk_decode_encode_conc and this?")
end
in
fun FULL_DECODE_ENCODE_THM target t = 
let 	val conc  = (mk_decode_encode_conc target t)
	val vlist = if is_imp_only (snd (strip_forall (snd (dest_imp_only (snd (strip_forall conc))))))
			then fst (strip_forall conc) else []
in
	GENL vlist (if is_vartype t
		then DISCH_ALL (ASSUME (snd (dest_imp_only (snd (strip_forall (mk_decode_encode_conc target t))))))
		else FDET target t)
end
end

local
fun wrap e = wrapException "FULL_ENCODE_DETECT_THM" e
val rthm = DISCH_ALL (CONV_HYP (REWRITE_CONV [FUN_EQ_THM,K_THM])
		(ASSUME (mk_eq(mk_var("A",alpha --> bool),mk_comb(mk_const("K",bool --> alpha --> bool),T)))))
fun FEDT target t =
let	val thm1 = FULL_ENCODE_DETECT_ALL_THM target t handle e => wrap e
	val thm2 = FULL_ALL_ID_THM t handle e => wrap e
	
	val thm2a = CONV_RULE (REWR_CONV FUN_EQ_THM THENC
			STRIP_QUANT_CONV (RAND_CONV (REWR_CONV K_THM) THENC bool_EQ_CONV)) thm2 handle e => wrap e
	val thm1a = snd (EQ_IMP_RULE (SPEC_ALL (CONV_RULE (REWR_CONV FUN_EQ_THM) thm1))) handle e => wrap e
	
	val conc = mk_encode_detect_conc target t handle e => wrap e
	val imps = map (MATCH_MP rthm o CONV_RULE (STRIP_QUANT_CONV (REWR_CONV (GSYM o_THM))) o ASSUME o 
			snd o dest_imp_only o snd o strip_forall o mk_encode_detect_conc target) (type_vars t)
			handle e => wrap e
	val thm3 = GEN_ALL (CONV_RULE (REWR_CONV o_THM) (MATCH_MP (PURE_REWRITE_RULE imps thm1a) (SPEC_ALL thm2a)))
			handle e => wrap e
	val thm3' = GEN_ALL (UNDISCH_ALL (PART_MATCH (snd o strip_imp) (DISCH_ALL thm3)
			(snd (dest_imp (snd (strip_forall conc))) handle _ => snd (strip_forall conc)))) 
			handle e => wrap e;
	
	val (vars,body) = strip_forall conc
	val (vs,timps) = (vars,strip_conj (fst (dest_imp body))) handle _ => ([],[])
	val r = GENL vs (DISCH_LIST_CONJ timps thm3')
in	
	if null (hyp r) then r else
		raise (mkDebugExn "FULL_ENCODE_DETECT_THM"
			"Hypothesis remain in resultant theorem, mismatch between mk_encode_detect_conc and this?")
end
in
fun FULL_ENCODE_DETECT_THM target t = 
	if is_vartype t then DECIDE (mk_encode_detect_conc target t)
		else FEDT target t
end;

(*****************************************************************************)
(* Conversions to fully apply functions:                                     *)
(*                                                                           *)
(* ENCODER_CONV : term -> thm                                                *)
(* APP_MAP_CONV : term -> thm                                                *)
(* APP_ALL_CONV : term -> thm                                                *)
(* DECODE_PAIR_CONV : term -> thm                                            *)
(* DETECT_PAIR_CONV : hol_type -> term -> thm                                *)
(*                                                                           *)
(*        ENCODER_CONV : |- (encode (C a b)) = encode_pair (x,a,b)           *)
(*        APP_MAP_CONV : |- (map (C a b)) = C (map a) (map b)                *)
(*        APP_ALL_CONV : |- (all (C a b)) = (all a) /\ (all b)               *)
(*        DECODE_PAIR_CONV : |- (decode (encode_pair f g a)) =               *)
(*                              C (decode (f (FST (SND a)))) ...             *)
(*        DETECT_PAIR_CONV : |- (detect (encode_pair f g a)) =               *)
(*                              (detect (f (FST (SND a)))) /\ ...            *)
(*                                                                           *)
(*****************************************************************************)

fun ENCODER_CONV term = 
let	val t = type_of (rand term)
	val target = type_of term
	val check = check_function (get_encode_function target) t
	val def = get_coding_function_def target t "encode"
in
	if can (match_term check) (rator term) then
		FIRST_CONV (map REWR_CONV (CONJUNCTS def)) term
	else	
		NO_CONV term
end	handle e => NO_CONV term

fun APP_MAP_CONV term = 
let	val t = type_of (rand term)
	val check = check_function get_map_function t
	val def = get_source_function_def t "map"
in
	if can (match_term check) (rator term) then
		FIRST_CONV (map REWR_CONV (CONJUNCTS def)) term
	else 	NO_CONV term
end	handle e => NO_CONV term
	
fun APP_ALL_CONV term = 
let	val t = type_of (rand term)
	val check = check_function get_all_function t
	val def = get_source_function_def t "all"
in
	if can (match_term check) (rator term) then
		(FIRST_CONV (map REWR_CONV (CONJUNCTS def))) term
	else 	NO_CONV term
end	handle e => NO_CONV term

fun DECODE_PAIR_CONV term = 
let	val t = type_of term
	val target = type_of (rand term)
	val check = check_function (get_decode_function target) t
	val def = get_coding_function_def target t "decode"
	
	val pairp_pair = get_coding_theorem target (mk_prod(alpha,beta)) "encode_detect_all"
	val nump_num = get_coding_theorem target num "encode_detect_all"
	val labelled = mk_comb(get_detect_function target (mk_prod(num,target)),rand term)
	val pairp_id = get_source_theorem (mk_prod(alpha,beta)) "all_id"
	val pair_map = get_source_function_def (mk_prod(alpha,beta)) "map"
	val paird_pair = PURE_REWRITE_RULE [pair_map] 
				(ISPEC (mk_pair(genvar (gen_tyvar()),genvar (gen_tyvar())))
					(PURE_REWRITE_RULE [FUN_EQ_THM,o_THM] 
				(SPEC_ALL (get_coding_theorem target (mk_prod(alpha,beta)) "encode_decode_map"))));
	val numd_num = get_coding_theorem target num "encode_decode_map";
	val cs = constructors_of t
	val all_rwr = 	if all (not o can dom_rng o type_of) cs then
				PURE_REWRITE_CONV [o_THM,PURE_REWRITE_RULE [FUN_EQ_THM,o_THM] nump_num,K_THM] (mk_comb(get_detect_function target num,rand term))
			else if length cs = 1 then 
				PURE_REWRITE_RULE [get_coding_function_def target t "encode"]
					(ISPEC (list_mk_comb(hd cs,map genvar (fst (strip_fun (type_of (hd cs))))))
						(PURE_REWRITE_RULE [FUN_EQ_THM,o_THM] (SPEC_ALL (generate_coding_theorem target "encode_detect_all" t))))
			else	PURE_REWRITE_RULE [K_THM,pairp_id,nump_num,K_o_THM] (PART_MATCH lhs (PURE_REWRITE_RULE [o_THM,FUN_EQ_THM] pairp_pair) labelled)

	val first_decode = if all (not o can dom_rng o type_of) cs then
				PURE_REWRITE_CONV [o_THM,PURE_REWRITE_RULE [FUN_EQ_THM,o_THM] numd_num,I_THM] (mk_comb(get_decode_function target num,rand term))
			else if length cs = 1 then
				REFL labelled
			else	PURE_REWRITE_CONV [paird_pair,numd_num,I_o_ID,I_THM] (mk_comb(get_decode_function target (mk_prod(num,target)),rand term))

	fun re_o_conv term = 
	let	val (r,subs) = (REFL ## map (REWR_CONV (GSYM o_THM))) (strip_comb term)
	in
		foldl (fn (a,b) => MK_COMB(b,a)) r subs
	end;
in
	if can (match_term check) (rator term) then
		(REWR_CONV def THENC PURE_REWRITE_CONV (COND_CLAUSES::all_rwr::first_decode::K_THM::K_o_THM::[generate_source_theorem "all_id" t]) THENC 
		 TRY_CONV let_CONV THENC DEPTH_CONV (reduceLib.NEQ_CONV) THENC PURE_REWRITE_CONV [COND_CLAUSES,paird_pair,o_THM] THENC
		 TRY_CONV let_CONV THENC re_o_conv) term
	else	NO_CONV term
end handle e => wrapException "DETECT_PAIR_CONV" e

fun DETECT_PAIR_CONV t term = 
let	val target = type_of (rand term)
	val check = check_function (get_detect_function target) t
	val def = get_coding_function_def target t "detect"
	
	val pairp_pair = generate_coding_theorem target "encode_detect_all" (mk_prod(alpha,beta))
	val nump_num = generate_coding_theorem target "encode_detect_all" num
	val pairp_id = generate_source_theorem "all_id" (mk_prod(alpha,beta))
	val labelled = mk_comb(get_detect_function target (mk_prod(num,target)),rand term)
	val pair_all = get_source_function_def (mk_prod(alpha,beta)) "all"
	val pair_map = get_source_function_def (mk_prod(alpha,beta)) "map"
	val paird_pair = PURE_REWRITE_RULE [pair_map] 
				(ISPEC (mk_pair(genvar (gen_tyvar()),genvar (gen_tyvar())))
					(PURE_REWRITE_RULE [FUN_EQ_THM,o_THM] (SPEC_ALL (get_coding_theorem target (mk_prod(alpha,beta)) "encode_decode_map"))));
	val numd_num = get_coding_theorem target num "encode_decode_map";
	val cs = constructors_of t
	val all_rwr = 	if all (not o can dom_rng o type_of) cs then
				PURE_REWRITE_CONV [o_THM,PURE_REWRITE_RULE [FUN_EQ_THM,o_THM] nump_num,K_THM] (mk_comb(get_detect_function target num,rand term))
			else if length cs = 1 then 
				REFL labelled
			else	PURE_REWRITE_RULE [K_THM,pairp_id,nump_num,K_o_THM] (PART_MATCH lhs (PURE_REWRITE_RULE [o_THM,FUN_EQ_THM] pairp_pair) labelled)

	val first_decode = 
			if all (not o can dom_rng o type_of) cs then
				PURE_REWRITE_CONV [o_THM,PURE_REWRITE_RULE [FUN_EQ_THM,o_THM] numd_num,I_THM] (mk_comb(get_decode_function target num,rand term))
			else if length cs = 1 then
				REFL labelled
			else 	PURE_REWRITE_CONV [paird_pair,numd_num,I_o_ID,I_THM] (mk_comb(get_decode_function target (mk_prod(num,target)),rand term))
in
	if can (match_term check) (rator term) then
		(REWR_CONV def THENC PURE_REWRITE_CONV [COND_CLAUSES,all_rwr,first_decode] THENC 
		 TRY_CONV let_CONV THENC DEPTH_CONV (reduceLib.NEQ_CONV ORELSEC (REWR_CONV REFL_CLAUSE)) THENC PURE_REWRITE_CONV [COND_CLAUSES] THENC
		 TRY_CONV let_CONV THENC TRY_CONV (REWR_CONV (GSYM o_THM))) term
	else	NO_CONV term
end	handle e => wrapException "DETECT_PAIR_CONV" e

(*****************************************************************************)
(* Tactics to prove the goals described previously:                          *)
(*                                                                           *)
(* encode_decode_map_tactic : hol_type -> hol_type -> tactic                 *)
(* encode_detect_all_tactic : hol_type -> hol_type -> tactic                 *)
(* decode_encode_fix_tactic : hol_type -> hol_type -> tactic                 *)
(* encode_map_encode_tactic : hol_type -> hol_type -> tactic                 *)
(* map_compose_tactic       : hol_type -> tactic                             *)
(* map_id_tactic            : hol_type -> tactic                             *)
(* all_id_tactic            : hol_type -> tactic                             *)
(* fix_id_tactic            : hol_type -> hol_type -> tactic                 *)
(* general_detect_tactic    : hol_type -> hol_type -> tactic                 *)
(*                                                                           *)
(*    Tactics to solve inductive clauses for the goals given previously.     *)
(*                                                                           *)
(* detect_dead_rule         : hol_type -> hol_type -> thm                    *)
(*    Generates a single application of detect to 'nil'. Used in             *)
(*    CONSOLIDATE_CONV to show that bottom values terminate.                 *)
(*                                                                           *)
(*****************************************************************************)

fun encode_decode_map_tactic target (t:hol_type) (a,g) = 
let	val t = type_of (rand (rhs (snd (strip_forall (snd (strip_imp (snd (strip_forall g)))))))) 
	val rts = relevant_types t
	val thms = map (generate_coding_theorem target "encode_decode_map") rts
	val map_defs = map (C get_source_function_def "map") rts
in
	(REPEAT STRIP_TAC THEN
	FIRST [ CONV_TAC (LAND_CONV (RATOR_CONV (FIRST_CONV (map REWR_CONV thms)))) THEN
		RULE_ASSUM_TAC GSYM THEN ASM_REWRITE_TAC (map_defs @ thms),
		PURE_REWRITE_TAC [o_THM] THEN CONV_TAC (LAND_CONV (RAND_CONV ENCODER_CONV THENC DECODE_PAIR_CONV) THENC RAND_CONV APP_MAP_CONV) THEN 
		ASM_REWRITE_TAC (get_source_function_def (mk_prod(alpha,beta)) "map"::thms) THEN
		RULE_ASSUM_TAC GSYM THEN ASM_REWRITE_TAC (map_defs @ thms)]) (a,g)
end	handle e => wrapException "encode_decode_map_tactic" e

local
fun fix_type tm ty = 
	if is_pair tm then uncurry cons ((I ## fix_type (snd (dest_pair tm))) (dest_prod ty)) else [ty];
fun PTAC target rset t (a,g) =
let	val endt = rand (lhs g)
	val t' = delete_matching_types rset (cannon_type (type_of endt))
	val thm1 = PURE_REWRITE_RULE [FUN_EQ_THM,o_THM] (SPEC_ALL (generate_coding_theorem target "encode_map_encode" t'));
	val thm2 = PURE_REWRITE_RULE [I_THM,I_o_ID,get_source_function_def t' "map"] (ISPEC (list_mk_pair(map genvar (fix_type endt t'))) thm1)
in
	(CONV_TAC (LAND_CONV (REWR_CONV thm2))) (a,g)
end
fun CTAC target rset t = 
let	val cs = constructors_of t
in	if all (not o can dom_rng o type_of) cs then ALL_TAC
	else if length cs = 1 then ALL_TAC else PTAC target rset t
end
in
fun encode_map_encode_tactic target (t:hol_type) (a,g) = 
let	val t = type_of (rand (rhs (snd (strip_forall (snd (strip_imp (snd (strip_forall g))))))))
	val rset = map fst (split_nested_recursive_set t)
	val rts = relevant_types t
	val thms = map (generate_coding_theorem target "encode_map_encode") rts
	val enc_defs = map (C (get_coding_function_def target) "encode") (mk_prod(alpha,beta)::all_types t);
	val all_thms = map (PURE_REWRITE_RULE [o_THM,FUN_EQ_THM]) thms @ thms @ enc_defs
in
	(REPEAT STRIP_TAC THEN 
	FIRST [ CONV_TAC (LAND_CONV (RATOR_CONV (FIRST_CONV (map REWR_CONV thms)))) THEN
		RULE_ASSUM_TAC GSYM THEN ASM_REWRITE_TAC all_thms,
		PURE_REWRITE_TAC [o_THM] THEN CONV_TAC (LAND_CONV (RAND_CONV APP_MAP_CONV THENC ENCODER_CONV) THENC RAND_CONV ENCODER_CONV) THEN
		PURE_REWRITE_TAC [I_THM,I_o_ID] THEN CTAC target rset t THEN ASM_REWRITE_TAC all_thms THEN
		RULE_ASSUM_TAC GSYM THEN ASM_REWRITE_TAC (o_THM::all_thms)]) (a,g)
end
end

fun map_compose_tactic (t:hol_type) (a,g) = 
let	val t = type_of (rand (rhs (snd (strip_forall (snd (strip_imp (snd (strip_forall g))))))))
	val rts = relevant_types t
	val thms = map (generate_source_theorem "map_compose") rts
	val map_defs = map (C get_source_function_def "map") (mk_prod(alpha,beta)::all_types t);
	val all_thms = map (PURE_REWRITE_RULE [o_THM,FUN_EQ_THM]) thms @ thms @ map_defs
in
	(REPEAT STRIP_TAC THEN
	 FIRST [CONV_TAC (LAND_CONV (RATOR_CONV (FIRST_CONV (map REWR_CONV thms)))) THEN
		RULE_ASSUM_TAC GSYM THEN ASM_REWRITE_TAC all_thms,
		PURE_REWRITE_TAC [o_THM] THEN CONV_TAC (LAND_CONV (RAND_CONV APP_MAP_CONV THENC APP_MAP_CONV) THENC RAND_CONV APP_MAP_CONV) THEN
		REWRITE_TAC (mapfilter TypeBase.one_one_of (all_types t)) THEN REPEAT CONJ_TAC THEN
		CONV_TAC (LAND_CONV (REWR_CONV (GSYM o_THM))) THEN
		ASM_REWRITE_TAC all_thms]) (a,g)
end;

fun encode_detect_all_tactic target (t:hol_type) (a,g) = 
let	val t = type_of (rand (rhs (snd (strip_forall (snd (strip_imp (snd (strip_forall g))))))))
	val thms = map (generate_coding_theorem target "encode_detect_all") (relevant_types t)
	val all_defs = mapfilter (C get_source_function_def "all") (all_types t)
in
	(REPEAT STRIP_TAC THEN 
	FIRST [	CONV_TAC (LAND_CONV (RATOR_CONV (FIRST_CONV (map REWR_CONV thms)))) THEN
		RULE_ASSUM_TAC GSYM THEN ASM_REWRITE_TAC (all_defs @ thms),
		PURE_REWRITE_TAC [o_THM] THEN CONV_TAC (LAND_CONV (RAND_CONV ENCODER_CONV THENC (DETECT_PAIR_CONV t)) THENC RAND_CONV APP_ALL_CONV) THEN 
		ASM_REWRITE_TAC (get_source_function_def (mk_prod(alpha,beta)) "all"::thms) THEN
		RULE_ASSUM_TAC GSYM THEN ASM_REWRITE_TAC (all_defs @ thms)]) (a,g)
end	handle e => wrapException "encode_detect_all_tactic" e


fun LET_RAND_CONV match term = 
let	fun strip_pair x = if is_pair x then op:: ((I ## strip_pair) (dest_pair x)) else [x]
	val (func_tm,let_tm) = dest_comb term
	val (inputs,output) = pairSyntax.dest_anylet let_tm
	val ginput = map (fn (a,b) => (a,genvar (type_of a))) inputs
	val alpha = gen_tyvar()
	val beta = gen_tyvar()
	val goutput = list_mk_comb(mk_var("M",list_mk_fun(flatten (map (map type_of o strip_pair o fst) ginput),alpha)),
				flatten (map (strip_pair o fst) ginput));
	val gterml = mk_comb(mk_var("f",alpha --> beta),pairSyntax.mk_anylet (ginput,goutput));
	val gtermr = pairSyntax.mk_anylet(ginput,mk_comb(mk_var("f",alpha --> beta),goutput));
	val thm = CONV_RULE bool_EQ_CONV (DEPTH_CONV (REWR_CONV LET_DEF ORELSEC GEN_BETA_CONV ORELSEC REWR_CONV REFL_CLAUSE) (mk_eq(gterml,gtermr)))
in
	if match = func_tm then HO_REWR_CONV thm term else NO_CONV term
end

local
fun PCONV tm = if is_pair tm then RAND_CONV PCONV tm else TRY_CONV (REWR_CONV (GSYM PAIR) THENC PCONV) tm
fun PLET_CONV term = 
let	val len = strip_pair (fst (dest_pabs (rand (rator term))));	
	val full_pair = list_mk_prod(map (fn a => gen_tyvar ()) len)
	val thm = PCONV (mk_var("x",full_pair))
in
	(RATOR_CONV (RATOR_CONV (REWR_CONV LET_DEF)) THENC
	RATOR_CONV BETA_CONV THENC BETA_CONV  THENC
	RAND_CONV (REWR_CONV thm) THENC
	PAIRED_BETA_CONV THENC
	REWRITE_CONV [GSYM thm]) term
end;
fun COND_CONG_TAC (a,g) = 
	TRY (MATCH_MP_TAC COND_CONG THEN CONJ_TAC THENL [ALL_TAC,CONJ_TAC] THENL 
		[ALL_TAC,DISCH_TAC THEN COND_CONG_TAC,DISCH_TAC THEN COND_CONG_TAC]) (a,g);
fun START_LABEL_TAC enc encoder target t =
	PURE_REWRITE_TAC [o_THM] THEN
	ONCE_REWRITE_TAC [get_coding_function_def target t "decode"] THEN
	ONCE_REWRITE_TAC [get_coding_function_def target t "fix"] THEN
	CONV_TAC (LAND_CONV (REDEPTH_CONV (FIRST_CONV [HO_REWR_CONV (ISPEC enc COND_RAND),LET_RAND_CONV enc]))) THEN
	MATCH_MP_TAC COND_CONG THEN REPEAT STRIP_TAC THEN 
	REWRITE_TAC [REWRITE_RULE [FUN_EQ_THM,o_THM] (generate_coding_theorem target "encode_map_encode" t)] THEN
	ONCE_REWRITE_TAC [encoder] THEN
	CONV_TAC (REDEPTH_CONV (let_CONV ORELSEC PLET_CONV)) THEN COND_CONG_TAC THEN
	TRY (REWRITE_TAC [get_coding_function_def target (mk_prod(alpha,beta)) "encode",I_THM] THEN NO_TAC)
fun LABEL_TAC thms enc encoder target t =
	START_LABEL_TAC enc encoder target t THEN
	FIRST [FIRST_ASSUM (CONV_TAC o LAND_CONV o RAND_CONV o REWR_CONV o GSYM),REFL_TAC] THEN
	REWRITE_TAC (map (REWRITE_RULE [FUN_EQ_THM,o_THM]) thms) THEN
	MATCH_MP_TAC (get_coding_theorem target num "fix_id") THEN
	FIRST_ASSUM ACCEPT_TAC
fun XTAC fix_defs (a,g) = 
	(if is_var (rand (rhs g)) then 
	CONV_TAC (BINOP_CONV (FIRST_CONV (map REWR_CONV fix_defs)) THENC DEPTH_CONV (REWR_CONV LET_DEF) THENC DEPTH_CONV GEN_BETA_CONV) THEN
	COND_CONG_TAC else NO_TAC) (a,g)
in
fun decode_encode_fix_tactic target _ (a,g) = 
let	val term = (rator o lhs o snd o strip_forall o snd o strip_imp o snd o strip_forall) g
	val enc = rand (rator term);
	val t = fst (dom_rng (type_of enc))
	val encoder = get_coding_function_def target t "encode";
	val mt = first (not o C (exists_coding_theorem target) "decode_encode_fix") (all_types t)
	val rts = mk_prod(alpha,beta)::num::relevant_types mt
	val thms = map (generate_coding_theorem target "decode_encode_fix" o base_type) rts
	val fix_defs = map (C (get_coding_function_def target) "fix") (mk_prod(alpha,beta)::num::all_types mt)
	val dead_thm = #bottom_thm (get_translation_scheme target)
	val all_defs = foldl (fn (a,b) => get_coding_function_def target a "encode"::get_source_function_def a "map"::
				get_coding_function_def target a "decode"::get_coding_function_def target a "fix"::
				get_coding_function_def target a "detect"::b) [o_THM,dead_thm] (all_types t)
	val thm = REWRITE_RULE [I_THM,get_source_function_def (mk_prod(alpha,beta)) "map"] 
		(ISPEC (mk_pair(mk_var("x",num),mk_var("y",beta))) (REWRITE_RULE [FUN_EQ_THM,o_THM] 
			(SPEC_ALL (generate_coding_theorem target "encode_map_encode" (mk_prod(num,beta))))))
in
	(REPEAT STRIP_TAC THEN
	FIRST [
		CONV_TAC (LAND_CONV (RATOR_CONV (FIRST_CONV (map REWR_CONV thms)))),
		LABEL_TAC thms enc encoder target t,
		START_LABEL_TAC enc encoder target t THEN
		TRY (FULL_SIMP_TAC std_ss [get_coding_function_def target (mk_prod(alpha,beta)) "detect"] THEN NO_TAC) THEN
		TRY (FIRST_ASSUM (CONV_TAC o LAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV o REWR_CONV o GSYM) THEN
		CONV_TAC (LAND_CONV (REWR_CONV thm THENC RAND_CONV (REWR_CONV PAIR)))) THEN
		CONV_TAC (LAND_CONV (FIRST_CONV (map (REWR_CONV o PURE_REWRITE_RULE [FUN_EQ_THM,o_THM]) thms))) THEN
		REWRITE_TAC [I_o_ID]] THEN
	REPEAT (XTAC fix_defs THEN RES_TAC THEN
		ASM_REWRITE_TAC (get_coding_function_def target (mk_prod(alpha,beta)) "encode"::thms) THEN
		RULE_ASSUM_TAC GSYM THEN ASM_REWRITE_TAC (map GSYM thms)) THEN
	REPEAT (CHANGED_TAC (ONCE_ASM_REWRITE_TAC (K_THM::all_defs) THEN 
		CONV_TAC (DEPTH_CONV (REWR_CONV LET_DEF) THENC DEPTH_CONV GEN_BETA_CONV)))) (a,g)
end
end;

local
fun MATCH_FIX_TAC target rset all_types (a,g) = 
let	fun mcheck rset t = exists (can (C match_type t)) rset orelse
			(can dest_type t andalso exists (mcheck rset) (snd (dest_type t)))
	val ftypes = (filter (not o is_vartype) (filter (not o mcheck rset) (num::all_types)));
	val thms = map (fn a => (C (PART_MATCH I) (snd (strip_forall (mk_fix_id_conc target a))) o FULL_FIX_ID_THM target) a) ftypes;
	val thms' = map (CONV_RULE (DEPTH_CONV RIGHT_IMP_FORALL_CONV THENC REWRITE_CONV [AND_IMP_INTRO])) thms
in
	(MATCH_MP_TAC (first (curry op= ((rator o lhs) g) o rator o lhs o snd o strip_imp o
			snd o strip_forall o snd o strip_imp o snd o strip_forall o concl) thms')) (a,g)
end;
in
fun fix_id_tactic target t (a,g) =
let	val all_types = all_types t
	val mt = first (not o C (exists_coding_theorem target) "fix_id" o base_type) all_types
	val defs = map (C (get_coding_function_def target) "fix" o base_type) (mk_prod(alpha,beta)::num::all_types)
	val pdefs = flatten (mapfilter (CONJUNCTS o C (get_coding_function_def target) "detect" o base_type)
				(mk_prod(alpha,beta)::num::all_types))
	val split_thm = generate_coding_theorem target "fix_id" (mk_prod(num,target))
	val rts = relevant_types mt
	val rset = map fst (split_nested_recursive_set mt)
	val def_thms = mapfilter (generate_coding_theorem target "decode_encode_fix" o base_type) 
				(mk_prod(alpha,beta)::num::rts)
	val tsplit_thm = SIMP_RULE std_ss [get_coding_function_def target (mk_prod(alpha,beta)) "detect",
				get_coding_function_def target (mk_prod(alpha,beta)) "fix"] 
			(GSYM (generate_coding_theorem target "fix_id" (mk_prod(target,target))));
	val thms = mapfilter (GEN_ALL o (CONV_RULE (DEPTH_CONV RIGHT_IMP_FORALL_CONV THENC 
			REWRITE_CONV [AND_IMP_INTRO])) o 
			generate_coding_theorem target "fix_id") (rev (mk_prod(alpha,beta)::num::rts))
	val cond_tm = mk_cond(mk_var("p",bool),mk_var("a",alpha),(mk_var("b",alpha)));
in
	(REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN
	FIRST [
		RULE_ASSUM_TAC (CONV_RULE (ONCE_REWRITE_CONV pdefs THENC REWRITE_CONV [COND_EXPAND])) THEN 
		POP_ASSUM STRIP_ASSUME_TAC THEN ONCE_REWRITE_TAC defs THEN ASM_REWRITE_TAC [COND_ID] THEN NO_TAC,
		RULE_ASSUM_TAC (ONCE_REWRITE_RULE pdefs) THEN
		RULE_ASSUM_TAC (ONCE_REWRITE_RULE [get_coding_function_def target (mk_prod(alpha,beta)) "detect"]) THEN
		POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC [] THEN NO_TAC,
		IMP_RES_TAC tsplit_thm THEN POP_ASSUM (CONV_TAC o RAND_CONV o REWR_CONV) THEN
		CONV_TAC (LAND_CONV (FIRST_CONV (map REWR_CONV defs))) THEN
		RULE_ASSUM_TAC (CONV_RULE (TRY_CONV (FIRST_CONV (map REWR_CONV pdefs) THENC REWR_CONV COND_EXPAND))) THEN
		POP_ASSUM STRIP_ASSUME_TAC THEN
		CONV_TAC (DEPTH_CONV (REWR_CONV LET_DEF ORELSEC GEN_BETA_CONV)) THEN
		RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV (REWR_CONV LET_DEF ORELSEC GEN_BETA_CONV))) THEN
		ASM_REWRITE_TAC [] THEN
		TRY (	REPEAT IF_CASES_TAC THEN
			PAT_ASSUM cond_tm MP_TAC THEN ASM_REWRITE_TAC [get_coding_function_def target (mk_prod(alpha,beta)) "encode"] THEN TRY STRIP_TAC THEN
			TRY (CONV_TAC (LAND_CONV (FIRST_CONV (map REWR_CONV defs)))) THEN ASM_REWRITE_TAC []) THEN
		TRY (MK_COMB_TAC THENL [MK_COMB_TAC,ALL_TAC]) THEN
		REWRITE_TAC [] THEN 
		TRY (	(FIRST_ASSUM (CONV_TAC o LAND_CONV o REWR_CONV o GSYM) ORELSE 
				FIRST_ASSUM (CONV_TAC o LAND_CONV o RAND_CONV o REWR_CONV o GSYM) ORELSE MATCH_MP_TAC tsplit_thm) THEN
			REWRITE_TAC [get_coding_function_def target (mk_prod(alpha,beta)) "decode"] THEN 
			ASM_REWRITE_TAC (I_THM::FST::SND::map (REWRITE_RULE [o_THM,FUN_EQ_THM]) def_thms)) THEN
		(FIRST_ASSUM ACCEPT_TAC ORELSE FIRST_ASSUM MATCH_MP_TAC ORELSE MATCH_FIX_TAC target rset all_types) THEN
		FULL_SIMP_TAC std_ss [get_coding_function_def target (mk_prod(alpha,beta)) "detect",get_coding_function_def target (mk_prod(alpha,beta)) "decode"] THEN 
		RULE_ASSUM_TAC (REWRITE_RULE [ISPEC fst_tm COND_RAND,ISPEC snd_tm COND_RAND,I_THM]) THEN
		REPEAT (POP_ASSUM MP_TAC) THEN REPEAT IF_CASES_TAC THEN REPEAT STRIP_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE []) THEN ASM_REWRITE_TAC [],
		ONCE_REWRITE_TAC defs THEN IF_CASES_TAC THEN 
		TRY (FIRST_ASSUM MATCH_MP_TAC) THEN TRY (MATCH_FIX_TAC target rset all_types) THENL
			[RULE_ASSUM_TAC (ONCE_REWRITE_RULE pdefs),ALL_TAC] THEN
		REPEAT (FIRST_ASSUM (fn th => MP_TAC th THEN WEAKEN_TAC (curry op= (concl th)) THEN IF_CASES_TAC THEN DISCH_TAC)) THEN
		RES_TAC THEN IMP_RES_TAC (generate_coding_theorem target "general_detect" (base_type t)) THEN REPEAT CONJ_TAC THEN 
		REPEAT ((FIRST_ASSUM ACCEPT_TAC ORELSE FIRST_ASSUM (ACCEPT_TAC o GSYM) ORELSE REPEAT (POP_ASSUM MP_TAC) THEN ASM_REWRITE_TAC []) THEN
			ONCE_REWRITE_TAC [get_coding_function_def target t "detect"] THEN REPEAT (IF_CASES_TAC THEN ASM_REWRITE_TAC []) THEN REPEAT STRIP_TAC THEN
			MAP_EVERY (IMP_RES_TAC o generate_coding_theorem target "general_detect" o base_type) (filter (not o is_vartype) all_types))]) (a,g)
end
end;

local
fun FULL_MATCH_TAC thm (a,g) = 
let	val (tsub,_) = match_term (snd (strip_exists g)) (concl thm)
	val list = map (fn v => #residue (first (curry op= v o #redex) tsub) handle _ => v) (fst (strip_exists g))
in
	(MAP_EVERY EXISTS_TAC list THEN MATCH_ACCEPT_TAC thm) (a,g)
end;
fun COMPLETE thm split thms (a,g) = 
	(FIRST [REWRITE_TAC [K_THM] THEN NO_TAC,
		FIRST_ASSUM MATCH_MP_TAC,
		MAP_FIRST (MATCH_MP_TAC o GEN_ALL) thms THEN FIRST_ASSUM FULL_MATCH_TAC,
		CONV_TAC (UNDISCH o PART_MATCH (lhs o snd o dest_imp_only) thm) THEN REPEAT CONJ_TAC THEN COMPLETE thm split thms,
		IMP_RES_TAC thm THEN RES_TAC THEN COMPLETE thm split thms]) (a,g)
in	
fun general_detect_tactic target t = 	
let	val all_types = map base_type ((mk_prod(alpha,beta))::(filter (not o is_vartype) (flatten (map (op@ o snd) (split_nested_recursive_set t)))));
	val pair_def = get_coding_function_def target (mk_prod(alpha,beta)) "detect"
	val thms = [K_THM,get_coding_function_def target (mk_prod(alpha,beta)) "decode",I_THM];
	val (thm,split) = CONJ_PAIR (CONV_RULE (REWR_CONV COND_RAND THENC 
		REWRITE_CONV [COND_EXPAND,GSYM (SPEC (mk_neg(mk_var("a",bool))) DISJ_COMM),GSYM IMP_DISJ_THM]) (SPEC_ALL pair_def));

in	REPEAT GEN_TAC THEN REWRITE_TAC [get_coding_function_def target t "detect"] THEN
	TRY (FULL_SIMP_TAC std_ss [pair_def] THEN NO_TAC) THEN
	REWRITE_TAC [LET_DEF] THEN GEN_BETA_TAC THEN ASM_REWRITE_TAC thms THEN
	REPEAT (IF_CASES_TAC THEN ASM_REWRITE_TAC []) THEN REPEAT STRIP_TAC THEN
	REPEAT (FIRST_ASSUM (fn th => MP_TAC th THEN WEAKEN_TAC (curry op= (concl th)) THEN IF_CASES_TAC)) THEN 
	RES_TAC THEN ASM_REWRITE_TAC [FST,SND] THEN REPEAT STRIP_TAC THEN
	REPEAT (CHANGED_TAC (IMP_RES_TAC split THEN IMP_RES_TAC thm)) THEN
	COMPLETE thm split (mapfilter (generate_coding_theorem target "general_detect") all_types)
end
end

local
fun DDR dead_value target t = 
let	val def = get_coding_function_def target t "detect"
	val den = get_coding_theorem target num "detect_dead"
	val t' = fst (strip_fun (type_of (hd (constructors_of t))))
	val dead_thm = #bottom_thm (get_translation_scheme target)
in
	(ONCE_REWRITE_CONV [def] THENC
	REWRITE_CONV (dead_thm::den::mapfilter (generate_coding_theorem target "detect_dead" o list_mk_prod) [t']))
	(mk_comb(check_function (get_detect_function target) t,dead_value))
end
in
fun detect_dead_rule target t = 
let	val dead_value = #bottom (get_translation_scheme target)
in
	if t = target then 
		REWRITE_CONV [get_coding_theorem target bool "encode_decode",K_THM] (mk_comb(get_decode_function target bool,mk_comb(get_detect_function target t,dead_value)))
	else DDR dead_value target t
end
end;

fun all_id_tactic t (a,g) = 
let	val t = type_of (rand (rhs (snd (strip_forall (snd (strip_imp (snd (strip_forall g))))))))
	val all_thms = mapfilter (generate_source_theorem "all_id") (relevant_types t)
	val def = get_source_function_def t "all"
	val pair_def = get_source_function_def (mk_prod(alpha,beta)) "all"
in
	(REPEAT STRIP_TAC THEN REWRITE_TAC [def,pair_def] THEN ASM_REWRITE_TAC (K_THM::all_thms)) (a,g)
end

fun map_id_tactic t (a,g) = 
let	val t = type_of (rand (rhs (snd (strip_forall (snd (strip_imp (snd (strip_forall g))))))))
	val all_thms = mapfilter (generate_source_theorem "map_id") (relevant_types t)
	val def = get_source_function_def t "map"
	val pair_def = get_source_function_def (mk_prod(alpha,beta)) "map"
in
	(REPEAT STRIP_TAC THEN REWRITE_TAC [def,pair_def] THEN ASM_REWRITE_TAC (I_THM::all_thms)) (a,g)
end;

(*****************************************************************************)
(* Destructors:                                                              *)
(*     mk_destructors : hol_type -> hol_type -> thm list                     *)
(*                                                                           *)
(*     Produces destructor theorems and conditional rewrites for resolving   *)
(*     them. This will also produce predicate theorems, eg:                  *)
(*         |- (FST o sexp_to_pair nat f o pair g) (Ci ...) = i               *)
(*                                                                           *)
(*****************************************************************************)

fun MK_FST thm = 
    AP_TERM (mk_const("FST",
    	    type_of (lhs (concl thm)) --> 
	    fst (dest_prod (type_of (lhs (concl thm)))))) thm;
fun MK_SND thm = 
    AP_TERM (mk_const("SND",
    	    type_of (lhs (concl thm)) --> 
	    snd (dest_prod (type_of (lhs (concl thm)))))) thm;

local
fun PRODUCTS 0 thm = [thm]
  | PRODUCTS n thm = 
    MK_FST thm :: PRODUCTS (n - 1) (MK_SND thm) handle _ => [thm];
fun O_CONV c term = 
    if free_in c (rator term) orelse free_in c (rator (rand term))
       handle _ => true
       then ALL_CONV term
       else (RAND_CONV (O_CONV c) THENC REWR_CONV (GSYM o_THM)) term
fun dest_filter l = 
    filter (fn thm => 
    	   mem (rhs (concl thm)) (snd (strip_comb (rand (lhs (concl thm)))))
	   handle e => false) l
exception NotAPair
fun mk_single_destructor target t c = 
let val (types,_) = strip_fun (type_of c)
    val args = map (fn (n,t) => mk_var((implode o base26) n,t))
    	       	   (enumerate 0 types);
    val cons = list_mk_comb(c,args)
    val encoders = CONJUNCTS (get_coding_function_def target t "encode")
    val e = SPEC_ALL (tryfind (C (PART_MATCH (rand o lhs)) cons) encoders)
    val encoder = PART_MATCH (rator o lhs) e (get_encode_function target t)
    val product = type_of (rand (rhs (concl encoder)))
    		  handle _ => raise NotAPair
    val _ = if can pairLib.dest_prod product then () else raise NotAPair
    val applied = AP_TERM (get_decode_function target
    		  	  product) (SPEC_ALL encoder);
    val decoder = SPEC_ALL (FULL_ENCODE_DECODE_THM target product)
    val decoder' = PART_MATCH (lhs o snd o strip_forall o snd o strip_imp)
    		   	      decoder (rhs (concl applied))
    val decoder'' = SPEC_ALL (UNDISCH decoder' handle _ => decoder')
    val rewritten = RIGHT_CONV_RULE (REWR_CONV decoder'') applied
    val product_encoder = get_encode_function target product;
    val apped = RIGHT_CONV_RULE (REWR_CONV (GSYM encoder)) 
       	       		       (AP_TERM product_encoder rewritten);
    val var = variant (thm_frees apped) (mk_var("x",t));
    val eterm = list_mk_exists(args,mk_eq(var,cons))
    val rapped = PURE_REWRITE_RULE [GSYM (ASSUME (mk_eq(var,cons)))] apped;
    val chosen = DISCH_ALL_CONJ (CHOOSE_L (args,ASSUME eterm) rapped);
    val subtypes = sub_types t
in
    (chosen,dest_filter (map (CONV_RULE (LAND_CONV (O_CONV c)) o 
    	   	RIGHT_CONV_RULE (REWRITE_CONV [FST,SND]))
    	      	    (PRODUCTS (length args) rewritten)))
end
fun mapf f [] = []
  | mapf f (x::xs) = 
let val r = mapf f xs
in  (f x :: r) handle NotAPair => r | e => raise e end
in
fun mk_destructors target t =
let val (chosen,destructors) = 
    	unzip (mapf (mk_single_destructor target t) (constructors_of t))
        handle e => wrapException "mk_destructors" e
in
    (chosen, flatten destructors)
end
end

(*****************************************************************************)
(* Initialisation:                                                           *)
(*     initialise_source_function_generators : unit -> unit                  *)
(*     initialise_coding_function_generators : hol_type -> unit              *)
(*                                                                           *)
(*****************************************************************************)

fun initialise_source_function_generators () = 
let	val _ = add_compound_source_function_generator 
		"map"
		mk_map_term
		get_map_function
		REFL REFL;
	val _ = add_compound_source_function_generator 
		"all"
		mk_all_term
		get_all_function
		(fn x => (EVERY_CONJ_CONV (STRIP_QUANT_CONV (RAND_CONV
			(PURE_REWRITE_CONV [get_source_function_def (mk_prod(alpha,beta)) "all"])))) x
				handle UNCHANGED => REFL x)
		REFL;
in
	()
end;

fun initialise_coding_function_generators target = 
let	val _ = add_compound_coding_function_generator 
		"encode"
		(mk_encode_term target)
		(get_encode_function target)
		(ENCODE_CONV (get_coding_function_def target (mk_prod(alpha,beta)) "encode"))
		REFL target;
	val _ = add_compound_target_function_generator 
		"detect"
		(mk_detect_term target)
		(get_detect_function target)
		(DETECT_CONV target)
		REFL target;
	val _ = add_rule_coding_theorem_generator "detect_dead" (can constructors_of)
		(detect_dead_rule target) target;
	val _ = add_compound_target_function_generator 
		"decode"
		(fn t => (	generate_source_function "map" (base_type t) ; 
				generate_coding_function target "encode" (base_type t) ; 
				mk_decode_term target t))
		(get_decode_function target)
		(DECODE_CONV target)
		(CONSOLIDATE_CONV I)
		target;
	val _ = add_compound_target_function_generator 
		"fix"
		(mk_fix_term target)
		(get_fix_function target)
		(FIX_CONV target)
		(CONSOLIDATE_CONV rand)
		target;
in
	()
end

fun initialise_coding_theorem_generators target =
let	val _ = set_coding_theorem_conclusion 
		target "encode_detect_all" 
		(mk_encode_detect_all_conc target);
	val _ = set_source_theorem_conclusion
		"all_id" mk_all_id_conc;
	val _ = set_source_theorem_conclusion
		"map_id" mk_map_id_conc;
	val _ = set_source_theorem_conclusion
		"map_compose" mk_map_compose_conc;
	val _  = set_coding_theorem_conclusion 
		target "encode_decode_map" (mk_encode_decode_map_conc target);
	val _ = set_coding_theorem_conclusion
		target "encode_map_encode" (mk_encode_map_encode_conc target);
	val _ = set_coding_theorem_conclusion
		target "general_detect" (mk_general_detect_conc target);
	val _ = set_coding_theorem_conclusion
		target "decode_encode_fix" (mk_decode_encode_fix_conc target);
	val _ = set_coding_theorem_conclusion
		target "fix_id" (mk_fix_id_conc target);

	val _ = add_inductive_coding_theorem_generator 
		"encode" "encode_detect_all"
		target FUN_EQ_CONV 
		(encode_detect_all_tactic target);
	val _ = add_inductive_source_theorem_generator
		"all" "all_id"
		FUN_EQ_CONV all_id_tactic;
	val _ = add_inductive_source_theorem_generator
		"map" "map_id"
		FUN_EQ_CONV map_id_tactic;
	val _ = add_inductive_source_theorem_generator
		"map" "map_compose"
		FUN_EQ_CONV map_compose_tactic;
	val _ = add_inductive_coding_theorem_generator 
		"encode" "encode_decode_map"
		target FUN_EQ_CONV 
		(encode_decode_map_tactic target);
	val _ = add_inductive_coding_theorem_generator 
		"encode" "encode_map_encode"
		target FUN_EQ_CONV 
		(encode_map_encode_tactic target);
	val _ = add_inductive_coding_theorem_generator
		"detect" "general_detect"
		target REFL
		(general_detect_tactic target);
	val _ = add_inductive_coding_theorem_generator 
		"decode" "decode_encode_fix"
		target FUN_EQ_CONV 
		(decode_encode_fix_tactic target);
	val _ = add_inductive_coding_theorem_generator 
		"fix" "fix_id"
		target REFL
		(fix_id_tactic target);

	fun check_target_rule_use function_name theorem_name t = 
	    (exists_coding_theorem target t theorem_name) orelse
	    not (can (C (get_coding_function_induction target) function_name) t)

	fun check_source_rule_use function_name theorem_name t = 
	    (exists_source_theorem t theorem_name) orelse
	    not (can (C get_source_function_induction function_name) t)
	    
	val _ = add_rule_coding_theorem_generator 
		"encode_detect_all" 
		(check_target_rule_use "encode" "encode_detect_all")
		(FULL_ENCODE_DETECT_ALL_THM target)
		target;
	val _ = add_rule_source_theorem_generator
		"all_id"
		(check_source_rule_use "all" "all_id")
		FULL_ALL_ID_THM;
	val _ = add_rule_source_theorem_generator
		"map_id"
		(check_source_rule_use "map" "map_id")
		FULL_MAP_ID_THM;
	val _ = add_rule_source_theorem_generator
		"map_compose"
		(check_source_rule_use "map" "map_compose")
		FULL_MAP_COMPOSE_THM;
	val _ = add_rule_coding_theorem_generator 
		"encode_decode_map"
		(check_target_rule_use "encode" "encode_decode_map")
		(FULL_ENCODE_DECODE_MAP_THM target)
		target;
	val _ = add_rule_coding_theorem_generator 
		"encode_map_encode" 
		(check_target_rule_use "encode" "encode_map_encode")
		(FULL_ENCODE_MAP_ENCODE_THM target)
		target;
	val _ = add_rule_coding_theorem_generator 
		"general_detect" 
		(C (exists_coding_theorem target) "general_detect") 
		(C (get_coding_theorem target) "general_detect")
		target;
	val _ = add_rule_coding_theorem_generator 
		"decode_encode_fix" 
		(check_target_rule_use "decode" "decode_encode_fix")
		(FULL_DECODE_ENCODE_FIX_THM target)
		target;
	val _ = add_rule_coding_theorem_generator 
		"fix_id"
		(check_target_rule_use "fix" "fix_id")
		(FULL_FIX_ID_THM target)
		target;
in
	()
end;

fun encode_type target t = 
let	val _ = if can (match_type t) (base_type t) then () else
	      	   raise (mkDebugExn "encode_type"
		  "encode_type should only be applied to base types")
	val _ = if exists_translation target t 
	      	   then () 
		   else add_translation target t
	val _ = generate_source_function "map" t
	val _ = generate_source_function "all" t
	val _ = generate_coding_function target "encode" t
	val _ = generate_coding_function target "decode" t
	val _ = generate_coding_function target "detect" t
	val _ = generate_coding_function target "fix" t
	
	val _ = generate_coding_theorem target "encode_detect_all" t
	val _ = generate_coding_theorem target "encode_map_encode" t
	val _ = generate_coding_theorem target "encode_decode_map" t
	val _ = generate_coding_theorem target "decode_encode_fix" t

	val _ = generate_coding_theorem target "fix_id" t
in	
	()
end	handle e => wrapException "encode_type" e

local
fun GENCF name f target t = 
    if (target = t) then f target t
    else 
    (if exists_coding_function target t name
       then f target t
       else (encode_type target (base_type t) ; f target t))
    handle e => wrapException ("gen_" ^ name ^ "_function") e
in
val gen_encode_function = GENCF "encode" get_encode_function
val gen_decode_function = GENCF "decode" get_decode_function
val gen_detect_function = GENCF "detect" get_detect_function
end;

(*****************************************************************************)
(* predicate_equivalence : hol_type -> hol_type -> thm                       *)
(*     Returns a theorem of the form:                                        *)
(*         |- (!x. P x) = (!x. detect x ==> P (decode x))                    *)
(*     for a type t.                                                         *)
(*     This can then be used to derive a fully encoded theorem using a rule  *)
(*     rule implication and the encoding of booleans.                        *)
(*                                                                           *)
(*****************************************************************************)

fun predicate_equivalence target t = 
let val pred = mk_var("P",t --> bool)
    val var = mk_var("x",t);
    val target_var = mk_var("x",target);
    val detect = mk_comb(get_detect_function target t,target_var)
    val decode = mk_comb(get_decode_function target t,target_var)
    val encode = mk_comb(get_encode_function target t,var)

    val full_pred = mk_forall(var,mk_comb(pred,var))
    
    val thm1 = GEN target_var (DISCH detect (SPEC decode (ASSUME full_pred)))

    val encdet = UNDISCH_ALL (SPEC_ALL (FULL_ENCODE_DETECT_THM target t))
    val decenc = UNDISCH_ALL (SPEC_ALL (FULL_ENCODE_DECODE_THM target t))
    val thm2 = GEN var (PURE_REWRITE_RULE [encdet,decenc,IMP_CLAUSES] 
    	            (SPEC encode (ASSUME (concl thm1))))
in	    
    DISCH_ALL_CONJ (IMP_ANTISYM_RULE (DISCH (concl thm2) thm1)
     		                     (DISCH (concl thm1) thm2))
end handle e => wrapException "predicate_equivalence" e

    
end