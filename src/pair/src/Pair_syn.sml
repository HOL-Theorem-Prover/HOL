(* ---------------------------------------------------------------------*)
(* 		Copyright (c) Jim Grundy 1992				*)
(*									*)
(* Jim Grundy, hereafter referred to as `the Author', retains the	*)
(* copyright and all other legal rights to the Software contained in	*)
(* this file, hereafter referred to as `the Software'.			*)
(* 									*)
(* The Software is made available free of charge on an `as is' basis.	*)
(* No guarantee, either express or implied, of maintenance, reliability	*)
(* or suitability for any purpose is made by the Author.		*)
(* 									*)
(* The user is granted the right to make personal or internal use	*)
(* of the Software provided that both:					*)
(* 1. The Software is not used for commercial gain.			*)
(* 2. The user shall not hold the Author liable for any consequences	*)
(*    arising from use of the Software.					*)
(* 									*)
(* The user is granted the right to further distribute the Software	*)
(* provided that both:							*)
(* 1. The Software and this statement of rights is not modified.	*)
(* 2. The Software does not form part or the whole of a system 		*)
(*    distributed for commercial gain.					*)
(* 									*)
(* The user is granted the right to modify the Software for personal or	*)
(* internal use provided that all of the following conditions are	*)
(* observed:								*)
(* 1. The user does not distribute the modified software. 		*)
(* 2. The modified software is not used for commercial gain.		*)
(* 3. The Author retains all rights to the modified software.		*)
(*									*)
(* Anyone seeking a licence to use this software for commercial purposes*)
(* is invited to contact the Author.					*)
(* ---------------------------------------------------------------------*)
(* CONTENTS: functions on the syntac of paired abstractions and         *)
(*           quantifications.                                           *)
(* ---------------------------------------------------------------------*)
(*$Id$*)

(* =====================================================================*)
(* Constructors for paired HOL syntax.                                  *)
(* =====================================================================*)

structure Pair_syn :> Pair_syn =
struct

local open pairTheory in end;

open HolKernel Parse ;

type hol_type = Type.hol_type;
type term  = Term.term

fun PAIR_ERR{function=fnm,message=msg} 
    = raise HOL_ERR{message=msg,origin_function=fnm,
                    origin_structure="pair lib"};
    
fun failwith msg = PAIR_ERR{function=msg,message=""};
    

(* ===================================================================== *)
(* All the elements in a pair struture.                                  *)
(* ===================================================================== *)

fun rip_pair p = 
    let val {fst,snd} = dest_pair p 
    in
	rip_pair fst @ rip_pair snd
    end
handle HOL_ERR _ => [p];

(* ===================================================================== *)
(* Check if a term is a pair structure of variables.                     *)
(* ===================================================================== *)

val is_pvar = (all is_var) o rip_pair ;

(* ===================================================================== *)
(* Paired version of variant.                                            *)
(* ===================================================================== *)

val pvariant =
    let fun uniq [] = []
	  | uniq (h::t) = (h::(uniq (filter (fn e => not (e = h)) t)))
	fun variantl avl [] = []
	  | variantl avl (h::t) =
	    let val h' = (variant (avl@(filter is_var t)) h)
	    in
		{residue=h',redex=h}::(variantl (h'::avl) t)
	    end
    in
  fn pl => 
  fn p =>
   let val avoid = (flatten (map ((map (assert is_var)) o rip_pair) pl)) 
       val originals = uniq (map (assert (fn p => is_var p orelse is_const p)) 
                                 (rip_pair p))
       val subl = variantl avoid originals 
   in
     subst subl p
  end end;

(* ===================================================================== *)
(* Generates a pair structure of variable with the same structure as     *)
(* its parameter.                                                        *)
(* ===================================================================== *)

fun genlike p =
    if is_pair p then
	let val {fst,snd} = dest_pair p
	    in
		mk_pair{fst=genlike fst,snd=genlike snd}
	end
    else
	genvar (type_of p);


(* ===================================================================== *)
(* Paired bound variable and body.                                       *)
(* ===================================================================== *)

fun bndpair tm = #Bvar (dest_pabs tm) handle HOL_ERR _ => failwith "bndpair"
and pbody tm = #Body (dest_pabs tm) handle HOL_ERR _ => failwith "pbody" ;

(* ===================================================================== *)
(* Occurence check for bound pairs.                                      *)
(* occs_in p t    true iff any of the variables in p occure free in t    *)
(* ===================================================================== *)

val occs_in =
    let fun occs_check vl t =
	if is_const t then
	    false
	else if is_var t then
	    mem t vl
	else if is_comb t then
	    let val {Rator,Rand} = dest_comb t 
	    in
		(occs_check vl Rator orelse occs_check vl Rand)
	    end
	else (* is_abs *)
	    let val {Bvar,Body} = dest_abs t 
	    in
		occs_check (filter (fn v => (not (v = Bvar))) vl) Body
	    end
    in
	fn p =>
	fn t =>
	if is_pvar p then
	    let val vs = free_vars p 
	    in
		occs_check vs t
	    end
	else
	    failwith "occs_in: not a pvar"
    end;

end;
