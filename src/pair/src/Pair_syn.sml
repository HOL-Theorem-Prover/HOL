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
    
val mk_pabs =
    let fun mk_uncurry cf =
	let val tycf = type_of cf 
	    fun uncurry_type ty =
		let val {Tyop=tycon1, Args=[tya, tyb]} = (dest_type ty) 
		    val {Tyop=tycon2, Args=[tyba, tybb]} = (dest_type tyb)
		in
		  assert (curry (op =) "fun") tycon1 ;
		  assert (curry (op =) "fun") tycon2 ;
		  mk_type {Tyop="fun", 
			   Args=[mk_type{Tyop="prod",Args=[tya,tyba]},tybb]}
		end
	in
	    mk_comb{Rator=mk_const{Name="UNCURRY",
				   Ty=mk_type{Tyop="fun",
					      Args=[tycf,uncurry_type tycf]}},
		    Rand=cf}
	end
        fun mpa (p,t) = if is_var p then mk_abs{Bvar=p,Body=t}
			else (* is_pair*)
			 let val {fst,snd} = dest_pair p 
			 in
			     mk_uncurry (mpa (fst, (mpa (snd, t))))
			 end
    in
	fn {Bvar,Body} => mpa (Bvar,Body)
	handle HOL_ERR _ => PAIR_ERR{function="mk_pabs",message=""}
    end;

val bool_ty = (==`:bool`==);
	       
fun mk_pforall {Bvar=x,Body=t} =
    let val ty = type_of x
	val allty = mk_type{Tyop="fun",
                          Args=[mk_type{Tyop="fun",Args=[ty,bool_ty]},bool_ty]}
    in
	mk_comb{Rator=mk_const{Name="!",Ty=allty},
		Rand=mk_pabs{Bvar=x,Body=t}}
	handle HOL_ERR _ => PAIR_ERR{function="mk_pforall",message=""}
    end;
    
fun mk_pexists {Bvar=x,Body=t} =
    let val ty = type_of x
	val exty = mk_type{Tyop="fun",
                           Args=[mk_type{Tyop="fun",
                                         Args=[ty,bool_ty]},bool_ty]}
    in
	mk_comb{Rator=mk_const{Name="?",Ty=exty},
		Rand=mk_pabs{Bvar=x,Body=t}}
	handle HOL_ERR _ => PAIR_ERR{function="mk_pexists",message=""}
    end;

fun mk_pselect {Bvar=x,Body=t} =
    let val ty = type_of x
	val selty = mk_type{Tyop="fun",Args=[mk_type{Tyop="fun",
						     Args=[ty,bool_ty]},ty]}
    in
	mk_comb{Rator=mk_const{Name="@",Ty=selty},
		Rand=mk_pabs{Bvar=x,Body=t}}
	handle HOL_ERR _ => PAIR_ERR{function="mk_pselect",message=""}
    end;

(* ===================================================================== *)
(* Destructors for paired HOL syntax.                                    *)
(* ===================================================================== *)

fun dest_pabs tm =
    if (is_abs tm) then
	dest_abs tm
    else if #Name (dest_const (rator tm)) = "UNCURRY" then
	let val {Bvar=v1,Body=b1} = dest_pabs (rand tm)
	    val {Bvar=v2,Body=b2} = dest_pabs b1
	in
	    {Bvar=mk_pair{fst=v1,snd=v2}, Body=b2}
	end
	 else PAIR_ERR{function="dest_pabs",message=""}
    handle HOL_ERR _ =>PAIR_ERR{function="dest_pabs",message=""};
	     

val dest_pforall =
    let val check = assert (fn c => #Name(dest_const c) = "!") 
    in
	fn tm => let val _ = (check o # Rator)(dest_comb tm)
		 in 
		     (dest_pabs o #Rand o dest_comb)tm 
		 end
	     handle HOL_ERR _ => PAIR_ERR{function="dest_pforall",message=""}
    end;

val dest_pexists =
    let val check = assert (fn c => #Name(dest_const c) = "?") 
    in
	fn tm => let val _ = (check o # Rator)(dest_comb tm)
		 in 
		     (dest_pabs o #Rand o dest_comb)tm 
		 end
	     handle HOL_ERR _ => PAIR_ERR{function="dest_pexists",message=""}
    end;

val dest_pselect =
    let val check = assert (fn c => #Name(dest_const c) = "@") 
    in
	fn tm => let val _ = (check o # Rator)(dest_comb tm)
		 in 
		     (dest_pabs o #Rand o dest_comb)tm 
		 end
	     handle HOL_ERR _ => PAIR_ERR{function="dest_pselect",message=""}
    end;

(* ===================================================================== *)
(* Discriminators for paired HOL syntax.                                 *)
(* ===================================================================== *)

val is_pabs    = can dest_pabs and
    is_pforall = can dest_pforall and
    is_pexists = can dest_pexists and
    is_pselect = can dest_pselect;

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
(* Iterated paired constructors:                                         *)
(*                                                                       *)
(*  * list_mk_pabs ([p1;...;pn],t)           --->   "\p1 ... pn.t"       *)
(*  * list_mk_pforall ([p1;...;pn],t)        --->   "!p1 ... pn.t"       *)
(*  * list_mk_pexists ([p1;...;pn],t)        --->   "?p1 ... pn.t"       *)
(* ===================================================================== *)

fun list_mk_pabs (pl, t) =
    (itlist (fn bv => fn bd => mk_pabs{Bvar=bv,Body=bd}) pl t)
    handle HOL_ERR _ => failwith "list_mk_pabs";
fun list_mk_pforall (pl, t) =
    (itlist (fn bv => fn bd => mk_pforall{Bvar=bv,Body=bd}) pl t)
    handle HOL_ERR _ => failwith "list_mk_pforall";
fun list_mk_pexists (pl, t) =
    (itlist (fn bv => fn bd => mk_pexists{Bvar=bv,Body=bd}) pl t)
    handle HOL_ERR _ => failwith "list_mk_pexists";

(* ===================================================================== *)
(* Iterated paired destructors:                                          *)
(*                                                                       *)
(*  * strip_abs "\p1 ... pn. t"           --->   [p1; ...; pn], t        *)
(*  * strip_forall "!p1 ... pn. t"        --->   [p1; ...; pn], t        *)
(*  * strip_exists "?p1 ... pn. t"        --->   [p1; ...; pn], t        *)
(* ===================================================================== *)

fun strip_pabs tm =
    let val {Bvar,Body} = dest_pabs tm
	val (bps,core) = strip_pabs Body 
    in
	(Bvar::bps, core)
    end
handle HOL_ERR _ => ([],tm);

fun strip_pforall tm =
    let val {Bvar,Body} = dest_pforall tm
	val (bps,core) = strip_pforall Body 
    in
	(Bvar::bps, core)
    end
handle HOL_ERR _ => ([],tm);

fun strip_pexists tm =
    let val {Bvar,Body} = dest_pexists tm
	val (bps,core) = strip_pexists Body 
    in
	(Bvar::bps, core)
    end
handle HOL_ERR _ => ([],tm);

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


(* ===================================================================== *)
(* Extra support of manipulating product types.                          *)
(* ===================================================================== *)

fun is_prod t =
    let val {Tyop,Args} = dest_type t 
    in
	((Tyop = "prod") andalso ((length Args) = 2)) 
    end;;

fun dest_prod t =
    let val {Tyop, Args=[ty1,ty2]} = dest_type t 
    in
	if Tyop = "prod" 
	    then (ty1,ty2)
	else
	    failwith""
    end 
handle HOL_ERR _ => failwith "dest_prod";

fun mk_prod (ty1,ty2) = mk_type{Tyop="prod",Args=[ty1,ty2]};

     
end;
