(* ---------------------------------------------------------------------*)
(* 		Copyright (c) Jim Grundy 1992				*)
(*									*)
(* Jim Grundy, hereafter referred to as "the Author', retains the	*)
(* copyright and all other legal rights to the Software contained in	*)
(* this file, hereafter referred to as "the Software'.			*)
(* 									*)
(* The Software is made available free of charge on an "as is' basis.	*)
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
(* CONTENTS: functions which are common to paired universal and		*)
(*		existential quantifications.				*)
(* ---------------------------------------------------------------------*)
(*$Id$*)

structure Pair_both1 :> Pair_both1 =
struct

open HolKernel Parse boolTheory Drule Conv Pair_syn Pair_basic;

   type term = Term.term
   type thm  = Thm.thm

fun PAIR_ERR{function=fnm,message=msg} = 
     raise HOL_ERR{message=msg,origin_function=fnm, 
                   origin_structure="pair lib"};
    
fun failwith msg = PAIR_ERR{function=msg,message=""};

fun mk_fun(y1,y2) = mk_type{Tyop="fun",Args=[y1,y2]};
fun comma(y1,y2) = mk_const{Name=",",
			    Ty=mk_fun(y1,mk_fun(y2,mk_prod(y1,y2)))};


val PFORALL_THM = pairTheory.PFORALL_THM;
val PEXISTS_THM = pairTheory.PEXISTS_THM;

(* ------------------------------------------------------------------------- *)
(* CURRY_FORALL_CONV "!(x,y).t" = (|- (!(x,y).t) = (!x y.t))                 *)
(* ------------------------------------------------------------------------- *)

    
fun CURRY_FORALL_CONV tm = 
    let val {Bvar=xy,Body=bod} = dest_pforall tm
	val {fst=x,snd=y} = dest_pair xy
	val result = list_mk_pforall ([x,y],bod) 
	val f = rand (rand tm)
	val th1 = RAND_CONV (PABS_CONV (UNPBETA_CONV xy)) tm 
	val th2 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV CURRY_CONV))) th1 
	val th3 = (SYM (ISPEC f PFORALL_THM)) 
	val th4 = CONV_RULE (RATOR_CONV (RAND_CONV (GEN_PALPHA_CONV xy))) th3 
	val th5 = CONV_RULE (RAND_CONV (GEN_PALPHA_CONV x)) (TRANS th2 th4) 
	val th6 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV
						   (GEN_PALPHA_CONV y)))) th5 
	val th7 = CONV_RULE(RAND_CONV(RAND_CONV(PABS_CONV (RAND_CONV 
                                (PABS_CONV(RATOR_CONV PBETA_CONV)))))) th6
	val th8 =
	    CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV 
                         (PABS_CONV PBETA_CONV))))) th7
    in
        TRANS th8 (REFL result)
    end    
handle HOL_ERR _ => failwith "CURRY_FORALL_CONV" ;

(* ------------------------------------------------------------------------- *)
(* CURRY_EXISTS_CONV "?(x,y).t" = (|- (?(x,y).t) = (?x y.t))                 *)
(* ------------------------------------------------------------------------- *)

fun CURRY_EXISTS_CONV tm = 
    let val {Bvar=xy,Body=bod} = dest_pexists tm 
	val {fst=x,snd=y} = dest_pair xy 
	val result = list_mk_pexists ([x,y],bod) 
	val f = rand (rand tm) 
	val th1 = RAND_CONV (PABS_CONV (UNPBETA_CONV xy)) tm 
	val th2 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV CURRY_CONV))) th1 
	val th3 = (SYM (ISPEC f PEXISTS_THM)) 
	val th4 = CONV_RULE (RATOR_CONV (RAND_CONV (GEN_PALPHA_CONV xy))) th3 
	val th5 = CONV_RULE (RAND_CONV (GEN_PALPHA_CONV x)) (TRANS th2 th4) 
	val th6 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV
						   (GEN_PALPHA_CONV y)))) th5 
	val th7 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV 
                       (PABS_CONV (RATOR_CONV PBETA_CONV)))))) th6 
	val th8 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV 
                               (RAND_CONV (PABS_CONV PBETA_CONV))))) th7
    in 
	TRANS th8 (REFL result)
    end
handle HOL_ERR _ => failwith "CURRY_EXISTS_CONV" ;

(* ------------------------------------------------------------------------- *)
(* UNCURRY_FORALL_CONV "!x y.t" = (|- (!x y.t) = (!(x,y).t))                 *)
(* ------------------------------------------------------------------------- *)

fun UNCURRY_FORALL_CONV tm =
    let val {Bvar=x,Body} = dest_pforall tm
	val {Bvar=y,Body=bod} = dest_pforall Body
	val xy = mk_pair{fst=x,snd=y}
	val result = mk_pforall {Bvar=xy,Body=bod}
	val th1 = (RAND_CONV (PABS_CONV (RAND_CONV (PABS_CONV
						    (UNPBETA_CONV xy))))) tm 
	val f = rand (rator (pbody (rand (pbody (rand (rand (concl th1)))))))
	val th2 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV 
                              (RAND_CONV (PABS_CONV CURRY_CONV))))) th1 
	val th3 = ISPEC f PFORALL_THM 
	val th4 = CONV_RULE (RATOR_CONV (RAND_CONV (GEN_PALPHA_CONV x))) th3 
	val th5 = CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (PABS_CONV
		(GEN_PALPHA_CONV y))))) th4 
	val th6 = CONV_RULE (RAND_CONV (GEN_PALPHA_CONV xy)) (TRANS th2 th5) 
	val th7 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RATOR_CONV
			    PBETA_CONV)))) th6 
	val th8 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV PBETA_CONV))) th7
    in
	TRANS th8 (REFL result)
    end
handle HOL_ERR _ => failwith "UNCURRY_FORALL_CONV";

(* ------------------------------------------------------------------------- *)
(* UNCURRY_EXISTS_CONV "?x y.t" = (|- (?x y.t) = (?(x,y).t))                 *)
(* ------------------------------------------------------------------------- *)

fun UNCURRY_EXISTS_CONV tm =
    let val {Bvar=x,Body} = dest_pexists tm
	val {Bvar=y,Body=bod} = dest_pexists Body
	val xy = mk_pair{fst=x,snd=y}
	val result = mk_pexists {Bvar=xy,Body=bod}
	val th1 = (RAND_CONV (PABS_CONV (RAND_CONV (PABS_CONV
						    (UNPBETA_CONV xy))))) tm 
	val f = rand (rator (pbody (rand (pbody (rand (rand (concl th1))))))) 
	val th2 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV 
                              (RAND_CONV (PABS_CONV CURRY_CONV))))) th1 
	val th3 = ISPEC f PEXISTS_THM 
	val th4 = CONV_RULE (RATOR_CONV (RAND_CONV (GEN_PALPHA_CONV x))) th3 
	val th5 = CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (PABS_CONV
			       (GEN_PALPHA_CONV y))))) th4 
	val th6 = CONV_RULE (RAND_CONV (GEN_PALPHA_CONV xy)) (TRANS th2 th5) 
	val th7 = CONV_RULE (RAND_CONV (RAND_CONV 
                        (PABS_CONV (RATOR_CONV PBETA_CONV)))) th6 
	val th8 = CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV PBETA_CONV))) th7
    in
	TRANS th8 (REFL result)
    end
    handle HOL_ERR _ => failwith "UNCURRY_EXISTS_CONV";

end;
