structure Pair_conv :> Pair_conv =
struct

open HolKernel Parse Drule Theory Conv;
open Pair_syn;
open Pair_basic;
        
type conv = Abbrev.conv

fun PAIR_ERR{function=fnm,message=msg} 
    = raise HOL_ERR{message=msg,origin_function=fnm,
                    origin_structure="pair lib"};
    
fun failwith msg = PAIR_ERR{function=msg,message=""};


val RIGHT_EXISTS_IMP_THM = boolTheory.RIGHT_EXISTS_IMP_THM;
val LEFT_EXISTS_IMP_THM = boolTheory.LEFT_EXISTS_IMP_THM;
val BOTH_EXISTS_IMP_THM = boolTheory.BOTH_EXISTS_IMP_THM;
val RIGHT_FORALL_IMP_THM = boolTheory.RIGHT_FORALL_IMP_THM;
val LEFT_FORALL_IMP_THM = boolTheory.LEFT_FORALL_IMP_THM;
val BOTH_FORALL_IMP_THM = boolTheory.BOTH_FORALL_IMP_THM;
val RIGHT_FORALL_OR_THM = boolTheory.RIGHT_FORALL_OR_THM;
val LEFT_FORALL_OR_THM = boolTheory.LEFT_FORALL_OR_THM;
val BOTH_FORALL_OR_THM = boolTheory.BOTH_FORALL_OR_THM;
val RIGHT_EXISTS_AND_THM = boolTheory.RIGHT_EXISTS_AND_THM;
val LEFT_EXISTS_AND_THM = boolTheory.LEFT_EXISTS_AND_THM;
val BOTH_EXISTS_AND_THM = boolTheory.BOTH_EXISTS_AND_THM;
val RIGHT_OR_EXISTS_THM = boolTheory.RIGHT_OR_EXISTS_THM;
val LEFT_OR_EXISTS_THM = boolTheory.LEFT_OR_EXISTS_THM;
val RIGHT_AND_FORALL_THM = boolTheory.RIGHT_AND_FORALL_THM;
val LEFT_AND_FORALL_THM = boolTheory.LEFT_AND_FORALL_THM;
val EXISTS_OR_THM = boolTheory.EXISTS_OR_THM;
val FORALL_AND_THM = boolTheory.FORALL_AND_THM;
val NOT_EXISTS_THM = boolTheory.NOT_EXISTS_THM;
val NOT_FORALL_THM = boolTheory.NOT_FORALL_THM;

(* ------------------------------------------------------------------------- *)
(* NOT_PFORALL_CONV "~!p.t" = |- (~!p.t) = (?p.~t)                           *)
(* ------------------------------------------------------------------------- *)

fun NOT_PFORALL_CONV tm =
    let val {Bvar=p,...} = dest_pforall (dest_neg tm) 
	val f = rand (rand tm) 
	val th = ISPEC f NOT_FORALL_THM 
	val th1 = CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV
		    ETA_CONV)))) th 
	val th2 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV p))) th1 
    in
	CONV_RULE
	   (RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
	       th2
    end
handle HOL_ERR _ => PAIR_ERR{function="NOT_PFORALL_CONV",
		     message="argument must have the form `~!p.tm`"};
		     
(* ------------------------------------------------------------------------- *)
(* NOT_PEXISTS_CONV "~?p.t" = |- (~?p.t) = (!p.~t)                           *)
(* ------------------------------------------------------------------------- *)

fun NOT_PEXISTS_CONV tm =
    let val {Bvar=p,...} = dest_pexists (dest_neg tm)
	val f = rand (rand tm)
	val th = ISPEC f NOT_EXISTS_THM
	val th1 = CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV
		    ETA_CONV)))) th
	val th2 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV p))) th1
    in
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
	    	   th2
    end
handle HOL_ERR _ => PAIR_ERR{function="NOT_PEXISTS_CONV",
		     message="argument must have the form `~!p.tm`"};


(* ------------------------------------------------------------------------- *)
(* PEXISTS_NOT_CONV "?p.~t" = |- (?p.~t) = (~!p.t)                           *)
(* ------------------------------------------------------------------------- *)

fun PEXISTS_NOT_CONV tm =
    let val {Bvar,Body} = dest_pexists tm
	val xtm = mk_pforall {Bvar=Bvar,Body=dest_neg Body}
    in
	SYM (NOT_PFORALL_CONV (mk_neg xtm))
    end
handle HOL_ERR _ => PAIR_ERR{function="PEXISTS_NOT_CONV",
		     message="argument must have the form `?x.~tm`"};

(* ------------------------------------------------------------------------- *)
(* PFORALL_NOT_CONV "!p.~t" = |- (!p.~t) = (~?p.t)                           *)
(* ------------------------------------------------------------------------- *)

fun PFORALL_NOT_CONV tm =
    let val {Bvar,Body} = dest_pforall tm
	val xtm = mk_pexists {Bvar=Bvar,Body=dest_neg Body}
    in
	SYM (NOT_PEXISTS_CONV (mk_neg xtm))
    end
handle HOL_ERR _ => PAIR_ERR{function="PFORALL_NOT_CONV",
		     message="argument must have the form `!x.~tm`"};


(* ------------------------------------------------------------------------- *)
(* PFORALL_AND_CONV "!x. P /\ Q" = |- (!x. P /\ Q) = (!x.P) /\ (!x.Q)        *)
(* ------------------------------------------------------------------------- *)

fun PFORALL_AND_CONV tm =
    let val {Bvar=x,Body}  = (dest_pforall tm) 
	val {conj1=P,conj2=Q} = dest_conj Body 
	val f = mk_pabs{Bvar=x,Body=P}
	val g = mk_pabs{Bvar=x,Body=Q}
	val th = ISPECL [f,g] FORALL_AND_THM 
	val th1 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RAND_CONV
		    (PALPHA_CONV x))))
		th 
	val th2 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RAND_CONV (PABS_CONV 
		    (RATOR_CONV (RAND_CONV PBETA_CONV))))))
		    th1 
	val th3 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RAND_CONV (PABS_CONV 
		    (RAND_CONV PBETA_CONV)))))
		    th2 
	val th4 =
	    CONV_RULE
		(RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
		th3 
    in
	(CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV)))) th4
    end
handle HOL_ERR _ => PAIR_ERR{function="PFORALL_AND_CONV",
		     message="argument must have the form `!p. P /\\ Q`"};


(* ------------------------------------------------------------------------- *)
(* PEXISTS_OR_CONV "?x. P \/ Q" = |- (?x. P \/ Q) = (?x.P) \/ (?x.Q)         *)
(* ------------------------------------------------------------------------- *)

fun PEXISTS_OR_CONV tm =
    let val {Bvar=x,Body} = dest_pexists tm
	val {disj1=P,disj2=Q} = dest_disj Body
	val f = mk_pabs{Bvar=x,Body=P}
	val g = mk_pabs{Bvar=x,Body=Q}
	val th = ISPECL [f,g] EXISTS_OR_THM 
	val th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV
						     (PALPHA_CONV x))))) th
	val th2 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (PABS_CONV 
	    (RATOR_CONV (RAND_CONV PBETA_CONV))))))) th1
	val th3 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (PABS_CONV 
	    (RAND_CONV PBETA_CONV)))))) th2
	val th4 = (CONV_RULE (RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV 
	    ETA_CONV))))) th3 
    in
	(CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV)))) th4
    end
handle HOL_ERR _ => PAIR_ERR{function="PEXISTS_OR_CONV",
		     message="argument must have the form `?p. P \\/ Q`"};


(* ------------------------------------------------------------------------- *)
(* AND_PFORALL_CONV "(!x. P) /\ (!x. Q)" = |- (!x.P)/\(!x.Q) = (!x. P /\ Q)  *)
(* ------------------------------------------------------------------------- *)

fun AND_PFORALL_CONV tm =
    let val {conj1,conj2} = dest_conj tm 
	val {Bvar=x,Body=P} = dest_pforall conj1
	and {Bvar=y,Body=Q} = dest_pforall conj2
    in
	if (not (x=y)) then failwith""
	else
	    let val f = mk_pabs {Bvar=x,Body=P} 
		val g = mk_pabs{Bvar=x,Body=Q} 
		val th = SYM (ISPECL [f,g] FORALL_AND_THM) 
		val th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RATOR_CONV 
                                       (RAND_CONV (RAND_CONV ETA_CONV)))))) th 
		val th2 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV 
					(RAND_CONV ETA_CONV))))) th1 
		val th3 = (CONV_RULE(RAND_CONV(RAND_CONV(PALPHA_CONV x)))) th2 
		val th4 = (CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV
				    (RATOR_CONV (RAND_CONV PBETA_CONV)))))) th3
	    in
		(CONV_RULE (RAND_CONV(RAND_CONV(PABS_CONV(RAND_CONV
					                    PBETA_CONV))))) th4
	    end
    end
handle HOL_ERR _ => PAIR_ERR{function="AND_PFORALL_CONV",
		     message="arguments must have form `(!p.P)/\\(!p.Q)`"};

    

(* ------------------------------------------------------------------------- *)
(* LEFT_AND_PFORALL_CONV "(!x.P) /\  Q" =                                    *)
(*   |- (!x.P) /\ Q = (!x'. P[x'/x] /\ Q)                                    *)
(* ------------------------------------------------------------------------- *)

fun LEFT_AND_PFORALL_CONV tm =
    let val {conj1,conj2=Q} = dest_conj tm 
	val {Bvar=x,Body=P} = dest_pforall conj1
	val f = mk_pabs{Bvar=x,Body=P} 
	val th = ISPECL [Q,f] LEFT_AND_FORALL_THM 
	val th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV
						 (RAND_CONV ETA_CONV)))))) th 
	val th2 = (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x)))) th1
    in
	(CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
							 PBETA_CONV)))))) th2
    end
handle HOL_ERR _ => PAIR_ERR{function="LEFT_AND_PFORALL_CONV",
			       message="expecting `(!p.P) /\\ Q`"};

(* ------------------------------------------------------------------------- *)
(* RIGHT_AND_PFORALL_CONV "P /\ (!x.Q)" =                                    *)
(*   |-  P /\ (!x.Q) = (!x'. P /\ Q[x'/x])                                   *)
(* ------------------------------------------------------------------------- *)

fun RIGHT_AND_PFORALL_CONV tm =
    let val {conj1=P,conj2} = dest_conj tm 
	val {Bvar=x,Body=Q} = dest_pforall conj2
	val g = mk_pabs{Bvar=x,Body=Q} 
	val th = (ISPECL [P,g] RIGHT_AND_FORALL_THM) 
	val th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV 
                               (RAND_CONV ETA_CONV))))) th
	val th2 = (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x)))) th1 
    in
	CONV_RULE
	    (RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th2
    end
handle HOL_ERR _ => PAIR_ERR{function="RIGHT_AND_PFORALL_CONV",
		     message="expecting `P /\\ (!p.Q)`"};

(* ------------------------------------------------------------------------- *)
(* OR_PEXISTS_CONV "(?x. P) \/ (?x. Q)" = |- (?x.P) \/ (?x.Q) = (?x. P \/ Q) *)
(* ------------------------------------------------------------------------- *)

fun OR_PEXISTS_CONV tm =
    let val {disj1,disj2} = dest_disj tm
	val {Bvar=x,Body=P} = dest_pexists disj1
	and {Bvar=y,Body=Q} = dest_pexists disj2
    in
	if (not (x=y)) then failwith""
	else
	    let val f = mk_pabs{Bvar=x,Body=P} 
		val g = mk_pabs{Bvar=x,Body=Q} 
		val th = SYM (ISPECL [f,g] EXISTS_OR_THM) 
		val th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RATOR_CONV 
                                       (RAND_CONV (RAND_CONV ETA_CONV)))))) th 
		val th2 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV 
						  (RAND_CONV ETA_CONV))))) th1 
		val th3 = (CONV_RULE(RAND_CONV(RAND_CONV(PALPHA_CONV x)))) th2 
		val th4 = (CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV
				    (RATOR_CONV (RAND_CONV PBETA_CONV)))))) th3
	    in
		(CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV(RAND_CONV
							    PBETA_CONV))))) th4
	    end
    end
handle HOL_ERR _ => PAIR_ERR{function="OR_PEXISTS_CONV",
		     message="arguments must have form `(!p.P) \\/ (!p.Q)`"};

    

(* ------------------------------------------------------------------------- *)
(* LEFT_OR_PEXISTS_CONV (--`(?x.P) \/  Q`--) =                               *)
(*   |- (?x.P) \/ Q = (?x'. P[x'/x] \/ Q)                                    *)
(* ------------------------------------------------------------------------- *)

fun LEFT_OR_PEXISTS_CONV tm =
    let val {disj1,disj2=Q} = dest_disj tm
	val {Bvar=x,Body=P} = dest_pexists disj1
	val f = mk_pabs{Bvar=x,Body=P}
	val th = ISPECL [Q,f] LEFT_OR_EXISTS_THM
	val th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV
	    (RAND_CONV ETA_CONV)))))) th 
	val th2 = (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x)))) th1
	in
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
		    PBETA_CONV)))))
		th2
    end
handle HOL_ERR _ => PAIR_ERR{function="LEFT_OR_PEXISTS_CONV",
		     message="expecting `(?p.P) \\/ Q`"};

(* ------------------------------------------------------------------------- *)
(* RIGHT_OR_PEXISTS_CONV "P \/ (?x.Q)" =                                     *)
(*   |-  P \/ (?x.Q) = (?x'. P \/ Q[x'/x])                                   *)
(* ------------------------------------------------------------------------- *)

fun RIGHT_OR_PEXISTS_CONV tm =
    let val {disj1=P,disj2} = dest_disj tm
	val {Bvar=x,Body=Q} = dest_pexists disj2
	val g = mk_pabs{Bvar=x,Body=Q} 
	val th = (ISPECL [P, g] RIGHT_OR_EXISTS_THM) 
	val th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV
	    ETA_CONV))))) th 
	val th2 = (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x)))) th1 
    in
	CONV_RULE
	    (RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th2
    end
handle HOL_ERR _ => PAIR_ERR{function="RIGHT_OR_PEXISTS_CONV",
		     message="expecting `P \\/ (?p.Q)`"};
    
       

(* ------------------------------------------------------------------------- *)
(* PEXISTS_AND_CONV : move existential quantifier into conjunction.          *)
(*                                                                           *)
(* A call to PEXISTS_AND_CONV "?x. P /\ Q"  returns:                         *)
(*                                                                           *)
(*    |- (?x. P /\ Q) = (?x.P) /\ Q        [x not free in Q]                 *)
(*    |- (?x. P /\ Q) = P /\ (?x.Q)        [x not free in P]                 *)
(*    |- (?x. P /\ Q) = (?x.P) /\ (?x.Q)   [x not free in P /\ Q]            *)
(* ------------------------------------------------------------------------- *)

fun PEXISTS_AND_CONV tm =
    let val {Bvar=x,Body} = dest_pexists tm
	handle HOL_ERR _ => failwith "expecting `?x. P /\\ Q`" 
	val {conj1=P,conj2=Q} = dest_conj Body
	    handle HOL_ERR _ => failwith "expecting `?x. P /\\ Q`" 
	val oP = occs_in x P and oQ =  occs_in x Q 
    in
	if (oP andalso oQ) then
	    failwith "bound pair occurs in both conjuncts"
	else if ((not oP) andalso (not oQ)) then
	    let	val th1 = INST_TYPE[{residue=type_of x, redex=mk_vartype "'a"}]
		                   BOTH_EXISTS_AND_THM
		val th2 = SPECL [P,Q] th1 
		val th3 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th2 
		val th4 =
		    CONV_RULE
			(RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
			    (PALPHA_CONV x)))))
			th3 
		val th5 =
		    CONV_RULE
			(RAND_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))th4
	    in
		th5
	    end
	     else if oP then (* not free in Q *)
		 let val f = mk_pabs{Bvar=x,Body=P} 
		     val th1 = ISPECL [Q,f] LEFT_EXISTS_AND_THM 
		     val th2 = CONV_RULE
  			   (RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			   th1
		     val th3 = CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV 
			    (PABS_CONV (RATOR_CONV (RAND_CONV PBETA_CONV))))))
			     th2
		     val th4 = 
			 CONV_RULE
			     (RAND_CONV
			      (RATOR_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
			     th3
		 in
		     th4
		 end
	    else (* not free in P*)
		let val g = mk_pabs{Bvar=x,Body=Q}
		    val th1 = ISPECL [P,g] RIGHT_EXISTS_AND_THM
		    val th2 =
			CONV_RULE
			   (RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			    th1 
		    val th3 = 
			CONV_RULE
			    (RATOR_CONV (RAND_CONV (RAND_CONV 
				    (PABS_CONV (RAND_CONV PBETA_CONV)))))
			    th2
		    val th4 = 
	             CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV))) th3
		in
		    th4
		end
    end
handle HOL_ERR {origin_function=msg,...} 
 => PAIR_ERR{function="PEXISTS_AND_CONV", message=msg};

(* ------------------------------------------------------------------------- *)
(* AND_PEXISTS_CONV "(?x.P) /\ (?x.Q)" = |- (?x.P) /\ (?x.Q) = (?x. P /\ Q)  *)
(* ------------------------------------------------------------------------- *)

fun AND_PEXISTS_CONV tm =
    let val {conj1,conj2} = dest_conj tm
	    handle HOL_ERR _ => failwith "expecting `(?x.P) /\\ (?x.Q)`"
	val {Bvar=x,Body=P} = dest_pexists conj1
	    handle HOL_ERR _ => failwith "expecting `(?x.P) /\\ (?x.Q)`"
	val {Bvar=y,Body=Q} = dest_pexists conj2
	    handle HOL_ERR _ => failwith "expecting `(?x.P) /\\ (?x.Q)`"
	in
	    if not (x=y) then
		failwith "expecting `(?x.P) /\\ (?x.Q)`"
	    else if (occs_in x P) orelse (occs_in x Q) then
		failwith ("`" ^ (#Name(dest_var x)) ^ "` free in conjunct(s)")
	    else
	     SYM (PEXISTS_AND_CONV 
                       (mk_pexists {Bvar=x,Body=mk_conj{conj1=P,conj2=Q}}))
    end
handle HOL_ERR{origin_function=st,...}
=> PAIR_ERR{function="AND_EXISTS_CONV",message=st};

(* ------------------------------------------------------------------------- *)
(* LEFT_AND_PEXISTS_CONV "(?x.P) /\  Q" =                                    *)
(*   |- (?x.P) /\ Q = (?x'. P[x'/x] /\ Q)                                    *)
(* ------------------------------------------------------------------------- *)
     
fun LEFT_AND_PEXISTS_CONV tm =
    let val {conj1,conj2=Q} = dest_conj tm
	val {Bvar=x,Body=P} = dest_pexists conj1
	val f = mk_pabs{Bvar=x,Body=P} 
	val th1 = SYM (ISPECL [Q,f] LEFT_EXISTS_AND_THM) 
	val th2 =
	    CONV_RULE   
		(RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
		    ETA_CONV)))))
		th1 
	val th3 = (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x)))) th2 
	val th4 =
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
		    PBETA_CONV)))))
		th3
    in
	th4
    end
handle HOL_ERR _ => PAIR_ERR{function="LEFT_AND_PEXISTS_CONV",
		     message="expecting `(?x.P) /\\ Q`"};

(* ------------------------------------------------------------------------- *)
(* RIGHT_AND_PEXISTS_CONV "P /\ (?x.Q)" =                                    *)
(*   |- P /\ (?x.Q) = (?x'. P /\ (Q[x'/x])                                   *)
(* ------------------------------------------------------------------------- *)

fun RIGHT_AND_PEXISTS_CONV tm =
    let val {conj1=P,conj2} = dest_conj tm
	val {Bvar=x,Body=Q} = dest_pexists conj2
	val g = mk_pabs{Bvar=x,Body=Q} 
	val th1 = SYM (ISPECL [P,g] RIGHT_EXISTS_AND_THM) 
	val th2 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
		th1 
	val th3 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x))) th2 
	val th4 =
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th3
    in
	th4
    end
handle HOL_ERR _ => PAIR_ERR{function="RIGHT_AND_EXISTS_CONV",
		     message="expecting `P /\\ (?x.Q)`"};
    

(* ------------------------------------------------------------------------- *)
(* PFORALL_OR_CONV : move universal quantifier into disjunction.             *)
(*                                                                           *)
(* A call to PFORALL_OR_CONV "!x. P \/ Q"  returns:                          *)
(*                                                                           *)
(*   |- (!x. P \/ Q) = (!x.P) \/ Q        [if x not free in Q]               *)
(*   |- (!x. P \/ Q) = P \/ (!x.Q)        [if x not free in P]               *)
(*   |- (!x. P \/ Q) = (!x.P) \/ (!x.Q)   [if x free in neither P nor Q]     *)
(* ------------------------------------------------------------------------- *)

fun PFORALL_OR_CONV tm =
    let val {Bvar=x,Body} = dest_forall tm
	    handle HOL_ERR _ => failwith "expecting `!x. P \\/ Q`" 
	val {disj1=P,disj2=Q} = dest_disj Body
	    handle HOL_ERR _ => failwith "expecting `!x. P \\/ Q`" 
	val oP = occs_in x P and oQ =  occs_in x Q 
    in
	if (oP andalso oQ) then
		failwith "bound pair occurs in both conjuncts"
	else if ((not oP) andalso (not oQ)) then
	    let	val th1 =
		INST_TYPE[{residue=type_of x, redex=mk_vartype "'a"}]
		         BOTH_FORALL_OR_THM
		val th2 = SPECL [P,Q] th1 
		val th3 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th2 
		val th4 =
		    CONV_RULE
			(RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
			    (PALPHA_CONV x)))))
			th3
		val th5 =
		    CONV_RULE
			(RAND_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th4
	    in
		    th5
	    end
	     else if oP then (* not free in Q *)
		 let val f = mk_pabs{Bvar=x,Body=P} 
		     val th1 = ISPECL [Q,f] LEFT_FORALL_OR_THM 
		     val th2 =
			 CONV_RULE
			   (RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			     th1 
		     val th3 = 
			 CONV_RULE
			    (RATOR_CONV (RAND_CONV (RAND_CONV 
			     (PABS_CONV (RATOR_CONV (RAND_CONV PBETA_CONV))))))
			     th2
		     val th4 = 
			 CONV_RULE
			     (RAND_CONV
			      (RATOR_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
			     th3
		 in
		     th4
		 end
		  else (* not free in P*)
		      let val g = mk_pabs{Bvar=x,Body=Q} 
			  val th1 = ISPECL [P,g] RIGHT_FORALL_OR_THM 
			  val th2 = CONV_RULE
  			   (RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
				  th1 
			  val th3 = 
			      (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV 
				        (PABS_CONV (RAND_CONV PBETA_CONV)))))) 
			      th2
			  val th4 = (CONV_RULE (RAND_CONV 
                                       (RAND_CONV (RAND_CONV ETA_CONV))))
			            th3
		      in
			  th4
		      end
    end
handle HOL_ERR {origin_function=st,...}
=> PAIR_ERR{function="PFORALL_OR_CONV",message=st};

(* ------------------------------------------------------------------------- *)
(* OR_PFORALL_CONV "(!x.P) \/ (!x.Q)" = |- (!x.P) \/ (!x.Q) = (!x. P \/ Q)   *)
(* ------------------------------------------------------------------------- *)

fun OR_PFORALL_CONV tm =
    let val ((x,P),(y,Q)) =
	let val {disj1,disj2} = dest_disj tm
	    val {Bvar=x,Body=P} = dest_pforall disj1
	    and {Bvar=y,Body=Q} = dest_pforall disj2
	in
	    ((x,P),(y,Q))
	end
    handle HOL_ERR _ => failwith "expecting `(!x.P) \\/ (!x.Q)`"
    in
	if not (x=y) then
	    failwith "expecting `(!x.P) \\/ (!x.Q)'"
	else if (occs_in x P) orelse (occs_in x Q) then
	    failwith "quantified variables free in disjuncts(s)"
	     else
		 SYM (PFORALL_OR_CONV 
                        (mk_pforall {Bvar=x, Body=mk_disj{disj1=P,disj2=Q}}))
    end
handle HOL_ERR{origin_function=st,...}
=> PAIR_ERR{function="OR_FORALL_CONV",message=st};


(* ------------------------------------------------------------------------- *)
(* LEFT_OR_PFORALL_CONV "(!x.P) \/  Q" =                                     *)
(*   |- (!x.P) \/ Q = (!x'. P[x'/x] \/ Q)                                    *)
(* ------------------------------------------------------------------------- *)
     
fun LEFT_OR_PFORALL_CONV tm =
    let val ((x,P),Q) =
	let val {disj1,disj2=Q} = dest_disj tm
	    val {Bvar=x,Body=P} = dest_pforall disj1
	in
	    ((x,P),Q)
	end
	val f = mk_pabs{Bvar=x,Body=P} 
	val th1 = SYM (ISPECL [Q,f] LEFT_FORALL_OR_THM) 
	val th2 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
		    ETA_CONV)))))
		th1 
	val th3 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x))) th2 
	val th4 =
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
		    PBETA_CONV)))))
		th3
    in
	th4
    end
handle HOL_ERR _ => PAIR_ERR{function="LEFT_OR_PFORALL_CONV",
		     message="expecting `(!x.P) \\/ Q`"};


(* ------------------------------------------------------------------------- *)
(* RIGHT_OR_PFORALL_CONV "P \/ (!x.Q)" =                                     *)
(*   |- P \/ (!x.Q) = (!x'. P \/ (Q[x'/x])                                   *)
(* ------------------------------------------------------------------------- *)

fun RIGHT_OR_PFORALL_CONV tm =
    let val (P,(x,Q)) =
	let val {disj1=P,disj2} = dest_disj tm
	    val {Bvar=x,Body=Q} = dest_pforall disj2
	in
	    (P,(x,Q))
	end
	val g = mk_pabs{Bvar=x,Body=Q} 
	val th1 = SYM (ISPECL [P,g] RIGHT_FORALL_OR_THM) 
	val th2 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
		th1 
	val th3 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x))) th2 
	val th4 =
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th3
    in
	th4
    end 
handle HOL_ERR _ => PAIR_ERR{function="RIGHT_OR_FORALL_CONV",
		     message="expecting `P \\/ (!x.Q)`"};
	

(* ------------------------------------------------------------------------- *)
(* PFORALL_IMP_CONV, implements the following axiom schemes.                 *)
(*                                                                           *)
(*       |- (!x. P==>Q[x]) = (P ==> (!x.Q[x]))     [x not free in P]         *)
(*                                                                           *)
(*       |- (!x. P[x]==>Q) = ((?x.P[x]) ==> Q)     [x not free in Q]         *)
(*                                                                           *)
(*       |- (!x. P==>Q) = ((?x.P) ==> (!x.Q))      [x not free in P==>Q]     *)
(* ------------------------------------------------------------------------- *)

fun PFORALL_IMP_CONV tm =
    let val (x,(P,Q)) =
	let val {Bvar,Body} = dest_pforall tm
	    val {ant,conseq} = dest_imp Body
	in
	    (Bvar,(ant,conseq))
	end
    handle HOL_ERR _ => failwith "expecting `!x. P ==> Q`" 
	val oP = occs_in x P and oQ =  occs_in x Q 
    in
	if (oP andalso oQ) then
	    failwith "bound pair occurs in both sides of `==>`"
	else if ((not oP) andalso (not oQ)) then
	    let val th1 = INST_TYPE[{residue=type_of x,redex=mk_vartype "'a"}]
		                   BOTH_FORALL_IMP_THM
		val th2 = SPECL [P,Q] th1
		val th3 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th2 
		val th4 =
		    CONV_RULE
			(RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
			    (PALPHA_CONV x)))))
			th3 
		val th5 =
		    CONV_RULE
			(RAND_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th4
		in
		    th5
	    end
	     else if oP then (* not free in Q *)
		let val f = mk_pabs{Bvar=x,Body=P} 
		    val th1 = ISPECL [Q,f] LEFT_FORALL_IMP_THM 
		    val th2 =
			CONV_RULE
			    (RATOR_CONV(RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			    th1 
		    val th3 = 
			CONV_RULE
			    (RATOR_CONV (RAND_CONV (RAND_CONV 
			       (PABS_CONV(RATOR_CONV(RAND_CONV PBETA_CONV))))))
			    th2 
		    val th4 = CONV_RULE
	               (RAND_CONV(RATOR_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
		       th3
		in
		    th4
		end
	    else (* not free in P*)
		let val g = mk_pabs{Bvar=x,Body=Q} 
		    val th1 = ISPECL [P,g] RIGHT_FORALL_IMP_THM 
		    val th2 = CONV_RULE
			    (RATOR_CONV(RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			    th1 
		    val th3 = 
			CONV_RULE
			    (RATOR_CONV (RAND_CONV (RAND_CONV (PABS_CONV
					       (RAND_CONV PBETA_CONV)))))
			    th2 
		    val th4 = 
			CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV)))
                                  th3
		in
		    th4
		end
    end
handle HOL_ERR{origin_function=st,...} 
=> PAIR_ERR{function="PFORALL_IMP_CONV",message=st};

(* ------------------------------------------------------------------------- *)
(* LEFT_IMP_PEXISTS_CONV "(?x.P) ==>  Q" =                                   *)
(*   |- ((?x.P) ==> Q) = (!x'. P[x'/x] ==> Q)                                *)
(* ------------------------------------------------------------------------- *)

fun LEFT_IMP_PEXISTS_CONV tm =
    let val ((x,P),Q) =
	let val {ant,conseq} = dest_imp tm
	    val {Bvar,Body} = dest_pexists ant
	in
	    ((Bvar,Body),conseq)
	end
	val f = mk_pabs{Bvar=x,Body=P} 
	val th = SYM (ISPECL [Q,f] LEFT_FORALL_IMP_THM) 
	val th1 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV
		    (RAND_CONV ETA_CONV)))))
		th 
	val th2 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x))) th1
    in
	CONV_RULE
	    (RAND_CONV (RAND_CONV (PABS_CONV
		    (RATOR_CONV (RAND_CONV PBETA_CONV)))))
	    th2
    end
handle HOL_ERR _ => PAIR_ERR{function="LEFT_IMP_PEXISTS_CONV",
		     message="expecting `(?p.P) ==> Q`"};


(* ------------------------------------------------------------------------- *)
(* RIGHT_IMP_PFORALL_CONV "P ==> (!x.Q)" =                                   *)
(*   |- (P ==> (!x.Q)) = (!x'. P ==> (Q[x'/x])                               *)
(* ------------------------------------------------------------------------- *)

fun RIGHT_IMP_PFORALL_CONV tm =
    let val (P,(x,Q)) = 
	let val {ant,conseq} = dest_imp tm
	    val{Bvar,Body} = dest_pforall conseq
	in
	    (ant,(Bvar,Body))
	end
	val g = mk_pabs{Bvar=x,Body=Q} 
	val th1 = SYM (ISPECL [P,g] RIGHT_FORALL_IMP_THM) 
	val th2 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
		th1 
	val th3 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x))) th2 
	val th4 =
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th3
    in
	th4
    end
handle HOL_ERR _ => PAIR_ERR{function="RIGHT_IMP_FORALL_CONV",
		     message="expecting `P ==> (!x.Q)`"};


(* ------------------------------------------------------------------------- *)
(* PEXISTS_IMP_CONV, implements the following axiom schemes.                 *)
(*                                                                           *)
(*       |- (?x. P==>Q[x]) = (P ==> (?x.Q[x]))     [x not free in P]         *)
(*                                                                           *)
(*       |- (?x. P[x]==>Q) = ((!x.P[x]) ==> Q)     [x not free in Q]         *)
(*                                                                           *)
(*       |- (?x. P==>Q) = ((!x.P) ==> (?x.Q))      [x not free in P==>Q]     *)
(* ------------------------------------------------------------------------- *)

fun  PEXISTS_IMP_CONV tm =
    let val (x,(P,Q)) =
	let val {Bvar,Body} = dest_pexists tm
	    val {ant,conseq} = dest_imp Body
	in
	    (Bvar,(ant,conseq))
	end
    handle HOL_ERR _ => failwith "expecting `?x. P ==> Q`" 
	val oP = occs_in x P and oQ =  occs_in x Q 
    in
	if (oP andalso oQ) then
		failwith "bound pair occurs in both sides of `==>`"
	else if ((not oP) andalso (not oQ)) then
	    let	val th1 = INST_TYPE[{residue=type_of x,redex=mk_vartype "'a"}]
		                   BOTH_EXISTS_IMP_THM 
		val th2 = SPECL [P,Q] th1 
		val th3 =
		    CONV_RULE
			(RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th2 
		val th4 =
		    CONV_RULE
			(RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
			    (PALPHA_CONV x)))))
			th3 
		val th5 =
		    CONV_RULE
			(RAND_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			th4
	    in
		th5
	    end
	     else if oP then (* not free in Q *)
		let val f = mk_pabs{Bvar=x,Body=P} 
		    val th1 = ISPECL [Q,f] LEFT_EXISTS_IMP_THM 
		    val th2 =
			CONV_RULE
			    (RATOR_CONV (RAND_CONV (RAND_CONV(PALPHA_CONV x))))
			    th1 
		    val th3 = 
			CONV_RULE
			    (RATOR_CONV (RAND_CONV (RAND_CONV 
			       (PABS_CONV(RATOR_CONV(RAND_CONV PBETA_CONV))))))
			    th2 
		    val th4 = 
			CONV_RULE
			    (RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
			        ETA_CONV))))
			    th3
		in
		    th4
		end
		  else (* not free in P*)
		      let val g = mk_pabs{Bvar=x,Body=Q} 
			  val th1 = ISPECL [P,g] RIGHT_EXISTS_IMP_THM 
			  val th2 = CONV_RULE
			   (RATOR_CONV (RAND_CONV (RAND_CONV (PALPHA_CONV x))))
			   th1 
			  val th3 = 
			      CONV_RULE
			          (RATOR_CONV (RAND_CONV (RAND_CONV 
					  (PABS_CONV (RAND_CONV PBETA_CONV)))))
				  th2 
			  val th4 = 
			      CONV_RULE (RAND_CONV (RAND_CONV 
						    (RAND_CONV ETA_CONV))) th3
		      in
			  th4
		      end
    end
handle HOL_ERR{origin_function=st,...}
=> PAIR_ERR{function="PEXISTS_IMP_CONV",message=st};


(* ------------------------------------------------------------------------- *)
(* LEFT_IMP_PFORALL_CONV "(!x. t1[x]) ==> t2" =                              *)
(*   |- (!x. t1[x]) ==> t2 = (?x'. t1[x'] ==> t2)                            *)
(* ------------------------------------------------------------------------- *)

fun LEFT_IMP_PFORALL_CONV tm =
    let val ((x,P),Q) =
	let val {ant,conseq} = dest_imp tm
	    val {Bvar,Body} = dest_pforall ant
	in
	    ((Bvar,Body),conseq)
	end
	val f = mk_pabs{Bvar=x,Body=P} 
	val th1 = SYM (ISPECL [Q,f] LEFT_EXISTS_IMP_THM) 
	val th2 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV (RAND_CONV
		    ETA_CONV)))))
		th1 
	val th3 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x))) th2 
	val th4 =
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV
		    (RATOR_CONV (RAND_CONV PBETA_CONV)))))
		th3
    in
	th4
    end
handle HOL_ERR _ => PAIR_ERR{function="LEFT_IMP_PFORALL_CONV",
		     message="expecting `(!x.P) ==> Q`"};

(* ------------------------------------------------------------------------- *)
(* RIGHT_IMP_EXISTS_CONV "t1 ==> (?x. t2)" =                                 *)
(*   |- (t1 ==> ?x. t2) = (?x'. t1 ==> t2[x'/x])                             *)
(* ------------------------------------------------------------------------- *)

fun RIGHT_IMP_PEXISTS_CONV tm =
    let val (P,(x,Q)) =
	let val {ant,conseq} = dest_imp tm
	    val {Bvar,Body} = dest_pexists conseq
	in
	    (ant,(Bvar,Body))
	end
	val g = mk_pabs{Bvar=x,Body=Q} 
	val th1 = SYM (ISPECL [P,g] RIGHT_EXISTS_IMP_THM) 
	val th2 =
	    CONV_RULE
		(RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV ETA_CONV))))
		th1 
	val th3 = CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x))) th2 
	val th4 =
	    CONV_RULE
		(RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th3
    in
	th4
    end
handle HOL_ERR _ => PAIR_ERR{function="RIGHT_IMP_PEXISTS_CONV",
		     message="expecting `P ==> (!x.Q)`"};

end;
