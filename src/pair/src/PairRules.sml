structure PairRules :> PairRules =
struct

infix THENC |-> THEN ## ORELSE; infixr -->;

open HolKernel Parse boolLib pairSyntax;

val ERR = mk_HOL_ERR "PairRules"


(* structure Pair_basic :> Pair_basic = struct *)

fun MK_PAIR (t1,t2) =
 let val y1 = type_of (rand (concl t1))
     val y2 = type_of (rand (concl t2))
     val icomma = inst [alpha |-> y1, beta |-> y2] comma_tm
 in
   MK_COMB (AP_TERM icomma t1,t2)
 end;

(* ------------------------------------------------------------------------- *)
(* Paired abstraction                                                        *)
(*                                                                           *)
(*         A |- t1 = t2                                                      *)
(*     -----------------------  (provided p is not free in A)                *)
(*      A |- (\p.t1) = (\p.t2)                                               *)
(* ------------------------------------------------------------------------- *)

fun PABS p th =
    if is_var p then ABS p th
    else (* is_pair *)
	let val (p1,p2) = dest_pair p
	    val t1 = PABS p2 th
	    val t2 = PABS p1 t1
	    val pty = type_of p
	    val p1ty = type_of p1
	    val p2ty = type_of p2
	    val cty = type_of (rand (concl th))
	in
	  AP_TERM
           (inst [alpha |-> p1ty, beta |-> p2ty,gamma |-> cty] uncurry_tm) t2
	end
    handle HOL_ERR _ => failwith "PABS";

(* ----------------------------------------------------------------------- *)
(* PABS_CONV conv "\p. t[p]" applies conv to t[p]                          *)
(* ----------------------------------------------------------------------- *)

fun PABS_CONV conv tm =
    let val (Bvar,Body) = with_exn dest_pabs tm (ERR "PABS_CONV" "")
	val bodyth = conv Body
    in
      PABS Bvar bodyth handle HOL_ERR _ => failwith "PABS_CONV"
    end;

(* ----------------------------------------------------------------------- *)
(* PSUB_CONV conv tm: applies conv to the subterms of tm.                  *)
(* ----------------------------------------------------------------------- *)

fun PSUB_CONV conv tm =
    if is_pabs tm then PABS_CONV conv tm else
    if is_comb tm
       then let val (Rator,Rand) = dest_comb tm
	    in MK_COMB (conv Rator, conv Rand)
            end
       else ALL_CONV tm;

(* ------------------------------------------------------------------------- *)
(* CURRY_CONV "(\(x,y).f)(a,b)" = (|- ((\(x,y).f)(a,b)) = ((\x y. f) a b))   *)
(* ------------------------------------------------------------------------- *)

val UNCURRY_DEF = pairTheory.UNCURRY_DEF;
val CURRY_DEF = pairTheory.CURRY_DEF;
val PAIR =  pairTheory.PAIR;

val CURRY_CONV =
    let val gfty = alpha --> beta --> gamma
	and gxty = alpha
	and gyty = beta
	and gpty = mk_prod(alpha,beta)
	and grange = gamma
	val gf = genvar gfty
	and gx = genvar gxty
	and gy = genvar gyty
	and gp = genvar gpty
	val uncurry_thm = SPECL [gf,gx,gy] UNCURRY_DEF
	and pair_thm = SYM (SPEC gp PAIR)
	val (fgp,sgp) = dest_pair (rand (concl pair_thm))
	val pair_uncurry_thm =
	(CONV_RULE
	    ((RATOR_CONV o RAND_CONV o RAND_CONV) (K (SYM pair_thm))))
	    (SPECL [gf,fgp,sgp]UNCURRY_DEF)
    in
	fn tm =>
	let val (Rator,p) = dest_comb tm
	    val f = rand Rator
	    val fty = type_of f
	    val rnge = hd(tl(snd(dest_type(hd(tl(snd(dest_type fty)))))))
	    val gfinst = mk_var(fst(dest_var gf),fty)
	in
	    if is_pair p then
		let val (x,y) = dest_pair p
		    val xty = type_of x
		    and yty = type_of y
		    val gxinst = mk_var(fst(dest_var gx),xty)
		    and gyinst = mk_var(fst(dest_var gy),yty)
		in
		    INST_TY_TERM
			([gfinst |-> f, gxinst |-> x, gyinst |-> y],
                         [gxty |-> xty, gyty |-> yty, grange |-> rnge])
			uncurry_thm
		end
	    else
		let val pty = type_of p
		    val gpinst = mk_var(fst (dest_var gp),pty)
		    val (xty,yty) = dest_prod pty
		in
		    (INST_TY_TERM
                       ([gfinst |-> f, gpinst |-> p],
                        [gxty |-> xty, gyty |-> yty, grange |-> rnge])
			pair_uncurry_thm)
		end
	end
    end
handle HOL_ERR _ => failwith "CURRY_CONV" ;

(* ------------------------------------------------------------------------- *)
(* UNCURRY_CONV "(\x y. f) a b" = (|- ((\x y. f) a b) = ((\(x,y).f)(x,y)))   *)
(* ------------------------------------------------------------------------- *)

val UNCURRY_CONV =
    let val gfty = alpha --> beta --> gamma
	and gxty = alpha
	and gyty = beta
	and grange = gamma
	val gf = genvar gfty
	and gx = genvar gxty
	and gy = genvar gyty
	val uncurry_thm = SYM (SPECL [gf,gx,gy] UNCURRY_DEF)
    in
	fn tm =>
	let val (Rator,y) = dest_comb tm
	    val (f,x) = dest_comb Rator
	    val fty = type_of f
	    val rnge = hd(tl(snd(dest_type(hd(tl(snd(dest_type fty)))))))
	    val gfinst = mk_var(fst(dest_var gf), fty)
	    val	xty = type_of x
	    and yty = type_of y
	    val gxinst = mk_var(fst(dest_var gx), xty)
	    and gyinst = mk_var(fst(dest_var gy), yty)
	in
	    INST_TY_TERM
		([gfinst |-> f,gxinst |-> x, gyinst |-> y],
		 [gxty |-> xty,gyty |-> yty, grange |-> rnge])
		uncurry_thm
	end
    end
handle HOL_ERR _ => failwith "UNCURRY_CONV" ;

(* ------------------------------------------------------------------------- *)
(* PBETA_CONV "(\p1.t)p2" = (|- (\p1.t)p2 = t[p2/p1])                        *)
(* ------------------------------------------------------------------------- *)

val PBETA_CONV =
    (* pairlike p x: takes a pair structure p and a term x.		  *)
    (* It returns the struture ((change, thm), assoclist)		  *)
    (* where change is true if x does not have the same structure as p.   *)
    (* if changes is true then thm is a theorem of the form (|-x'=x) 	  *)
    (* where x' is of the same structure as p, created by making terms	  *)
    (* into pairs of the form (FST t,SND t).                              *)
    (* assoc thm list is a list of theorms for all the subpairs of x that *)
    (* required changing along the correspoing subpair from p.		  *)
    let val pairlike =
      let fun int_pairlike p x =
	if is_pair p
        then let val (p1,p2) = dest_pair p
	    in
	    if is_pair x
            then let val (x1,x2) = dest_pair x
 		   val ((cl,lt),pl) = int_pairlike p1 x1
	           val ((cr,rt),pr) = int_pairlike p2 x2
                   val (c,t) = if cl andalso cr then (true,MK_PAIR(lt,rt))
                      else if cl
                           then let val ty1 = type_of x1
				    and ty2 = type_of x2
				in (true,
                                    AP_THM (AP_TERM
                                      (inst[alpha|->ty1, beta|->ty2] comma_tm)
                                          lt) x2)
				end
			   else if cr
                                then let val ty1 = type_of x1
					 val ty2 = type_of x2
				     in (true,
                                         AP_TERM (mk_comb (inst
                                          [alpha|->ty1,beta|->ty2]comma_tm,x1))
                                          rt)
				     end
                                else (false,TRUTH)
                 in if c then ((true,t),((p,t)::(pl@pr)))
		         else ((false,TRUTH),[])
		 end
            else
              let val th1 = ISPEC x PAIR
		  val x' = rand (rator (concl th1))
	          val (x'1,x'2) = dest_pair x'
 	          val ((cl,lt),pl) = (int_pairlike p1 x'1)
		  val ((cr,rt),pr) = (int_pairlike p2 x'2)
                  val t = if cl andalso cr then TRANS (MK_PAIR(lt,rt)) th1
 			  else if cl
                               then let val ty1 = type_of x'1
					and ty2 = type_of x'2
				    in TRANS(AP_THM (AP_TERM
                                         (inst[alpha|->ty1,beta|->ty2]comma_tm)
                                         lt) x'2) th1
				    end
			       else if cr
                                    then let val ty1 = type_of x'1
					     val ty2 = type_of x'2
					 in
					 TRANS(AP_TERM (mk_comb
                                         (inst[alpha|->ty1,beta|->ty2]comma_tm,
                                           x'1)) rt)
                                              th1
					 end
                                    else th1
              in
		 ((true,t),((p,t)::(pl@pr)))
	      end
            end  (* let val (p1,p2) = ... *)
        else
	   ((false,TRUTH),[])
      in
	 int_pairlike
      end
    (* find_CONV mask assl:                                        	*)
    (* mask is the body of the original abstraction, containing 	*)
    (* instances of the bound pair p and it subcomponents.		*)
    (* assl is the theorem list generated by pairlike that will allow	*)
    (* us to find these pairs and map them back into nonpairs where	*)
    (* possible.							*)
    fun find_CONV mask assl =
     let fun search m pthl =
	  (true, (K (assoc m assl)))
	    handle HOL_ERR _
	    => if is_comb m then
	        let val (f,b) = dest_comb m
		    val (ff,fc) = search f pthl
		    and (bf,bc) = search b pthl
		in
		    (if (ff andalso bf) then
			(true, (RATOR_CONV fc) THENC (RAND_CONV bc))
		    else if ff then
			(true, (RATOR_CONV fc))
		    else if bf then
			(true, (RAND_CONV bc))
		    else
			(false, ALL_CONV))
		end
	    else if is_abs m then
		     let val (v,b) = dest_abs m
			 val pthl' = filter(fn (p,_) => not (free_in v p)) pthl
		     in
			 if null pthl' then
			     (false, ALL_CONV)
			 else
			     let val (bf,bc) = search b pthl'
			     in
				 if bf then
				     (true, ABS_CONV bc)
				 else
				     (false, ALL_CONV)
			     end
		     end
		 else
		     (false, ALL_CONV)
	in
	    snd (search mask assl)
	end
    fun INT_PBETA_CONV tm =
	let val (Rator,a) = dest_comb tm
	    val (p,b) = dest_pabs Rator
	in
	    if is_var p then BETA_CONV tm
	    else (* is_pair p *)
		(CURRY_CONV THENC
		 (RATOR_CONV INT_PBETA_CONV) THENC
		 INT_PBETA_CONV
		 ) tm
	end
    in
    fn tm =>
      let val (Rator,a) = dest_comb tm
          val (p,b) = dest_pabs Rator
	  val ((dif,difthm),assl) = pairlike p a
      in
	 if dif
           then	(RAND_CONV (K (SYM difthm))
                  THENC INT_PBETA_CONV THENC find_CONV b assl) tm
         else INT_PBETA_CONV tm
      end
 end;

val PBETA_RULE = CONV_RULE (DEPTH_CONV PBETA_CONV)
and PBETA_TAC  = CONV_TAC (DEPTH_CONV PBETA_CONV) ;

fun RIGHT_PBETA th =
    TRANS th (PBETA_CONV (rhs (concl th)))
      handle HOL_ERR _ => failwith "RIGHT_PBETA";

fun LIST_PBETA_CONV tm =
    let val (f,a) = dest_comb tm
    in
	RIGHT_PBETA (AP_THM (LIST_PBETA_CONV f) a)
    end
handle HOL_ERR _ => REFL tm;

fun RIGHT_LIST_PBETA th =
    TRANS th (LIST_PBETA_CONV (rhs (concl th)));

fun LEFT_PBETA th =
    CONV_RULE (RATOR_CONV (RAND_CONV PBETA_CONV)) th
    handle HOL_ERR _ => failwith "LEFT_PBETA";

fun LEFT_LIST_PBETA th =
    CONV_RULE (RATOR_CONV (RAND_CONV LIST_PBETA_CONV)) th
handle HOL_ERR _ => failwith "LEFT_LIST_PBETA";;

(* ------------------------------------------------------------------------- *)
(* UNPBETA_CONV "p" "t" = (|- t = (\p.t)p)                                   *)
(* ------------------------------------------------------------------------- *)

fun UNPBETA_CONV v tm =
    SYM (PBETA_CONV (mk_comb(mk_pabs(v,tm),v)))
    handle HOL_ERR _ => failwith "UNPBETA_CONV";

(* ------------------------------------------------------------------------- *)
(* PETA_CONV "\ p. f p" = (|- (\p. f p) = t)                                 *)
(* ------------------------------------------------------------------------- *)

fun occs_in p t =  (* should use set operations for better speed *)
  if is_vstruct p
  then let fun check V tm =
            if is_const tm then false else
            if is_var tm then mem tm V else
            if is_comb tm then check V (rand tm) orelse check V (rator tm) else
            if is_abs tm then check (set_diff V [bvar tm]) (body tm)
                         else raise ERR "occs_in" "malformed term"
        in check (free_vars p) t
       end
  else raise ERR "occs_in" "varstruct expected in first argument";

fun PETA_CONV tm =
 let val (p,fp) = dest_pabs tm
     val (f,p') = dest_comb fp
     val x = genvar (type_of p)
 in
   if p=p' andalso not (occs_in p f)
   then EXT (GEN x (PBETA_CONV (mk_comb(tm,x))))
   else failwith ""
 end
handle HOL_ERR _ => failwith "PETA_CONV";

(* ------------------------------------------------------------------------- *)
(* PALPHA_CONV p2 "\p1. t" = (|- (\p1. t) = (\p2. t[p2/p1]))                 *)
(* ------------------------------------------------------------------------- *)

fun PALPHA_CONV np tm =
 let val (opr,_) = dest_pabs tm
 in if is_var np
    then if is_var opr then ALPHA_CONV np tm
         else (* is_pair opr *)
         let val np' = genvar (type_of np)
             val t1 =  PBETA_CONV (mk_comb(tm, np'))
             val t2 = ABS np' t1
             val t3 = CONV_RULE (RATOR_CONV (RAND_CONV ETA_CONV)) t2
         in
            CONV_RULE (RAND_CONV (ALPHA_CONV np)) t3
         end
    else (* is_pair np *)
    if is_var opr
    then let val np' = genvarstruct (type_of np)
             val t1 = PBETA_CONV (mk_comb(tm, np'))
             val t2 = PABS np' t1
             val th3 = CONV_RULE (RATOR_CONV (RAND_CONV PETA_CONV)) t2
         in
            CONV_RULE (RAND_CONV (PALPHA_CONV np)) th3
         end
    else (* is_pair opr *)
    let val (np1,np2) = dest_pair np
    in CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (PALPHA_CONV np2))))
                 ((RAND_CONV (PALPHA_CONV np1)) tm)
    end
 end
 handle HOL_ERR _ => failwith "PALPHA_CONV" ;

(* ------------------------------------------------------------------------- *)
(* For any binder B:                                                         *)
(* GEN_PALPHA_CONV p2 "B p1. t" = (|- (B p1. t) = (B p2. t[p2/p1]))          *)
(* ------------------------------------------------------------------------- *)

fun GEN_PALPHA_CONV p tm =
    if is_pabs tm then
	PALPHA_CONV p tm
    else
	AP_TERM (rator tm) (PALPHA_CONV p (rand tm))
	handle HOL_ERR _ => failwith "GEN_PALPHA_CONV";

(* ------------------------------------------------------------------------- *)
(* Iff t1 and t2 are alpha convertable then                                  *)
(* PALPHA t1 t2 = (|- t1 = t2)                                               *)
(*                                                                           *)
(* Note the PALPHA considers "(\x.x)" and "\(a,b).(a,b)" to be               *)
(*   alpha convertable where ALPHA does not.                                 *)
(* ------------------------------------------------------------------------- *)

fun PALPHA t1 t2 =
   if t1 = t2 then REFL t1 else
   if (is_pabs t1) andalso (is_pabs t2)
   then let val (p1,b1) = dest_pabs t1
            val (p2,b2) = dest_pabs t2
        in if is_var p1
           then let val th1 = PALPHA_CONV p1 t2
                    val b2' = pbody (rand (concl th1))
                in
                   TRANS(PABS p1 (PALPHA b1 b2'))(SYM th1)
                end
           else let val th1 = PALPHA_CONV p2 t1
                    val b1' = pbody (rand (concl th1))
                in
                  TRANS th1 (PABS p2 (PALPHA b2 b1'))
                end
        end
   else if (is_comb t1) andalso(is_comb t2)
        then let val (t1f,t1a) = dest_comb t1
                 val (t2f,t2a) = dest_comb t2
                 val thf = PALPHA t1f t2f
                 val tha = PALPHA t1a t2a
             in
                TRANS (AP_THM thf t1a)  (AP_TERM t2f tha)
             end
        else failwith "PALPHA";

val paconv = curry (can (uncurry PALPHA));

(* ------------------------------------------------------------------------- *)
(* PAIR_CONV : conv -> conv                                                  *)
(*                                                                           *)
(* If the argument of the resulting conversion is a pair, this conversion    *)
(* recursively applies itself to both sides of the pair.                     *)
(* Otherwise the basic conversion is applied to the argument.                *)
(* ------------------------------------------------------------------------- *)

fun PAIR_CONV c t =
   if is_pair t
     then let val (fst,snd) = dest_pair t
          in MK_PAIR(PAIR_CONV c fst,PAIR_CONV c snd)
          end
     else c t;

(* end Pair_basic *)

(* structure Pair_conv :> Pair_conv = struct *)


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
    let val (p,_) = dest_pforall (dest_neg tm)
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
handle HOL_ERR _ => raise ERR "NOT_PFORALL_CONV"
                              "argument must have the form `~!p.tm`";

(* ------------------------------------------------------------------------- *)
(* NOT_PEXISTS_CONV "~?p.t" = |- (~?p.t) = (!p.~t)                           *)
(* ------------------------------------------------------------------------- *)

fun NOT_PEXISTS_CONV tm =
    let val (p,_) = dest_pexists (dest_neg tm)
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
handle HOL_ERR _ => raise ERR "NOT_PEXISTS_CONV"
		        "argument must have the form `~!p.tm`";


(* ------------------------------------------------------------------------- *)
(* PEXISTS_NOT_CONV "?p.~t" = |- (?p.~t) = (~!p.t)                           *)
(* ------------------------------------------------------------------------- *)

fun PEXISTS_NOT_CONV tm =
    let val (Bvar,Body) = dest_pexists tm
	val xtm = mk_pforall (Bvar,dest_neg Body)
    in
	SYM (NOT_PFORALL_CONV (mk_neg xtm))
    end
handle HOL_ERR _ => raise ERR "PEXISTS_NOT_CONV"
                        "argument must have the form `?x.~tm`";

(* ------------------------------------------------------------------------- *)
(* PFORALL_NOT_CONV "!p.~t" = |- (!p.~t) = (~?p.t)                           *)
(* ------------------------------------------------------------------------- *)

fun PFORALL_NOT_CONV tm =
    let val (Bvar,Body) = dest_pforall tm
	val xtm = mk_pexists (Bvar,dest_neg Body)
    in
	SYM (NOT_PEXISTS_CONV (mk_neg xtm))
    end
handle HOL_ERR _ => raise ERR "PFORALL_NOT_CONV"
		        "argument must have the form `!x.~tm`";


(* ------------------------------------------------------------------------- *)
(* PFORALL_AND_CONV "!x. P /\ Q" = |- (!x. P /\ Q) = (!x.P) /\ (!x.Q)        *)
(* ------------------------------------------------------------------------- *)

fun PFORALL_AND_CONV tm =
    let val (x,Body) = dest_pforall tm
	val (P,Q) = dest_conj Body
	val f = mk_pabs(x,P)
	val g = mk_pabs(x,Q)
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
handle HOL_ERR _ => raise ERR "PFORALL_AND_CONV"
		     "argument must have the form `!p. P /\\ Q`";


(* ------------------------------------------------------------------------- *)
(* PEXISTS_OR_CONV "?x. P \/ Q" = |- (?x. P \/ Q) = (?x.P) \/ (?x.Q)         *)
(* ------------------------------------------------------------------------- *)

fun PEXISTS_OR_CONV tm =
    let val (x,Body) = dest_pexists tm
	val (P,Q) = dest_disj Body
	val f = mk_pabs(x,P)
	val g = mk_pabs(x,Q)
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
handle HOL_ERR _ => raise ERR"PEXISTS_OR_CONV"
                       "argument must have the form `?p. P \\/ Q`";


(* ------------------------------------------------------------------------- *)
(* AND_PFORALL_CONV "(!x. P) /\ (!x. Q)" = |- (!x.P)/\(!x.Q) = (!x. P /\ Q)  *)
(* ------------------------------------------------------------------------- *)

fun AND_PFORALL_CONV tm =
    let val (conj1,conj2) = dest_conj tm
	val (x,P) = dest_pforall conj1
	and (y,Q) = dest_pforall conj2
    in
	if (not (x=y)) then failwith""
	else
	    let val f = mk_pabs (x,P)
		val g = mk_pabs(x,Q)
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
handle HOL_ERR _ => raise ERR "AND_PFORALL_CONV"
		     "arguments must have form `(!p.P)/\\(!p.Q)`";



(* ------------------------------------------------------------------------- *)
(* LEFT_AND_PFORALL_CONV "(!x.P) /\  Q" =                                    *)
(*   |- (!x.P) /\ Q = (!x'. P[x'/x] /\ Q)                                    *)
(* ------------------------------------------------------------------------- *)

fun LEFT_AND_PFORALL_CONV tm =
    let val (conj1,Q) = dest_conj tm
	val (x,P) = dest_pforall conj1
	val f = mk_pabs(x,P)
	val th = ISPECL [Q,f] LEFT_AND_FORALL_THM
	val th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV
						 (RAND_CONV ETA_CONV)))))) th
	val th2 = (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x)))) th1
    in
	(CONV_RULE (RAND_CONV (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
							 PBETA_CONV)))))) th2
    end
handle HOL_ERR _ => raise ERR "LEFT_AND_PFORALL_CONV"
			     "expecting `(!p.P) /\\ Q`";

(* ------------------------------------------------------------------------- *)
(* RIGHT_AND_PFORALL_CONV "P /\ (!x.Q)" =                                    *)
(*   |-  P /\ (!x.Q) = (!x'. P /\ Q[x'/x])                                   *)
(* ------------------------------------------------------------------------- *)

fun RIGHT_AND_PFORALL_CONV tm =
    let val (P,conj2) = dest_conj tm
	val (x,Q) = dest_pforall conj2
	val g = mk_pabs(x,Q)
	val th = (ISPECL [P,g] RIGHT_AND_FORALL_THM)
	val th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV
                               (RAND_CONV ETA_CONV))))) th
	val th2 = (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x)))) th1
    in
	CONV_RULE
	    (RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th2
    end
handle HOL_ERR _ => raise ERR "RIGHT_AND_PFORALL_CONV"
		        "expecting `P /\\ (!p.Q)`";

(* ------------------------------------------------------------------------- *)
(* OR_PEXISTS_CONV "(?x. P) \/ (?x. Q)" = |- (?x.P) \/ (?x.Q) = (?x. P \/ Q) *)
(* ------------------------------------------------------------------------- *)

fun OR_PEXISTS_CONV tm =
    let val (disj1,disj2) = dest_disj tm
	val (x,P) = dest_pexists disj1
	and (y,Q) = dest_pexists disj2
    in
	if (not (x=y)) then failwith""
	else
	    let val f = mk_pabs(x,P)
		val g = mk_pabs(x,Q)
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
handle HOL_ERR _ => raise ERR "OR_PEXISTS_CONV"
		        "arguments must have form `(!p.P) \\/ (!p.Q)`";



(* ------------------------------------------------------------------------- *)
(* LEFT_OR_PEXISTS_CONV (--`(?x.P) \/  Q`--) =                               *)
(*   |- (?x.P) \/ Q = (?x'. P[x'/x] \/ Q)                                    *)
(* ------------------------------------------------------------------------- *)

fun LEFT_OR_PEXISTS_CONV tm =
    let val (disj1,Q) = dest_disj tm
	val (x,P) = dest_pexists disj1
	val f = mk_pabs(x,P)
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
handle HOL_ERR _ => raise ERR "LEFT_OR_PEXISTS_CONV"
		        "expecting `(?p.P) \\/ Q`";

(* ------------------------------------------------------------------------- *)
(* RIGHT_OR_PEXISTS_CONV "P \/ (?x.Q)" =                                     *)
(*   |-  P \/ (?x.Q) = (?x'. P \/ Q[x'/x])                                   *)
(* ------------------------------------------------------------------------- *)

fun RIGHT_OR_PEXISTS_CONV tm =
    let val (P,disj2) = dest_disj tm
	val (x,Q) = dest_pexists disj2
	val g = mk_pabs(x,Q)
	val th = (ISPECL [P, g] RIGHT_OR_EXISTS_THM)
	val th1 = (CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (RAND_CONV
	    ETA_CONV))))) th
	val th2 = (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV x)))) th1
    in
	CONV_RULE
	    (RAND_CONV (RAND_CONV (PABS_CONV (RAND_CONV PBETA_CONV))))
		th2
    end
handle HOL_ERR _ => raise ERR "RIGHT_OR_PEXISTS_CONV"
		        "expecting `P \\/ (?p.Q)`";



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
    let val (x,Body) = dest_pexists tm
	handle HOL_ERR _ => failwith "expecting `?x. P /\\ Q`"
	val (P,Q) = dest_conj Body
	    handle HOL_ERR _ => failwith "expecting `?x. P /\\ Q`"
	val oP = occs_in x P and oQ =  occs_in x Q
    in
	if (oP andalso oQ) then
	    failwith "bound pair occurs in both conjuncts"
	else if ((not oP) andalso (not oQ)) then
	    let	val th1 = INST_TYPE[alpha |-> type_of x ] BOTH_EXISTS_AND_THM
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
		 let val f = mk_pabs(x,P)
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
		let val g = mk_pabs(x,Q)
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
handle e => raise (wrap_exn "PEXISTS_AND_CONV" "" e);

(* ------------------------------------------------------------------------- *)
(* AND_PEXISTS_CONV "(?x.P) /\ (?x.Q)" = |- (?x.P) /\ (?x.Q) = (?x. P /\ Q)  *)
(* ------------------------------------------------------------------------- *)

fun AND_PEXISTS_CONV tm =
    let val (conj1,conj2) = dest_conj tm
	    handle HOL_ERR _ => failwith "expecting `(?x.P) /\\ (?x.Q)`"
	val (x,P) = dest_pexists conj1
	    handle HOL_ERR _ => failwith "expecting `(?x.P) /\\ (?x.Q)`"
	val (y,Q) = dest_pexists conj2
	    handle HOL_ERR _ => failwith "expecting `(?x.P) /\\ (?x.Q)`"
	in
	    if not (x=y) then
		failwith "expecting `(?x.P) /\\ (?x.Q)`"
	    else if (occs_in x P) orelse (occs_in x Q) then
		failwith ("`" ^ (fst(dest_var x)) ^ "` free in conjunct(s)")
	    else
	     SYM (PEXISTS_AND_CONV (mk_pexists (x,mk_conj(P,Q))))
    end
handle e => raise (wrap_exn "AND_EXISTS_CONV" "" e);

(* ------------------------------------------------------------------------- *)
(* LEFT_AND_PEXISTS_CONV "(?x.P) /\  Q" =                                    *)
(*   |- (?x.P) /\ Q = (?x'. P[x'/x] /\ Q)                                    *)
(* ------------------------------------------------------------------------- *)

fun LEFT_AND_PEXISTS_CONV tm =
    let val (conj1,Q) = dest_conj tm
	val (x,P) = dest_pexists conj1
	val f = mk_pabs(x,P)
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
handle HOL_ERR _ => raise (ERR "LEFT_AND_PEXISTS_CONV"
                               "expecting `(?x.P) /\\ Q`");

(* ------------------------------------------------------------------------- *)
(* RIGHT_AND_PEXISTS_CONV "P /\ (?x.Q)" =                                    *)
(*   |- P /\ (?x.Q) = (?x'. P /\ (Q[x'/x])                                   *)
(* ------------------------------------------------------------------------- *)

fun RIGHT_AND_PEXISTS_CONV tm =
    let val (P,conj2) = dest_conj tm
	val (x,Q) = dest_pexists conj2
	val g = mk_pabs(x,Q)
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
handle HOL_ERR _ => raise ERR "RIGHT_AND_EXISTS_CONV"
		               "expecting `P /\\ (?x.Q)`";


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
    let val (x,Body) = dest_forall tm
	    handle HOL_ERR _ => failwith "expecting `!x. P \\/ Q`"
	val (P,Q) = dest_disj Body
	    handle HOL_ERR _ => failwith "expecting `!x. P \\/ Q`"
	val oP = occs_in x P and oQ =  occs_in x Q
    in
	if (oP andalso oQ) then
		failwith "bound pair occurs in both conjuncts"
	else if ((not oP) andalso (not oQ)) then
	    let	val th1 =
		INST_TYPE [alpha |-> type_of x] BOTH_FORALL_OR_THM
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
		 let val f = mk_pabs(x,P)
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
		      let val g = mk_pabs(x,Q)
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
handle e => raise (wrap_exn "PFORALL_OR_CONV" "" e);

(* ------------------------------------------------------------------------- *)
(* OR_PFORALL_CONV "(!x.P) \/ (!x.Q)" = |- (!x.P) \/ (!x.Q) = (!x. P \/ Q)   *)
(* ------------------------------------------------------------------------- *)

fun OR_PFORALL_CONV tm =
    let val ((x,P),(y,Q)) =
	let val (disj1,disj2) = dest_disj tm
	    val (x,P) = dest_pforall disj1
	    and (y,Q) = dest_pforall disj2
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
		 SYM (PFORALL_OR_CONV (mk_pforall (x, mk_disj(P,Q))))
    end
handle e => raise (wrap_exn "OR_FORALL_CONV" "" e);


(* ------------------------------------------------------------------------- *)
(* LEFT_OR_PFORALL_CONV "(!x.P) \/  Q" =                                     *)
(*   |- (!x.P) \/ Q = (!x'. P[x'/x] \/ Q)                                    *)
(* ------------------------------------------------------------------------- *)

fun LEFT_OR_PFORALL_CONV tm =
    let val ((x,P),Q) =
	let val (disj1,Q) = dest_disj tm
	    val (x,P) = dest_pforall disj1
	in
	    ((x,P),Q)
	end
	val f = mk_pabs(x,P)
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
handle HOL_ERR _ => raise (ERR "LEFT_OR_PFORALL_CONV"
		               "expecting `(!x.P) \\/ Q`");


(* ------------------------------------------------------------------------- *)
(* RIGHT_OR_PFORALL_CONV "P \/ (!x.Q)" =                                     *)
(*   |- P \/ (!x.Q) = (!x'. P \/ (Q[x'/x])                                   *)
(* ------------------------------------------------------------------------- *)

fun RIGHT_OR_PFORALL_CONV tm =
    let val (P,(x,Q)) =
	let val (P,disj2) = dest_disj tm
	    val (x,Q) = dest_pforall disj2
	in
	    (P,(x,Q))
	end
	val g = mk_pabs(x,Q)
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
handle HOL_ERR _ => raise (ERR "RIGHT_OR_FORALL_CONV"
		               "expecting `P \\/ (!x.Q)`");


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
	let val (Bvar,Body) = dest_pforall tm
	    val (ant,conseq) = dest_imp Body
	in
	    (Bvar,(ant,conseq))
	end
    handle HOL_ERR _ => failwith "expecting `!x. P ==> Q`"
	val oP = occs_in x P and oQ =  occs_in x Q
    in
	if (oP andalso oQ) then
	    failwith "bound pair occurs in both sides of `==>`"
	else if ((not oP) andalso (not oQ)) then
	    let val th1 = INST_TYPE[alpha |-> type_of x] BOTH_FORALL_IMP_THM
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
		let val f = mk_pabs(x,P)
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
		let val g = mk_pabs(x,Q)
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
handle e => raise (wrap_exn "PFORALL_IMP_CONV" "" e);

(* ------------------------------------------------------------------------- *)
(* LEFT_IMP_PEXISTS_CONV "(?x.P) ==>  Q" =                                   *)
(*   |- ((?x.P) ==> Q) = (!x'. P[x'/x] ==> Q)                                *)
(* ------------------------------------------------------------------------- *)

fun LEFT_IMP_PEXISTS_CONV tm =
    let val ((x,P),Q) =
	let val (ant,conseq) = dest_imp tm
	    val (Bvar,Body) = dest_pexists ant
	in
	    ((Bvar,Body),conseq)
	end
	val f = mk_pabs(x,P)
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
handle HOL_ERR _ => raise (ERR "LEFT_IMP_PEXISTS_CONV"
		               "expecting `(?p.P) ==> Q`");


(* ------------------------------------------------------------------------- *)
(* RIGHT_IMP_PFORALL_CONV "P ==> (!x.Q)" =                                   *)
(*   |- (P ==> (!x.Q)) = (!x'. P ==> (Q[x'/x])                               *)
(* ------------------------------------------------------------------------- *)

fun RIGHT_IMP_PFORALL_CONV tm =
    let val (P,(x,Q)) =
	let val (ant,conseq) = dest_imp tm
	    val (Bvar,Body) = dest_pforall conseq
	in
	    (ant,(Bvar,Body))
	end
	val g = mk_pabs(x,Q)
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
handle HOL_ERR _ => raise (ERR "RIGHT_IMP_FORALL_CONV"
		               "expecting `P ==> (!x.Q)`");


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
	let val (Bvar,Body) = dest_pexists tm
	    val (ant,conseq) = dest_imp Body
	in
	    (Bvar,(ant,conseq))
	end
    handle HOL_ERR _ => failwith "expecting `?x. P ==> Q`"
	val oP = occs_in x P and oQ =  occs_in x Q
    in
	if (oP andalso oQ) then
		failwith "bound pair occurs in both sides of `==>`"
	else if ((not oP) andalso (not oQ)) then
	    let	val th1 = INST_TYPE[alpha |-> type_of x] BOTH_EXISTS_IMP_THM
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
		let val f = mk_pabs(x,P)
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
		      let val g = mk_pabs(x,Q)
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
handle e => raise (wrap_exn "PEXISTS_IMP_CONV" "" e);


(* ------------------------------------------------------------------------- *)
(* LEFT_IMP_PFORALL_CONV "(!x. t1[x]) ==> t2" =                              *)
(*   |- (!x. t1[x]) ==> t2 = (?x'. t1[x'] ==> t2)                            *)
(* ------------------------------------------------------------------------- *)

fun LEFT_IMP_PFORALL_CONV tm =
    let val ((x,P),Q) =
	let val (ant,conseq) = dest_imp tm
	    val (Bvar,Body) = dest_pforall ant
	in
	    ((Bvar,Body),conseq)
	end
	val f = mk_pabs(x,P)
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
handle HOL_ERR _ => raise (ERR "LEFT_IMP_PFORALL_CONV"
		               "expecting `(!x.P) ==> Q`");

(* ------------------------------------------------------------------------- *)
(* RIGHT_IMP_EXISTS_CONV "t1 ==> (?x. t2)" =                                 *)
(*   |- (t1 ==> ?x. t2) = (?x'. t1 ==> t2[x'/x])                             *)
(* ------------------------------------------------------------------------- *)

fun RIGHT_IMP_PEXISTS_CONV tm =
    let val (P,(x,Q)) =
	let val (ant,conseq) = dest_imp tm
	    val (Bvar,Body) = dest_pexists conseq
	in
	    (ant,(Bvar,Body))
	end
	val g = mk_pabs(x,Q)
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
handle HOL_ERR _ => raise (ERR "RIGHT_IMP_PEXISTS_CONV"
		               "expecting `P ==> (!x.Q)`");

(* end Pair_conv *)

(* ---------------------------------------------------------------------*)
(* CONTENTS: functions which are common to paired universal and		*)
(*		existential quantifications.				*)
(* ---------------------------------------------------------------------*)

(* structure Pair_both1 :> Pair_both1 = struct *)


fun mk_fun(y1,y2) = y1 --> y2;
fun comma(ty1,ty2) = Term.inst[alpha |-> ty1, beta |-> ty2]pairSyntax.comma_tm

val PFORALL_THM = pairTheory.PFORALL_THM;
val PEXISTS_THM = pairTheory.PEXISTS_THM;

(* ------------------------------------------------------------------------- *)
(* CURRY_FORALL_CONV "!(x,y).t" = (|- (!(x,y).t) = (!x y.t))                 *)
(* ------------------------------------------------------------------------- *)


fun CURRY_FORALL_CONV tm =
    let val (xy,bod) = dest_pforall tm
	val (x,y) = pairSyntax.dest_pair xy
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
    let val (xy,bod) = dest_pexists tm
	val (x,y) = pairSyntax.dest_pair xy
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
    let val (x,Body) = dest_pforall tm
	val (y,bod) = dest_pforall Body
	val xy = pairSyntax.mk_pair(x,y)
	val result = mk_pforall (xy,bod)
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
    let val (x,Body) = dest_pexists tm
	val (y,bod) = dest_pexists Body
	val xy = pairSyntax.mk_pair(x,y)
	val result = mk_pexists (xy,bod)
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

(* end; Pair_both1 *)

(* ---------------------------------------------------------------------*)
(* CONTENTS: functions for dealing with paired universal quantification.*)
(* ---------------------------------------------------------------------*)

(* ------------------------------------------------------------------------- *)
(* Paired Specialisation:                                                    *)
(*    A |- !p.t                                                              *)
(*  ------------- PSPEC c [where c is free for p in t]                       *)
(*   A |- t[c/p]                                                             *)
(* ------------------------------------------------------------------------- *)

(* structure Pair_forall :> Pair_forall = struct *)

val FORALL_DEF = boolTheory.FORALL_DEF;

val PSPEC =
    let val spec_thm =
	prove
	(
	    --`!(x:'a) f. $!f ==> (f x)`--
	,
	    GEN_TAC THEN
	    GEN_TAC THEN
	    (PURE_ONCE_REWRITE_TAC [FORALL_DEF]) THEN
	    BETA_TAC THEN
	    DISCH_TAC THEN
	    (PURE_ASM_REWRITE_TAC []) THEN
	    BETA_TAC
	)
	val gxty = Type.alpha
	val gfty = alpha --> bool
	val gx = genvar gxty
	val gf = genvar gfty
	val sth = ISPECL [gx,gf] spec_thm
    in
	fn x =>
	fn th =>
	let val f = rand (concl th)
	    val xty = type_of x
	    and fty = type_of f
	    val gxinst = mk_var((fst o dest_var) gx, xty)
	    and gfinst = mk_var((fst o dest_var) gf, fty)
	in
	    (CONV_RULE PBETA_CONV)
	    (MP (INST_TY_TERM ([{residue=x,redex=gxinst},
                                {residue=f,redex=gfinst}],
			       [{residue=xty,redex=gxty}]) sth) th)
	end
    end
handle HOL_ERR _ => failwith "PSPEC";

fun PSPECL xl th = rev_itlist PSPEC xl th;

fun IPSPEC x th =
    let val (p,tm) = with_exn dest_pforall(concl th)
                    (ERR"IPSPEC" "input theorem not universally quantified")
	val (_,inst) = match_term p x
	    handle HOL_ERR _ => raise (ERR "IPSPEC"
			        "can't type-instantiate input theorem")
    in
	PSPEC x (INST_TYPE inst th) handle HOL_ERR _ =>
        raise (ERR "IPSPEC" "type variable free in assumptions")
    end;

val IPSPECL =
 let val tup = end_itlist (curry mk_pair)
     fun strip [] = K []
       | strip (_::ts) = fn t =>
          let val (Bvar,Body) = dest_pforall t in Bvar::(strip ts Body) end
 in
  fn xl =>
    if (null xl) then I
    else let val tupxl = tup xl
             val striper = strip xl
         in
	 fn th =>
	  let val pl = with_exn striper (concl th)
                       (ERR "IPSPECL"
                            "list of terms too long for theorem")
	       val (_,inst) = match_term (tup pl) tupxl handle HOL_ERR _ =>
                  raise (ERR "IPSPECL"
                             "can't type-instantiate input theorem")
	  in
             PSPECL xl (INST_TYPE inst th) handle HOL_ERR _ =>
              raise (ERR "IPSPECL" "type variable free in assumptions")
          end
         end
 end;


val pvariant =
    let fun uniq [] = []
	  | uniq (h::t) = h::uniq (filter (not o equal h) t)
	fun variantl avl [] = []
	  | variantl avl (h::t) =
	    let val h' = variant (avl@(filter is_var t)) h
	    in {residue=h',redex=h}::(variantl (h'::avl) t)
	    end
    in
  fn pl =>
  fn p =>
   let val avoid = (flatten (map ((map (assert is_var)) o strip_pair) pl))
       val originals = uniq (map (assert (fn p => is_var p orelse is_const p))
                                 (strip_pair p))
       val subl = variantl avoid originals
   in
     subst subl p
  end end;

fun PSPEC_PAIR th =
    let val (p,_) = dest_pforall (concl th)
	val p' = pvariant (free_varsl (hyp th)) p
    in
	(p', PSPEC p' th)
    end;

val PSPEC_ALL =
    let fun f p (ps,l) =
	let val p' = pvariant ps p
	in
	    ((free_vars p')@ps,p'::l)
	end
    in
	fn th =>
	let val (hxs,con) = (free_varsl ## I) (dest_thm th)
	    val fxs = free_vars con
	    and pairs = fst(strip_pforall con)
	in
	    PSPECL (snd(itlist f pairs (hxs @ fxs,[]))) th
	end
    end;

fun GPSPEC th =
    let val (_,t) = dest_thm th
    in
	if is_pforall t then
	    GPSPEC (PSPEC
             (genvarstruct (type_of (fst (dest_pforall t)))) th)
	else
	    th
    end;


fun PSPEC_TAC (t,x) =
    if (not (is_pair t)) andalso (is_var x) then
	SPEC_TAC (t,x)
    else if (is_pair t) andalso (is_pair x) then
	let val (t1,t2) = dest_pair t
	    val (x1,x2) = dest_pair x
	in
	    (PSPEC_TAC (t2,x2)) THEN
	    (PSPEC_TAC (t1,x1)) THEN
	    (CONV_TAC UNCURRY_FORALL_CONV)
	end
    else if (not (is_pair t)) andalso (is_pair x) then
	let val x' = genvar (type_of x)
	in
	    (SPEC_TAC (t,x')) THEN
	    (CONV_TAC (GEN_PALPHA_CONV x))
	end
    else (* (is_pair t) & (is_var x) *)
	let val (fst,snd) = dest_pair t
	    val x' = mk_pair(genvar(type_of fst), genvar(type_of snd))
	in
	    (PSPEC_TAC (t,x')) THEN
	    (CONV_TAC (GEN_PALPHA_CONV x))
	end
    handle HOL_ERR _ => failwith "PSPEC_TAC";

(* ------------------------------------------------------------------------- *)
(* Paired Generalisation:                                                    *)
(*    A |- t                                                                 *)
(*  ----------- PGEN p [where p is not free in A]                            *)
(*   A |- !p.t                                                               *)
(* ------------------------------------------------------------------------- *)

fun PGEN p th =
    if is_var p then
	GEN p th
    else (* is_pair p *)
	let val (v1, v2) = dest_pair p
	in
	    CONV_RULE UNCURRY_FORALL_CONV (PGEN v1 (PGEN v2 th))
	end
    handle HOL_ERR _ => failwith "PGEN" ;

fun PGENL xl th = itlist PGEN xl th;;

fun P_PGEN_TAC p :tactic = fn (a,t) =>
    let val (x,b) = with_exn dest_pforall t
            (ERR "P_PGEN_TAC" "Goal not universally quantified")
    in
	if (is_var x) andalso (is_var p) then
	    X_GEN_TAC p (a,t)
	else if (is_pair x) andalso (is_pair p) then
	    let val (p1,p2) = dest_pair p
	    in
		((CONV_TAC CURRY_FORALL_CONV) THEN
		(P_PGEN_TAC p1) THEN
		(P_PGEN_TAC p2)) (a,t)
	    end
	else if (is_var p) andalso (is_pair x) then
	    let val x' = genvar (type_of p)
	    in
		((CONV_TAC (GEN_PALPHA_CONV x')) THEN
		 (X_GEN_TAC p)) (a,t)
	    end
	else (*(is_pair p) & (is_var x)*)
	    let val (fst,snd) = dest_pair p
		val x' = mk_pair(genvar(type_of fst),genvar(type_of snd))
	    in
		((CONV_TAC (GEN_PALPHA_CONV x')) THEN
		(P_PGEN_TAC p)) (a,t)
	    end
    end
handle HOL_ERR _ => failwith "P_PGEN_TAC" ;

val PGEN_TAC : tactic = fn (a,t)  =>
    let val (x,b) = with_exn dest_pforall t
                           (ERR "PGEN_TAC" "Goal not universally quantified")
    in
	P_PGEN_TAC (pvariant (free_varsl(t::a)) x) (a,t)
    end;

fun FILTER_PGEN_TAC tm : tactic = fn (a,t) =>
    if (is_pforall t) andalso (not (tm = (fst (dest_pforall t)))) then
	PGEN_TAC (a,t)
    else
	failwith "FILTER_PGEN_TAC";
(* end;  Pair_forall *)

(* ---------------------------------------------------------------------*)
(* CONTENTS: functions for paired existential quantifications.          *)
(* ---------------------------------------------------------------------*)

(* structure Pair_exists :> Pair_exists = struct *)

val EXISTS_DEF = boolTheory.EXISTS_DEF;
val EXISTS_UNIQUE_DEF = boolTheory.EXISTS_UNIQUE_DEF;

fun mk_fun(y1,y2) = (y1 --> y2)

val PEXISTS_CONV =
    let val f = (--`f:'a->bool`--)
	val th1 = AP_THM EXISTS_DEF f
	val th2 = GEN f ((CONV_RULE (RAND_CONV BETA_CONV)) th1)
    in
	fn tm =>
	let val (p,b) = dest_pexists tm
	    val g = mk_pabs(p,b)
	in
	    (CONV_RULE (RAND_CONV PBETA_CONV)) (ISPEC g th2)
	end
    end
handle HOL_ERR _ => failwith "PEXISTS_CONV" ;

(* ------------------------------------------------------------------------- *)
(*    A |- ?p. t[p]                                                          *)
(* ------------------ PSELECT_RULE                                           *)
(*  A |- t[@p .t[p]]                                                         *)
(* ------------------------------------------------------------------------- *)

val PSELECT_RULE = CONV_RULE PEXISTS_CONV ;

(* ------------------------------------------------------------------------- *)
(* PSELECT_CONV "t [@p. t[p]]" = (|- (t [@p. t[p]]) = (?p. t[p]))            *)
(* ------------------------------------------------------------------------- *)

val PSELECT_CONV =
    let fun find_first p tm =
	if p tm then
	    tm
	else if is_abs tm then
	    find_first p (body tm)
	else if is_comb tm then
	    let val (f,a) = dest_comb tm
	    in
		(find_first p f) handle HOL_ERR _ => (find_first p a)
	    end
	else
	    failwith""
    in
	fn tm =>
	let fun right t = is_pselect t andalso
			   (rhs (concl (PBETA_CONV (mk_comb(rand t,t)))) = tm)
	    val epi = find_first right tm
	    val (p,b) = dest_pselect epi
	in
	    SYM (PEXISTS_CONV (mk_pexists(p,b)))
	end
    end
handle HOL_ERR _ => failwith "PSELECT_CONV" ;


(* ------------------------------------------------------------------------- *)
(*  A |- t[@p .t[p]]                                                         *)
(* ------------------ PEXISTS_RULE                                           *)
(*    A |- ?p. t[p]                                                          *)
(* ------------------------------------------------------------------------- *)

val PEXISTS_RULE = CONV_RULE PSELECT_CONV ;

(* ------------------------------------------------------------------------- *)
(*    A |- P t                                                               *)
(* -------------- PSELECT_INTRO                                              *)
(*  A |- P($@ P)                                                             *)
(* ------------------------------------------------------------------------- *)

val PSELECT_INTRO = SELECT_INTRO ;

(* ------------------------------------------------------------------------- *)
(*  A1 |- f($@ f)  ,  A2, f p |- t                                           *)
(* -------------------------------- PSELECT_ELIM th1 ("p", th2) [p not free] *)
(*          A1 u A2 |- t                                                     *)
(* ------------------------------------------------------------------------- *)

fun  PSELECT_ELIM th1 (v,th2) =
    let val (f,sf) = dest_comb (concl th1)
	val t1 = MP (PSPEC sf (PGEN v (DISCH (mk_comb(f,v)) th2))) th1
	val t2 = ALPHA (concl t1) (concl th2)
    in
	EQ_MP t2 t1
    end
handle HOL_ERR _ => failwith "PSELECT_ELIM" ;

(* ------------------------------------------------------------------------- *)
(*  A |- t[q]                                                                *)
(* ----------------- PEXISTS ("?p. t[p]", "q")                               *)
(*  A |- ?p. t[p]                                                            *)
(* ------------------------------------------------------------------------- *)

fun PEXISTS (fm,tm) th =
    let val (p,b) = dest_pexists fm
	val th1 = PBETA_CONV (mk_comb(mk_pabs(p,b),tm))
	val th2 = EQ_MP (SYM th1) th
	val th3 = PSELECT_INTRO th2
	val th4 = AP_THM(INST_TYPE [alpha |-> type_of p] EXISTS_DEF)
                        (mk_pabs(p, b))
	val th5 = TRANS th4 (BETA_CONV(rhs(concl th4)))
    in
	EQ_MP (SYM th5) th3
    end
handle HOL_ERR _ => failwith "PEXISTS" ;

(* ------------------------------------------------------------------------- *)
(*  A1 |- ?p. t[p]  ,  A2, t[v] |- u                                         *)
(* ---------------------------------- PCHOOSE (v,th1) th2 [v not free]       *)
(*             A1 u A2 |- u                                                  *)
(* ------------------------------------------------------------------------- *)

val PCHOOSE =
    let val f = (--`f:'a->bool`--)
	val t1 = AP_THM EXISTS_DEF f
	val t2 = GEN f ((CONV_RULE (RAND_CONV BETA_CONV)) t1)
    in
        fn (v,th1) =>
	fn th2 =>
	let val p = rand (concl th1)
	    val th1' = EQ_MP (ISPEC p t2) th1
	    val u1 = UNDISCH (fst
                       (EQ_IMP_RULE (PBETA_CONV (mk_comb(p,v)))))
	    val th2' = PROVE_HYP u1 th2
	in
	    PSELECT_ELIM th1' (v,th2')
	end
    end
handle HOL_ERR _ => failwith "PCHOOSE" ;

fun P_PCHOOSE_THEN v ttac pth :tactic =
    let val (p,b) = dest_pexists (concl pth)
	handle HOL_ERR _ => failwith "P_PCHOOSE_THEN"
    in
	fn (asl,w) =>
	let val th = itlist ADD_ASSUM (hyp pth)
	                    (ASSUME
			     (rhs(concl(PBETA_CONV
                                 (mk_comb(mk_pabs(p,b),v))))))
	    val (gl,prf) = ttac th (asl,w)
	in
	    (gl, (PCHOOSE (v, pth)) o prf)
	end
    end;

fun PCHOOSE_THEN ttac pth :tactic =
    let val (p,b) = dest_pexists (concl pth)
	handle HOL_ERR _ => failwith "CHOOSE_THEN"
    in
	fn (asl,w) =>
	let val q = pvariant ((thm_frees pth) @ (free_varsl (w::asl))) p
	    val th =
		itlist
		    ADD_ASSUM
		    (hyp pth)
		    (ASSUME
	              (rhs (concl
	               (PairedLambda.PAIRED_BETA_CONV
                           (mk_comb(mk_pabs(p,b),q))))))
	    val (gl,prf) = ttac th (asl,w)
	in
	    (gl, (PCHOOSE (q, pth)) o prf)
	end
    end;


fun P_PCHOOSE_TAC p = P_PCHOOSE_THEN p ASSUME_TAC ;

val PCHOOSE_TAC = PCHOOSE_THEN ASSUME_TAC ;

(* ------------------------------------------------------------------------- *)
(*  A ?- ?p. t[p]                                                            *)
(* =============== PEXISTS_TAC "u"                                           *)
(*    A ?- t[u]                                                              *)
(* ------------------------------------------------------------------------- *)

fun PEXISTS_TAC v :tactic = fn (a, t) =>
    let val (p,b) = dest_pexists t
    in
	([(a, rhs (concl (PBETA_CONV (mk_comb(mk_pabs(p,b),v)))))
         ],
	 fn [th] => PEXISTS (t,v) th)
    end
handle HOL_ERR _ => failwith "PEXISTS_TAC" ;

(* ------------------------------------------------------------------------- *)
(*  |- ?!p. t[p]                                                             *)
(* -------------- PEXISTENCE                                                 *)
(*  |- ?p. t[p]                                                              *)
(* ------------------------------------------------------------------------- *)

fun PEXISTENCE th =
    let val (p,b) = dest_pabs (rand (concl th))
	val th1 =
	    AP_THM
	    (INST_TYPE [alpha |-> type_of p] EXISTS_UNIQUE_DEF) (mk_pabs(p,b))
	val th2 = EQ_MP th1 th
	val th3 = CONV_RULE BETA_CONV th2
    in
	CONJUNCT1 th3
    end
handle HOL_ERR _ => failwith "PEXISTENCE" ;

(* ------------------------------------------------------------------------- *)
(* PEXISTS_UNIQUE_CONV "?!p. t[p]" =                                         *)
(*   (|- (?!p. t[p]) = (?p. t[p] /\ !p p'. t[p] /\ t[p'] ==> (p='p)))        *)
(* ------------------------------------------------------------------------- *)

fun PEXISTS_UNIQUE_CONV tm =
    let val (p,b) = dest_pabs (rand tm)
	val p' = pvariant (p::(free_vars tm)) p
	val th1 =
	    AP_THM
	    (INST_TYPE [alpha |-> type_of p] EXISTS_UNIQUE_DEF) (mk_pabs(p,b))
	val th2 = CONV_RULE (RAND_CONV BETA_CONV) th1
	val th3 = CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV (ABS_CONV
				       (GEN_PALPHA_CONV p'))))) th2
	val th4 = CONV_RULE (RAND_CONV (RAND_CONV (GEN_PALPHA_CONV p))) th3
	val th5 = CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV (PABS_CONV
		             (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
			      (RATOR_CONV (RAND_CONV PBETA_CONV)))))))))) th4
    in
	CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV (PABS_CONV
	    (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
	    (RAND_CONV PBETA_CONV))))))))) th5
    end
handle HOL_ERR _ => failwith "PEXISTS_UNIQUE_CONV" ;

(* ------------------------------------------------------------------------- *)
(* P_PSKOLEM_CONV : introduce a skolem function.                             *)
(*                                                                           *)
(*   |- (!x1...xn. ?y. tm[x1,...,xn,y])                                      *)
(*        =                                                                  *)
(*      (?f. !x1...xn. tm[x1,..,xn,f x1 ... xn]                              *)
(*                                                                           *)
(* The first argument is the function f.                                     *)
(* ------------------------------------------------------------------------- *)

local fun BABY_P_PSKOLEM_CONV f =
    if not(is_vstruct f) then
	raise ERR "P_SKOLEM_CONV" "first argument not a varstruct"
    else
	fn tm =>
	let val (xs,(y,P)) = (I ## dest_exists) (strip_pforall tm)
	    val fx = with_exn list_mk_comb(f,xs)
		(ERR"P_SKOLEM_CONV" "function variable has the wrong type")
	in
	    if free_in f tm then
		raise ERR "P_SKOLEM_CONV"
			  "skolem function free in the input term"
	    else
		let val pat = mk_exists(f,list_mk_pforall(xs,subst[y |-> fx]P))
		    val fnc = list_mk_pabs(xs,mk_select(y,P))
		    val bth = SYM(LIST_PBETA_CONV (list_mk_comb(fnc,xs)))
		    val thm1 =
			SUBST[y |-> bth] P (SELECT_RULE(PSPECL xs (ASSUME tm)))
		    val imp1 = DISCH tm (EXISTS (pat,fnc) (PGENL xs thm1))
		    val thm2 = PSPECL xs (ASSUME (snd(dest_exists pat)))
		    val thm3 = PGENL xs (EXISTS (mk_exists(y,P),fx) thm2)
		    val imp2 = DISCH pat (CHOOSE (f,ASSUME pat) thm3)
		in
		    IMP_ANTISYM_RULE imp1 imp2
		end
	end
in
    fun P_PSKOLEM_CONV f =
	if not (is_vstruct f) then
	    raise ERR"P_SKOLEM_CONV" "first argument not a variable pair"
	else
	    fn tm =>
	    let val (xs,(y,P)) = (I##dest_pexists) (strip_pforall tm)
		handle HOL_ERR _ => raise ERR "P_SKOLEM_CONV"
				      "expecting `!x1...xn. ?y.tm`"
		val FORALL_CONV =
		     end_itlist
			(curry (op o))
			(map (K (RAND_CONV o PABS_CONV)) xs)
	    in
		if is_var f then
		    if is_var y then
			BABY_P_PSKOLEM_CONV f tm
		    else (* is_pair y *)
			let val y' = genvar (type_of y)
			    val tha1 =
				(FORALL_CONV (RAND_CONV (PALPHA_CONV y'))) tm
			in
			    CONV_RULE (RAND_CONV (BABY_P_PSKOLEM_CONV f)) tha1
			end
		else (* is_par f *)
		    let val (f1,f2) = dest_pair f
			val thb1 =
			    if is_var y then
				let val (y1',y2') =
				    (genvar ## genvar) (dest_prod (type_of y))
				    handle HOL_ERR _ => raise
                                     ERR "P_PSKOLEM_CONV"
			             "existential variable not of pair type"
				in
				(FORALL_CONV
				  (RAND_CONV
				   (PALPHA_CONV (mk_pair(y1',y2')))))tm
				end
			    else
				REFL tm
			val thb2 =
			    CONV_RULE
			    (RAND_CONV (FORALL_CONV CURRY_EXISTS_CONV))
			    thb1
			val thb3 = CONV_RULE (RAND_CONV (P_PSKOLEM_CONV f1))
                                             thb2
			val thb4 = CONV_RULE(RAND_CONV
					     (RAND_CONV (PABS_CONV
							 (P_PSKOLEM_CONV f2))))
                                            thb3
		    in
			CONV_RULE (RAND_CONV UNCURRY_EXISTS_CONV) thb4
		    end
	    end
end;

(* ------------------------------------------------------------------------- *)
(* PSKOLEM_CONV : introduce a skolem function.                               *)
(*                                                                           *)
(*   |- (!x1...xn. ?y. tm[x1,...,xn,y])                                      *)
(*        =                                                                  *)
(*      (?y'. !x1...xn. tm[x1,..,xn,f x1 ... xn]                             *)
(*                                                                           *)
(* Where y' is a primed variant of y not free in the input term.             *)
(* ------------------------------------------------------------------------- *)

val PSKOLEM_CONV =
    let fun mkfn tm tyl =
	if is_var tm then
	    let val (n,t) = dest_var tm
	    in
		mk_var(n, itlist (curry (op -->)) tyl t)
	    end
	else
	    let val (p1,p2) = dest_pair tm
	    in
		mk_pair(mkfn p1 tyl, mkfn p2 tyl)
	    end
    in
	fn tm =>
	let val (xs,(y,P)) = (I ## dest_pexists) (strip_pforall tm)
	    val f = mkfn y (map type_of xs)
	    val f' = pvariant (free_vars tm) f
	in
	    P_PSKOLEM_CONV f' tm
	end
    end
handle HOL_ERR _ => failwith "PSKOLEM_CONV: expecting `!x1...xn. ?y.tm`";

(* end; Pair_exists *)

(* ---------------------------------------------------------------------*)
(* CONTENTS: Functions which are common to both paired universal and	*)
(*           existential quantifications and which rely on more		*)
(*           primitive functions.                                       *)
(*                                                                      *)
(* Paired stripping tactics, same as basic ones, but they use PGEN_TAC  *)
(* and PCHOOSE_THEN rather than GEN_TAC and CHOOSE_THEN                 *)
(* ---------------------------------------------------------------------*)

(* structure Pair_both2 :> Pair_both2 = struct *)


val PSTRIP_THM_THEN =
    FIRST_TCL [CONJUNCTS_THEN, DISJ_CASES_THEN, PCHOOSE_THEN];

val PSTRIP_ASSUME_TAC =
    (REPEAT_TCL PSTRIP_THM_THEN) CHECK_ASSUME_TAC;

val PSTRUCT_CASES_TAC =
    REPEAT_TCL PSTRIP_THM_THEN
	 (fn th => SUBST1_TAC th  ORELSE  ASSUME_TAC th);

fun PSTRIP_GOAL_THEN ttac = FIRST [PGEN_TAC, CONJ_TAC, DISCH_THEN ttac];

fun FILTER_PSTRIP_THEN ttac tm =
    FIRST [
	FILTER_PGEN_TAC tm,
	FILTER_DISCH_THEN ttac tm,
	CONJ_TAC ];

val PSTRIP_TAC = PSTRIP_GOAL_THEN PSTRIP_ASSUME_TAC;

val FILTER_PSTRIP_TAC = FILTER_PSTRIP_THEN PSTRIP_ASSUME_TAC;

(* ------------------------------------------------------------------------- *)
(*  A |- !p. (f p) = (g p)                                                   *)
(* ------------------------ PEXT                                             *)
(*       A |- f = g                                                          *)
(* ------------------------------------------------------------------------- *)

fun PEXT th =
    let val (p,_) = dest_pforall (concl th)
	val p' = pvariant (thm_frees th) p
	val th1 = PSPEC p' th
	val th2 = PABS p' th1
	val th3 = (CONV_RULE (RATOR_CONV (RAND_CONV PETA_CONV))) th2
    in
	(CONV_RULE (RAND_CONV PETA_CONV)) th3
    end
handle HOL_ERR _ => failwith "PEXT";

(* ------------------------------------------------------------------------- *)
(* P_FUN_EQ_CONV "p" "f = g" = |- (f = g) = (!p. (f p) = (g p))              *)
(* ------------------------------------------------------------------------- *)

val P_FUN_EQ_CONV =
    let val gpty = alpha
	val grange = beta
	val gfty = alpha --> beta
	val gf = genvar gfty
	val gg = genvar gfty
	val gp = genvar gpty
	val imp1 = DISCH_ALL (GEN gp (AP_THM (ASSUME (mk_eq(gf,gg))) gp))
	val imp2 = DISCH_ALL (EXT (ASSUME
                     (mk_forall(gp,mk_eq(mk_comb(gf,gp),mk_comb(gg,gp))))))
	val ext_thm = IMP_ANTISYM_RULE imp1 imp2
    in
	fn p =>
	fn tm =>
	let val (f,g) = dest_eq tm
	    val fty = type_of f
	    and pty = type_of p
	    val gfinst = mk_var((fst o dest_var)gf, fty)
	    and gginst = mk_var((fst o dest_var)gg, fty)
	    val rnge = hd (tl(snd(dest_type fty)))
	    val th =
		INST_TY_TERM
		    ([{residue=f,redex=gfinst},{residue=g,redex=gginst}],
		     [{residue=pty,redex=gpty},{residue=rnge,redex=grange}])
		    ext_thm
	in
	    (CONV_RULE (RAND_CONV (RAND_CONV (PALPHA_CONV p)))) th
	end
    end;


(* ------------------------------------------------------------------------- *)
(*      A |- !p. t = u                                                       *)
(* ------------------------ MK_PABS                                          *)
(*  A |- (\p. t) = (\p. u)                                                   *)
(* ------------------------------------------------------------------------- *)

fun MK_PABS th =
    let val (p,_) = dest_pforall (concl th)
	val th1 = (CONV_RULE (RAND_CONV (PABS_CONV (RATOR_CONV (RAND_CONV
						   (UNPBETA_CONV p)))))) th
	val th2 = (CONV_RULE (RAND_CONV (PABS_CONV (RAND_CONV
					(UNPBETA_CONV p))))) th1
	val th3 = PEXT th2
	val th4 = (CONV_RULE (RATOR_CONV (RAND_CONV (PALPHA_CONV p)))) th3
    in
	(CONV_RULE (RAND_CONV (PALPHA_CONV p))) th4
    end
handle HOL_ERR _ => failwith "MK_PABS";

(* ------------------------------------------------------------------------- *)
(*  A |- !p. t p = u                                                         *)
(* ------------------ HALF_MK_PABS                                           *)
(*  A |- t = (\p. u)                                                         *)
(* ------------------------------------------------------------------------- *)

fun HALF_MK_PABS th =
    let val (p,_) = dest_pforall (concl th)
	val th1 = (CONV_RULE (RAND_CONV (PABS_CONV (RAND_CONV
						    (UNPBETA_CONV p))))) th
	val th2 = PEXT th1
    in
	(CONV_RULE (RAND_CONV (PALPHA_CONV p))) th2
    end
handle HOL_ERR _ => failwith "HALF_MK_PABS" ;

(* ------------------------------------------------------------------------- *)
(*      A |- !p. t = u                                                       *)
(* ------------------------ MK_PFORALL                                       *)
(*  A |- (!p. t) = (!p. u)                                                   *)
(* ------------------------------------------------------------------------- *)

fun MK_PFORALL th =
    let val (p,_) = dest_pforall (concl th)
    in
	AP_TERM
	(mk_const("!",(type_of p --> bool) --> bool))
	(MK_PABS th)
    end
handle HOL_ERR _ => failwith "MK_PFORALL" ;


(* ------------------------------------------------------------------------- *)
(*      A |- !p. t = u                                                       *)
(* ------------------------ MK_PEXISTS                                       *)
(*  A |- (?p. t) = (?p. u)                                                   *)
(* ------------------------------------------------------------------------- *)

fun MK_PEXISTS th =
    let val (p,_) = dest_pforall (concl th)
    in
	AP_TERM
	(mk_const("?",(type_of p --> bool) --> bool))
	(MK_PABS th)
    end
handle HOL_ERR _ => failwith "MK_PEXISTS" ;

(* ------------------------------------------------------------------------- *)
(*      A |- !p. t = u                                                       *)
(* ------------------------ MK_PSELECT                                       *)
(*  A |- (@p. t) = (@p. u)                                                   *)
(* ------------------------------------------------------------------------- *)

fun MK_PSELECT th =
    let val (p,_) = dest_pforall (concl th)
	val pty = type_of p
    in
	AP_TERM
	(mk_const("@",(pty --> bool)--> pty))
	(MK_PABS th)
    end
handle HOL_ERR _ => failwith "MK_PSELECT" ;

(* ------------------------------------------------------------------------- *)
(*       A |- t = u                                                          *)
(* ------------------------ PFORALL_EQ "p"                                   *)
(*  A |- (!p. t) = (!p. u)                                                   *)
(* ------------------------------------------------------------------------- *)

fun PFORALL_EQ p th =
   let val pty = type_of p
   in
       AP_TERM
       (mk_const("!",(pty --> bool) --> bool))
       (PABS p th)
   end
handle HOL_ERR _ => failwith "PFORALL_EQ" ;

(* ------------------------------------------------------------------------- *)
(*       A |- t = u                                                          *)
(* ------------------------ PEXISTS_EQ "p"                                   *)
(*  A |- (?p. t) = (?p. u)                                                   *)
(* ------------------------------------------------------------------------- *)

fun PEXISTS_EQ p th =
    let val pty = type_of p
    in
	AP_TERM
	(mk_const("?",(pty --> bool) --> bool))
	(PABS p th)
    end
handle HOL_ERR _ => failwith "PEXISTS_EQ" ;

(* ------------------------------------------------------------------------- *)
(*       A |- t = u                                                          *)
(* ------------------------ PSELECT_EQ "p"                                   *)
(*  A |- (@p. t) = (@p. u)                                                   *)
(* ------------------------------------------------------------------------- *)

fun PSELECT_EQ p th =
    let val pty = type_of p
    in
	AP_TERM
	(mk_const("@",(pty --> bool) --> pty))
	(PABS p th)
    end
handle HOL_ERR _ => failwith "PSELECT_EQ" ;

(* ------------------------------------------------------------------------- *)
(*                A |- t = u                                                 *)
(* ---------------------------------------- LIST_MK_PFORALL [p1;...pn]       *)
(*  A |- (!p1 ... pn. t) = (!p1 ... pn. u)                                   *)
(* ------------------------------------------------------------------------- *)

val LIST_MK_PFORALL = itlist PFORALL_EQ ;

(* ------------------------------------------------------------------------- *)
(*                A |- t = u                                                 *)
(* ---------------------------------------- LIST_MK_PEXISTS [p1;...pn]       *)
(*  A |- (?p1 ... pn. t) = (?p1 ... pn. u)                                   *)
(* ------------------------------------------------------------------------- *)

val LIST_MK_PEXISTS = itlist PEXISTS_EQ ;

(* ------------------------------------------------------------------------- *)
(*         A |- P ==> Q                                                      *)
(* -------------------------- EXISTS_IMP "p"                                 *)
(*  A |- (?p. P) ==> (?p. Q)                                                 *)
(* ------------------------------------------------------------------------- *)

fun PEXISTS_IMP p th =
    let val (a,c) = dest_imp (concl th)
	val th1 = PEXISTS (mk_pexists(p,c),p) (UNDISCH th)
	val asm = mk_pexists(p,a)
	val th2 = DISCH asm (PCHOOSE (p, ASSUME asm) th1)
    in
	(CONV_RULE (RAND_CONV (GEN_PALPHA_CONV p))) th2
    end
handle HOL_ERR _ => failwith "PEXISTS_IMP";

(* ------------------------------------------------------------------------- *)
(* SWAP_PFORALL_CONV "!p q. t" = (|- (!p q. t) = (!q p. t))                  *)
(* ------------------------------------------------------------------------- *)

val genlike = genvarstruct o type_of;

fun SWAP_PFORALL_CONV pqt =
    let val (p,qt) = dest_pforall pqt
	val (q,t) = dest_pforall qt
	val p' = genlike p
	val q' = genlike q
	val th1 = GEN_PALPHA_CONV p' pqt
	val th2 = CONV_RULE(RAND_CONV (RAND_CONV
				       (PABS_CONV (GEN_PALPHA_CONV q')))) th1
        val t' = (snd o dest_pforall o snd o dest_pforall o rhs o concl)th2
	val pqt' = list_mk_pforall([p',q'],t')
        and qpt' = list_mk_pforall([q',p'],t')
	val th3 = IMP_ANTISYM_RULE
	          ((DISCH pqt' o PGENL[q',p'] o PSPECL[p',q'] o ASSUME)pqt')
	          ((DISCH qpt' o PGENL[p',q'] o PSPECL[q',p'] o ASSUME)qpt')
	val th4 = CONV_RULE(RAND_CONV(GEN_PALPHA_CONV q))th3
	val th5 = CONV_RULE(RAND_CONV (RAND_CONV
				       (PABS_CONV (GEN_PALPHA_CONV p)))) th4
    in
	TRANS th2 th5
    end
handle HOL_ERR _ => failwith "SWAP_PFORALL_CONV";


(* ------------------------------------------------------------------------- *)
(* SWAP_PEXISTS_CONV "?p q. t" = (|- (?p q. t) = (?q p. t))                  *)
(* ------------------------------------------------------------------------- *)

fun SWAP_PEXISTS_CONV xyt =
   let val (x,yt) = dest_pexists xyt
       val (y,t) = dest_pexists yt
       val xt = mk_pexists (x,t)
       val yxt = mk_pexists(y,xt)
       val t_thm = ASSUME t
   in
   IMP_ANTISYM_RULE
         (DISCH xyt (PCHOOSE (x,ASSUME xyt) (PCHOOSE (y, (ASSUME yt))
          (PEXISTS (yxt,y) (PEXISTS (xt,x) t_thm)))))
         (DISCH yxt (PCHOOSE (y,ASSUME yxt) (PCHOOSE (x, (ASSUME xt))
         (PEXISTS (xyt,x) (PEXISTS (yt,y) t_thm)))))
   end
handle HOL_ERR _ => failwith "SWAP_PEXISTS_CONV";

(* --------------------------------------------------------------------- *)
(* PART_PMATCH : just like PART_MATCH but doesn't mind leading paird q.s *)
(* --------------------------------------------------------------------- *)

fun PART_PMATCH partfn th =
    let val pth = GPSPEC (GSPEC (GEN_ALL th))
	val pat = partfn (concl pth)
	val matchfn = match_term pat
    in
	fn tm => INST_TY_TERM (matchfn tm) pth
    end;


(* --------------------------------------------------------------------- *)
(*  A ?- !v1...vi. t'                                                    *)
(* ================== MATCH_MP_TAC (A' |- !x1...xn. s ==> !y1...tm. t)	 *)
(*  A ?- ?z1...zp. s'                                                    *)
(* where z1, ..., zp are (type instances of) those variables among	 *)
(* x1, ..., xn that do not occur free in t.				 *)
(* --------------------------------------------------------------------- *)

val PMATCH_MP_TAC : thm_tactic =
    let fun efn p (tm,th) =
	let val ntm = mk_pexists(p,tm)
	in
	    (ntm, PCHOOSE (p, ASSUME ntm) th)
	end
    in
	fn thm =>
	let val (tps,(ant,conseq)) = ((I ## dest_imp) o strip_pforall o concl)
                                     thm
	    handle HOL_ERR _ => raise ERR "MATCH_MP_TAC" "not an implication"
	    val (cps,con) = strip_forall conseq
	    val th1 = PSPECL cps (UNDISCH (PSPECL tps thm))
	    val eps = filter (fn p => not (occs_in p con)) tps
	    val th2 = uncurry DISCH (itlist efn eps (ant,th1))
	in
	    fn (A,g) =>
	    let val (gps,gl) = strip_pforall g
		val ins = match_term con gl handle HOL_ERR _ =>
                raise ERR "PMATCH_MP_TAC" "no match"
		val ith = INST_TY_TERM ins th2
		val newg = fst(dest_imp(concl ith))
		val gth = PGENL gps (UNDISCH ith) handle HOL_ERR _ =>
                raise ERR "PMATCH_MP_TAC" "generalized pair(s)"
	    in
		([(A,newg)], fn [th] => PROVE_HYP th gth)
	    end
	end
    end;


(* --------------------------------------------------------------------- *)
(*  A1 |- !x1..xn. t1 ==> t2   A2 |- t1'            			*)
(* --------------------------------------  PMATCH_MP			*)
(*        A1 u A2 |- !xa..xk. t2'					*)
(* --------------------------------------------------------------------- *)

fun gen_assoc (keyf,resf)item =
 let fun assc (v::rst) = if (item = keyf v) then resf v else assc rst
       | assc [] = raise ERR "gen_assoc" "not found"
 in
    assc
 end;


val PMATCH_MP =
    let fun variants asl [] = []
	  | variants asl (h::t) =
	    let val h' = variant (asl@(filter (fn e => not (e = h)) t)) h
	    in {residue=h',redex=h}::(variants (h'::asl) t)
	    end
	fun frev_assoc e2 (l:(''a,''a)subst) = gen_assoc(#redex,#residue)e2 l
	    handle HOL_ERR _ => e2
    in
	fn ith =>
	let val t = (fst o dest_imp o snd o strip_pforall o concl) ith
	    handle HOL_ERR _ => raise ERR "PMATCH_MP" "not an implication"
	in
	    fn th =>
	    let val (B,t') = dest_thm th
		val ty_inst = snd (match_term t t')
		val ith_ = INST_TYPE ty_inst ith
		val (A_, forall_ps_t_imp_u_) = dest_thm ith_
		val (ps_,t_imp_u_) = strip_pforall forall_ps_t_imp_u_
		val (t_,u_) = dest_imp (t_imp_u_)
		val pvs = free_varsl ps_
		val A_vs = free_varsl A_
		val B_vs = free_varsl B
		val tm_inst = fst (match_term t_ t')
		val (match_vs, unmatch_vs) = partition (C free_in t_)
                                                       (free_vars u_)
		val rename = subtract unmatch_vs (subtract A_vs pvs)
		val new_vs = free_varsl (map (C frev_assoc tm_inst) match_vs)
		val renaming = variants (new_vs@A_vs@B_vs) rename
		val (specs,insts) = partition (C mem (free_varsl pvs) o #redex)
		    (renaming@tm_inst)
		val spec_list = map (subst specs) ps_
		val mp_th = MP (PSPECL spec_list (INST insts ith_)) th
		val gen_ps = (filter (fn p => null (subtract (strip_pair p)
						             rename)) ps_)
		val qs = map (subst renaming) gen_ps
	    in
		PGENL qs mp_th
	    end
	end
    end
handle HOL_ERR _ => failwith "PMATCH_MP: can't instantiate theorem";

(* end;  Pair_both2 *)

end
