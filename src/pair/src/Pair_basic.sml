(*****************************************************************************)
(* Hi Mike,                                                                  *)
(*                                                                           *)
(*   I spent a little time making Pair_basic work in Kananaskis-0. This      *)
(* includes PBETA_CONV, PALPHA_CONV, GEN_PALPHA_CONV and some other useful   *)
(* things. Pair_basic is at the bottom of the Grundy hierarchy, so it        *)
(* doesn't depend on other things. Probably, you should just compile it in   *)
(* your development directory.                                               *)
(*                                                                           *)
(* In the following, Pair_basic.sig comes before Pair_basic.sml.             *)
(*                                                                           *)
(* Konrad.                                                                   *)
(*****************************************************************************)

structure Pair_basic :> Pair_basic =
struct

open HolKernel boolLib pairSyntax Abbrev;

infix THENC |->
infixr -->;

val PAIR_ERR = mk_HOL_ERR "Pair_basic"

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
    let val (Bvar,Body) = with_exn dest_pabs tm (PAIR_ERR "PABS_CONV" "")
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
                         else raise (PAIR_ERR "occs_in" "malformed term")
        in check (free_vars p) t
       end
  else raise PAIR_ERR "occs_in" "varstruct expected in first argument";

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

end;
