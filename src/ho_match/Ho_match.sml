(*========================================================================
 *  Higher Order Matching as a derived rule.
 * This code is due to John Harrison's GTT.  The only change is the
 * check to encure bound variables don't match free variables (DRS).
 *
 * Code ported from GTT to hol90 by DRS.
 *=======================================================================*)

structure Ho_match :> Ho_match = 
struct 

open HolKernel Drule Conv liteLib Psyntax;

infixr 3 ##;
infix 5 |-> 
infix THENC
fun WRAP_ERR p = STRUCT_WRAP "Ho_match" p;

type hol_type = Type.hol_type;
type term = Term.term;
type thm = Thm.thm;
type conv = Abbrev.conv;


(* -- Pipefitting -- *)

exception NOT_FOUND
fun rev_assoc_nf x l = 
    liteLib.rev_assoc x l handle HOL_ERR _ => raise NOT_FOUND 


(*-------------------------------------------------------------------------- 
 * match_term [] (--`x:'a`--) (--`x:'a`--);
 * match_term [] (--`I (x:'a)`--) (--`I (y:'a)`--);
 * match_term [] (--`I (x:'a)`--) (--`I (I (y:'a))`--);
 * match_term [] (--`I (x:'a)`--) (--`I (I (x:'a))`--);
 * match_term [] (--`\x:'a. x`--) (--`\y:'b. y`--);
 * match_term [] (--`\x. t`--) (--`\y. y`--);
 * match_term [] (--`!x:'a. t`--) (--`!x:'a. f x`--);
 * match_term [] (--`!x:'a. t`--) (--`!x:'a. f (y:'a)`--);
 * match_term [] (--`(\x. (f:'a->'b) x) y`--) (--`(\x. t1) t2`--);
 * PART_MATCH lhs BETA_THM (--`(\x:'a. (t1:'b)) t2`--);
 * match_term [] (--`\x:'a. (P x:'b)`--) (--`\y. y + 1`--);
 * match_term [] (--`P x`--) (--`\y. y + 1`--);
 * match_term [] (--`!x:'a. P x`--) (--`!x. x + 1 = 2`--);
 * match_term [] (--`!(x:'a) (y:'b). P x y`--) (--`!x y. x + y = 2`--);
 * match_term [] (--`!x. t`--) (--`!x. x + 1 = 2`--);
 * match_term [] (--`!x. t`--) (--`!x. t + 1 = 2`--);
 * match_term [] (--`!x. t`--) (--`!x. x + 1 = 2`--);
 *
 * match_term [] (--` (\x:'a. f x:'b) y`--) (lhs t);
 * PART_MATCH lhs BETA_THM  (lhs t);
 *
 * Lib.try (match_term []) (--`!n. P (SUC n) n`--) (--`!n. f (SUC n) = n`--);
 * match_term [] (--`!c. P ($COND c x y)`--) (--`!g. (g => t | f) ==> r`--);
 * match_term [] (--`P ($COND c x y)`--) (--`(g => t | f) ==> (~g)`--);
 * match_term [] (lhs (concl COND_ELIM_THM)) (--`f (b => t | e) = T`--);
 * match_term [] (--`(f:'a->'b) ($COND b x y)`--) (--`(\x.T) ($COND T F T)`--);
 * match_term [] (--`!opt.  P (option_CASE e (f:'a->'b) opt) opt`--) 
                 (--`!opt. option_CASE T Q opt`--) handle e => Raise e;
 * match_term [] (--`!opt.  P (option_CASE e (f:'a->'b) opt) opt`--) 
                 (--`!opt. g (option_CASE e f opt)`--) handle e => Raise e;
 * match_term [] (--`!opt.  P (option_CASE e (f:'a->'b) opt) opt`--) 
                 (--`!opt. g (option_CASE e f opt)`--) handle e => Raise e;
 * GTT: term_match [] (--`!n. P (SUC n) n`--) (--`!n. f (SUC n) = n`--);;
 * timen (fn () => match_term [] (--`I x`--) (--`I (I y)`--)) 1000;
 * timen (fn () => match_term [] (--`!x. t`--) (--`!x. t + 1 = 2`--)) 1000;
 * timen (fn () => match_term [] (--`!n. P (SUC n) n`--)
 *                               (--`!n. f (SUC n) = n`--)) 1000;
 *
 * ------------------------------------------------------------------------- *)

fun match_term lconsts = let
  fun safe_insert (n as (y,x)) l =
    let val z = rev_assoc_nf x l
    in 
      if (y = z) then l else failwith "match: safe_insert"
    end 
    handle NOT_FOUND => n::l  (* binding not there *)


  fun safe_inserta (n as (y,x)) l =
    let val z = rev_assoc_nf x l
    in if aconv y z then l else failwith "match: safe_inserta"
    end handle NOT_FOUND => n::l

  fun type_match' vty cty sofar =
    if is_vartype vty then
       if vty = cty then sofar else safe_insert (cty,vty) sofar
    else
       let val (vop,vargs) = dest_type vty 
           and (cop,cargs) = dest_type cty
       in if vop = cop then itlist2 type_match' vargs cargs sofar
          else failwith "match: type_match"
       end;

  val mk_dummy =
    let val name = fst(dest_var(genvar(mk_vartype "'a")))
    in fn tm => mk_var(name,type_of tm)
    end;

(*-------------------------------------------------------------------
 * VERSION 1: No "difficult" pattern matching
 * 
 *   exception Itlist2;
 *   fun itlist2 f L1 L2 base_value =
 *    let fun it ([],[]) = base_value
 *          | it ((a::rst1),(b::rst2)) = f a b (it (rst1,rst2))
 *          | it _ = raise Itlist2
 *    in  it (L1,L2)
 *    end;
 *   fun match_term' env vtm ctm sofar =
 *     if is_var vtm then
 *       let val ctm' = rev_assoc vtm env
 *       in if ctm' = ctm then sofar else failwith "match: match_term"
 *       end handle Subscript => (* vtm is a free var *)
 *           if exists (can (fn x => assoc x env)) (free_vars ctm) 
 *      then failwith"match: free vars don't match terms containing bound vars"
 *           else if (vtm = ctm) then sofar 
 * 	  else safe_inserta (ctm,vtm) sofar
 *     else if is_const vtm then
 * 	if name_of_const vtm = name_of_const ctm then
 * 	    safe_inserta (mk_dummy ctm,mk_dummy vtm) sofar
 * 	else failwith "match: match_term"
 *     else if is_abs vtm then
 *       let val (vv,vbod) = dest_abs vtm
 *           and (cv,cbod) = dest_abs ctm
 *           val sofar' = safe_inserta (mk_dummy cv,mk_dummy vv) sofar
 *       in match_term' (insert (cv,vv) env) vbod cbod sofar' 
 *       end
 *     else
 *       let val (vhop,vargs) = strip_comb vtm
 *           and (chop,cargs) = strip_comb ctm
 *       in (if not (is_var vhop) orelse can (C rev_assoc env) vhop then fail()
 *           else
 *            let val vargs' = map (C rev_assoc env) vargs
 *            in if vargs' = cargs then safe_inserta (chop,vhop) sofar
 *              else safe_inserta (list_mk_abs(vargs',ctm),vhop) sofar
 *            end)
 *          handle HOL_ERR _ =>  
 *           (itlist2 (match_term' env) vargs cargs 
 *                          (match_term' env vhop chop sofar)
 *            handle Itlist2 => 
 *              let val (lv,rv) = dest_comb vtm
 *                  and (lc,rc) = dest_comb ctm
 *                  val insts1 = match_term' env lv lc sofar
 *              in match_term' env rv rc insts1
 *              end)
 *        end
 * 
 * in
 *    fn vtm => fn ctm =>
 *      let val rawins = match_term' [] vtm ctm []
 *        val (cins,vins) = unzip rawins
 *      val tyins = itlist2 type_match' (map type_of vins)(map type_of cins) []
 * 	 fun mk_subst (x,y) = (y |-> x)
 * 	 val tysubst = map mk_subst tyins
 *          val vins' = map (inst tysubst) vins
 *          val tmins = filter (fn (x,y) =>  not (x = y)) (zip cins vins')
 *      in (map mk_subst tmins,tysubst)
 *      end
 *      handle e => WRAP_ERR("match_term",e)
 * 
 *------------------------------------------------------------------------*)


 (*----------------------------------------------------------------------
 * VERSION 2 Complex pattern matching
 * 
 *   fun term_pmatch env vtm ctm (sofar as (insts,homs)) =
 *     if is_var vtm then
 * 	let val ctm' = rev_assoc vtm env 
 * 	in if ctm' = ctm then sofar else failwith "term_pmatch"
 * 	end handle Subscript =>
 * 	    if mem vtm lconsts then
 * 		if ctm = vtm then sofar
 * 		else failwith "term_pmatch: can't instantiate local constant"
 * 	    else (safe_inserta (ctm,vtm) insts,homs)
 *     else if is_const vtm then
 *       let val (vname,vty) = dest_const vtm
 * 	  and (cname,cty) = dest_const ctm 
 *       in if vname = cname then
 * 	  if vty = cty then sofar
 * 	  else (safe_inserta (mk_dummy ctm,mk_dummy vtm) insts,homs)
 * 	 else failwith "term_pmatch"
 *       end
 *     else if is_abs vtm then
 *       let val (vv,vbod) = dest_abs vtm
 * 	  and (cv,cbod) = dest_abs ctm
 * 	  val sofar' = (safe_inserta (mk_dummy cv,mk_dummy vv) insts,homs)
 *       in term_pmatch (insert (cv,vv) env) vbod cbod sofar' 
 *       end
 *     else
 *     let val vhop = repeat rator vtm 
 *     in if is_var vhop andalso not (mem vhop lconsts) andalso
 * 	not (can (rev_assoc vhop) env) then
 * 	(insts,(env,ctm,vtm)::homs)
 *        else
 * 	    let val (lv,rv) = dest_comb vtm
 * 		and (lc,rc) = dest_comb ctm
 * 		val sofar1 = term_pmatch env lv lc sofar 
 * 	    in term_pmatch env rv rc sofar1 
 * 	    end
 *     end;
 * 
 *   fun get_type_insts insts =
 *     map (fn (x,y) => y |-> x) 
 *     (itlist (fn (t,x) => type_match' (type_of x) (type_of t)) insts []);
 * 
 *   fun separate_insts insts =
 *       let val tyins = get_type_insts insts 
 * 	  val inst_fn = inst tyins
 *       in (mapfilter (fn (t,x) => 
 * 		    let val x' = inst_fn x 
 * 		    in if t = x' then fail() else (t,x')
 * 		    end) insts,tyins) 
 *       end;
 * 
 *   fun term_matches (insts,homs) =
 *     if homs = [] then insts else
 *     let val (env,ctm,vtm) = hd homs 
 * 	val (vhop,vargs) = strip_comb vtm 
 *     in if vargs = [] then
 *       let val newinsts =
 *         if vtm = ctm then insts else safe_inserta (ctm,vtm) insts 
 *       in term_matches (newinsts,tl homs) 
 *       end else
 *     let val afvs = free_varsl vargs 
 *     in let val xfvs = map
 *           (fn a => (rev_assoc a env
 *                     handle Subscript => rev_assoc a insts
 * 			handle Subscript => fail(), a)) afvs 
 *         val tyins = get_type_insts insts 
 *         val inst_fn = inst tyins
 *         val pats0 = map inst_fn vargs
 *         val tmins = map (fn (x,a) => inst_fn a |-> x) xfvs
 *         val pats = map (subst tmins) pats0
 *         val ictm = list_mk_comb(inst_fn vhop,pats)
 *         val ni =
 * 	    let val (chop,cargs) = strip_comb ctm
 * 	    in if cargs = pats then
 * 		if chop = vhop then insts 
 * 		else safe_inserta (chop,vhop) insts 
 * 	       else
 * 		let val ginsts = map (fn p => p |-> (if is_var p then p 
 * 					       else genvar(type_of p))) pats
 *                 val abstm = list_mk_abs(map residue ginsts,subst ginsts ctm)
 * 		in if abstm = vhop then insts 
 * 		   else safe_inserta (abstm,vhop) insts
 * 		end
 * 	    end
 *        in term_matches (ni,tl homs)
 *        end
 *     handle HOL_ERR _ =>
 * 	let val (lc,rc) = dest_comb ctm
 * 	    and (lv,rv) = dest_comb vtm
 * 	in term_matches
 * 	    (term_pmatch env rv rc (insts,(env,lc,lv)::(tl homs)))
 * 	end
 *     end
 *     end;
 * 
 * in fn vtm => fn ctm =>
 *     let val (pinsts,homs) = term_pmatch [] vtm ctm ([],[]) 
 * 	val insts = term_matches (pinsts,homs)
 *     in (map (fn (x,y) => y |-> x) ## I) (separate_insts insts)
 *     end
 * 
 *------------------------------------------------------------------------*)

(* This is version 1 *)

  exception Itlist2;
  fun itlist2 f L1 L2 base_value =
   let fun it ([],[]) = base_value
         | it ((a::rst1),(b::rst2)) = f a b (it (rst1,rst2))
         | it _ = raise Itlist2
   in  it (L1,L2)
   end;

  fun match_term' env vtm ctm sofar =
   if is_var vtm 
   then let val ctm' = rev_assoc_nf vtm env
        in 
          if ctm' = ctm then sofar else failwith "match: match_term"
        end 
        handle NOT_FOUND  (* vtm is a free var *)
        => if mem vtm lconsts 
           then if ctm = vtm then sofar
	        else failwith "match_term': can't instantiate local constant"
           else if exists (can (fn x => assoc x env)) (free_vars ctm)
               then failwith"match: free vars don't match terms with bound vars"
           else if (vtm = ctm) then sofar 
           else safe_inserta (ctm,vtm) sofar 
   else 
   if is_const vtm 
   then if name_of_const vtm = name_of_const ctm 
        then safe_inserta (mk_dummy ctm,mk_dummy vtm) sofar
	else failwith "match: match_term" 
   else 
   if is_abs vtm 
   then let val (vv,vbod) = dest_abs vtm
            and (cv,cbod) = dest_abs ctm
            val sofar' = safe_inserta (mk_dummy cv,mk_dummy vv) sofar
        in 
          match_term' (insert (cv,vv) env) vbod cbod sofar' 
        end
   else (* is_comb *)
   let val (vhop,vargs) = strip_comb vtm
       and (chop,cargs) = strip_comb ctm
   in (if not (is_var vhop) orelse  mem vhop lconsts 
          orelse can (C rev_assoc env) vhop 
       then fail()
       else let val vargs' = map (C rev_assoc env) vargs
            in 
              if vargs' = cargs 
              then safe_inserta (chop,vhop) sofar
              else safe_inserta (list_mk_abs(vargs',ctm),vhop) sofar
           end)
         handle HOL_ERR _ =>  
          (itlist2 (match_term' env) vargs cargs 
                         (match_term' env vhop chop sofar)
           handle Itlist2 => 
             let val (lv,rv) = dest_comb vtm
                 and (lc,rc) = dest_comb ctm
                 val insts1 = match_term' env lv lc sofar
             in match_term' env rv rc insts1
             end)
       end

in fn vtm => fn ctm =>
 let val rawins = match_term' [] vtm ctm []
     val (cins,vins) = unzip rawins
     val tyins = itlist2 type_match' (map type_of vins) (map type_of cins) []
     val vins' = map (inst tyins) vins
     val tmins = filter (fn (x,y) =>  not (x = y)) (zip cins vins')
 in (tmins,tyins)
 end
 handle (e as HOL_ERR _) => WRAP_ERR("match_term",e)

end;


(* ------------------------------------------------------------------------- 
 * Set up beta-conversion for head instances of free variable v in tm.       
 * ------------------------------------------------------------------------- *)

fun COMB_CONV2 lconv rconv tm =
    let val (l,r) = dest_comb tm 
    in MK_COMB(lconv l,rconv r)
    end;

(* ------------------------------------------------------------------------- *)
(* Attempt alpha conversion.                                                 *)
(* ------------------------------------------------------------------------- *)

fun tryalpha v tm =
  alpha v tm 
  handle HOL_ERR _ => alpha (variant (free_vars tm) v) tm
  handle HOL_ERR _ => tm;

(* ------------------------------------------------------------------------- *)
(* Match up bound variables names.                                           *)
(* ------------------------------------------------------------------------- *)

fun match_bvs t1 t2 acc =
 let val (v1,b1) = dest_abs t1
     and (v2,b2) = dest_abs t2
     val n1 = fst(dest_var v1) and n2 = fst(dest_var v2)
     val newacc = if n1 = n2 then acc else insert (n1,n2) acc
 in
     match_bvs b1 b2 newacc
 end
 handle HOL_ERR _ =>
 let val (l1,r1) = dest_comb t1
     and (l2,r2) = dest_comb t2
 in 
     match_bvs l1 l2 (match_bvs r1 r2 acc)
 end
 handle HOL_ERR _ => acc;

(* ------------------------------------------------------------------------- *)
(* Modify bound variable names at depth. (Not very efficient...)             *)
(* ------------------------------------------------------------------------- *)

fun deep_alpha env tm =
  if env = [] then tm else
  let val (v,bod) = dest_abs tm
      val (vn,vty) = dest_var v
  in let val ((vn',_),newenv) = Lib.pluck (fn (_,x) => x = vn) env 
         val pp = (vn',vn)
         val v' = mk_var(vn',vty)
         val tm' = tryalpha v' tm
         val (iv,ib) = dest_abs tm' 
     in
	 mk_abs(iv,deep_alpha newenv ib)
     end
     handle HOL_ERR _ => mk_abs(v,deep_alpha env bod)
  end
  handle HOL_ERR _ =>
    let val (l,r) = dest_comb tm 
    in  mk_comb(deep_alpha env l, deep_alpha env r)
    end
  handle HOL_ERR _ => tm;;

(* ------------------------------------------------------------------------- 
 * BETA_VAR
 *
 * Set up beta-conversion for head instances of free variable v in tm.       
 *
 * EXAMPLES
 *
 *   BETA_VAR (--`x:num`--) (--`(P:num->num->bool) x x`--);
 *   BETA_VAR (--`x:num`--) (--`x + 1`--);
 * ------------------------------------------------------------------------- *)

val BETA_VAR = let 
  fun BETA_CONVS n =
    if n = 1 then TRY_CONV BETA_CONV else
    RATOR_CONV (BETA_CONVS (n - 1)) THENC TRY_CONV BETA_CONV
  fun free_beta v tm =
    if is_abs tm then
      let val (bv,bod) = dest_abs tm
      in if v = bv then failwith "BETA_VAR: UNCHANGED"
         else ABS_CONV(free_beta v bod)
      end
    else 
      let val (oper,args) = strip_comb tm
      in if (args = []) then failwith "BETA_VAR: UNCHANGED"
         else if oper = v then BETA_CONVS (length args)
         else let val (l,r) = dest_comb tm
              in let val lconv = free_beta v l
                 in let val rconv = free_beta v r
                    in COMB_CONV2 lconv rconv
                    end handle HOL_ERR _ => RATOR_CONV lconv
                 end handle HOL_ERR _ => RAND_CONV (free_beta v r)
              end
      end
  in free_beta end;;

(* ------------------------------------------------------------------------- 
 * Match (higher-order) part of a theorem to a term.                         
 *
 * PART_MATCH (snd o strip_forall) BOOL_CASES_AX (--`(P = T) \/ (P = F)`--);
 * val NOT_FORALL_THM = mk_thm([],(--`~(!x:'a. P x) = (?x. ~P x)`--));
 * val NOT_EXISTS_THM = mk_thm([],(--`(?x. ~P x) = ~(!x:'a. P x)`--));
 * val LEFT_AND_EXISTS_THM = mk_thm([],(--`((?x:'a. P x) /\ Q) = (?x. P x /\ Q)`--));
 * val f = PART_MATCH lhs;
 * profile2 f NOT_FORALL_THM (--`~!x. (P:num->num->bool) x y`--);
 * profile2 f NOT_EXISTS_THM (--`?x. ~(P:num->num->bool) x y`--);
 * profile2 f LEFT_AND_EXISTS_THM (--`(?x. (P:num->num->bool) x x) /\ Q (y:num)`--);
 * profile LEFT_AND_EXISTS_CONV (--`(?x. (P:num->num->bool) x x) /\ Q (x:num)`--);
 * profile2 f NOT_FORALL_THM (--`~!x. (P:num->num->bool) y x`--);
 * profile NOT_FORALL_CONV (--`~!x. (P:num->num->bool) y x`--);
 * val f = PART_MATCH (lhs o snd o strip_imp);
 * val CRW_THM = mk_thm([],(--`P x ==> Q x (y:num) ==> (x + 0 = x)`--));
 * f CRW_THM (--`y + 0`--);
 *
 * val beta_thm = prove(--`(\x:'a. P x) b = (P b:'b)`--)--, BETA_TAC THEN REFL_TAC);
 * val f = profile PART_MATCH lhs beta_thm;
 * profile f (--`(\x. I x) 1`--);
 * profile f (--`(\x. x) 1`--);
 * profile f (--`(\x. P x x:num) 1`--);
 *
 * The current version attempts to keep variable names constant.  This
 * is courtesy of JRH.
 *
 * Non renaming version (also courtesy of JRH!!)
 *
 * fun PART_MATCH partfn th =
 *   let val sth = SPEC_ALL th
 *       val bod = concl sth
 *       val possbetas = mapfilter (fn v => (v,BETA_VAR v bod)) (free_vars bod)
 *       fun finish_fn tyin bvs =
 *         let val npossbetas = map (inst tyin ## I) possbetas
 *         in CONV_RULE (EVERY_CONV (mapfilter (C assoc npossbetas) bvs))
 *         end
 *       val pbod = partfn bod
 *   in fn tm =>
 *     let val (tmin,tyin) = match_term pbod tm
 *         val th0 = INST tmin (INST_TYPE tyin sth)
 *     in finish_fn tyin (map #redex tmin) th0
 *     end
 *   end;
 * 
 * EXAMPLES:
 *
 * val CET = mk_thm([],(--`(!c. P ($COND c x y) c) = (P x T /\ P y F)`--));

 * PART_MATCH lhs FORALL_SIMP (--`!x. y + 1 = 2`--);
 * PART_MATCH lhs FORALL_SIMP (--`!x. x + 1 = 2`--); (* fails *)
 * PART_MATCH lhs CET (--`!b. ~(f (b => t | e))`--);
 * PART_MATCH lhs option_CASE_ELIM (--`!b. ~(P (option_CASE e f b))`--);
 * PART_MATCH lhs (MK_FORALL (--`c:bool`--) COND_ELIM_THM) (--`!b. ~(f (b => t | e))`--);
 * PART_MATCH lhs (MK_FORALL (--`c:bool`--) COND_ELIM_THM) (--`!b. ~(f (b => t | e))`--);
term_match [] (--`!c.  P ($COND c x y)`--) 
 * BUG FIXES & TEST CASES
 *
 * Variable Renaming:
 * PART_MATCH (lhs o snd o strip_forall) SKOLEM_THM (--`!p. ?GI. Q GI p`--);
 * Before renaming this produced: |- (!x. ?y. Q y x) = (?y. !x. Q (y x) x)
 * After renaming this produced: |- (!p. ?GI. Q GI p) = (?GI. !p. Q (GI p) p)
 *
 * Variable renaming problem (DRS, Feb 1996):  
 * PART_MATCH lhs NOT_FORALL_THM (--`~!y. P x`--);
 * Before fix produced:  |- ~(!x'. P x) = (?x'. ~(P x)) : thm
 * After fix produced:  |- ~(!y. P x) = (?y. ~(P x))
 * Fix:
 *	val bvms = match_bvs tm (inst tyin pbod) []
 * Became:
 *      val bvms = match_bvs tm (partfn (concl th0)) []
 *
 * Variable renaming problem (DRS, Feb 1996):
 * PART_MATCH lhs NOT_FORALL_THM (--`~!x. (\y. t) T`--);
 * Before fix produced (--`?y. ~(\y. t) T`--);
 * After fix produced (--`?x. ~(\y. t) T`--);
 * Fix: 
 *      Moved beta reduction to be before alpha renaming.  This makes
 * match_bvs more accurate.  This was not a problem before the previous
 * fix.
 *
 * Another bug (unfixed).  bvms =  [("x","y"),("E'","x")]
 *   PART_MATCH lhs SWAP_EXISTS_THM  (--`?E' x const'.
        ((s = s') /\
         (E = E') /\
         (val = Val_Constr (const',x)) /\
         (sym = const)) /\
        (a1 = NONE) /\
        ~(const = const')`--)
 * ------------------------------------------------------------------------- *)


fun PART_MATCH partfn th =
  let val sth = SPEC_ALL th
      val bod = concl sth
      val pbod = partfn bod 
      val possbetas = mapfilter (fn v => (v,BETA_VAR v bod)) (free_vars bod)
      fun finish_fn tyin ivs =
         let val npossbetas =
           if tyin = [] then possbetas else map (inst tyin ## I) possbetas 
         in
	     if null npossbetas then (fn th => th)
	     else CONV_RULE (EVERY_CONV (mapfilter (C assoc npossbetas) ivs))
	 end
      val lconsts = intersect (free_vars (concl th)) (free_varsl(hyp th)) 
  in  fn tm =>
    let val (tmin,tyin) = match_term lconsts pbod tm
	val th0 = INST tmin (INST_TYPE tyin sth)
	val th1 = finish_fn tyin (map redex tmin) th0
	val bvms = match_bvs tm (partfn (concl th1)) []
    in 
	if bvms = [] then th1
	else let val tm0 = concl th1
		 val tm1 = deep_alpha bvms tm0
	     in  EQ_MP (ALPHA tm0 tm1) th1
	     end
    end
  end;

end (* struct *)
