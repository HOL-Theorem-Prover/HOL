(*---------------------------------------------------------------------------*
 * Syntax support for the theory of pairs. When possible, functions          *
 * below deal with both paired and unpaired input.                           *
 *---------------------------------------------------------------------------*)

structure pairSyntax :> pairSyntax =
struct

open HolKernel Drule Conv boolTheory pairTheory boolSyntax Abbrev;

infix |-> THENC ORELSEC ##;
infixr -->;

val ERR = mk_HOL_ERR "pairSyntax";

(*---------------------------------------------------------------------------
             Operations on product types
 ---------------------------------------------------------------------------*)

fun mk_prod (ty1,ty2) = Type.mk_thy_type{Tyop="prod",Thy="pair",Args=[ty1,ty2]}
val list_mk_prod = end_itlist (curry mk_prod);

fun dest_prod ty = 
  case total dest_thy_type ty
   of SOME{Tyop="prod", Thy="pair", Args=[ty1,ty2]} => (ty1,ty2)
    | other => raise ERR "dest_prod" "not a product type";

fun strip_prod_list [] A = rev A
  | strip_prod_list (h::t) A = 
       case total dest_prod h
        of SOME(ty1,ty2) => strip_prod_list (ty1::ty2::t) A
         | NONE => strip_prod_list t (h::A)

fun strip_prod ty = strip_prod_list [ty] [];


(*---------------------------------------------------------------------------
         Useful constants in the theory of pairs
 ---------------------------------------------------------------------------*)

val comma    = prim_mk_const {Name=",",       Thy="pair"};
val Fst      = prim_mk_const {Name="FST",     Thy="pair"};
val Snd      = prim_mk_const {Name="SND",     Thy="pair"};
val Uncurry  = prim_mk_const {Name="UNCURRY", Thy="pair"};
val Curry    = prim_mk_const {Name="CURRY",   Thy="pair"};
val pair_fun = prim_mk_const {Name="##",      Thy="pair"};


(*---------------------------------------------------------------------------
      Make a pair from two components, or a tuple from a list of components
 ---------------------------------------------------------------------------*)

fun mk_pair(fst,snd) =
 let val ty1 = type_of fst
     and ty2 = type_of snd
 in list_mk_comb(inst [alpha |-> ty1, beta |-> ty2] comma, [fst,snd])
 end;

val list_mk_pair = end_itlist (curry mk_pair);

(*---------------------------------------------------------------------------
      Take a pair apart. Take a list of tuples apart. The atoms 
      appear in left-to-right order.
 ---------------------------------------------------------------------------*)

val dest_pair = dest_binop (",","pair") (ERR "dest_pair" "not a pair")


fun strip_pairs [] A = rev A
  | strip_pairs (h::t) A =
     case total dest_pair h
      of SOME (fst,snd) => strip_pairs (fst::snd::t) A
       | NONE => strip_pairs t (h::A)

fun strip_pair tm = strip_pairs [tm] [];

(*---------------------------------------------------------------------------
       Is it a pair?
 ---------------------------------------------------------------------------*)

val is_pair = can dest_pair;


(*---------------------------------------------------------------------------
      Making applications of FST and SND
 ---------------------------------------------------------------------------*)

fun mk_fst tm =
  let val (ty1,ty2) = dest_prod (type_of tm)
  in mk_comb(inst[alpha |-> ty1, beta |-> ty2] Fst, tm)
  end
  handle HOL_ERR _ => raise ERR "mk_fst" "";

fun mk_snd tm =
  let val (ty1,ty2) = dest_prod (type_of tm)
  in mk_comb(inst[alpha |-> ty1, beta |-> ty2] Snd,tm)
  end
  handle HOL_ERR _ => raise ERR "mk_snd" "";


(*---------------------------------------------------------------------------*)
(* Constructor, destructor and discriminator functions for paired            *)
(* abstractions and ordinary abstractions.                                   *)
(* [JRH 91.07.17]                                                            *)
(* Intentionally named so as to replace the existing operations on binders.  *)
(*---------------------------------------------------------------------------*)

fun mk_uncurry(xt,yt,zt) = 
  inst [alpha |-> xt, beta |-> yt, gamma |-> zt] Uncurry;

fun isUncurry c = 
 case total dest_thy_const c
  of SOME{Name="UNCURRY",Thy="pair",...} => true
   | otherwise => false;

val is_uncurry = isUncurry o rator;

fun mk_abs(vstruct,body) =
  if is_var vstruct then Term.mk_abs(vstruct, body)
  else let val (fst,snd) = dest_pair vstruct
           val cab = mk_abs(fst,mk_abs(snd,body))
           val unc = mk_uncurry(type_of fst,type_of snd,type_of body)
       in mk_comb(unc, cab)
       end 
       handle HOL_ERR _ => raise ERR "mk_abs" "";

fun mk_forall(vstruct,body) =
 mk_comb(inst [alpha |-> type_of vstruct] universal, mk_abs(vstruct,body))
 handle HOL_ERR _ => raise ERR "mk_forall" "";

fun mk_exists(vstruct,body) =
 mk_comb(inst [alpha |-> type_of vstruct] existential,mk_abs(vstruct,body))
 handle HOL_ERR _ => raise ERR "mk_exists" "";

fun mk_exists1(vstruct,body) =
 mk_comb(inst [alpha |-> type_of vstruct] exists1, mk_abs(vstruct,body))
 handle HOL_ERR _ => raise ERR "mk_exists1" "";

fun mk_select(vstruct,body) =
 mk_comb(inst [alpha |-> type_of vstruct] select,mk_abs(vstruct,body))
 handle HOL_ERR _ => raise ERR "mk_select" "";


fun dest_abs tm =
 Term.dest_abs tm
 handle HOL_ERR _
  => let val (Rator,Rand) = with_exn dest_comb tm (ERR "dest_abs" "")
     in if isUncurry Rator
        then let val (lv, body) = dest_abs Rand
                 val (rv, body) = dest_abs body
             in (mk_pair(lv, rv), body)
             end
        else raise ERR "dest_abs" ""
     end;

fun bvar tm = fst (dest_abs tm) handle HOL_ERR _ => failwith "bvar"
and body tm = snd (dest_abs tm) handle HOL_ERR _ => failwith "body" ;


local val FORALL_ERR  = ERR "dest_forall"  "not a (possibly paired) \"!\""
      val EXISTS_ERR  = ERR "dest_exists"  "not a (possibly paired) \"?\""
      val EXISTS1_ERR = ERR "dest_exists1" "not a (possibly paired) \"?!\""
      val SELECT_ERR  = ERR "dest_select"  "not a (possibly paired) \"@\""
in 
fun dest_paired_binder c e M =
  let val (Rator,Rand) = with_exn dest_comb M e
  in if can (match_term c) Rator then dest_abs Rand else raise e
  end

val dest_forall  = dest_paired_binder universal   FORALL_ERR
val dest_exists  = dest_paired_binder existential EXISTS_ERR
val dest_exists1 = dest_paired_binder exists1     EXISTS1_ERR
val dest_select  = dest_paired_binder select      SELECT_ERR
end;

val is_abs     = can dest_abs;
val is_forall  = can dest_forall;
val is_exists  = can dest_exists;
val is_exists1 = can dest_exists1;
val is_select  = can dest_select;

fun list_mk_abs(V,M)    = itlist (curry mk_abs) V M;
fun list_mk_forall(V,M) = itlist (curry mk_forall) V M;
fun list_mk_exists(V,M) = itlist (curry mk_exists) V M;

fun strip dest =
 let fun decomp M =
       case dest M
       of NONE => ([],M)
        | SOME(vstruct,body) => 
           let val (V,kern) = strip dest body 
           in (vstruct::V,kern) 
           end
 in decomp
 end;

val strip_abs    = strip (total dest_abs)
val strip_forall = strip (total dest_forall)
val strip_exists = strip (total dest_exists);


(*---------------------------------------------------------------------------
     A "vstruct" is a tuple of variables, with no duplicate occurrences.
     Later in this file, we lift definition principles so that they 
     allow varstructs on the left-hand-sides of definitions.
 ---------------------------------------------------------------------------*)

local fun check [] = true
        | check (h::t) = is_var h andalso not(mem h t) andalso check t
in
fun is_vstruct M = check (strip_pair M)
end;

(* ===================================================================== *)
(* Generates a pair structure of variable with the same structure as     *)
(* its parameter.                                                        *)
(* ===================================================================== *)

fun genvstruct ty =
  case total dest_prod ty
   of SOME(ty1,ty2) => mk_pair(genvstruct ty1, genvstruct ty2)
    | NONE => genvar ty;


(*---------------------------------------------------------------------------
    Raising basic lambda calculus conversions to handle pairs
 ---------------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* PAIRED_BETA_CONV: Generalized beta conversions for tupled lambda	*)
(*		    abstractions applied to tuples (i.e. redexes)	*)
(*									*)
(* Given the term:                                    			*)
(*                                                                      *)
(*   "(\(x1, ... ,xn).t) (t1, ... ,tn)"                                	*)
(*                                                                      *)
(* PAIRED_BETA_CONV proves that:					*)
(*                                                                      *)
(*   |- (\(x1, ... ,xn).t) (t1, ... ,tn) = t[t1, ... ,tn/x1, ... ,xn]   *)
(*                                                                      *)
(* where t[t1,...,tn/x1,...,xn] is the result of substituting ti for xi	*)
(* in parallel in t, with suitable renaming of variables to prevent	*)
(* free variables in t1,...,tn becoming bound in the result.     	*)
(*                                                                      *)
(* The conversion works for arbitrarily nested tuples.  For example:	*)
(*									*)
(*   PAIRED_BETA_CONV "(\((a,b),(c,d)).t) ((1,2),(3,4))"		*)
(*									*)
(* gives:								*)
(*									*)
(*  |- (\((a,b),(c,d)).t) ((1,2),(3,4)) = t[1,2,3,4/a,b,c,d]     	*)
(*									*)
(* Bugfix: INST used instead of SPEC to avoid priming.    [TFM 91.04.17]*)
(* ---------------------------------------------------------------------*)

local val vs = map genvar [alpha --> beta --> gamma, alpha, beta]
      val DEF = SPECL vs pairTheory.UNCURRY_DEF
      val RBCONV = RATOR_CONV BETA_CONV THENC BETA_CONV
      fun conv tm = 
       let val (Rator,Rand) = dest_comb tm
           val (fst,snd) = dest_pair Rand
           val (Rator,f) = dest_comb Rator
           val _ = assert isUncurry Rator
           val (t1,ty') = dom_rng (type_of f)
           val (t2,t3) = dom_rng ty'
           val iDEF = INST_TYPE [alpha |-> t1, beta |-> t2, gamma |-> t3] DEF
           val (fv,[xv,yv]) = strip_comb(rand(concl iDEF))
           val def = INST [yv |-> snd, xv |-> fst, fv |-> f] iDEF
       in
         TRANS def 
          (if Term.is_abs f 
           then if Term.is_abs (body f) 
                then RBCONV (rhs(concl def))
                else CONV_RULE (RAND_CONV conv)
                      (AP_THM(BETA_CONV(mk_comb(f, fst))) snd)
           else let val recc = conv (rator(rand(concl def)))
                in if Term.is_abs (rhs(concl recc))
                   then RIGHT_BETA (AP_THM recc snd)
                   else TRANS (AP_THM recc snd) 
                           (conv(mk_comb(rhs(concl recc), snd)))
                end)
       end
in
fun PAIRED_BETA_CONV tm 
    = conv tm handle HOL_ERR _ => raise ERR "PAIRED_BETA_CONV" ""
end;


(*---------------------------------------------------------------------------
     Lifting primitive definition principle to understand varstruct
     arguments in definitions.
 ---------------------------------------------------------------------------*)

fun inter s1 [] = []
  | inter s1 (h::t) = case intersect s1 h of [] => inter s1 t | X => X

fun joint_vars []  = []
  | joint_vars [_] = []
  | joint_vars (h::t) = case inter h t of [] => joint_vars t | X => X;

fun dest t = 
  let val (lhs,rhs) = dest_eq (snd(strip_forall t))
      val (f,args) = strip_comb lhs
  in 
  case gather (not o is_vstruct) args 
   of [] => (case joint_vars (map free_vars args)
              of [] => (args, mk_eq(f,list_mk_abs(args,rhs)))
               | V  => raise ERR "new_definition" (String.concat
                       ("shared variables between arguments: " ::
                        commafy (map Parse.term_to_string V))))
    | tml => raise ERR "new_definition" (String.concat
             ("The following arguments are not varstructs: "::
              commafy (map Parse.term_to_string tml)))
  end;

fun RHS_CONV conv th = TRANS th (conv(rhs(concl th)));
fun add_varstruct v th = 
  RHS_CONV (BETA_CONV ORELSEC PAIRED_BETA_CONV) (AP_THM th v)

fun post (V,th) =
  let val cname = fst(dest_const(lhs(concl th)))
      val vars = List.concat (map free_vars_lr V)
  in Parse.add_const cname;
     itlist GEN vars (rev_itlist add_varstruct V th)
  end;
  
val _ = Definition.new_definition_hook := (dest, post)


(*-------------------------------------------------------*)
(* PAIRED_ETA_CONV "\(x1,.(..).,xn). P (x1,.(..).,xn)" = *)
(*       |- \(x1,.(..).,xn). P (x1,.(..).,xn) = P        *)
(* [JRH 91.07.17]                                        *)
(*-------------------------------------------------------*)

local val pthm = GEN_ALL (SYM (SPEC_ALL pairTheory.PAIR))
      fun pairify tm =
        let val step = ISPEC tm pthm
            val (Rator,r) = dest_comb (rhs (concl step))
            val (pop,l) = dest_comb Rator
        in
          TRANS step (MK_COMB(AP_TERM pop (pairify l), pairify r))
        end
        handle HOL_ERR _ => REFL tm
in
fun PAIRED_ETA_CONV tm =
   let val (varstruct,body) = dest_abs tm
       val (f,Rand) = dest_comb body
       val _ = assert (equal varstruct) Rand
       val xv = mk_var("x", type_of varstruct)
       val peq = pairify xv
       val par = rhs (concl peq)
       val bth = PAIRED_BETA_CONV (mk_comb(tm, par))
   in
     EXT (GEN xv (SUBS [SYM peq] bth))
   end
   handle HOL_ERR _ => raise ERR "PAIRED_ETA_CONV" ""
end;

(*--------------------------------------------------------------------*)
(* GEN_BETA_CONV - reduces single or paired abstractions, introducing *)
(* arbitrarily nested "FST" and "SND" if the rand is not sufficiently *)
(* paired. Example:                                                   *)
(*                                                                    *)
(*   #GEN_BETA_CONV "(\(x,y). x + y) numpair";                        *)
(*   |- (\(x,y). x + y)numpair = (FST numpair) + (SND numpair)        *)
(* [JRH 91.07.17]                                                     *)
(*--------------------------------------------------------------------*)

local val pair = CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) pairTheory.PAIR
    val uncth = SPEC_ALL pairTheory.UNCURRY_DEF
    fun gbc tm =
     let val (abst,arg) = dest_comb tm
     in if Term.is_abs abst 
        then BETA_CONV tm 
        else let val _ = assert is_uncurry abst
               val eqv = if is_pair arg then REFL arg else ISPEC arg pair
               val _ = dest_pair (rhs (concl eqv))
               val res = AP_TERM abst eqv
               val rt0 = TRANS res (PART_MATCH lhs uncth (rhs (concl res)))
               val (tm1a,tm1b) = dest_comb (rhs (concl rt0))
               val rt1 = AP_THM (gbc tm1a) tm1b
               val tm2 = rhs (concl rt1) 
               val rt2 = gbc tm2
             in
                TRANS rt0 (TRANS rt1 rt2) 
             end
     end
in
fun GEN_BETA_CONV tm = gbc tm handle HOL_ERR _ => raise ERR "GEN_BETA_CONV" ""
end;

local open Tactic Conv 
in
val GEN_BETA_RULE = CONV_RULE (DEPTH_CONV GEN_BETA_CONV)
val GEN_BETA_TAC  = CONV_TAC (DEPTH_CONV GEN_BETA_CONV)
end;


(*---------------------------------------------------------------------------
        Let reduction
 ---------------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* Internal function: ITER_BETA_CONV (iterated, tupled beta-conversion).*)
(*									*)
(* The conversion ITER_BETA_CONV reduces terms of the form:		*)
(*									*)
(*     (\v1 v2...vn.tm) x1 x2 ... xn xn+1 ... xn+i			*)
(*									*)
(* where the v's can be varstructs. The behaviour is similar to		*)
(* LIST_BETA_CONV, but this function also does paired abstractions.	*)
(* ---------------------------------------------------------------------*)

fun ITER_BETA_CONV tm = 
  let val (Rator,Rand) = dest_comb tm 
      val thm = AP_THM (ITER_BETA_CONV Rator) Rand
      val redex = rand(concl thm)
      val red = TRY_CONV(BETA_CONV ORELSEC PAIRED_BETA_CONV) redex
  in
    TRANS thm red
  end
  handle HOL_ERR _ => REFL tm;


(* ---------------------------------------------------------------------*)
(* Internal function: ARGS_CONV (apply a list of conversions to the 	*)
(* arguments of a curried function application).			*)
(*									*)
(* ARGS_CONV [conv1;...;convn] "f a1 ... an" applies convi to ai.	*)
(* ---------------------------------------------------------------------*)

local fun appl [] [] = []
        | appl (f::frst) (a::arest) = f a::appl frst arest
        | appl _ _ = raise ERR "ARGS_CONV" "appl"
in
fun ARGS_CONV cs tm =
  let val (f,ths) = (I ## appl cs) (strip_comb tm)
  in rev_itlist (C (curry MK_COMB)) ths (REFL f) 
  end
end;

(* ---------------------------------------------------------------------*)
(* Internal function RED_WHERE.						*)
(*									*)
(* Given the arguments "f" and "tm[f]", this function produces a 	*)
(* conversion that will apply ITER_BETA_CONV to its argument at all	*)
(* subterms that correspond to occurrences of f (bottom-up).		*)
(* ---------------------------------------------------------------------*)

fun RED_WHERE fnn body = 
 if is_var body orelse is_const body then REFL 
 else let val (_,Body) = Term.dest_abs body 
      in ABS_CONV (RED_WHERE fnn Body)
      end
   handle HOL_ERR _ => 
    let val (f,args) = strip_comb body 
    in if f=fnn
       then ARGS_CONV (map (RED_WHERE fnn) args) THENC ITER_BETA_CONV
       else let val (Rator,Rand) = dest_comb body 
            in RAND_CONV(RED_WHERE fnn Rand)
                  THENC 
               RATOR_CONV (RED_WHERE fnn Rator)
            end
    end;

(* ---------------------------------------------------------------------*)
(* Internal function: REDUCE						*)
(* 									*)
(* This function does the appropriate beta-reductions in the result of	*)
(* expanding a let-term.  For terms of the form:			*)
(*									*)
(*      "let f x1 ... xn = t in tm[f]"					*)
(*									*)
(* we have that:							*)
(*									*)
(*      th |- <let term> = tm[\x1 ... xn. t/f]				*)
(*									*)
(* And the arguments x and f will be:					*)
(*									*)
(*       x = \x1 ... xn. t						*)
(*       f = \f. tm[f]							*)
(*									*)
(* REDUCE searches in tm[f] for places in which f occurs, and then does	*)
(* an iterated beta-reduction (possibly of varstruct-abstractions) in	*)
(* the right-hand side of the input theorem th, at the places that	*)
(* correspond to occurrences of f in tm[f].				*)
(* ---------------------------------------------------------------------*)

fun REDUCE f x th =
  if not(is_abs x orelse is_uncurry x) then th 
  else let val (Bvar,Body) = Term.dest_abs f 
       in CONV_RULE (RAND_CONV (RED_WHERE Bvar Body)) th
       end;

(* ---------------------------------------------------------------------*)
(* let_CONV: conversion for reducing "let" terms.			*)
(*									*)
(* Given a term:                                    			*)
(*                                                                      *)
(*   "let v1 = x1 and ... and vn = xn in tm[v1,...,vn]"			*)
(*                                                                      *)
(* let_CONV proves that:						*)
(*                                                                      *)
(*   |- let v1 = x1 and ... and vn = xn in tm[v1,...,vn] 		*)
(*	=								*)
(*      tm[x1,...,xn/v1,...,vn]						*)
(*                                                                      *)
(* where t[t1,...,tn/x1,...,xn] is the result of "substituting" the 	*)
(* value xi for vi  in parallel in tm (see below).			*)
(*									*)
(* Note that the vi's can take any one of the following forms:  	*)
(*									*)
(*    Variables:    "x" etc.    					*)
(*    Tuples:       "(x,y)" "(a,b,c)" "((a,b),(c,d))" etc.		*)
(*    Applications: "f (x,y) z" "f x" etc.				*)
(*									*)
(* Variables are just substituted for. With tuples, the substitution is	*)
(* done component-wise, and function applications are effectively	*)
(* rewritten in the body of the let-term.				*)
(* ---------------------------------------------------------------------*)

local
fun conv tm = 
   let val (func,arg) = dest_let tm
       val (ty1,ty2) = dom_rng (type_of func)
       val defn = INST_TYPE [alpha |-> ty1, beta |-> ty2] LET_DEF
       val thm = RIGHT_BETA(AP_THM(RIGHT_BETA(AP_THM defn func))arg)
   in 
   if Term.is_abs func
   then REDUCE func arg (RIGHT_BETA thm) 
   else if is_uncurry func
        then CONV_RULE (RAND_CONV PAIRED_BETA_CONV) thm 
        else CONV_RULE (RAND_CONV conv) 
                       (AP_THM(AP_TERM (rator(rator tm)) (conv func)) arg)
   end
in
fun let_CONV tm = conv tm 
 handle HOL_ERR _ => raise ERR "let_CONV" "cannot reduce the let"
end;


(* ===================================================================== *)
(* Paired version of variant.                                            *)
(* ===================================================================== *)

(*
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
(* Occurence check for bound pairs.                                      *)
(* occs_in p t    true iff any of the variables in p occur free in t     *)
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
*)

end;
