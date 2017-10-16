structure liteLib :> liteLib =
struct

open Feedback Thm Conv Abbrev;

val aconv = Term.aconv

(*---------------------------------------------------------------------------
 * Fake for NJSML: it does not use Interrupt anyway so it won't ever
 * get raised.
 *---------------------------------------------------------------------------*)
(* exception Interrupt;   *)



(*---------------------------------------------------------------------
 *               Exceptions
 *--------------------------------------------------------------------*)

val ERR = mk_HOL_ERR "liteLib"

fun STRUCT_ERR s (func,mesg) = raise Feedback.mk_HOL_ERR s func mesg
fun STRUCT_WRAP s (func,exn) = raise Feedback.wrap_exn s func exn

(*---------------------------------------------------------------------
 * options
 *--------------------------------------------------------------------*)

fun the (SOME x) = x
  | the _ = failwith "the: can't take \"the\" of NONE"

fun is_some (SOME x) = true
  | is_some NONE = false

fun is_none NONE = true
  | is_none _ = false

fun option_cases f e (SOME x) = f x
  | option_cases f e NONE = e

fun option_app f (SOME x) = SOME (f x)
  | option_app f NONE = NONE


infix 3 |> thenf orelsef;
fun (x |> f) = f x;

fun (f thenf g) x = g(f x);

fun (f orelsef g) x =
  f x handle Interrupt => raise Interrupt
           |         _ => g x;

val repeat = Lib.repeat

fun foldr f e L =
   let fun itl [] = e
         | itl (a::rst) = f (a,itl rst)
   in itl L
   end;

fun foldl f e L =
   let fun rev_it [] e  = e
         | rev_it (a::rst) e = rev_it rst (f (a,e))
   in rev_it L e
   end;

fun end_foldr f =
   let fun endit [] = failwith "end_foldr: list too short"
         | endit alist =
            let val (base,ralist) = case rev alist of
                                      h::t => (h,t)
                                    | _ => raise Bind
            in foldr f base (rev ralist)
            end
   in endit
   end;

val chop_list = Lib.split_after;

fun rotl (a::rst) = rst@[a]
  | rotl [] = failwith "rotl: empty list"

fun rotr lst =
   let val (front,last) = Lib.front_last lst
   in last::front
   end
   handle HOL_ERR _ => failwith "rotr: empty list"


fun replicate (x,n) =
   let fun repl 0 = []
         | repl n = x::repl (n-1)
   in repl n
   end

fun upto (n,m) = if n >= m then [] else n::upto (n+1,m);

(* ------------------------------------------------------------------------- *)
(* Iterative splitting (list) and stripping (tree) via destructor.           *)
(* ------------------------------------------------------------------------- *)

fun splitlist dest x =
  let val (l,r) = dest x
      val (ls,res) = splitlist dest r
  in (l::ls,res)
  end
  handle Interrupt => raise Interrupt
       | _ => ([],x);;

fun rev_splitlist dest =
  let fun rsplist ls x =
    let val (l,r) = dest x
    in  rsplist (r::ls) l
    end
    handle Interrupt => raise Interrupt
	 | _ => (x,ls)
  in
    fn x => rsplist [] x
  end;;

fun striplist dest =
  let fun strip x acc =
    let val (l,r) = dest x
    in strip l (strip r acc)
    end
    handle Interrupt => raise Interrupt
	 | _ => x::acc
  in
    fn x => strip x []
  end;;


(*--------------------------------------------------------------------*
 * Associative list functions                                         *
 *--------------------------------------------------------------------*)

val rev_assoc = Lib.rev_assoc;

fun remove_assoc x =
    let fun remove [] = raise ERR "" ""
	  | remove ((h as (l,r))::t) = if (x = l) then t else (h::remove t)
    in fn l => (remove l handle HOL_ERR _ => l)
    end;

fun add_assoc (x as (l,r)) ll = x::remove_assoc l ll;

(* ------------------------------------------------------------------------- *)
(* "lazy" objects to delay calculation and avoid recalculation.              *)
(* ------------------------------------------------------------------------- *)

datatype ('a,'b)Lazysum = Unrealized of ('a -> 'b) * 'a
                        | Realized of 'b;

type ('a,'b)lazy = ('a,'b) Lazysum ref;

fun lazy f x = ref(Realized (f x));
fun eager y  = ref(Realized y);;

fun eval r =
  case !r of
    Realized(y) => y
  | Unrealized(f,x) => let val y = f(x) in (r := Realized(y); y) end;;

(*-------------------------------------------------------------------*
 * Orders                                                            *
 *-------------------------------------------------------------------*)

fun ord_of_lt lt (x,y) =
    if lt(x, y) then LESS else
    if lt(y,x) then GREATER else EQUAL;

fun lt_of_ord ord (x,y) = (ord(x, y) = LESS);

val list_ord = Lib.list_compare


(* ===================================================================== *
 * Basic equality reasoning including conversionals.                     *
 * ===================================================================== *)

(*--------------------------------------------------------------------------*
 * General syntax for binary operators (monomorphic constructor only).      *
 *                                                                          *
 * Nb. strip_binop strips only on the right, binops strips both             *
 * left and right (alal conjuncts and disjuncts).                           *
 * -------------------------------------------------------------------------*)

fun mk_binop opr (l,r) =
    Term.list_mk_comb(opr,[l,r]) handle HOL_ERR _ => failwith "mk_binop"

fun list_mk_binop opr = Lib.end_itlist (Lib.curry (mk_binop opr));

fun dest_binop opr tm =
    let val (Rator,rhs) = Term.dest_comb tm
	val (opr',lhs) = Term.dest_comb Rator
    in
	if aconv opr opr' then (lhs,rhs) else fail()
    end
    handle HOL_ERR _ => failwith "dest_binop";

fun strip_binop opr =
    let val dest = dest_binop opr
	fun strip tm =
	    let val (l,r) = dest tm
		val (str,rm) = strip r
	    in (l::str,rm)
	    end
  	    handle HOL_ERR _ => ([],tm)
    in strip
    end;

fun binops opr =
    let val dest = dest_binop opr
	fun strip tm =
	    let val (l,r) = dest tm
	    in strip l @ strip r
	    end
  	    handle HOL_ERR _ => [tm]
    in strip
    end;

fun is_binop opr = Lib.can (dest_binop opr)

val is_imp    = is_binop boolSyntax.implication;
val dest_imp  = dest_binop boolSyntax.implication;
val strip_imp = splitlist dest_imp;


(* ------------------------------------------------------------------------- *)
(* Grabbing left operand of a binary operator (or something coextensive!)    *)
(* ------------------------------------------------------------------------- *)

val lhand = Term.rand o Term.rator;;

(* ------------------------------------------------------------------------- *)
(* Like mk_comb, but instantiates type variables in rator if necessary.      *)
(* ------------------------------------------------------------------------- *)

fun mk_icomb(tm1,tm2) =
  let val ty = Lib.fst(Type.dom_rng(Term.type_of tm1))
      val tyins = Type.match_type ty (Term.type_of tm2)
  in
    Term.mk_comb(Term.inst tyins tm1, tm2)
  end;;

(* ------------------------------------------------------------------------- *)
(* Instantiates types for constant c and iteratively makes combination.      *)
(* ------------------------------------------------------------------------- *)

fun list_mk_icomb tm1 args =
   Lib.rev_itlist (Lib.C (Lib.curry mk_icomb)) args tm1;;

(* ------------------------------------------------------------------------- *)
(* Rule allowing easy instantiation of polymorphic proformas.                *)
(* ------------------------------------------------------------------------- *)

fun PINST tyin tmin =
  let val inst_fn = Term.inst tyin
      val tmin' = map (fn {redex,residue} =>
                          {redex=inst_fn redex, residue=residue}) tmin
      val iterm_fn = Thm.INST tmin'
      val itype_fn = Thm.INST_TYPE tyin
  in
      fn th => iterm_fn (itype_fn th) handle HOL_ERR _ => failwith "PINST"
  end;


(* ------------------------------------------------------------------------- *)
(* Really basic stuff for equality.                                          *)
(* ------------------------------------------------------------------------- *)

fun MK_BINOP oper (lth,rth) = MK_COMB(AP_TERM oper lth,rth);

(* ------------------------------------------------------------------------- *)
(* Subterm conversions.                                                      *)
(* ------------------------------------------------------------------------- *)

val LAND_CONV   = Conv.LAND_CONV
val BINDER_CONV = Conv.BINDER_CONV

fun COMB2_CONV lconv rconv tm =
 let val (Rator,Rand) = Term.dest_comb tm
 in MK_COMB(lconv Rator, rconv Rand)
 end;

val COMB_CONV = Lib.W COMB2_CONV;;

fun alpha v tm =
  let
    val (v0,bod) = Term.dest_abs tm
                   handle HOL_ERR _ => failwith "alpha: Not an abstraction"
  in
    if aconv v v0 then tm
    else if not (Term.free_in v bod) then
      Term.mk_abs(v, Term.subst [Lib.|->(v0,v)] bod)
    else failwith "alpha: Invalid new variable"
  end;


val ABS_CONV = Conv.ABS_CONV

val BODY_CONV =
 let fun dest_quant tm =
       let val (q,atm) = Term.dest_comb tm
           val (v,bod) = Term.dest_abs atm
       in ((q,v),bod)
       end
     val strip_quant = splitlist dest_quant
 in fn conv => fn tm =>
    let val (quants,bod) = strip_quant tm
    in Lib.itlist(fn (q,v) => fn th => AP_TERM q (ABS v th)) quants (conv bod)
    end
 end;;

(* ------------------------------------------------------------------------- *)
(* Faster depth conversions using failure rather than returning a REFL.      *)
(* ------------------------------------------------------------------------- *)

val rhs = boolSyntax.rhs;

infix THENQC THENCQC;

fun op THENQC (conv1,conv2) tm =
  let val th1 = conv1 tm
  in let val th2 = conv2(rhs(concl th1))
     in TRANS th1 th2
     end handle HOL_ERR _ => th1
  end
  handle HOL_ERR _ => conv2 tm;


fun op THENCQC (conv1,conv2) tm =
  let val th1 = conv1 tm
  in let val th2 = conv2(rhs(concl th1))
     in TRANS th1 th2
     end
     handle HOL_ERR _ => th1
  end

fun REPEATQC conv tm = (conv THENCQC (REPEATQC conv)) tm;;

fun COMB2_QCONV conv1 conv2 tm =
  let val (l,r) = Term.dest_comb tm
  in let val th1 = conv1 l
     in let val th2 = conv2 r
	in MK_COMB(th1,th2)
	end
        handle HOL_ERR _ => AP_THM th1 r
     end
     handle HOL_ERR _ => AP_TERM l (conv2 r)
  end;

val COMB_QCONV = Lib.W COMB2_QCONV;;

fun SUB_QCONV conv tm =
  if Term.is_abs tm then ABS_CONV conv tm
  else COMB_QCONV conv tm;;

fun ONCE_DEPTH_QCONV conv tm =
  (conv ORELSEC (SUB_QCONV (ONCE_DEPTH_QCONV conv))) tm;;

fun DEPTH_QCONV conv tm =
   ((SUB_QCONV (DEPTH_QCONV conv)) THENQC
    (REPEATQC conv)) tm;;

fun REDEPTH_QCONV conv tm =
   ((SUB_QCONV (REDEPTH_QCONV conv)) THENQC
    (conv THENCQC (REDEPTH_QCONV conv))) tm;;

fun TOP_DEPTH_QCONV conv tm =
   ((REPEATQC conv) THENQC
    (SUB_QCONV (TOP_DEPTH_QCONV conv)
      THENCQC
     (conv THENCQC (TOP_DEPTH_QCONV conv)))) tm;;

fun TOP_SWEEP_QCONV conv tm =
  ((REPEATQC conv) THENQC
   (SUB_QCONV (TOP_SWEEP_QCONV conv))) tm;;

(* ------------------------------------------------------------------------- *)
(* Standard conversions.                                                     *)
(* ------------------------------------------------------------------------- *)

fun TOP_SWEEP_CONV c = TRY_CONV (TOP_SWEEP_QCONV c);;

(* ------------------------------------------------------------------------- *)
(* Apply at leaves of op-tree; NB any failures at leaves cause failure.      *)
(* ------------------------------------------------------------------------- *)

local exception DEST_BINOP
in
fun DEPTH_BINOP_CONV oper conv tm =
  let val (l,r) = dest_binop oper tm handle HOL_ERR _ => raise DEST_BINOP
      val lth = DEPTH_BINOP_CONV oper conv l
      and rth = DEPTH_BINOP_CONV oper conv r
  in MK_COMB(AP_TERM oper lth,rth)
  end
  handle DEST_BINOP => conv tm
end;


(* ------------------------------------------------------------------------- *)
(* Single bottom-up pass, starting at the topmost success!                   *)
(* ------------------------------------------------------------------------- *)

fun SINGLE_DEPTH_CONV conv tm =
  conv tm handle HOL_ERR _
  => (SUB_CONV (SINGLE_DEPTH_CONV conv)
               THENC TRY_CONV conv) tm;;

(*-----------------------------------------------------------------------*)
(* MK_ABS_CONV - Abstract a term by a variable                           *)
(* MK_ABSL_CONV - Abstract a term by a set of variables                  *)
(*                                                                       *)
(* [DRS 96.01.28]                                                        *)
(*-----------------------------------------------------------------------*)

fun MK_ABS_CONV var tm =
  if Term.is_comb tm andalso aconv (Term.rand tm) var
     andalso not (Term.free_in var (Term.rator tm))
  then
    REFL tm
  else
    let
      val rhs = Term.mk_abs(var,tm)
      val newrhs = Term.mk_comb(rhs,var)
    in
      SYM (BETA_CONV newrhs)
    end;

fun MK_ABSL_CONV vars tm =
 let val rhs = boolSyntax.list_mk_abs (vars,tm)
     val newrhs = Term.list_mk_comb(rhs,vars)
     val thm1 = foldr (fn (_,conv) => (RATOR_CONV conv) THENC BETA_CONV)
                      ALL_CONV vars newrhs
 in SYM thm1
 end;

val RIGHT_BETAS =
  Lib.rev_itlist (fn a => CONV_RULE (RAND_CONV BETA_CONV) o Lib.C AP_THM a);;

fun name_of_const tm =
 let val {Name,Thy,...} = Term.dest_thy_const tm in (Name,Thy) end;

fun MK_CONJ eq1 eq2 = MK_COMB(AP_TERM boolSyntax.conjunction eq1,eq2)
fun MK_DISJ eq1 eq2 = MK_COMB(AP_TERM boolSyntax.disjunction eq1,eq2)
fun MK_FORALL v th =
  let val theta = [{redex=Type.alpha, residue=Term.type_of v}]
  in AP_TERM (Term.inst theta boolSyntax.universal) (ABS v th)
  end;
fun MK_EXISTS v th =
  let val theta = [{redex=Type.alpha, residue=Term.type_of v}]
  in AP_TERM (Term.inst theta boolSyntax.existential) (ABS v th)
  end;

fun SIMPLE_DISJ_CASES th1 th2 =
  case (hyp th1, hyp th2)
   of (h1::_, h2::_) => DISJ_CASES (ASSUME(boolSyntax.mk_disj(h1,h2))) th1 th2
    |  _ => raise ERR "SIMPLE_DISJ_CASES" "";

val SIMPLE_CHOOSE = Drule.SIMPLE_CHOOSE

end;
