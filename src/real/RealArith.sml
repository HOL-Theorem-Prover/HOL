(* ========================================================================= *)
(* Linear decision procedure for the reals, plus some proof procedures.      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*                                                                           *)
(*       Ported to hol98 by Joe Hurd, 2 Oct 1998                             *)
(* ========================================================================= *)
(* Framework for universal real decision procedures, and a simple instance.  *)
(*             (HOL-Light's calc_int.ml and realarith.ml)                    *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                                                                           *)
(*       Ported to HOL4 by Chun Tian, 5 June 2022                            *)
(* ========================================================================= *)

structure RealArith :> RealArith =
struct

open HolKernel Parse boolLib liteLib

open reduceLib Ho_Rewrite Canon_Port AC RealArith0

open normalForms  (* for HOL-Light's GEN_NNF_CONV, etc. *)
open Normalizer   (* for HOL-Light's SEMIRING_NORMALIZERS_CONV *)

open realaxTheory real_arithTheory (* NOTE: cannot open realTheory here *)
open Arbint       (* TODO: remove this in the future, using the default Int *)

(*---------------------------------------------------------------------------*)
(* Establish the required grammar(s) for executing this file                 *)
(*---------------------------------------------------------------------------*)

structure Parse = struct
  open Parse
  val (Type,Term) =
      parse_from_grammars
        (apsnd ParseExtras.grammar_loose_equality $ valOf $
           grammarDB {thyname = "realax"})
end

open Parse

(* clarify some conflicting functions *)
val assert      = Lib.assert
val SKOLEM_CONV = Canon_Port.SKOLEM_CONV

(*----------------------------------------------------------------------- *)
(* The trace system.                                                      *)
(* ---------------------------------------------------------------------- *)

local
  open Int
  val traceval = ref 0

  fun trace_pure s () = print s
  fun check f = if !traceval > 0 then f() else ()
  infix >>
  fun (f >> g) () = (f (); g ())
  val _ = register_trace ("RealArith dp", traceval, 1)
  fun trace_line () = print "\n"
  local
    fun tl f [] = (fn () => ())
      | tl f [h] = f h
      | tl f (h::t) = (f h >> trace_pure ", " >> tl f t)
  in
    fun trace_list_pure f l () =
        (trace_pure "[" >> tl f l >> trace_pure "]") ()
  end
  fun trace_term_pure t () = print (term_to_string t)
  fun trace_thm_pure t = trace_term_pure (concl t)
in
  fun trace s = check (trace_pure (s ^ "\n"))
  fun trace_term t = check (trace_term_pure t >> trace_line)
  fun trace_term_list l =
      check (trace_list_pure trace_term_pure l >> trace_line)
  fun trace_thm t = check (trace_thm_pure t >> trace_line)
  fun trace_thm_list l = check (trace_list_pure trace_thm_pure l >> trace_line)
end

(* ------------------------------------------------------------------------- *)
(* Functions to be compatible with hol-light.                                *)
(* ------------------------------------------------------------------------- *)

fun failwith s = raise mk_HOL_ERR "RealArith" "?" s

fun term_lt u t = (Term.compare(u,t) = LESS)
fun term_le t u = not (term_lt u t)

fun el0 n l = if n <= zero then hd l
              else el0 (n - one) (tl l) handle _ => raise Fail "RealArith.el0"

fun index x =
  let
    fun ind n [] = failwith "index"
      | ind n (h::t) = if x = h then n else ind (n + one) t
  in
    ind zero
  end

fun index_ac x = let
  fun ind n [] = failwith "index_ac"
    | ind n (h::t) = if aconv x h then n else ind (n + one) t
in
  ind zero
end

fun chop_list n l =
  if n = zero then ([],l) else
    let
      val (m,l') = chop_list (n-one) (Lib.trye tl l)
    in
      (Lib.trye hd l::m, l')
    end
    handle HOL_ERR _ => failwith "chop_list"

val mk_binop =
  let
    fun mk_binop_alt t = curry (liteLib.mk_binop t)
  in
    mk_binop_alt
  end

fun list_mk_binop op_alt = end_itlist (mk_binop op_alt)

(* ------------------------------------------------------------------------- *)
(* Preparing the real linear decision procedure.                             *)
(* ------------------------------------------------------------------------- *)

val REAL_ADD_AC = AC (REAL_ADD_ASSOC, REAL_ADD_SYM)
val REAL_MUL_AC = AC (REAL_MUL_ASSOC, REAL_MUL_SYM)

val PROP_DNF_CONV =
  GEN_REWRITE_CONV REDEPTH_CONV
   [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, GSYM CONJ_ASSOC, GSYM DISJ_ASSOC]

(* ------------------------------------------------------------------------- *)
(* Conversion to normalize product terms, i.e:                               *)
(*                                                                           *)
(* Separate out (and multiply out) integer constants, put the term in        *)
(* the form "([-]&n) * x" where either x is a canonically ordered product    *)
(* of the non-integer-constants, or is "&1".                                 *)
(* ------------------------------------------------------------------------- *)

local
  val x_tm = ``x:real``
  val mul_tm = ``$* : real -> real -> real``
  val binops_mul = liteLib.binops mul_tm
  val list_mk_binop_mul = list_mk_binop mul_tm
  val mk_binop_mul = mk_binop mul_tm
in
  fun REAL_PROD_NORM_CONV tm =
    let
      val _ = trace "REAL_PROD_NORM_CONV"
      val _ = trace_term tm
      val factors = binops_mul tm
      val (consts,others) = partition is_intconst factors
      val res =
      if null others then
        let
          val th1 = QCONV (DEPTH_CONV REAL_INT_MUL_CONV) tm
        in
          TRANS th1 (INST [x_tm |-> rand(concl th1)] REAL_PROD_NORM_CONV_pth1)
        end
      else
        let
          val sothers = sort term_lt others
        in
          if null consts then
            let
              val t = mk_eq (tm, list_mk_binop_mul sothers)
              val th1 = REAL_MUL_AC t
            in
              TRANS th1 (INST [x_tm |-> rand(concl th1)] REAL_PROD_NORM_CONV_pth2)
            end
          else
            let
              val th1 = REAL_MUL_AC
                (mk_eq(tm,mk_binop_mul(list_mk_binop_mul consts)
                          (list_mk_binop_mul sothers)))
              val tm1 = rand(concl th1)
              val th2 = AP_TERM mul_tm (QCONV (DEPTH_CONV REAL_INT_MUL_CONV)
                                              (liteLib.lhand tm1))
            in
              TRANS th1 (AP_THM th2 (rand tm1))
            end
        end
      val _ = trace_thm res
      val _ = trace "done REAL_PROD_NORM_CONV"
    in
      res
    end
end

(* ------------------------------------------------------------------------- *)
(* Add together canonically ordered standard linear lists.                   *)
(* ------------------------------------------------------------------------- *)

local
  val x_tm = ``x:real``
  val [pth1, pth2, pth3, pth4, pth5, pth6] = CONJUNCTS LINEAR_ADD_pth1
  val tm1_tm = ``tm1:real``
  val l1_tm = ``l1:real``
  val r1_tm = ``r1:real``
  val tm2_tm = ``tm2:real``
  val l2_tm = ``l2:real``
  val r2_tm = ``r2:real``
  val add_tm = ``$+ :real->real->real``
  val dest = liteLib.dest_binop add_tm
  val mk = mk_binop add_tm
  val zero_tm = ``&0 :real``
  val COEFF_CONV =
    QCONV (REWR_CONV (GSYM REAL_ADD_RDISTRIB) THENC LAND_CONV REAL_INT_ADD_CONV)
  fun linear_add tm1 tm2 =
    let
      val _ = trace "linear_add"
      val _ = trace_term tm1
      val _ = trace_term tm2
      val res =
      let
        val ltm = mk tm1 tm2
      in
        if tm1 ~~ zero_tm then INST [x_tm |-> tm2] LINEAR_ADD_pth0a
        else if tm2 ~~ zero_tm then INST [x_tm |-> tm1] LINEAR_ADD_pth0b else
          let
            val (l1,r1) = dest tm1
            val v1 = rand l1
            val _ = trace "v1 ="
            val _ = trace_term v1
          in
            let
              val (l2,r2) = dest tm2
              val v2 = rand l2
              val _ = trace "v2 ="
              val _ = trace_term v2
            in
              if aconv v1 v2 then
                let
                  val th1 = INST [l1_tm |-> l1, l2_tm |-> l2,
                                  r1_tm |-> r1, r2_tm |-> r2] pth1
                  val th2 = CONV_RULE (RAND_CONV(LAND_CONV COEFF_CONV)) th1
                  val ctm = rator(rand(concl th2))
                in
                  TRANS th2 (AP_TERM ctm (linear_add r1 r2))
                end
                (* handle e as HOL_ERR => Raise e *)
              else if term_lt v1 v2 then
                let
                  val th1 = INST [l1_tm |-> l1, r1_tm |-> r1, tm2_tm |-> tm2] pth2
                  val ctm = rator(rand(concl th1))
                in
                  TRANS th1 (AP_TERM ctm (linear_add r1 tm2))
                end
              else
                let
                  val th1 = INST [tm1_tm |-> tm1, l2_tm |-> l2, r2_tm |-> r2] pth3
                  val ctm = rator(rand(concl th1))
                in
                  TRANS th1 (AP_TERM ctm (linear_add tm1 r2))
                end
            end
            handle HOL_ERR _ =>
              let
                val _ = trace "can't add_dest term2"
                val v2 = rand tm2
                val _ = trace "v2 ="
                val _ = trace_term v2
              in
                if aconv v1 v2 then
                  let
                    val th1 = INST [l1_tm |-> l1, r1_tm |-> r1, tm2_tm |-> tm2] pth4
                  in
                    CONV_RULE (RAND_CONV(LAND_CONV COEFF_CONV)) th1
                  end
                else if term_lt v1 v2 then
                  let
                    val th1 = INST [l1_tm |-> l1, r1_tm |-> r1, tm2_tm |-> tm2] pth2
                    val ctm = rator(rand(concl th1))
                  in
                    TRANS th1 (AP_TERM ctm (linear_add r1 tm2))
                  end
                else
                  INST [tm1_tm |-> tm1, tm2_tm |-> tm2] pth5
              end
          end
          handle _ =>
            let
              val _ = trace "can't add_dest term1"
              val v1 = rand tm1
            in
              let
                val (l2,r2) = dest tm2
                val v2 = rand l2
              in
                if aconv v1 v2 then
                  let
                    val th1 = INST [tm1_tm |-> tm1, l2_tm |-> l2, r2_tm |-> r2] pth6
                  in
                    CONV_RULE (RAND_CONV(LAND_CONV COEFF_CONV)) th1
                  end
                else if term_lt v1 v2 then
                  REFL ltm
                else
                  let
                    val th1 = INST [tm1_tm |-> tm1, l2_tm |-> l2, r2_tm |-> r2] pth3
                    val ctm = rator(rand(concl th1))
                  in
                    TRANS th1 (AP_TERM ctm (linear_add tm1 r2))
                  end
              end
              handle _ =>
                let
                  val _ = trace "can't add_dest term2 either"
                  val v2 = rand tm2
                in
                  if aconv v1 v2 then
                    COEFF_CONV ltm
                  else if term_lt v1 v2 then
                    REFL ltm
                  else
                    INST [tm1_tm |-> tm1, tm2_tm |-> tm2] pth5
                end
            end
      end
    val _ = trace_thm res
    val _ = trace "done linear_add"
  in
    res
  end
in
  fun LINEAR_ADD tm1 tm2 =
    let
      val _ = trace "LINEAR_ADD"
      val _ = trace_term tm1
      val _ = trace_term tm2
      val th = linear_add tm1 tm2
      val tm = rand(concl th)
      val zth =
          QCONV (GEN_REWRITE_CONV
                    DEPTH_CONV
                    [REAL_MUL_LZERO, REAL_ADD_LID', REAL_ADD_RID]) tm
      val res = TRANS th zth
      val _ = trace_thm res
      val _ = trace "done LINEAR_ADD"
    in
      res
    end
end

(* ------------------------------------------------------------------------- *)
(* Collection of like terms.                                                 *)
(* ------------------------------------------------------------------------- *)

local
  val add_tm = ``$+ :real->real->real``
  val dest = liteLib.dest_binop add_tm
in
  fun COLLECT_CONV tm =
    let
      val (l,r) = dest tm
      val lth = COLLECT_CONV l
      val rth = COLLECT_CONV r
      val xth = LINEAR_ADD (rand(concl lth)) (rand(concl rth))
    in
      TRANS (MK_COMB(AP_TERM add_tm lth,rth)) xth
    end
    handle HOL_ERR _ => REFL tm
end

(* ------------------------------------------------------------------------- *)
(* Normalize a term in the standard linear form.                             *)
(* ------------------------------------------------------------------------- *)

local
  val ptm = ``$~ :real->real``
  val stm = ``$+ :real->real->real``
  val one_tm = ``&1 :real``
  val binops_add = liteLib.binops stm
  val list_mk_binop_add = list_mk_binop stm
  fun prelim_conv t =
    let
      val _ = trace "prelim_conv"
      fun c1 t = (trace "gen_rewrite 1";
                  trace_term t;
                  GEN_REWRITE_CONV I [REAL_SUM_NORM_CONV_pth1] t)
      fun c2 t = (trace "gen_rewrite 2";
                  trace_term t;
                  GEN_REWRITE_CONV I [REAL_SUM_NORM_CONV_pth2] t)
      fun c3 t = (trace "gen_rewrite 3"; trace_term t;
                  GEN_REWRITE_CONV TOP_DEPTH_CONV
                  [REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB] t)
      fun c4 t = (trace "gen_rewrite 4"; trace_term t;
                  GEN_REWRITE_CONV DEPTH_CONV
                  [REAL_MUL_LZERO, REAL_MUL_RZERO,
                  REAL_MUL_LID', REAL_MUL_RID,
                  REAL_ADD_LID', REAL_ADD_RID] t)
      val c = DEPTH_CONV((c1 o assert(fn t => not (rand t ~~ one_tm)))
              ORELSEC c2) THENC c3 THENC c4
      val res = c t
      val _ = trace "done prelim_conv"
    in
      res
    end
in
  fun REAL_SUM_NORM_CONV tm =
    let
      val _ = trace "REAL_SUM_NORM_CONV"
      val _ = trace_term tm
      val th1 = QCONV prelim_conv tm
      val th2 = liteLib.DEPTH_BINOP_CONV stm
                    (QCONV REAL_PROD_NORM_CONV) (rand(concl th1))
      val tm2 = rand(concl th2)
      val elements = binops_add tm2
      val selements = sort (fn x => fn y => term_le (rand x) (rand y))
                            elements
      val th3 = REAL_ADD_AC(mk_eq(tm2,list_mk_binop_add selements))
      val th4 = COLLECT_CONV (rand(concl th3))
      val res = itlist TRANS [th1, th2, th3] th4
      val _ = trace "done REAL_SUM_NORM_CONV"
    in
      res
    end
end

(* ------------------------------------------------------------------------- *)
(* Produce negated forms of canonicalization theorems.                       *)
(* ------------------------------------------------------------------------- *)

local
  val rewr1_CONV = FIRST_CONV
    (map REWR_CONV [REAL_NEGATE_CANON_pth2, REAL_NEGATE_CANON_pth3])
  val rewr2_CONV = FIRST_CONV
    (map REWR_CONV [REAL_NEGATE_CANON_pth4, REAL_NEGATE_CANON_pth5])
  fun distrib_neg_conv tm =
    let
      val _ = trace "distrib_neg_conv"
      val _ = trace_term tm
      val res =
        let
          val th = rewr1_CONV tm
          val _ = trace "ok so far"
          val t = rand (concl th)
          val _ = trace_term t
        in
          TRANS th (RAND_CONV distrib_neg_conv t)
        end
        handle HOL_ERR _ => rewr2_CONV tm
      val _ = trace "done distrib_neg_conv"
    in
      res
    end
in
  fun REAL_NEGATE_CANON th =
    let
      val _ = trace "REAL_NEGATE_CANON"
      val _ = trace_thm th
      val th1 = GEN_REWRITE_RULE I [REAL_NEGATE_CANON_pth1] th
      val _ = trace_thm th1
      val t = rand (concl th1)
      val _ = trace_term t
      val res = TRANS th1 (RAND_CONV distrib_neg_conv t)
      val _ = trace "done REAL_NEGATE_CANON"
    in
      res
    end
end

(* ------------------------------------------------------------------------- *)
(* Version for whole atom, with intelligent cacheing.                        *)
(* ------------------------------------------------------------------------- *)

local
  val right_CONV = RAND_CONV REAL_SUM_NORM_CONV
  val atomcache = ref []
  fun lookup_cache tm =
    first (fn th => liteLib.lhand(concl th) ~~ tm) (!atomcache)
  val negate_CONV = GEN_REWRITE_CONV I
    [REAL_ATOM_NORM_CONV_pth2, REAL_ATOM_NORM_CONV_pth3]
  val le_tm = ``$<= :real->real->bool``
  val lt_tm = ``$< :real->real->bool``
in
  fun clear_atom_cache () = (atomcache := [])
  fun REAL_ATOM_NORM_CONV tm = (trace "REAL_ATOM_NORM_CONV"; lookup_cache tm
    handle HOL_ERR _ =>
      let
        val th = right_CONV tm
      in
        (atomcache := th::(!atomcache);
        let
          val th' = REAL_NEGATE_CANON th
        in
          atomcache := th'::(!atomcache)
        end
        handle HOL_ERR _ => ();
        th)
      end)
end

(* ------------------------------------------------------------------------- *)
(* abs                                                                       *)
(* ------------------------------------------------------------------------- *)

val REAL_INT_ABS_CONV =
  TRY_CONV(GEN_REWRITE_CONV I [REAL_INT_ABS_CONV_pth])

fun real_int_compset () = let
  open computeLib
  val compset = num_compset()
  val _ = add_conv (realSyntax.leq_tm,     2, REAL_INT_LE_CONV) compset
  val _ = add_conv (realSyntax.less_tm,    2, REAL_INT_LT_CONV) compset
  val _ = add_conv (realSyntax.geq_tm,     2, REAL_INT_GE_CONV) compset
  val _ = add_conv (realSyntax.greater_tm, 2, REAL_INT_GT_CONV) compset
  val _ = add_conv (realSyntax.real_eq_tm, 2, REAL_INT_EQ_CONV) compset
  val _ = add_conv (realSyntax.negate_tm,  1,
                                 CHANGED_CONV REAL_INT_NEG_CONV) compset
  val _ = add_conv (realSyntax.absval_tm,  1, REAL_INT_ABS_CONV) compset
  val _ = add_conv (realSyntax.plus_tm,    2, REAL_INT_ADD_CONV) compset
  val _ = add_conv (realSyntax.minus_tm,   2, REAL_INT_SUB_CONV) compset
  val _ = add_conv (realSyntax.mult_tm,    2, REAL_INT_MUL_CONV) compset
  val _ = add_conv (realSyntax.exp_tm,     2, REAL_INT_POW_CONV) compset
in
  compset
end

val REAL_INT_REDUCE_CONV = let
  val cs = real_int_compset ()
  val _ = computeLib.set_skip cs boolSyntax.conditional NONE
          (* ensure that REDUCE_CONV will look at all of a term, even
             conditionals' branches *)
in
  computeLib.CBV_CONV cs
end

(* ------------------------------------------------------------------------- *)
(* Combinators.                                                              *)
(* ------------------------------------------------------------------------- *)

infix F_F
fun (f F_F g) (x, y) = (f x, g y)

(* ------------------------------------------------------------------------- *)
(* Replication and sequences.                                                *)
(* ------------------------------------------------------------------------- *)

local
  fun down l n = if n < zero then l else down (n::l) (n - one)
in
  val upto = down []
end

(* ------------------------------------------------------------------------- *)
(* Encodings of linear inequalities with justifications.                     *)
(* ------------------------------------------------------------------------- *)

datatype lineq_type = Eq | Le | Lt

datatype injust = Given of thm
                | Multiplied of int * injust
                | Added of injust * injust

datatype lineq = Lineq of int * lineq_type * int list * injust

val thmeq = pair_eq (list_eq aconv) aconv

fun injust_eq (Given t, Given t') = thmeq (dest_thm t) (dest_thm t')
  | injust_eq (Multiplied (i,j), Multiplied (i',j')) =
      (i = i') andalso injust_eq (j,j')
  | injust_eq (Added (j1,j2), Added (j1',j2')) =
      injust_eq (j1,j1') andalso injust_eq (j2,j2')
  | injust_eq (j,j') = false

fun lineq_eq (Lineq(i,t,l,j),Lineq(i',t',l',j')) =
  i = i' andalso t = t' andalso l = l' andalso injust_eq (j,j')

(* ------------------------------------------------------------------------- *)
(* The main refutation-finding code.                                         *)
(* ------------------------------------------------------------------------- *)

fun is_trivial (Lineq(_,_,l,_)) = all ((curry op=) zero) l

fun find_answer (ans as Lineq (k,ty,l,_)) =
  if ty = Eq andalso (not (k = zero))
    orelse ty = Le andalso k > zero
    orelse ty = Lt andalso k >= zero
  then
    ans
  else
    failwith "find_answer"

fun calc_blowup l =
  let
    val (p,n) = partition ((curry op<) zero) (filter ((curry op<>) zero) l)
  in
    (fromInt (length p)) * (fromInt (length n))
  end

(* ------------------------------------------------------------------------- *)
(* "Set" operations on lists.                                                *)
(* ------------------------------------------------------------------------- *)

fun union l1 l2 = itlist insert l1 l2

fun Union l = itlist union l []

(* ------------------------------------------------------------------------- *)
(* Calculate new (in)equality type after addition.                           *)
(* ------------------------------------------------------------------------- *)

val find_add_type =
  fn (Eq,x) => x
    | (x,Eq) => x
    | (_,Lt) => Lt
    | (Lt,_) => Lt
    | (Le,Le) => Le

(* ------------------------------------------------------------------------- *)
(* Add together (in)equations.                                               *)
(* ------------------------------------------------------------------------- *)

fun add_ineq (i1 as Lineq(k1,ty1,l1,just1)) (i2 as Lineq(k2,ty2,l2,just2)) =
  let
    val l = map2 (curry op+) l1 l2
  in
    Lineq(k1+k2,find_add_type(ty1,ty2),l,Added(just1,just2))
  end

(* ------------------------------------------------------------------------- *)
(* Multiply out an (in)equation.                                             *)
(* ------------------------------------------------------------------------- *)

fun multiply_ineq n (i as Lineq(k,ty,l,just)) =
  if n = one then i
  else if n = zero andalso ty = Lt then failwith "multiply_ineq"
  else if n < zero andalso (ty = Le orelse ty = Lt) then
    failwith "multiply_ineq"
  else Lineq(n * k,ty,map ((curry op* ) n) l,Multiplied(n,just))

(* ------------------------------------------------------------------------- *)
(* Elimination of variable between a single pair of (in)equations.           *)
(* If they're both inequalities, 1st coefficient must be +ve, 2nd -ve.       *)
(* ------------------------------------------------------------------------- *)

fun elim_var v (i1 as Lineq(k1,ty1,l1,just1)) (i2 as Lineq(k2,ty2,l2,just2)) =
  let
    val c1 = el0 v l1
    val c2 = el0 v l2
    val m = Arbint.lcm (abs c1, abs c2)
    val m1 = m div (abs c1)
    val m2 = m div (abs c2)
    val (n1,n2) =
      if sgn(c1) = sgn(c2)
      then if ty1 = Eq
           then (~m1,m2)
           else if ty2 = Eq
                then (m1,~m2)
                else failwith "elim_var"
      else (m1,m2)
    val (p1,p2) =
      if ty1 = Eq andalso ty2 = Eq andalso (n1 = ~one orelse n2 = ~one)
      then (~n1,~n2)
      else (n1,n2)
  in
    add_ineq (multiply_ineq n1 i1) (multiply_ineq n2 i2)
  end

(* ------------------------------------------------------------------------- *)
(* Main elimination code:                                                    *)
(*                                                                           *)
(* (1) Looks for immediate solutions (false assertions with no variables).   *)
(*                                                                           *)
(* (2) If there are any equations, picks a variable with the lowest absolute *)
(* coefficient in any of them, and uses it to eliminate.                     *)
(*                                                                           *)
(* (3) Otherwise, chooses a variable in the inequality to minimize the       *)
(* blowup (number of consequences generated) and eliminates it.              *)
(* ------------------------------------------------------------------------- *)

fun elim ineqs =
  let
    val _ = trace ("elim: #(ineqs) = " ^ (Int.toString (length ineqs)) ^ ".")
    val (triv,nontriv) = partition is_trivial ineqs
    val res =
      if not (null triv) then tryfind find_answer triv
                              handle HOL_ERR _ => elim nontriv
      else
        if null nontriv then failwith "elim" else
          let
            val (eqs,noneqs) = partition (fn (Lineq(_,ty,_,_)) => ty = Eq)
                                         nontriv
          in
            if not (null eqs) then
              let
                val clists = map (fn (Lineq(_,_,l,_)) => l) eqs
                val sclist = sort (fn x => fn y => abs(x) <= abs(y))
                  (filter ((curry op<>) zero) (Union clists))
                val _ = trace ("elim: #(sclist) = "
                               ^ (Int.toString (length sclist)) ^ ".")
                val c = hd sclist
                val (v,eq) = tryfind
                              (fn (i as Lineq(_,_,l,_)) => (index c l,i)) eqs
                val othereqs = filter (not o ((curry lineq_eq) eq)) eqs
                val (ioth,roth) =
                        partition (fn (Lineq(_,_,l,_)) => el0 v l = zero)
                                  (othereqs @ noneqs)
                val others = map (elim_var v eq) roth @ ioth
              in
                elim others
              end
            else
              let
                val lists = map (fn (Lineq(_,_,l,_)) => l) noneqs
                val _ = trace ("elim: #(lists) = "
                               ^ (Int.toString (length lists)) ^ ".")
                val numlist = upto (fromInt (length(hd lists)) - one)
                val coeffs = map (fn i => map (el0 i) lists) numlist
                val blows = map calc_blowup coeffs
                val iblows = zip blows numlist
                val _ = trace ("elim: #(iblows) = "
                               ^ (Int.toString (length iblows)) ^ ".")
                val iblows' = filter ((curry op<>) zero o fst) iblows
                val _ = trace ("elim: #(iblows') = "
                               ^ (Int.toString (length iblows')) ^ ".")
                val (c,v) = Lib.trye hd
                             (sort (fn x => fn y => fst(x) <= fst(y)) iblows')
                val (no,yes) = partition
                                 (fn (Lineq(_,_,l,_)) => el0 v l = zero) ineqs
                val (pos,neg) = partition
                                  (fn (Lineq(_,_,l,_)) => el0 v l > zero) yes
              in
                elim (no @ op_allpairs (curry lineq_eq) (elim_var v) pos neg)
              end
          end
    val _ = trace "done elim"
  in
    res
  end


(* ------------------------------------------------------------------------- *)
(* Multiply standard linear list by a constant.                              *)
(* ------------------------------------------------------------------------- *)

local
  val mult_tm = realSyntax.mult_tm
  val zero_tm = realSyntax.zero_tm
  val x_tm = ``x:real``
  val add_tm = realSyntax.plus_tm
  val conv1 = GEN_REWRITE_CONV TOP_SWEEP_CONV [REAL_ADD_LDISTRIB]
  val conv2 = liteLib.DEPTH_BINOP_CONV add_tm
                (REWR_CONV REAL_MUL_ASSOC THENC LAND_CONV REAL_INT_MUL_CONV)
in
  fun LINEAR_MULT n tm =
    if tm ~~ zero_tm then INST [x_tm |-> n] LINEAR_MULT_pth else
      let
        val ltm = mk_comb(mk_comb(mult_tm,n),tm)
      in
        (conv1 THENC conv2) ltm
      end
end

(* ------------------------------------------------------------------------- *)
(* Translate back a proof.                                                   *)
(* ------------------------------------------------------------------------- *)

local
  val TRIVIAL_CONV = DEPTH_CONV
    (CHANGED_CONV REAL_INT_NEG_CONV ORELSEC
    REAL_INT_ADD_CONV ORELSEC
    REAL_INT_MUL_CONV ORELSEC
    REAL_INT_LE_CONV ORELSEC
    REAL_INT_EQ_CONV ORELSEC
    REAL_INT_LT_CONV) THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV (implicit_rewrites())

  local
    val a_tm = ``a:real``
    val b_tm = ``b:real``
    val pths = CONJUNCTS ADD_INEQS_pth
  in
    fun ADD_INEQS th1 th2 =
      let
        val a = rand(concl th1)
        val b = rand(concl th2)
        val xth = tryfind
                    (C MP (CONJ th1 th2) o INST [a_tm |-> a, b_tm |-> b]) pths
        val yth = LINEAR_ADD a b
      in
        EQ_MP (AP_TERM (rator(concl xth)) yth) xth
      end
  end

  local
    val pths = CONJUNCTS MULTIPLY_INEQS_pth
    val x_tm = ``x:real``
    val y_tm = ``y:real``
  in
    fun MULTIPLY_INEQS x th =
      let
        val y = rand(concl th)
        val xth = tryfind (C MP th o INST [x_tm |-> x, y_tm |-> y]) pths
        val wth = if is_imp(concl xth) then
          MP (CONV_RULE(LAND_CONV TRIVIAL_CONV) xth) TRUTH else xth
        val yth = LINEAR_MULT x (rand(rand(concl wth)))
      in
        EQ_MP (AP_TERM (rator(concl wth)) yth) wth
      end
  end

in
  fun TRANSLATE_PROOF refutation =
    let
      val _ = trace "TRANSLATE_PROOF"
      val cache = Uref.new []
      open Uref
      fun translate refut =
        (op_assoc (curry injust_eq) refut (!cache))
        handle HOL_ERR _
        => case refut
            of Given(th) => (cache:= (refut,th)::(!cache); th)
             | Added(r1,r2) =>
                let
                  val th1 = translate r1
                  val _ = trace_thm th1
                  val th2 = translate r2
                  val _ = trace_thm th2
                  val th = ADD_INEQS th1 th2
                  val _ = trace_thm th
                in
                 (cache:= (refut,th)::(!cache); th)
                end
             | Multiplied(n,r) =>
                let
                  val th1 = translate r
                  val th = MULTIPLY_INEQS (mk_intconst n) th1
                in
                  (cache:= (refut,th)::(!cache); th)
                end
      val res = CONV_RULE TRIVIAL_CONV (translate refutation)
      val _ = trace "done TRANSLATE_PROOF"
    in
      res
    end
end

(* ------------------------------------------------------------------------- *)
(* Refute a conjunction of equations and/or inequations.                     *)
(* ------------------------------------------------------------------------- *)

local
  val add_tm = realSyntax.plus_tm
  val one_tm = realSyntax.one_tm
  val zero_tm = realSyntax.zero_tm
  val false_tm = boolSyntax.F
  val eq_tm = realSyntax.real_eq_tm
  val le_tm = realSyntax.leq_tm
  val lt_tm = realSyntax.less_tm
  fun fixup_atom th =
    let
      val _ = trace "fixup_atom"
      val _ = trace_term (snd (dest_thm th))
      val th0 = CONV_RULE REAL_ATOM_NORM_CONV th
      val _ = trace_thm th0
      val tm0 = concl th0
    in
      if rand tm0 ~~ zero_tm then
        if rator(rator tm0) ~~ lt_tm then
          EQ_MP REAL_SIMPLE_ARITH_REFUTER_trivthm th0
        else failwith "trivially true, so useless in refutation"
      else th0
    end
in
  fun REAL_SIMPLE_ARITH_REFUTER ths0 =
    let
      val _ = trace "REAL_SIMPLE_ARITH_REFUTER"
      val _ = trace ("#(ths0) = " ^ (Int.toString (length ths0)) ^ ".")
      val _ = trace_thm_list ths0
      val ths = mapfilter fixup_atom ths0
      val _ = trace ("#(ths) = " ^ (Int.toString (length ths)) ^ ".")
      val _ = trace_thm_list ths
      val res =
      first (fn th => Feq (concl th)) ths
      handle HOL_ERR _ =>
        let
          val allvars = itlist
            (op_union aconv o map rand o liteLib.binops add_tm o
              rand o concl) ths []
          val vars =
            if tmem one_tm allvars then
              one_tm::op_set_diff aconv allvars [one_tm]
            else one_tm::allvars
          fun unthmify th =
            let
              val t = concl th
              val op_alt = rator(rator t)
              val right = rand t
              val rights = liteLib.binops add_tm right
              val cvps = map (((dest_intconst o rand)
                                F_F (C index_ac vars)) o dest_comb) rights
              val k = ~((rev_assoc zero cvps)
                              handle HOL_ERR _ => zero)
              val l = Lib.trye tl (map (fn v => ((rev_assoc v cvps)
                                                  handle HOL_ERR _ => zero))
                                  (upto (fromInt (length(vars)) - one)))
              val ty = if op_alt ~~ eq_tm then Eq
                        else if op_alt ~~ le_tm then Le
                        else if op_alt ~~ lt_tm then Lt
                        else failwith "unknown op"
            in
              Lineq(k,ty,l,Given th)
            end
          val ineqs = map unthmify ths
          val _ = trace ("#(ineqs) = " ^ (Int.toString (length ineqs)) ^ ".")
          val (Lineq(_,_,_,proof)) = elim ineqs
        in
          TRANSLATE_PROOF proof
        end
      val _ = trace_thm res
      val _ = trace "done REAL_SIMPLE_ARITH_REFUTER"
    in
      res
    end
end

(* ------------------------------------------------------------------------- *)
(* General case: canonicalize and split up, then refute the bits.            *)
(* ------------------------------------------------------------------------- *)

local
  local
    val zero_tm = ``&0 :real``
    val raw_CONV = GEN_REWRITE_CONV I [ZERO_LEFT_CONV_pth] THENC
      GEN_REWRITE_CONV TOP_SWEEP_CONV
      [REAL_ADD_LID', REAL_NEG_ADD, REAL_NEG_NEG]
  in
    fun ZERO_LEFT_CONV tm =
      if liteLib.lhand tm ~~ zero_tm then REFL tm else raw_CONV tm
  end

  val init_CONV = GEN_REWRITE_CONV TOP_DEPTH_CONV [
      FORALL_SIMP, EXISTS_SIMP,
      real_gt, real_ge, real_sub,
      REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB,
      REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG, REAL_NEG_ADD,
      REAL_MUL_LZERO, REAL_MUL_RZERO,
      REAL_MUL_LID', REAL_MUL_RID,
      REAL_ADD_LID', REAL_ADD_RID] THENC
      REPEATC (CHANGED_CONV Sub_and_cond.COND_ELIM_CONV) THENC PRENEX_CONV
  val eq_tm = realSyntax.real_eq_tm
  val le_tm = realSyntax.leq_tm
  val lt_tm = realSyntax.less_tm
  local
    val plus_tm = realSyntax.plus_tm
    val abs_tm = realSyntax.absval_tm
    val neg_tm = realSyntax.negate_tm
    val strip_plus = liteLib.binops plus_tm
    val list_mk_plus = list_mk_binop plus_tm
    fun is_abstm tm = is_comb tm andalso rator tm ~~ abs_tm
    fun is_negtm tm = is_comb tm andalso rator tm ~~ neg_tm
    fun is_negabstm tm = is_negtm tm andalso is_abstm(rand tm)
    val ABS_ELIM_RULE = GEN_REWRITE_RULE I [ABS_ELIM_THM]
    val NEG_DISTRIB_RULE =
                  GEN_REWRITE_RULE (RAND_CONV o TOP_SWEEP_CONV)
                  [REAL_NEG_ADD, REAL_NEG_NEG]
    val REDISTRIB_RULE = CONV_RULE init_CONV
    val x_tm = ``x:real``
  in
    fun ABS_ELIM_TAC1 th =
      let
        val (tmx,tm0) = dest_comb(concl th)
        val op_alt = rator tmx
      in
        (trace "ABS_ELIM_TAC1";
        if op_alt !~ le_tm andalso op_alt !~ lt_tm
        then failwith "ABS_ELIM_TAC1" else
          let
            val tms = strip_plus tm0
            val tm = first is_negabstm tms
            val n = index_ac tm tms
            val (ltms,rtms) = chop_list n tms
            val ntms = tm::(ltms @ tl rtms)
            val th1 = AP_TERM tmx
              (REAL_ADD_AC (mk_eq(tm0, list_mk_plus ntms)))
            val th2 = ABS_ELIM_RULE (EQ_MP th1 th)
          in
            CONJUNCTS_THEN ASSUME_TAC (NEG_DISTRIB_RULE th2)
          end)
      end
    fun ABS_ELIM_TAC2 th =
      let
        val (tmx,tm0) = dest_comb(concl th)
        val op_alt = rator tmx
      in
        (trace "ABS_ELIM_TAC2";
        if op_alt !~ le_tm andalso op_alt !~ lt_tm
        then failwith "ABS_ELIM_TAC1"
        else
          let
            val tms = strip_plus tm0
            val tm = first is_abstm tms
          in
            DISJ_CASES_THEN2
            (fn th => RULE_ASSUM_TAC (SUBS [th]))
            (fn th => RULE_ASSUM_TAC (NEG_DISTRIB_RULE o SUBS [th]))
            (INST [x_tm |-> rand tm] ABS_CASES_THM)
          end)
      end
    fun ABS_ELIM_TAC3 th =
      let
        val tm = find_term is_abstm (concl th)
      in
        (trace "ABS_ELIM_TAC2";
        DISJ_CASES_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (fn th => RULE_ASSUM_TAC (SUBS [th])))
        (CONJUNCTS_THEN2 (ASSUME_TAC o REDISTRIB_RULE)
        (fn th => RULE_ASSUM_TAC (REDISTRIB_RULE o SUBS [th])))
        (INST [x_tm |-> rand tm] ABS_STRONG_CASES_THM))
      end
  end
  val atom_CONV = GEN_REWRITE_CONV I [atom_CONV_pth]
  fun DISCARD_UNREAL_TAC th =
    let
      val tm = concl th
    in
      if is_comb tm andalso
        let
          val tm' = rator tm
        in
          is_comb tm' andalso
          let
            val tm'' = rator tm'
          in
            tm'' ~~ eq_tm orelse tm'' ~~ le_tm orelse tm'' ~~ lt_tm
          end
        end
      then failwith "DISCARD_UNREAL_TAC"
      else
        ALL_TAC
    end
in
  fun PURE_REAL_ARITH_TAC g =
    let
      val _ = trace "PURE_REAL_ARITH_TAC"
      val tac =
        REPEAT GEN_TAC THEN
        CONV_TAC init_CONV THEN
        REPEAT GEN_TAC THEN
        REFUTE_THEN(MP_TAC o
                    CONV_RULE
                      (PRESIMP_CONV THENC NNF_CONV THENC SKOLEM_CONV THENC
                        PRENEX_CONV THENC ONCE_DEPTH_CONV atom_CONV THENC
                        PROP_DNF_CONV)) THEN
        DISCH_THEN(REPEAT_TCL
                      (CHOOSE_THEN ORELSE_TCL DISJ_CASES_THEN ORELSE_TCL
                      CONJUNCTS_THEN)
                      ASSUME_TAC) THEN
        TRY(FIRST_ASSUM CONTR_TAC) THEN
        REPEAT(FIRST_X_ASSUM DISCARD_UNREAL_TAC) THEN
        RULE_ASSUM_TAC(CONV_RULE ZERO_LEFT_CONV) THEN
        REPEAT(FIRST_X_ASSUM ABS_ELIM_TAC1 ORELSE
                FIRST_ASSUM ABS_ELIM_TAC2 ORELSE
                FIRST_ASSUM ABS_ELIM_TAC3) THEN
        POP_ASSUM_LIST(ACCEPT_TAC o REAL_SIMPLE_ARITH_REFUTER)
      val res = tac g
      val _ = trace "done PURE_REAL_ARITH_TAC"
    in
      res
    end
end

(* renamed with OLD_ prefixes *)
fun OLD_REAL_ARITH_TAC g =
  let
    val _ = trace "REAL_ARITH_TAC"
    val res = (POP_ASSUM_LIST(K ALL_TAC) THEN PURE_REAL_ARITH_TAC) g
    val _ = trace "done REAL_ARITH_TAC"
  in
    res
  end

fun OLD_REAL_ASM_ARITH_TAC g =
  let
    val _ = trace "REAL_ASM_ARITH_TAC"
    val res = (REPEAT (POP_ASSUM MP_TAC) THEN PURE_REAL_ARITH_TAC) g
    val _ = trace "done REAL_ASM_ARITH_TAC"
  in
    res
  end

(* ------------------------------------------------------------------------- *)
(* Rule version.                                                             *)
(* ------------------------------------------------------------------------- *)

fun OLD_REAL_ARITH tm =
  let
    val _ = trace "REAL_ARITH"
    val res = Tactical.default_prover (tm,OLD_REAL_ARITH_TAC)
    val _ = trace "done REAL_ARITH"
  in
    res
  end

(* ------------------------------------------------------------------------- *)
(* Slightly less parametrized GEN_REAL_ARITH with more intelligent           *)
(* elimination of abs, max and min hardwired in.                             *)
(* ------------------------------------------------------------------------- *)

(* In the code below we fallback to the default Int (instead of Arbint) lib. *)
open Int realSyntax Rewrite

val ABSMAXMIN_ELIM_CONV1 =
  GEN_REWRITE_CONV I empty_rewrites [ABSMAXMIN_ELIM_CONV1_pth]

local
  val abs_tm = absval_tm
  and p_tm = “P:real->bool”
  and x_tm = “x:real”
  and y_tm = “y:real”
  and is_abs = is_absval
  fun eliminate_construct (p :term -> bool) (c :term -> term -> thm) tm = let
    val t = find_term (fn t => p t andalso free_in t tm) tm
    val v = genvar(type_of t)
    val th0 = SYM(BETA_CONV(mk_comb(mk_abs(v,subst[t |-> v] tm),t)))
    val (p,ax) = dest_comb(rand(concl th0))
  in
    CONV_RULE(RAND_CONV(BINOP_CONV(RAND_CONV BETA_CONV)))
              (TRANS th0 (c p ax))
  end
  val elim_abs =
    eliminate_construct is_abs (fn p => fn ax =>
      INST [p_tm |-> p, x_tm |-> rand ax] ABSMAXMIN_ELIM_CONV2_pth_abs)
  and elim_max =
    eliminate_construct is_max (fn p => fn ax => let
      val (ax,y) = dest_comb ax
      in
        INST [p_tm |-> p, x_tm |-> rand ax, y_tm |-> y]
          ABSMAXMIN_ELIM_CONV2_pth_max
      end)
  and elim_min =
    eliminate_construct is_min (fn p => fn ax => let
      val (ax,y) = dest_comb ax
      in
        INST [p_tm |-> p, x_tm |-> rand ax, y_tm |-> y]
          ABSMAXMIN_ELIM_CONV2_pth_min
      end)
in
  val ABSMAXMIN_ELIM_CONV2 = FIRST_CONV [elim_abs, elim_max, elim_min]
end

(* exported function *)
fun GEN_REAL_ARITH (mkconst,EQ,GE,GT,NORM,NEG,ADD,MUL,PROVER) =
    GEN_REAL_ARITH0 (mkconst,EQ,GE,GT,NORM,NEG,ADD,MUL,
                     ABSMAXMIN_ELIM_CONV1,ABSMAXMIN_ELIM_CONV2,PROVER)

(* ------------------------------------------------------------------------- *)
(* Incorporate that. This gets overwritten again in RealField.sml.           *)
(* ------------------------------------------------------------------------- *)

local
  val (REAL_POLY_NEG_CONV,REAL_POLY_ADD_CONV,REAL_POLY_SUB_CONV,
       REAL_POLY_MUL_CONV,REAL_POLY_POW_CONV,REAL_POLY_CONV) =
    SEMIRING_NORMALIZERS_CONV REAL_POLY_CLAUSES REAL_POLY_NEG_CLAUSES
     (is_realintconst,
      REAL_INT_ADD_CONV,REAL_INT_MUL_CONV,REAL_INT_POW_CONV) term_lt
in
  val REAL_ARITH = GEN_REAL_ARITH
    (term_of_rat,
      REAL_INT_EQ_CONV,REAL_INT_GE_CONV,REAL_INT_GT_CONV,
      REAL_POLY_CONV,REAL_POLY_NEG_CONV,REAL_POLY_ADD_CONV,REAL_POLY_MUL_CONV,
      REAL_LINEAR_PROVER)
end

(* This function converts REAL_ARITH (a prover) to the corresponding tactics *)
fun mk_real_arith_tac (prover :term -> thm) :tactic * tactic = let
  val arith_tac = CONV_TAC (EQT_INTRO o prover)
  val asm_arith_tac =
      REPEAT(FIRST_X_ASSUM
              (fn th => if not(is_forall (concl th)) then MP_TAC th
                        else ALL_TAC)) THEN arith_tac
in
    (arith_tac, asm_arith_tac)
end

val (REAL_ARITH_TAC,REAL_ASM_ARITH_TAC) = mk_real_arith_tac REAL_ARITH

end; (* structure *)

(* References:

   [1] Bochnak, J., Coste, M., Roy, M.-F.: Real Algebraic Geometry. Springer
       Science & Business Media (2013). DOI: 10.1007/978-3-662-03718-8
 *)
