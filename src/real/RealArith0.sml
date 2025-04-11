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

structure RealArith0 :> RealArith0 =
struct

open HolKernel Parse boolLib liteLib

open reduceLib Ho_Rewrite numSyntax Canon_Port

open normalForms  (* for HOL-Light's GEN_NNF_CONV, etc. *)

open realaxTheory (* NOTE: cannot open realTheory here *)
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
val is_binop    = liteLib.is_binop
val SKOLEM_CONV = Canon_Port.SKOLEM_CONV

(* ------------------------------------------------------------------------- *)
(* Functions to be compatible with hol-light.                                *)
(* ------------------------------------------------------------------------- *)

fun failwith s = raise mk_HOL_ERR "RealArith" "?" s

fun term_lt u t = (Term.compare(u,t) = LESS)

fun el0 n l = if n <= zero then hd l
              else el0 (n - one) (tl l) handle _ => raise Fail "RealArith.el0"

val NUM_EQ_CONV = NEQ_CONV
val NUM_LE_CONV = LE_CONV
val NUM_LT_CONV = LT_CONV
val NUM_ADD_CONV = ADD_CONV

(* ------------------------------------------------------------------------- *)
(* Functions dealing with numbers (numerals) in theorems.                    *)
(* ------------------------------------------------------------------------- *)

val mk_numeral = numSyntax.mk_numeral o Arbint.toNat
val dest_numeral = Arbint.fromNat o numSyntax.dest_numeral

(* true for all nonnegative real literrals *)

local
  val amp = realSyntax.real_injection
in
  fun is_numconst tm =
    let
      val (l,r) = dest_comb tm
    in
      l ~~ amp andalso is_numeral r
    end
    handle HOL_ERR _ => false
end

(* NOTE: realSyntax.is_real_literal cannot be used here, as it's too smart to
         automatically remove (multiple) leading negations

   Also, “~0” is true here.
 *)
local
  val dsub = realSyntax.negate_tm
in
  fun is_intconst tm =
    is_numconst tm orelse
    let
      val (l,r) = dest_comb tm
    in
      l ~~ dsub andalso is_numconst r
    end
    handle HOL_ERR _ => false
end

val mk_intconst = realSyntax.term_of_int
val dest_intconst = realSyntax.int_of_term

(* ------------------------------------------------------------------------- *)
(* First all the comparison operators.                                       *)
(* ------------------------------------------------------------------------- *)

local
  val NUM2_EQ_CONV =
    BINOP_CONV NUM_EQ_CONV THENC GEN_REWRITE_CONV I [REAL_INT_LE_CONV_tth]
  val NUM2_NE_CONV =
    RAND_CONV NUM2_EQ_CONV THENC GEN_REWRITE_CONV I [REAL_INT_LE_CONV_nth]
  val [pth_le1, pth_le2a, pth_le2b, pth_le3] = CONJUNCTS REAL_INT_LE_CONV_pth
  val [pth_lt1, pth_lt2a, pth_lt2b, pth_lt3] = CONJUNCTS REAL_INT_LT_CONV_pth
  val [pth_ge1, pth_ge2a, pth_ge2b, pth_ge3] = CONJUNCTS REAL_INT_GE_CONV_pth
  val [pth_gt1, pth_gt2a, pth_gt2b, pth_gt3] = CONJUNCTS REAL_INT_GT_CONV_pth
  val [pth_eq1a, pth_eq1b, pth_eq2a, pth_eq2b] = CONJUNCTS REAL_INT_EQ_CONV_pth
in
  val REAL_INT_LE_CONV = FIRST_CONV [
    GEN_REWRITE_CONV I [pth_le1],
    GEN_REWRITE_CONV I [pth_le2a, pth_le2b] THENC NUM_LE_CONV,
    GEN_REWRITE_CONV I [pth_le3] THENC NUM2_EQ_CONV]
  val REAL_INT_LT_CONV = FIRST_CONV [
    GEN_REWRITE_CONV I [pth_lt1],
    GEN_REWRITE_CONV I [pth_lt2a, pth_lt2b] THENC NUM_LT_CONV,
    GEN_REWRITE_CONV I [pth_lt3] THENC NUM2_NE_CONV]
  val REAL_INT_GE_CONV = FIRST_CONV [
    GEN_REWRITE_CONV I [pth_ge1],
    GEN_REWRITE_CONV I [pth_ge2a, pth_ge2b] THENC NUM_LE_CONV,
    GEN_REWRITE_CONV I [pth_ge3] THENC NUM2_EQ_CONV]
  val REAL_INT_GT_CONV = FIRST_CONV [
    GEN_REWRITE_CONV I [pth_gt1],
    GEN_REWRITE_CONV I [pth_gt2a, pth_gt2b] THENC NUM_LT_CONV,
    GEN_REWRITE_CONV I [pth_gt3] THENC NUM2_NE_CONV]
  val REAL_INT_EQ_CONV = FIRST_CONV [
    GEN_REWRITE_CONV I [pth_eq1a, pth_eq1b] THENC NEQ_CONV,
    GEN_REWRITE_CONV I [pth_eq2a, pth_eq2b] THENC NUM2_EQ_CONV]
end

(* ------------------------------------------------------------------------- *)
(* Negation & multiplication.                                                *)
(* ------------------------------------------------------------------------- *)

val REAL_INT_NEG_CONV = GEN_REWRITE_CONV I [REAL_INT_NEG_CONV_pth]

local
  val (pth1,pth2) = CONJ_PAIR REAL_INT_MUL_CONV_pth1
in
  val REAL_INT_MUL_CONV = FIRST_CONV [
    GEN_REWRITE_CONV I [REAL_INT_MUL_CONV_pth0],
    GEN_REWRITE_CONV I [pth1] THENC RAND_CONV MUL_CONV,
    GEN_REWRITE_CONV I [pth2] THENC RAND_CONV(RAND_CONV MUL_CONV)]
end

(* ------------------------------------------------------------------------- *)
(* Addition and subtraction.                                                 *)
(* ------------------------------------------------------------------------- *)

local
  val neg_tm = realSyntax.negate_tm
  val amp_tm = realSyntax.real_injection
  val add_tm = realSyntax.plus_tm
  val dest = liteLib.dest_binop add_tm
  val m_tm = ``m:num`` and n_tm = ``n:num``
  val [pth1, pth2, pth3, pth4, pth5, pth6] = CONJUNCTS REAL_INT_ADD_CONV_pth1
in
  val REAL_INT_ADD_CONV =
    GEN_REWRITE_CONV I [REAL_INT_ADD_CONV_pth0] ORELSEC
    (fn tm =>
      let
        val (l,r) = dest tm
      in
        if rator l ~~ neg_tm then
          if rator r ~~ neg_tm then
            let
              val th1 = INST [m_tm |-> rand(rand l), n_tm |-> rand(rand r)] pth1
              val tm1 = rand(rand(rand(concl th1)))
              val th2 = AP_TERM neg_tm (AP_TERM amp_tm (NUM_ADD_CONV tm1))
            in
              TRANS th1 th2
            end
          else
            let
              val m = rand(rand l)
              val n = rand r
              val m' = dest_numeral m
              val n' = dest_numeral n
            in
              if m' <= n' then
                let
                  val p = mk_numeral (n' - m')
                  val th1 = INST [m_tm |-> m, n_tm |-> p] pth2
                  val th2 = NUM_ADD_CONV (rand(rand(liteLib.lhand(concl th1))))
                  val th3 = AP_TERM (rator tm) (AP_TERM amp_tm (SYM th2))
                in
                  TRANS th3 th1
                end
              else
                let
                  val p = mk_numeral (m' - n')
                  val th1 = INST [m_tm |-> n, n_tm |-> p] pth3
                  val th2 = NUM_ADD_CONV
                              (rand(rand(liteLib.lhand
                                   (liteLib.lhand(concl th1)))))
                  val th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2))
                  val th4 = AP_THM (AP_TERM add_tm th3) (rand tm)
                in
                  TRANS th4 th1
                end
            end
        else
          if rator r ~~ neg_tm then
            let
              val m = rand l and n = rand(rand r)
              val m' = dest_numeral m and n' = dest_numeral n
            in
              if n' <= m' then
                let
                  val p = mk_numeral (m' - n')
                  val th1 = INST [m_tm |-> n, n_tm |-> p] pth4
                  val th2 = NUM_ADD_CONV (rand(liteLib.lhand(liteLib.lhand(concl th1))))
                  val th3 = AP_TERM add_tm (AP_TERM amp_tm (SYM th2))
                  val th4 = AP_THM th3 (rand tm)
                in
                  TRANS th4 th1
                end
              else
                let
                  val p = mk_numeral (n' - m')
                  val th1 = INST [m_tm |-> m, n_tm |-> p] pth5
                  val th2 = NUM_ADD_CONV (rand(rand(rand(liteLib.lhand(concl th1)))))
                  val th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2))
                  val th4 = AP_TERM (rator tm) th3
                in
                  TRANS th4 th1
                end
            end
          else
            let
              val th1 = INST [m_tm |-> rand l, n_tm |-> rand r] pth6
              val tm1 = rand(rand(concl th1))
              val th2 = AP_TERM amp_tm (NUM_ADD_CONV tm1)
            in
              TRANS th1 th2
            end
      end
      handle HOL_ERR _ => failwith "REAL_INT_ADD_CONV")
end

val REAL_INT_SUB_CONV =
  GEN_REWRITE_CONV I [real_sub] THENC
  TRY_CONV(RAND_CONV REAL_INT_NEG_CONV) THENC
  REAL_INT_ADD_CONV

(* ------------------------------------------------------------------------- *)
(* pow                                                                       *)
(* ------------------------------------------------------------------------- *)

val NUM_EXP_CONV = EXP_CONV
val NUM_EVEN_CONV = EVEN_CONV

local
  val neg_tm = realSyntax.negate_tm
  val (pth1,pth2) = CONJ_PAIR REAL_INT_POW_CONV_pth1
in
  val REAL_INT_POW_CONV =
    (GEN_REWRITE_CONV I [pth1] THENC RAND_CONV NUM_EXP_CONV) ORELSEC
    (TRY_CONV(GEN_REWRITE_CONV I [pth2]) THENC
    RATOR_CONV(RATOR_CONV(RAND_CONV NUM_EVEN_CONV)) THENC
    TRY_CONV(GEN_REWRITE_CONV I [REAL_INT_POW_CONV_tth]) THENC
    (fn tm => if rator tm ~~ neg_tm then RAND_CONV(RAND_CONV NUM_EXP_CONV) tm
              else RAND_CONV NUM_EXP_CONV tm))
end

(* ========================================================================= *)
(* Framework for universal real decision procedures, and a simple instance.  *)
(* ========================================================================= *)

(* In the code below we fallback to the default Int (instead of Arbint) lib. *)
open Int realSyntax Rewrite

(* This overrides normalForms.NNF_CONV with the HOL-Light compatible version *)
val NNF_CONV = normalForms.NNFD_CONV

val chatting = ref (if !Globals.interactive then true else false)
val verbose_level = ref 1

fun print_verbose (message,default) =
  if !chatting andalso !verbose_level > 1 then print message
  else if !chatting andalso !verbose_level = 1 then say default
  else ()

type aint = Arbint.int
type rat  = Arbrat.rat
type dconv = term -> thm * thm (* for GEN_NNF_CONV *)

(* ------------------------------------------------------------------------- *)
(* A cacher for conversions (from HOL-Light's equal.ml)                      *)
(* ------------------------------------------------------------------------- *)

local
  fun ALPHA_HACK th = let
    val tm' = lhand(concl th)
  in
    fn tm => if tm' ~~ tm then th else TRANS (ALPHA tm tm') th
  end
in
  fun CACHE_CONV conv = let
    val net = ref Net.empty
  in
    fn tm => (tryfind (fn f => f tm) (Net.match tm (!net)))
             handle HOL_ERR _ => let
                 val th = conv tm
             in
                 (net := Net.insert (tm,ALPHA_HACK th) (!net); th)
             end
  end
end

(* ------------------------------------------------------------------------- *)
(* Data structure for Positivstellensatz refutations.                        *)
(* ------------------------------------------------------------------------- *)

(* NOTE: see [1] for a related theorem named "positivstellensatz". *)
datatype positivstellensatz =
    Axiom_eq of int
  | Axiom_le of int
  | Axiom_lt of int
  | Rational_eq of rat
  | Rational_le of rat
  | Rational_lt of rat
  | Square of term
  | Eqmul of term * positivstellensatz
  | Sum of positivstellensatz * positivstellensatz
  | Product of positivstellensatz * positivstellensatz

(* for debugging only *)
fun dest_positivstellensatz (Sum(p1,p2))     = (p1,p2)
  | dest_positivstellensatz (Product(p1,p2)) = (p1,p2)
  | dest_positivstellensatz _ = failwith "invalid positivstellensatz"

(* NOTE: “~&0” is not considered a real integer constant here *)
fun is_realintconst tm =
    if tm ~~ “~&0” then false else is_intconst tm

val dest_realintconst = dest_intconst
val mk_realintconst   = mk_intconst

(* Some test cases:
   is_ratconst “&2 / &3” = true;
   is_ratconst “~&2 / &4” = false;
   is_ratconst “~&1 / &2” = true;
   is_ratconst “&2 / &4” = false;
   is_ratconst “&0 / &4” = false;
   is_ratconst “(&4 :real)” = true;
   is_ratconst “(&0 :real)” = true;
   is_ratconst “~&0 :real” = false;
   is_ratconst “~&3 :real” = true;
   is_ratconst “~&0 / &3” = false;
 *)
fun is_ratconst tm =
  if is_div tm then let
    val (p,q) = dest_div tm
    in
      is_realintconst p andalso is_realintconst q andalso (let
        val m = dest_realintconst p and n = dest_realintconst q
        in Arbint.> (n,one) andalso Arbint.gcd (m, n) = one end)
    end
  else
    is_realintconst tm

fun rat_of_term tm =
  if is_div tm then let
    val (p,q) = dest_div tm
    in
      if is_realintconst p andalso is_realintconst q then let
        val m = dest_realintconst p and n = dest_realintconst q
        in
          if Arbint.>(n,one) andalso Arbint.gcd (m, n) = one then
            Arbrat./ (Arbrat.fromAInt m,Arbrat.fromAInt n)
          else failwith "rat_of_term"
        end
      else failwith "rat_of_term"
    end
  else Arbrat.fromAInt (dest_realintconst tm)

(* e.g. term_of_rat (Arbrat.fromAInt two) ~~ “&2” *)
fun term_of_rat x = let
  val p = Arbrat.numerator x and q = Arbrat.denominator x
  val ptm = mk_realintconst p
in
  if q = Arbnum.one then ptm
  else mk_div(ptm,mk_realintconst (fromNat q))
end

(* ------------------------------------------------------------------------- *)
(* Linear prover. This works over the rationals in general, but is designed  *)
(* to be OK on integers provided the input contains only integers.           *)
(* ------------------------------------------------------------------------- *)

(* A "linear expression" as a summation of constant-multiplied variables of
   the form “a * x + b * y + c”, represented by a finite map from terms to
   rationals such as [x |=> a, y |=> b, 1 |=> c].
 *)
local open HOLdict Arbrat in
type linear_type = (term,rat)dict

val is_undefined :linear_type -> bool = isEmpty
val undefined :linear_type = mkDict Term.compare
fun is_single (m :linear_type) = (numItems m = 1)
fun defined (m :linear_type) (k :term) = inDomain (m,k)
fun dom (m :linear_type) :term list = listKeys m

fun tryapply (m :linear_type) k d = find (m,k) handle NotFound => d
fun apply (m :linear_type) k = tryapply m k zero

infix |=>
fun (k :term) |=> (v :rat) :linear_type = singleton Term.compare (k,v)

fun undefine (k :term) (m :linear_type) :linear_type =
    (fst(remove(m,k))) handle NotFound => m

fun choose (m :linear_type) =
    case firsti m of
       SOME kx => kx
     | NONE    => failwith "empty dict"

val listItems = listItems
val mapWith = transform

fun mergeWithoutZero f (m1 :linear_type) (m2 :linear_type) :linear_type =
let
    fun add (SOME x, SOME y) = let val z = Arbrat.+ (x,y) in
                                   if z = Arbrat.zero then NONE
                                   else SOME z
                               end
      | add (SOME x, NONE  ) = SOME x
      | add (NONE,   SOME y) = SOME y
      | add (NONE,   NONE  ) = NONE
in
    mergeWith add (m1,m2)
end
end (* local *)

(* NOTE: this function is only used in verbose mode *)
fun dom_set (m :linear_type) :term set =
    HOLset.fromList Term.compare (dom m)

fun safe_delete (s :term set, i :term) =
    HOLset.delete(s,i) handle NotFound => s

(* Test code for linear_add (after linear_of_term):

   val m1 = linear_of_term “x + 1 / 2 * y”;
   listItems m1; (* [(“x”, 1i/1), (“y”, 1i/2)] *)

   val m2 = linear_of_term “2 * z + ~1 / 2 * y”;
   listItems m2; (* [(“y”, -1i/2), (“z”, 2i/1)] *)

   val m = linear_add m1 m2;
   listItems m; (* [(“x”, 1i/1), (“z”, 2i/1)] *)
 *)
fun linear_add (m1 :linear_type) (m2 :linear_type) :linear_type =
    mergeWithoutZero Arbrat.+ m1 m2

(* val m' = linear_cmul (rat_of_term “&2”) m1;
   listItems m'; (* [(“x”, 2i/1), (“y”, 1i/1)] *)
 *)
fun linear_cmul c (m :linear_type) :linear_type =
    if c = Arbrat.zero then undefined
    else if c = Arbrat.one then m
    else mapWith (curry Arbrat.* c) m

(* Test code for linear_of_term (was called "lin_of_hol"):

   val m = linear_of_term “&2 * x + &3 * y + &1 / &4”;
   listItems m; (* [(“x”, 2i/1), (“y”, 3i/1), (“1”, 1i/4)] *)
 *)
fun linear_of_term (tm :term) :linear_type =
    if tm ~~ zero_tm then undefined
    else if not (is_comb tm) then (tm |=> Arbrat.one)
    else if is_ratconst tm then (one_tm |=> rat_of_term tm) else
    let val (lop,r) = dest_comb tm in
        if not (is_comb lop) then (tm |=> Arbrat.one) else
        let val (op',l) = dest_comb lop in
            if op' ~~ plus_tm then linear_add (linear_of_term l) (linear_of_term r)
            else if op' ~~ mult_tm andalso is_ratconst l then (r |=> rat_of_term l)
            else (tm |=> Arbrat.one)
        end
    end

(* This is for verbose printing only (also, the resulting term is simplified)

   val e = linear_of_term “&0 + &1 * x + &2 * (y :real)”;
   term_of_linear e; (* “x + 2 * y” *)
 *)
fun term_of_linear (e :linear_type)  = let
    val vars = dom_set e
    val vars' = safe_delete (vars,one_tm)
    and base = term_of_rat(apply e one_tm)
    val sum = HOLset.foldl
                (fn (x,tm) => mk_plus(tm,mk_mult(term_of_rat(apply e x),x)))
                base vars'
    val th = (PURE_REWRITE_CONV [REAL_ADD_LID, REAL_MUL_LID] sum)
             handle UNCHANGED => REFL sum
in
    snd(dest_eq(concl th))
end

(* NOTE: empty linear expression is considered as zero here (of course).

   Thus this function tests, for a linear expression e without variables (i.e.
   reduced to just a rational constant), whether p(e) = false.
   The function returns false if the linear expression contains any variables.

   For instance, if a (reduced) linear expression c represent the inequation
  "c > 0" but actually ~(c > 0) (i.e. c <= 0), then this is a contradictory.
 *)
fun contradictory (p :rat -> bool)
                  ((e,_) :linear_type * positivstellensatz) :bool =
    (is_undefined e andalso not(p Arbrat.zero)) orelse
    (is_single e andalso defined e one_tm andalso not(p(apply e one_tm)))

(* linear prover (actually a refuter) for le and lt ineqs *)
fun linear_ineqs (vars :term set) (les :(linear_type * positivstellensatz) list,
                                   lts :(linear_type * positivstellensatz) list)
   :linear_type * positivstellensatz =

 (* termination case 1 (for lt ineqs) *)
    let val c = List.find (contradictory (fn x => Arbrat.> (x,Arbrat.zero))) lts in
        case c of SOME ep =>
                  (print_verbose ("[linear_prover] found contradiction: " ^
                                  term_to_string(term_of_linear(fst ep)) ^ " > 0\n",
                                  ".");
                   ep)
                | NONE    => failwith ""
    end handle HOL_ERR _ =>

 (* termination case 2 (for le ineqs) *)
    let val c = List.find (contradictory (fn x => Arbrat.>= (x,Arbrat.zero))) les in
        case c of SOME ep =>
                  (print_verbose ("[linear_prover] found contradiction: " ^
                                  term_to_string(term_of_linear(fst ep)) ^ " >= 0\n",
                                  ".");
                   ep)
                | NONE    => failwith ""
    end handle HOL_ERR _ =>

 (* termination case 3 *)
    if HOLset.isEmpty(vars) then failwith "linear_ineqs: no contradiction" else

 (* recursion cases *)
    let val ineqs = les @ lts

     (* The so-called "blowup" seems to be a heuristics on how frequently a variable
        occurs with "balanced" times with both positive and negative coefficients.
       (See also calc_blowup() for a similar piece of code.) *)
        fun blowup v = let
            val p = filter (fn (e,_) => Arbrat.> (apply e v,Arbrat.zero)) ineqs
            and n = filter (fn (e,_) => Arbrat.< (apply e v,Arbrat.zero)) ineqs in
            length p * length n
        end

     (* This finds the variable with minimal "blowup" *)
        val v = fst(hd(sort (fn (_,i) => fn (_,j) => i <= j)
                            (map (fn v => (v,blowup v)) (HOLset.listItems vars))))

     (* This adds up two linear inequations e1,e2 with their proofs p1,p2, w.r.t. v *)
        fun addup (e1,p1) (e2,p2) acc = let
            (* c1 and c2 are coefficients of v in e1 and e2. *)
            val c1 = apply e1 v and c2 = apply e2 v
        in
         (* NOTE: c1 * c2 is v's "blowup", which is currently minimal. And if
            it is already non-negative (which terminates the function), then
            so are the "blowup" of all others variables.

            If c1 * c2 is negative, one of them must be negative. Now e1 and e2
            looks like this:

            e1 := ... + c1 * v + ...               > or >= 0       (1)
            e2 := ... + c2 * v + ...               > or >= 0       (2)

            To eliminate v in both e1 and e2, we can add up |c2| * e1 + |c1| * e2:

            |c2| * e1 = ... + |c2| * c1 * v + ...  > or >= 0       (3)
            |c1| * e2 = ... + |c1| * c2 * v + ...  > or >= 0       (4)

            The variable v does't occur in (3)+(4) as |c2| * c1 + |c1| * c2 = 0.
          *)
            if Arbrat.>= (Arbrat.* (c1,c2), Arbrat.zero) then acc else
            let val e1' = linear_cmul (Arbrat.abs c2) e1
                and e2' = linear_cmul (Arbrat.abs c1) e2
                and p1' = Product(Rational_lt(Arbrat.abs c2),p1)
                and p2' = Product(Rational_lt(Arbrat.abs c1),p2)
                val e = linear_add e1' e2'
            in
               (print_verbose ("[linear_prover] adding up " ^
                               term_to_string(term_of_linear e1) ^ " and " ^
                               term_to_string(term_of_linear e2) ^ " for getting " ^
                               term_to_string(term_of_linear e) ^ "\n",
                               "");
                (e,Sum(p1',p2'))::acc)
            end
        end (* of addup *)

        (* les0 are le ineqs where v doesn't occur, les1 where v does occur *)
        val (les0,les1) = partition (fn (e,_) => apply e v = Arbrat.zero) les

        (* lts0 are lt ineqs where v doesn't occur, lts1 where v does occur *)
        and (lts0,lts1) = partition (fn (e,_) => apply e v = Arbrat.zero) lts

        (* lesp are le ineqs where v occurs with positive coefficients, lesn negative *)
        val (lesp,lesn) = partition (fn (e,_) => Arbrat.> (apply e v,Arbrat.zero)) les1

        (* ltsp are lt ineqs where v occurs with positive coefficients, ltsn negative *)
        and (ltsp,ltsn) = partition (fn (e,_) => Arbrat.> (apply e v,Arbrat.zero)) lts1

        (* les' is the addups of all ineqs from lesp, lesn and les0, w/o v.
           NOTE: le + le ineqs is still le ineq *)
        val les' = itlist (fn ep1 => itlist (addup ep1) lesp) lesn les0

        (* lts' is the addups of all ineqs from lesp/lesn, ltsp/ltsn and lts0, w/o v
           NOTE: les ineqs are involved because lt + le ineq is lt ineq.

           NOTE: now it is clear why v is chosen with minimal "blowup": such addups
                 of ineqs may cause a blowup on the number of ineqs for next rounds,
                 the choice of v guarentees that the number of new ineqs is minimal.
         *)
        and lts' = itlist (fn ep1 => itlist (addup ep1) (lesp @ ltsp)) ltsn
                          (itlist (fn ep1 => itlist (addup ep1) (lesn @ ltsn)) ltsp
                                  lts0)
    in
        (print_verbose ("","+" ^ Int.toString(List.length les' + List.length lts'));
         linear_ineqs (HOLset.delete (vars,v)) (les',lts'))
    end (* of linear_ineqs *)

(* This function eliminates all equations and then call linear_ineqs() *)
fun linear_eqs (eqs :(linear_type * positivstellensatz) list,
                les :(linear_type * positivstellensatz) list,
                lts :(linear_type * positivstellensatz) list)
   :linear_type * positivstellensatz =
 (* termination case for equations *)
    let val c = List.find (contradictory (fn x => x = Arbrat.zero)) eqs in
        case c of SOME ep => ep
                | NONE    => failwith ""
    end handle HOL_ERR _ =>
 (* recursion cases *)
    case eqs of
      [] => let val vars = safe_delete
                             (itlist (fn ep => fn s =>
                                         HOLset.addList (s,dom (fst ep)))
                                     (les @ lts) empty_tmset,
                              one_tm) in
                linear_ineqs vars (les,lts)
            end
    | ((e,p)::es) =>
      if is_undefined e then linear_eqs(es,les,lts) else
      (* now choose one arbitrary var x and its coefficient c *)
         let val (x,c) = choose (undefine one_tm e)
             (* e,p := ... +  c * x       + ... = 0                     (1)
                t,q := ... +  d * x       + ... =/>/>= 0                (2)
                k   := -d * |c| / c                                     (3)
                e'  := ... + -d * |c| * x + ... = 0         (=   k * e) (4)
                t'  := ... +  d * |c| * x + ... =/>/>= 0    (= |c| * t) (5)

                Thus "x" gets eliminated in (4)+(5) := (3)*(1) + |c|*(2).
              *)
             fun xform (inp as (t,q)) = let
                 val d = apply t x (* coefficient of x in other ineqs *)
             in
                 if d = Arbrat.zero then inp else
                 let val k = Arbrat./ (Arbrat.* (Arbrat.~ d, Arbrat.abs c), c)
                     val e' = linear_cmul k e
                     and t' = linear_cmul (Arbrat.abs c) t
                     and p' = Eqmul(term_of_rat k,p)
                     and q' = Product(Rational_lt(Arbrat.abs c),q)
                     val et = linear_add e' t'
                 in
                    (print_verbose ("[linear prover] adding up " ^
                                    term_to_string(term_of_linear e) ^ " = 0 and " ^
                                    term_to_string(term_of_linear t) ^ " for getting " ^
                                    term_to_string(term_of_linear et) ^ "\n",
                                    "+");
                     (et,Sum(p',q')))
                 end
             end
         in
            (* eliminate x in all equation and inequations, abbandon e. *)
            (print_verbose ("[linear prover] eliminating " ^
                            term_to_string(term_of_linear e) ^ " = 0 (with var " ^
                            term_to_string(x) ^ ")\n",
                            "-");
             linear_eqs (map xform es,map xform les,map xform lts))
         end

fun linear_prover (eq_pols :linear_type list,
                   le_pols :linear_type list,
                   lt_pols :linear_type list) :linear_type * positivstellensatz = let
    val eqs = map2 (fn p => fn n => (p,Axiom_eq n)) eq_pols (count (length eq_pols))
    and les = map2 (fn p => fn n => (p,Axiom_le n)) le_pols (count (length le_pols))
    and lts = map2 (fn p => fn n => (p,Axiom_lt n)) lt_pols (count (length lt_pols))
in
    (print_verbose ("", "positivstellensatz: ");
     let val ep = linear_eqs (eqs,les,lts) in
         (print_verbose ("","\n"); ep)
     end)
end

(* “&n” is alien, while “&1” (and others) is not *)
fun is_alien tm = is_injected tm andalso not(is_real_literal tm)

(* This takes out “n” (may be more than just a variable) from “&SUC n” *)
fun dest_suc_alien tm = numSyntax.dest_suc (dest_injected tm)

(* Test code for REAL_LINEAR_PROVER

   fun translator _ proof = proof;
   val lt0 = ASSUME (“~&1 + x + y + &1 / &2 * z > 0”);        (* Axiom_lt 0 *)
   val le0 = ASSUME (“~&1 * x + ~&1 * y + &1 / &2 * z >= 0”); (* Axiom_le 0 *)
   val eq0 = ASSUME (“~&1 + z = 0”);                          (* Axiom_eq 0 *)

   REAL_LINEAR_PROVER translator ([eq0],[le0],[lt0]);

val it =
   Sum
    (Product (Rational_lt 1i/1,
              Sum (Eqmul (“-1 / 2”, Axiom_eq 0),
                   Product (Rational_lt 1i/1, Axiom_lt 0))),
     Product (Rational_lt 1i/1,
              Sum (Eqmul (“-1 / 2”, Axiom_eq 0),
                   Product (Rational_lt 1i/1, Axiom_le 0)))): positivstellensatz

   NOTE: val translator = hol_of_positivstellensatz (* for debugging purposes *)
 *)
local
  val n_tm = “n:num”
in
  fun REAL_LINEAR_PROVER translator (eq,le,lt) = let
    val eq_pols = map (linear_of_term o lhand o concl) eq
    and le_pols = map (linear_of_term o lhand o concl) le
    and lt_pols = map (linear_of_term o lhand o concl) lt

    val all_vars = itlist (fn e => fn s => HOLset.addList(s, dom e))
                          (eq_pols @ le_pols @ lt_pols) empty_tmset
    val all_aliens = HOLset.listItems
                         (HOLset.filter (fn x => is_alien x) all_vars)

    val (suc_aliens,aliens) =
        partition (fn x => numSyntax.is_suc (dest_injected x)) all_aliens

    (* for all (normal) alien terms like “&n”, adding “1 * &n >= 0” into le_pols *)
    val le_pols' = le_pols @ map (fn v => (v |=> Arbrat.one)) aliens

    (* for all "SUC" alien terms like “&SUC n”, adding “1 * &SUC n > 0” into lt_pols *)
    val lt_pols' = lt_pols @ map (fn v => (v |=> Arbrat.one)) suc_aliens

    (* call linear prover to get the proof, droping the contradiction *)
    val (_,proof) = linear_prover(eq_pols,le_pols',lt_pols')

    (* adding “&n >= 0” theorems for alien terms before translating proof *)
    val le' = le @ map
      (fn a => INST [n_tm |-> rand a] REAL_LINEAR_PROVER_pth) aliens

    (* adding “&SUC n > 0” theorems for alien terms before translating proof *)
    val lt' = lt @ map
      (fn a => INST [n_tm |-> dest_suc_alien a] REAL_LINEAR_PROVER_pth') suc_aliens
  in
    translator (eq,le',lt') proof
  end
end

(* ------------------------------------------------------------------------- *)
(* Parametrized reals decision procedure (GEN_REAL_ARITH).                   *)
(*                                                                           *)
(* This is a bootstrapping version, and subsequently gets overwritten twice  *)
(* with more specialized versions, once here and finally in "calc_rat.ml".   *)
(* ------------------------------------------------------------------------- *)

(* This translation is provided by Konrad Slind, the author of HOL4's Net package *)
fun MATCH_MP_RULE rules =
  let val net = itlist
                 (fn th => Net.insert (lhand(concl th),PART_MATCH lhand th))
                 (CONJUNCTS rules) Net.empty
      fun apply_net th =
        let val tm = concl th
            val convs = Net.match tm net
        in
            if List.null(convs) then raise UNCHANGED
            else FIRST_CONV convs tm
        end
  in
      fn th => MP (apply_net th) th
  end

(* This commented code is for debugging GEN_REAL_ARITH only:

val (mk_numeric,
     NUMERIC_EQ_CONV,NUMERIC_GE_CONV,NUMERIC_GT_CONV,
     POLY_CONV,POLY_NEG_CONV,POLY_ADD_CONV,POLY_MUL_CONV,
     absconv1,absconv2,prover) =
    (term_of_rat,
     REAL_INT_EQ_CONV,REAL_INT_GE_CONV,REAL_INT_GT_CONV,
     REAL_POLY_CONV,REAL_POLY_NEG_CONV,REAL_POLY_ADD_CONV,REAL_POLY_MUL_CONV,
     NO_CONV,NO_CONV,REAL_LINEAR_PROVER)

val (mk_numeric,
     NUMERIC_EQ_CONV,NUMERIC_GE_CONV,NUMERIC_GT_CONV,
     POLY_CONV,POLY_NEG_CONV,POLY_ADD_CONV,POLY_MUL_CONV,
     absconv1,absconv2,prover) =
    (term_of_rat,
     REAL_RAT_EQ_CONV,REAL_RAT_GE_CONV,REAL_RAT_GT_CONV,
     REAL_POLY_CONV,REAL_POLY_NEG_CONV,REAL_POLY_ADD_CONV,REAL_POLY_MUL_CONV,
     ABSMAXMIN_ELIM_CONV1,ABSMAXMIN_ELIM_CONV2,REAL_LINEAR_PROVER)
 *)

local
  val pths_init = CONJUNCTS GEN_REAL_ARITH0_pth_init
  val pth10 = last pths_init
  val x_tm = “x:real” and y_tm = “y:real”
  and neg_tm = realSyntax.negate_tm
  and gt_tm = realSyntax.greater_tm
  and ge_tm = realSyntax.geq_tm
  and eq_tm = realSyntax.real_eq_tm
  and p_tm = “p:bool”
  and or_tm = boolSyntax.disjunction
  and false_tm = boolSyntax.F
  and z_tm = “&0 :real”
  and xy_lt = “(x:real) < y”
  and xy_nlt = “~((x:real) < y)”
  and xy_le = “(x:real) <= y”
  and xy_nle = “~((x:real) <= y)”
  and xy_gt = “(x:real) > y”
  and xy_ngt = “~((x:real) > y)”
  and xy_ge = “(x:real) >= y”
  and xy_nge = “~((x:real) >= y)”
  and xy_eq = “x:real = y”
  and xy_ne = “~(x:real = y)”
  val is_ge = realSyntax.is_geq
  and is_gt = realSyntax.is_greater
  and is_req = is_binop eq_tm
in
fun GEN_REAL_ARITH0 (mk_numeric,
                     NUMERIC_EQ_CONV,NUMERIC_GE_CONV,NUMERIC_GT_CONV,
                     POLY_CONV,POLY_NEG_CONV,POLY_ADD_CONV,POLY_MUL_CONV,
                     absconv1,absconv2,prover) =
let

  (* NOTE: sometimes the real arith expression is hidding in deeper level, e.g.
     in {x | x + 0 < 1}. Some proofs require their reducitions. -- Chun Tian *)
  val POLY_CONV' = QCONV (TOP_DEPTH_CONV POLY_CONV)

  fun REAL_INEQ_CONV pth tm = let
    val (lop,r) = dest_comb tm
    val th = INST [x_tm |-> rand lop, y_tm |-> r] pth
  in
    TRANS th (LAND_CONV POLY_CONV' (rand(concl th)))
  end

  val convs = map REAL_INEQ_CONV pths_init
  val REAL_LT_CONV     = el 1 convs (* x < y <=> y - x > 0     *)
  and REAL_LE_CONV     = el 2 convs (* x <= y <=> y - x >= 0   *)
  and REAL_GT_CONV     = el 3 convs (* x > y <=> x - y > 0     *)
  and REAL_GE_CONV     = el 4 convs (* x >= y <=> x - y >= 0   *)
  and REAL_EQ_CONV     = el 5 convs (* x = y <=> x - y = 0     *)
  and REAL_NOT_LT_CONV = el 6 convs (* ~(x < y) <=> x - y >= 0 *)
  and REAL_NOT_LE_CONV = el 7 convs (* ~(x <= y) <=> x - y > 0 *)
  and REAL_NOT_GT_CONV = el 8 convs (* ~(x > y) <=> y - x >= 0 *)
  and REAL_NOT_GE_CONV = el 9 convs (* ~(x >= y) <=> y - x > 0 *)

  (* NOTE: all REAL_NOT_*_CONV here take positive terms, e.g.,
     REAL_NOT_EQ_CONV “x = (y :real)” returns

     |- x <> y <=> x + -1 * y > 0 \/ -1 * x + y > 0: thm
   *)
  fun REAL_NOT_EQ_CONV tm = let
    val (l,r) = dest_eq tm
    val th = INST [x_tm |-> l, y_tm |-> r] pth10
    val th_p = POLY_CONV' (lhand(lhand(rand(concl th))))
    val th_x = AP_TERM neg_tm th_p
    val th_n = CONV_RULE (RAND_CONV POLY_NEG_CONV) th_x
    val th' = MK_DISJ (AP_THM (AP_TERM gt_tm th_p) z_tm)
                      (AP_THM (AP_TERM gt_tm th_n) z_tm)
    in TRANS th th' end (* REAL_NOT_EQ_CONV *)

  val net_single = itlist Net.insert
                  [(xy_lt,  REAL_LT_CONV),
                   (xy_nlt, REAL_NOT_LT_CONV o dest_neg),
                   (xy_le,  REAL_LE_CONV),
                   (xy_nle, REAL_NOT_LE_CONV o dest_neg),
                   (xy_gt,  REAL_GT_CONV),
                   (xy_ngt, REAL_NOT_GT_CONV o dest_neg),
                   (xy_ge,  REAL_GE_CONV),
                   (xy_nge, REAL_NOT_GE_CONV o dest_neg),
                   (xy_eq,  REAL_EQ_CONV),
                   (xy_ne,  REAL_NOT_EQ_CONV o dest_neg)] Net.empty

  fun REAL_INEQ_NORM_CONV tm = let
      val convs = Net.match tm net_single
  in
      if List.null(convs) then raise UNCHANGED
      (* NOTE: it's possible that an equation of non-reals were
         captured here, and REAL_EQ_CONV will raise NO_CONV *)
      else TRY_CONV (FIRST_CONV convs) tm
  end

  val net_double = itlist Net.insert
                  [(xy_lt,(fn t => (REAL_LT_CONV t,REAL_NOT_LT_CONV t))),
                   (xy_le,(fn t => (REAL_LE_CONV t,REAL_NOT_LE_CONV t))),
                   (xy_gt,(fn t => (REAL_GT_CONV t,REAL_NOT_GT_CONV t))),
                   (xy_ge,(fn t => (REAL_GE_CONV t,REAL_NOT_GE_CONV t))),
                   (xy_eq,(fn t => (REAL_EQ_CONV t,REAL_NOT_EQ_CONV t)))]
                   Net.empty

  fun REAL_INEQ_NORM_DCONV (tm :term) = let
      val convs = Net.match tm net_double
  in
      if List.null(convs) then raise UNCHANGED
      else let val f = hd(convs) in
               (* NOTE: it's possible that an equation of non-reals were
                  captured here, and REAL_EQ_CONV will raise HOL_ERR *)
               (f tm) handle HOL_ERR _ => raise UNCHANGED
           end
  end

  val NNF_NORM_CONV =
      GEN_NNF_CONV false (REAL_INEQ_NORM_CONV,REAL_INEQ_NORM_DCONV)

  fun MUL_RULE th =
      let val rules = MATCH_MP_RULE GEN_REAL_ARITH0_pth_mul in
          CONV_RULE(LAND_CONV POLY_MUL_CONV) (rules th)
      end

  fun ADD_RULE th =
      let val rules = MATCH_MP_RULE GEN_REAL_ARITH0_pth_add in
          CONV_RULE(LAND_CONV POLY_ADD_CONV) (rules th)
      end

  fun EMUL_RULE tm th =
      let val rule = MATCH_MP GEN_REAL_ARITH0_pth_emul in
          CONV_RULE(LAND_CONV POLY_MUL_CONV) (SPEC tm (rule th))
      end

  fun SQUARE_RULE t =
    CONV_RULE (LAND_CONV POLY_MUL_CONV)
      (SPEC t GEN_REAL_ARITH0_pth_square)

  (* val (eqs,les,lts) = (eq,le',lt')
     NOTE: for debugging purposes, one may use dest_positivstellensatz()
   *)
  fun hol_of_positivstellensatz(eqs,les,lts) = let
    fun translate (Axiom_eq n) = List.nth (eqs,n)
      | translate (Axiom_le n) = List.nth (les,n)
      | translate (Axiom_lt n) = List.nth (lts,n)
      | translate (Rational_eq x) =
          EQT_ELIM(NUMERIC_EQ_CONV(mk_comb(mk_comb(eq_tm,mk_numeric x),z_tm)))
      | translate (Rational_le x) =
          EQT_ELIM(NUMERIC_GE_CONV(mk_comb(mk_comb(ge_tm,mk_numeric x),z_tm)))
      | translate (Rational_lt x) =
          EQT_ELIM(NUMERIC_GT_CONV(mk_comb(mk_comb(gt_tm,mk_numeric x),z_tm)))
      | translate (Square t) = SQUARE_RULE t
      | translate (Eqmul(t,p)) = EMUL_RULE t (translate p)
      | translate (Sum(p1,p2)) = ADD_RULE (CONJ (translate p1) (translate p2))
      | translate (Product(p1,p2)) =
          MUL_RULE (CONJ (translate p1) (translate p2))
  in
    fn prf =>
       CONV_RULE(FIRST_CONV[NUMERIC_GE_CONV, NUMERIC_GT_CONV, NUMERIC_EQ_CONV])
                (translate prf)
  end

  val init_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    PRESIMP_CONV THENC

    (* NOTE: this step of POLY_CONV helps by cutting off real arith terms
       hidding in propositional terms, e.g. ‘closed {x | 1 * x = a}’ will
       be simplified to ‘closed {x | x = a}’ before going to NNF_CONV.
       Some HOL4 proofs rely on this. *)
    TOP_DEPTH_CONV POLY_CONV THENC

    NNF_CONV THENC DEPTH_BINOP_CONV or_tm CONDS_ELIM_CONV THENC
    NNF_NORM_CONV THENC
    SKOLEM_CONV THENC
    PRENEX_CONV THENC
    DNF_CONV (* was: WEAK_DNF_CONV in HOL-Light *)

  fun overall dun ths =
    case ths of
      [] => let val (eq,ne) = partition (is_req o concl) dun
                val (le,nl) = partition (is_ge o concl) ne
                val lt = filter (is_gt o concl) nl
            in
                prover hol_of_positivstellensatz (eq,le,lt)
            end
    | (th::oths) =>
      let val tm = concl th in
          if is_conj tm then
              let val (th1,th2) = CONJ_PAIR th in
                  overall dun (th1::th2::oths)
              end
          else if is_disj tm then
              let val (l,r) = dest_disj tm
                  val th1 = overall dun (ASSUME l :: oths)
                  and th2 = overall dun (ASSUME r :: oths)
              in
                  DISJ_CASES th th1 th2
              end
          else overall (th::dun) oths
      end
  val NNF_NORM_CONV' =
      GEN_NNF_CONV false
        (CACHE_CONV REAL_INEQ_NORM_CONV,fn t => failwith "")
  fun absremover (t :term) :thm =
     (TOP_DEPTH_CONV(absconv1 THENC BINOP_CONV (LAND_CONV POLY_CONV')) THENC
      TRY_CONV(absconv2 THENC NNF_NORM_CONV' THENC BINOP_CONV absremover)) t
in
  fn tm => let
    val th0 = init_conv(mk_neg tm)
    val tm0 = rand(concl th0)
    val th =
      if tm0 ~~ false_tm then fst(EQ_IMP_RULE th0) else
      let val (evs,bod) = strip_exists tm0
          val (avs,ibod) = strip_forall bod
          val th1 = itlist MK_FORALL avs
                            (DEPTH_BINOP_CONV or_tm (QCONV absremover) ibod)
          (* most of the job is done here *)
          val th2 = overall [] [SPECL avs (ASSUME(rand(concl th1)))]
          val th3 =
              itlist SIMPLE_CHOOSE evs (PROVE_HYP (EQ_MP th1 (ASSUME bod)) th2)
      in
          DISCH_ALL(PROVE_HYP (EQ_MP th0 (ASSUME (mk_neg tm))) th3)
      end
  in
    MP (INST [p_tm |-> tm] GEN_REAL_ARITH0_pth_final) th
  end
end
end (* local *)

end; (* structure *)
