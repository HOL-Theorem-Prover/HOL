(* ========================================================================= *)
(* Generic Gröbner basis algorithm [1]. (HOL-Light's grobner.ml)         UOK *)
(*                                                                           *)
(* Whatever the instantiation, it basically solves the universal theory of   *)
(* the complex numbers, or equivalently something like the theory of all     *)
(* commutative cancellation semirings with no nilpotent elements and having  *)
(* characteristic zero. We could do "all rings" by a more elaborate integer  *)
(* version of Grobner bases, but I don't have any useful applications.       *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                                                                           *)
(*               Ported to HOL4 by Chun Tian, May 2022                       *)
(* ========================================================================= *)

structure Grobner :> Grobner =
struct

open HolKernel Parse boolLib liteLib;

open boolSimps simpLib arithmeticTheory Num_conv numSyntax mesonLib metisLib
     tautLib Arithconv Canon_Port normalForms reduceLib;

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars arithmetic_grammars
end

open Parse
open Normalizer;

fun failwith s = raise mk_HOL_ERR "Grobner" "?" s

(* NOTE: OCaml's el is 0-indexed, while HOL4's Lib.el is 1-indexed. *)
fun el (i :int) (l :'a list) = failwith "please use List.nth instead";

val verbose = ref true;
fun print_verbose str = if !verbose then print str else ();

val num_0 = Arbnum.zero;
val num_1 = Arbnum.one;

(* NOTE: HOL-Light compatible *)
val NNF_CONV = normalForms.NNFD_CONV;

(* NOTE: somehow normalForms.PRENEX_CONV doesn't work *)
val PRENEX_CONV = Canon_Port.PRENEX_CONV;

(*---------------------------------------------------------------------------*
 * Lexcographic orders (from Oscar Abrahamsson's hol-light-sml project)      *
 *---------------------------------------------------------------------------*)

(* cf. List.collate, Portable.list_compare *)
fun llex rel l1 l2 =
  case (l1, l2) of
    ([], []) => false
  | ([], _) => true
  | (_::_, []) => false
  | (h1::t1, h2::t2) =>
      if rel h1 h2 then
        true
      else if h1 = h2 then
        llex rel t1 t2
      else
        false;

(* ------------------------------------------------------------------------- *)
(* Various useful list operations. (from HOL-Light's lib.ml)                 *)
(* ------------------------------------------------------------------------- *)

(* NOTE: Portable.sort is actually a mergesort. This is quicksort. *)
fun sort cmp [] = []
  | sort cmp (piv::rest) =
    let val (r,l) = partition (cmp piv) rest in
      (sort cmp l) @ (piv::(sort cmp r))
    end

(* merging and bottom-up mergesort *)
fun merge ord [] l2 = l2
  | merge ord (l1 as h1::t1) [] = l1
  | merge ord (l1 as h1::t1) (l2 as h2::t2) =
    if ord h1 h2 then h1::(merge ord t1 l2)
    else h2::(merge ord l1 t2)

fun mergesort ord = let
  fun mergepairs [s] [] = s
    | mergepairs l [] = mergepairs [] l
    | mergepairs l [s1] = mergepairs (s1::l) []
    | mergepairs l (s1::s2::ss) = mergepairs ((merge ord s1 s2)::l) ss;
in
  fn l => if null l then [] else mergepairs [] (map (fn x => [x]) l)
end

(* This is different with List.find which uses the option type *)
fun list_find p [] = failwith "find"
  | list_find p (h::t) = if p(h) then h else list_find p t;

val list_lt = llex (curry Arbnum.<);
fun setify_list lte = setify (llex lte);

val setify_int = setify (curry Int.<=);
val setify_num = setify (curry Arbnum.<=);
val setify_rat = setify (curry Arbrat.<=);

fun term_le x y = (Term.compare (x,y) <> GREATER);

(* ------------------------------------------------------------------------- *)
(* Type for recording history, i.e. how a polynomial was obtained.           *)
(* ------------------------------------------------------------------------- *)

type rat = Arbrat.rat
type aint = Arbint.int

(* NOTE: "term" of polynomial is a pair: the first part is the rational-valued
   coefficient, the second part is a list of integers representing the powers
   of each variables (also called "power product").

   For instance, “2 / 3 * x pow 2 * y pow 3” is denoted by (2/3i, [2, 3]),
   assuming the variable ordering is “x” < “y”). A constant term (coefficient
   only) is a power product of all zero powers, e.g. (2/3i, [0, 0]).
 *)
type pterm = rat * num list

(* NOTE: polynomial is a list of terms representing the summation of all terms.
  (subtraction is implemented by adding terms with negative coefficients.)
 *)
type poly = pterm list

(* A history can be also a proof

   NOTE: "Start(-1)" in HOL-Light is translated to "Start(NONE)" here, and
         the constructor "Mult" was "Mmul".
 *)
datatype history =
   Start of int option
 | Mult of pterm * history
 | Add of history * history;

type basis = (poly * history) list

(* a certificate as sum (as list) of multipliers (of polynomials) *)
type cert = (int * poly) list

local open Arbnum in
  fun lcm_num x y = (x * y) div (gcd (x, y));
end;

(* (for tests only) it easily makes rationals from two ints *)
local open Arbrat in
  fun mk_rat m n = fromInt m / fromInt n
end

(* ----------------------------------------------------------------------- *)
(* Monomial ordering.                                                      *)
(* ----------------------------------------------------------------------- *)

local open Arbnum in
fun morder_lt (m1 :num list) (m2 :num list) :bool = let
  fun lexorder [] [] = false
    | lexorder (x1::o1) (x2::o2) =
      x1 > x2 orelse x1 = x2 andalso lexorder o1 o2
    | lexorder _ _ = failwith "morder: inconsistent monomial lengths";
  val n1 = itlist (curry op+) m1 zero
  and n2 = itlist (curry op+) m2 zero
in
    n1 < n2 orelse n1 = n2 andalso lexorder m1 m2
end;
end (* local *)

(* ----------------------------------------------------------------------- *)
(* Arithmetic on canonical polynomials.                                    *)
(* ----------------------------------------------------------------------- *)

(* negation of poly terms *)
val grob_neg :poly -> poly =
    map (fn (c,m) => (Arbrat.~c, m));

fun grob_add ([] :poly) (l2 :poly) :poly = l2
  | grob_add l1 [] = l1
  | grob_add (l1 as (c1,m1)::o1) (l2 as (c2,m2)::o2) =
    if m1 = m2 then
        let val c = Arbrat.+ (c1,c2) and rest = grob_add o1 o2 in
            if c = Arbrat.zero then rest else (c,m1)::rest
        end
    else if morder_lt m2 m1 then
        (c1,m1)::(grob_add o1 l2)
    else
        (c2,m2)::(grob_add l1 o2);

fun grob_sub (l1 :poly) (l2 :poly) :poly =
    grob_add l1 (grob_neg l2);

fun grob_mmul ((c1,m1) :pterm) ((c2,m2) :pterm) :pterm =
   (Arbrat.* (c1,c2), map2 (curry Arbnum.+) m1 m2);

fun grob_cmul (cm :pterm) (pol :poly) :poly =
    map (grob_mmul cm) pol;

fun grob_mul ([] :poly) (l2 :poly) :poly = ([] :poly)
  | grob_mul (h1::t1) l2 =
    grob_add (grob_cmul h1 l2) (grob_mul t1 l2);

fun grob_inv ([(c,vs)] :poly) :poly =
    if all (fn x => x = num_0) vs then
        if c = Arbrat.zero then failwith "grob_inv: division by zero"
        else [(Arbrat./ (Arbrat.one,c),vs)]
    else failwith "grob_inv: non-constant divisor polynomial"
  | grob_inv _ = failwith "grob_inv: non-constant divisor polynomial";

fun grob_div (l1 :poly) ([(c,vs)] :poly) :poly =
    if all (fn x => x = num_0) vs then
        if c = Arbrat.zero then failwith "grob_div: division by zero"
        else grob_cmul (Arbrat./ (Arbrat.one,c),vs) l1
    else failwith "grob_div: non-constant divisor polynomial"
  | grob_div _ _ = failwith "grob_div: non-constant divisor polynomial";

local open Arbnum in
fun grob_pow (vars :term list) (l :poly) (n :num) :poly =
    if n = zero then [(Arbrat.one, map (fn v => zero) vars)]
    else grob_mul l (grob_pow vars l (n - one));
end;

(* ----------------------------------------------------------------------- *)
(* Monomial division operation.                                            *)
(* ----------------------------------------------------------------------- *)

fun mdiv ((c1,m1) :pterm) ((c2,m2) :pterm) :pterm =
   (Arbrat./ (c1,c2),
    map2 (fn n1 => fn n2 =>
             if Arbnum.< (n1,n2) then failwith "mdiv" else Arbnum.- (n1,n2))
         m1 m2);

(* ----------------------------------------------------------------------- *)
(* Lowest common multiple of two monomials.                                *)
(* ----------------------------------------------------------------------- *)

(* cf. arithmeticTheory.MAX_DEF *)
local open Arbnum in
fun max_num m n = if m < n then n else m
end;

fun mlcm ((c1,m1) :pterm) ((c2,m2) :pterm) :pterm =
   (Arbrat.one,map2 max_num m1 m2);

(* ----------------------------------------------------------------------- *)
(* Reduce monomial cm by polynomial pol, returning replacement for cm.     *)
(* ----------------------------------------------------------------------- *)

(* ‘:poly * history’ is the element of basis *)
fun reduce1 (cm :pterm) ([],hpol) :poly * history = failwith "reduce1"
  | reduce1 cm (cm1::cms,hpol) =
    let val (c,m) = mdiv cm cm1 in
        (grob_cmul (Arbrat.~ c,m) cms, Mult((Arbrat.~ c,m),hpol))
    end
    handle HOL_ERR _ => failwith "reduce1";

(* ----------------------------------------------------------------------- *)
(* Try this for all polynomials in a basis.                                *)
(* ----------------------------------------------------------------------- *)

fun reduceb (cm :pterm) (basis :basis) =
    tryfind (fn p => reduce1 cm p) basis;

(* ----------------------------------------------------------------------- *)
(* Reduction of a polynomial (always picking largest monomial possible).   *)
(* ----------------------------------------------------------------------- *)

fun reduce (basis :basis) ([],hist) : poly * history = ([],hist)
  | reduce basis (cm::ptl,hist) =
    let val (q,hnew) = reduceb cm basis in
        reduce basis (grob_add q ptl,Add(hnew,hist))
    end
    handle HOL_ERR _ =>
           let val (q,hist') = reduce basis (ptl,hist) in
               (cm::q,hist')
           end;

(* ----------------------------------------------------------------------- *)
(* Check for orthogonality w.r.t. LCM.                                     *)
(* ----------------------------------------------------------------------- *)

fun orthogonal (l :pterm) (p1 :poly) (p2 :poly) :bool =
    (snd l = snd(grob_mmul (hd p1) (hd p2)));

(* ----------------------------------------------------------------------- *)
(* Compute S-polynomial of two polynomials.                                *)
(* ----------------------------------------------------------------------- *)

fun spoly (cm :pterm) ([],h) p :poly * history = ([],h)
  | spoly cm p ([],h) = ([],h)
  | spoly cm (cm1::ptl1,his1) (cm2::ptl2,his2) =
    (grob_sub (grob_cmul (mdiv cm cm1) ptl1)
              (grob_cmul (mdiv cm cm2) ptl2),
     Add(Mult(mdiv cm cm1,his1),
         Mult(mdiv (Arbrat.~(fst cm),snd cm) cm2,his2)));

(* ----------------------------------------------------------------------- *)
(* Make a polynomial monic.                                                *)
(* ----------------------------------------------------------------------- *)

fun monic (pol,hist) : poly * history =
    if pol = [] then (pol,hist) else
    let val (c',m') = hd pol in
        (map (fn (c,m) => (Arbrat./ (c,c'),m)) pol,
         Mult((Arbrat./ (Arbrat.one,c'),map (K num_0) m'),hist))
    end;

(* ----------------------------------------------------------------------- *)
(* The most popular heuristic is to order critical pairs by LCM monomial.  *)
(* ----------------------------------------------------------------------- *)

fun forder ((((c1,m1) :pterm),_)) (((c2,m2) :pterm),_) = morder_lt m1 m2;

(* ----------------------------------------------------------------------- *)
(* Buchberger's second criterion. [2]                                      *)
(* ----------------------------------------------------------------------- *)

fun poly_lt (p :poly) ([] :poly) = false
  | poly_lt [] q = true
  | poly_lt ((c1,m1)::o1) ((c2,m2)::o2) =
    Arbrat.< (c1,c2) orelse
    c1 = c2 andalso
    (list_lt m1 m2 orelse m1 = m2 andalso poly_lt o1 o2);

fun align (((p,hp) :poly * history),
           ((q,hq) :poly * history)) =
    if poly_lt p q then ((p,hp),(q,hq)) else ((q,hq),(p,hp));

fun criterion2 (basis :basis) (lcm,((p1,h1),(p2,h2)))
               (opairs :('a * ((poly * history) * (poly * history))) list) =
    exists (fn g => (fst g) <> p1 andalso (fst g) <> p2 andalso
                    can (mdiv lcm) (hd(fst g)) andalso
                    not(mem (align(g,(p1,h1))) (map snd opairs)) andalso
                    not(mem (align(g,(p2,h2))) (map snd opairs))) basis;

(* ----------------------------------------------------------------------- *)
(* Test for hitting constant polynomial.                                   *)
(* ----------------------------------------------------------------------- *)

fun constant_poly (p :poly) : bool =
    (length p = 1 andalso forall (fn x => x = num_0) (snd(hd p)));

(* ----------------------------------------------------------------------- *)
(* Grobner basis algorithm.                                                *)
(* ----------------------------------------------------------------------- *)

fun grobner_basis (basis :basis)
                  (pairs :(pterm * ((poly * history) * (poly * history)))
                          list) =
   (print_verbose (Int.toString (length basis) ^ " basis elements and " ^
                   Int.toString (length pairs) ^ " critical pairs\n");
    case pairs of
      [] => basis
    | (l,(p1,p2))::opairs =>
      let val (sph as (sp,hist)) = monic (reduce basis (spoly l p1 p2)) in
          if null sp orelse criterion2 basis (l,(p1,p2)) opairs
          then grobner_basis basis opairs else
          if constant_poly sp then grobner_basis (sph::basis) [] else
          let val rawcps =
                  map (fn p => (mlcm (hd(fst p)) (hd sp),align(p,sph))) basis;
              val newcps = filter
                (fn (l,(p,q)) => not(orthogonal l (fst p) (fst q))) rawcps
          in
              grobner_basis (sph::basis)
                (merge forder opairs (mergesort forder newcps))
          end
      end);

(* ----------------------------------------------------------------------- *)
(* Interreduce initial polynomials.                                        *)
(* ----------------------------------------------------------------------- *)

fun grobner_interreduce (rpols :basis) [] :basis = map monic (rev rpols)
  | grobner_interreduce rpols (p::ps) =
    let val p' = reduce (rpols @ ps) p in
        if null(fst p') then grobner_interreduce rpols ps
        else grobner_interreduce (p'::rpols) ps
    end;

(* ----------------------------------------------------------------------- *)
(* Overall function.                                                       *)
(* ----------------------------------------------------------------------- *)

fun grobner (pols :poly list) :basis = let
    val npols = map2 (fn p => fn n => (p,Start (SOME n))) pols
                     (count (length pols));
    val phists = filter (fn (p,_) => not(null p)) npols;
    val bas = grobner_interreduce [] (map monic phists);
    val prs0 = allpairs (fn x => fn y => (x,y)) bas bas;
    val prs1 = filter (fn ((x,_),(y,_)) => poly_lt x y) prs0;
    val prs2 = map (fn (p,q) => (mlcm (hd(fst p)) (hd(fst q)),(p,q))) prs1;
    val prs3 =
      filter (fn (l,(p,q)) => not(orthogonal l (fst p) (fst q))) prs2
in
    grobner_basis bas (mergesort forder prs3)
end;

(* ----------------------------------------------------------------------- *)
(* Get proof of contradiction from Grobner basis.                          *)
(* ----------------------------------------------------------------------- *)

fun grobner_refute (pols :poly list) :history = let
    val gb = grobner pols
in
    snd(list_find
         (fn (p,h) =>
             length p = 1 andalso forall (fn x => x = num_0) (snd(hd p))) gb)
end;

(* ----------------------------------------------------------------------- *)
(* Turn proof into a certificate as sum of multipliers.                    *)
(*                                                                         *)
(* In principle this is very inefficient: in a heavily shared proof it may *)
(* make the same calculation many times. Could add a cache or something.   *)
(* ----------------------------------------------------------------------- *)

fun resolve_proof (vars :term list) (prf :history) :cert =
    case prf of
      Start NONE => []
    | Start (SOME m) => [(m,[(Arbrat.one,map (K num_0) vars)])]
    | Mult(pol,lin) =>
          let val lis = resolve_proof vars lin in
              map (fn (n,p) => (n,grob_cmul pol p)) lis
          end
    | Add(lin1,lin2) =>
          let val lis1 = resolve_proof vars lin1
              and lis2 = resolve_proof vars lin2;
              val dom = setify_int (union (map fst lis1) (map fst lis2))
          in
              map (fn n => let val a = assoc n lis1 handle HOL_ERR _ => []
                               and b = assoc n lis2 handle HOL_ERR _ => [] in
                             (n,grob_add a b)
                           end) dom
          end;

(* ----------------------------------------------------------------------- *)
(* Run the procedure and produce Weak Nullstellensatz certificate.         *)
(* ----------------------------------------------------------------------- *)

fun grobner_weak (vars :term list) (pols :poly list) :rat * cert =
    let val cert = resolve_proof vars (grobner_refute pols);
        val l = Arbrat.fromNat
           (itlist (itlist (lcm_num o Arbrat.denominator o fst) o snd) cert (num_1))
    in
        (l,map (fn (i,p) => (i,map (fn (d,m) => (Arbrat.* (l,d),m)) p)) cert)
    end;

(* ----------------------------------------------------------------------- *)
(* Prove polynomial is in ideal generated by others, using Grobner basis.  *)
(* ----------------------------------------------------------------------- *)

fun grobner_ideal (vars :term list) (pols :poly list) (pol :poly) :cert =
    let val (pol',h) = reduce (grobner pols)
                              (grob_neg pol,Start NONE) in
        if null(pol') then resolve_proof vars h
        else failwith "grobner_ideal: not in the ideal"
    end;

(* ----------------------------------------------------------------------- *)
(* Produce Strong Nullstellensatz certificate for a power of pol.          *)
(* ----------------------------------------------------------------------- *)

fun grobner_strong (vars :term list)
                   (pols :poly list) (pol :poly) :num * rat * cert =
    if null(pol) then
      (num_1,Arbrat.one,[])
    else
      let
        val vars' = (concl TRUTH)::vars
        val grob_z = [(Arbrat.one,num_1::(map (fn x => num_0) vars))]
        val grob_1 = [(Arbrat.one,(map (fn x => num_0) vars'))]
        val augment = map (fn (c,m) => (c,num_0::m))
        val pols' = map augment pols
        val pol' = augment pol
        val allpols = (grob_sub (grob_mul grob_z pol') grob_1)::pols'
        val (l,cert) = grobner_weak vars' allpols
        val d = itlist (itlist (max_num o hd o snd) o snd) cert num_0
        fun transform_monomial (c,m) =
          grob_cmul (c,tl m) (grob_pow vars pol (Arbnum.- (d,hd m)));
        fun transform_polynomial q = itlist (grob_add o transform_monomial) q []
        val cert' = map (fn (c,q) => (c - 1,transform_polynomial q))
                        (filter (fn (k,_) => k <> 0) cert)
      in
        (d,l,cert')
      end;

(* ----------------------------------------------------------------------- *)
(* Overall parametrized universal procedure for (semi)rings.               *)
(* We return an IDEAL_CONV and the actual ring prover.                     *)
(* ----------------------------------------------------------------------- *)

val pth_step = prove
   (“!(add:'a->'a->'a) (mul:'a->'a->'a) (n0:'a).
          (!x. mul n0 x = n0) /\
          (!x y z. (add x y = add x z) <=> (y = z)) /\
          (!w x y z. (add (mul w y) (mul x z) = add (mul w z) (mul x y)) <=>
                     (w = x) \/ (y = z))
          ==> (!a b c d. ~(a = b) /\ ~(c = d) <=>
                         ~(add (mul a c) (mul b d) =
                           add (mul a d) (mul b c))) /\
              (!n a b c d. ~(n = n0)
                           ==> (a = b) /\ ~(c = d)
                               ==> ~(add a (mul n c) = add b (mul n d)))”,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM DE_MORGAN_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [“n0:'a”, “n:'a”, “d:'a”, “c:'a”]) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN ASM_SIMP_TAC bool_ss []);

val FINAL_RULE = MATCH_MP(TAUT `(p ==> F) ==> (~q <=> p) ==> q`)
val false_tm = boolSyntax.F;

fun refute_disj rfn tm =
    if is_disj tm then
        let val (l,r) = dest_disj tm in
            DISJ_CASES (ASSUME tm) (refute_disj rfn l) (refute_disj rfn r)
        end
    else rfn tm;

(* for debug purposes only:
  val (ring_dest_const,ring_mk_const,RING_EQ_CONV,
       ring_neg_tm,ring_add_tm,ring_sub_tm,
       ring_inv_tm,ring_mul_tm,ring_div_tm,ring_pow_tm,
       RING_INTEGRAL,RABINOWITSCH_THM,RING_NORMALIZE_CONV) =
        (Arbrat.fromNat o dest_numeral,mk_numeral o Arbrat.toNat,
         NUM_EQ_CONV,
         genvar num_ty1 (* neg *), plus_tm, genvar num_ty2 (* sub *),
         genvar num_ty1 (* inv *), mult_tm, genvar num_ty2 (* div *), exp_tm,
         NUM_INTEGRAL,TRUTH,NUM_NORMALIZE_CONV);

local open realSyntax in
  val (ring_dest_const,ring_mk_const,RING_EQ_CONV,
       ring_neg_tm,ring_add_tm,ring_sub_tm,
       ring_inv_tm,ring_mul_tm,ring_div_tm,ring_pow_tm,
       RING_INTEGRAL,RABINOWITSCH_THM,RING_NORMALIZE_CONV) =

        (rat_of_term, term_of_rat, REAL_RAT_EQ_CONV,
         negate_tm, plus_tm, minus_tm, inv_tm, mult_tm, div_tm, exp_tm,
         REAL_INTEGRAL, REAL_RABINOWITSCH, REAL_POLY_CONV);
end
 *)

fun RING_AND_IDEAL_CONV
      (ring_dest_const,ring_mk_const,RING_EQ_CONV,
       ring_neg_tm,ring_add_tm,ring_sub_tm,
       ring_inv_tm,ring_mul_tm,ring_div_tm,ring_pow_tm,
       RING_INTEGRAL,RABINOWITSCH_THM,RING_NORMALIZE_CONV) = let

    val INITIAL_CONV =
      TOP_DEPTH_CONV BETA_CONV THENC
      PRESIMP_CONV THENC
      CONDS_ELIM_CONV THENC
      NNF_CONV THENC
      (if is_eq(snd(strip_forall(concl RABINOWITSCH_THM)))
       then GEN_REWRITE_CONV ONCE_DEPTH_CONV empty_rewrites [RABINOWITSCH_THM]
       else ALL_CONV) THENC
      PRENEX_CONV;

    fun ring_dest_neg t =
      let val (l,r) = dest_comb t in
        if l ~~ ring_neg_tm then r else failwith "ring_dest_neg"
      end;
    fun ring_dest_inv t =
      let val (l,r) = dest_comb t in
        if l ~~ ring_inv_tm then r else failwith "ring_dest_inv"
      end;

    val ring_dest_add = dest_binop ring_add_tm
    and ring_mk_add = mk_binop ring_add_tm
    and ring_dest_sub = dest_binop ring_sub_tm
    and ring_dest_mul = dest_binop ring_mul_tm
    and ring_mk_mul = mk_binop ring_mul_tm
    and ring_dest_div = dest_binop ring_div_tm
    and ring_dest_pow = dest_binop ring_pow_tm
    and ring_mk_pow = mk_binop ring_pow_tm;

    fun grobvars (tm :term) (acc :term list) :term list =
      if can ring_dest_const tm then acc
      else if can ring_dest_neg tm then grobvars (rand tm) acc
      else if can ring_dest_pow tm andalso is_numeral (rand tm)
           then grobvars (lhand tm) acc
      else if can ring_dest_add tm orelse can ring_dest_sub tm
           orelse can ring_dest_mul tm
           then grobvars (lhand tm) (grobvars (rand tm) acc)
      else if can ring_dest_inv tm then
           let val gvs = grobvars (rand tm) [] in
             if null(gvs) then acc else tm::acc
           end
      else if can ring_dest_div tm then
           let val lvs = grobvars (lhand tm) acc
               and gvs = grobvars (rand tm) [] in
             if null(gvs) then lvs else tm::acc
           end
      else tm::acc;

    fun grobify_term (vars :term list) (tm :term) : poly =
     (if not(exists (fn i => i ~~ tm) vars) then failwith "" else
          [(Arbrat.one,map (fn i => if i ~~ tm then num_1 else num_0) vars)])
      handle HOL_ERR _ =>
      let val x = ring_dest_const tm in
          if x = Arbrat.zero then [] else [(x,map (fn v => num_0) vars)]
      end
      handle HOL_ERR _ =>
      grob_neg(grobify_term vars (ring_dest_neg tm))
      handle HOL_ERR _ =>
      grob_inv(grobify_term vars (ring_dest_inv tm))
      handle HOL_ERR _ =>
      let val (l,r) = ring_dest_add tm in
          grob_add (grobify_term vars l) (grobify_term vars r)
      end
      handle HOL_ERR _ =>
      let val (l,r) = ring_dest_sub tm in
          grob_sub (grobify_term vars l) (grobify_term vars r)
      end
      handle HOL_ERR _ =>
      let val (l,r) = ring_dest_mul tm in
          grob_mul (grobify_term vars l) (grobify_term vars r)
      end
      handle HOL_ERR _ =>
      let val (l,r) = ring_dest_div tm in
          grob_div (grobify_term vars l) (grobify_term vars r)
      end
      handle HOL_ERR _ =>
      let val (l,r) = ring_dest_pow tm in
          grob_pow vars (grobify_term vars l) (dest_numeral r)
      end
      handle HOL_ERR _ =>
          failwith "grobify_term: unknown or invalid term";

    fun grobify_equation vars tm =
      let val (l,r) = dest_eq tm in
        grob_sub (grobify_term vars l) (grobify_term vars r)
      end;

    fun grobify_equations (tm :term) :term list * poly list = let
      val cjs = strip_conj tm;
      val rawvars =
        itlist (fn eq => fn a => grobvars (lhand eq) (grobvars (rand eq) a))
               cjs [];
      val vars = sort term_le (setify_term rawvars)
    in
      (vars,map (grobify_equation vars) cjs)
    end;

    val holify_polynomial : term list -> (rat * num list) list -> term =
    let
      fun holify_varpow (v,n) =
        if n = num_1 then v else ring_mk_pow (v,(mk_numeral n));
      fun holify_monomial vars (c,m) =
        let val xps = map holify_varpow
          (filter (fn (_,n) => n <> num_0) (zip vars m)) in
          end_itlist (curry ring_mk_mul) (ring_mk_const c :: xps)
        end;
      fun holify_polynomial vars p =
        if p = [] then ring_mk_const Arbrat.zero
        else end_itlist (curry ring_mk_add) (map (holify_monomial vars) p)
    in
      holify_polynomial
    end;

    val (pth_idom,pth_ine) = CONJ_PAIR(MATCH_MP pth_step RING_INTEGRAL);
    val IDOM_RULE :thm -> thm = CONV_RULE(REWR_CONV pth_idom);
    fun PROVE_NZ (n :rat) = EQF_ELIM(RING_EQ_CONV
                              (mk_eq(ring_mk_const n,ring_mk_const(Arbrat.zero))));
    val NOT_EQ_01 = PROVE_NZ (Arbrat.one);
    fun INE_RULE (n :rat) = MATCH_MP(MATCH_MP pth_ine (PROVE_NZ n));
    fun MK_ADD th1 th2 :thm = MK_COMB(AP_TERM ring_add_tm th1,th2);

    fun assoceq a [] = failwith "assoceq"
      | assoceq a ((x,y)::t) = if x = a then y else assoceq a t;

    val (x,th1) = SPEC_VAR(CONJUNCT1(CONJUNCT2 RING_INTEGRAL));
    val (y,th2) = SPEC_VAR th1;
    val (z,th3) = SPEC_VAR th2;
    val SUB_EQ_RULE = GEN_REWRITE_RULE I empty_rewrites
                        [SYM(INST [x |-> mk_comb(ring_neg_tm,z)] th3)];

    fun ADD_RULE th1 th2 =
       CONV_RULE (BINOP_CONV RING_NORMALIZE_CONV)
                 (MK_COMB(AP_TERM ring_add_tm th1,th2));
    fun MUL_RULE (vars :term list) (m :rat * num list) th =
       CONV_RULE (BINOP_CONV RING_NORMALIZE_CONV)
                 (AP_TERM (mk_comb(ring_mul_tm,holify_polynomial vars [m]))
                          th);

    fun execute_proof vars eths prf = let
      val initpols = map (CONV_RULE(BINOP_CONV RING_NORMALIZE_CONV) o
                          SUB_EQ_RULE) eths;
      val run_proof =
        if is_eq(snd(strip_forall(concl RABINOWITSCH_THM))) then
         (print_verbose "Generating HOL version of proof\n";
          let val execache = ref [];
              fun memoize prf x = (execache := (prf,x)::(!execache); x);
              fun run_proof vars prf =
                  assoceq prf (!execache)
                  handle HOL_ERR _ =>
                    (case prf of
                         Start NONE => failwith "impossible"
                       | Start (SOME m) => List.nth (initpols,m)
                       | Add(p1,p2) =>
                         memoize prf (ADD_RULE (run_proof vars p1) (run_proof vars p2))
                       | Mult(m,p2) =>
                         memoize prf (MUL_RULE vars m (run_proof vars p2)))
          in
              fn vars => fn prf =>
                 let val ans = run_proof vars prf in
                     (execache := []; ans)
                 end
          end)
        else
         (print_verbose "Generating HOL version of scaled proof\n";
          let val km = map (fn x => num_0) vars;
              val execache = ref [];
              fun memoize prf x = (execache := (prf,x)::(!execache); x);
              fun run_scaled_proof vars prf =
                  assoceq prf (!execache)
                  handle HOL_ERR _ =>
                    (case prf of
                         Start NONE => failwith "impossible"
                       | Start (SOME m) => (Arbnum.one,List.nth (initpols,m))
                       | Add(p1,p2) =>
                         let val (d1,th1) = run_scaled_proof vars p1
                             and (d2,th2) = run_scaled_proof vars p2;
                             val d = lcm_num d1 d2
                         in
                           memoize prf
                            (d,
                             ADD_RULE (MUL_RULE vars (Arbrat./ (Arbrat.fromNat d,
                                                                Arbrat.fromNat d1),km) th1)
                                      (MUL_RULE vars (Arbrat./ (Arbrat.fromNat d,
                                                                Arbrat.fromNat d2),km) th2))
                         end
                       | Mult((c,xs),p2) =>
                         let val e = Arbrat.denominator c;
                             val (d,th) = run_scaled_proof vars p2
                         in
                           memoize prf
                            (Arbnum.* (d, e),
                             MUL_RULE vars (Arbrat.* (c, Arbrat.fromNat e),xs) th)
                         end)
          in
              fn vars => fn prf =>
                 let val (_,ans) = run_scaled_proof vars prf in
                     (execache := []; ans)
                 end
          end);
      val th = run_proof vars prf
    in
      CONV_RULE RING_EQ_CONV th
    end; (* of execute_proof *)

    fun REFUTE tm =
      if tm ~~ false_tm then ASSUME tm else
      let val (nths0,eths0) = partition (is_neg o concl) (CONJUNCTS(ASSUME tm));
          val nths = filter (is_eq o rand o concl) nths0
          and eths = filter (is_eq o concl) eths0 in
      if null(eths) then
        let val th1 = end_itlist (fn th1 => fn th2 => IDOM_RULE(CONJ th1 th2)) nths;
            val th2 = CONV_RULE(RAND_CONV(BINOP_CONV RING_NORMALIZE_CONV)) th1;
            val (l,r) = dest_eq(rand(concl th2)) in
          EQ_MP (EQF_INTRO th2) (REFL l)
        end
      else if null(nths) andalso not(is_var ring_neg_tm) then
        let val (vars,pols) = grobify_equations(list_mk_conj(map concl eths)) in
          execute_proof vars eths (grobner_refute pols)
        end
      else
      let val (vars,l,cert,noteqth) =
        if null(nths) then
          let val (vars,pols) = grobify_equations(list_mk_conj(map concl eths));
              val (l,cert) = grobner_weak vars pols in
            (vars,l,cert,NOT_EQ_01)
          end
        else
          let val nth = end_itlist (fn th1 => fn th2 => IDOM_RULE(CONJ th1 th2)) nths;
              val (vars,xs) =
                  grobify_equations(list_mk_conj(rand(concl nth)::map concl eths));
              val pol = hd xs and pols = tl xs;
              val (deg,l,cert) = grobner_strong vars pols pol;
              val th1 = CONV_RULE(RAND_CONV(BINOP_CONV RING_NORMALIZE_CONV)) nth;
              (* NOTE: Arbnum.toInt may fail if deg (very unlikely) exceeds Int.maxInt *)
              val th2 = funpow (Arbnum.toInt deg) (IDOM_RULE o CONJ th1) NOT_EQ_01
          in (vars,l,cert,th2) end
      in
     (print_verbose "Translating certificate to HOL inferences\n";
      let val cert_pos = map
             (fn (i,p) => (i,filter (fn (c,m) => Arbrat.> (c,Arbrat.zero)) p)) cert
          and cert_neg = map
             (fn (i,p) => (i,map (fn (c,m) => (Arbrat.~ c,m))
                              (filter (fn (c,m) => Arbrat.< (c,Arbrat.zero)) p))) cert;
          val herts_pos =
              map (fn (i,p) => (i,holify_polynomial vars p)) cert_pos
          and herts_neg =
              map (fn (i,p) => (i,holify_polynomial vars p)) cert_neg;
          fun thm_fn pols =
              if null(pols) then REFL(ring_mk_const Arbrat.zero) else
              end_itlist MK_ADD
                (map (fn (i,p) => AP_TERM(mk_comb(ring_mul_tm,p)) (List.nth (eths,i)))
                     pols);
          val th1 = thm_fn herts_pos
          and th2 = thm_fn herts_neg;
          val th3 = CONJ(MK_ADD (SYM th1) th2) noteqth;
          val th4 = CONV_RULE (RAND_CONV(BINOP_CONV RING_NORMALIZE_CONV))
                              (INE_RULE l th3);
          val (l,r) = dest_eq(rand(concl th4))
      in
          EQ_MP (EQF_INTRO th4) (REFL l)
      end)
      end (* let val (vars,l,cert,noteqth) *)
    end; (* let val (nths0,eths0) ... *)

  val ring_ty = snd(dest_fun_ty(snd(dest_fun_ty(type_of ring_add_tm))));
  fun RING tm = let
    val avs = filter (fn x => ring_ty = type_of x) (free_vars tm);
    val tm' = list_mk_forall(avs,tm);
    val th1 = INITIAL_CONV(mk_neg tm');
    val (evs,bod) = strip_exists(rand(concl th1))
  in
    if is_forall bod then failwith "RING: non-universal formula" else
    let val th1a = DNF_CONV bod; (* NOTE: it was WEAK_DNF_CONV here *)
        val boda = rand(concl th1a);
        val th2a = refute_disj REFUTE boda;
        val th2b = TRANS th1a (EQF_INTRO(NOT_INTRO(DISCH boda th2a)));
        val th2 = UNDISCH(NOT_ELIM(EQF_ELIM th2b));
        val (finbod,th3) = let
            fun CHOOSES [] (etm,th) = (etm,th)
              | CHOOSES (ev::oevs) (etm,th) =
                let val (etm',th') = CHOOSES oevs (etm,th) in
                  (mk_exists(ev,etm'),CHOOSE (ev,ASSUME (mk_exists(ev,etm'))) th')
                end
        in
            CHOOSES evs (bod,th2)
        end
    in
      SPECL avs (MATCH_MP (FINAL_RULE (DISCH finbod th3)) th1)
    end
  end; (* of RING *)

  fun ideal tms tm = let
    val rawvars = itlist grobvars (tm::tms) [];
    val vars = sort term_le (setify_term rawvars);
    val pols = map (grobify_term vars) tms
    and pol = grobify_term vars tm;
    val cert = grobner_ideal vars pols pol
  in
    map (fn n => let val p = assoc n cert in holify_polynomial vars p end)
        (count (length pols))
  end; (* of ideal *)
in
  (RING,ideal)
end; (* of RING_AND_IDEAL_CONV *)

(* ----------------------------------------------------------------------- *)
(* Separate out the cases.                                                 *)
(* ----------------------------------------------------------------------- *)

fun RING            parms = fst(RING_AND_IDEAL_CONV parms);
fun ideal_cofactors parms = snd(RING_AND_IDEAL_CONV parms);

(* ------------------------------------------------------------------------- *)
(* Simplify a natural number assertion to eliminate conditionals, DIV, MOD,  *)
(* PRE, cutoff subtraction, EVEN and ODD. Try to do it in a way that makes   *)
(* new quantifiers universal. At the moment we don't split "<=>" which would *)
(* make this quantifier selection work there too; better to do NNF first if  *)
(* you care. This also applies to EVEN and ODD.                              *)
(* ------------------------------------------------------------------------- *)

val NOT_EVEN = GSYM ODD_EVEN;
val NOT_ODD  = GSYM EVEN_ODD;

val NUM_REDUCE_CONV = REDUCE_CONV;

val NUM_SIMPLIFY_CONV = let
  val p_tm = “P:num->bool” and n_tm = “n:num” and m_tm = “m:num”
  and q_tm = “P:num->num->bool” and a_tm = “a:num” and b_tm = “b:num”;
  val is_sub = is_minus;
  fun is_divmod tm = is_div tm orelse is_mod tm;
  val is_uexists = is_exists1;
  val contains_quantifier =
    can (find_term (fn t => is_forall t orelse is_exists t orelse is_uexists t));
  val BETA2_CONV = RATOR_CONV BETA_CONV THENC BETA_CONV
  and PRE_ELIM_THM'' = CONV_RULE (RAND_CONV NNF_CONV) PRE_ELIM_THM' (* forall *)
  and SUB_ELIM_THM'' = CONV_RULE (RAND_CONV NNF_CONV) SUB_ELIM_THM' (* forall *)
  and DIVMOD_ELIM_THM'' = CONV_RULE (RAND_CONV NNF_CONV)
                                    (SPEC_ALL DIVMOD_ELIM_THM);
  val pth_evenodd = prove
   (“(EVEN(x) <=> (!y. ~(x = SUC(2 * y)))) /\
     (ODD(x) <=> (!y. ~(x = 2 * y))) /\
     (~EVEN(x) <=> (!y. ~(x = 2 * y))) /\
     (~ODD(x) <=> (!y. ~(x = SUC(2 * y))))”,
    rpt strip_tac >| [
      REWRITE_TAC[EVEN_ODD, ODD_EXISTS],
      REWRITE_TAC[ODD_EVEN, EVEN_EXISTS],
      REWRITE_TAC[EVEN_EXISTS],
      REWRITE_TAC[ODD_EXISTS]
    ] >> CONV_TAC (LAND_CONV NOT_EXISTS_CONV) >> REWRITE_TAC[])

  fun NUM_MULTIPLY_CONV pos tm =
    if is_forall tm orelse is_exists tm orelse is_uexists tm then
       BINDER_CONV (NUM_MULTIPLY_CONV pos) tm
    else if is_imp tm andalso contains_quantifier tm then
        COMB2_CONV (RAND_CONV(NUM_MULTIPLY_CONV(not pos)))
                   (NUM_MULTIPLY_CONV pos) tm
    else if (is_conj tm orelse is_disj tm orelse is_eq tm) andalso
            contains_quantifier tm
         then BINOP_CONV (NUM_MULTIPLY_CONV pos) tm
    else if is_neg tm andalso not pos andalso contains_quantifier tm then
       RAND_CONV (NUM_MULTIPLY_CONV (not pos)) tm
    else
       let val t = find_term (fn t => is_pre t andalso free_in t tm) tm;
           val ty = type_of t;
           val v = genvar ty;
           val p = mk_abs(v,subst [t |-> v] tm);
           val th0 = if pos then PRE_ELIM_THM'' else PRE_ELIM_THM_EXISTS;
           val th1 = INST [p_tm |-> p, n_tm |-> rand t] th0;
           val th2 = CONV_RULE(COMB2_CONV (RAND_CONV BETA_CONV)
                      (BINDER_CONV(RAND_CONV BETA_CONV))) th1
       in
           CONV_RULE(RAND_CONV (NUM_MULTIPLY_CONV pos)) th2
       end
       handle HOL_ERR _ =>
       let val t = find_term (fn t => is_sub t andalso free_in t tm) tm;
           val ty = type_of t;
           val v = genvar ty;
           val p = mk_abs(v,subst [t |-> v] tm);
           val th0 = if pos then SUB_ELIM_THM'' else SUB_ELIM_THM';
           val th1 = INST [p_tm |-> p, a_tm |-> lhand t, b_tm |-> rand t] th0;
           val th2 = CONV_RULE(COMB2_CONV (RAND_CONV BETA_CONV)
                      (BINDER_CONV(RAND_CONV BETA_CONV))) th1
       in
           CONV_RULE(RAND_CONV (NUM_MULTIPLY_CONV pos)) th2
       end
       handle HOL_ERR _ =>
       let val t = find_term (fn t => is_divmod t andalso free_in t tm) tm;
           val x = lhand t and y = rand t;
           val dtm = mk_comb(mk_comb(div_tm,x),y)
           and mtm = mk_comb(mk_comb(mod_tm,x),y);
           val vd = genvar(type_of dtm)
           and vm = genvar(type_of mtm);
           val p = list_mk_abs([vd,vm],subst[dtm |-> vd, mtm |-> vm] tm);
           val th0 = if pos then DIVMOD_ELIM_THM'' else DIVMOD_ELIM_THM';
           val th1 = INST [q_tm |-> p, m_tm |-> x, n_tm |-> y] th0;
           val th2 = CONV_RULE(COMB2_CONV(RAND_CONV BETA2_CONV)
                (funpow 2 BINDER_CONV(RAND_CONV BETA2_CONV))) th1
       in
           CONV_RULE(RAND_CONV (NUM_MULTIPLY_CONV pos)) th2
       end
       handle HOL_ERR _ => raise UNCHANGED (* end of NUM_MULTIPLY_CONV *)
in
  NUM_REDUCE_CONV THENC
  CONDS_CELIM_CONV THENC
  NNF_CONV THENC
  NUM_MULTIPLY_CONV true THENC
  NUM_REDUCE_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV empty_rewrites [pth_evenodd]
end;

(* ----------------------------------------------------------------------- *)
(* Natural number version of ring procedure with this normalization.       *)
(* ----------------------------------------------------------------------- *)

val ADD_AC  = AC ADD_SYM ADD_ASSOC;
val MULT_AC = AC MULT_SYM MULT_ASSOC;
val EQ_ADD_LCANCEL_0 = ADD_INV_0_EQ;
val LE_CASES = LESS_EQ_CASES;
val LE_EXISTS = LESS_EQ_EXISTS;
val NUM_EQ_CONV = NEQ_CONV;
val num_ty1 = “:num -> num”;
val num_ty2 = “:num -> num -> num”;

val NUM_RING = let
  val NUM_INTEGRAL_LEMMA = prove
   (“((w :num) = x + d) /\ (y = z + e)
     ==> ((w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))”,
    DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THEN
    ONCE_REWRITE_TAC [SIMP_PROVE bool_ss [ADD_AC]
     “(a :num) + b + (c + d) + e = a + c + (e + (b + d))”] THEN
    REWRITE_TAC[EQ_ADD_LCANCEL, EQ_ADD_LCANCEL_0, MULT_EQ_0]);
  val NUM_INTEGRAL = prove
   (“(!(x :num). 0 * x = 0) /\
     (!(x :num) y z. (x + y = x + z) <=> (y = z)) /\
     (!(w :num) x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))”,
    REWRITE_TAC[MULT_CLAUSES, EQ_ADD_LCANCEL] THEN
    REPEAT GEN_TAC THEN
    DISJ_CASES_TAC (SPECL [“w:num”, “x:num”] LE_CASES) THEN
    DISJ_CASES_TAC (SPECL [“y:num”, “z:num”] LE_CASES) THEN
    REPEAT(FIRST_X_ASSUM
     (CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS])) THEN
    Lib.with_flag (mesonLib.chatting, 0)
      (ASM_MESON_TAC[NUM_INTEGRAL_LEMMA, ADD_SYM, MULT_SYM]));
  val rawring =
    RING(Arbrat.fromNat o dest_numeral,mk_numeral o Arbrat.toNat,
         NUM_EQ_CONV,
         genvar num_ty1 (* neg *), plus_tm, genvar num_ty2 (* sub *),
         genvar num_ty1 (* inv *), mult_tm, genvar num_ty2 (* div *), exp_tm,
         NUM_INTEGRAL,TRUTH,NUM_NORMALIZE_CONV);
  val initconv = NUM_SIMPLIFY_CONV THENC
                 GEN_REWRITE_CONV DEPTH_CONV empty_rewrites [ADD1]
in
  fn tm => let val th = initconv tm in
              if rand(concl th) ~~ T then th
              else EQ_MP (SYM th) (rawring(rand(concl th)))
           end
end;

end; (* structure *)

(* References:

 [1] https://en.wikipedia.org/wiki/Gröbner_basis                             UOK
 [2] https://en.wikipedia.org/wiki/Buchberger%27s_algorithm
 [3] Davenport, J.H., Siret, Y., Tournier, E.: Computer algebra - systems and
     algorithms for algebraic computation. Academic Press (1993). (Chapter 3)
 [4] Adams, W.W., Loustaunau, P.: An Introduction to Gröbner Bases.          UOK
     American Mathematical Soc. (1994).
 *)
