(* ========================================================================= *)
(* Sum-of-squares (SOS) decomposition and nonlinear real arithmetic.         *)
(*                                                                           *)
(* Ported from HOL-Light's Examples/sos.ml (BSD-2-Clause).                   *)
(*   Original author: John Harrison                                          *)
(*   Port to HOL4: Charles Cooper and Claude Opus 4.6, 2026                  *)
(* ========================================================================= *)

structure SOSLib :> SOSLib =
struct

open HolKernel Parse boolLib liteLib;
open realSyntax realTheory RealArith RealField;

val ERR = mk_HOL_ERR "SOSLib";

val sos_debugging = ref false;

(* ===================================================================== *)
(* Exact rational arithmetic via Arbrat                                  *)
(* ===================================================================== *)

type rat = Arbrat.rat;

val rat0 = Arbrat.zero;
val rat1 = Arbrat.one;
val rat_add = Arbrat.+;
val rat_sub = Arbrat.-;
val rat_mul = Arbrat.*;
val rat_div = Arbrat./;
val rat_neg = Arbrat.~;
val rat_abs = Arbrat.abs;
val rat_inv = Arbrat.inv;
val rat_lt  = Arbrat.<;
val rat_le  = Arbrat.<=;
val rat_gt  = Arbrat.>;
val rat_ge  = Arbrat.>=;

fun rat_pow (x:rat) 0 = rat1
  | rat_pow x 1 = x
  | rat_pow x n =
    let val half = rat_pow x (n div 2)
        val sq = rat_mul(half, half)
    in if n mod 2 = 0 then sq else rat_mul(x, sq)
    end;

fun rat_numer (x:rat) = Arbrat.numerator x;
fun rat_denom (x:rat) = Arbrat.denominator x;

(* LCM/GCD for rationals used in scaling *)
fun gcd_num (a:Arbnum.num) (b:Arbnum.num) : Arbnum.num =
    if b = Arbnum.zero then a
    else gcd_num b (Arbnum.mod(a, b));

fun lcm_num (a:Arbnum.num) (b:Arbnum.num) : Arbnum.num =
    if a = Arbnum.zero orelse b = Arbnum.zero then Arbnum.zero
    else Arbnum.div(Arbnum.*(a, b), gcd_num a b);

(* ===================================================================== *)
(* Sparse finite maps for monomials and polynomials                      *)
(* We use (term, int) Redblackmap for monomials (var -> power)           *)
(* and (monomial, rat) for polynomials                                   *)
(* ===================================================================== *)

(* A monomial is a map from variables (terms) to positive integer powers *)
type monomial = (term, int) Redblackmap.dict;

val mono_empty : monomial = Redblackmap.mkDict Term.compare;

(* Canonical monomial comparison for use as map keys *)
fun mono_compare (m1:monomial, m2:monomial) =
    let val l1 = Redblackmap.listItems m1
        val l2 = Redblackmap.listItems m2
        fun cmp ([], []) = EQUAL
          | cmp ([], _)  = LESS
          | cmp (_, [])  = GREATER
          | cmp ((v1,p1)::t1, (v2,p2)::t2) =
            case Term.compare(v1,v2) of
                EQUAL => (case Int.compare(p1,p2) of
                              EQUAL => cmp(t1,t2)
                            | ord => ord)
              | ord => ord
    in cmp(l1, l2)
    end;

val mono_1 : monomial = mono_empty;

fun mono_var x : monomial = Redblackmap.insert(mono_empty, x, 1);

fun mono_mul (m1:monomial) (m2:monomial) : monomial =
    Redblackmap.foldl
      (fn (v, p, acc) =>
          case Redblackmap.peek(acc, v) of
              NONE => Redblackmap.insert(acc, v, p)
            | SOME q => let val s = p + q in
                          if s = 0 then #1(Redblackmap.remove(acc, v))
                          else Redblackmap.insert(acc, v, s)
                        end)
      m1 m2;

fun mono_pow (m:monomial) 0 = mono_1
  | mono_pow m k = Redblackmap.map (fn (_, p) => k * p) m;

fun mono_degree (m:monomial) =
    Redblackmap.foldl (fn (_, p, acc) => acc + p) 0 m;

fun mono_var_degree x (m:monomial) =
    case Redblackmap.peek(m, x) of NONE => 0 | SOME p => p;

fun mono_variables (m:monomial) : term list =
    map #1 (Redblackmap.listItems m);

fun mono_is1 (m:monomial) = Redblackmap.numItems m = 0;

(* A polynomial is a map from monomials to rational coefficients *)
type poly = (monomial, rat) Redblackmap.dict;

val poly_empty : poly = Redblackmap.mkDict mono_compare;

val poly_0 : poly = poly_empty;

fun poly_isconst (p:poly) =
    Redblackmap.foldl (fn (m, _, acc) => acc andalso mono_is1 m) true p;

fun poly_const (c:rat) : poly =
    if c = rat0 then poly_0
    else Redblackmap.insert(poly_empty, mono_1, c);

fun poly_var x : poly =
    Redblackmap.insert(poly_empty, mono_var x, rat1);

fun poly_neg (p:poly) : poly =
    Redblackmap.map (fn (_, c) => rat_neg c) p;

fun poly_cmul (c:rat) (p:poly) : poly =
    if c = rat0 then poly_0
    else Redblackmap.map (fn (_, d) => rat_mul(c, d)) p;

fun poly_add (p1:poly) (p2:poly) : poly =
    Redblackmap.foldl
      (fn (m, c, acc) =>
          case Redblackmap.peek(acc, m) of
              NONE => Redblackmap.insert(acc, m, c)
            | SOME d => let val s = rat_add(c, d) in
                          if s = rat0 then #1(Redblackmap.remove(acc, m))
                          else Redblackmap.insert(acc, m, s)
                        end)
      p1 p2;

fun poly_sub p1 p2 = poly_add p1 (poly_neg p2);

fun poly_cmmul (c:rat, m:monomial) (p:poly) : poly =
    if c = rat0 then poly_0
    else
      Redblackmap.foldl
        (fn (m', d, acc) =>
            let val m'' = mono_mul m m'
                val cd = rat_mul(c, d)
            in case Redblackmap.peek(acc, m'') of
                   NONE => Redblackmap.insert(acc, m'', cd)
                 | SOME e => let val s = rat_add(cd, e) in
                               if s = rat0
                               then #1(Redblackmap.remove(acc, m''))
                               else Redblackmap.insert(acc, m'', s)
                             end
            end)
        poly_0 p;

fun poly_mul (p1:poly) (p2:poly) : poly =
    Redblackmap.foldl
      (fn (m, c, acc) => poly_add (poly_cmmul (c, m) p2) acc)
      poly_0 p1;

fun poly_square p = poly_mul p p;

fun poly_pow p 0 = poly_const rat1
  | poly_pow p 1 = p
  | poly_pow p k =
    let val q = poly_square (poly_pow p (k div 2))
    in if k mod 2 = 1 then poly_mul p q else q
    end;

fun poly_eval (p:poly) = (* evaluate at an empty assignment = constant term *)
    Redblackmap.foldl
      (fn (m, c, acc) =>
          if mono_is1 m then rat_add(acc, c) else acc)
      rat0 p;

fun degree x (p:poly) =
    Redblackmap.foldl (fn (m,_,acc) => Int.max(mono_var_degree x m, acc)) 0 p;

fun multidegree (p:poly) =
    Redblackmap.foldl (fn (m,_,acc) => Int.max(mono_degree m, acc)) 0 p;

fun poly_variables (p:poly) : term list =
    let val vs = Redblackmap.foldl
                   (fn (m,_,acc) => mono_variables m @ acc) [] p
    in HOLset.listItems (HOLset.addList(empty_tmset, vs))
    end;

fun poly_is0 (p:poly) = Redblackmap.numItems p = 0;

(* ===================================================================== *)
(* Conversion between HOL terms and polynomials                          *)
(* ===================================================================== *)

val real_ty = realSyntax.real_ty;
val zero_tm = realSyntax.zero_tm;    (* &0 *)
val neg_tm  = realSyntax.negate_tm;  (* real_neg *)
val add_tm  = realSyntax.plus_tm;    (* real_add *)
val sub_tm  = realSyntax.minus_tm;   (* real_sub *)
val mul_tm  = realSyntax.mult_tm;    (* real_mul *)
val pow_tm  = realSyntax.exp_tm;     (* real_pow *)
val inv_tm  = realSyntax.inv_tm;     (* real_inv *)
val div_tm  = realSyntax.div_tm;     (* real_div *)

fun poly_of_term tm =
    if tm ~~ zero_tm then poly_0
    else if RealArith.is_ratconst tm then
      poly_const (RealArith.rat_of_term tm)
    else if not (is_comb tm) then
      (if type_of tm = real_ty then poly_var tm
       else raise ERR "poly_of_term" "not a real term")
    else
      let val (opr, r) = dest_comb tm in
        if opr ~~ neg_tm then poly_neg (poly_of_term r)
        else if opr ~~ inv_tm then
          let val p = poly_of_term r in
            if poly_isconst p then
              let val c = poly_eval p in
                if c = rat0 then raise ERR "poly_of_term" "inv of zero"
                else poly_const (rat_inv c)
              end
            else raise ERR "poly_of_term" "inv of non-constant"
          end
        else if not (is_comb opr) then
          (if type_of tm = real_ty then poly_var tm
           else raise ERR "poly_of_term" "not a real term")
        else
          let val (op2, l) = dest_comb opr in
            if op2 ~~ pow_tm andalso numSyntax.is_numeral r then
              poly_pow (poly_of_term l) (numSyntax.dest_numeral r
                                         |> Arbnum.toInt)
            else if op2 ~~ add_tm then
              poly_add (poly_of_term l) (poly_of_term r)
            else if op2 ~~ sub_tm then
              poly_sub (poly_of_term l) (poly_of_term r)
            else if op2 ~~ mul_tm then
              poly_mul (poly_of_term l) (poly_of_term r)
            else if op2 ~~ div_tm then
              let val q = poly_of_term r in
                if poly_isconst q then
                  let val c = poly_eval q in
                    if c = rat0 then raise ERR "poly_of_term" "div by zero"
                    else poly_cmul (rat_inv c) (poly_of_term l)
                  end
                else raise ERR "poly_of_term" "div by non-constant"
              end
            else if type_of tm = real_ty then poly_var tm
            else raise ERR "poly_of_term" "not a real term"
          end
      end;

(* Convert polynomial back to HOL term *)
fun term_of_varpow x 1 = x
  | term_of_varpow x k =
    mk_comb(mk_comb(pow_tm, x), numSyntax.mk_numeral(Arbnum.fromInt k));

fun term_of_monomial (m:monomial) =
    let val items = Redblackmap.listItems m in
      case items of
          [] => realSyntax.one_tm
        | _ =>
          let val vps = map (fn (x,k) => term_of_varpow x k) items
          in List.foldl (fn (t, acc) =>
                            mk_comb(mk_comb(mul_tm, acc), t))
                        (hd vps) (tl vps)
          end
    end;

fun term_of_cmonomial (m, c:rat) =
    if mono_is1 m then RealArith.term_of_rat c
    else if c = rat1 then term_of_monomial m
    else mk_comb(mk_comb(mul_tm, RealArith.term_of_rat c),
                 term_of_monomial m);

fun term_of_poly (p:poly) =
    if poly_is0 p then zero_tm
    else
      let
        (* Sort monomials: higher degree first, then lexicographic *)
        val items = Redblackmap.listItems p
        fun cmp ((m1,_),(m2,_)) =
            case Int.compare(mono_degree m2, mono_degree m1) of
                EQUAL => mono_compare(m1, m2)
              | ord => ord
        val sorted = Listsort.sort cmp items
        val tms = map term_of_cmonomial sorted
      in
        List.foldl (fn (t, acc) =>
                       mk_comb(mk_comb(add_tm, acc), t))
                   (hd tms) (tl tms)
      end;

(* ===================================================================== *)
(* Vector and matrix operations with exact rationals                     *)
(* Vectors are 1-indexed, stored as (dim, (int,rat) map)                *)
(* Matrices are ((rows,cols), ((int*int),rat) map)                       *)
(* ===================================================================== *)

(* We use IntRedBlackMap for vectors and a custom comparison for matrices *)
structure IMap = Redblackmap;

fun int_compare (i:int, j:int) = Int.compare(i,j);
fun intpair_compare ((i1,j1):int*int, (i2,j2):int*int) =
    case Int.compare(i1,i2) of EQUAL => Int.compare(j1,j2) | ord => ord;

type vector = int * (int, rat) IMap.dict;
type matrix = (int * int) * ((int * int), rat) IMap.dict;

val imap_empty = IMap.mkDict int_compare;
val mmap_empty = IMap.mkDict intpair_compare;

fun vec_dim ((n, _):vector) = n;

fun vec_el ((_, m):vector) i =
    case IMap.peek(m, i) of NONE => rat0 | SOME c => c;

fun vec_0 n : vector = (n, imap_empty);

fun vec_cmul c ((n, m):vector) : vector =
    if c = rat0 then vec_0 n
    else (n, IMap.map (fn (_, x) => rat_mul(c, x)) m);

fun vec_of_list l : vector =
    let val n = length l
    in (n, #2 (List.foldl (fn (c, (i, m)) =>
                              if c = rat0 then (i+1, m)
                              else (i+1, IMap.insert(m, i, c)))
                          (1, imap_empty) l))
    end;

(* Matrix operations *)
fun mat_dims ((d, _):matrix) = d;

fun mat_el ((_, m):matrix) (i,j) =
    case IMap.peek(m, (i,j)) of NONE => rat0 | SOME c => c;

fun mat_0 (r,c) : matrix = ((r,c), mmap_empty);

fun mat_neg (((r,c), m):matrix) : matrix =
    ((r,c), IMap.map (fn (_, x) => rat_neg x) m);

fun mat_cmul k (((r,c), m):matrix) : matrix =
    if k = rat0 then mat_0 (r,c)
    else ((r,c), IMap.map (fn (_, x) => rat_mul(k, x)) m);

fun mat_add (((r1,c1), m1):matrix) (((r2,c2), m2):matrix) : matrix =
    if r1 <> r2 orelse c1 <> c2
    then raise ERR "mat_add" "incompatible dimensions"
    else ((r1,c1),
          IMap.foldl
            (fn (ij, c, acc) =>
                case IMap.peek(acc, ij) of
                    NONE => IMap.insert(acc, ij, c)
                  | SOME d => let val s = rat_add(c,d) in
                                if s = rat0 then #1(IMap.remove(acc, ij))
                                else IMap.insert(acc, ij, s)
                              end)
            m1 m2);

fun mat_row k (((r,c), m):matrix) : vector =
    (c, IMap.foldl
          (fn ((i,j), v, acc) =>
              if i = k then IMap.insert(acc, j, v) else acc)
          imap_empty m);

fun mat_is0 (((_, _), m):matrix) = IMap.numItems m = 0;

(* ===================================================================== *)
(* Newton polytope and convex hull                                       *)
(* ===================================================================== *)

(* Test if point pt is in the convex hull of pts using CSDP.
   Rather than computational geometry, express as LP and call CSDP.
   This is the HOL-Light approach — lazy but effective. *)

(* For environments without CSDP, use a simple fallback:
   just return all monomials up to half-degree *)

fun all_monomials_upto vars ds =
    case (vars, ds) of
        ([], _) => [mono_1]
      | (_, []) => [mono_1]
      | (v::vs, d::dds) =>
        List.concat
          (List.tabulate(d+1, fn k =>
             map (fn m => if k = 0 then m
                          else Redblackmap.insert(m, v, k))
                 (all_monomials_upto vs dds)));

(* Newton polytope: monomials m s.t. 2*m is in the convex hull of
   the monomials of pol. We approximate by taking monomials whose
   total degree is at most half the total degree of pol, AND whose
   per-variable degree is at most half the per-variable degree in pol. *)
fun newton_polytope (pol:poly) =
    let val vars = poly_variables pol
        val half_total = (multidegree pol + 1) div 2
        val ds = map (fn x => (degree x pol + 1) div 2) vars
        val all = all_monomials_upto vars ds
        (* Filter by total degree *)
        val filtered = List.filter (fn m => mono_degree m <= half_total) all
    in rev filtered
    end;

(* ===================================================================== *)
(* Equation elimination (Gaussian elimination for parametric equations)   *)
(* ===================================================================== *)

(* An "equation" is a map from variables to rational coefficients.
   Variables are (int*int) pairs representing Gram matrix entries,
   plus a special pseudo-variable (0,0) for the constant. *)

type eqvar = int * int;

fun eqvar_compare ((a1,b1):eqvar, (a2,b2):eqvar) =
    case Int.compare(a1,a2) of EQUAL => Int.compare(b1,b2) | ord => ord;

type equation = (eqvar, rat) Redblackmap.dict;
val eq_empty : equation = Redblackmap.mkDict eqvar_compare;

fun eq_cmul (c:rat) (eq:equation) : equation =
    if c = rat0 then eq_empty
    else Redblackmap.map (fn (_, d) => rat_mul(c, d)) eq;

fun eq_add (eq1:equation) (eq2:equation) : equation =
    Redblackmap.foldl
      (fn (v, c, acc) =>
          case Redblackmap.peek(acc, v) of
              NONE => Redblackmap.insert(acc, v, c)
            | SOME d => let val s = rat_add(c, d) in
                          if s = rat0 then #1(Redblackmap.remove(acc, v))
                          else Redblackmap.insert(acc, v, s)
                        end)
      eq1 eq2;

fun eq_eval (assig: eqvar -> rat) (eq:equation) : rat =
    Redblackmap.foldl (fn (v, c, acc) => rat_add(acc, rat_mul(assig v, c)))
      rat0 eq;

fun eq_is0 (eq:equation) = Redblackmap.numItems eq = 0;

fun eq_peek (eq:equation) v = Redblackmap.peek(eq, v);

fun eq_remove v (eq:equation) =
    #1(Redblackmap.remove(eq, v)) handle NotFound => eq;

fun eq_vars (eq:equation) = map #1 (Redblackmap.listItems eq);

(* Eliminate all variables from a system of equations.
   Returns (free_vars, assignment) where assignment maps
   eliminated vars to equations in terms of free vars. *)
fun eliminate_all_equations (one:eqvar) (eqs: equation list)
    : eqvar list * (eqvar, equation) Redblackmap.dict =
    let
      fun choose_variable (eq:equation) =
          let val items = Redblackmap.listItems eq in
            case items of
                [] => raise ERR "choose_variable" "empty equation"
              | [(v,_)] => if eqvar_compare(v, one) = EQUAL
                           then raise ERR "choose_variable" "only constant"
                           else v
              | (v,_)::_ =>
                if eqvar_compare(v, one) = EQUAL then #1(List.nth(items, 1))
                else v
          end
      val assig_empty = Redblackmap.mkDict eqvar_compare
      fun elim dun [] = dun
        | elim dun (eq::oeqs) =
          if eq_is0 eq then elim dun oeqs
          else
            let
              val v = choose_variable eq
              val a = case eq_peek eq v of
                          SOME c => c
                        | NONE => raise ERR "eliminate" "impossible"
              val eq' = eq_cmul (rat_div(rat_neg rat1, a)) (eq_remove v eq)
              fun subst_in (e:equation) : equation =
                  case eq_peek e v of
                      NONE => e
                    | SOME b =>
                      eq_add (eq_remove v e)
                             (eq_cmul (rat_div(rat_neg b, a)) (eq_remove v eq))
              val dun' = Redblackmap.insert(
                           Redblackmap.map (fn (_, f) => subst_in f) dun,
                           v, eq')
            in
              elim dun' (map subst_in oeqs)
            end
      val assig = elim assig_empty eqs
      val vs = Redblackmap.foldl
                 (fn (_, f, acc) =>
                     let val fvs = List.filter
                                     (fn v => eqvar_compare(v, one) <> EQUAL)
                                     (eq_vars f)
                     in fvs @ acc
                     end)
                 [] assig
      val vs' = Lib.mk_set (Listsort.sort eqvar_compare vs)
    in (vs', assig)
    end;

(* Solve equations: set free vars to 0, evaluate *)
fun solve_equations (one:eqvar) (eqs: equation list) =
    let
      val (free_vars, assig) = eliminate_all_equations one eqs
      (* Map: free vars -> 0, 'one' -> -1 *)
      val vfn = fn v => if eqvar_compare(v, one) = EQUAL then rat_neg rat1
                        else rat0
      val result = Redblackmap.map (fn (_, eq) => eq_eval vfn eq) assig
      (* Also add free vars -> 0 *)
      val result' = List.foldl
                      (fn (v, acc) => Redblackmap.insert(acc, v, rat0))
                      result free_vars
      (* Verify *)
      val lookup = fn v => case Redblackmap.peek(result', v) of
                               NONE => if eqvar_compare(v, one) = EQUAL
                                       then rat_neg rat1 else rat0
                             | SOME c => c
      val ok = List.all (fn eq => eq_eval lookup eq = rat0) eqs
    in
      if ok then result'
      else raise ERR "solve_equations" "sanity check failed"
    end;

(* ===================================================================== *)
(* Cholesky / LDU diagonalization                                        *)
(* ===================================================================== *)

(* Given a PSD matrix, compute its LDL^T decomposition:
   returns list of (diagonal_entry, row_vector) pairs *)
fun diag (mat : matrix) =
    let
      val (n, _) = mat_dims mat
      fun go i m =
          if mat_is0 m then []
          else if i > n then []
          else
            let val a_ii = mat_el m (i,i) in
              if rat_lt(a_ii, rat0) then
                raise ERR "diag" "matrix not PSD"
              else if a_ii = rat0 then
                (* Check row is zero *)
                let val row_i = mat_row i m in
                  if IMap.numItems (#2 row_i) = 0 then go (i+1) m
                  else raise ERR "diag" "matrix not PSD (zero pivot, nonzero row)"
                end
              else
                let
                  val row_i = mat_row i m
                  (* v' = row / a_ii *)
                  val v' = vec_cmul (rat_inv a_ii) row_i
                  (* Update: m'[j,k] = m[j,k] - m[j,i]*v'[k] for j,k > i *)
                  val acc = ref mmap_empty
                  val _ =
                    List.app (fn j =>
                      List.app (fn k =>
                        let val v =
                              rat_sub(mat_el m (j,k),
                                      rat_mul(vec_el row_i j,
                                              vec_el v' k))
                        in if v <> rat0
                           then acc := IMap.insert(!acc, (j,k), v)
                           else ()
                        end)
                      (List.tabulate(n - i, fn x => x + i + 1)))
                    (List.tabulate(n - i, fn x => x + i + 1))
                  val new_m = ((n,n), !acc)
                in (a_ii, v') :: go (i+1) new_m
                end
            end
    in go 1 mat
    end;

(* Adjust diagonalization to have integer-like coefficients:
   scale each row so coefficients are integers, collect the scaling *)
fun deration (d : (rat * vector) list) =
    if null d then (rat0, d)
    else
      let
        fun adj (c, (n, m) : vector) =
            let
              (* Find LCM of denominators and GCD of numerators *)
              val lcd = IMap.foldl
                          (fn (_, v, acc) => lcm_num acc (rat_denom v))
                          (Arbnum.fromInt 1) m
              val gcn = IMap.foldl
                          (fn (_, v, acc) =>
                              gcd_num acc (Arbint.toNat(Arbint.abs(rat_numer v))))
                          Arbnum.zero m
              val gcn' = if gcn = Arbnum.zero then Arbnum.fromInt 1 else gcn
              val a = Arbrat.fromNat(Arbnum.div(lcd, gcn'))
              val a_sq = rat_mul(a, a)
            in (rat_div(c, a_sq),
                (n, IMap.map (fn (_, x) => rat_mul(a, x)) m))
            end
        val d' = map adj d
        (* Now find overall scaling *)
        val overall_lcd =
            List.foldl (fn ((c,_), acc) => lcm_num acc (rat_denom c))
                       (Arbnum.fromInt 1) d'
        val overall_gcn =
            List.foldl (fn ((c,_), acc) =>
                           gcd_num acc (Arbint.toNat(Arbint.abs(rat_numer c))))
                       Arbnum.zero d'
        val overall_gcn' = if overall_gcn = Arbnum.zero
                           then Arbnum.fromInt 1 else overall_gcn
        val a = rat_div(Arbrat.fromNat overall_lcd,
                        Arbrat.fromNat overall_gcn')
      in
        (rat_inv a,
         map (fn (c, l) => (rat_mul(a, c), l)) d')
      end;

(* ===================================================================== *)
(* CSDP interface                                                        *)
(* ===================================================================== *)

(* Decimalize a rational number for SDPA format output.
   We convert to a floating-point string with sufficient precision. *)
(* Convert SML real string to C-style (replace ~ with -) *)
fun sml_to_c_float s =
    String.translate (fn #"~" => "-" | c => String.str c) s;

fun decimalize (_:int) (x:rat) : string =
    if x = rat0 then "0.0"
    else
      let
        val n = Arbint.toInt(Arbrat.numerator x)
        val d = Arbnum.toInt(Arbrat.denominator x)
        val r = Real.fromInt n / Real.fromInt d
      in sml_to_c_float (Real.fmt (StringCvt.SCI (SOME 18)) r)
      end
      handle Overflow =>
        let val s = Arbrat.toString x
        in case Real.fromString s of
               SOME r => sml_to_c_float (Real.fmt (StringCvt.SCI (SOME 18)) r)
             | NONE => raise ERR "decimalize"
                         ("cannot convert to float: " ^ s)
        end;

(* Write SDPA-sparse format for a single-block SDP problem.
   Format:
     "comment"
     m          (number of constraint matrices = length mats - 1)
     1          (number of blocks)
     n          (block size)
     c1 c2 ...  (objective vector, m entries)
     matno blkno i j value   (sparse matrix entries, upper triangle)
   Matrix 0 is the constant matrix (negated RHS), matrices 1..m are constraints.
*)
fun sdpa_of_problem (obj:vector) (mats : matrix list) =
    let
      val m = length mats - 1
      val (n, _) = mat_dims (hd mats)
      fun fmt_entry matno ((_, mm):matrix) =
          let val ents = IMap.foldl
                (fn ((i,j), c, acc) =>
                    if i > j then acc else (i,j,c)::acc)
                [] mm
              val sorted = Listsort.sort
                (fn ((i1,j1,_),(i2,j2,_)) =>
                    case Int.compare(i1,i2) of
                        EQUAL => Int.compare(j1,j2) | ord => ord)
                ents
          in String.concat
               (map (fn (i,j,c) =>
                        Int.toString matno ^ " 1 " ^
                        Int.toString i ^ " " ^ Int.toString j ^ " " ^
                        decimalize 20 c ^ "\n")
                    sorted)
          end
    in
      "\"SOS\"\n" ^
      Int.toString m ^ "\n" ^
      "1\n" ^
      Int.toString n ^ "\n" ^
      String.concatWith " "
        (List.tabulate(m, fn i =>
           decimalize 20 (vec_el obj (i+1)))) ^ "\n" ^
      String.concat
        (List.tabulate(length mats, fn k =>
           fmt_entry k (List.nth(mats, k))))
    end;

(* Parse CSDP output: a single line of space-separated decimals.
   CSDP writes the dual solution y as a single line. *)
fun parse_csdp_output (s:string) : vector =
    let
      val lines = String.tokens (fn c => c = #"\n") s
      val first_line = if null lines then ""
                       else hd lines
      val tokens = String.tokens Char.isSpace first_line
      val tokens' = List.filter (fn t => t <> "") tokens
      fun real_to_rat r =
          (* Convert float to rational: use 10^15 precision *)
          let val scale = 1000000000000000.0
              val n = Real.toLargeInt IEEEReal.TO_NEAREST (r * scale)
              val scale_int = Real.toLargeInt IEEEReal.TO_NEAREST scale
          in rat_div(Arbrat.fromAInt(Arbint.fromLargeInt n),
                     Arbrat.fromAInt(Arbint.fromLargeInt scale_int))
          end
      fun parse_tok tok =
          case Real.fromString tok of
              NONE => rat0
            | SOME r => real_to_rat r
      val vals = map parse_tok tokens'
    in vec_of_list vals
    end;

(* Find CSDP binary.
   Checks HOL4_CSDP_EXECUTABLE env var first, then tries "csdp" in PATH. *)
(* Safe file I/O with guaranteed resource cleanup *)
fun with_out_file path f =
    let val os = TextIO.openOut path
    in (f os before TextIO.closeOut os)
       handle e => (TextIO.closeOut os; raise e)
    end;

fun with_in_file path f =
    let val is = TextIO.openIn path
    in (f is before TextIO.closeIn is)
       handle e => (TextIO.closeIn is; raise e)
    end;

fun find_csdp () =
    case OS.Process.getEnv "HOL4_CSDP_EXECUTABLE" of
        SOME p => SOME p
      | NONE =>
        let val result = OS.Process.system "which csdp > /dev/null 2>&1"
        in if OS.Process.isSuccess result then SOME "csdp"
           else NONE
        end;

(* Round a vector to "nice" rationals *)
(* Round x to nearest multiple of 1/n *)
fun nice_rational n (x:rat) =
    let val nx = rat_mul(n, x)
        val f = Arbrat.floor nx
        val c = Arbrat.ceil nx
        val diff_f = rat_abs(rat_sub(nx, Arbrat.fromAInt f))
        val diff_c = rat_abs(rat_sub(nx, Arbrat.fromAInt c))
        val rounded = if rat_le(diff_f, diff_c) then f else c
    in rat_div(Arbrat.fromAInt rounded, n)
    end;

fun nice_vector n ((dim, vm):vector) : vector =
    (dim, IMap.map (fn (_, x) => nice_rational n x) vm);

(* Run CSDP on an SDP problem, return the dual vector.
   CSDP syntax: csdp <input.dat-s> <output.sol>
   Return code: 0=success, 1/2=infeasible, 3=reduced accuracy *)
fun run_csdp (obj:vector) (mats:matrix list) : vector =
    case find_csdp () of
        NONE => raise ERR "run_csdp" "CSDP not found"
      | SOME csdp_bin =>
    let
      val input_file = OS.FileSys.tmpName () ^ ".dat-s"
      val output_file = input_file ^ ".out"
      val params_file = input_file ^ ".params"

      (* Write SDPA-format input *)
      val sdpa = sdpa_of_problem obj mats
      val _ = with_out_file input_file (fn os => TextIO.output(os, sdpa))

      (* Write CSDP params (printlevel=0 for quiet) *)
      val params = "axtol=1.0e-8\natytol=1.0e-8\nobjtol=1.0e-8\n" ^
                   "pinftol=1.0e8\ndinftol=1.0e8\nmaxiter=100\n" ^
                   "minstepfrac=0.9\nmaxstepfrac=0.97\n" ^
                   "minstepp=1.0e-8\nminstepd=1.0e-8\n" ^
                   "usexzgap=1\ntweakgap=0\naffine=0\nprintlevel=0\n"
      val _ = with_out_file params_file (fn os => TextIO.output(os, params))

      (* Run CSDP *)
      val cmd = csdp_bin ^ " " ^ input_file ^ " " ^ output_file ^
                " > /dev/null 2>&1"
      val _ = if !sos_debugging then print ("CSDP: " ^ cmd ^ "\n") else ()
      val _ = OS.Process.system cmd

      (* Parse output — CSDP writes dual y vector on first line *)
      val op_str = with_in_file output_file TextIO.inputAll
                   handle IO.Io _ => ""
      val res = parse_csdp_output op_str

      (* Debug: show raw result *)
      val _ = if !sos_debugging then
                let val d = vec_dim res in
                  print ("CSDP: got " ^ Int.toString d ^ " dual values\n")
                end
              else ()

      (* Cleanup temp files *)
      val _ = (OS.FileSys.remove input_file;
               OS.FileSys.remove output_file;
               OS.FileSys.remove params_file) handle OS.SysErr _ => ()
    in
      if vec_dim res = 0 then
        raise ERR "run_csdp" "CSDP produced no output (problem may be infeasible)"
      else res
    end;

(* ===================================================================== *)
(* Pure SOS: sumofsquares via exact arithmetic (no external tools)       *)
(* ===================================================================== *)

(* Build the Gram matrix equations for p = m^T G m where m is the
   monomial basis. Returns list of equations, one per monomial of p. *)
fun gram_equations (pol:poly) (mons:monomial list) =
    let
      val n = length mons
      val indexed_mons = ListPair.zip(mons, List.tabulate(n, fn i => i+1))
      (* For each pair (i,j) with i<=j, the Gram entry G[i,j] contributes
         to monomial mons[i]*mons[j] with coefficient 1 (if i=j) or 2 *)
      val eqs_map = ref (Redblackmap.mkDict mono_compare
                         : (monomial, equation) Redblackmap.dict)
      fun get_eq m = case Redblackmap.peek(!eqs_map, m) of
                         SOME eq => eq | NONE => eq_empty
      fun set_eq m eq = eqs_map := Redblackmap.insert(!eqs_map, m, eq)
      val _ =
        List.app (fn (m1, i) =>
          List.app (fn (m2, j) =>
            if i > j then ()
            else
              let val m = mono_mul m1 m2
                  val c = if i = j then rat1 else Arbrat.fromInt 2
                  val eq = get_eq m
                  val eq' = Redblackmap.insert(eq, (i,j), c)
              in set_eq m eq'
              end)
          indexed_mons)
        indexed_mons

      (* Add the constant terms from pol.
         Convention: pseudo-variable (0,0) evaluates to -1 in solve_equations.
         We want: sum(G[i,j]*coeff) + entry*(−1) = 0 ⟹ sum(G[i,j]*coeff) = entry
         For the equation to give sum(...) = c (coeff of pol at monomial m),
         we need entry = c, so that c*(−1) makes sum(...) − c = 0 ⟹ sum(...) = c.
         But wait: c*(-1) = -c, so sum(...) + (-c) = 0 ⟹ sum(...) = c. YES.
         So we add (0,0) |-> c (the positive coefficient). *)
      val _ =
        Redblackmap.app
          (fn (m, c) =>
              let val eq = get_eq m
                  val eq' = Redblackmap.insert(eq, (0,0), c)
              in set_eq m eq'
              end)
          pol

      val eqs = map #2 (Redblackmap.listItems (!eqs_map))
    in eqs
    end;

(* Build polynomial from vector: sum_i vec[i] * mons[i-1] *)
fun poly_of_lin (mons:monomial list) ((_, vm):vector) : poly =
    IMap.foldl
      (fn (i, c, acc) =>
          if c = rat0 then acc
          else let val m = List.nth(mons, i-1)
               in poly_add acc (Redblackmap.insert(poly_empty, m, c))
               end)
      poly_0 vm;

(* The main pure SOS function: try to decompose pol as a sum of squares
   using exact rational arithmetic only. *)
fun sumofsquares_pure (pol:poly) : rat * (rat * poly) list =
    let
      val mons = newton_polytope pol
      val n = length mons
      val _ = if !sos_debugging then
                print ("SOS: " ^ Int.toString n ^ " monomials in basis\n")
              else ()
      val eqs = gram_equations pol mons
      (* Solve the linear system *)
      val solution = solve_equations (0,0) eqs
      (* Build the Gram matrix *)
      fun build_gram () : matrix =
          let val entries = ref mmap_empty
              fun set (i,j) v =
                  if v <> rat0 then
                    (entries := IMap.insert(!entries, (i,j), v);
                     entries := IMap.insert(!entries, (j,i), v))
                  else ()
          in
            List.app (fn i =>
              List.app (fn j =>
                if i > j then ()
                else
                  let val v = case Redblackmap.peek(solution, (i,j)) of
                                  SOME c => c | NONE => rat0
                  in set (i,j) v
                  end)
              (List.tabulate(n, fn x => x+1)))
            (List.tabulate(n, fn x => x+1));
            ((n,n), !entries)
          end
      val gram = build_gram ()
      (* Diagonalize *)
      val dia = diag gram
      (* Adjust to nice form *)
      val (rat_factor, dia') = deration dia
      val lins = map (fn (d, v) => (d, poly_of_lin mons v)) dia'
      (* Sanity check: verify the decomposition equals the polynomial *)
      val sqs = map (fn (d,l) => poly_mul (poly_const d) (poly_square l)) lins
      val sos = poly_cmul rat_factor
                  (List.foldl (fn (p,a) => poly_add a p) poly_0 sqs)
      val residual = poly_sub sos pol
    in
      if poly_is0 residual then (rat_factor, lins)
      else raise ERR "sumofsquares_pure" "sanity check failed"
    end;

(* ===================================================================== *)
(* Full SOS via CSDP (with rounding to exact rational certificate)       *)
(* ===================================================================== *)

fun sumofsquares_csdp (pol:poly) : rat * (rat * poly) list =
    let
      val mons = newton_polytope pol
      val n = length mons
      val _ = if !sos_debugging then
                print ("SOS/CSDP: " ^ Int.toString n ^ " monomials in basis\n")
              else ()
      val eqs = gram_equations pol mons
      (* Eliminate equations to get free variables *)
      val (pvs, assig) = eliminate_all_equations (0,0) eqs
      val _ = if !sos_debugging then
                print ("SOS/CSDP: " ^ Int.toString (length pvs) ^
                       " free variables\n")
              else ()
    in
      if null pvs then
        (* No free variables — direct solve like pure SOS *)
        let
          (* All variables are determined. Augment assignment with identity
             for free vars (none) and build the single matrix. *)
          val allassig = assig
          fun mk_matrix v : matrix =
              let val entries = ref mmap_empty
              in Redblackmap.app
                   (fn (ij as (i,j), eq) =>
                       if i < 1 orelse j < 1 then ()
                       else
                         let val c = case Redblackmap.peek(eq, v) of
                                         SOME r => r | NONE => rat0
                         in if c <> rat0 then
                              (entries := IMap.insert(!entries, (i,j), c);
                               if i <> j then
                                 entries := IMap.insert(!entries, (j,i), c)
                               else ())
                            else ()
                         end)
                   allassig;
                 ((n,n), !entries)
              end
          val mat = mat_neg (mk_matrix (0,0))
          val (rat_factor, dia) = deration (diag mat)
          val lins = map (fn (d, v) => (d, poly_of_lin mons v)) dia
        in (rat_factor, lins)
        end
      else
        let
          (* Build the parametric matrices for CSDP.
             allassig maps each Gram entry (i,j) to a linear expression
             in the free variables pvs and the constant (0,0). *)
          val allassig =
              List.foldl
                (fn (v, acc) =>
                    Redblackmap.insert(acc, v,
                      Redblackmap.insert(eq_empty, v, rat1)))
                assig pvs

          (* For each variable v, build the matrix M_v where
             M_v[i,j] = coefficient of v in allassig[(i,j)] *)
          fun mk_matrix v : matrix =
              let val entries = ref mmap_empty
              in Redblackmap.app
                   (fn ((i,j), eq) =>
                       if i < 1 orelse j < 1 then ()
                       else
                         let val c = case Redblackmap.peek(eq, v) of
                                         SOME r => r | NONE => rat0
                         in if c <> rat0 then
                              (entries := IMap.insert(!entries, (i,j), c);
                               if i <> j then
                                 entries := IMap.insert(!entries, (j,i), c)
                               else ())
                            else ()
                         end)
                   allassig;
                 ((n,n), !entries)
              end

          (* Objective: maximize trace. For each free variable v_k,
             the objective coefficient is the sum of coefficients of v_k
             in diagonal entries allassig[(i,i)] for i=1..n *)
          val diagents =
              List.foldl
                (fn (i, acc) =>
                    case Redblackmap.peek(allassig, (i,i)) of
                        SOME e => eq_add acc e
                      | NONE => acc)
                eq_empty (List.tabulate(n, fn i => i+1))

          val _ = if !sos_debugging then
                    print "SOS/CSDP: building matrices...\n"
                  else ()
          val qvars = (0,0) :: pvs
          val mats = map mk_matrix qvars
          val obj_coeffs =
              map (fn v =>
                      case Redblackmap.peek(diagents, v) of
                          SOME c => c | NONE => rat0)
                  pvs
          val obj = vec_of_list obj_coeffs

          (* Call CSDP to get the dual vector *)
          val _ = if !sos_debugging then
                    print ("SOS/CSDP: calling CSDP with " ^
                           Int.toString (length mats) ^ " matrices\n")
                  else ()
          val raw_vec = run_csdp obj mats
          val _ = if !sos_debugging then
                    print "SOS/CSDP: CSDP returned, building rounding\n"
                  else ()

          (* Try rounding at various precisions *)
          fun find_rounding d =
              let
                val _ = if !sos_debugging then
                          print ("SOS/CSDP: rounding with d=" ^
                                 Arbrat.toString d ^ "\n")
                        else ()
                val vec = nice_vector d raw_vec
                (* Build: mat = -M_0 + sum_i v_i * M_i *)
                val mat = List.foldl
                  (fn (i, acc) =>
                      mat_add acc
                        (mat_cmul (vec_el vec i)
                                  (List.nth(mats, i))))
                  (mat_neg (hd mats))
                  (List.tabulate(length pvs, fn i => i+1))
              in deration (diag mat)
              end

          val rounding_vals =
              (List.tabulate(31, fn i => Arbrat.fromInt (i+1))) @
              (List.tabulate(62, fn i => rat_pow (Arbrat.fromInt 2) (i+5)))

          fun try_roundings [] =
              raise ERR "sumofsquares_csdp" "rounding failed at all precisions"
            | try_roundings (d::ds) =
              find_rounding d
              handle HOL_ERR _ => try_roundings ds

          val _ = if !sos_debugging then
                    (print ("SOS/CSDP: built " ^ Int.toString (length mats) ^
                           " matrices, obj dim=" ^
                           Int.toString (vec_dim obj) ^ "\n");
                     print "SOS/CSDP: starting rounding loop\n")
                  else ()
          (* Debug: check dimensions *)
          val _ = if vec_dim raw_vec <> length pvs then
                    (if !sos_debugging then
                       print ("SOS/CSDP WARNING: vec dim " ^
                              Int.toString (vec_dim raw_vec) ^
                              " != pvs " ^ Int.toString (length pvs) ^ "\n")
                     else ())
                  else ()
          val (rat_factor, dia) = try_roundings rounding_vals
          val _ = if !sos_debugging then
                    print ("SOS/CSDP: rounding succeeded, " ^
                           Int.toString (length dia) ^ " terms\n")
                  else ()

          (* Convert diagonalization to polynomial form *)
          val lins = map (fn (d, v) => (d, poly_of_lin mons v)) dia

          (* Sanity check *)
          val sqs = map (fn (d,l) => poly_mul (poly_const d) (poly_square l))
                        lins
          val sos = poly_cmul rat_factor
                      (List.foldl (fn (p, acc) => poly_add acc p) poly_0 sqs)
          val residual = poly_sub sos pol
        in
          if poly_is0 residual then (rat_factor, lins)
          else raise ERR "sumofsquares_csdp" "sanity check failed"
        end
    end;

(* Main SOS function — tries pure first, then CSDP *)
fun sumofsquares (pol:poly) : rat * (rat * poly) list =
    sumofsquares_pure pol
    handle HOL_ERR _ =>
      (if !sos_debugging then
         print "SOS: pure failed, trying CSDP path\n"
       else ();
       sumofsquares_csdp pol);

(* ===================================================================== *)
(* Block-diagonal SOS: 3-tuple eqvars and multi-block CSDP               *)
(* For Positivstellensatz certificate search with hypotheses.            *)
(* ===================================================================== *)

(* 3-tuple eqvar: (block, row, col) *)
type eqvar3 = int * int * int;

fun eqvar3_compare ((a1,b1,c1):eqvar3, (a2,b2,c2):eqvar3) =
    case Int.compare(a1,a2) of
        EQUAL => (case Int.compare(b1,b2) of
                      EQUAL => Int.compare(c1,c2)
                    | ord => ord)
      | ord => ord;

type equation3 = (eqvar3, rat) Redblackmap.dict;
val eq3_empty : equation3 = Redblackmap.mkDict eqvar3_compare;

fun eq3_cmul (c:rat) (eq:equation3) : equation3 =
    if c = rat0 then eq3_empty
    else Redblackmap.map (fn (_, d) => rat_mul(c, d)) eq;

fun eq3_add (eq1:equation3) (eq2:equation3) : equation3 =
    Redblackmap.foldl
      (fn (v, c, acc) =>
          case Redblackmap.peek(acc, v) of
              NONE => Redblackmap.insert(acc, v, c)
            | SOME d => let val s = rat_add(c, d) in
                          if s = rat0 then #1(Redblackmap.remove(acc, v))
                          else Redblackmap.insert(acc, v, s)
                        end)
      eq1 eq2;

fun eq3_eval (assig: eqvar3 -> rat) (eq:equation3) : rat =
    Redblackmap.foldl (fn (v, c, acc) => rat_add(acc, rat_mul(assig v, c)))
      rat0 eq;

fun eq3_is0 (eq:equation3) = Redblackmap.numItems eq = 0;

fun eq3_peek (eq:equation3) v = Redblackmap.peek(eq, v);

fun eq3_remove v (eq:equation3) =
    #1(Redblackmap.remove(eq, v)) handle NotFound => eq;

fun eq3_vars (eq:equation3) = map #1 (Redblackmap.listItems eq);

(* Eliminate all variables from a system of equations (3-tuple version) *)
fun eliminate_all_equations3 (one:eqvar3) (eqs: equation3 list)
    : eqvar3 list * (eqvar3, equation3) Redblackmap.dict =
    let
      fun choose_variable (eq:equation3) =
          let val items = Redblackmap.listItems eq in
            case items of
                [] => raise ERR "choose_variable3" "empty equation"
              | [(v,_)] => if eqvar3_compare(v, one) = EQUAL
                           then raise ERR "choose_variable3" "only constant"
                           else v
              | (v,_)::_ =>
                if eqvar3_compare(v, one) = EQUAL then #1(List.nth(items, 1))
                else v
          end
      val assig_empty = Redblackmap.mkDict eqvar3_compare
      fun elim dun [] = dun
        | elim dun (eq::oeqs) =
          if eq3_is0 eq then elim dun oeqs
          else
            let
              val v = choose_variable eq
              val a = case eq3_peek eq v of
                          SOME c => c
                        | NONE => raise ERR "eliminate3" "impossible"
              val eq' = eq3_cmul (rat_div(rat_neg rat1, a)) (eq3_remove v eq)
              fun subst_in (e:equation3) : equation3 =
                  case eq3_peek e v of
                      NONE => e
                    | SOME b =>
                      eq3_add (eq3_remove v e)
                             (eq3_cmul (rat_div(rat_neg b, a)) (eq3_remove v eq))
              val dun' = Redblackmap.insert(
                           Redblackmap.map (fn (_, f) => subst_in f) dun,
                           v, eq')
            in
              elim dun' (map subst_in oeqs)
            end
      val assig = elim assig_empty eqs
      val vs = Redblackmap.foldl
                 (fn (_, f, acc) =>
                     let val fvs = List.filter
                                     (fn v => eqvar3_compare(v, one) <> EQUAL)
                                     (eq3_vars f)
                     in fvs @ acc
                     end)
                 [] assig
      val vs' = Lib.mk_set (Listsort.sort eqvar3_compare vs)
    in (vs', assig)
    end;

(* ===================================================================== *)
(* Block-diagonal CSDP format                                            *)
(* ===================================================================== *)

(* 3D matrix type: (block, row, col) -> rat *)
type bmatrix = (eqvar3, rat) Redblackmap.dict;
val bmat_empty : bmatrix = Redblackmap.mkDict eqvar3_compare;

fun bmatrix_add (m1:bmatrix) (m2:bmatrix) : bmatrix =
    Redblackmap.foldl
      (fn (k, c, acc) =>
          case Redblackmap.peek(acc, k) of
              NONE => Redblackmap.insert(acc, k, c)
            | SOME d => let val s = rat_add(c, d) in
                          if s = rat0 then #1(Redblackmap.remove(acc, k))
                          else Redblackmap.insert(acc, k, s)
                        end)
      m1 m2;

fun bmatrix_cmul (c:rat) (bm:bmatrix) : bmatrix =
    if c = rat0 then bmat_empty
    else Redblackmap.map (fn (_, x) => rat_mul(c, x)) bm;

fun bmatrix_neg bm = bmatrix_cmul (rat_neg rat1) bm;

(* SDPA-sparse for block diagonal matrix *)
fun sdpa_of_blockdiagonal matno (bm:bmatrix) =
    let val pfx = Int.toString matno ^ " "
        val ents = Redblackmap.foldl
          (fn ((b,i,j), c, acc) =>
              if i > j then acc else ((b,i,j),c)::acc)
          [] bm
        val sorted = Listsort.sort
          (fn (((b1,i1,j1),_),((b2,i2,j2),_)) =>
              case Int.compare(b1,b2) of
                  EQUAL => (case Int.compare(i1,i2) of
                                EQUAL => Int.compare(j1,j2) | o2 => o2)
                | o1 => o1)
          ents
    in String.concat
         (map (fn ((b,i,j),c) =>
                  pfx ^ Int.toString b ^ " " ^
                  Int.toString i ^ " " ^ Int.toString j ^ " " ^
                  decimalize 20 c ^ "\n")
              sorted)
    end;

fun sdpa_of_blockproblem nblocks blocksizes (obj:vector) (mats:bmatrix list) =
    let val m = length mats - 1
    in "\"SOS\"\n" ^
       Int.toString m ^ "\n" ^
       Int.toString nblocks ^ "\n" ^
       String.concatWith " " (map Int.toString blocksizes) ^ "\n" ^
       String.concatWith " "
         (List.tabulate(m, fn i =>
            decimalize 20 (vec_el obj (i+1)))) ^ "\n" ^
       String.concat
         (List.tabulate(length mats, fn k =>
            sdpa_of_blockdiagonal k (List.nth(mats, k))))
    end;

(* Smash block matrix into per-block 2D matrices *)
fun blocks (blocksizes:int list) (bm:bmatrix) : matrix list =
    let val indexed = ListPair.zip(blocksizes,
                                   List.tabulate(length blocksizes, fn i => i+1))
    in map (fn (bs, b0) =>
         let val m = Redblackmap.foldl
               (fn ((b,i,j), c, acc) =>
                   if b = b0 then IMap.insert(acc, (i,j), c) else acc)
               mmap_empty bm
         in ((bs,bs), m) : matrix
         end)
       indexed
    end;

(* Run CSDP on a block-diagonal SDP problem *)
fun run_csdp_blocks nblocks blocksizes (obj:vector) (mats:bmatrix list)
    : vector =
    case find_csdp () of
        NONE => raise ERR "run_csdp_blocks" "CSDP not found"
      | SOME csdp_bin =>
    let
      val input_file = OS.FileSys.tmpName () ^ ".dat-s"
      val output_file = input_file ^ ".out"
      val params_file = input_file ^ ".params"
      val sdpa = sdpa_of_blockproblem nblocks blocksizes obj mats
      val _ = with_out_file input_file (fn os => TextIO.output(os, sdpa))
      val params = "axtol=1.0e-8\natytol=1.0e-8\nobjtol=1.0e-8\n" ^
                   "pinftol=1.0e8\ndinftol=1.0e8\nmaxiter=100\n" ^
                   "minstepfrac=0.9\nmaxstepfrac=0.97\n" ^
                   "minstepp=1.0e-8\nminstepd=1.0e-8\n" ^
                   "usexzgap=1\ntweakgap=0\naffine=0\nprintlevel=0\n"
      val _ = with_out_file params_file (fn os => TextIO.output(os, params))
      val cmd = csdp_bin ^ " " ^ input_file ^ " " ^ output_file ^
                " > /dev/null 2>&1"
      val _ = if !sos_debugging then print ("CSDP: " ^ cmd ^ "\n") else ()
      val _ = OS.Process.system cmd
      val op_str = with_in_file output_file TextIO.inputAll
                   handle IO.Io _ => ""
      val res = parse_csdp_output op_str
      val _ = (OS.FileSys.remove input_file;
               OS.FileSys.remove output_file;
               OS.FileSys.remove params_file) handle OS.SysErr _ => ()
    in
      if vec_dim res = 0 then
        raise ERR "run_csdp_blocks" "CSDP produced no output"
      else res
    end;

(* Scale matrices before sending to CSDP (from HOL-Light's scale_then) *)
fun scale_then solver (obj:vector) (mats:bmatrix list) : vector =
    let
      fun common_denom (bm:bmatrix) acc =
          Redblackmap.foldl (fn (_, c, a) => lcm_num (rat_denom c) a) acc bm
      fun max_elt (bm:bmatrix) acc =
          Redblackmap.foldl (fn (_, c, a) =>
              let val ac = rat_abs c in if rat_gt(ac, a) then ac else a end)
            acc bm
      val cd1 = List.foldl (fn (m, a) => common_denom m a)
                  (Arbnum.fromInt 1) mats
      val mats' = map (Redblackmap.map (fn (_, x) =>
                         rat_mul(Arbrat.fromNat cd1, x))) mats
      val obj' = vec_cmul (Arbrat.fromNat cd1) obj
      (* Scale to reasonable magnitudes *)
      val max1 = List.foldl (fn (m, a) => max_elt m a) rat0 mats'
      val max2 = IMap.foldl (fn (_, c, a) =>
                     let val ac = rat_abs c in
                       if rat_gt(ac, a) then ac else a end) rat0 (#2 obj')
      fun log2_scale mx =
          if mx = rat0 then rat1
          else let val f = Real.fromLargeInt
                             (Arbint.toLargeInt (rat_numer mx))
                           / Real.fromLargeInt
                             (Arbint.toLargeInt
                               (Arbint.fromNat (rat_denom mx)))
                   val e = 20 - Real.floor(Math.ln(Real.abs f) / Math.ln 2.0)
               in rat_pow (Arbrat.fromInt 2) (Int.max(0, e))
               end handle _ => rat1
      val scal1 = log2_scale max1
      val scal2 = log2_scale max2
      val mats'' = map (Redblackmap.map (fn (_, x) => rat_mul(scal1, x))) mats'
      val obj'' = vec_cmul scal2 obj'
    in solver obj'' mats''
    end;

(* ===================================================================== *)
(* Equation-parametrized polynomials (epoly)                             *)
(* An epoly maps monomials to equation3 (linear combinations of Gram    *)
(* matrix variables). Each coefficient of the poly is a linear expr.    *)
(* ===================================================================== *)

type epoly = (monomial, equation3) Redblackmap.dict;
val epoly_empty : epoly = Redblackmap.mkDict mono_compare;

(* Multiply regular poly p by epoly q, accumulate into acc *)
fun epoly_pmul (p:poly) (q:epoly) (acc:epoly) : epoly =
    Redblackmap.foldl
      (fn (m1, c, a) =>
          Redblackmap.foldl
            (fn (m2, e, b) =>
                let val m = mono_mul m1 m2
                    val es = case Redblackmap.peek(b, m) of
                                 SOME e0 => e0 | NONE => eq3_empty
                in Redblackmap.insert(b, m, eq3_add (eq3_cmul c e) es)
                end)
            a q)
      acc p;

fun epoly_cmul (c:rat) (l:epoly) : epoly =
    if c = rat0 then epoly_empty
    else Redblackmap.map (fn (_, e) => eq3_cmul c e) l;

(* Convert poly to epoly: each coefficient c at monomial m becomes
   (0,0,0) |=> -c  (convention: (0,0,0) evaluates to -1) *)
fun epoly_of_poly (p:poly) : epoly =
    Redblackmap.foldl
      (fn (m, c, a) =>
          Redblackmap.insert(a, m,
            Redblackmap.insert(eq3_empty, (0,0,0), rat_neg c)))
      epoly_empty p;

(* ===================================================================== *)
(* Positivstellensatz certificate search                                 *)
(* ===================================================================== *)

val max_sos_degree = ref 20;

(* Enumerate monomials of a given total degree d over given variables *)
fun enumerate_monomials d (vars : term list) : monomial list =
    if d < 0 then []
    else if d = 0 then [mono_1]
    else case vars of
        [] => [mono_1]
      | v::vs =>
        List.concat
          (List.tabulate(d+1, fn k =>
            map (fn m => if k = 0 then m
                         else Redblackmap.insert(m, v, k))
                (enumerate_monomials (d - k) vs)));

(* Enumerate products of distinct input polys with degree <= d.
   Returns (product_poly, positivstellensatz_certificate) pairs. *)
fun enumerate_products d (pols : (poly * positivstellensatz) list)
    : (poly * positivstellensatz) list =
    if d = 0 then [(poly_const rat1, Rational_lt rat1)]
    else if d < 0 then []
    else case pols of
        [] => [(poly_const rat1, Rational_lt rat1)]
      | (p,b)::ps =>
        let val e = multidegree p
        in if e = 0 then enumerate_products d ps
           else enumerate_products d ps @
                map (fn (q,c) => (poly_mul p q, Product(b,c)))
                    (enumerate_products (d - e) ps)
        end;

(* The main certificate search: Positivstellensatz via block-diagonal SDP *)
fun real_positivnullstellensatz_general linf d
    (eqs : poly list) (leqs : (poly * positivstellensatz) list) (pol : poly)
    : poly list * (positivstellensatz * (rat * poly) list) list =
  let
    val vars = List.foldl
      (fn (p, acc) => op_union aconv (poly_variables p) acc)
      [] (pol :: eqs @ map #1 leqs)
    val monoid =
      if linf then
        (poly_const rat1, Rational_lt rat1) ::
        (List.filter (fn (p,_) => multidegree p <= d) leqs)
      else enumerate_products d leqs
    val nblocks = length monoid

    (* Make ideal multiplier for equality k with poly p:
       degree-bounded poly with variables (-k, -n, n) *)
    fun mk_idmultiplier k p =
      let val e = d - multidegree p
          val mons = enumerate_monomials e vars
          val nons = ListPair.zip(mons, List.tabulate(length mons, fn i => i+1))
      in (mons,
          List.foldl (fn ((m,n), acc) =>
            Redblackmap.insert(acc, m,
              Redblackmap.insert(eq3_empty, (~k, ~n, n), rat1)))
          epoly_empty nons)
      end

    (* Make SOS multiplier for block k with poly/cert (p,c):
       parametric Gram matrix block *)
    fun mk_sqmultiplier k (p,_) =
      let val e = (d - multidegree p) div 2
          val mons = enumerate_monomials e vars
          val nons = ListPair.zip(mons, List.tabulate(length mons, fn i => i+1))
      in (mons,
          List.foldl (fn ((m1,n1), acc1) =>
            List.foldl (fn ((m2,n2), acc2) =>
              if n1 > n2 then acc2
              else
                let val m = mono_mul m1 m2
                    val c = if n1 = n2 then rat1 else Arbrat.fromInt 2
                    val es = case Redblackmap.peek(acc2, m) of
                                 SOME e => e | NONE => eq3_empty
                in Redblackmap.insert(acc2, m,
                     eq3_add (Redblackmap.insert(eq3_empty, (k,n1,n2), c)) es)
                end)
            acc1 nons)
          epoly_empty nons)
      end

    val sq_results = ListPair.map (fn (k, mp) => mk_sqmultiplier k mp)
                       (List.tabulate(nblocks, fn i => i+1), monoid)
    val (sqmonlist, sqs) = ListPair.unzip sq_results

    val id_results = ListPair.map (fn (k, eq) => mk_idmultiplier k eq)
                       (List.tabulate(length eqs, fn i => i+1), eqs)
    val (idmonlist, ids) = ListPair.unzip id_results

    val blocksizes = map length sqmonlist

    (* Build the big sum:
       sum(eq_i * id_i) + sum(monoid_j * sq_j) + epoly_of_poly(-pol) *)
    val bigsum =
      let val s0 = epoly_of_poly (poly_neg pol)
          val s1 = ListPair.foldl (fn ((p,_), s, acc) => epoly_pmul p s acc)
                     s0 (monoid, sqs)
          val s2 = ListPair.foldl (fn (p, s, acc) => epoly_pmul p s acc)
                     s1 (eqs, ids)
      in s2
      end

    (* Extract equations (one per monomial in bigsum) *)
    val eqns = Redblackmap.foldl (fn (_, e, acc) => e :: acc) [] bigsum

    (* Eliminate to get free variables *)
    val (pvs, assig) = eliminate_all_equations3 (0,0,0) eqns
    val qvars = (0,0,0) :: pvs
    val allassig =
      List.foldl (fn (v, acc) =>
                     Redblackmap.insert(acc, v,
                       Redblackmap.insert(eq3_empty, v, rat1)))
                 assig pvs

    (* Build block-diagonal matrices for each variable *)
    fun mk_matrix v : bmatrix =
      Redblackmap.foldl
        (fn ((b,i,j), ass, m) =>
            if b < 0 then m (* skip ideal multiplier entries *)
            else let val c = case Redblackmap.peek(ass, v) of
                                 SOME r => r | NONE => rat0
                 in if c = rat0 then m
                    else let val m' = Redblackmap.insert(m, (b,j,i), c)
                         in Redblackmap.insert(m', (b,i,j), c)
                         end
                 end)
        bmat_empty allassig

    (* Objective: sum of diagonal entries *)
    val diagents =
      Redblackmap.foldl
        (fn ((b,i,j), e, a) =>
            if b > 0 andalso i = j then eq3_add e a else a)
        eq3_empty allassig

    val mats = map mk_matrix qvars
    val obj_coeffs =
      map (fn v => case Redblackmap.peek(diagents, v) of
                       SOME c => c | NONE => rat0) pvs
    val obj = vec_of_list obj_coeffs

    val _ = if !sos_debugging then
              print ("PSatz: " ^ Int.toString nblocks ^ " blocks, " ^
                     Int.toString (length pvs) ^ " free vars, sizes=" ^
                     String.concatWith "," (map Int.toString blocksizes) ^ "\n")
            else ()

    (* Call CSDP *)
    val raw_vec =
      if null pvs then vec_0 0
      else scale_then (run_csdp_blocks nblocks blocksizes) obj mats

    (* Rounding loop *)
    fun find_rounding dd =
      let
        val _ = if !sos_debugging then
                  print ("PSatz: rounding d=" ^ Arbrat.toString dd ^ "\n")
                else ()
        val vec = nice_vector dd raw_vec
        val blockmat =
          List.foldl
            (fn (i, a) =>
                bmatrix_add (bmatrix_cmul (vec_el vec i)
                              (List.nth(mats, i))) a)
            (bmatrix_neg (hd mats))
            (List.tabulate(vec_dim vec, fn i => i+1))
        val allmats = blocks blocksizes blockmat
      in (vec, map diag allmats)
      end

    val rounding_vals =
      (List.tabulate(31, fn i => Arbrat.fromInt (i+1))) @
      (List.tabulate(62, fn i => rat_pow (Arbrat.fromInt 2) (i+5)))

    fun try_roundings [] =
        raise ERR "real_positivnullstellensatz_general" "rounding failed"
      | try_roundings (dd::dds) =
        find_rounding dd
        handle HOL_ERR _ => try_roundings dds

    val (vec, ratdias) =
      if null pvs then find_rounding rat1
      else try_roundings rounding_vals

    (* Reconstruct certificates *)
    val newassigs =
      let val base = Redblackmap.insert(eq3_empty, (0,0,0), rat_neg rat1)
      in List.foldl (fn (k, acc) =>
           Redblackmap.insert(acc, List.nth(pvs, k-1), vec_el vec k))
         base (List.tabulate(vec_dim vec, fn i => i+1))
      end

    val finalassigs =
      Redblackmap.foldl
        (fn (v, e, a) =>
            Redblackmap.insert(a, v, eq3_eval (fn w =>
              case Redblackmap.peek(newassigs, w) of
                  SOME c => c | NONE => rat0) e))
        newassigs allassig

    fun poly_of_epoly (ep:epoly) : poly =
      Redblackmap.foldl
        (fn (m, e, a) =>
            let val c = eq3_eval (fn w =>
                  case Redblackmap.peek(finalassigs, w) of
                      SOME r => r | NONE => rat0) e
            in if c = rat0 then a
               else poly_add a (Redblackmap.insert(poly_empty, m, c))
            end)
        poly_0 ep

    fun mk_sos mons dia =
      map (fn (c, (_, vm)) =>
        (c, IMap.foldl
              (fn (k, v, acc) =>
                  if v = rat0 then acc
                  else poly_add acc
                    (Redblackmap.insert(poly_empty,
                       List.nth(mons, k-1), v)))
              poly_0 vm))
      dia

    val sqs_out = ListPair.map (fn (m, d) => mk_sos m d) (sqmonlist, ratdias)
    val cfs = map poly_of_epoly ids

    (* Filter out empty SOS blocks *)
    val msq = List.mapPartial
      (fn (((_,cert), sq)) =>
          if null sq then NONE else SOME (cert, sq))
      (ListPair.zip(monoid, sqs_out))

    (* Sanity check *)
    fun eval_sq sqs =
      List.foldl (fn ((c,q), acc) =>
        poly_add (poly_cmul c (poly_square q)) acc) poly_0 sqs
    val sanity =
      List.foldl (fn ((cert,s), acc) =>
        let val p = case List.find (fn ((_, c), _) =>
                          (* find the monoid entry matching this cert *)
                          true) (ListPair.zip(monoid, sqs_out))
                    of _ => poly_0  (* simplified: check overall *)
        in acc end)
      poly_0 msq
    (* Full sanity: sum of (monoid_poly * eval_sq(sqs)) + sum of (eq * cf) - pol *)
    val sanity_full =
      let val s1 = ListPair.foldl
            (fn ((p,_), sq, acc) => poly_add (poly_mul p (eval_sq sq)) acc)
            poly_0 (monoid, sqs_out)
          val s2 = ListPair.foldl
            (fn (p, cf, acc) => poly_add (poly_mul p cf) acc)
            s1 (eqs, cfs)
      in poly_add s2 (poly_neg pol)
      end
  in
    if not (poly_is0 sanity_full) then
      raise ERR "real_positivnullstellensatz_general" "sanity check failed"
    else (cfs, msq)
  end;

(* ===================================================================== *)
(* HOL proof construction                                                *)
(* ===================================================================== *)

local
  val pow_tm_2 = numSyntax.mk_numeral(Arbnum.fromInt 2)
  fun mk_square tm = mk_comb(mk_comb(pow_tm, tm), pow_tm_2)
  fun mk_prod (t1, t2) = mk_comb(mk_comb(mul_tm, t1), t2)
  fun mk_sum (t1, t2) = mk_comb(mk_comb(add_tm, t1), t2)
in

(* SOS_CONV: given a real polynomial term p, produce
   |- p = c1 * q1^2 + ... + cn * qn^2
   by computing an SOS decomposition and verifying with REAL_POLY_CONV *)
fun SOS_CONV tm =
    let
      val pol = poly_of_term tm
      val (k, sos) = sumofsquares pol
      val _ = if null sos then raise ERR "SOS_CONV" "empty decomposition"
              else ()
      fun mk_sqtm (c, p) =
          mk_prod(RealArith.term_of_rat (rat_mul(k, c)),
                  mk_square(term_of_poly p))
      val tms = map mk_sqtm sos
      val rhs_tm = List.foldl mk_sum (hd tms) (tl tms)
      val _ = if !sos_debugging then
                (print ("SOS_CONV lhs: " ^ term_to_string tm ^ "\n");
                 print ("SOS_CONV rhs: " ^ term_to_string rhs_tm ^ "\n"))
              else ()
      (* Verify: both sides should normalize to the same polynomial.
         REAL_POLY_CONV raises UNCHANGED if the term is already normal. *)
      fun poly_conv t =
          REAL_POLY_CONV t handle UNCHANGED => REFL t
      val lhs_th = poly_conv tm
      val rhs_th = poly_conv rhs_tm
      val _ = if !sos_debugging then
                (print ("SOS_CONV lhs_norm: " ^ thm_to_string lhs_th ^ "\n");
                 print ("SOS_CONV rhs_norm: " ^ thm_to_string rhs_th ^ "\n"))
              else ()
      (* |- tm = norm, |- rhs = norm, so |- tm = rhs by TRANS *)
    in TRANS lhs_th (SYM rhs_th)
    end
    handle e => raise wrap_exn "SOSLib" "SOS_CONV" e

end (* local *)

(* ===================================================================== *)
(* PURE_SOS_TAC and PURE_SOS: prove &0 <= p by SOS decomposition        *)
(* ===================================================================== *)

(* Prove &0 <= sum-of-squares term by decomposing it *)
local
  (* |- &0 <= x pow 2 *)
  val le_sq = realTheory.REAL_LE_POW2
  (* |- &0 <= x /\ &0 <= y ==> &0 <= x + y *)
  val le_add = realTheory.REAL_LE_ADD
  (* |- &0 <= x /\ &0 <= y ==> &0 <= x * y *)
  val le_mul = realTheory.REAL_LE_MUL
  (* |- &0 <= &n *)
  val le_rat = fn tm =>
    EQT_ELIM (RealArith.REAL_INT_LE_CONV
                (mk_comb(mk_comb(realSyntax.leq_tm, zero_tm), tm)))
    handle HOL_ERR _ =>
    EQT_ELIM (REAL_RAT_LE_CONV
                (mk_comb(mk_comb(realSyntax.leq_tm, zero_tm), tm)))
in

(* Recursively prove &0 <= t where t is a sum-of-squares expression *)
fun prove_nonneg tm =
    (* Try: rational constant *)
    (le_rat tm)
    handle HOL_ERR _ =>
    (* Try: x pow 2 *)
    (let val (b, e) = realSyntax.dest_pow tm
     in if e ~~ numSyntax.term_of_int 2 then SPEC b le_sq
        else raise ERR "prove_nonneg" "not pow 2"
     end)
    handle HOL_ERR _ =>
    (* Try: a + b where a >= 0 and b >= 0 *)
    (let val (l, r) = realSyntax.dest_plus tm
         val lth = prove_nonneg l
         val rth = prove_nonneg r
     in MATCH_MP le_add (CONJ lth rth)
     end)
    handle HOL_ERR _ =>
    (* Try: a * b where a >= 0 and b >= 0 *)
    (let val (l, r) = realSyntax.dest_mult tm
         val lth = prove_nonneg l
         val rth = prove_nonneg r
     in MATCH_MP le_mul (CONJ lth rth)
     end)
    handle HOL_ERR _ =>
    raise ERR "prove_nonneg" ("can't prove &0 <= " ^ term_to_string tm);

(* Tactic: prove |- &0 <= p or p >= &0 by SOS decomposition *)
val PURE_SOS_TAC : tactic =
  fn (asl, w) =>
    let
      (* w should be of the form &0 <= p or p >= &0 *)
      val (goal_lhs, goal_rhs) =
          realSyntax.dest_leq w
          handle HOL_ERR _ =>
            let val (l, r) = realSyntax.dest_geq w
            in (r, l) end
      val _ = if goal_lhs ~~ zero_tm then ()
              else raise ERR "PURE_SOS_TAC" "goal not of form &0 <= p"
      (* Decompose goal_rhs as sum of squares *)
      val eq_th = SOS_CONV goal_rhs  (* |- goal_rhs = sos_expression *)
      val sos_tm = boolSyntax.rhs (concl eq_th)
      (* Prove &0 <= sos_expression *)
      val nonneg_th = prove_nonneg sos_tm
      (* nonneg_th: |- &0 <= sos_expression *)
      (* eq_th: |- goal_rhs = sos_expression *)
      (* We need: |- &0 <= goal_rhs *)
      val goal_th = ONCE_REWRITE_RULE [SYM eq_th] nonneg_th
    in ([], fn _ => goal_th)
    end
    handle e => raise wrap_exn "SOSLib" "PURE_SOS_TAC" e

end (* local *)

fun PURE_SOS tm = prove(tm, PURE_SOS_TAC)
    handle e => raise wrap_exn "SOSLib" "PURE_SOS" e;

(* ===================================================================== *)
(* REAL_SOS: nonlinear real arithmetic via GEN_REAL_ARITH                *)
(* Uses Positivstellensatz certificate search with hypotheses.           *)
(* ===================================================================== *)

(* Convert positivstellensatz certificate for SOS terms *)
fun term_of_sqterm (c, p) =
    Product(Rational_lt c, Square(term_of_poly p));

fun term_of_sos (pr, sqs) =
    if null sqs then pr
    else Product(pr,
           List.foldl (fn (a, b) => Sum(b, a))
             (term_of_sqterm (hd sqs)) (map term_of_sqterm (tl sqs)));

(* Iterative deepening with bounded depth *)
fun deepen f n =
    let val _ = if !sos_debugging then
                  print ("SOS: trying degree " ^ Int.toString n ^ "\n")
                else ()
    in f n
    end
    handle HOL_ERR _ =>
      if n >= !max_sos_degree then
        raise ERR "deepen" ("exceeded max degree " ^
                            Int.toString (!max_sos_degree))
      else deepen f (n + 1);

(* The core nonlinear prover for GEN_REAL_ARITH.
   Given (eqs, les, lts) hypothesis theorems, find a Positivstellensatz
   certificate and pass it to the translator. *)
fun SOS_PROVER translator (eqs, les, lts) =
  (* Try linear first — avoid CSDP overhead for linear goals *)
  REAL_LINEAR_PROVER translator (eqs, les, lts)
  handle HOL_ERR _ =>
  let
    val eq0 = map (poly_of_term o lhand o concl) eqs
    val le0 = map (poly_of_term o lhand o concl) les
    val lt0 = map (poly_of_term o lhand o concl) lts
    val eqp0 = ListPair.map (fn (t,i) => (t, Axiom_eq i))
                 (eq0, List.tabulate(length eq0, fn i => i))
    val lep0 = ListPair.map (fn (t,i) => (t, Axiom_le i))
                 (le0, List.tabulate(length le0, fn i => i))
    val ltp0 = ListPair.map (fn (t,i) => (t, Axiom_lt i))
                 (lt0, List.tabulate(length lt0, fn i => i))
    (* Separate constant from non-constant hypotheses *)
    val (keq, eq) = List.partition (fn (p,_) => multidegree p = 0) eqp0
    val (klep, lep) = List.partition (fn (p,_) => multidegree p = 0) lep0
    val (kltp, ltp) = List.partition (fn (p,_) => multidegree p = 0) ltp0
    (* Check for trivially contradictory constant axioms *)
    fun trivial_axiom (p, ax) =
      case ax of
          Axiom_eq n => if poly_eval p <> rat0
                        then SOME (List.nth(eqs, n)) else NONE
        | Axiom_le n => if rat_lt(poly_eval p, rat0)
                        then SOME (List.nth(les, n)) else NONE
        | Axiom_lt n => if rat_le(poly_eval p, rat0)
                        then SOME (List.nth(lts, n)) else NONE
        | _ => NONE
    val trivial = List.mapPartial trivial_axiom (keq @ klep @ kltp)
  in
    case trivial of
        (th :: _) =>
          CONV_RULE (LAND_CONV (REAL_POLY_CONV THENC REAL_RAT_REDUCE_CONV)) th
      | [] =>
    let
      val pol = List.foldl (fn ((p,_), acc) => poly_mul p acc)
                  (poly_const rat1) ltp
      val leq = lep @ ltp

      fun tryall dd =
        let val e = multidegree pol
            val k = if e = 0 then 0 else dd div e
            val eq' = map #1 eq
            fun try_i i =
              (dd, i, real_positivnullstellensatz_general false dd eq' leq
                        (poly_neg (poly_pow pol i)))
        in case List.find (fn i =>
             (try_i i; true) handle HOL_ERR _ => false) (List.tabulate(k+1, fn i => i))
           of SOME i => try_i i
            | NONE => raise ERR "tryall" "no degree/power worked"
        end

      val (dd, i, (cert_ideal, cert_cone)) = deepen tryall 0

      (* Build the proof certificate *)
      val proofs_ideal =
        ListPair.map (fn (q, (_, ax)) => Eqmul(term_of_poly q, ax))
          (cert_ideal, eq)
      val proofs_cone = map term_of_sos cert_cone
      val proof_ne =
        if null ltp then Rational_lt rat1
        else
          let val p = List.foldl (fn ((_,c), acc) => Product(acc, c))
                        (snd (hd ltp)) (tl ltp)
          in Lib.funpow i (fn q => Product(p, q)) (Rational_lt rat1)
          end
      val proof = List.foldl (fn (a, b) => Sum(b, a))
                    proof_ne (proofs_ideal @ proofs_cone)

      val _ = if !sos_debugging then
                print "SOS: translating certificate to HOL\n"
              else ()
    in
      translator (eqs, les, lts) proof
    end
  end


(* Variable substitution preprocessing (REAL_NONLINEAR_SUBST_PROVER).
   Tries to eliminate variables from equalities before calling SOS_PROVER. *)
local
  val zero_real = realSyntax.zero_tm
  val real_mul_tm = realSyntax.mult_tm
  val shuffle1 =
    CONV_RULE (REWR_CONV (REAL_ARITH ``a + x = (y:real) <=> x = y - a``))
  val shuffle2 =
    CONV_RULE (REWR_CONV (REAL_ARITH ``x + a = (y:real) <=> x = y - a``))

  fun substitutable_monomial fvs tm =
    if is_var tm andalso type_of tm = realSyntax.real_ty
       andalso not (op_mem aconv tm fvs)
    then (rat1, tm)
    else if is_comb tm then
      let val (opr, r) = dest_comb tm in
        if is_comb opr then
          let val (op2, l) = dest_comb opr in
            if op2 ~~ real_mul_tm andalso RealArith.is_ratconst l
               andalso is_var r andalso type_of r = realSyntax.real_ty
               andalso not (op_mem aconv r fvs)
            then (RealArith.rat_of_term l, r)
            else if op2 ~~ realSyntax.plus_tm then
              (substitutable_monomial
                 (op_union aconv (free_vars r) fvs) l
               handle HOL_ERR _ =>
               substitutable_monomial
                 (op_union aconv (free_vars l) fvs) r)
            else raise ERR "substitutable_monomial" ""
          end
        else raise ERR "substitutable_monomial" ""
      end
    else raise ERR "substitutable_monomial" ""

  fun isolate_variable v th =
    let val lhs_tm = lhand (concl th) in
      if lhs_tm ~~ v then th
      else if is_comb lhs_tm then
        let val (opr, _) = dest_comb lhs_tm in
          if is_comb opr then
            let val (op2, l) = dest_comb opr in
              if op2 ~~ realSyntax.plus_tm then
                if is_var l andalso l ~~ v then shuffle2 th
                else isolate_variable v (shuffle1 th)
              else raise ERR "isolate_variable" ""
            end
          else raise ERR "isolate_variable" ""
        end
      else raise ERR "isolate_variable" ""
    end

  fun make_substitution th =
    let
      val (c, v) = substitutable_monomial [] (lhand (concl th))
      val inv_c = rat_div(rat1, c)
      val th1 = AP_TERM (mk_comb(real_mul_tm,
                   RealArith.term_of_rat inv_c)) th
      val th2 = CONV_RULE (BINOP_CONV REAL_POLY_MUL_CONV) th1
    in
      CONV_RULE (RAND_CONV REAL_POLY_CONV) (isolate_variable v th2)
    end
in
  fun SOS_SUBST_PROVER translator =
    let
      fun substfirst (eqs, les, lts) =
        (let val eth = tryfind make_substitution eqs
             fun modify th =
               CONV_RULE (LAND_CONV (PURE_REWRITE_CONV [eth]
                                     THENC REAL_POLY_CONV)) th
             val eqs' = List.filter (fn t => not (lhand (concl t) ~~ zero_real))
                          (map modify eqs)
         in substfirst (eqs', map modify les, map modify lts)
         end
         handle HOL_ERR _ => SOS_PROVER translator (eqs, les, lts))
    in substfirst
    end
end (* local *);

(* REAL_SOS: the main entry point.
   Uses GEN_REAL_ARITH to handle hypotheses via Positivstellensatz
   certificate search. Falls back to direct SOS proof for pure
   nonnegativity goals without hypotheses. *)
local
  val DECIMAL = markerTheory.unint_def
  val dec_conv = QCONV (ONCE_DEPTH_CONV (REWR_CONV DECIMAL))
  val core = RealField.GEN_REAL_ARITH SOS_SUBST_PROVER

  val REAL_SUB_LE = realTheory.REAL_SUB_LE
  val real_ge_def = realTheory.real_ge

  fun prove_le0 poly_tm =
      let val eq_th = SOS_CONV poly_tm
          val sos_tm = boolSyntax.rhs (concl eq_th)
      in ONCE_REWRITE_RULE [SYM eq_th] (prove_nonneg sos_tm)
      end

  fun direct_sos tm =
    let
      val (avs, bod) = strip_forall tm
      fun build () =
        (* &0 <= p *)
        (let val (l, r) = realSyntax.dest_leq bod
         in if l ~~ zero_tm then GENL avs (prove_le0 r)
            else raise ERR "direct_sos" ""
         end handle HOL_ERR _ =>
        (* p >= q *)
        (let val (l, r) = realSyntax.dest_geq bod
             val diff = mk_comb(mk_comb(realSyntax.minus_tm, l), r)
             val le_th = EQ_MP (SPECL [l, r] REAL_SUB_LE) (prove_le0 diff)
         in GENL avs (EQ_MP (SYM (SPECL [l, r] real_ge_def)) le_th)
         end handle HOL_ERR _ =>
        (* p <= q *)
        (let val (l, r) = realSyntax.dest_leq bod
             val diff = mk_comb(mk_comb(realSyntax.minus_tm, r), l)
         in GENL avs (EQ_MP (SPECL [r, l] REAL_SUB_LE) (prove_le0 diff))
         end handle HOL_ERR _ =>
        raise ERR "direct_sos" "not a simple inequality")))
    in build ()
    end
in
  fun REAL_SOS tm =
    let val th0 = dec_conv tm
        val tm0 = rhs (concl th0)
    in EQ_MP (SYM th0)
         (core tm0
          handle HOL_ERR {origin_structure=s1, origin_function=f1,
                          message=m1} =>
            direct_sos tm0
            handle HOL_ERR _ =>
              raise ERR "REAL_SOS"
                (m1 ^ (if isSome (find_csdp ()) then ""
                       else " (CSDP not found — install CSDP or set \
                             \HOL4_CSDP_EXECUTABLE for nonlinear goals \
                             \with hypotheses)")))
    end
    handle e => raise wrap_exn "SOSLib" "REAL_SOS" e
end;

val (REAL_SOS_TAC, REAL_SOS_ASM_TAC) = RealArith.mk_real_arith_tac REAL_SOS;

(* ===================================================================== *)
(* REAL_SOS_DIRECT_TAC: bypass GEN_REAL_ARITH normalization              *)
(* Use when REAL_SOS_ASM_TAC hangs on goals with many nonlinear hyps.   *)
(* Expects: all assumptions and goal are :real polynomial inequalities.  *)
(* ===================================================================== *)

local
  val le_tm = realSyntax.leq_tm
  val lt_tm = realSyntax.less_tm
  val ge_tm = realSyntax.geq_tm
  val gt_tm = realSyntax.greater_tm
  val eq_tm = realSyntax.real_eq_tm
  val x_tm = mk_var("x", real_ty)
  val y_tm = mk_var("y", real_ty)

  val pth_le = REAL_ARITH ``x <= y <=> y - x >= &0:real``
  val pth_lt = REAL_ARITH ``x < y <=> y - x > &0:real``
  val pth_ge = REAL_ARITH ``x >= y <=> x - y >= &0:real``
  val pth_gt = REAL_ARITH ``x > y <=> x - y > &0:real``
  val pth_eq = REAL_ARITH ``(x = y:real) <=> x - y = &0``
  val pth_nle = REAL_ARITH ``~(x <= y) <=> x - y > &0:real``
  val pth_nlt = REAL_ARITH ``~(x < y) <=> x - y >= &0:real``
  val pth_nge = REAL_ARITH ``~(x >= y) <=> y - x > &0:real``
  val pth_ngt = REAL_ARITH ``~(x > y) <=> y - x >= &0:real``

  fun norm_ineq th =
    let val tm = concl th
        val (opr, args) = strip_comb tm
        fun bin_args xs = case xs of [l, r] => (l, r)
              | _ => raise ERR "norm_ineq" "expected binary"
        fun do_conv pth l r =
          let val th1 = INST [x_tm |-> l, y_tm |-> r] pth
          in EQ_MP (CONV_RULE (RAND_CONV (LAND_CONV REAL_POLY_CONV)) th1) th
          end
    in
      if same_const opr le_tm then
        let val (l,r) = bin_args args in do_conv pth_le l r end
      else if same_const opr lt_tm then
        let val (l,r) = bin_args args in do_conv pth_lt l r end
      else if same_const opr ge_tm then
        let val (l,r) = bin_args args in do_conv pth_ge l r end
      else if same_const opr gt_tm then
        let val (l,r) = bin_args args in do_conv pth_gt l r end
      else if same_const opr eq_tm andalso
              type_of (hd args) = real_ty then
        let val (l,r) = bin_args args in do_conv pth_eq l r end
      else if is_neg tm then
        let val inner = dest_neg tm
            val (iop, iargs) = strip_comb inner
        in
          if same_const iop le_tm then
            let val (l,r) = bin_args iargs in do_conv pth_nle l r end
          else if same_const iop lt_tm then
            let val (l,r) = bin_args iargs in do_conv pth_nlt l r end
          else if same_const iop ge_tm then
            let val (l,r) = bin_args iargs in do_conv pth_nge l r end
          else if same_const iop gt_tm then
            let val (l,r) = bin_args iargs in do_conv pth_ngt l r end
          else raise ERR "norm_ineq" "unexpected negated form"
        end
      else raise ERR "norm_ineq" "unexpected form"
    end

  fun is_ge_concl th =
    (same_const (fst (strip_comb (concl th))) ge_tm) handle _ => false
  fun is_gt_concl th =
    (same_const (fst (strip_comb (concl th))) gt_tm) handle _ => false
  fun is_eq_concl th =
    (is_eq (concl th) andalso type_of (lhs (concl th)) = real_ty)
    handle _ => false

  val pth_add = fetch "realax" "GEN_REAL_ARITH0_pth_add"
  val pth_mul = fetch "realax" "GEN_REAL_ARITH0_pth_mul"
  val pth_emul = fetch "realax" "GEN_REAL_ARITH0_pth_emul"
  val pth_square = fetch "realax" "GEN_REAL_ARITH0_pth_square"

  fun MATCH_MP_RULE rules =
    let val net = itlist
          (fn th => Net.insert (lhand(concl th), PART_MATCH lhand th))
          (CONJUNCTS rules) Net.empty
    in fn th =>
       let val convs = Net.match (concl th) net
       in if null convs then raise UNCHANGED
          else MP (FIRST_CONV convs (concl th)) th
       end
    end

  fun MUL_RULE th =
    CONV_RULE(LAND_CONV REAL_POLY_MUL_CONV) (MATCH_MP_RULE pth_mul th)
  fun ADD_RULE th =
    CONV_RULE(LAND_CONV REAL_POLY_ADD_CONV) (MATCH_MP_RULE pth_add th)
  fun EMUL_RULE tm th =
    CONV_RULE(LAND_CONV REAL_POLY_MUL_CONV) (SPEC tm (MATCH_MP pth_emul th))
  fun SQUARE_RULE t =
    CONV_RULE (LAND_CONV REAL_POLY_MUL_CONV) (SPEC t pth_square)

  fun hol_translator (eqs,les,lts) prf =
    let
      fun translate (Axiom_eq n) = List.nth (eqs,n)
        | translate (Axiom_le n) = List.nth (les,n)
        | translate (Axiom_lt n) = List.nth (lts,n)
        | translate (Rational_eq x) =
            EQT_ELIM(REAL_RAT_EQ_CONV
              (mk_comb(mk_comb(eq_tm,RealArith.term_of_rat x),zero_tm)))
        | translate (Rational_le x) =
            EQT_ELIM(REAL_RAT_GE_CONV
              (mk_comb(mk_comb(ge_tm,RealArith.term_of_rat x),zero_tm)))
        | translate (Rational_lt x) =
            EQT_ELIM(REAL_RAT_GT_CONV
              (mk_comb(mk_comb(gt_tm,RealArith.term_of_rat x),zero_tm)))
        | translate (Square t) = SQUARE_RULE t
        | translate (Eqmul(t,p)) = EMUL_RULE t (translate p)
        | translate (Sum(p1,p2)) =
            ADD_RULE (CONJ (translate p1) (translate p2))
        | translate (Product(p1,p2)) =
            MUL_RULE (CONJ (translate p1) (translate p2))
    in
      CONV_RULE(FIRST_CONV[REAL_RAT_GE_CONV, REAL_RAT_GT_CONV,
                            REAL_RAT_EQ_CONV])
               (translate prf)
    end
in
  fun REAL_SOS_DIRECT_TAC (asl, gl) =
    let
      val neg_gl_th = ASSUME (mk_neg gl)
      val all_ths = neg_gl_th :: map ASSUME asl
      val normed = List.mapPartial
        (fn th => SOME (norm_ineq th) handle HOL_ERR _ => NONE) all_ths
      val eqs = filter is_eq_concl normed
      val les = filter is_ge_concl normed
      val lts = filter is_gt_concl normed
      val false_th = SOS_PROVER hol_translator (eqs, les, lts)
      val res = CCONTR gl false_th
    in
      ([], fn _ => foldl (fn (a, th) => PROVE_HYP (ASSUME a) th) res asl)
    end
    handle e => raise wrap_exn "SOSLib" "REAL_SOS_DIRECT_TAC" e
end;

(* ===================================================================== *)
(* REAL_SOSFIELD: handles division/inv in real goals                     *)
(* Ported from HOL-Light sos.ml lines 1294-1338                         *)
(* ===================================================================== *)

local
  val and_tm = boolSyntax.conjunction
  val inv_tm = realSyntax.inv_tm

  (* Prenex conversion: expand div/inv, prenex quantifiers *)
  val prenex_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    PURE_REWRITE_CONV [boolTheory.FORALL_SIMP, boolTheory.EXISTS_SIMP,
                       realTheory.real_div, realTheory.REAL_INV_INV,
                       realTheory.REAL_INV_MUL',
                       GSYM realTheory.REAL_POW_INV] THENC
    normalForms.NNFC_CONV THENC
    DEPTH_BINOP_CONV and_tm normalForms.CONDS_CELIM_CONV THENC
    normalForms.PRENEX_CONV

  val setup_conv =
    normalForms.NNF_CONV THENC
    normalForms.WEAK_CNF_CONV THENC
    normalForms.CONJ_CANON_CONV

  fun core_rule t =
    (REAL_ARITH t) handle HOL_ERR _ =>
    (REAL_RING t)  handle HOL_ERR _ =>
    REAL_SOS t

  fun is_inv' tm =
    (realSyntax.is_div tm orelse
     (is_comb tm andalso rator tm ~~ inv_tm))
    andalso not (is_ratconst (rand tm))

  fun BASIC_REAL_SOSFIELD tm =
    let
      fun is_freeinv t = is_inv' t andalso free_in t tm
      val itms = op_mk_set aconv (map rand (find_terms is_freeinv tm))
      val hyps = map (fn t => SPEC t realTheory.REAL_MUL_RINV) itms
      val tm' = itlist (fn th => fn t => mk_imp(concl th, t)) hyps tm
      val itms' = map (curry mk_comb inv_tm) itms
      val gvs = map (genvar o type_of) itms'
      val tm'' = subst (ListPair.map (fn (g,i) => i |-> g) (gvs, itms')) tm'
      val th1 = setup_conv tm''
      val cjs = strip_conj (rand (concl th1))
      val ths = map core_rule cjs
      val th2 = EQ_MP (SYM th1) (end_itlist CONJ ths)
    in
      rev_itlist (C MP) hyps (INST (ListPair.map (fn (i,g) => g |-> i) (itms', gvs)) th2)
    end
in
  fun REAL_SOSFIELD tm =
    let
      val th0 = prenex_conv tm
      val tm0 = rand (concl th0)
      val (avs, bod) = strip_forall tm0
      val th1 = setup_conv bod
      val ths = map BASIC_REAL_SOSFIELD (strip_conj (rand (concl th1)))
    in
      EQ_MP (SYM th0)
        (GENL avs (EQ_MP (SYM th1) (end_itlist CONJ ths)))
    end
    handle e => raise wrap_exn "SOSLib" "REAL_SOSFIELD" e
end;

val (REAL_SOSFIELD_TAC, REAL_SOSFIELD_ASM_TAC) =
  RealArith.mk_real_arith_tac REAL_SOSFIELD;

(* ===================================================================== *)
(* INT_SOS: integer SOS via reduction to real                            *)
(* Ported from HOL-Light sos.ml lines 1340-1367                         *)
(* ===================================================================== *)

local
  (* Theorems for atom normalization (negated int comparisons + discreteness) *)
  val INT_NOT_LE    = integerTheory.INT_NOT_LE     (* ~(x <= y) <=> y < x *)
  val INT_NOT_LT    = integerTheory.INT_NOT_LT     (* ~(x < y) <=> y <= x *)
  val INT_NOT_EQ    = integerTheory.INT_NOT_EQ     (* ~(x = y) <=> x<y \/ y<x *)
  val INT_LT_DISCRETE = integerTheory.INT_LT_DISCRETE  (* x<y <=> x+1 <= y *)
  val INT_GT        = integerTheory.INT_GT          (* x > y <=> y < x *)
  val INT_GE        = integerTheory.INT_GE          (* x >= y <=> y <= x *)

  (* atom_CONV: handle negated int comparisons using discreteness *)
  val atom_CONV =
    CHANGED_CONV (REWRITE_CONV [INT_NOT_LE, INT_NOT_LT, INT_NOT_EQ,
                                INT_LT_DISCRETE])

  (* bub_CONV: convert int operations to real_of_int *)
  val bub_CONV = REWRITE_CONV [
    GSYM intrealTheory.real_of_int_11,
    GSYM intrealTheory.real_of_int_le,
    GSYM intrealTheory.real_of_int_lt,
    intrealTheory.real_of_int_add,
    intrealTheory.real_of_int_neg,
    intrealTheory.real_of_int_mul,
    intrealTheory.real_of_int_sub,
    intrealTheory.real_of_int_num
  ]

  val base_CONV = TRY_CONV atom_CONV THENC bub_CONV

  (* NNF normalization with atom handling *)
  val NNF_NORM_CONV =
    normalForms.GEN_NNF_CONV false
      (base_CONV,
       fn t => (base_CONV t, base_CONV (mk_neg t)))

  val init_CONV =
    GEN_REWRITE_CONV DEPTH_CONV empty_rewrites
      [boolTheory.FORALL_SIMP, boolTheory.EXISTS_SIMP] THENC
    GEN_REWRITE_CONV DEPTH_CONV empty_rewrites [INT_GT, INT_GE] THENC
    normalForms.CONDS_ELIM_CONV THENC
    NNF_NORM_CONV

  val p_var = mk_var("p", bool)
  val not_tm = boolSyntax.negation
  (* |- ~~p <=> p *)
  val pth = EQT_ELIM (REWRITE_CONV [] (mk_eq(mk_neg(mk_neg p_var), p_var)))
in
  fun INT_SOS tm =
    let
      val th0 = INST [p_var |-> tm] pth
      val th1 = init_CONV (mk_neg tm)
      val th2 = REAL_SOS (mk_neg (rand (concl th1)))
    in
      EQ_MP th0 (EQ_MP (AP_TERM not_tm (SYM th1)) th2)
    end
    handle e => raise wrap_exn "SOSLib" "INT_SOS" e
end;

val INT_SOS_TAC : tactic = fn gl => ACCEPT_TAC (INT_SOS (snd gl)) gl;

val INT_SOS_ASM_TAC : tactic = fn (gl : goal) =>
  let val (asl, g) = gl
      val g' = list_mk_conj (asl @ [g]) handle HOL_ERR _ => g
  in ACCEPT_TAC (INT_SOS g') gl
  end handle HOL_ERR _ => raise ERR "INT_SOS_ASM_TAC" "failed";

(* ===================================================================== *)
(* NUM_SOS_RULE: natural number SOS via reduction to int                 *)
(* Ported from HOL-Light sos.ml lines 1369-1375                         *)
(* ===================================================================== *)

local
  (* NUM_SOS_RULE: Convert num goals to int via int_of_num (&), then use INT_SOS.
     Uses GSYM INT_OF_NUM_LE etc. to rewrite num comparisons/operations to int.
     Handles: +, *, EXP, <=, <, >=, >, =, numerals *)

  (* First expand >= to <= and > to < in the num domain *)
  val num_normalize_conv =
    PURE_REWRITE_CONV [arithmeticTheory.GREATER_EQ,
                       arithmeticTheory.GREATER_DEF]

  (* Then convert num ops to int ops via GSYM INT_OF_NUM_* *)
  val num_to_int_conv =
    PURE_REWRITE_CONV [GSYM integerTheory.INT_OF_NUM_LE,
                       GSYM integerTheory.INT_OF_NUM_LT,
                       GSYM integerTheory.INT_OF_NUM_EQ,
                       GSYM integerTheory.INT_OF_NUM_ADD,
                       GSYM integerTheory.INT_OF_NUM_MUL,
                       GSYM integerTheory.INT_OF_NUM_POW]

  val NUM_TO_INT_CONV = num_normalize_conv THENC num_to_int_conv
in
  fun NUM_SOS_RULE tm =
    let
      val avs = free_vars tm
      val tm' = list_mk_forall (avs, tm)
      val th1 = NUM_TO_INT_CONV tm'
      val th2 = INT_SOS (rand (concl th1))
    in
      SPECL avs (EQ_MP (SYM th1) th2)
    end
    handle e => raise wrap_exn "SOSLib" "NUM_SOS_RULE" e
end;

val NUM_SOS_RULE_TAC : tactic = fn gl =>
  ACCEPT_TAC (NUM_SOS_RULE (snd gl)) gl;

val NUM_SOS_RULE_ASM_TAC : tactic = fn (gl : goal) =>
  let val (asl, g) = gl
      val g' = list_mk_conj (asl @ [g]) handle HOL_ERR _ => g
  in ACCEPT_TAC (NUM_SOS_RULE g') gl
  end handle HOL_ERR _ => raise ERR "NUM_SOS_RULE_ASM_TAC" "failed";

end (* struct *)
