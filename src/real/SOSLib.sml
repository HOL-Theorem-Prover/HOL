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
(* REAL_SOS: nonlinear real arithmetic via SOS decomposition             *)
(* ===================================================================== *)

local
  (* |- !x y. &0 <= x - y <=> y <= x *)
  val REAL_SUB_LE = realTheory.REAL_SUB_LE
  (* |- !x y. x >= y <=> y <= x *)
  val real_ge = realTheory.real_ge

  (* Prove |- &0 <= poly_tm via SOS_CONV + prove_nonneg *)
  fun prove_le0 poly_tm =
      let val eq_th = SOS_CONV poly_tm
          val sos_tm = boolSyntax.rhs (concl eq_th)
          val nonneg_th = prove_nonneg sos_tm
      in ONCE_REWRITE_RULE [SYM eq_th] nonneg_th
      end
in

(* REAL_SOS: prove a universally quantified nonnegativity goal via SOS.
   Handles: &0 <= p, p >= &0, p >= q, p <= q, !x y. ... &0 <= f(x,y).
   Does NOT handle hypotheses — that requires GEN_REAL_ARITH integration
   with positivstellensatz certificate search (future work). *)
(* Parse goal form, returning (poly_to_decompose, result_builder).
   Separated from proving so SOS failures propagate directly. *)
fun parse_sos_goal bod =
    (* &0 <= p *)
    (let val (l, r) = realSyntax.dest_leq bod
     in if l ~~ zero_tm then (r, fn th => th)
        else raise ERR "parse_sos_goal" ""
     end handle HOL_ERR _ =>
    (* p >= q  (includes p >= &0) *)
    (let val (l, r) = realSyntax.dest_geq bod
         val diff = mk_comb(mk_comb(realSyntax.minus_tm, l), r)
     in (diff, fn le_diff =>
           let val le_th = EQ_MP (SPECL [l, r] REAL_SUB_LE) le_diff
           in EQ_MP (SYM (SPECL [l, r] real_ge)) le_th
           end)
     end handle HOL_ERR _ =>
    (* p <= q *)
    (let val (l, r) = realSyntax.dest_leq bod
         val diff = mk_comb(mk_comb(realSyntax.minus_tm, r), l)
     in (diff, fn le_diff =>
           EQ_MP (SPECL [r, l] REAL_SUB_LE) le_diff)
     end handle HOL_ERR _ =>
    raise ERR "REAL_SOS"
      "goal must be of the form &0 <= p, p >= &0, p >= q, or p <= q"
    )))

fun REAL_SOS tm =
    let
      val (avs, bod) = strip_forall tm
      val (poly_tm, build_result) = parse_sos_goal bod
      val nonneg_th = prove_le0 poly_tm
    in GENL avs (build_result nonneg_th)
    end
    handle e => raise wrap_exn "SOSLib" "REAL_SOS" e;

val REAL_SOS_TAC : tactic = fn (asl, w) =>
    let val th = REAL_SOS w
    in ([], fn _ => th)
    end;

end (* local *)

end (* struct *)
