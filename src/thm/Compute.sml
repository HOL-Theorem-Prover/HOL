(* ========================================================================= *)
(* FILE          : Compute.sml                                               *)
(* DESCRIPTION   : Interpreter for first-order lisp-style terms with natural *)
(*                 numbers.                                                  *)
(*                                                                           *)
(* AUTHORS       : (c) Oskar Abrahamsson, Magnus O. Myreen                   *)
(* DATE          : May 2023, Oskar Abrahamsson                               *)
(* ========================================================================= *)

structure Compute :> Compute =
struct

open Feedback Lib Term;

val ERR = mk_HOL_ERR "Compute";
val WARN = HOL_WARNING "Compute";

type num = Arbnum.num;

type ctsyntax = {
      truth_tm : term,
      false_tm : term,
      cond_tm : term,
      let_tm : term,
      alt_zero_tm : term,
      zero_tm : term,
      suc_tm : term,
      bit1_tm : term,
      bit2_tm : term,
      numeral_tm  : term,
      add_tm : term,
      sub_tm : term,
      mul_tm : term,
      div_tm : term,
      mod_tm : term,
      lt_tm : term,
      cv_pair_tm : term,
      cv_num_tm : term,
      cv_fst_tm : term,
      cv_snd_tm : term,
      cv_ispair_tm : term,
      cv_add_tm : term,
      cv_sub_tm : term,
      cv_mul_tm : term,
      cv_div_tm : term,
      cv_mod_tm : term,
      cv_lt_tm : term,
      cv_if_tm : term,
      cv_eq_tm : term,
      cval_type : hol_type ,
      num_type : hol_type }

infix ##;

local
  fun strip_comb sofar tm =
    if is_comb tm then
      let val (f,x) = dest_comb tm in
        strip_comb (x::sofar) f
      end
    else
      (tm, sofar);
in
  val strip_comb = strip_comb [];
end (* local *)

(* Term does not export dest_eq: *)

fun dest_eq tm =
  case total (((same_const equality ## I) o dest_comb ## I) o dest_comb) tm of
    SOME ((true,l),r) => (l,r)
  | _ => raise ERR "dest_eq" "term is not an equality";

(* -------------------------------------------------------------------------
 * Interpreter for compute expressions.
 * ------------------------------------------------------------------------- *)

datatype binop = Add | Sub | Mul | Divide | Mod | Less | Eq | MkPair;

datatype uop = Fst | Snd | IsPair;

datatype cval = Num of num
              | Pair of cval * cval;

datatype cexp = Const of num
              | Var of int
              | Monop of (cval -> cval) * cexp
              | Binop of (cval -> cval -> cval) * cexp * cexp
              | App of int * cexp list
              | If of cexp * cexp * cexp
              | Let of cexp * cexp;

local
  open Arbnum
in
  val cv_zero = Num zero;
  val cv_one = Num one
end (* local *)

fun env_lookup n xs =
  case xs of
    [] => raise ERR "compute.env_lookup" "Impossible: out of bounds access"
  | x::xs => if n < 1 then x else env_lookup (n - 1) xs;

fun get_code f funs =
  Vector.sub (funs, f)
  handle Subscript =>
  raise ERR "compute.get_code" "Impossible: out of bounds access";

fun exec funs env ce =
  case ce of
    Const n => Num n
  | Var n => env_lookup n env
  | Monop (m, x) => m (exec funs env x)
  | Binop (b, x, y) => b (exec funs env x) (exec funs env y)
  | App (f, xs) => exec funs (exec_list funs env xs [])
                             (get_code f funs)
  | Let (x, y) => exec funs (exec funs env x::env) y
  | If (x, y, z) =>
      exec funs env (if exec funs env x = cv_zero then z else y)
and exec_list funs env xs acc =
  case xs of
    [] => List.rev acc
  | x::xs => exec_list funs env xs (exec funs env x::acc);

local
  open Arbnum
  fun to_num cv =
    case cv of
      Pair _ => zero
    | Num n => n;
  fun do_fst x = case x of Pair (y, z) => y | _ => cv_zero;
  fun do_snd x = case x of Pair (y, z) => z | _ => cv_zero;
  fun do_ispair x = case x of Pair (y, z) => cv_one | _ => cv_zero;
  fun do_mkpair x y = Pair (x, y);
  fun do_add x y = Num (to_num x + to_num y);
  fun do_sub x y = Num (to_num x - to_num y);
  fun do_mul x y = Num (to_num x * to_num y);
  fun do_div x y = Num (to_num x div to_num y) handle Div => cv_zero
  fun do_mod x y = Num (to_num x mod to_num y) handle Div => x
  fun do_eq x y = if x = y then cv_one else cv_zero;
  fun do_less x y =
    case x of Pair _ => cv_zero | Num n =>
    case y of Pair _ => cv_zero | Num m =>
      if n < m then cv_one else cv_zero;
in
  fun monop mop =
    case mop of
      Fst => do_fst
    | Snd => do_snd
    | IsPair => do_ispair;
  fun binop opn =
    case opn of
      MkPair => do_mkpair
    | Add    => do_add
    | Sub    => do_sub
    | Mul    => do_mul
    | Divide => do_div
    | Mod    => do_mod
    | Eq     => do_eq
    | Less   => do_less;
end (* local *)

(* -------------------------------------------------------------------------
 * Destructors for arithmetic.
 * ------------------------------------------------------------------------- *)

fun dest_zero ({alt_zero_tm, zero_tm, ...}:ctsyntax) tm =
  if same_const alt_zero_tm tm orelse same_const zero_tm tm then Arbnum.zero
  else raise ERR "" ""

fun dest_app tm1 tm =
  case total ((same_const tm1 ## I) o dest_comb) tm of
    SOME (true, n) => n
  | _ => raise ERR "" "";

fun dest_bit1 ({bit1_tm, ...} : ctsyntax) = dest_app bit1_tm;

fun dest_bit2 ({bit2_tm, ...} : ctsyntax) = dest_app bit2_tm;

local
  open Arbnum
  fun dest_num ct tm =
    dest_zero ct tm
    handle HOL_ERR _ => two * dest_num ct (dest_bit1 ct tm) + one
    handle HOL_ERR _ => two * dest_num ct (dest_bit2 ct tm) + two;
in
  fun dest_numeral (ct as {numeral_tm, ...}) tm =
    case total (dest_app numeral_tm) tm of
      SOME nt => dest_num ct nt
    | NONE =>
        case total (dest_num ct) tm of
          SOME n => n
        | NONE => raise ERR "dest_numeral" "term is not a numeral";
end (* local *)

(* -------------------------------------------------------------------------
 * Destructors for turning compute value terms into compute expressions.
 * ------------------------------------------------------------------------- *)

local
  datatype token = LET of string * term * term
                 | IF of term * term * term
                 | PAIR of term * term
                 | FST of term
                 | SND of term
                 | ISPAIR of term
                 | ADD of term * term
                 | SUB of term * term
                 | MUL of term * term
                 | DIV of term * term
                 | MOD of term * term
                 | LE of term * term
                 | EQ of term * term
                 | VAR of string
                 | NUM of Arbnum.num
                 | APP of term * term list;
  fun term_to_token ct tm =
    let
      val (f,args) = strip_comb tm
    in
      if same_const f (#let_tm ct) then
        case args of
          [binder,bndexp] =>
            let
              val ((s,_),letbod) = (dest_var ## I) (dest_abs binder)
            in
              SOME (LET (s,bndexp,letbod))
            end
        | _ => NONE
      else if same_const f (#cv_if_tm ct) then
        case args of [x,y,z] => SOME (IF (x,y,z)) | _ => NONE
      else if same_const f (#cv_pair_tm ct) then
        case args of [x,y] => SOME (PAIR (x,y)) | _ => NONE
      else if same_const f (#cv_fst_tm ct) then
        case args of [x] => SOME (FST x) | _ => NONE
      else if same_const f (#cv_snd_tm ct) then
        case args of [x] => SOME (SND x) | _ => NONE
      else if same_const f (#cv_ispair_tm ct) then
        case args of [x] => SOME (ISPAIR x) | _ => NONE
      else if same_const f (#cv_add_tm ct) then
        case args of [x,y] => SOME (ADD (x,y)) | _ => NONE
      else if same_const f (#cv_sub_tm ct) then
        case args of [x,y] => SOME (SUB (x,y)) | _ => NONE
      else if same_const f (#cv_mul_tm ct) then
        case args of [x,y] => SOME (MUL (x,y)) | _ => NONE
      else if same_const f (#cv_div_tm ct) then
        case args of [x,y] => SOME (DIV (x,y)) | _ => NONE
      else if same_const f (#cv_mod_tm ct) then
        case args of [x,y] => SOME (MOD (x,y)) | _ => NONE
      else if same_const f (#cv_lt_tm ct) then
        case args of [x,y] => SOME (LE (x,y)) | _ => NONE
      else if same_const f (#cv_eq_tm ct) then
        case args of [x,y] => SOME (EQ (x,y)) | _ => NONE
      else if same_const f (#cv_num_tm ct) then
        case args of [x] => Option.map NUM (total (dest_numeral ct) x)
                   | _ => NONE
      else if is_var f then
        SOME (VAR (fst (dest_var f)))
      else if is_const f then
        SOME (APP (f, args))
      else
        NONE
    end
  fun mk_monop mop x = Monop (monop mop, x);
  fun mk_binop bop x y = Binop (binop bop, x, y);
in
  fun dest_cexp ct bvs fns tm =
    case partial (ERR "dest_cexp" "term is not a compute value")
         (term_to_token ct) tm of
      NUM n => Const n
    | VAR nm => Var (index (fn x => x = nm) bvs)
    | LET (s,x,y) => Let (dest_cexp ct bvs fns x, dest_cexp ct (s::bvs) fns y)
    | IF (x,y,z) => If (dest_cexp ct bvs fns x,
                        dest_cexp ct bvs fns y,
                        dest_cexp ct bvs fns z)
    | FST x => mk_monop Fst (dest_cexp ct bvs fns x)
    | SND x => mk_monop Snd (dest_cexp ct bvs fns x)
    | ISPAIR x => mk_monop IsPair (dest_cexp ct bvs fns x)
    | PAIR (x,y) => mk_binop MkPair (dest_cexp ct bvs fns x)
                                    (dest_cexp ct bvs fns y)
    | ADD (x,y) => mk_binop Add (dest_cexp ct bvs fns x)
                                (dest_cexp ct bvs fns y)
    | SUB (x,y) => mk_binop Sub (dest_cexp ct bvs fns x)
                                (dest_cexp ct bvs fns y)
    | MUL (x,y) => mk_binop Mul (dest_cexp ct bvs fns x)
                                (dest_cexp ct bvs fns y)
    | DIV (x,y) => mk_binop Divide (dest_cexp ct bvs fns x)
                                   (dest_cexp ct bvs fns y)
    | MOD (x,y) => mk_binop Mod (dest_cexp ct bvs fns x)
                                (dest_cexp ct bvs fns y)
    | LE (x,y) => mk_binop Less (dest_cexp ct bvs fns x)
                                (dest_cexp ct bvs fns y)
    | EQ (x,y) => mk_binop Eq (dest_cexp ct bvs fns x)
                              (dest_cexp ct bvs fns y)
    | APP (f,xs) =>
        case Vector.findi (same_const f o fst o snd) fns of
          SOME (i, _) => App (i, List.map (dest_cexp ct bvs fns) xs)
        | _ => raise ERR "dest_cexp"
                         ("could not find equation for: " ^ fst (dest_const f))
end (* local *)

(* -------------------------------------------------------------------------
 * Constructors for creating compute value terms from interpreter results.
 * ------------------------------------------------------------------------- *)

local
  open Arbnum;
  fun even n = mod2 n = zero;
in
  fun mk_numeral ({alt_zero_tm, bit1_tm, bit2_tm, ...} : ctsyntax) =
    let
      fun mk_num n =
        if n = zero then
          alt_zero_tm
        else if even n then
          mk_comb (bit2_tm, mk_num (div2 (n - two)))
        else
          mk_comb (bit1_tm, mk_num (div2 (n - one)))
    in
      mk_num
    end;
end (* local *)

fun mk_num ({cv_num_tm, numeral_tm, ...} : ctsyntax) t =
  mk_comb (cv_num_tm, mk_comb (numeral_tm, t));

fun mk_pair ({cv_pair_tm, ...} : ctsyntax) s t =
  mk_comb (mk_comb (cv_pair_tm, s), t);

fun mk_cval_term ct cv =
  case cv of
    Num n => mk_num ct (mk_numeral ct n)
  | Pair (p, q) => mk_pair ct (mk_cval_term ct p) (mk_cval_term ct q);

(* -------------------------------------------------------------------------
 * [dest_code_eqn] takes apart a code equation and performs a type check at the
 * same time:
 * - the equation is on the form 'f v1 ... vN = rhs'
 * - all 'vi' are variables with type ':cval_type'
 * - 'rhs' is closed under the variables 'vi' and has type ':cval_type'
 * - 'f' and all constants in 'rhs' have code equations
 * ------------------------------------------------------------------------- *)

fun dest_eqn ({cval_type, ...} : ctsyntax) tm =
  case total dest_eq tm of
    SOME (l, r) =>
      if type_of r = cval_type then (l, r)
      else raise ERR "dest_code_eqn" "not a code equation"
  | _ => raise ERR "dest_code_eqn" "not a code equation";

fun dest_lhs ({cval_type, ...} : ctsyntax) tm =
  let
    val (f,args) = strip_comb tm
  in
    if is_const f andalso not (List.null args) then
      if List.all (fn t => is_var t andalso type_of t = cval_type) args then
        (f, args)
      else
        raise ERR "dest_code_eqn" "term lhs has non-cexp variable"
    else
      raise ERR "dest_code_eqn"
                "term lhs is not a constant applied to variables"
  end;

local
  fun term_consts sofar tm =
    if is_const tm then
      HOLset.add (sofar,tm)
    else if is_comb tm then
      let val (l, r) = dest_comb tm in
        term_consts (term_consts sofar l) r
      end
    else if is_abs tm then
      term_consts sofar (snd (dest_abs tm))
    else sofar;
  fun consts tm = HOLset.listItems (term_consts empty_tmset tm);
in
  fun dest_code_eqn ct fns th =
    let
      val (l, r) = dest_eqn ct th
      val (f, vs) = dest_lhs ct l
      val fns = HOLset.addList (empty_tmset, fns)
      val vars = HOLset.addList (empty_varset, vs)
    in
      if List.all (fn tm => HOLset.member (fns, tm)) (consts f) then
        if List.all (fn tm => HOLset.member (vars, tm)) (free_vars r) then
          (f, (List.map (fst o dest_var) vs, r))
        else raise ERR "dest_code_eqn" "free variables"
      else raise ERR "dest_code_eqn" "unknown constant"
    end;
end (* local *)

(* -------------------------------------------------------------------------
 * [check_thms] checks that compute value terms satisfy their characteristic
 * equations. For example: we expect [SUC] and [+] to satisfy this equation:
 *   |- SUC m + n = SUC (m + n).
 * ------------------------------------------------------------------------- *)

local
  open Type
  infixr 3 -->
  infix 2 ===
  fun op === (l,r) = fn tm =>
    case total dest_eq tm of SOME (s,t) => l s andalso r t | _ => false;
  fun APP1 l r tm =
    case total dest_comb tm of
      SOME (s,t) => l s  andalso r t
    | _ => false;
  fun APP2 a b c tm =
    case total ((dest_comb ## I) o dest_comb) tm of
      SOME ((x,y),z) => a x andalso b y andalso c z
    | _ => false;
  fun APP3 a b c d tm =
    case total (((dest_comb ## I) o dest_comb ## I) o dest_comb) tm of
      SOME (((x,y),z),w) => a x andalso b y andalso c z andalso d w
    | _ => false;
  fun mk_recs (ct : ctsyntax) =
    let
      fun var n t tm = total dest_var tm = SOME (n, t)
      val T = same_const (#truth_tm ct)
      and F = same_const (#false_tm ct)
      val N_ = var "n" (#num_type ct)
      val M_ = var "m" (#num_type ct)
      val P_ = var "p" (#cval_type ct)
      val Q_ = var "q" (#cval_type ct)
      val R_ = var "r" (#cval_type ct)
      val S_ = var "s" (#cval_type ct)
      val F_ = var "f" (alpha --> beta)
      val A_ = var "a" alpha
      val B_ = var "b" alpha
      val X_ = var "x" alpha
      val COND = APP3 (same_const (#cond_tm ct))
      val NUMERAL = APP1 (same_const (#numeral_tm ct))
      val ALT_ZERO = same_const (#alt_zero_tm ct)
      val ZERO = same_const (#zero_tm ct)
      val BIT1 = APP1 (same_const (#bit1_tm ct))
      val BIT2 = APP1 (same_const (#bit2_tm ct))
      val SUC = APP1 (same_const (#suc_tm ct))
      val ADD = APP2 (same_const (#add_tm ct))
      val SUB = APP2 (same_const (#sub_tm ct))
      val MUL = APP2 (same_const (#mul_tm ct))
      val DIV = APP2 (same_const (#div_tm ct))
      val MOD = APP2 (same_const (#mod_tm ct))
      val LT = APP2 (same_const (#lt_tm ct))
      val CV_PAIR = APP2 (same_const (#cv_pair_tm ct))
      val CV_NUM = APP1 (same_const (#cv_num_tm ct))
      val CV_FST = APP1 (same_const (#cv_fst_tm ct))
      val CV_SND = APP1 (same_const (#cv_snd_tm ct))
      val CV_ISPAIR = APP1 (same_const (#cv_ispair_tm ct))
      val CV_ADD = APP2 (same_const (#cv_add_tm ct))
      val CV_SUB = APP2 (same_const (#cv_sub_tm ct))
      val CV_MUL = APP2 (same_const (#cv_mul_tm ct))
      val CV_DIV = APP2 (same_const (#cv_div_tm ct))
      val CV_MOD = APP2 (same_const (#cv_mod_tm ct))
      val CV_LT = APP2 (same_const (#cv_lt_tm ct))
      val CV_IF = APP3 (same_const (#cv_if_tm ct))
      val CV_EQ = APP2 (same_const (#cv_eq_tm ct))
      val LET = APP2 (same_const (#let_tm ct))
    in
      [("alt_zero",   ALT_ZERO === ZERO),
       ("cond_T",     COND T A_ B_ === A_),
       ("cond_F",     COND F A_ B_ === B_),
       ("numeral",    NUMERAL N_ === N_),
       ("bit1",       BIT1 N_ === ADD N_ (ADD N_ (SUC ZERO))),
       ("bit2",       BIT2 N_ === ADD N_ (ADD N_ (SUC (SUC ZERO)))),
       ("add1",       ADD ZERO N_ === N_),
       ("add2",       ADD (SUC M_) N_ === SUC (ADD M_ N_)),
       ("sub1",       SUB ZERO M_ === ZERO),
       ("sub2",       SUB (SUC M_) N_ ===
                      COND (LT M_ N_) ZERO (SUC (SUB M_ N_))),
       ("mul1",       MUL ZERO N_ === ZERO),
       ("mul2",       MUL (SUC M_) N_ === ADD (MUL M_ N_) N_),
       ("div",        DIV M_ N_ ===
                      COND (N_ === ZERO) ZERO
                           (COND (LT M_ N_) ZERO (SUC (DIV (SUB M_ N_) N_)))),
       ("mod",        MOD M_ N_ ===
                      COND (N_ === ZERO) M_
                           (COND (LT M_ N_) M_ (MOD (SUB M_ N_) N_))),
       ("lt1",        LT M_ ZERO === F),
       ("lt2",        LT M_ (SUC N_) === COND (M_ === N_) T (LT M_ N_)),
       ("suc1",       (SUC M_ === ZERO) === F),
       ("suc2",       (SUC M_ === SUC N_) === (M_ === N_)),
       ("cval1",      (CV_PAIR P_ Q_ === CV_PAIR R_ S_) ===
                      (COND (P_ === R_) (Q_ === S_) F)),
       ("cval2",      (CV_PAIR P_ Q_ === CV_NUM N_ ) === F),
       ("cval3",      (CV_NUM M_ === CV_NUM N_ ) === (M_ === N_)),
       ("cv_add1",    CV_ADD (CV_NUM M_) (CV_NUM N_) === CV_NUM (ADD M_ N_)),
       ("cv_add2",    CV_ADD (CV_NUM M_) (CV_PAIR P_ Q_) === CV_NUM M_),
       ("cv_add3",    CV_ADD (CV_PAIR P_ Q_) (CV_NUM N_) === CV_NUM N_),
       ("cv_add4",    CV_ADD (CV_PAIR P_ Q_) (CV_PAIR R_ S_) === CV_NUM ZERO),
       ("cv_sub1",    CV_SUB (CV_NUM M_) (CV_NUM N_) === CV_NUM (SUB M_ N_)),
       ("cv_sub2",    CV_SUB (CV_NUM M_) (CV_PAIR P_ Q_) === CV_NUM M_),
       ("cv_sub3",    CV_SUB (CV_PAIR P_ Q_) (CV_NUM N_) === CV_NUM ZERO),
       ("cv_sub4",    CV_SUB (CV_PAIR P_ Q_) (CV_PAIR R_ S_) === CV_NUM ZERO),
       ("cv_mul1",    CV_MUL (CV_NUM M_) (CV_NUM N_) === CV_NUM (MUL M_ N_)),
       ("cv_mul2",    CV_MUL (CV_NUM M_) (CV_PAIR P_ Q_) === CV_NUM ZERO),
       ("cv_mul3",    CV_MUL (CV_PAIR P_ Q_) (CV_NUM N_) === CV_NUM ZERO),
       ("cv_mul4",    CV_MUL (CV_PAIR P_ Q_) (CV_PAIR R_ S_) === CV_NUM ZERO),
       ("cv_div1",    CV_DIV (CV_NUM M_) (CV_NUM N_) === CV_NUM (DIV M_ N_)),
       ("cv_div2",    CV_DIV (CV_NUM M_) (CV_PAIR P_ Q_) === CV_NUM ZERO),
       ("cv_div3",    CV_DIV (CV_PAIR P_ Q_) (CV_NUM N_) === CV_NUM ZERO),
       ("cv_div4",    CV_DIV (CV_PAIR P_ Q_) (CV_PAIR R_ S_) === CV_NUM ZERO),
       ("cv_mod1",    CV_MOD (CV_NUM M_) (CV_NUM N_) === CV_NUM (MOD M_ N_)),
       ("cv_mod2",    CV_MOD (CV_NUM M_) (CV_PAIR P_ Q_) === CV_NUM M_),
       ("cv_mod3",    CV_MOD (CV_PAIR P_ Q_) (CV_NUM N_) === CV_NUM ZERO),
       ("cv_mod4",    CV_MOD (CV_PAIR P_ Q_) (CV_PAIR R_ S_) === CV_NUM ZERO),
       ("cv_lt1",     CV_LT (CV_NUM M_) (CV_NUM N_) ===
                      CV_NUM (COND (LT M_ N_) (SUC ZERO) ZERO)),
       ("cv_lt2",     CV_LT (CV_NUM M_) (CV_PAIR P_ Q_) === CV_NUM ZERO),
       ("cv_lt3",     CV_LT (CV_PAIR P_ Q_) (CV_NUM N_) === CV_NUM ZERO),
       ("cv_lt4",     CV_LT (CV_PAIR P_ Q_) (CV_PAIR R_ S_) === CV_NUM ZERO),
       ("cv_if1",     CV_IF (CV_NUM (SUC M_)) P_ Q_ === P_),
       ("cv_if2",     CV_IF (CV_NUM ZERO) P_ Q_ === Q_),
       ("cv_if3",     CV_IF (CV_PAIR R_ S_) P_ Q_ === Q_),
       ("cv_fst1",    CV_FST (CV_PAIR P_ Q_) === P_),
       ("cv_fst2",    CV_FST (CV_NUM M_) === CV_NUM ZERO),
       ("cv_snd1",    CV_SND (CV_PAIR P_ Q_) === Q_),
       ("cv_snd2",    CV_SND (CV_NUM M_) === CV_NUM ZERO),
       ("cv_ispair1", CV_ISPAIR (CV_PAIR P_ Q_) === CV_NUM (SUC ZERO)),
       ("cv_ispair2", CV_ISPAIR (CV_NUM M_) === CV_NUM ZERO),
       ("cv_eq",      CV_EQ P_ Q_ ===
                      CV_NUM (COND (P_ === Q_) (SUC ZERO) ZERO)),
       ("let",        LET F_ X_ === APP1 F_ X_)]
    end
in
  fun check_thms ct ths =
    let
      val recs = mk_recs ct
      fun check xs ys =
        case (xs, ys) of
          ([], []) => ()
        | ([], _) => raise ERR "check_thms" "too many equations provided"
        | (_, []) => raise ERR "check_thms" "too few equations provided"
        | ((nm1,f)::xs, (nm2,tm)::ys) =>
            if nm1 = nm2 then
              if f tm then
                check xs ys
              else
                raise ERR "check_thms" ("check failed for equation: " ^ nm1)
            else
              raise ERR "check_thms" ("name mismatch at: " ^ nm2 ^
                                      " (should be: " ^ nm1 ^ ")")
    in
      check recs ths
    end
end (* local *)

(* -------------------------------------------------------------------------
 * Entry-point: [term_compute] takes a collection of compute value terms, a list
 * of characteristic equations (indexed by name), a list of code equations,
 * and a term. (The checks of compute values terms and types and characteristic
 * can be cached.)
 * ------------------------------------------------------------------------- *)

fun term_compute {cval_terms, cval_type, num_type, char_eqns } =
  let
    fun get name =
      Lib.assoc name cval_terms
      handle HOL_ERR _ => raise ERR "compute" (name ^ " is not in cval_terms")
    val ct = {
      truth_tm = get "truth",
      false_tm = get "false",
      cond_tm = get "cond",
      let_tm = get "let",
      alt_zero_tm = get "alt_zero",
      zero_tm = get "zero",
      suc_tm = get "suc",
      bit1_tm = get "bit1",
      bit2_tm = get "bit2",
      numeral_tm  = get "numeral",
      add_tm = get "add",
      sub_tm = get "sub",
      mul_tm = get "mul",
      div_tm = get "div",
      mod_tm = get "mod",
      lt_tm = get "lt",
      cv_pair_tm = get "cv_pair",
      cv_num_tm = get "cv_num",
      cv_fst_tm = get "cv_fst",
      cv_snd_tm = get "cv_snd",
      cv_ispair_tm = get "cv_ispair",
      cv_add_tm = get "cv_add",
      cv_sub_tm = get "cv_sub",
      cv_mul_tm = get "cv_mul",
      cv_div_tm = get "cv_div",
      cv_mod_tm = get "cv_mod",
      cv_lt_tm = get "cv_lt",
      cv_if_tm = get "cv_if",
      cv_eq_tm = get "cv_eq",
      cval_type = cval_type,
      num_type = num_type }
    val _ = check_thms ct char_eqns
  in
    fn code_eqs => fn tm =>
      let
        (* all function constants from the left-hand sides of code equations *)
        val fns = List.map (fst o strip_comb o fst o dest_eq) code_eqs
        (* vector with (const * (variables * rhs)) *)
        val eqs = Vector.map (dest_code_eqn ct fns) (Vector.fromList code_eqs)
        (* replace functions and variables with indices, with dest_cexp: *)
        val code = Vector.map (fn (_,(bvs,r)) => dest_cexp ct bvs eqs r) eqs
        val cexp = dest_cexp ct [] eqs tm
        val cval = exec code [] cexp
      in
        mk_cval_term ct cval
      end
  end;

end (* struct *)

