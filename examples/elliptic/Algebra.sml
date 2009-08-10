(* ========================================================================= *)
(* NORMALIZING ALGEBRAIC EXPRESSIONS                                         *)
(* Copyright (c) 2006 Joe Hurd, distributed under the GNU GPL version 2      *)
(* ========================================================================= *)

structure Algebra :> Algebra =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun exponential _ 0 = 1
  | exponential m 1 = m
  | exponential m n =
    (if n mod 2 = 0 then 1 else m) * exponential (m * m) (n div 2);

fun primeDividesFactorial p =
    let
      fun f k = k + (if k < p then 0 else f (k div p))
    in
      fn n => f (n div p)
    end;

fun multinomial n l =
    let
      fun g p (k,z) = z - primeDividesFactorial p k

      fun f (p,z) =
          z * exponential p (foldl (g p) (primeDividesFactorial p n) l)
    in
      foldl f 1 (Useful.primes_up_to n)
    end;

fun first_multinomial n k = Useful.funpow (k - 1) (fn l => 0 :: l) [n];

val next_multinomial =
    let
      fun f _ _ [] = NONE
        | f z h (0 :: l) = f (0 :: z) h l
        | f z h (k :: l) = SOME (List.revAppend (z, (h + 1) :: (k - 1) :: l))
    in
      fn [] => raise Bug "next_multinomial"
       | h :: t => f [] h t
    end;

fun all_multinomials n k =
    let
      fun f m l =
          let
            val l = m :: l
          in
            case next_multinomial m of NONE => l | SOME m => f m l
          end
    in
      f (first_multinomial n k) []
    end;

(* ------------------------------------------------------------------------- *)
(* A type of algebraic expressions.                                          *)
(* ------------------------------------------------------------------------- *)

(* Invariants: *)
(* 1. A Sum map: *)
(*    a) Does not map any expression to 0. *)
(*    b) Does not map any Sum expressions. *)
(*    c) Does not consist of a single expression mapped to 1. *)
(* 2. A Prod map: *)
(*    a) Does not map any expression to 0. *)
(*    b) Does not map any Prod expressions. *)
(*    c) Does not consist of a single expression mapped to 1. *)

datatype expression =
    Var of string
  | Sum of (expression,int) Map.map
  | Prod of (expression,int) Map.map;

type expressionl = (expression,int) Map.map;

val explCompare : expressionl * expressionl -> order =
    let
      fun cmp (n1,n2) =
          case Int.compare (n1,n2) of
            LESS => GREATER
          | EQUAL => EQUAL
          | GREATER => LESS
    in
      Map.compare cmp
    end;

fun compare (e1,e2) =
    case (e1,e2) of
      (Var v1, Var v2) => String.compare (v1,v2)
    | (Var _, _) => LESS
    | (_, Var _) => GREATER
    | (Sum m1, Sum m2) => explCompare (m1,m2)
    | (Sum _, _) => LESS
    | (_, Sum _) => GREATER
    | (Prod m1, Prod m2) => explCompare (m1,m2);

fun equal e1 e2 = compare (e1,e2) = EQUAL;

fun destVar (Var n) = n
  | destVar _ = raise Error "destVar";

val isVar = can destVar;

fun destSum (Sum n) = n
  | destSum _ = raise Error "destSum";

val isSum = can destSum;

fun destProd (Prod n) = n
  | destProd _ = raise Error "destProd";

val isProd = can destProd;

val explEmpty : expressionl = Map.new compare;

fun explSingle e_n : expressionl = Map.singleton compare e_n;

fun destExplSingle m : expression * int =
    if Map.size m <> 1 then raise Error "destExplSingle"
    else Option.valOf (Map.findl (K true) m);

val isExplSingle = can destExplSingle;

fun explUnit e = explSingle (e,1);

fun destExplUnit m =
    case total destExplSingle m of
      SOME (e,1) => e
    | _ => raise Error "destExplUnit";

val isExplUnit = can destExplUnit;

local
  fun combine (a,b) =
      let
        val c = a + b
      in
        if c = 0 then NONE else SOME c
      end;
in
  val explCombine : expressionl -> expressionl -> expressionl =
      Map.union combine;
end;

fun explCons e_n m = explCombine (explSingle e_n) m;

fun explScale 0 _ = explEmpty
  | explScale 1 m = m
  | explScale n m = Map.transform (fn k => k * n) m;

fun explProdCons (Prod mp, n) m = explCombine m (explScale n mp)
  | explProdCons (e,n) m = explCons (e,n) m;

fun explSumCons (Sum ms, n) m = explCombine m (explScale n ms)
  | explSumCons (e,n) m = explCons (e,n) m;

val zero = Sum explEmpty;

val one = Prod explEmpty;

fun fromInt 0 = zero
  | fromInt 1 = one
  | fromInt n = Sum (explSingle (one,n));

val minusOne = fromInt (~1);

fun toInt (Var _) = NONE
  | toInt (Prod m) = if Map.null m then SOME 1 else NONE
  | toInt (Sum m) =
    if Map.null m then SOME 0
    else
      case total destExplSingle m of
        SOME (Prod m, n) => if Map.null m then SOME n else NONE
      | _ => NONE;

fun isInt exp = Option.isSome (toInt exp);

fun mkSum m =
    case total destExplUnit m of SOME e => e | NONE => Sum m;

fun mkProd m =
    case total destExplUnit m of SOME e => e | NONE => Prod m;

fun add (a,b) =
    mkSum (explSumCons (a,1) (explSumCons (b,1) explEmpty));

fun multiply (a,b) =
    mkProd (explProdCons (a,1) (explProdCons (b,1) explEmpty));

fun negate e = multiply (minusOne,e);

fun subtract (a,b) = add (a, negate b);

fun power e_n = mkProd (explCons e_n explEmpty);

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

local
  val infixes : Parser.infixities =
      [{tok = " ** ", prec = 10, left_assoc = false},
       {tok = " / ",  prec = 8,  left_assoc = true },
       {tok = " * ",  prec = 8,  left_assoc = true },
       {tok = " . ",  prec = 7,  left_assoc = true },
       {tok = " + ",  prec = 6,  left_assoc = true },
       {tok = " - ",  prec = 6,  left_assoc = true }];

  fun expDestInfix (Var _) = NONE
    | expDestInfix (e as Sum m) =
      if isInt e then NONE
      else
        let
          val (e,n) = Option.valOf (Map.findr (K true) m)
          val m = Map.delete m e
        in
          if Map.null m then SOME (".", fromInt n, e)
          else
            let
              val a = Option.getOpt (total destExplUnit m, Sum m)
              and b = if n = 1 then e else Sum (explSingle (e,n))
            in
              SOME ("+",a,b)
            end
        end
    | expDestInfix (e as Prod m) =
      if isInt e then NONE
      else
        let
          val (e,n) = Option.valOf (Map.findr (K true) m)
          val m = Map.delete m e
        in
          if Map.null m then SOME ("**", e, fromInt n)
          else
            let
              val a = Option.getOpt (total destExplUnit m, Prod m)
              and b = if n = 1 then e else Prod (explSingle (e,n))
            in
              SOME ("*",a,b)
            end
        end;

  fun pp_basic_exp pp (Var v, _) = Useful.pp_string pp v
    | pp_basic_exp pp (e,_) =
      case toInt e of
        SOME n => Useful.pp_int pp n
      | NONE => raise Bug "pp_basic_exp";
in
  val pp =
      Useful.pp_map
        (fn e => (e,false))
        (Parser.pp_infixes infixes expDestInfix pp_basic_exp);

  val toString = PP.pp_to_string (!Useful.LINE_LENGTH) pp;
end;

(* ------------------------------------------------------------------------- *)
(* Normalization with a set of equations.                                    *)
(* ------------------------------------------------------------------------- *)

fun explSumExp m 1 = m
  | explSumExp m n =
    let
      fun g (_,_,(_,_,[])) = raise Bug "explSumExp"
        | g (_, _, (c, mp, 0 :: l)) = (c,mp,l)
        | g (e, a, (c, mp, r :: l)) =
          (c * exponential a r, explProdCons (e,r) mp, l)

      fun f multi ms =
          let
            val np = multinomial n multi

            val (np,mp,_) = Map.foldl g (np,explEmpty,multi) m

            val ms = explSumCons (mkProd mp, np) ms
          in
            case next_multinomial multi of
              NONE => ms
            | SOME multi => f multi ms
          end
    in
      f (first_multinomial n (Map.size m)) explEmpty
    end;

local
  fun subtract (e,n,m) : expressionl =
      case Map.peek m e of
        SOME n' => if n = n' then Map.delete m e
                   else raise Error "explSubtract*: wrong exp"
      | NONE => raise Error "explSubtract*: no such base";
in
  fun explSubtract m1 m2 = Map.foldl subtract m1 m2;

  fun explSubtractSingle m (e,n) = subtract (e,n,m);

  fun explSubtractUnit m e = subtract (e,1,m);
end;

fun explProdRewr (Prod l_m, r) m = explProdCons (r,1) (explSubtract m l_m)
  | explProdRewr (l_e,r) m = explProdCons (r,1) (explSubtractUnit m l_e);

fun explProdRewrite eqns m =
    case Useful.first (total (C explProdRewr m)) eqns of
      NONE => raise Error "explProdRewrite"
    | SOME m => m;

local
  fun norm _ (Var _) = raise Error "unchanged"
    | norm eqns (Sum m) =
      let
        fun f (e,n,(changed,m)) =
            case total (norm eqns) e of
              SOME e => (true, explSumCons (e,n) m)
            | NONE => (changed, explSumCons (e,n) m)

        val (changed,m) = Map.foldl f (false,explEmpty) m
      in
        if not changed then raise Error "unchanged" else mkSum m
      end
    | norm eqns (Prod m) =
      case Map.findr (K true) m of
        SOME (e as Sum ms, n) =>
        if Map.null ms then zero
        else
          let
            val m = Map.delete m e

            fun f (e,n,ms) =
                explSumCons (mkProd (explProdCons (e,1) m), n) ms

            val ms = explSumExp ms n
          in
            mkSum (if Map.null m then ms else Map.foldl f explEmpty ms)
          end
      | _ => mkProd (explProdRewrite eqns m);

  fun repeat_norm eqns e =
      case total (norm eqns) e of SOME e => repeat_norm eqns e | NONE => e;
in
  fun normalize {equations} exp =
      let
        val _ = print ("normalize: input =\n" ^ toString exp ^ "\n")
        val exp = repeat_norm equations exp
        val _ = print ("normalize: result =\n" ^ toString exp ^ "\n")
      in
        exp
      end;
end;

(* Quick testing
installPP pp_exp;

val Sum ms = add (add (Var "x", Var "y"), Var "z");

Sum (explSumExp ms 9);

val e = multiply (Var "x", add (fromInt 1, Var "y"));

val e = multiply (Var "x", fromInt (~1));

try normalize [] e;
*)

end
