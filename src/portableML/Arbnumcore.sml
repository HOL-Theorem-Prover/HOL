(* Author: Michael Norrish *)

(* very simple-minded implementation of arbitrary precision natural
   numbers *)

structure Arbnumcore :> Arbnumcore =
struct

(* app load ["Substring", "Random", "Int", "Process"] *)

fun extract arg = ArraySlice.vector(ArraySlice.slice arg)

fun copyVec' {di,dst,len,src,si} = let
  val v = VectorSlice.vector(VectorSlice.slice(src,si,len));
in
  Array.copyVec {di = di, dst = dst, src = v}
end


(* base must be <= the sqrt of MaxInt *)
val BASE = 10000;
val BASEless1 = BASE - 1;

type num = int list

fun asList x = x

(* each element in the list is in the range 0 - (BASE - 1), least significant
   "digit" is the first element in the list. *)

val zero = [0];
val one = [1];
val two = [2];

fun plus1 [] = raise Fail "Should never happen"
  | plus1 [n] = if n = BASEless1 then [0, 1] else [n + 1]
  | plus1 (n::xs) = if n = BASEless1 then 0::plus1 xs else (n + 1)::xs

fun less1 [] = raise Fail "arbnum invariant falsified"
  | less1 [x] = if x = 0 then raise Fail "Can't take one off zero"
                else [x - 1]
  | less1 (0::xs) = BASEless1::less1 xs
  | less1 (x::xs) = (x - 1)::xs
val less2 = less1 o less1

val plus2 = plus1 o plus1

fun times2 [] = []
  | times2 [x] = if 2 * x < BASE then [2 * x] else [2 * x - BASE, 1]
  | times2 (x::xs) =
      if 2 * x < BASE then (2 * x)::(times2 xs)
      else (2 * x - BASE)::(plus1 (times2 xs))

fun revdiv2 [] = []
  | revdiv2 [x] = [x div 2]
  | revdiv2 (x::y::xs) = let
      val dividend = x div 2
      val remainder = x mod 2
    in
      dividend::(revdiv2 ((remainder * BASE) + y::xs))
    end

fun div2 n = let
  val n' = List.rev n
  fun strip [] = []
    | strip [x] = [x]
    | strip (0::xs) = strip xs
    | strip (y as (x::xs)) = y
in
  List.rev (strip (revdiv2 n'))
end

fun mod2 (x::_) = [x mod 2]
  | mod2 [] = raise Fail "arbnum representation invariant violated"

fun fromInt n = let
  val _ = n >= 0 orelse raise Overflow
  val dividend = n div BASE
  val rem = n mod BASE
in
  rem::(if dividend > 0 then fromInt dividend else [])
end

fun toInt [] = 0
  | toInt (x::xs) = Int.+(x, Int.*(BASE, toInt xs))



fun (x + y) = addwc x y false
and
(* add with carry *)
  addwc xn yn b =
  case xn of
    [] =>
      if b then
        if null yn then one else plus1 yn
      else yn
  | (x::xs) => let
    in
      case yn of
        [] =>
          if b then
            if null xn then one else plus1 xn
          else xn
      | (y::ys) => let
          val xy = Int.+(x, y)
          val xyc = if b then Int.+(xy, 1) else xy
          val (carry, rem) = if xyc >= BASE then (true, Int.-(xyc, BASE))
                             else (false, xyc)
        in
          rem::(addwc xs ys carry)
        end
    end

fun floor r = let
  val _ = 0.0 <= r orelse raise Overflow
  fun count_base_powers r =
      (Real.floor r, 0)
      handle Overflow => let
               val (res, n) = count_base_powers (r / real BASE)
             in
               (res, Int.+(n,1))
             end
  val (sig_part, exp) = count_base_powers r
  fun shl n a = if n = 0 then a else shl (n - 1) (0 :: a)
  fun exp_r n r = if n = 0 then r else exp_r (n - 1) (r * real BASE)
  val sig_anum = shl exp (fromInt sig_part)
  val sig_real = exp_r exp (real sig_part)
in
  if exp > 0 then sig_anum + floor (r - sig_real)
  else sig_anum
end

fun toReal anum = List.foldl (fn (i,acc) => Real.+(acc * real BASE, real i))
                             0.0 (List.rev anum)

(*   x0 + 1000x < y0 + 1000y   (where x,y < BASE
   =
*)
fun (xn < yn) =
  case (xn, yn) of
    (_, []) => false
  | ([], _) => true
  | (x::xs, y::ys) => xs < ys orelse (xs = ys andalso Int.<(x,y))
fun (xn <= yn) = xn = yn orelse xn < yn
fun (xn >= yn) = yn <= xn
fun (xn > yn) = yn < xn

fun compare(x,y) = if x < y then LESS else if y < x then GREATER else EQUAL

fun normalise [] = [0]
  | normalise x = let
      fun strip_leading_zeroes [] = []
        | strip_leading_zeroes (list as n::ns) =
        if n = 0 then strip_leading_zeroes ns else list
      val x' = List.rev (strip_leading_zeroes (List.rev x))
    in
      if null x' then [0] else x'
    end

fun (xn - yn) =
  if xn < yn then zero else normalise (subwc xn yn false)
and subwc xn yn b =
  case (xn, yn) of
    (_, []) => if b then less1 xn else xn
  | ([], _) => zero
  | (x::xs, y::ys) => let
      val (x', carry) =
        if b then
          if Int.<=(x,y) then (Int.-(Int.+(x,BASEless1), y), true)
          else (Int.-(Int.-(x,y), 1), false)
        else
          if Int.<(x,y) then (Int.-(Int.+(x, BASE), y), true)
          else (Int.-(x,y), false)
    in
      x'::subwc xs ys carry
    end

(* (x0 + BASEx) * y = x0 * y + BASE * x * y *)
fun single_digit(n, xn) =
  case n of
    0 => zero
  | 1 => xn
  | 2 => times2 xn
  | _ => let
      fun f [] = []
        | f (x::xs) = let
            val newx = Int.*(n,x)
            val (rem, carry) = (Int.mod(newx, BASE), Int.div(newx,BASE))
          in
            if carry = 0 then rem::f xs
            else rem::(f xs + [carry])
          end
    in
      f xn
    end


fun (xn * yn) =
  case (xn, yn) of
    ([], _) => zero
  | (_, []) => zero
  | (x::xs, _) => normalise(single_digit(x, yn) + (0::(xs * yn)))

fun pow (xn, yn) =
  if mod2 yn = one then
    (xn * pow(xn, less1 yn))
  else
    if yn = zero then
      one
    else
      pow((xn * xn), div2 yn);

fun replicate n el = List.tabulate(n, fn _ => el)
(* returns result in wrong order *)
fun comp_sub acc carry (xn, yn) =
  case (xn, yn) of
    ([], []) => (acc, carry)
  | (x::xs, y::ys) => let
      val (res, newcarry) =
        if carry then
          if Int.>(x, y) then
            (Int.-(x, Int.+(y, 1)), false)
          else
            (Int.-(Int.+(x, BASEless1), y), true)
        else
          if Int.>=(x, y) then
            (Int.-(x, y), false)
          else
            (Int.-(Int.+(x,BASE), y), true)
    in
      comp_sub (res::acc) newcarry (xs, ys)
    end
  | _ => raise Fail "comp_sub : arguments of different length"


(* y < BASE *)
fun single_divmod (xn:int list) (y:int) = let
  val xnr = List.rev xn
  fun loop xn acc =
    case xn of
      [] => raise Fail "single_divmod: can't happen"
    | [x] => let
        val q = Int.div(x, y)
      in
        (q::acc, [Int.mod(x,y)])
      end
    | [x1, x2] => let
        val x = Int.+(Int.*(x1, BASE), x2)
        val q = Int.div(x, y)
      in
        ((fromInt q) @ acc, [Int.mod(x, y)])
      end
    | (x1::x2::xs) => let
        val x = Int.+(Int.*(x1, BASE), x2)
        val q = Int.div(x, y)
        val r = Int.mod(x, y)
        (* r < y, so r < BASE *)
      in
        loop (r::xs) ((fromInt q) @ acc)
      end
  val _ = y <> 0 orelse raise Div
  val (q, r) = loop xnr []
in
  (normalise q, normalise r)
end


fun divmod (xn, yn) =
  if yn = zero then raise Div
  else let

    (* following algorithm from Knuth 4.3.1 Algorith D *)
    (* we require
       - that length vn > 1
       - that length un >= length vn
       - that hd vn <> 0
     *)
    fun KnuthD un vn = let
      (* Knuth's algorithm is stateful so we mimic it here with
       two arrays u and v *)
      val d = Int.div(BASE, Int.+(List.last vn, 1))
      val n = length vn
      val m = Int.-(length un, length vn)
      val normalised_u = single_digit(d, un)
      val normalised_v = single_digit(d, vn)
      val _ = length normalised_v = length vn orelse
        raise Fail "normalised_v not same length as v"
      val norm_v_rev = List.rev normalised_v
      val v1 = hd norm_v_rev
      val v2 = hd (tl norm_v_rev)
      val norm_u_rev =
        if (length normalised_u = length un) then 0::List.rev normalised_u
        else List.rev normalised_u
      val u = Array.fromList norm_u_rev
      val _ = Array.length u = Int.+(m, Int.+(n, 1)) orelse
        raise Fail "Array u of unexpected length"
      val q = Array.array(Int.+(m, 1), 0)
      fun inner_loop j = let
        infix 9 sub
        open Array
        (* D3. Calculate q hat *)
        fun qhat_test qhat = let
          open Int
        in
          v2 * qhat >
          (u sub j * BASE + u sub (j + 1) - qhat * v1) * BASE + u sub (j + 2)
        end
        val qhat0 = let
          open Int
        in
          if u sub j = v1 then BASEless1
          else ((u sub j) * BASE + (u sub (j + 1)))  div v1
        end
        val qhat =
          if qhat_test qhat0 then
            if qhat_test (Int.-(qhat0, 1)) then Int.-(qhat0, 2)
            else Int.-(qhat0, 1)
          else
            qhat0
        (* D4. multiply and subtract *)
        val uslice_v = extract(u, j, SOME (Int.+(n, 1)))
        val uslice_l = List.rev (Vector.foldr (op::) [] uslice_v)
        val multiply_result0 = single_digit(qhat, normalised_v)
        val multiply_result = let
          val mr_len = List.length multiply_result0
          val u_len = List.length uslice_l
        in
          if  mr_len <> u_len then
            multiply_result0 @ replicate (Int.-(u_len, mr_len)) 0
          else
            multiply_result0
        end
        val (newu_l, d4carry) = comp_sub [] false (uslice_l, multiply_result)
        val newu_v = Vector.fromList newu_l
        val _ = copyVec' {di=j, dst=u, len=NONE, src=newu_v, si=0}
        (* D5. test remainder *)
        val () = update(q, j, qhat)
        val _ =
          if d4carry then let
            (* D6. Add back *)
            val uslice_v = extract(u, j, SOME (Int.+(n, 1)))
            val uslice_l = List.rev(Vector.foldr (op::) [] uslice_v)
            val newu0 = uslice_l + normalised_v
            (* have to ignore rightmost digit *)
            val newu = List.drop(List.rev newu0, 1);
            val newu_v = Vector.fromList newu
          in
            update(q, j, Int.-(q sub j, 1));
            copyVec' {di = j, dst = u, len = NONE, src = newu_v, si = 0}
          end
          else ()
        open Int
      in
        if j + 1 <= m then inner_loop (j + 1)
        else ()
      end
      val unnormal_result = inner_loop 0
      val qn = normalise (List.rev (Array.foldr (op::) [] q))
      val rn0 = let
        open Int
      in
        normalise (List.rev
                   (Vector.foldr (op::) [] (extract(u, m + 1, NONE))))
      end
      val rn = #1 (single_divmod rn0 d)
    in
      (qn, rn)
    end
  in
    if length yn = 1 then
      single_divmod xn (hd yn)
    else
      if Int.>(length yn, length xn) then
        (zero, xn)
      else
        KnuthD xn yn
  end

fun (xn div yn) = #1 (divmod (xn, yn))
fun (xn mod yn) = #2 (divmod (xn, yn))

local
  fun recurse x n = if x = zero then n else recurse (div2 x) (plus1 n)
 in
  fun log2 x = if x = zero then raise Domain else recurse (div2 x) zero
end

local
  fun gcd' i j = let
    val r = i mod j
  in
    if r = zero then j else gcd' j r
  end
in
fun gcd(i,j) = if i = zero then j
               else if j = zero then i
               else if i < j then gcd' j i
               else gcd' i j
end

fun intexp(base,exponent) = let
  fun recurse acc b n =
      if Int.<=(n,0) then acc
      else if Int.mod(n,2) = 1 then
        recurse (Int.*(acc, b)) b (Int.-(n,1))
      else recurse acc (Int.*(b,b)) (Int.div(n,2))
in
  recurse 1 base exponent
end

fun genFromString rdx = let
  open StringCvt
  val (base, chunksize, chunkshift) =
      case rdx of
        BIN => (2, 10, fromInt 1024)
      | OCT => (8, 5, fromInt 32768)
      | DEC => (10, 5, fromInt 100000)
      | HEX => (16, 5, fromInt 1048576)
  val scanner = Int.scan rdx
  fun readchunk s = StringCvt.scanString scanner s
  fun recurse acc s = let
    val sz = size s
  in
    if Int.<=(sz, chunksize) then
      fromInt (intexp(base,sz)) * acc + fromInt (valOf (readchunk s))
    else let
        val sz_less_cs = Int.-(sz, chunksize)
        val pfx = substring(s, 0, chunksize)
        val sfx = String.extract(s, chunksize, NONE)
      in
        recurse (chunkshift * acc + fromInt (valOf (readchunk pfx))) sfx
      end
  end
in
  recurse zero
end handle Option => raise Fail "String not numeric"
val fromHexString = genFromString StringCvt.HEX
val fromOctString = genFromString StringCvt.OCT
val fromBinString = genFromString StringCvt.BIN
val fromString = genFromString StringCvt.DEC


fun toString n =
  if n = zero then "0"
  else let
    fun nonzero_recurse n =
      if n = zero then ""
      else let
        val (q,r) = divmod(n, fromInt 10)
      in
        nonzero_recurse q^Int.toString (toInt r)
      end
  in
    nonzero_recurse n
  end


local
  fun toChar n =
      str (if Int.<(n, 10)
           then chr (Int.+(ord #"0", n))
           else chr (Int.-(Int.+(ord #"A", n), 10)))
  fun toBaseString base n =
    let val (q,r) = divmod(n, base)
        val s = toChar (toInt r)
  in
    if q = zero then s else toBaseString base q^s
  end
in
  val toBinString = toBaseString (fromInt 2)
  val toOctString = toBaseString (fromInt 8)
  val toHexString = toBaseString (fromInt 16)
end

(*  useful test code follows
exception ArgsBad;


fun test_op (nf, origf, P, print_opn, testresult) arg1 arg2 = let
  val _ = P (arg1, arg2) orelse raise ArgsBad
  val orig_result = origf(arg1, arg2)
  val new_result = nf(fromInt arg1, fromInt arg2)
  val ok = testresult(new_result, orig_result)
in
  print (Int.toString arg1^print_opn^Int.toString arg2);
  if ok then print " agree\n"
  else (print " disagree\n"; raise Fail "Urk")
end

fun test n opdetails = let
  open Random
  val gen = newgen()
  fun do_test () = let
    val arg1 = range (0, 60000000) gen
    val arg2 = range (0, 60000000) gen
  in
    test_op opdetails arg1 arg2
  end
  fun doit_until_success f = f ()
    handle Fail s => raise Fail s
         | Interrupt => raise Interrupt
         | _ => doit_until_success f
  fun doit f n = if Int.<=(n, 0) then () else (doit_until_success f ;
                                               doit f (Int.-(n,1)))
in
  doit do_test n
end

fun testintresult (new, old) = toInt new = old
val test_addition = (op+, Int.+, (fn _ => true), " + ", testintresult);
val test_less = (op<, Int.<, (fn _ => true), " < ", op=);
val test_leq = (op<=, Int.<=, (fn _ => true), " <= ", op=);
val test_subtraction = (op-, Int.-, (fn (x,y) => Int.>=(x,y)), " - ", testintresult)
val test_mult = (op*, Int.*, (fn _ => true), " * ", testintresult)
val test_div = (op div, Int.div, (fn(x,y) => y <> 0), " div ", testintresult);
val test_mod = (op mod, Int.mod, (fn(x,y) => y <> 0), " mod ", testintresult);

val _ = test_op test_addition 78826 3251
val _ = test_op test_div 49772146 458048
val _ = test_op test_mod 34182186 2499
val _ = test_op test_mod 26708509 29912224
val _ = test_op test_div 6258 42171
val _ = test_op test_div 6 13766
val _ = test_op test_mod 6 13766
val _ = test_op test_mod 38294758 10769
val _ = test_op test_div 38294758 10769

val _ = test 200 test_addition
val _ = test 200 test_less
val _ = test 200 test_leq
val _ = test 200 test_subtraction
(* val _ = test 30 test_mult *)
val _ = test 200 test_div
val _ = test 200 test_mod

exception FailedProp
fun testproperty3 (f, printprop) = let
  val gen = Random.newgen()
  fun generate_arg () = let
    val size = Random.range(1,8) gen
  in
    normalise (Random.rangelist(0,BASE) (size, gen))
  end
  val x = generate_arg()
  val y = generate_arg()
  val z = generate_arg()
  val propstring =
    "Property "^printprop^" for x = "^toString x^", y = "^toString y^
    ", z = "^toString z^"..."
in
  print propstring;
  if f(x,y,z) then print "OK\n"
  else (print "FAILED\n"; raise FailedProp)
end

fun testprop n prop = if Int.<=(n, 0) then ()
                      else (testproperty3 prop; testprop (Int.-(n,1)) prop) handle FailedProp => Process.exit Process.failure

val addition_associative =
  ((fn (x,y,z) => (x + (y + z) = (x + y) + z)),
   "(x + (y + z) = (x + y) + z)")
val mult_assoc =
  ((fn (x,y,z) => x * (y * z) = (x * y) * z),
   "x * (y * z) = (x * y) * z")
val distrib =
  ((fn (x,y,z) => x * (y + z) = (x * y) + (x * z)),
   "x * (y + z) = (x * y) + (x * z)")
val divmod_test =
  ((fn (x,y,z) => if y <> zero then (x div y) * y + (x mod y) = x else true),
   "(x div y) * y + (x mod y) = x")

val xn = fromString "260309023368"
val yn = fromString "76734110"
val _ =
  if #1 divmod_test (xn, yn, zero) then print "OK\n"
  else (print "FAILED\n"; Process.exit Process.failure)

val _ = testprop 100 addition_associative
val _ = testprop 100 mult_assoc
val _ = testprop 100 distrib
val _ = testprop 100 divmod_test
*)

end
