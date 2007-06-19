structure numML :> numML =
struct
  nonfix MOD DIV DIVMOD findq LEAST WHILE MAX MIN FUNPOW FACT ODD EVEN
         EXP iSQR iSUB iDUB PRE iiSUC iZ SUC NUMERAL BIT2 BIT1 ZERO * /
         quot rem + - ^ @ <> > < >= <= := o before;

  type num = LargeInt.int;
  open combinML;

  val ZERO = (0:num)
  val ONE = (1:num)
  val TWO = (2:num)

  fun times2 x = LargeInt.+(x, x)
  fun plus1 x = LargeInt.+(x, ONE)
  fun plus2 x = LargeInt.+(x, TWO)
  fun less1 x = LargeInt.-(x, ONE)
  fun mod2 x = LargeInt.rem(x, TWO)

  fun BIT1 n = plus1(times2 n)

  fun BIT2 n = plus2(times2 n)

  fun DIV2 x = LargeInt.quot(x, TWO)

  val num_size = I

  fun NUMERAL x = x

  val SUC = plus1

  fun iZ x = x

  fun iiSUC n = SUC(SUC(n))

  fun + n m = LargeInt.+(n, m)

  fun < n m = LargeInt.<(n, m)

  fun <= n m = LargeInt.<=(n, m)

  fun > n m = LargeInt.>(n, m)

  fun >= m n = LargeInt.>=(n, m)

  fun PRE n = if n = ZERO then ZERO else less1 n

  val iDUB = times2

  fun iSUB b n m =
        if b then LargeInt.-(n, m) else plus1 (LargeInt.-(n, m))

  fun - n m = if < n m then ZERO else LargeInt.-(n, m)

  fun  *  n m = LargeInt.*(n, m)

  fun iSQR x =  *  x x

  fun pow (xn, yn) =
    if mod2 yn = ONE then
      LargeInt.*(xn, pow(xn, less1 yn))
    else
      if yn = ZERO then
        ONE
      else
        pow(LargeInt.*(xn, xn), DIV2 yn);

  fun EXP n m = pow(n, m)

  fun EVEN n = mod2 n = ZERO

  fun ODD n = not (EVEN n)

  fun FACT n =
       let fun fact n a = if n = ZERO then a
                          else fact (less1 n) (LargeInt.*(n, a))
       in fact n ONE end

  fun FUNPOW f n x =
       let fun iter (n,res) = if n = ZERO then res
                              else iter (less1 n, f res)
       in iter(n,x) end

  fun MOD_2EXP x n =
        if x = ZERO orelse n = ZERO then ZERO else
          let val v = times2 (MOD_2EXP (less1 x) (DIV2 n))
          in
            if EVEN n then v else plus1 v
          end

  fun DIV_2EXP x n = FUNPOW DIV2 x n

  fun MIN x y = (if < x y then x else y)

  fun MAX x y = (if < x y then y else x)

  fun WHILE P g x = if P x then WHILE P g (g x) else x

  fun LEAST P = WHILE (o not P) SUC ZERO

  fun findq (a,(m,n)) =
        if n = ZERO then a
          else let val d =  *  (BIT2 ZERO) n
               in
                  if < m d then a else findq ( *  (BIT2 ZERO) a,(m,d))
               end

  fun DIVMOD (a,(m,n)) =
        if n = ZERO then (ZERO,ZERO)
          else if < m n then (a,m)
                 else let val q = findq (BIT1 ZERO,(m,n))
                      in
                         DIVMOD (+ a q,(- m ( *  n q),n))
                      end

  fun DIV m n = LargeInt.quot(m, n)

  fun MOD m n = LargeInt.rem(m, n)

  fun measure f x y = < (f x) (f y)

 (*---------------------------------------------------------------------------*)
 (* Supplementary ML, not generated from HOL theorems, aimed at supporting    *)
 (* parsing and pretty printing of numerals.                                  *)
 (*---------------------------------------------------------------------------*)

  val toBinString = LargeInt.fmt StringCvt.BIN

  val toDecString = LargeInt.toString

  val toOctString = LargeInt.fmt StringCvt.OCT

  val toHexString = LargeInt.fmt StringCvt.HEX

  val fromDecString = o valOf LargeInt.fromString
  fun fromBinString s =
        valOf (StringCvt.scanString (LargeInt.scan StringCvt.BIN) s)
  fun fromOctString s =
        valOf (StringCvt.scanString (LargeInt.scan StringCvt.OCT) s)
  fun fromHexString s =
        valOf (StringCvt.scanString (LargeInt.scan StringCvt.HEX) s)

  (* Installed in MoscowML with Meta.installPP *)

  fun ppBin ppstrm n = PP.add_string ppstrm (toBinString n);
  fun ppOct ppstrm n = PP.add_string ppstrm (toOctString n);
  fun ppDec ppstrm n = PP.add_string ppstrm (toDecString n);
  fun ppHex ppstrm n = PP.add_string ppstrm (toHexString n);
  val toString = toDecString;
  val fromString = fromDecString;
  val pp_num = ppDec;

  val fromInt = LargeInt.fromInt
  fun toInt n  = Int.fromString (toDecString n);

end
