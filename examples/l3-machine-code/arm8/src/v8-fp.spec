-----------------------------------------------------------------------
-- Scalar binary64 floating point for ARMv8-A. FPCR controls other than
-- RMode are unsupported and V[127:64] is not modelled.
-- See COPYRIGHT for the original model licence.
-----------------------------------------------------------------------

unit CheckFP =
   when (FPCR && ~0x00C00000) != 0 do
      #UNDEFINED_FAULT ("Unsupported FPCR controls")

ieee_rounding FPRoundingMode =
   match FPCR<23:22>
   {
      case '00' => roundTiesToEven
      case '01' => roundTowardPositive
      case '10' => roundTowardNegative
      case '11' => roundTowardZero
   }

component D (n::reg) :: dword
{
   value = FP_REG (n)
   assign value = FP_REG (n) <- value
}

unit FPSetFlags (flags::ieee_flags) =
   FPSR <- FPSR || (0`27 : [flags.Precision]`1 : [flags.Underflow]`1 :
                     [flags.Overflow]`1 : [flags.DivideByZero]`1 : [flags.InvalidOp]`1)

bits(4) FPCompare64 (a::dword, b::dword) =
   if FP64_IsNan (a) or FP64_IsNan (b) then '0011'
   else if FP64_Equal (a, b) then '0110'
   else if FP64_LessThan (a, b) then '1000'
   else '0010'

-- NaN results as in the ASL: the first signalling NaN operand (quietened),
-- else the first quiet NaN operand, else the default NaN.
dword FPNaNResult (result::dword, a::dword, b::dword, c::dword) =
   if not FP64_IsNan (result) then result
   else if FP64_IsSignallingNan (a) then a || 0x0008000000000000
   else if FP64_IsSignallingNan (b) then b || 0x0008000000000000
   else if FP64_IsSignallingNan (c) then c || 0x0008000000000000
   else if FP64_IsNan (a) then a
   else if FP64_IsNan (b) then b
   else if FP64_IsNan (c) then c
   else 0x7FF8000000000000

define FloatingPoint > FMov (n::reg, d::reg) =
{ CheckFP; D(d) <- D(n) }

define FloatingPoint > FAbs (n::reg, d::reg) =
{ CheckFP; D(d) <- FP64_Abs (D(n)) }

define FloatingPoint > FNeg (n::reg, d::reg) =
{ CheckFP; D(d) <- FP64_Neg (D(n)) }

define FloatingPoint > FSqrt (n::reg, d::reg) =
{
   CheckFP;
   operand = D(n);
   flags, result = FP64_Sqrt_ (FPRoundingMode, operand);
   status = if FP64_IsNan (operand) then
               0`31 : [FP64_IsSignallingNan (operand)]`1
            else
               0`27 : [flags.Precision]`1 : [flags.Underflow]`1 :
                 [flags.Overflow]`1 : [flags.DivideByZero]`1 : [flags.InvalidOp]`1;
   FPSR <- FPSR || status;
   D(d) <- FPNaNResult (result, operand, operand, operand)
}

define FloatingPoint > FAdd (m::reg, n::reg, d::reg) =
{
   CheckFP;
   a = D(n); b = D(m);
   flags, result = FP64_Add_ (FPRoundingMode, a, b);
   FPSetFlags (flags);
   D(d) <- FPNaNResult (result, a, b, b)
}

define FloatingPoint > FSub (m::reg, n::reg, d::reg) =
{
   CheckFP;
   a = D(n); b = D(m);
   flags, result = FP64_Sub_ (FPRoundingMode, a, b);
   FPSetFlags (flags);
   D(d) <- FPNaNResult (result, a, b, b)
}

define FloatingPoint > FMul (m::reg, n::reg, d::reg) =
{
   CheckFP;
   a = D(n); b = D(m);
   flags, result = FP64_Mul_ (FPRoundingMode, a, b);
   FPSetFlags (flags);
   D(d) <- FPNaNResult (result, a, b, b)
}

define FloatingPoint > FDiv (m::reg, n::reg, d::reg) =
{
   CheckFP;
   a = D(n); b = D(m);
   flags, result = FP64_Div_ (FPRoundingMode, a, b);
   FPSetFlags (flags);
   D(d) <- FPNaNResult (result, a, b, b)
}

define FloatingPoint > FMAdd (m::reg, a::reg, n::reg, d::reg) =
{
   CheckFP;
   x = D(n); y = D(m); addend = D(a);
   flags, result = FP64_MulAdd_ (FPRoundingMode, x, y, addend);
   FPSetFlags (flags);
   -- the ASL rejects a quiet NaN added to infinity times zero
   invalid = FP64_IsNan (addend) and not FP64_IsSignallingNan (addend) and
             (FP64_Abs (x) == FP64_PosInf and FP64_IsZero (y) or
              FP64_IsZero (x) and FP64_Abs (y) == FP64_PosInf);
   FPSR<0> <- FPSR<0> or invalid;
   D(d) <- if invalid then 0x7FF8000000000000
           else FPNaNResult (result, addend, x, y)
}

define FloatingPoint > FCompare (n::reg, m::reg) =
{
   CheckFP;
   a = D(n); b = D(m);
   nzcv = FPCompare64 (a, b);
   FPSR<0> <- FPSR<0> or FP64_IsSignallingNan (a) or FP64_IsSignallingNan (b);
   SetTheFlags (true, nzcv<3>, nzcv<2>, nzcv<1>, nzcv<0>)
}

define FloatingPoint > FMovToGeneral
   (sf::bits(N), n::reg, d::reg) with N in 32, 64 =
{ CheckFP; X(d) <- [D(n)]::bits(N) }

define FloatingPoint > FMovFromGeneral
   (sf::bits(N), n::reg, d::reg) with N in 32, 64 =
{ CheckFP; D(d) <- [X(n)::bits(N)] }

-- FCVTNS Wd, Dn: ties-to-even and saturating; a NaN gives zero.
define FloatingPoint > FToInt32 (n::reg, d::reg) =
{
   CheckFP;
   operand = D(n);
   result = match FP64_ToInt (roundTiesToEven, operand)
   {
      case Some (i) =>
         if i < -2147483648 then (true, false, 0x80000000`32)
         else if i > 2147483647 then (true, false, 0x7FFFFFFF`32)
         else (false, not FP64_Equal (FP64_FromInt (roundTiesToEven, i), operand), [i]::word)
      case None =>
         (true, false, if FP64_IsNan (operand) then 0`32
                       else if operand<63> then 0x80000000`32 else 0x7FFFFFFF`32)
   };
   invalid, inexact, value = result;
   FPSR<0> <- FPSR<0> or invalid;
   FPSR<4> <- FPSR<4> or inexact;
   X(d) <- value
}

-- SCVTF Dd, Wn: exact, and zero gives +0 in every rounding mode.
define FloatingPoint > FFromInt32 (n::reg, d::reg) =
{
   CheckFP;
   operand = [X(n)::word]::int;
   D(d) <- if operand == 0 then 0`64 else FP64_FromInt (FPRoundingMode, operand)
}
