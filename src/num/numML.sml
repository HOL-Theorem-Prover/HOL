structure numML :> numML = 
struct
  open Arbnum

  fun curry f x y = f (x,y);

  val zero = Arbnum.zero
  val one = Arbnum.one
  val two = Arbnum.two
  val op + = curry Arbnum.+
  val op - = curry Arbnum.-
  val op * = curry Arbnum.*
  val exp  = curry Arbnum.pow
  val op div = curry Arbnum.div
  val op mod = curry Arbnum.mod

  val op <   = curry Arbnum.<
  val op <=  = curry Arbnum.<=
  val op >   = curry Arbnum.>
  val op >=  = curry Arbnum.>=

  fun pre n = if n = zero then zero else Arbnum.less1 n;

  fun even n = Arbnum.mod2 n = Arbnum.zero;
  fun odd n  = not (even n);

  fun fact n = if n = zero then one else Arbnum.*(n,fact(Arbnum.less1 n));

  fun funpow f n x = if n = zero then x else funpow f (Arbnum.less1 n) (f x);

  fun While P g x = if P x then While P g (g x) else x;

  fun least P = While (not o P) Arbnum.plus1 zero;

  val toString = Arbnum.toString
  val fromString = Arbnum.fromString

  val _ = app ConstMapML.insert
              [(numSyntax.zero_tm,   ("numML","zero")),
               (numSyntax.plus_tm,   ("numML","+")),
               (numSyntax.minus_tm,  ("numML","-")),
               (numSyntax.pre_tm,    ("numML","pre")),
               (numSyntax.mult_tm,   ("numML","*")),
               (numSyntax.exp_tm,    ("numML","exp")),
               (numSyntax.div_tm,    ("numML","div")),
               (numSyntax.mod_tm,    ("numML","mod")),
               (numSyntax.less_tm,   ("numML","<")),
               (numSyntax.greater_tm,("numML",">")),
               (numSyntax.geq_tm,    ("numML",">=")),
               (numSyntax.leq_tm,    ("numML","<=")),
               (numSyntax.even_tm,   ("numML","even")),
               (numSyntax.odd_tm,    ("numML","odd")),
               (numSyntax.fact_tm,   ("numML","fact")),
               (numSyntax.funpow_tm, ("numML","funpow")),
               (numSyntax.while_tm,  ("numML","While")),
               (numSyntax.least_tm,  ("numML","least"))];
end
