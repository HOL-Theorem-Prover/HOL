signature ordinalML = 
sig
  type num = numML.num
  datatype osyntax = End of num | Plus of osyntax * num * osyntax
  val expt : osyntax -> osyntax
  val coeff : osyntax -> num
  val finp : osyntax -> bool
  val tail : osyntax -> osyntax
  val rank : osyntax -> num
  val oless : osyntax -> osyntax -> bool
  val is_ord : osyntax -> bool
  val ord_less : osyntax -> osyntax -> bool
  val ord_add : osyntax -> osyntax -> osyntax
  val ord_sub : osyntax -> osyntax -> osyntax
  val ord_mult : osyntax -> osyntax -> osyntax
end
