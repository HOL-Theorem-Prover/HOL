structure Numtab = Table(
  type key = Arbnum.num
  val ord = Arbnum.compare
  val pp = HOLPP.add_string o Arbnum.toString
);
