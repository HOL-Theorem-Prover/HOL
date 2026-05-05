structure Chartab = Table(
  type key = char
  val ord = Char.compare
  val pp = HOLPP.add_string o Char.toString
);
