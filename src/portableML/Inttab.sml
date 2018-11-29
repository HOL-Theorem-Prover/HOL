structure Inttab = Table(
  type key = int
  val ord = Int.compare
  fun pp i = HOLPP.add_string (Int.toString i)
);
