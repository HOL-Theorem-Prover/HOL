structure Int_Graph = Graph(
  type key = int
  val ord = Int.compare
  val pp = HOLPP.add_string o Int.toString
);
