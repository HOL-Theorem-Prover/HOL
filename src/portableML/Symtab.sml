structure Symtab = Table(
  type key = string
  val ord = String.compare
  val pp = HOLPP.add_string o Portable.mlquote
);
