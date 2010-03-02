signature TermCoding =
sig

  val encode : Term.term -> string
  val decode : string -> Term.term option
  val reader : Term.term Coding.reader

end
