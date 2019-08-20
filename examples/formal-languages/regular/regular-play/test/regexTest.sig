signature regexTest =
sig

  val getTests : unit -> (int * bool * regexType.Reg * string) list

  val getPerformanceTests : string -> int -> (int * bool * regexType.Reg * string) list

  val getPerformanceTestsRegexSize : string -> int -> int -> (int * bool * regexType.Reg * string) list

end
