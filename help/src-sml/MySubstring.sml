structure OldSubstringSTRUCT = Substring
signature NewSubstringSIG = sig
  include Substring
  val full : string -> substring
end
structure Substring :> NewSubstringSIG =
struct
  open OldSubstringSTRUCT
  val full = all
end
