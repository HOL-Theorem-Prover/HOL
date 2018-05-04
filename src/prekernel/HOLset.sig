signature HOLset =
sig
  include Redblackset
  val pp_holset : int -> ('a * int -> HOLPP.pretty) -> 'a set -> HOLPP.pretty
end
