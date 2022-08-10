signature HOLset =
sig
  include Redblackset
  val pp_holset : FixedInt.int -> ('a * FixedInt.int -> HOLPP.pretty) ->
                  'a set -> HOLPP.pretty
end
