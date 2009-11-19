signature HOLset =
sig
  include Redblackset
  val pp_holset : HOLPP.ppstream -> 'a set -> unit
end
