signature Timeout =
sig
  exception TIMEOUT of Time.time
  val apply: Time.time -> ('a -> 'b) -> 'a -> 'b
end
