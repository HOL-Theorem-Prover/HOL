signature rlAim =
sig

  include Abbrev

  val tread_file : string -> (term * int) list
  val transform_ex : term * int -> term * real

end
