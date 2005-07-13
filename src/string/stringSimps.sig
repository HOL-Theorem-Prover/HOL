signature stringSimps =
sig
  include Abbrev

  val char_rewrites   : thm list
  val string_rewrites : thm list
  val STRING_ss : simpLib.ssfrag
end
