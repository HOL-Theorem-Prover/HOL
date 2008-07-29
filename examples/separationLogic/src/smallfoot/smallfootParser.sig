signature smallfootParser =
sig
  include Abbrev

  val parse_smallfoot_file : string -> term;


end
