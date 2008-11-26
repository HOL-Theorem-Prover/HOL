signature smallfootParser =
sig
  include Abbrev

  val parse_smallfoot_file : string -> term;
  val print_file : string -> unit;


end
