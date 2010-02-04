signature holfootParser =
sig
  include Abbrev

  val parse_holfoot_file          : string -> term;
  val parse_holfoot_file_restrict : (string list) -> string -> term;
  val print_file_contents         : string -> unit;

end
