signature holfootParser =
sig
  include Abbrev

  val parse_holfoot_file          : string -> term;
  val parse_holfoot_file_restrict : (string list) -> string -> term;

end
