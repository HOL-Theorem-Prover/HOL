signature holfootParser =
sig
  include Abbrev

  val parse_holfoot_file          : string -> term;
  val parse_holfoot_file_restrict : (string list) -> string -> term;
  val print_file_contents         : string -> unit;

  val add_genpred                 : (string * Parsetree.a_genpredargType list * (Absyn.absyn list -> Absyn.absyn)) -> unit
  val remove_genpred              : unit -> (string * Parsetree.a_genpredargType list * (Absyn.absyn list -> Absyn.absyn) * int)
  val reset_genpreds              : unit -> unit

  val list_data_tag  : string ref;
  val data_list_tag  : string ref;
  val array_data_tag : string ref;
  val list_link_tag  : string ref;
  val tree_data_tag  : string ref;
  val tree_link_tags : (string * string) ref;

end
