signature AttributeSyntax =
sig

  val mk_strsafe : string -> string
  val bslash_escape : char -> string
  val bslash_escape_s : string -> string
  val dest_ml_thm_binding : string -> {keyword: string, name : string,
                                       name_attr_original : string,
                                       attributes : string list}
  val dest_name_attrs : string -> string * string list
  val key_vallist : string list -> (string * string list) list
  val mk_tacmodifier_string : (string * string list) list -> string

  type ('a,'b) gtm =
       {values : string list -> 'b, combine : 'a * 'a -> 'a, null: 'a,
        perkey : string -> 'b -> 'a}
  val gen_mktm : ('a,'b) gtm -> (string * string list) list -> 'a

end
