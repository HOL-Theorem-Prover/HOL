signature tttToken =
sig

  include Abbrev

  type thmdata = mlThmData.thmdata
  type call = mlTacticData.call
  type tacdata = mlTacticData.tacdata
  type symweight = mlFeature.symweight
  
  datatype pretac = 
      NoargTac of tactic  
    | ThmlTac of thm list -> tactic
    | TermTac of term quotation -> tactic
  datatype aty = Aterm | Athml
  datatype token = Stac of string | Sterm of string | Sthml of string list
  val dest_stac : token -> string
  val dest_sterm : token -> string
  val dest_sthml : token -> string list  

  val termarg_placeholder : string
  val thmlarg_placeholder : string
  val extract_atyl : string -> aty list

  val is_thmlstac : string -> bool
  val abstract_thml : string -> (string * string list list) option
  val sthml_of_thmidl : string list -> string
  val inst_thml : string list -> string -> string

  val is_termstac : string -> bool
  val abstract_term : string -> (string * string) option
  val inst_term : string -> string -> string
  
  type parsetoken = 
    {parse_stac : string -> pretac ,
     parse_thmidl : string list -> thm list, 
     parse_sterm : string -> term quotation}
  val string_of_token : token -> string
  val compare_token : token * token -> order

  val tactictoe_thmlarg : thm list 
  val tactictoe_termarg : term quotation
  
  val sml_pretacl_glob : pretac list ref
  val pretacl_of_sml : real -> string list -> pretac list option  

  val build_tac : parsetoken -> token list -> tactic
  val build_stac : token list -> string

end

