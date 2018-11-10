signature tttLearn =
sig

  include Abbrev

  type lbl = (string * real * goal * goal list)
  type fea = int list
  type tacdata =
    {
    tacfea : (lbl,fea) Redblackmap.dict,
    tacfea_cthy : (lbl,fea) Redblackmap.dict,
    taccov : (string, int) Redblackmap.dict,
    tacdep : (goal, lbl list) Redblackmap.dict
    }  

  (* abstraction of theorem list arguments in tactics *)
  val thmlarg_placeholder : string
  val abstract_stac : string -> string option
  val inst_stac : string list -> string -> string
  val is_thmlarg_stac : string -> bool 
 
  (* competition between different tactics over a goal *)
  val orthogonalize : tacdata -> (lbl * fea) -> lbl 

  (* abstraction info for the nn branch *)
  val pe_abs : string -> (string * (string * thm) list list) 

end
