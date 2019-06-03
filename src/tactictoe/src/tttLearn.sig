signature tttLearn =
sig

  include Abbrev

  type lbl = (string * real * goal * goal list)
  type fea = int list

  type thmdata = (int, real) Redblackmap.dict *
    (string, int list) Redblackmap.dict

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
  val ortho_predstac_time : real ref
  val ortho_predthm_time : real ref
  val ortho_teststac_time : real ref
  val orthogonalize : (thmdata * tacdata) -> lbl -> lbl

end
