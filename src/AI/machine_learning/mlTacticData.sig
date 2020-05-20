signature mlTacticData =
sig

  include Abbrev

  (* term data (can be useful for other purposes) *)
  val export_terml : string -> term list -> unit
  val import_terml : string -> term list
  val export_goal : string -> goal -> unit
  val import_goal : string -> goal

  (* tactic data *)
  type lbl = (string * real * goal * goal list)
  type fea = int list
  type tacdata =
    {
    tacfea : (lbl,fea) Redblackmap.dict,
    tacfea_cthy : (lbl,fea) Redblackmap.dict,
    taccov : (string, int) Redblackmap.dict,
    tacdep : (goal, lbl list) Redblackmap.dict
    }
  val empty_tacdata : tacdata

  val export_tacfea : string -> (lbl,fea) Redblackmap.dict -> unit
  val import_tacfea : string -> (lbl,fea) Redblackmap.dict
  val import_tacdata : string list -> tacdata

  (* tactictoe database *)
  val ttt_tacdata_dir : string
  val exists_tacdata_thy : string -> bool
  val ttt_create_tacdata : unit -> tacdata
  val ttt_update_tacdata : (lbl * tacdata) -> tacdata
  val ttt_export_tacdata : string -> tacdata -> unit

  type ex = (goal * string * (goal * goal list) * goal list) * bool
  val exl_glob : ex list ref
  val ttt_export_exl_human : string -> ex list -> unit
  val ttt_export_exl : string -> ex list -> unit
  val ttt_import_exl : string -> ex list
  val ttt_export_tptpexl : string -> ex list -> unit

  val prepare_exl : ex list -> (term * real list) list list
  val nntm_of_goal : goal -> term  

end
