signature mlTacticData =
sig

  include Abbrev

  (* term data (can be useful for other purpose) *)
  val export_terml : string -> term list -> unit
  val import_terml : string -> term list
  val export_goal : string -> goal -> unit
  val import_goal : string -> goal

  (* tactic data *)
  type stac = string
  type call = 
    {
    stac : stac, ortho : stac, 
    time : real,
    ig : goal, ogl : goal list,
    loc : string * int, fea : mlFeature.fea
    }
  val call_compare : call * call -> order

  type tacdata =
    {
    calls : call list,
    calls_cthy : call list,
    taccov : (stac, int) Redblackmap.dict,
    calldep : (goal, call list) Redblackmap.dict
    }
  val empty_tacdata : tacdata
  val export_calls : string -> call list -> unit
  val import_calls : string -> call list
  val import_tacdata : string list -> tacdata
  val export_tacdata : string -> tacdata -> unit
 
  (* tactictoe database *)
  val ttt_tacdata_dir : string
  val exists_tacdata_thy : string -> bool
  val ttt_import_tacdata : unit -> tacdata
  val ttt_update_tacdata : (call * tacdata) -> tacdata
  val ttt_export_tacdata : string -> tacdata -> unit

end
