signature mlTacticData =
sig

  include Abbrev

  (* tactic data *)
  type stac = string
  type call =
    {stac : stac, ogl : int list, 
     loc : string * int * int, fea : mlFeature.fea}
  val call_compare : call * call -> order
  type tacdata =
    {
    calls : call list,
    taccov : (stac, int) Redblackmap.dict,
    symfreq : (int, int) Redblackmap.dict
    }
  
  (* tactic calls I/O *)
  val empty_tacdata : tacdata
  val export_calls : string -> call list -> unit
  val import_calls : string -> call list
  val import_tacdata : string list -> tacdata
  val export_tacdata : string -> string -> tacdata -> unit

  (* tactictoe database *)
  val ttt_tacdata_dir : string
  val exists_tacdata_thy : string -> bool
  val create_tacdata : unit -> tacdata
  val ttt_update_tacdata : (call * tacdata) -> tacdata
  val ttt_export_tacdata : string -> tacdata -> unit

end
