signature mlTacticData =
sig

  include Abbrev

  (* datatype *)
  type stac = string
  type loc = string * int * int
  type call = {stac : stac, ogl : int list, fea : mlFeature.fea}
  val loc_compare : loc * loc -> order
  val call_compare : call * call -> order
  type tacdata =
    {
    calld : (loc,call) Redblackmap.dict,
    taccov : (stac,int) Redblackmap.dict,
    symfreq : (int,int) Redblackmap.dict
    }
  val empty_tacdata : tacdata

  (* I/O *)
  val export_calls : string -> (loc * call) list -> unit
  val import_calls : string -> (loc * call) list
  val import_tacdata : string list -> tacdata
  val export_tacdata : string -> string -> tacdata -> unit

  (* tactictoe database; the on-disk identity and manifest live in
     tttManifest *)
  val ttt_tacdata_file_override : string option ref
  val exists_tacdata_thy : string -> bool
  val create_tacdata : unit -> tacdata
  val ttt_update_tacdata : ((loc * call) * tacdata) -> tacdata
  val ttt_export_tacdata : string -> tacdata -> unit

end
