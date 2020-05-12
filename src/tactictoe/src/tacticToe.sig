signature tacticToe =
sig

  include Abbrev

  val set_timeout : real -> unit
  val ttt : tactic
  val tactictoe : term -> thm

  (* hide messages from search and reconstruction (on by default) *)
  val hide_flag : bool ref  

  (* contains recorded data from the ancestries of the current theory *)
  val clean_ttt_tacdata_cache : unit -> unit

  (* evaluation *)
  type lbl = (string * real * goal * goal list)
  type fea = int list
  type thmdata =
    (int, real) Redblackmap.dict *
    (string, int list) Redblackmap.dict
  type tacdata =
    {
    tacfea : (lbl,fea) Redblackmap.dict,
    tacfea_cthy : (lbl,fea) Redblackmap.dict,
    taccov : (string, int) Redblackmap.dict,
    tacdep : (goal, lbl list) Redblackmap.dict
    }
  val ttt_eval : thmdata * tacdata -> goal -> unit

end
