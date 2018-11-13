signature tttSetup =
sig

  include Abbrev

  (* directories *)
  val infix_file : string
  val tactictoe_dir : string
  val ttt_debugdir : string

  (* nearest neighbor *)
  val ttt_thmlarg_radius : int ref
  val ttt_ortho_radius   : int ref
  val ttt_presel_radius  : int ref

  (* recording *)
  val ttt_recprove_flag : bool ref
  val ttt_reclet_flag   : bool ref
  val ttt_rectac_time   : real ref
  val ttt_recproof_time : real ref

  (* search *)
  val ttt_search_time : real ref
  val ttt_tactic_time : real ref
  val init_metis : unit -> unit
  val ttt_metis_time : real ref
  val ttt_metis_radius : int ref
  val ttt_policy_coeff : real ref

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
  (* global carrying the evaluation function (instantiated in tttUnfold) *)
  val ttt_evalfun_glob : (thmdata * tacdata -> goal -> unit) option ref
  val ttt_hheval_flag : bool ref
  val ttt_ttteval_flag : bool ref

end
