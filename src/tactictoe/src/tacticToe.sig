signature tacticToe =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn

  (* allows tactictoe to call holyhammer: disabled by default *)
  val hh_use : bool ref
  val hh_lemmas :
    (string -> mlThmData.thmdata -> goal -> string list option) option ref
  val hh_time : int ref
  val atp_dir : string ref
  val import_hh : unit ->
    (string -> mlThmData.thmdata -> goal -> string list option) option

  (* parametrizable functions *)
  val build_searchobj :
     mlThmData.thmdata * mlTacticData.tacdata ->
    tnn option * tnn option * tnn option ->
    goal -> tttSearch.searchobj
  val main_tactictoe :
    mlThmData.thmdata * mlTacticData.tacdata ->
    tnn option * tnn option * tnn option ->
    goal -> tttSearch.proofstatus * tttSearch.searchtree

  (* tactictoe parameters *)
  val clean_ttt_tacdata_cache : unit -> unit
  val set_timeout : real -> unit
  val prioritize_stacl : string list ref

  (* tnn-based function *)
  val confidence_tnn : tnn -> goal -> real

  (* main functions *)
  val ttt_tnn : tnn -> tactic
  val tactictoe_tnn : tnn -> term -> thm

  val ttt : tactic
  val tactictoe : term -> thm

  (* search tree produced by the main fucntions *)
  val searchtree_glob : tttSearch.searchtree option ref

  (* suggest a possible proof after a failed attempt from the search tree *)
  val suggest_depth : int option ref
  val suggest : unit -> tactic

end
