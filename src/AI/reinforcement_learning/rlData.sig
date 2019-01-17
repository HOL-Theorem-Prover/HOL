signature rlData =
sig

  include Abbrev

  (* reinforcement learning data *)
  (* val data_mg2 : unit -> term list *)
  val data_copy : unit -> term list

  (* syntactic problem *)
  val data_nboccurSUC : unit -> (term * real) list * (term * real) list
  val read_nboccur : real -> real

  (* semantic problems *)
  val data_truth : unit -> (term * real) list * (term * real) list
  val data_truth_forallvar : unit -> (term * real) list * (term * real) list
  val data_truth_existsvar : unit -> (term * real) list * (term * real) list


end
