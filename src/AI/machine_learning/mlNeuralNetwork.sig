signature mlNeuralNetwork =
sig

  type vect = real vector
  type mat = vect vector

  (* hyperparameters *)
  val learningrate_glob : real ref
  val show_stats : bool ref

  (* activation *)
  val tanh : real -> real
  val dtanh : real -> real
  val relu : real -> real
  val drelu : real -> real
  val leakyrelu : real -> real
  val dleakyrelu : real -> real

  (* neural network *)
  type layer = {a : real -> real, da : real -> real, w : mat}
  type nn = layer list

  type fpdata = {layer : layer, inv : vect, outv : vect, outnv : vect}
  type bpdata = {doutnv : vect, doutv : vect, dinv : vect, dw : mat}

  (* weights randomly initialized *)
  val random_nn : (real -> real) * (real -> real) -> int list -> nn

  (* forward and backward pass *)
  val fp_nn        : nn -> vect -> fpdata list
  val bp_nn        : fpdata list -> vect -> bpdata list
  val bp_nn_wocost : fpdata list -> vect -> bpdata list

  (* weight updates *)
  val update_nn         : nn -> mat list -> nn
  val smult_dwl         : real -> mat list -> mat list
  val sum_dwll          : mat list list -> mat list
  val mean_square_error : vect -> real
  val average_loss      : bpdata list list -> real

  (* training *)
  val train_nn_batch : int -> nn -> (vect * vect) list -> (nn * real)

  (* input/output *)
  val reall_to_string : real list -> string
  val string_to_reall : string -> real list
  val string_of_wl : mat list -> string
  val string_of_nn : nn -> string
  val read_wl_sl : string list -> mat list
  val read_nn_sl : string list -> nn
  val write_nn : string -> nn -> unit
  val read_nn : string -> nn
  val write_exl : string -> (real list * real list) list -> unit
  val read_exl : string -> (real list * real list) list

  (* interface *)
  val scale_out : real list -> vect
  val scale_ex : real list * real list -> vect * vect
  val descale_out : vect -> real list
  val infer_nn : nn -> real list -> real list
  val train_nn : int -> int -> nn -> int -> (real list * real list) list -> nn

end
