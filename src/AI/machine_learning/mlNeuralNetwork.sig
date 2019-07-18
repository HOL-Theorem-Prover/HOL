signature mlNeuralNetwork =
sig

  (* hyperparameters *)
  val learningrate_glob : real ref

  (* activation *)
  val tanh : real -> real
  val dtanh : real -> real
  val relu : real -> real
  val drelu : real -> real
  val leakyrelu : real -> real
  val dleakyrelu : real -> real

  (* NN *)
  type vect = real vector
  type mat = real vector vector

  type layer = {a : real -> real, da : real -> real, w : real vector vector}

  type nn = layer list

  type fpdata =
    {layer : layer,
     inv   : real vector,
     outv  : real vector,
     outnv : real vector}

  type bpdata =
    {doutnv : real vector,
     doutv  : real vector,
     dinv   : real vector,
     dw     : real vector vector}

  (* initialization of the nn *)
  val random_nn :
    (real -> real) * (real -> real) ->
    (real -> real) * (real -> real) ->
    int list -> nn

  (* forward and backward pass *)
  val fp_nn        : nn -> real vector -> fpdata list
  val bp_nn        : fpdata list -> real vector -> bpdata list
  val bp_nn_wocost : fpdata list -> real vector -> bpdata list

  (* weight updates *)
  val update_nn         : nn -> mat list -> nn
  val smult_dwl         : real -> mat list -> mat list
  val sum_dwll          : mat list list -> mat list
  val mean_square_error : real vector -> real
  val average_loss      : bpdata list list -> real
  val random_wu         : nn -> mat list
  val random_update_nn  : nn -> nn

  (* training *)
  val ext_flag : bool ref
  val extspec : (nn, (vect * vect) list, mat list * real) smlParallel.extspec

  val train_nn :
    int -> int -> nn -> int -> (vect * vect) list -> nn

  (* I/O *)
  val reall_to_string : real list -> string
  val string_to_reall : string -> real list
  val string_of_wl : mat list -> string
  val string_of_nn : nn -> string
  val read_wl_sl : string list -> mat list
  val read_nn_sl : string list -> nn


end
