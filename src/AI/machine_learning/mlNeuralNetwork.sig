signature mlNeuralNetwork =
sig

  include Abbrev

  type vect = real vector
  type mat = vect vector

  (* activation *)
  val idactiv : real -> real
  val didactiv : real -> real
  val tanh : real -> real
  val dtanh : real -> real

  (* neural network *)
  type layer = {a : real -> real, da : real -> real, w : mat}
  type nn = layer list
  type trainparam =
    {ncore: int, verbose: bool,
     learning_rate: real, batch_size: int, nepoch: int}
  val string_of_trainparam : trainparam -> string
  val trainparam_of_string : string -> trainparam
  type schedule = trainparam list
  val write_schedule : string -> schedule -> unit
  val read_schedule : string -> schedule

  type fpdata = {layer : layer, inv : vect, outv : vect, outnv : vect}
  type bpdata = {doutnv : vect, doutv : vect, dinv : vect, dw : mat}

  (* dimension *)
  val dimin_nn : nn -> int
  val dimout_nn : nn -> int

  (* weights randomly initialized *)
  val random_nn : (real -> real) * (real -> real) -> int list -> nn

  (* forward and backward pass *)
  val fp_nn : nn -> vect -> fpdata list
  val bp_nn : fpdata list -> vect -> bpdata list
  val bp_nn_doutnv : fpdata list -> vect -> bpdata list

  (* weight updates *)
  val update_nn : trainparam -> nn -> mat list -> nn
  val smult_dwl : real -> mat list -> mat list
  val sum_dwll : mat list list -> mat list
  val mean_square_error : vect -> real
  val average_loss : bpdata list list -> real

  (* input/output *)
  val enc_nn : nn -> HOLsexp_dtype.t
  val dec_nn : HOLsexp_dtype.t -> nn option
  val write_nn : string -> nn -> unit
  val read_nn : string -> nn
  val reall_to_string : real list -> string
  val string_to_reall : string -> real list
  val write_exl : string -> (real list * real list) list -> unit
  val read_exl : string -> (real list * real list) list

  (* interface *)
  val scale_real : real -> real
  val scale_out : real list -> vect
  val scale_ex : real list * real list -> vect * vect
  val descale_real : real -> real
  val descale_out : vect -> real list
  val infer_nn : nn -> real list -> real list
  val train_nn : trainparam -> nn -> (real list * real list) list -> nn


end
