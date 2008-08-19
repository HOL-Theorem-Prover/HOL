signature UTF8_Printing =
sig

  (* boolTheory connectives *)
  val forall : string
  val exists : string
  val conj : string
  val disj : string
  val imp : string
  val neg : string
  val neq : string
  val setelementof : string
  val longdoublerightarrow : string
  val turnstile : string
            
  (* arithmeticTheory *)
  val leq : string
  val geq : string
  val nats : string

  (* pred_setTheory *)
  val emptyset : string
  val union : string
  val inter : string

  val bool_printing : unit -> unit
  val arith_printing : unit -> unit
  val set_printing : unit -> unit
  val all_printing : unit -> unit

end

