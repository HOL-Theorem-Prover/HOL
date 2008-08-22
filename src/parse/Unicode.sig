signature Unicode =
sig

  type term = Term.term
  (* functions for manipulating use of Unicode versions of constants *)
  val unicode_version : (string * term) -> unit
  val temp_unicode_version : (string * term) -> unit
  (*
  val disable_one_unicode : string -> unit
  val disable_one_unicode_t : term -> unit
  val enable_one_unicode : string -> unit
  val enable_one_unicode_t : term -> unit
  *)

  structure UChar : sig
  (* Greek letters *)
  val alpha : string
  val beta : string
  val gamma : string
  val delta : string
  val zeta : string
  val eta : string
  val theta : string
  val lambda : string
  val mu : string
  val nu : string
  val xi : string
  val sigma : string
  val tau : string
  val phi : string
  val psi : string
  val omega : string

  val Gamma : string
  val Delta : string
  val Theta : string
  val Lambda : string
  val Xi : string
  val Sigma : string
  val Phi : string
  val Psi : string
  val Omega : string

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
  val subset : string

  (* wordsTheory *)
  val lo : string
  val ls : string
  val hi : string
  val hs : string
  val or : string
  val xor : string
  val lsl : string
  val lsr : string
  val asr : string
  val rol : string
  val ror : string
  end (* sig *)

end

