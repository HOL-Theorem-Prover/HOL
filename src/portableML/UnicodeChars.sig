signature UnicodeChars =
sig

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

  (* superscripts *)
  val sup_plus : string
  val sup_minus : string
  val sup_1 : string

  (* arrows *)
  val rightarrow : string
  val leftarrow : string
  val longleftarrow : string
  val longrightarrow : string
  val Rightarrow : string
  val Leftarrow : string
  val longdoublerightarrow : string
  val longdoubleleftarrow : string

  (* boolTheory connectives *)
  val forall : string
  val exists : string
  val conj : string
  val disj : string
  val imp : string
  val neg : string
  val neq : string
  val turnstile : string
  val iff : string
  val not_iff : string

  (* arithmeticTheory *)
  val leq : string
  val geq : string
  val nats : string
  val ints : string
  val rats : string
  val reals : string

  (* pred_setTheory *)
  val emptyset : string
  val union : string
  val inter : string
  val subset : string
  val setelementof : string
  val not_elementof : string

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

  val isAlpha : string -> bool
  val isDigit : string -> bool
  val isAlphaNum : string -> bool
  val isSymbolic : string -> bool
  val isMLIdent : string -> bool


end

