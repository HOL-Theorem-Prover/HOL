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
  val kappa : string
  val lambda : string
  val mu : string
  val nu : string
  val xi : string
  val pi : string
  val rho : string
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
  val Pi : string
  val Phi : string
  val Psi : string
  val Omega : string

  (* superscripts *)
  val sup_0 : string
  val sup_1 : string
  val sup_2 : string
  val sup_3 : string
  val sup_4 : string
  val sup_5 : string
  val sup_6 : string
  val sup_7 : string
  val sup_8 : string
  val sup_9 : string
  val sup_lparen : string
  val sup_rparen : string
  val sup_eq : string
  val sup_plus : string
  val sup_minus : string
  val sup_h : string
  val sup_i : string
  val sup_j : string
  val sup_l : string
  val sup_n : string
  val sup_r : string
  val sup_s : string
  val sup_w : string
  val sup_x : string
  val sup_y : string
  val sup_gamma : string

  (* subscripts *)
  val sub_plus : string

  (* arrows *)
  val rightarrow : string
  val leftarrow : string
  val longleftarrow : string
  val longrightarrow : string
  val Rightarrow : string
  val Leftarrow : string
  val longdoublerightarrow : string
  val longdoubleleftarrow : string
  val mapsto         : string
  val mapsfrom       : string
  val longmapsto     : string
  val longmapsfrom   : string
  val hookleftarrow  : string
  val hookrightarrow : string

  (* brackets, braces and parentheses *)
  val double_bracel : string
  val double_bracer : string
  val langle : string
  val rangle : string
  val double_langle : string
  val double_rangle : string
  val lensel : string
  val lenser : string

  (*stars*)
  val blackstar      : string
  val whitestar      : string
  val bigasterisk    : string
  val asterisk       : string
  val circlestar     : string
  val stardiaeresis  : string

  (* quotation marks *)
  val ldquo : string
  val lsquo : string
  val rdquo : string
  val rsquo : string

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
  val minus : string
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
  val universal_set : string

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
