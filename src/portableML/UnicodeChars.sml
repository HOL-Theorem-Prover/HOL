structure UnicodeChars :> UnicodeChars =
struct

val U = UTF8.chr

(* Greek letters *)
val alpha = "\u00ce\u00b1"
val beta = "\u00ce\u00b2"
val gamma = "\u00ce\u00b3"
val delta = "\u00ce\u00b4"
val zeta = "\u00ce\u00b6"
val eta = "\u00ce\u00b7"
val theta = "\u00ce\u00b8"
val lambda = "\u00ce\u00bb"
val mu = "\u00ce\u00bc"
val nu = "\u00ce\u00bd"
val xi = "\u00ce\u00be"
val sigma = "\u00cf\u0083"
val tau = "\u00cf\u0084"
val phi = "\u00cf\u0086"
val psi = "\u00cf\u0088"
val omega = "\u00cf\u0089"

val Gamma = "\u00ce\u0093"
val Delta = "\u00ce\u0094"
val Theta = "\u00ce\u0098"
val Lambda = "\u00ce\u009b"
val Xi = "\u00ce\u009e"
val Sigma = "\u00ce\u00a3"
val Phi = "\u00ce\u00a6"
val Psi = "\u00ce\u00a8"
val Omega = "\u00ce\u00a9"

(* Boolean gadgets *)
val forall = "\u00e2\u0088\u0080";
val exists = "\u00e2\u0088\u0083";
val conj = "\u00e2\u0088\u00a7";
val disj = "\u00e2\u0088\u00a8";
val imp = "\u00e2\u0087\u0092";
val neg = "\u00c2\u00ac"
val iff = U 0x21D4
val not_iff = U 0x21CE

(* not a constant, but might be useful *)
val neq = "\u00e2\u0089\u00a0"
val turnstile = "\u00e2\u008a\u00a2";

(* arrows *)
val leftarrow            = U 0x2190
val rightarrow           = U 0x2192
val longleftarrow        = U 0x27F5
val longrightarrow       = U 0x27F6

val Leftarrow            = U 0x21D0
val Rightarrow           = U 0x21D2
val longdoubleleftarrow  = U 0x27F8
val longdoublerightarrow = U 0x27F9

(* latter probably needs a proportional font to print well - would be
   good for implication if available - actually seems OK also on
   Leopard's Courier font, which is supposedly fixed-width *)

val mapsto               = U 0x21A6
val mapsfrom             = U 0x21A4
val longmapsto           = U 0x27FC
val longmapsfrom         = U 0x27FB
val hookleftarrow        = U 0x21A9
val hookrightarrow       = U 0x21AA

(*stars*)
val blackstar            = U 0x2605
val whitestar            = U 0x2606
val bigasterisk          = U 0x229B
val asterisk             = U 0x2217
val circlestar           = U 0x235F
val stardiaeresis        = U 0x2363

(* superscripts *)
val sup_0 = UTF8.chr 0x2070
val sup_1 = UTF8.chr 0xB9
val sup_2 = UTF8.chr 0xB2
val sup_3 = UTF8.chr 0xB3
val sup_4 = UTF8.chr 0x2074
val sup_5 = UTF8.chr 0x2075
val sup_6 = UTF8.chr 0x2076
val sup_7 = UTF8.chr 0x2077
val sup_8 = UTF8.chr 0x2078
val sup_9 = UTF8.chr 0x2079
val sup_plus = UTF8.chr 0x207A
val sup_minus = UTF8.chr 0x207B
val sup_eq = UTF8.chr 0x207C
val sup_lparen = UTF8.chr 0x207D
val sup_rparen = UTF8.chr 0x207E
val sup_h = UTF8.chr 0x2B0
val sup_i = UTF8.chr 0x2071
val sup_j = UTF8.chr 0x2B2
val sup_l = UTF8.chr 0x2E1
val sup_n = UTF8.chr 0x207F
val sup_r = UTF8.chr 0x2B3
val sup_s = UTF8.chr 0x2E2
val sup_w = UTF8.chr 0x2B7
val sup_x = UTF8.chr 0x2E3
val sup_y = UTF8.chr 0x2B8
val sup_gamma = UTF8.chr 0x2E0

(* arithmetic *)
val leq = "\u00e2\u0089\u00a4"
val geq = "\u00e2\u0089\u00a5"
val nats = U 0x2115
val ints = U 0x2124
val reals = U 0x211D
val rats = U 0x211A

(* sets *)
val emptyset = "\u00e2\u0088\u0085"
val subset = "\u00e2\u008a\u0086"
val inter = "\u00e2\u0088\u00a9"
val union = "\u00e2\u0088\u00aa"
val setelementof = "\u00e2\u0088\u0088"
val not_elementof = U 0x2209
val universal_set = U 0x1D54C

(* words *)
val lo = "<\u00e2\u0082\u008a"
val hi = ">\u00e2\u0082\u008a"
val ls = leq ^ "\u00e2\u0082\u008a"
val hs = geq ^ "\u00e2\u0082\u008a"
val or = "\u00e2\u0080\u0096"
val xor = "\u00e2\u008a\u0095"
val lsl = "\u00e2\u0089\u00aa"
val asr = "\u00e2\u0089\u00ab"
val lsr = "\u00e2\u008b\u0099"
val rol = "\u00e2\u0087\u0086"
val ror = "\u00e2\u0087\u0084"

fun isAlpha s = let
  val ((_, i), _) = valOf (UTF8.getChar s)
in
  if i < 128 then Char.isAlpha (String.sub(s,0))
  else
    0x370 <= i andalso i <= 0x3ff andalso i <> 0x37E (* Greek *) orelse
    i = 0xAA (* ordinal a *) orelse
    i = 0xB5 (* Latin-1 mu *) orelse
    i = 0xBA (* ordinal o *) orelse
    0xC0 <= i andalso i <= 0xFF andalso i <> 0xD7 andalso i <> 0xF7
    (* Latin-1 *)
end

fun isDigit s = let
  val ((_, i), _) = valOf (UTF8.getChar s)
in
  if i < 128 then Char.isDigit (String.sub(s,0))
  else
    0x2080 <= i andalso i <= 0x2089 (* subscripts *)

end

fun isAlphaNum s = isAlpha s orelse isDigit s

fun isMLIdent s = isAlphaNum s orelse s = "'" orelse s = "_"

fun isSymbolic s = let
  val ((_, i), _) = valOf (UTF8.getChar s)
in
  if i < 128 then Char.isPunct (String.sub(s,0))
  else not (isAlphaNum s)
end

end (* struct *)

