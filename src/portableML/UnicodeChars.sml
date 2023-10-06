structure UnicodeChars :> UnicodeChars =
struct

val U = UTF8.chr

(* Greek letters *)
val alpha =  U 0x03B1
val beta =   U 0x03B2
val gamma =  U 0x03B3
val delta =  U 0x03B4
val zeta =   U 0x03B6
val eta =    U 0x03B7
val theta =  U 0x03B8
val kappa =  U 0x03BA
val lambda = U 0x03BB
val mu =     U 0x03BC
val nu =     U 0x03BD
val xi =     U 0x03BE
val pi =     U 0x03C0
val rho =    U 0x03C1
val sigma =  U 0x03C3
val tau =    U 0x03C4
val phi =    U 0x03C6
val chi =    U 0x03C7
val psi =    U 0x03C8
val omega =  U 0x03C9

val Gamma =  U 0x0393
val Delta =  U 0x0394
val Theta =  U 0x0398
val Lambda = U 0x039B
val Xi =     U 0x039E
val Pi =     U 0x03A0
val Sigma =  U 0x03A3
val Phi =    U 0x03A6
val Psi =    U 0x03A8
val Omega =  U 0x03A9

(* Boolean gadgets *)
val forall =  U 0x2200
val exists =  U 0x2203
val conj =    U 0x2227
val disj =    U 0x2228
val imp =     U 0x21D2
val neg =     U 0x00AC
val iff =     U 0x21D4
val not_iff = U 0x21CE
val fwAmpersand = U 0xFF06

(* not constants, but might be useful *)
val neq =       U 0x2260
val turnstile = U 0x22A2

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

(* brackets, braces and parentheses *)
val double_bracel = U 0x2983
val double_bracer = U 0x2984
val langle = U 0x27E8
val rangle = U 0x27E9
val double_langle = U 0x27EA
val double_rangle = U 0x27EB
val lensel = U 0x2987
val lenser = U 0x2988
val clgl = U 0x2308
val clgr = U 0x2309
val flrl = U 0x230A
val flrr = U 0x230B


(*stars*)
val blackstar            = U 0x2605
val whitestar            = U 0x2606
val bigasterisk          = U 0x229B
val asterisk             = U 0x2217
val circlestar           = U 0x235F
val stardiaeresis        = U 0x2363

(* quotation marks *)
val ldquo = U 0x201C
val lsquo = U 0x2018
val rdquo = U 0x201D
val rsquo = U 0x2019

(* superscripts *)
val sup_0 =      U 0x2070
val sup_1 =      U 0x00B9
val sup_2 =      U 0x00B2
val sup_3 =      U 0x00B3
val sup_4 =      U 0x2074
val sup_5 =      U 0x2075
val sup_6 =      U 0x2076
val sup_7 =      U 0x2077
val sup_8 =      U 0x2078
val sup_9 =      U 0x2079
val sup_plus =   U 0x207A
val sup_minus =  U 0x207B
val sup_eq =     U 0x207C
val sup_lparen = U 0x207D
val sup_rparen = U 0x207E
val sup_h =      U 0x02B0
val sup_i =      U 0x2071
val sup_j =      U 0x02B2
val sup_l =      U 0x02E1
val sup_n =      U 0x207F
val sup_r =      U 0x02B3
val sup_s =      U 0x02E2
val sup_w =      U 0x02B7
val sup_x =      U 0x02E3
val sup_y =      U 0x02B8
val sup_gamma =  U 0x02E0

(* subscripts *)
val sub_plus =   U 0x208A
val sub_r =      U 0x1D63

(* arithmetic *)
val leq =   U 0x2264
val geq =   U 0x2265
val nats =  U 0x2115
val ints =  U 0x2124
val reals = U 0x211D
val rats =  U 0x211A
val minus = U 0x2212

(* sets *)
val emptyset =      U 0x2205
val subset =        U 0x2286
val inter =         U 0x2229
val union =         U 0x222A
val setelementof =  U 0x2208
val not_elementof = U 0x2209
val universal_set = U 0x1D54C  (* outside BMP! *)

(* words *)
val lo = "<" ^ sub_plus
val hi = ">" ^ sub_plus
val ls = leq ^ sub_plus
val hs = geq ^ sub_plus
val or =  U 0x2016
val xor = U 0x2295
val lsl = U 0x226A
val asr = U 0x226B
val lsr = U 0x22D9
val rol = U 0x21C6
val ror = U 0x21C4

val doubleplus = U 0x29FA

fun isAlpha_i i =
  if i < 128 then Char.isAlpha (Char.chr i)
  else
    0x370 <= i andalso i <= 0x3ff andalso i <> 0x37E (* Greek *) orelse
    i = 0xAA (* ordinal a *) orelse
    i = 0xB5 (* Latin-1 mu *) orelse
    i = 0xBA (* ordinal o *) orelse
    0xC0 <= i andalso i <= 0xFF andalso i <> 0xD7 andalso i <> 0xF7
     (* Latin-1 *) orelse
    0x1D400 <= i andalso i <= 0x1D7CB
     (* beyond BMP "Math Alphanumeric Symbols", excluding digits starting at
        U+1D7CE *)
fun isDigit_i i =
  if i < 128 then Char.isDigit (Char.chr i)
  else
    0x2080 <= i andalso i <= 0x2089 (* subscripts *)
fun isAlphaNum_i i = isAlpha_i i orelse isDigit_i i
fun isSymbolic_i i =
  if i < 128 then Char.isPunct (Char.chr i)
  else not (isAlphaNum_i i)
val c' = Char.ord #"'"
val c_ = Char.ord #"_"
fun isMLIdent_i i = isAlphaNum_i i orelse i = c' orelse i = c_

fun flip2itest P s =
    case UTF8.getChar s of
        NONE => false
      | SOME ((_, i), _) => P i
val isAlpha = flip2itest isAlpha_i
val isDigit = flip2itest isDigit_i
val isSymbolic = flip2itest isSymbolic_i
fun isAlphaNum s = isAlpha s orelse isDigit s
fun isMLIdent s = isAlphaNum s orelse s = "'" orelse s = "_"


(* see Unicode section of
      https://en.wikipedia.org/wiki/Whitespace_character
*)
val individual_pts = [0x20, 0x85, 0xA0, 0x1680, 0x2028, 0x2029, 0x202F, 0x205F,
                      0x3000]
fun mem i [] = false
  | mem i (h::t) = i = h orelse mem i t
fun isSpace_i i =
    0x9 <= i andalso i <= 0xD orelse
    0x2000 <= i andalso i <= 0x200A orelse
    mem i individual_pts
val isSpace = flip2itest isSpace_i

fun foldthis (s, (sm,im,i)) =
    let
      val ((_, k), _) = valOf (UTF8.getChar s)
    in
      (Binarymap.insert(sm,s,i), Binarymap.insert(im,k,i), i + 1)
    end
val (supdigits_smap, supdigits_imap, _) =
    List.foldl foldthis (Binarymap.mkDict String.compare,
                         Binarymap.mkDict Int.compare,
                         0)
               [sup_0, sup_1, sup_2, sup_3, sup_4, sup_5, sup_6, sup_7,
                sup_8, sup_9]
fun supDigitVal s = Binarymap.peek(supdigits_smap, s)
fun supDigitVal_i i = Binarymap.peek(supdigits_imap, i)

fun isSupDigit_i i = isSome (Binarymap.peek(supdigits_imap, i))
fun isSupDigit s = isSome (supDigitVal s)


end (* struct *)
