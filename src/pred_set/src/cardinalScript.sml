Theory cardinal[bare]
Ancestors
  cardinalityCore pred_set pair sum option wellorder set_relation
Libs
  HolKernel Parse boolLib

(* ----------------------------------------------------------------------
    Cardinality, with its notation.

    cardinalityCoreTheory has the definitions and the theorems and makes
    no grammar of its own, so that a theory needing the *facts* -- the
    datatype package needs them for a functor's bound, and so becomes
    every theory's ancestor -- does not thereby give every theory the
    notation as well.  The ASCII forms are the ones that bite: `=~` is
    a token wherever this grammar reaches, and `a = ~b` is then read as
    `a =~ b`.

    This theory is the notation, and re-exports what it is about.
   ---------------------------------------------------------------------- *)

val _ =
    let val seen = ref ([] : string list)
        fun once (nm, th) =
            if List.exists (fn n => n = nm) (!seen) then ()
            else (seen := nm :: !seen; ignore (save_thm (nm, th)))
    in
      List.app once (DB.definitions "cardinalityCore" @
                     DB.thms "cardinalityCore")
    end

Overload "𝟚" = “{T;F}”
Overload "ℵ₀" = “univ(:num)”
val _ = set_fixity "=~" (Infix(NONASSOC, 450));
val _ = Unicode.unicode_version {u = UTF8.chr 0x2248, tmnm = "=~"};
val _ = TeX_notation {hol = "=~",            TeX = ("\\ensuremath{\\approx}", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x2248, TeX = ("\\ensuremath{\\approx}", 1)};
Overload "=~" = ``cardeq``
Overload "≉" = “λa b. ¬(a ≈ b)”
val _ = set_fixity "≉" (Infix(NONASSOC, 450))
Overload "<<=" = ``cardleq``
val _ = set_fixity "<</=" (Infix(NONASSOC, 450));
val _ = Unicode.unicode_version {u = UTF8.chr 0x227A, tmnm = "<</="};
val _ = TeX_notation {hol = "<</=",          TeX = ("\\ensuremath{\\prec}", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x227A, TeX = ("\\ensuremath{\\prec}", 1)};
Overload cardlt = ``\s1 s2. ~(cardleq s2 s1)``(* cardlt *)
Overload "<</=" = ``cardlt``
val _ = set_fixity "<=_c" (Infix(NONASSOC, 450)); (* for cardleq *)
Overload "<=_c" = ``cardleq``
Overload "<<=" = ``$<=_c``(* defined in pred_setTheory *)
val _ = set_fixity "<_c" (Infix(NONASSOC, 450));  (* for cardlt *)
Overload "<_c" = ``cardlt``
Overload "<</=" = ``$<_c``
val _ = set_fixity ">=_c" (Infix(NONASSOC, 450)); (* for cardgeq *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x227D, tmnm = ">=_c"};
val _ = TeX_notation {hol = ">=_c",          TeX = ("\\ensuremath{\\succcurlyeq}", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x227D, TeX = ("\\ensuremath{\\succcurlyeq}", 1)};
val _ = set_fixity ">_c" (Infix(NONASSOC, 450));  (* for cardgt *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x227B, tmnm = ">_c"};
val _ = TeX_notation {hol = ">_c",           TeX = ("\\ensuremath{\\succ}", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x227B, TeX = ("\\ensuremath{\\succ}", 1)};
val _ = set_fixity "=_c" (Infix(NONASSOC, 450));  (* for cardeq *)
Overload "=_c" = ``cardeq``
Overload "=~" = ``$=_c``
Overload ">=_c" = ``cardgeq``
Overload ">_c" = ``cardgt``
