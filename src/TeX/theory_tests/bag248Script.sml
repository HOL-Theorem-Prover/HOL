open HolKernel Parse boolLib bossLib;

val _ = new_theory "bag248";

val BAG_IN = new_definition (
  "BAG_IN",
  ``BAG_IN (e:'a) b = 1 <= b e``);

val _ = set_fixity "<:" (Infix(NONASSOC, 425))
val _ = overload_on ("<:", ``BAG_IN``)
val _ = Unicode.unicode_version {tmnm = "<:", u = UTF8.chr 0x22F2}
        (* U+22F2 looks like ⋲ in your current font; unfortunately this   (* UOK *)
           symbol doesn't seem to correspond to anything in LaTeX... *)
val _ = TeX_notation {hol = "<:", TeX = ("\\HOLTokenIn{}:",2)}
val _ = TeX_notation {hol = UTF8.chr 0x22F2, TeX = ("\\HOLTokenIn{}:",2)}

val _ = export_theory();
