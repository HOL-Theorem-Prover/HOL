structure stringML :> stringML =
struct

val emptystring = "";
val explode = String.explode;
val implode = String.implode;
fun strlen s = Arbnum.fromInt(String.size s);
fun strcat s1 s2 = String.concat [s1,s2];
val is_prefix = String.isPrefix;

(* Dodgy? *)
fun chr n = Char.chr (Arbnum.toInt n);

(*
val _ = app ConstMapML.insert
           [(stringSyntax.chr_tm,        ("stringML","chr")),
            (stringSyntax.emptystring_tm,("stringML","emptystring")),
            (stringSyntax.implode_tm,    ("stringML","implode")),
            (stringSyntax.explode_tm,    ("stringML","explode")),
            (stringSyntax.strlen_tm,     ("stringML","strlen")),
            (stringSyntax.strcat_tm,     ("stringML","strcat")),
            (stringSyntax.isprefix_tm,   ("stringML","is_prefix"))];

*)
end
