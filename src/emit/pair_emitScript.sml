open HolKernel boolLib bossLib Parse;
open EmitML pairTheory;

val _ = new_theory "pair_emit";

val defs = 
  map EmitML.DEFN [CURRY_DEF,UNCURRY_DEF,FST,SND,PAIR_MAP_THM,LEX_DEF_THM];

val _ = eSML "pair" defs;
val _ = eCAML "pair" defs;

val _ = adjoin_to_theory
  {sig_ps = NONE,
   struct_ps = SOME (fn ppstrm =>
     (PP.add_string ppstrm  "val _ = ConstMapML.insert pairSyntax.comma_tm;";
      PP.add_newline ppstrm))}

val _ = export_theory ();
