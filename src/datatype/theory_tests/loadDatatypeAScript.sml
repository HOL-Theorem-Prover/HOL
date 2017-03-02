open HolKernel Parse boolLib

open Datatype

val _ = new_theory "loadDatatypeA";

val _ = Datatype`enum = EC1 | EC2 | EC3 | EC4`;

val _ = Datatype`simple = SC1 num | SC2 bool num`

val _ = Datatype`polysimple = PS1 'a | PS2 'b num`

val _ = Datatype`recursive = RC1 num | RC2 recursive bool`

val _ = Datatype`polyrec = PR1 'a | PR2 polyrec 'b`;

val _ = Datatype`simpleref = SR1 num | SR2 ((num,'a) polyrec)`

val _ = Datatype`
  mut1 = con1 'a num | con2 mut2 ;
  mut2 = con3 bool | con4 mut1 mut2
`;

val _ = Datatype`simplenest = SN1 num | SN2 (simplenest option)`;

(* bug in older implementations of Datatype too --
val _ = Datatype`
  nested1 = con5 'a nested2 ;
  nested2 = con6 (nested1 mut1)
`;
*)


val _ = export_theory();
