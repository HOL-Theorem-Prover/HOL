open HolKernel Parse boolLib

(* File: enumfDemo Author: F. Lockwood Morris created: 17 Dec. 2013 *)

(* A small example exercising much of the finite-sets-and-maps package
   via computation of a transitive closure of a relation whose element
   type is string # num. *)

open totoTheory  totoTacs tcTacs enumTacs fmapalTacs;

(* Start with the Hasse diagram of the relation of lineal descent
   on nine of the Romanov emperors. *)

val RomHasse =
``fmap [(("PETER", 1), {("PETER", 3)});
        (("PETER", 3), {("PAUL", 1)});
        (("CATHERINE", 2), {("PAUL", 1)});
        (("PAUL", 1), {("ALEXANDER", 1); ("NICHOLAS", 1)});
        (("NICHOLAS", 1), {("ALEXANDER", 2)});
        (("ALEXANDER", 2), {("ALEXANDER", 3)});
        (("ALEXANDER", 3), {("NICHOLAS", 2)})]``;

val tsarto_CONV = lextoto_CONV stringto_CONV numto_CONV;

val RomH = ENUF_CONV tsarto_CONV ``stringto lextoto numto`` RomHasse;

val tsar_tc = ``(FMAP_TO_RELN ^(rand (concl RomH)))^+``;

val tsar_anc_thm = Count.apply (TC_CONV tsarto_CONV) tsar_tc;
(* 21401 primitive inferences *)

val tsar_enum_fmap =  Count.apply (FMAPAL_TO_fmap_CONV tsarto_CONV)
              (rand (rand (concl tsar_anc_thm)));
(* 912 primitive inferences *)

val alist =
rand (concl
 (Count.apply (MAP_ELEM_CONV (RAND_CONV (ENUMERAL_TO_DISPLAY_CONV tsarto_CONV)))
  (rand (rand (concl tsar_enum_fmap)))));
(* 3665 primitive inferences *)

(* Find that the transitive closure holds of a particular pair *)

val tcpair = let
  val tc_fmapal = rand (rand (concl tsar_anc_thm))
  val testNic2 = ``("NICHOLAS", 2) IN (^tc_fmapal ' ("PETER", 1))``
in
  (Count.apply (RAND_CONV (FAPPLY_CONV tsarto_CONV)) (* 178 prim infs *) THENC
   Count.apply (IN_CONV tsarto_CONV) (* 221 prim infs *)) testNic2
end;

(* Same example the asymptotically slow way, with no trees. *)

val TSAR_EQ_CONV =
  REWR_CONV pairTheory.PAIR_EQ THENC
  RATOR_CONV (RAND_CONV stringLib.string_EQ_CONV) THENC
  numLib.REDUCE_CONV

val tsar_anc_no_trees =
    Count.apply (TC_CONV TSAR_EQ_CONV) ``(FMAP_TO_RELN ^RomHasse)^+``;
(* 15254 primitive inferences *)

(* Find that the transitive closure holds of a particular pair *)

val tcpair' = let
  val tc_fmap = rand (rand (concl tsar_anc_no_trees))
  val testNic2 = ``("NICHOLAS", 2) IN (^tc_fmap ' ("PETER", 1))``
in
  (Count.apply (RAND_CONV (FAPPLY_CONV TSAR_EQ_CONV)) (* 66 prim infs *) THENC
   Count.apply (IN_CONV TSAR_EQ_CONV) (* 473 prim infs *)) testNic2
end;
