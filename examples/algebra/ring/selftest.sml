(* ========================================================================= *)
(*  A decision procedure for the universal theory of rings (test cases)      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(* ========================================================================= *)

open HolKernel Portable Parse boolLib;

open ringLib testutils;

(* Tests for RING_RULE

   NOTE: RING_RULE may output theorem with extra antecedents in comparison with
         the input term.
 *)
fun rule_test prover (r as (n,tm)) =
    let
      fun check res = let
          val input = tm and output = concl res;
      in
          input ~~ output orelse
          if is_imp output then
             input ~~ rand output
          else
             false
      end
    in
      tprint (n ^ ": " ^ term_to_string tm);
      require_msg (check_result check) (term_to_string o concl) prover tm
    end;

(* NOTE: These test cases were taken from calls of RING_RULE in HOL-Light's
        "ringtheory.ml".
 *)
val _ = List.app (rule_test RING_RULE) [
      ("RING_RULE_00",
       “ring_mul r y1 (ring_inv r y1) = ring_1 r /\
        ring_mul r y2 (ring_inv r y2) = ring_1 r /\
        ring_mul r x1 y2 = ring_mul r x2 y1
    ==> ring_mul r x1 (ring_inv r y1) = ring_mul r x2 (ring_inv r y2)”),
      ("RING_RULE_01",
       “z IN ring_carrier r
    ==> ring_add r z (ring_1 r) = ring_add r (ring_1 r) z /\
        ring_sub r z (ring_1 r) = ring_neg r (ring_sub r (ring_1 r) z)”),
      ("RING_RULE_02",
       “ring_1 r = ring_sub r (ring_1 r) (ring_0 r)”),
      ("RING_RULE_03",
       “u IN ring_carrier r /\ v IN ring_carrier r /\ z IN ring_carrier r /\
        ring_mul r u (v :'a) = ring_1 r
    ==> ring_add r u z =
        ring_mul r u (ring_add r (ring_1 r) (ring_mul r v z)) /\
        ring_add r z u =
        ring_mul r u (ring_add r (ring_1 r) (ring_mul r v z)) /\
        ring_sub r u z =
        ring_mul r u (ring_sub r (ring_1 r) (ring_mul r v z)) /\
        ring_sub r z u =
        ring_mul r u (ring_neg r
           (ring_sub r (ring_1 r) (ring_mul r v z)))”),
      ("RING_RULE_04",
       “~(ring_mul r x y = ring_0 r)
    ==> x IN ring_carrier r /\ y IN ring_carrier r
        ==> ~(x = ring_0 r) /\ ~(y = ring_0 r)”),
      ("RING_RULE_05",
       “a IN ring_carrier r /\ b IN ring_carrier r /\ c IN ring_carrier r /\
        x IN ring_carrier r /\ y IN ring_carrier r /\
        ring_mul r a b = c
    ==> ring_mul r (ring_mul r x y) c =
        ring_mul r (ring_mul r x a) (ring_mul r y b)”),
      ("RING_RULE_06",
       “x IN ring_carrier r /\ y IN ring_carrier r /\
       (x = ring_0 r \/ y = ring_0 r)
    ==> ring_mul r x y = ring_0 r”),
      ("RING_RULE_07",
       “(x IN ring_carrier r /\ y IN ring_carrier r) /\
        (x = ring_0 r \/ y = ring_0 r)
    ==> ring_mul r x y = ring_0 r”),
      ("RING_RULE_08",
       “x IN ring_carrier r /\ y IN ring_carrier r
    ==> x = ring_add r y (ring_sub r x y)”)
      ];
