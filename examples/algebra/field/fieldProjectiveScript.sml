Theory fieldProjective
Ancestors
  field ringLib fieldRing
Libs
  ringLib

Overload "+"[local] = “r.sum.op”
Overload "*"[local] = “r.prod.op”
Overload "**"[local] = “r.prod.exp”
Overload "/"[local] = “field_div r”

(* Ordinary homogeneous coordinates: the affine point is (x/z,y/z). *)
Theorem projective_denominator_clear:
    Field r /\ a IN r.carrier /\ b IN r.carrier /\
    x IN r.carrier /\ y IN r.carrier /\ z IN r.carrier /\
    z <> r.sum.id ==>
    (y ** 2 * z = x ** 3 + a * x * z ** 2 + b * z ** 3 <=>
     (y / z) ** 2 = (x / z) ** 3 + a * (x / z) + b)
Proof
    rpt strip_tac >>
    ‘a IN ring_carrier (toRing r) /\
     b IN ring_carrier (toRing r) /\
     x IN ring_carrier (toRing r) /\
     y IN ring_carrier (toRing r) /\
     z IN ring_carrier (toRing r) /\ z <> ring_0 (toRing r)’
      by simp [toRing_operations] >>
    ‘ring_inv (toRing r) z IN ring_carrier (toRing r)’
      by metis_tac [FIELD_INV] >>
    ‘ring_mul (toRing r) (ring_inv (toRing r) z) z =
     ring_1 (toRing r)’
      by metis_tac [FIELD_MUL_LINV] >>
    qpat_x_assum ‘Field r’ (fn th =>
      ONCE_REWRITE_TAC
        (GSYM (MATCH_MP field_toRing_div (MATCH_MP field_is_ring th)) ::
         map GSYM (CONJUNCTS
           (MATCH_MP toRing_operations (MATCH_MP field_is_ring th))))) >>
    rewrite_tac [ring_div_def] >>
    (* RING_TAC finds its ring among free variables; its input equations
       must be equations of ring elements, not of rings. *)
    qmatch_goalsub_abbrev_tac `ring_pow s` >>
    qpat_x_assum `Abbrev (s = _)` kall_tac >>
    eq_tac >> strip_tac >> ringLib.RING_TAC
QED
