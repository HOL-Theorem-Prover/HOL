open HolKernel Parse boolLib bossLib;
open pred_setTheory;
open listTheory;

val _ = new_theory "hilbert";

(* Useful definition/s *)
Definition only_one_def:
  only_one A ⇔ ∃!i . EL i A ∧ i < LENGTH A
End

(* GEOMETRY BEGINS *)
(* Hilbert's axioms *)

(* GROUP 1: AXIOMS OF CONNECTION *)
(* Types of point, line. *)
val _ = new_type("point", 0);
val _ = new_type("line", 0);
val _ = new_constant ("on_line", “:point -> line -> bool”);
val _ = set_mapped_fixity{term_name = "on_line", tok = "ol", fixity = Infix(NONASSOC,450)};
val _ = set_mapped_fixity{term_name = "on_line", tok = "∊", fixity = Infix(NONASSOC,450)};

(* G1.1 There exists a straight line passing through any two points. *)
val line_exists = new_axiom("line_exists",
                            “∀p₁ p₂ . ∃l . on_line p₁ l ∧ on_line p₂ l”);

(* G1.2) There exists only one straight line passing through any two distinct points. *)
val line_unique = new_axiom("line_unique",
                            “∀p₁ p₂ . p₁ ≠ p₂ ⇒ ∃! l. on_line p₁ l ∧ on_line p₂ l”);

Definition line_def:
  line a b = @l . on_line a l ∧ on_line b l
End

Definition points_on_a_line_def:
  points_on_a_line l = {p | on_line p l}
End

Definition collinear_def:
  collinear ps = ∃l . ∀p . p ∈ ps ⇒ on_line p l
End

Theorem on_line_thm[simp]:
  on_line a (line a b) ∧ on_line b (line a b)
Proof
  strip_tac >> simp[line_def] >> SELECT_ELIM_TAC >> metis_tac[line_exists]
QED

Theorem collinear_two[simp]:
  collinear {a;b}
Proof
  simp[collinear_def] >> metis_tac[line_exists]
QED

Theorem on_line_implies_collinear_thm:
   a ol l ∧ b ol l ∧ c ol l ⇒ collinear {a;b;c}
Proof
  simp[collinear_def] >> strip_tac >> qexists ‘l’ >> strip_tac >> metis_tac[]
QED

Theorem not_collinear_implies_not_on_line:
  ¬collinear {a;b;c} ⇒ ¬(c ol (line a b))
Proof
  strip_tac >> reverse $ Cases_on ‘c ol (line a b)’ >- simp[]
  >> metis_tac[on_line_thm,on_line_implies_collinear_thm]
QED

Theorem unique_line:
  ∀p₁ p₂. ∀l m. p₁ ≠ p₂ ∧ on_line p₁ l ∧ on_line p₂ l ∧ on_line p₁ m ∧ on_line p₂ m ⇒ l = m
Proof
  metis_tac[line_unique]
QED

Theorem one_line:
  ∀ a . ∃l . l = line a a
Proof
  simp[line_def]
QED

Theorem three_points_on_same_line:
  ∀a b c l. a ≠ c ∧ a ol l ∧ b ol l ∧ c ol l ⇒ b ol (line a c)
Proof
  simp[line_def] >> metis_tac[line_unique]
QED

Theorem collinear_line:
  a ≠ b ∧ collinear {a;b;x} ⇒ x ol (line a b)
Proof
  rw[collinear_def] >> metis_tac[three_points_on_same_line]
QED

Theorem collinear_implies_line_equations:
  a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ collinear {a;b;c} ⇒ line c b = line a b ∧ line c a = line a b
Proof
  rw[collinear_def,DISJ_IMP_THM,FORALL_AND_THM] >> metis_tac[line_unique,on_line_thm]
QED

Theorem line_symm:
  a ≠ b ⇒ line a b = line b a
Proof
  simp[line_def] >> metis_tac[line_unique]
QED

Theorem equal_lines_thm:
  l = m ⇒ (p ol l ⇔ p ol m)
Proof
  metis_tac[]
QED

Theorem on_line_switch_thm:
  line x a = line y b ⇒ (x ol (line x a) ⇔ x ol (line y b))
Proof
  strip_tac >> metis_tac[on_line_thm]
QED

Theorem equal_line_def_thm:
  line x a = line y b ⇒ x ol (line y b)
Proof
  metis_tac[on_line_thm]
QED

Theorem on_line_collinear_thm:
  line x a = line y b ⇒ collinear {a;b;y;b}
Proof
  strip_tac >> ‘x ol (line x a) ∧ a ol (line x a) ∧ y ol (line x a) ∧ b ol (line x a)’ by metis_tac[on_line_thm] >> simp[collinear_def] >> qexists ‘line x a’ >> strip_tac >> metis_tac[]
QED

(* Any two different lines have either one point or no point in common *)
Theorem two_lines_thm:
  ∀l m. l ≠ m ⇒ (¬∃p . on_line p l ∧ on_line p m) ∨ (∃!p . on_line p l ∧ on_line p m)
Proof
  metis_tac[line_unique]
QED

(* G1.3 (part 1) At least two points lie on any straight line. *)
val at_least_two_points_on_line = new_axiom("at_least_two_points_on_line",
                                           “∀l. ∃ p₁ p₂. p₁ ≠ p₂ ∧ on_line p₁ l ∧ on_line p₂ l”);

(* G1.3 (part 2) There exist at least three points not lying on the same straight line, i.e. there exist non-trivial triangles. *)
val exist_three_non_collinear_points = new_axiom("exist_three_non_collinear_points",
                                                 “∃p₁ p₂ p₃ . ¬collinear {p₁;p₂;p₃}”);

Theorem exists_point_not_on_line:
  ∀l . ∃p . ¬on_line p l
Proof
  strip_tac
  >> ‘∃p₁ p₂ p₃ . ¬collinear {p₁;p₂;p₃}’ by rw[exist_three_non_collinear_points]
  >> ‘¬∃l . ∀p . p ∈ {p₁;p₂;p₃} ⇒ on_line p l’ by metis_tac[collinear_def]
  >> reverse $ Cases_on ‘p₁ ol l’ >- (qexists ‘p₁’ >> simp[])
  >> reverse $ Cases_on ‘p₂ ol l’ >- (qexists ‘p₂’ >> simp[])
  >> reverse $ Cases_on ‘p₃ ol l’ >- (qexists ‘p₃’ >> simp[])
  >> metis_tac[on_line_implies_collinear_thm]
QED

Theorem different_lines_exist:
 ∃l m : line . l ≠ m
Proof
  ‘∃a b . a ≠ b ∧ a ol l ∧ b ol l’ by rw[at_least_two_points_on_line]
  >> ‘∃c . ¬(c ol l)’ by rw[exists_point_not_on_line] >> ‘c ≠ a ∧ c ≠ b’ by metis_tac[]
  >> ‘∃m₁ . a ol m₁ ∧ c ol m₁’ by metis_tac[line_unique]
  >> ‘∃m₂ . b ol m₂ ∧ c ol m₂’ by metis_tac[line_unique]
  >> ‘m₁ ≠ m₂’ by metis_tac[line_unique]
  >> qexistsl [‘m₁’,‘m₂’] >> metis_tac[]
QED

Theorem two_lines_through_point:
  ∀p. ∃l m . on_line p l ∧ on_line p m ∧ l ≠ m
Proof
  metis_tac[line_exists, exist_three_non_collinear_points,collinear_def]
QED

(* GROUP 2: AXIOMS OF ORDER *)
val _ = new_constant ("between", “:point -> point -> point -> bool”);
Overload opposite_side_of_point = “λ p a b. between p a b”
Overload BT = “λ x a b . between x a b”

(* G2.1.1) If B lies between A and C, then A, B, C are distinct points on the same line. *)
val between_implies_distinct_collinear = new_axiom(
  "between_implies_distinct_collinear",
  “∀a b c . between b a c ⇒ ALL_DISTINCT [a;b;c] ∧ collinear {a;b;c}”);

Theorem between_irrefl[simp]:
  ¬between b a a
Proof
  strip_tac >> drule between_implies_distinct_collinear >> simp[]
QED

Theorem between_implies_on_line:
  ∀a b c . between b a c ⇒ b ol (line a c) ∧ a ol (line b c) ∧ c ol (line a b)
Proof
  rpt strip_tac >> ‘collinear {a;b;c}’ by metis_tac[between_implies_distinct_collinear]
  >> ‘∃l . a ol l ∧ b ol l ∧ c ol l’ by metis_tac[collinear_def, NOT_IN_EMPTY, IN_INSERT]
  >> ‘a ≠ b ∧ b ≠ c ∧ c ≠ a’ by metis_tac[between_implies_distinct_collinear, ALL_DISTINCT, MEM]
  >> metis_tac[three_points_on_same_line]
QED

Theorem between_implies_on_line':
  ∀a b c . between b a c ⇒ b ol (line a c) ∧ a ≠ c
Proof
  metis_tac[between_implies_on_line,between_implies_distinct_collinear,ALL_DISTINCT,MEM]
QED


(* G2.1.2 If B lies between A and C, then B lies also between C and A (symmetry). *)
val between_symm = new_axiom("between_symm",
                                     “∀a b c . between b a c ⇒ between b c a”);

(* G2.2 (part 1)) If A and C are two distinct points on a line, then there exists at least one point B that lies between A and C. *)
val between_exists = new_axiom("between_exists",
                               “∀a c . a ≠ c ⇒ ∃b . between b a c”);

(* G2.2 (part 2) If A and B are two distinct points on a line then there exists at least one point C that is so situated that B lies between A and C (so C is beyond B). *)
val beyond_exists = new_axiom("beyond_exists",
                                “∀a b . a ≠ b ⇒ ∃c . between b a c”);

(* G2.3) Of any three points situated on a straight line, there is always one and only one which lies between the other two. *)
val exactly_one_between = new_axiom("exactly_one_between",
                                    “∀a b c. collinear {a;b;c} ∧ ALL_DISTINCT [a;b;c]
                                                            ⇒ only_one [between a b c;between b c a;between c a b]”);

(* G2.4) Any four points A, B, C, D of a straight line can always be so arranged that B shall lie between A and C and also between A and D, and, furthermore, that C shall lie between A and D and also between B and D. *)
val four_points_arranged = new_axiom("four_points_arranged",
 “∀a b c d . ALL_DISTINCT [a;b;c;d] ∧ collinear {a;b;c;d} ⇒
               ∃a' b' c' d' . {a;b;c;d} = {a';b';c';d'} ∧ between b' a' c' ∧ between b' a' d'
                                                    ∧ between c' a' d' ∧ between c' b' d'”);

(* Segment definition *)
Type segment = “:point -> bool”;

val thm = REFL (“f:segment”);

Definition is_segment_def:
  is_segment (s : segment) ⇔ ∃a b . a ≠ b ∧ s = {a;b}
End

Theorem distinct_two_implies_segment:
  a ≠ b ⇒ is_segment {a;b}
Proof
  rw[is_segment_def] >> qexistsl [‘a’,‘b’] >> simp[]
QED

Theorem singleton_set[simp]:
  {a} = {a';b} ⇔ a = a' ∧ a = b
Proof
 rw[EXTENSION] >> metis_tac[]
QED

Definition line_of_segment_def:
  line_of_segment s = @l . ∃a b . s = {a;b} ∧ l = line a b
End

Definition interior_of_segment_def:
  interior_of_segment p s = ∃a b . s = {a;b} ∧ between p a b
End

Theorem set_elements_lemma:
  {x;y} = {a;b} ⇔ x = a ∧ y = b ∨ x = b ∧ y = a
Proof
  simp[EXTENSION] >> metis_tac[]
QED

Theorem between_implies_interior:
  ∀a b c . between b a c ⇒ interior_of_segment b {a;c}
Proof
  simp[interior_of_segment_def] >> rpt strip_tac >> qexistsl [‘a’,‘c’] >> simp[] >> metis_tac[between_implies_on_line]
QED

Theorem interior_implies_between:
  ∀a b c . interior_of_segment b {a;c} ⇒ between b a c
Proof
  simp[interior_of_segment_def] >> rpt strip_tac
  >> ‘a = a' ∧ c = b' ∨ a = b' ∧ c = a'’ by metis_tac[set_elements_lemma]
  >- metis_tac[] >> metis_tac[between_symm]
QED

Theorem interior_implies_on_line:
  ∀a b c . interior_of_segment b {a;c} ⇒ b ol (line a c)
Proof
  rpt strip_tac >> ‘between b a c’ by simp[interior_implies_between] >> ‘{a;b;c} = {a;c;b}’ by simp[SET_EQ_SUBSET]
  >> metis_tac[collinear_line,between_implies_distinct_collinear,ALL_DISTINCT,MEM]
QED

Definition outside_of_segment_def:
  outside_of_segment p s = ∃a b . s = {a;b} ∧ a ≠ b ∧ p ol (line a b) ∧ ¬between p a b ∧ p ≠ a ∧ p ≠ b
End

Definition extremity_of_segment_def:
  extremity_of_segment p s = ∃a b . s = {a;b} ∧ a ≠ b ∧ (p = a ∨ p = b)
End

Theorem extremity_implies_end_point:
  ∀a b c . extremity_of_segment p {a;b} ⇒ p = a ∨ p = b
Proof
  simp[extremity_of_segment_def] >> rpt strip_tac
  >> ‘a = a' ∧ b = b' ∨ a = b' ∧ b = a'’ by metis_tac[set_elements_lemma]
  >> simp[] >> metis_tac[]
QED

Definition line_intersects_segment_def:
  line_intersects_segment l s = ∃p . p ol l ∧ (interior_of_segment p s ∨ extremity_of_segment p s)
End

Theorem line_intersects_segment_unique_point:
  l ≠ line a b ⇒ ∀p p' . p ol l ∧ p' ol l
                          ∧ (interior_of_segment p {a;b} ∨ extremity_of_segment p {a;b})
                          ∧ (interior_of_segment p' {a;b} ∨ extremity_of_segment p' {a;b}) ⇒ p = p'
Proof
  strip_tac >> metis_tac[interior_implies_on_line, extremity_implies_end_point, unique_line, on_line_thm]
QED

Definition segments_intersect_def:
  segments_intersect r s = ∃p . interior_of_segment p r ∧ interior_of_segment p s
End

Definition segments_connect_def:
  segments_connect r s = ∃a b c . r = {a;b} ∧ s = {b;c}
End

Definition lines_intersect_def:
  lines_intersect l m = ∃p . on_line p l ∧ on_line p m
End

(* G2.5) (Pasch's axiom) Let A, B, C be three non-collinear points and let l be a straight line not passing through any of these points. Then, if l passes through a point of the segment AB, it will also pass through either a point of the segment BC or a point of the segment AC. *)
val line_enters_must_exit_triangle = new_axiom(
  "line_enters_must_exit_triangle",
  “∀a b c l. ¬collinear {a;b;c} ∧ ¬on_line a l ∧ ¬on_line b l ∧ ¬on_line c l ∧ line_intersects_segment l {a;b} ⇒
                                  (line_intersects_segment l {b;c} ∨ line_intersects_segment l {a;c})
                               ∧ ¬(line_intersects_segment l {b;c} ∧ line_intersects_segment l {a;c})”);

(* Between any two points of a straight line, there always exists an unlimited number of points. *)
Theorem unlimited_points:
  ∀p₁ p₂ x . between x p₁ p₂ ⇒ ∃y . x ≠ y ∧ between y p₁ x
Proof
  metis_tac[between_exists,between_implies_distinct_collinear, ALL_DISTINCT, MEM]
QED

Theorem one_between:
  ∀x p₁ p₂ . between x p₁ p₂ ⇒ ¬between p₂ x p₁ ∧ ¬between p₁ x p₂
Proof
  rpt gen_tac >> strip_tac >>
  ‘ALL_DISTINCT [p₁;x;p₂] ∧ collinear {p₁;x;p₂}’ by metis_tac[between_implies_distinct_collinear] >>
  drule exactly_one_between >> simp[EXISTS_UNIQUE_THM, only_one_def] >> strip_tac >>
  pop_assum drule >> simp[]
  >> ‘between x p₂ p₁’ by metis_tac[between_symm] >> gvs[] >> strip_tac
  >> first_assum (qspec_then ‘1’ mp_tac) >> impl_tac >- simp[]
  >> strip_tac >> pop_assum SUBST_ALL_TAC
  >> first_assum (qspec_then ‘0’ mp_tac)
  >> simp_tac (srw_ss()) [] >>  strip_tac
  >> first_x_assum (qspec_then ‘2’ assume_tac) >> gvs[]
  >> metis_tac[between_symm]
QED

Theorem exactly_one_between_lemma:
  ∀a b c. collinear {a;b;c} ∧ ALL_DISTINCT [a;b;c] ∧ ¬between a b c ∧ ¬between b c a ⇒ between c a b
Proof
  rpt strip_tac >> drule exactly_one_between >> simp[EXISTS_UNIQUE_THM, only_one_def] >> strip_tac >>
  pop_assum drule >> simp[] >> strip_tac
  >> Cases_on ‘i = 0’ >- (‘EL 0 [F; F; BT c a b] = F’ by simp[] >> metis_tac[])
  >> Cases_on ‘i = 1’ >- (‘EL 1 [F; F; BT c a b] = F’ by simp[] >> metis_tac[])
  >> Cases_on ‘i = 2’ >> gvs[]
QED

Theorem between_property:
  ∀p₁ p₂ x y. between x p₁ p₂ ∧ between y p₁ x ⇒ between y p₁ p₂
Proof
  rpt strip_tac >>
  ‘x ≠ p₁ ∧ x ≠ p₂ ∧ p₁ ≠ p₂ ∧ y ≠ p₁ ∧ y ≠ x’ by metis_tac[between_implies_distinct_collinear, ALL_DISTINCT, MEM]
  >> ‘∃l . x ol l ∧  p₁ ol l ∧ p₂ ol l’ by metis_tac[between_implies_distinct_collinear, collinear_def, NOT_IN_EMPTY, IN_INSERT]
  >> ‘∃m . y ol m ∧ p₁ ol m ∧ x ol m’ by metis_tac[between_implies_distinct_collinear, collinear_def, NOT_IN_EMPTY, IN_INSERT]
  >> ‘m = l’ by metis_tac[line_unique] >> gvs[]
  >> ‘¬(between p₂ x p₁)’ by metis_tac[one_between]
  >> ‘y ≠ p₂’ by metis_tac[NOT_IN_EMPTY, IN_INSERT, between_symm, exactly_one_between]
  >> ‘ALL_DISTINCT [x;p₁;p₂;y]’ by simp[]
  >> ‘collinear {x;p₁;p₂;y}’ by (simp[collinear_def] >> metis_tac[])
  >> drule_all four_points_arranged >> strip_tac >> gvs[EXTENSION, IN_INSERT, NOT_IN_EMPTY]
  >> map_every (fn q => first_assum (qspec_then q mp_tac) >> rewrite_tac[] >> strip_tac >> gvs[]) [‘x’,‘y’,‘p₁’, ‘p₂’]
  >> metis_tac[one_between, between_symm]
QED

Theorem between_reverse_property:
  ∀p₁ p₂ x y. between x p₁ p₂ ∧ between y p₁ p₂ ∧ y ≠ x ⇒ between y p₁ x ∨ between y x p₂
Proof
  rpt strip_tac
  >> ‘ALL_DISTINCT [p₁;x;y;p₂]’ by metis_tac[between_implies_distinct_collinear,ALL_DISTINCT,MEM]
  >> ‘p₁ ≠ p₂’ by metis_tac[ALL_DISTINCT,MEM]
  >> ‘{p₁;x;p₂} = {p₁;p₂;x} ∧ {p₁;y;p₂} = {p₁;p₂;y}’ by simp[SET_EQ_SUBSET]
  >> ‘x ol (line p₁ p₂) ∧ y ol (line p₁ p₂) ∧ p₁ ol (line p₁ p₂) ∧ p₂ ol (line p₁ p₂)’
     by metis_tac[between_implies_distinct_collinear,collinear_line,on_line_thm]
  >> ‘collinear {p₁;x;y;p₂}’ by (simp[collinear_def] >> metis_tac[])
  >> drule_all four_points_arranged >> strip_tac >> gvs[EXTENSION, IN_INSERT, NOT_IN_EMPTY]
  >> map_every (fn q => first_assum (qspec_then q mp_tac) >> rewrite_tac[] >> strip_tac >> gvs[]) [‘x’,‘y’,‘p₁’, ‘p₂’]
  >> metis_tac[one_between, between_symm]
QED

Theorem between_implies_property:
  b ol l ∧ c ol l ∧ d ol l ∧ p ol l ∧ b ≠ c ∧ between b p d ⇒ between b p c ∨ between b c d
Proof
  rpt strip_tac
  >> Cases_on ‘BT c p d’ >- (irule between_reverse_property >> simp[])
  >> Cases_on ‘c = p’ >- gvs[]
  >> Cases_on ‘c = d’ >- gvs[]
  >> ‘ALL_DISTINCT [b;c;d;p]’ by metis_tac[between_implies_distinct_collinear,ALL_DISTINCT,MEM]
  >> ‘collinear {b;c;d;p}’ by (simp[collinear_def] >> metis_tac[])
  >> drule_all four_points_arranged >> strip_tac >> gvs[EXTENSION, IN_INSERT, NOT_IN_EMPTY]
  >> map_every (fn q => first_assum (qspec_then q mp_tac) >> rewrite_tac[] >> strip_tac >> gvs[]) [‘b’,‘c’,‘d’, ‘p’]
  >>  metis_tac[one_between, between_symm]
QED

Theorem unlimited_points_different_approach:
  ∀p₁ p₂ x . between x p₁ p₂ ⇒ ∃y . x ≠ y ∧ between y p₁ p₂
Proof
  metis_tac[unlimited_points, between_property, between_symm]
QED

Theorem line_intersects_between_lemma:
  ¬(a ∊ l) ∧ ¬(b ∊ l) ∧ ¬(c ∊ l) ∧ collinear {a;b;c}
                                 ∧ line_intersects_segment l {a; b} ∧ ¬line_intersects_segment l {c;b}
                                                                    ⇒ line_intersects_segment l {a;c}
Proof
  rw[line_intersects_segment_def]
  >- (qexists ‘p’ >> simp[] >> DISJ1_TAC
      >> ‘between p a b’ by simp[interior_implies_between]
      >> ‘collinear {a;p;b}’ by simp[between_implies_distinct_collinear] >> ‘{a;p;b} = {a;b;p}’ by simp[SET_EQ_SUBSET]
      >> ‘a ≠ b’ by metis_tac[between_implies_distinct_collinear,ALL_DISTINCT,MEM]
      >> ‘a ol (line a b) ∧ b ol (line a b) ∧ c ol (line a b) ∧ p ol (line a b)’
        by metis_tac[collinear_line,on_line_thm]
      >> ‘between p a c ∨ between p c b’ by metis_tac[between_implies_property]
      >- (simp[interior_of_segment_def] >> qexistsl [‘a’,‘c’] >> simp[])
      >> metis_tac[interior_of_segment_def])
  >> ‘p = a ∨ p = b’ by simp[extremity_implies_end_point] >> metis_tac[]
QED

Theorem four_points_between:
  BT p c b ∧ BT p c a ∧ BT p a b ⇒ F
Proof
  strip_tac >> ‘ALL_DISTINCT [a;b;c;p]’ by metis_tac[between_implies_distinct_collinear,ALL_DISTINCT,MEM]
  >> ‘collinear {a;b;c;p}’ by (imp_res_tac between_implies_distinct_collinear >> gvs[collinear_def] >> metis_tac[unique_line])
  >> drule_all four_points_arranged >> simp[EXTENSION] >> rpt strip_tac
  >> map_every (fn q => first_assum (qspec_then q mp_tac) >> rewrite_tac[] >> strip_tac >> gvs[]) [‘a’,‘b’,‘c’, ‘p’] >> metis_tac[one_between, between_symm]
QED

Theorem not_line_intersects_lemma:
  ¬(a ∊ l) ∧ ¬(b ∊ l) ∧ ¬(c ∊ l) ∧ collinear {a;b;c}
                                 ∧ line_intersects_segment l {a;b} ∧ line_intersects_segment l {c;a}
                                                                   ⇒ ¬line_intersects_segment l {c;b}
Proof
  rpt strip_tac >> drule_at (Pos last) collinear_implies_line_equations >> strip_tac
  >> ‘l ≠ line a b’ by metis_tac[on_line_thm]
  >> gvs[collinear_def,DISJ_IMP_THM,FORALL_AND_THM]
  >> gvs[line_intersects_segment_def]
  >> IMP_RES_TAC interior_implies_between >> IMP_RES_TAC extremity_implies_end_point
  >> IMP_RES_TAC between_implies_on_line' >> gvs[]
  >> ‘p' = p ∧ p'' = p’ by metis_tac[unique_line] >> gvs[] >> metis_tac[four_points_between]
QED

Theorem four_points_intersects_lemma:
  ¬(a ∊ l) ∧ ¬(b ∊ l) ∧ ¬(a' ∊ l) ∧ ¬(b' ∊ l)
  ∧ line_intersects_segment l {a;b} ∧ ¬line_intersects_segment l {a';a} ∧ ¬line_intersects_segment l {b';b}
                                                                        ⇒ line_intersects_segment l {a'; b'}
Proof
  ‘{a;b} = {b;a} ∧ {a';a} = {a;a'} ∧ {b';b} = {b;b'} ∧ {a';b'} = {b';a'}’ by simp[SET_EQ_SUBSET]
  >> rw[] >> CCONTR_TAC >> Cases_on ‘collinear {a;b;a'}’ >> Cases_on ‘collinear {a';b;b'}’
  >> metis_tac[line_intersects_between_lemma,line_enters_must_exit_triangle]
QED

(* Sides of line definitions *)
Definition same_side_of_line_def:
  same_side_of_line l b a ⇔ ¬on_line a l ∧ ¬on_line b l ∧ ((a = b) ∨ ¬line_intersects_segment l {a;b})
End

Definition opposite_side_of_line_def:
  opposite_side_of_line l b a ⇔ ¬on_line a l ∧ ¬on_line b l ∧ line_intersects_segment l {a;b}
End

Theorem opposite_side_of_line_irrefl[simp]:
  ¬opposite_side_of_line l a a
Proof
  rw[opposite_side_of_line_def,line_intersects_segment_def,interior_of_segment_def,extremity_of_segment_def]
QED

Theorem not_same_side_implies_thm:
  ¬same_side_of_line l b a ⇔ a ol l ∨ b ol l ∨ a ≠ b ∧ opposite_side_of_line l b a
Proof
  simp[same_side_of_line_def, opposite_side_of_line_def] >> metis_tac[]
QED

Theorem same_side_of_line_symm:
  same_side_of_line l a b ⇔ same_side_of_line l b a
Proof
  simp[same_side_of_line_def] >> ‘{a;b} = {b;a}’ by simp[SET_EQ_SUBSET] >> iff_tac >> metis_tac[]
QED

Theorem same_side_of_line_transitive:
  ∀p₁ p₂ a . same_side_of_line l a p₁ ∧ same_side_of_line l a p₂ ⇒ same_side_of_line l p₂ p₁
Proof
  simp[same_side_of_line_def] >> rpt strip_tac >> simp[]
  >- (‘{p₂;a} = {a;p₂}’ by simp[SET_EQ_SUBSET] >> simp[] >> metis_tac[])
  >> Cases_on ‘p₁ = p₂’ >- simp[]
  >> DISJ2_TAC >> strip_tac
  >> reverse $ Cases_on ‘collinear {p₁;p₂;a}’ >- metis_tac[line_enters_must_exit_triangle]
  >> ‘∃p . p ol l ∧ (interior_of_segment p {p₁;p₂} ∨ extremity_of_segment p {p₁;p₂})’
    by metis_tac[line_intersects_segment_def]
  >- (‘between p p₁ p₂’ by metis_tac[interior_implies_between]
      >> Cases_on ‘between p₂ p₁ a’
      >- metis_tac[between_property,between_implies_interior,line_intersects_segment_def]
      >> Cases_on ‘between p₁ p₂ a’
      >- metis_tac[between_property,between_implies_interior,line_intersects_segment_def,between_symm]
      >> Cases_on ‘a = p₁’
      >- (‘{p₁;p₂} = {p₂;a}’ by simp[SET_EQ_SUBSET] >> metis_tac[])
      >> Cases_on ‘a = p₂’ >- metis_tac[]
      >> ‘ALL_DISTINCT[p₁;p₂;a]’ by metis_tac[ALL_DISTINCT,MEM]
      >> ‘between a p₁ p₂’ by metis_tac[exactly_one_between_lemma,between_symm] >> ‘a ≠ p’ by metis_tac[]
      >> ‘between p p₁ a ∨ between p a p₂’ by metis_tac[between_reverse_property]
      >- metis_tac[between_implies_interior,line_intersects_segment_def]
      >> metis_tac[between_symm,between_implies_interior,line_intersects_segment_def])
  >> metis_tac[extremity_implies_end_point]
QED

Theorem points_opposite_line_exist:
  ∀l . ∃a c . opposite_side_of_line l c a
Proof
  strip_tac >> simp[opposite_side_of_line_def]
  >> ‘∃b . b ol l’ by metis_tac[at_least_two_points_on_line]
  >> ‘∃a . ¬(a ol l) ∧ a ≠ b’ by metis_tac[exists_point_not_on_line]
  >> ‘∃c . between b a c’ by metis_tac[beyond_exists]
  >> ‘c ol (line a b) ∧ b ol (line a b) ∧ b ol (line a c)’ by metis_tac[between_implies_on_line,on_line_thm]
  >> ‘line a b ≠ l’ by metis_tac[on_line_thm]
  >> ‘b ≠ c’ by metis_tac[between_implies_distinct_collinear,ALL_DISTINCT,MEM]
  >> Cases_on ‘c ol l’ >- metis_tac[two_lines_thm]
  >> simp[line_intersects_segment_def,interior_of_segment_def]
  >> qexistsl [‘a’,‘c’] >> simp[] >> qexists ‘b’ >> simp[]
  >> DISJ1_TAC >> qexistsl [‘a’,‘c’] >> simp[]
QED

Theorem opposite_implies_not_same_side_of_line:
  opposite_side_of_line l a p ⇒ ¬same_side_of_line l a p
Proof
  rw[same_side_of_line_def,opposite_side_of_line_def,line_intersects_segment_def,
     interior_of_segment_def,extremity_of_segment_def,set_elements_lemma]
  >> metis_tac[between_implies_distinct_collinear,ALL_DISTINCT,MEM]
QED

Theorem same_opposite_side_line_lemma:
  same_side_of_line l a p ∧ opposite_side_of_line l b a ⇒ opposite_side_of_line l b p
Proof
  rw[same_side_of_line_def,opposite_side_of_line_def] >- simp[]
  >> ‘{a;b} = {b;a} ∧ {p;b} = {b;p} ∧ {p;a} = {a;p}’ by simp[SET_EQ_SUBSET]
  >> Cases_on ‘collinear {b;a;p}’
  >- metis_tac[line_intersects_between_lemma]
  >> metis_tac[line_enters_must_exit_triangle]
QED

Theorem opposite_implies_same_side_line_lemma:
  opposite_side_of_line l b a ∧ opposite_side_of_line l a x ⇒ same_side_of_line l b x
Proof
  rw[same_side_of_line_def,opposite_side_of_line_def]
  >> Cases_on ‘x = b’ >- simp[] >> DISJ2_TAC
  >> ‘{x;a} = {a;x} ∧ {x;b} = {b;x}’ by simp[SET_EQ_SUBSET]
  >> reverse $ Cases_on ‘collinear {a;b;x}’
  >- (reverse $ Cases_on ‘line_intersects_segment l {x;b}’ >- simp[]
      >> metis_tac[line_enters_must_exit_triangle])
  >> metis_tac[not_line_intersects_lemma]
QED

(* Lemmas for two regions of line theorem *)
Theorem two_regions_disjoint_lemma:
  opposite_side_of_line l b a ⇒ DISJOINT {p | same_side_of_line l a p} {p | same_side_of_line l b p}
Proof
  rw[DISJOINT_ALT] >> metis_tac[opposite_implies_not_same_side_of_line,same_opposite_side_line_lemma]
QED

Theorem two_regions_univ_lemma:
  opposite_side_of_line l b a
  ⇒ {p | same_side_of_line l a p} ∪ {p | same_side_of_line l b p} ∪ {p | p ol l} = UNIV
Proof
  gs[EXTENSION] >> rpt strip_tac
  >> Cases_on ‘x ol l’ >> simp[] >> drule opposite_implies_not_same_side_of_line >> strip_tac
  >> Cases_on ‘same_side_of_line l a x’ >> simp[] >> gvs[not_same_side_implies_thm]
  >- gvs[opposite_side_of_line_def] >> Cases_on ‘a = b’ >- gvs[]
  >> metis_tac[opposite_implies_same_side_line_lemma]
QED

Theorem two_points_in_same_region_lemma:
  ∀a' b' . same_side_of_line l a a' ∧ same_side_of_line l a b'
           ⇒ ¬line_intersects_segment l {a'; b'} ∨ a' = b'
Proof
  simp[] >> metis_tac[same_side_of_line_transitive,same_side_of_line_def]
QED

Theorem two_points_in_diff_region_lemma:
   opposite_side_of_line l b a ⇒ ∀a' b' . same_side_of_line l a a' ∧ same_side_of_line l b b'
                                          ⇒ line_intersects_segment l {a';b'}
Proof
  rw[opposite_side_of_line_def,same_side_of_line_def] >- simp[]
  >- (reverse $ Cases_on ‘collinear {a;b;b'}’
      >- (‘{b';b} = {b;b'}’ by simp[SET_EQ_SUBSET] >> metis_tac[line_enters_must_exit_triangle])
      >- metis_tac[line_intersects_between_lemma])
  >- (‘{a;b} = {b;a} ∧ {a';a} = {a;a'} ∧ {a';b} = {b;a'}’ by simp[SET_EQ_SUBSET]
      >> reverse $ Cases_on ‘collinear {a;b;a'}’
      >- metis_tac[line_enters_must_exit_triangle]
      >> metis_tac[line_intersects_between_lemma])
  >- metis_tac[four_points_intersects_lemma]
QED

(* Every straight line l, divides the remaining points not on the line into two regions having the following properties: Every point A of the one region determines with each point B of the other region a segment AB containing a point of the line l. On the other hand, any two points A' of the same region determine a segment AA' containing no point of l. *)
Theorem two_regions_of_line_thm:
  ∀l . ∃A B . DISJOINT A B ∧ A ∪ B ∪ {p | on_line p l} = UNIV
                                          ∧ (∀a b . a ∈ A ∧ b ∈ B ⇒  line_intersects_segment l {a;b})
                                          ∧ (∀a b . a ∈ A ∧ b ∈ A ⇒  ¬line_intersects_segment l {a;b} ∨ a = b)
                                          ∧ (∀a b . a ∈ B ∧ b ∈ B ⇒  ¬line_intersects_segment l {a;b} ∨ a = b)
Proof
  gen_tac
  >> ‘∃a b . opposite_side_of_line l b a’ by metis_tac[points_opposite_line_exist]
  >> ‘∃A B . A = {p | same_side_of_line l a p} ∧ B = {p | same_side_of_line l b p}’ by metis_tac[]
  >> qexistsl [‘A’,‘B’]
  >> simp[] >> rpt strip_tac
  >- metis_tac[two_regions_disjoint_lemma]
  >> metis_tac[two_regions_disjoint_lemma,two_regions_univ_lemma,
               two_points_in_same_region_lemma,two_points_in_diff_region_lemma]
QED

Theorem two_regions_thm:
  ∀l a b . ¬on_line a l ∧ ¬on_line b l ⇒ opposite_side_of_line l b a ∨ same_side_of_line l b a
Proof
  metis_tac[same_side_of_line_def, opposite_side_of_line_def]
QED

(* Sides of a point definitions *)
Definition same_side_of_point_def:
  same_side_of_point p b a ⇔ p ≠ a ∧ p ≠ b ∧ collinear {p;a;b} ∧ ((a = b) ∨ ¬between p a b)
End

Theorem same_side_of_point_irreflexive[simp]:
  ¬same_side_of_point y y x ∧ ¬same_side_of_point y x y
Proof
  simp[same_side_of_point_def]
QED

Theorem one_same_side_of_point:
  a ≠ p ⇒ same_side_of_point p a a
Proof
  simp[same_side_of_point_def, collinear_def] >> metis_tac[line_exists]
QED

(* Ray definition *)
Type ray = “:point -> bool”;

Definition ray_def:
  ray x a = {p | same_side_of_point x a p}
End

Definition is_ray_def:
  is_ray (r : ray) ⇔ ∃x a . r = ray x a ∧ x ≠ a
End

Theorem ray_non_empty[simp]:
  ray x a = ∅ ⇔ a = x
Proof
  simp[ray_def] >> iff_tac
  >- (simp[EXTENSION, same_side_of_point_def] >> strip_tac >> pop_assum (qspec_then ‘a’ strip_assume_tac) >> gvs[])
  >> simp[]
QED

Theorem same_side_of_point_symm:
  same_side_of_point p b a ⇔ same_side_of_point p a b
Proof
  iff_tac >> simp[same_side_of_point_def] >> ‘{p;a;b} = {p;b;a}’ by simp[SET_EQ_SUBSET] >> metis_tac[between_symm]
QED

Theorem same_side_of_point_transitive:
  same_side_of_point b c p ∧ same_side_of_point b c d ⇒ same_side_of_point b d p
Proof
  rw[same_side_of_point_def]
  >> simp[]
  >- (‘{b;d;c} = {b;c;d}’ by simp[SET_EQ_SUBSET] >> metis_tac[])
  >- metis_tac[between_symm]
  >- metis_tac[collinear_line,on_line_thm,on_line_implies_collinear_thm]
  >> Cases_on ‘p = d’ >- simp[] >> DISJ2_TAC
  >> reverse $ Cases_on ‘between b p d’ >- simp[]
  >> ‘{b;p;c} = {b;c;p} ∧ {b;d;c} = {b;c;d}’ by simp[SET_EQ_SUBSET]
  >> ‘collinear {b;c;p} ∧ collinear {b;c;d}’ by metis_tac[]
  >> ‘b ol (line b c) ∧ c ol (line b c) ∧ d ol (line b c) ∧ p ol (line b c)’ by metis_tac[between_symm,collinear_line,on_line_thm]
  >> ‘between b p c ∨ between b d c’ by metis_tac[between_implies_property,between_symm]
QED

Theorem in_ray_implies_collinear:
  b ∈ ray x a ⇒ collinear {a;b;x} ∧ same_side_of_point x b a
Proof
  rw[ray_def] >- (gvs[same_side_of_point_def] >> ‘{a;b;x} = {x;b;a}’ suffices_by metis_tac[] >> simp[SET_EQ_SUBSET])
  >> metis_tac[same_side_of_point_symm]
QED

Theorem ray_excludes_base:
  x ∉ ray x a
Proof
  simp[ray_def, same_side_of_point_def]
QED

Theorem ray_includes_initial_point:
  x ≠ a ⇒ a ∈ ray x a
Proof
  strip_tac >> ‘same_side_of_point x a a’ by simp[same_side_of_point_def] >> simp[ray_def]
QED

Theorem in_ray_condition:
  same_side_of_point x b a ⇒ a ∈ ray x b
Proof
  simp[ray_def]
QED

Theorem point_in_ray:
  x ∈ ray b c ⇒ same_side_of_point b c x
Proof
  rw[ray_def]
QED

Theorem point_not_in_ray:
  x ∉ ray b c ⇒ ¬same_side_of_point b c x
Proof
  rw[ray_def]
QED

Theorem equal_rays_by_ref_point:
  d ∈ ray b c ⇒ ray b d = ray b c
Proof
  strip_tac >> ‘same_side_of_point b d c’ by metis_tac[in_ray_implies_collinear]
  >> ‘same_side_of_point b c d’ by metis_tac[same_side_of_point_symm]
  >> ‘ray b c = {p | same_side_of_point b c p} ∧ ray b d = {p | same_side_of_point b d p}’ by simp[ray_def]
  >> ‘∀p. p ∈ ray b c ⇒ p ∈ ray b d’ by (rpt strip_tac >> ‘same_side_of_point b c p’ by metis_tac[point_in_ray]
                                         >> ‘same_side_of_point b d p’ by metis_tac[same_side_of_point_transitive]
                                         >> ‘p ∈ ray b d’ by simp[ray_def])
  >> ‘ray b c ⊆ ray b d’ by simp[SUBSET_DEF]
  >> ‘∀p. p ∈ ray b d ⇒ p ∈ ray b c’ by (rpt strip_tac >> ‘same_side_of_point b d p’ by metis_tac[point_in_ray]
                                         >> ‘same_side_of_point b c p’ by metis_tac[same_side_of_point_transitive]
                                         >> ‘p ∈ ray b c’ by simp[ray_def])
  >> ‘ray b d ⊆ ray b c’ by simp[SUBSET_DEF]
  >> metis_tac[SET_EQ_SUBSET]
QED

Definition line_of_ray:
  line_of_ray r = @l . ∃a x . r = ray x a ∧ l = line a x
End

Theorem equal_rays_line_thm:
  ray x a = ray y b ∧ x ≠ a ∧ y ≠ b ⇒ line x a = line y b
Proof
  strip_tac >> ‘a ol (line x a) ∧ b ol (line y b)’ by metis_tac[on_line_thm]
  >> ‘a ∈ ray x a ∧ b ∈ ray y b’ by metis_tac[ray_includes_initial_point] >> ‘a ∈ ray y b ∧ b ∈ ray x a’ by metis_tac[]
  >> ‘collinear {b;a;y} ∧ collinear {a;b;x}’ by metis_tac[in_ray_implies_collinear]
  >> ‘{b;a;y} = {y;b;a} ∧ {a;b;x} = {x;a;b}’ by simp[SET_EQ_SUBSET] >> ‘collinear {y;b;a} ∧ collinear {x;a;b}’ by metis_tac[]
  >> ‘a ol (line y b) ∧ b ol (line x a)’ by metis_tac[collinear_line]
  >> Cases_on ‘line x a = line y b’ >- simp[]
  >> reverse $ Cases_on ‘a = b’
  >> ‘(¬∃p . p ol (line x a) ∧ p ol (line y b)) ∨ (∃!p . p ol (line x a) ∧ p ol (line y b))’ by metis_tac[two_lines_thm]
  >- metis_tac[] >- metis_tac[] >- metis_tac[]
  >> ‘∃c . between c x a’ by metis_tac[between_exists]
  >> ‘c ≠ a ∧ c ≠ x ∧ collinear {x;c;a}’ by metis_tac[between_implies_distinct_collinear,ALL_DISTINCT, MEM]
  >> ‘¬between x c a’ by metis_tac[one_between] >> ‘same_side_of_point x a c’ by metis_tac[same_side_of_point_def]
  >> ‘c ∈ ray x a’ by simp[in_ray_condition] >> ‘c ∈ ray y b’ by metis_tac[]
  >> ‘collinear {b;c;y}’ by metis_tac[in_ray_implies_collinear]
  >> ‘{x;c;a} = {x;a;c} ∧ {b;c;y} = {y;b;c}’ by simp[SET_EQ_SUBSET] >> ‘collinear {x;a;c} ∧ collinear {y;b;c}’ by metis_tac[]
  >> ‘c ol (line x a) ∧ c ol (line y b)’ by metis_tac[collinear_line] >> metis_tac[]
QED

Theorem four_points_between':
  ALL_DISTINCT [a;b;x;y] ∧  collinear {a;b;x;y} ∧ ¬BT x a b ∧ ¬BT y b a ∧ BT y x b ∧ BT x y a ⇒ F
Proof
  strip_tac >>
  drule_all four_points_arranged >> simp[EXTENSION] >> rpt strip_tac
  >> map_every (fn q => first_assum (qspec_then q mp_tac) >> rewrite_tac[] >> strip_tac >> gvs[]) [‘a’,‘b’,‘x’, ‘y’]
  >> metis_tac[one_between, between_symm]
QED

Theorem equal_rays_bases_thm:
  ray x a = ray y b ∧ x ≠ a ∧ y ≠ b ⇒ x = y
Proof
  strip_tac >> ‘x ∉ ray x a ∧ y ∉ ray y b’ by metis_tac[ray_excludes_base]
  >> ‘a ∈ ray x a ∧ b ∈ ray y b’ by metis_tac[ray_includes_initial_point] >> ‘a ∈ ray y b ∧ b ∈ ray x a’ by metis_tac[]
  >> ‘line x a = line y b’ by metis_tac[equal_rays_line_thm]
  >> imp_res_tac in_ray_implies_collinear
  >> Cases_on ‘x = y’ >- simp[]
  >> Cases_on ‘a = b’
  >- (‘x ol (line x a) ∧ a ol (line x a) ∧ y ol (line y b)’ by metis_tac[on_line_thm] >> ‘y ol (line x a)’ by metis_tac[]
      >> reverse $ Cases_on ‘between x y a’
      >- (‘same_side_of_point x a y’ by metis_tac[same_side_of_point_def,on_line_implies_collinear_thm]
          >> ‘y ∈ ray x a’ by simp[in_ray_condition] >> metis_tac[NOT_EQUAL_SETS])
      >> ‘¬between y x b’ by metis_tac[one_between,between_symm]
      >> ‘same_side_of_point y b x’ by metis_tac[same_side_of_point_def,on_line_implies_collinear_thm]
      >> ‘x ∈ ray y b’ by simp[in_ray_condition] >> metis_tac[NOT_EQUAL_SETS])
  >> ‘x ol (line a b) ∧ y ol (line a b) ∧ a ol (line a b) ∧ b ol (line a b)’ by metis_tac[collinear_line,on_line_thm,line_symm]
  >> Cases_on ‘x = b’ >- metis_tac[]
  >> Cases_on ‘y = a’ >- metis_tac[]
  >> ‘ALL_DISTINCT [a;b;x;y]’ by metis_tac[ALL_DISTINCT, MEM]
  >> ‘collinear {a;b;x;y}’ by (simp[collinear_def] >> qexists ‘line a b’ >> metis_tac[])
  >> ‘¬between x a b ∧ ¬between y b a’ by metis_tac[same_side_of_point_def]
  >> ‘collinear {y;x;b} ∧ collinear {x;y;a}’ by (gvs[collinear_def] >> metis_tac[collinear_def])
  >> ‘between y x b ∧ between x y a’ by metis_tac[point_not_in_ray,same_side_of_point_def]
  >> metis_tac[four_points_between']
QED

Theorem point_not_between_points_on_ray_thm:
  d ∈ ray b c ∧ ¬(c ∊ line a b) ∧ c ≠ d ∧ p ∊ line a b ∧ {d; c} = {a'; b'} ⇒ ¬between p a' b'
Proof
  rw[set_elements_lemma,ray_def,same_side_of_point_def]
  >> reverse $ Cases_on ‘between p a' b'’ >> simp[]
  >> ‘line a b ≠ line a' b'’ by metis_tac[on_line_thm]
  >> ‘{b;a';b'} = {a';b';b} ∧ {b;b';a'} = {a';b';b}’ by simp[SET_EQ_SUBSET]
  >> ‘p ol (line a' b') ∧ b ol (line a' b')’ by metis_tac[between_implies_on_line,collinear_line]
  >> metis_tac[unique_line,on_line_thm,between_symm]
QED

Theorem collinear_implies_lies_on_unique_line:
  b ≠ d ∧ b ≠ c ∧ c ≠ d ∧ collinear {b;d;c} ∧ b ol l ∧ d ol l ⇒ c ol l
Proof
  strip_tac >> ‘l = line b d’ by metis_tac[line_unique,on_line_thm] >> metis_tac[collinear_line]
QED

Theorem point_not_equal_different_lines_thm:
  d ∈ ray b c ∧ ¬(c ∊ line a b) ∧ c ≠ d ∧ p ∊ line a b ⇒ p ≠ d
Proof
  rw[ray_def,same_side_of_point_def] >> reverse $ Cases_on ‘p = d’ >> simp[]
  >> ‘d ol (line a b) ∧ b ol (line a b)’ by metis_tac[on_line_thm] >> metis_tac[collinear_implies_lies_on_unique_line]
QED

Theorem in_ray_implies_same_side_of_line_thm:
  d ∈ ray b c ∧ ¬(c ol (line a b)) ⇒ same_side_of_line (line a b) c d
Proof
  rw[same_side_of_line_def]
  >- ( ‘{c;d;b} = {b;c;d}’ by simp[SET_EQ_SUBSET]
       >> ‘collinear {b;c;d}’ by metis_tac[in_ray_implies_collinear]
       >> Cases_on ‘b = c’ >- (‘ray b c = ∅’ by simp[] >> metis_tac[NOT_IN_EMPTY])
       >> ‘d ol (line b c)’ by metis_tac[collinear_line] >> ‘b ∉ ray b c’ by metis_tac[ray_excludes_base]
       >> ‘b ≠ d’ by metis_tac[]
       >> reverse $ Cases_on ‘d ol (line a b)’ >- simp[]
       >> ‘b ol (line a b) ∧ b ol (line b c) ∧ c ol (line b c)’ by metis_tac[on_line_thm]
       >> ‘line a b ≠ line b c’ by metis_tac[] >> metis_tac[line_unique])
  >> Cases_on ‘c = d’ >- simp[] >> DISJ2_TAC
  >> rw[line_intersects_segment_def]
  >> reverse $ Cases_on ‘p ol (line a b)’ >- simp[] >> DISJ2_TAC
  >> rw[interior_of_segment_def,extremity_of_segment_def]
  >- metis_tac[point_not_between_points_on_ray_thm]
  >> Cases_on ‘a' = b'’ >- simp[] >> DISJ2_TAC
  >> ‘p ≠ c’ by metis_tac[] >> ‘p ≠ d’ by metis_tac[point_not_equal_different_lines_thm]
  >> ‘p ∉ {d;c}’ by simp[EXTENSION] >> ‘p ∉ {a';b'}’ by metis_tac[]
  >> Cases_on ‘p = a'’ >- ‘p ∈ {a';b'}’ by metis_tac[IN_INSERT]
  >> Cases_on ‘p = b'’ >- ‘p ∈ {a';b'}’ by metis_tac[IN_INSERT]
  >> simp[]
QED

(* A system of segments AB, BC, CD, ..., KL is called a broken line joining A with L and is designated as the broken line ABCDE...KL. *)
Definition seg_in_bl_def:
  seg_in_bl s bl ⇔ ∃a b . s = {a;b} ∧ a ≠ b ∧ adjacent bl a b
End

Definition point_of_bl_def:
  point_of_bl a bl ⇔ MEM a bl ∨ ∃s . seg_in_bl s bl ∧ interior_of_segment a s
End

(* Polygon types *)
Type polygon = “:point list”

(* If the point A coincides with L, the broken line is called a polygon and is designated as the polygon ABCD...K. *)
Definition bl_is_polygon_def:
  bl_is_polygon (bl : point list) ⇔ HD bl = LAST bl
End

Definition is_polygon_def:
  is_polygon (p : polygon) ⇔ ALL_DISTINCT p ∧ LENGTH p >= 3
End

Definition polygon_to_bl_def:
  polygon_to_bl (p : polygon) = APPEND p [HD p]
End

(* The segments AB, BC, CD,..., KA are called the sides of the polygon ABC...K *)
Definition is_side_of_polygon_def:
  is_side_of_polygon (s : segment) (p : polygon) ⇔ is_polygon p ∧ ∃a b . s = {a;b} ∧ a ≠ b ∧ (adjacent p a b ∨ (a = HD p ∧ b = LAST p))
End

Definition sides_of_polygon_def:
  sides_of_polygon p = {s | is_side_of_polygon s p}
End

Theorem sides_of_triangle_thm:
  ∀a b c . is_polygon [a;b;c] ⇒ {{a;b};{b;c};{c;a}} ⊆ sides_of_polygon [a;b;c]
Proof
  rpt strip_tac >> ‘a ≠ b ∧ b ≠ c ∧ c ≠ a’ by metis_tac[is_polygon_def, ALL_DISTINCT, MEM]
  >> ‘adjacent [a;b;c] a b ∧ adjacent [a;b;c] b c’ by simp[adjacent_EL,adjacent_iff]
  >> ‘a = HD [a;b;c] ∧ c = LAST [a;b;c] ∧ {a;c} = {c;a}’ by simp[HD,LAST_DEF,SET_EQ_SUBSET]
  >> ‘is_side_of_polygon {a;b} [a;b;c] ∧ is_side_of_polygon {b;c} [a;b;c] ∧ is_side_of_polygon {c;a} [a;b;c]’
    by metis_tac[is_side_of_polygon_def,SET_EQ_SUBSET]
  >> simp[sides_of_polygon_def,SUBSET_DEF]
QED

(* The points A, B, C, D,..., K are called the vertices *)
Overload is_vertex_of_polygon = “λp:point ps . MEM p ps”

Definition point_of_polygon_def:
  point_of_polygon a p ⇔ is_vertex_of_polygon a p ∨ ∃s . is_side_of_polygon s p ∧ interior_of_segment a s
End

Definition points_belonging_to_polygon_def:
  points_belonging_to_polygon p = {x | point_of_polygon x p}
End

(* If the vertices of a polygon are all distinct and none of them lie within the segments composing the sides of the polygon, and, furthermore, if no two sides have a point in common, then the polygon is called a simple polygon. *)
Definition is_simple_polygon_def:
  is_simple_polygon (p : polygon) ⇔
    is_polygon p ∧
    (∀a s . is_vertex_of_polygon a p ∧ is_side_of_polygon s p ⇒ ¬interior_of_segment a s) ∧
    (∀s r. s ≠ r ∧ is_side_of_polygon s p ∧ is_side_of_polygon r p ⇒ ¬segments_intersect s r)
End

Theorem between_three_lemma:
  ∀a b c l . a ol l ∧ b ol l ∧ c ol l ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a ⇒ between a b c ∨ between b c a ∨ between c a b
Proof
  rpt strip_tac >> ‘collinear {a;b;c}’ by metis_tac[collinear_def, IN_INSERT, NOT_IN_EMPTY] >> drule exactly_one_between >> simp[only_one_def, EXISTS_UNIQUE_THM] >> strip_tac >> ‘i = 0 ∨ i = 1 ∨ i = 2’ by simp[] >> gvs[]
QED

Theorem is_triangle_thm:
  ∀a b c . is_simple_polygon [a;b;c] ⇒ ¬collinear {a;b;c}
Proof
  rw[is_simple_polygon_def, is_side_of_polygon_def] >> simp[collinear_def] >> strip_tac
  >> reverse $ Cases_on ‘a ol l’ >- metis_tac[]
  >> reverse $ Cases_on ‘b ol l’ >- metis_tac[]
  >> qexists ‘c’ >> simp[] >> strip_tac
  >> ‘between a b c ∨ between b c a ∨ between c a b’ by metis_tac[between_three_lemma,is_polygon_def,ALL_DISTINCT,MEM]
  >- (first_x_assum (qspecl_then [‘a’, ‘{b;c}’] mp_tac) >> simp[] >> strip_tac
      >- (qexistsl [‘b’,‘c’] >> simp[adjacent_iff] >> metis_tac[between_implies_distinct_collinear,ALL_DISTINCT,MEM])
      >> simp[interior_of_segment_def] >> qexistsl [‘b’,‘c’] >> simp[]
      >> ‘b ≠ c’ by metis_tac[between_implies_distinct_collinear,ALL_DISTINCT,MEM] >> metis_tac[three_points_on_same_line])
  >- (‘interior_of_segment b {c;a}’ by metis_tac[between_implies_interior]
      >> first_x_assum (qspecl_then [‘b’, ‘{c;a}’] mp_tac)
      >> simp[] >> qexistsl [‘a’,‘c’] >> simp[SET_EQ_SUBSET]
      >> metis_tac[between_implies_distinct_collinear,ALL_DISTINCT,MEM])
  >- (‘interior_of_segment c {a;b}’ by metis_tac[between_implies_interior]
      >> simp[] >> first_x_assum (qspecl_then [‘c’, ‘{a;b}’] mp_tac)
      >> simp[] >> qexistsl [‘a’,‘b’] >> simp[]
      >> metis_tac[between_implies_distinct_collinear,ALL_DISTINCT,MEM])
QED

(* Future work *)
(* Idea to prove the general theorem is to induct with base case on triangle *)
(* Theorem polygon_not_collinear_thm:
  ∀p . is_simple_polygon p ⇒ ¬collinear (set p)
Proof
  cheat
QED *)

Definition line_intersects_polygon_def:
  line_intersects_polygon l p ⇔ ∃a . point_of_polygon a p ∧ a ol l
End

Definition bl_intersects_polygon_def:
  bl_intersects_polygon bl p ⇔ ∃a . point_of_bl a bl ∧ point_of_polygon a p
End

Definition bl_joins_points_def:
  bl_joins_points bl a b ⇔ HD bl = a ∧ LAST bl = b ∨ HD bl = b ∧ LAST bl = a
End

(* Future work *)
(* Every simple polygon divides the points not belonging to the broken line constituting the sides of the polygon into two regions, an interior and an exterior with the following properties: If A and B are interior and exterior, then any broken line joining A and B must have at least one point in common with the polygon. If A and B are either both interior or both exterior then there exists a broken line joining A with B that does not have a point in common with the polygon. *)
(* Theorem int_ext_of_polygon_thm:
  ∀p . is_simple_polygon p ⇒ ∃A B . DISJOINT A B ∧ A ∪ B ∪ point_belongs_to_polygon p = UNIV
                                    ∧ (∀a b . a ∈ A ∧ b ∈ A ⇒ ∃bl . bl_joins_points bl a b ∧ ¬bl_intersects_polygon bl p)
                                    ∧ (∀a b . a ∈ B ∧ b ∈ B ⇒ ∃bl . bl_joins_points bl a b ∧ ¬bl_intersects_polygon bl p)
                                    ∧ (∀a b . a ∈ A ∧ b ∈ B ⇒ ∀bl . bl_joins_points bl a b ⇒ bl_intersects_polygon bl p)
Proof
  rpt strip_tac >> cheat
QED *)

Definition is_convex_polygon_def:
  is_convex_polygon p ⇔ is_simple_polygon p
                        ∧ ∀s r x . s ∈ sides_of_polygon p ∧ r ∈ sides_of_polygon p ∧ s ≠ r
                                   ∧ (interior_of_segment x r ∨ extremity_of_segment x r) ⇒ ¬(x ol (line_of_segment s))
End

(* GROUP 3: AXIOM OF PARALLELS (EUCLID’S AXIOM) *)
Definition parallel_through_point_def:
  parallel_through_point m p l ⇔ on_line p m ∧ (l = m ∨ ¬lines_intersect l m)
End

Definition parallel_def:
  parallel l m ⇔ (¬lines_intersect l m) ∨ (l = m)
End

(* Given any point p, lying outside of a straight line l, there is one and only one straight line which does not intersect the line l. This straight line is called the parallel to l through the given point p. *)
val unique_parallel = new_axiom("unique_parallel",
                                 “∀l p . ∃! m . parallel_through_point m p l”);

(*  If two lines a, b do not meet a third line c, then they do not meet each other. *)
Theorem parallel_transitivity:
  ∀l₁ l₂ l₃ . parallel l₁ l₂ ∧ parallel l₂ l₃ ⇒ parallel l₁ l₃
Proof
  rw[parallel_def] >> simp[] >> Cases_on ‘l₁ = l₃’ >- simp[]
  >> reverse $ Cases_on ‘lines_intersect l₁ l₃’ >- simp[]
  >> ‘∃p . on_line p l₁ ∧ on_line p l₃ ∧ ¬lines_intersect l₂ l₁’ by metis_tac[lines_intersect_def]
  >> ‘parallel_through_point l₃ p l₂ ∧ parallel_through_point l₁ p l₂’ by metis_tac[parallel_through_point_def]
  >> ‘l₁ = l₃’ by metis_tac[unique_parallel]
QED

(* GROUP 4: AXIOMS OF CONGRUENCE *)
val _ = new_constant ("congruent", “:α -> α -> bool”);
val _ = set_mapped_fixity{term_name = "congruent", tok = "≡", fixity = Infix(NONASSOC,450)};

val _ = new_constant ("congruent_triangles", “:point list -> point list -> bool”);
val _ = set_mapped_fixity{term_name = "congruent_triangles", tok = "≅", fixity = Infix(NONASSOC,450)};

(* G4.1.1) Given a segment AB and a ray XC, there exists exactly one point D on XC such that the segment AB is congruent to the segment XD, i.e. AB ≡ XD. *)
val segment_copy = new_axiom(
  "segment_copy",
  “∀a b x c . a ≠ b ∧ x ≠ c ⇒ ∃! d . d ∈ ray x c ∧ congruent {a;b} {x;d}”);

Theorem segment_copy_exists:
  b ≠ c ∧ b' ≠ c' ⇒ ∃d' . d' ol (line b' c') ∧ congruent {b;c} {b';d'}
Proof
  strip_tac >> ‘∃ d . d ∈ ray b' c' ∧ congruent {b;c} {b';d}’ by metis_tac[segment_copy]
  >> ‘collinear {c';d;b'}’ by metis_tac[in_ray_implies_collinear] >> ‘{c';d;b'} = {b';c';d}’ by simp[SET_EQ_SUBSET]
  >> ‘collinear {b';c';d}’ by metis_tac[] >> ‘d ol (line b' c')’ by metis_tac[collinear_line]
  >> qexists ‘d’ >> simp[]
QED

(* G4.1.2) Every segment is congruent to itself; that is, we always have AB ≡ AB *)
val segment_refl = new_axiom("segment_refl", “∀s : segment . is_segment s ∧ congruent s s”);

(* G4.1.3) Two segments are not congruent if they are not equal in measure *)
val segment_not_congruent = new_axiom("segment_not_congruent",
                                      “∀(a : point) (b : point) . a ≠ b ⇒ ¬congruent {a} {a;b}”);


(* G4.2) If segment AB ≡ CD and AB ≡ EF, then CD ≡ EF. *)
val segment_transitivity = new_axiom("segment_transitivity",
                                     “∀s : segment r t . is_segment s ∧ is_segment r ∧ congruent s r ∧ congruent s t
                                                         ⇒ congruent r t”);

Theorem segment_congruence_symm:
  ∀a b : segment. congruent a b ⇔ congruent b a
Proof
  metis_tac[segment_refl, segment_transitivity]
QED

Theorem segment_refl_applied:
  ∀a b . is_segment {a;b} ⇒ congruent {a;b} {a;b}
Proof
  rpt strip_tac >> metis_tac[segment_refl]
QED

(* G4.3) Let AB and BC be two segments of a straight line l which have no points in common aside from the point B and let A'B' and B'C' be two segments of the same or of another straight line l' having, likewise, no point other than B' in common. Then, if AB ≡ A'B' and BC ≡ B'C', we have AC ≡ A'C' *)
val segment_additivity = new_axiom(
  "segment_additivity",
  “∀a b c a' b' c'. a ≠ b ∧ b ≠ c ∧ line_of_segment {a;b} = line_of_segment {b;c} ∧ ¬segments_intersect {a;b} {b;c}
                 ∧  a' ≠ b' ∧ b' ≠ c' ∧ line_of_segment {a';b'} = line_of_segment {b';c'} ∧ ¬segments_intersect {a';b'} {b';c'}
                 ∧ congruent {a;b} {a';b'} ∧ congruent {b;c} {b';c'} ⇒ congruent {a;c} {a'c'}”);

(* Angle definitions *)
Type angle = “:point set # point set”

Definition angle_def:
  angle a b c = (ray b a, ray b c)
End

Definition is_angle_def:
  is_angle (α : angle) ⇔ ∃a b c . α = angle a b c
End

Definition interior_of_angle_def:
  interior_of_angle p x ⇔ ∃a b c . x = angle a b c ∧ same_side_of_line (line b a) c p ∧ same_side_of_line (line b c) a p
End

(* G4.4.1) Given an angle ∠AXB, and a ray X'A', suppose that a definite side of the straight line X'A' is assigned.Then this side contains one and only one ray X'B' such that ∠AXB ≡ ∠A'X'B' and at the same time all interior points of the angle ∠A'X'B' lie upon the given side of line X'A'. *)
val angle_copy = new_axiom(
  "angle_copy",
  “∀a x b x' a' ref . ¬(ref ol (line x' a')) ⇒ ∃!r . ∃b' . r = ray x' b' ∧ same_side_of_line (line x' a') ref b'
                                                              ∧ congruent (angle a x b) (angle  a' x' b')”);

val angle_copy_interior_points = new_axiom(
  "angle_copy_interior_points",
  “∀a x b x' a' ref . ¬on_line ref (line x' a') ⇒ ∃!r . ∃b' . r = ray x' b'
                                    ∧ same_side_of_line (line x' a') ref b'
                                    ∧ congruent (angle a x b) (angle  a' x' b')
                                    ∧ (∀ p . interior_of_angle p (angle a' x' b') ⇒ same_side_of_line (line x' a') ref p)”);

Theorem unique_ray_defines_angle:
  ∀a b c. ¬(c ol (line a b)) ⇒ ∃!r. ∃d. r = ray a d ∧ same_side_of_line (line a b) c d ∧ congruent (angle b a c) (angle b a d)
Proof
  metis_tac[angle_copy]
QED

(* G4.4.2) Every angle is congruent to itself. *)
val angle_refl = new_axiom("angle_refl",
                           “∀a . is_angle a ⇒ congruent a a”);

Theorem angle_copy_lemma:
  ¬collinear {a;b;c} ∧ d ∈ ray b c ∧ congruent (angle b a c) (angle b a d) ⇒ c = d
Proof
  strip_tac >> ‘¬(c ol (line a b))’ by metis_tac[not_collinear_implies_not_on_line]
  >> ‘∃!r . ∃d . r = ray a d ∧ same_side_of_line (line a b) c d
                   ∧ congruent (angle b a c) (angle b a d)’ by metis_tac[angle_copy]
  >> ‘∃r . r = ray a c’ by metis_tac[] >> ‘same_side_of_line (line a b) c c’ by metis_tac[same_side_of_line_def]
  >> ‘is_angle (angle b a c)’ by metis_tac[is_angle_def]
  >> ‘congruent (angle b a c) (angle b a c)’ by metis_tac[angle_refl]
  >> ‘∃r' . r' = ray a d’ by metis_tac[]
  >> ‘same_side_of_line (line a b) c d’ by metis_tac[in_ray_implies_same_side_of_line_thm]
  >> ‘ray a c = ray a d’ by metis_tac[]
  >> ‘a ≠ c ∧ a ≠ d’ by metis_tac[on_line_thm,same_side_of_line_def]
  >> ‘line a c = line a d’ by metis_tac[equal_rays_line_thm]
  >> ‘{c;d;b} = {b;c;d}’ by simp[SET_EQ_SUBSET] >> ‘collinear {b;c;d}’ by metis_tac[in_ray_implies_collinear]
  >> Cases_on ‘c = d’ >- simp[]
  >> Cases_on ‘b = c’ >- (‘ray b c = ∅’ by simp[] >> metis_tac[NOT_IN_EMPTY])
  >> ‘d ol (line b c)’ by metis_tac[collinear_line] >> ‘d ol (line a c)’ by metis_tac[on_line_thm]
  >> ‘{a;c;b} = {a;b;c}’ by simp[SET_EQ_SUBSET] >> ‘¬(b ol (line a c))’ by metis_tac[not_collinear_implies_not_on_line]
  >> ‘b ol (line b c) ∧ c ol (line b c) ∧ c ol (line a c)’ by metis_tac[on_line_thm] >> ‘line b c ≠ line a c’ by metis_tac[]
  >> metis_tac[line_unique]
QED

Theorem applied_angle_refl:
  ∀a b c . is_angle (angle a b c) ⇒ congruent (angle a b c) (angle a b c)
Proof
  rpt strip_tac >> metis_tac[angle_refl]
QED

val angle_symm = new_axiom("angle_symm",
                           “∀x y z . angle z y x = angle x y z”);

(* G4.5) Angle transitivity: If angle a is congruent to angle b and angle c then angle b and c are also congruent. *)
val angle_transitivity = new_axiom("angle_transitivity",
                                   “∀a b c . is_angle a ∧ is_angle b ∧ is_angle c ∧ congruent a b ∧ congruent a c
                                                     ⇒ congruent b c”);

Theorem angle_congruence_symm:
  ∀a b . is_angle a ∧ is_angle b ⇒ (congruent a b ⇔ congruent b a)
Proof
  rpt strip_tac >> metis_tac[angle_refl, angle_transitivity]
QED

Theorem applied_angle_congruence_symm:
  ∀a b c x y z . is_angle (angle a b c) ∧ is_angle (angle x y z)
                 ⇒ (congruent (angle a b c) (angle x y z) ⇔ congruent (angle x y z) (angle a b c))
Proof
  rpt strip_tac >> metis_tac[angle_congruence_symm]
QED

Theorem angle_equal_by_ray:
  d ∈ ray b c ⇒ congruent (angle a b c) (angle a b d)
Proof
  strip_tac
  >> ‘angle a b d = (ray b a, ray b d) ∧ angle a b c = (ray b a, ray b c)’ by simp[angle_def]
  >> ‘ray b d = ray b c’ by metis_tac[equal_rays_by_ref_point]
  >> metis_tac[is_angle_def,applied_angle_refl]
QED

Type triangle = “:point list”

Definition is_nontrivial_triangle_def:
  is_nontrival_triangle t ⇔ is_simple_polygon t ∧ LENGTH t = 3
End

Theorem nontrivial_implies_distinct:
  is_nontrival_triangle t ⇒ ALL_DISTINCT t
Proof
  rw[is_nontrivial_triangle_def] >> metis_tac[is_simple_polygon_def,is_polygon_def]
QED

Definition triangle_def:
  triangle (a : point) (b : point) (c : point) = [a;b;c]
End

Definition is_triangle_def:
  is_triangle (t : triangle) ⇔ ∃a b c . t = triangle a b c
End

Definition sides_of_triangle_def:
  sides_of_triangle (a : point) (b : point) (c : point) = {{a;b};{b;c};{c;a}}
End

Definition angles_of_triangle_def:
  angles_of_triangle (a : point) (b : point) (c : point) = {angle a b c;angle b c a;angle c a b}
End

(* Definition triangle_angle_names: *)
(*   angle b a c = t_angle a ∧ angle a b c = t_angle b ∧ angle a c b = t_angle c *)
(* End *)

(* G4.6) Triangle SAS congruence relation *)
val sas_congruence_relation = new_axiom(
  "sas_congruence_relation",
  “∀a b c a' b' c' . congruent {a;b} {a';b'} ∧ congruent {c;a} {c';a'} ∧ congruent (angle c a b) (angle c' a' b')
                      ⇒ congruent (angle a b c) (angle a' b' c') ∧ congruent (angle b c a) (angle b' c' a')”);

Definition congruent_triangles_def:
  congruent_triangles (t₁ : triangle) (t₂ : triangle)
                      ⇔ ∃ a b c a' b' c' . t₁ = [a;b;c] ∧ t₂ = [a';b';c']
                       ∧ congruent {a;b} {a';b'} ∧ congruent {b;c} {b';c'} ∧ congruent {c;a} {c';a'}
                       ∧ congruent (angle a b c) (angle a' b' c') ∧ congruent (angle b c a) (angle b' c' a')
                       ∧ congruent (angle c a b) (angle c' a' b')
End

Theorem sas_congruence_thm:
  ∀(t₁ : triangle) (t₂ : triangle) . ∃ a b c a' b' c' . t₁ = [a;b;c] ∧ t₂ = [a';b';c']
                                       ∧ is_nontrival_triangle t₁ ∧ is_nontrival_triangle t₂
                                       ∧ congruent {a;b} {a';b'} ∧ congruent {c;a} {c';a'}
                                       ∧ congruent (angle c a b) (angle c' a' b') ⇒ congruent_triangles t₁ t₂
Proof
  rpt strip_tac >> qexistsl [‘a’,‘b’,‘c’,‘a'’,‘b'’,‘c'’] >> strip_tac
  >> ‘congruent (angle a b c) (angle a' b' c')
      ∧ congruent (angle b c a) (angle b' c' a')’ by metis_tac[sas_congruence_relation]
  >> Cases_on ‘congruent {b;c} {b';c'}’ >- metis_tac[congruent_triangles_def]
  >> ‘∃d' . d' ∈ ray b' c' ∧ congruent {b;c} {b';d'}’
    by metis_tac[segment_copy,nontrivial_implies_distinct,ALL_DISTINCT,MEM]
  >> ‘congruent (angle a' b' c') (angle a' b' d')’ by metis_tac[angle_equal_by_ray]
  >> ‘congruent (angle a b c) (angle a' b' d')’ by metis_tac[angle_transitivity,angle_congruence_symm,is_angle_def]
  >> ‘congruent (angle c a b) (angle d' a' b')’ by metis_tac[sas_congruence_relation]
  >> ‘congruent (angle c' a' b') (angle d' a' b')’ by metis_tac[angle_transitivity,is_angle_def]
  >> ‘congruent (angle b' a' c') (angle b' a' d')’ by metis_tac[angle_symm]
  >> ‘¬collinear {a';b';c'}’ by metis_tac[is_triangle_thm,is_nontrivial_triangle_def]
  >> ‘c' = d'’ suffices_by metis_tac[]
  >> metis_tac[angle_copy_lemma]
QED

(* Two angles having the same vertex and one side in common, while the sides not common form a straight line, are called supplementary angles. *)
Definition supplementary_angles_def:
  supplementary_angles α β = ∃a b c d . α = angle a b c ∧ β = angle c b d ∧ collinear {a;b;d}
End

(* Two angles having a common vertex and whose sides form straight lines are called vertical angles *)
Definition vertical_angles_def:
  vertical_angles α β = ∃ a b c d e . α = angle a b c ∧ β = angle d b e ∧ ((collinear {a;b;d} ∧ collinear {c;b;e}) ∨ (collinear {a;b;e} ∧ collinear {c;b;d}))
End

(* An angle which is congruent to its supplementary angle is called a right angle *)
Definition right_angle_def:
  right_angle a ⇔ ∃b . supplementary_angles a b ∧ congruent a b
End

(* Circle definition: If M is an arbitrary point, the totality of all points A, for which the segments MA are congruent to one another, is called a circle. M is called the centre of the circle*)
Definition circle_def:
  circle (m : point) (a : point) = {a' | congruent {m;a} {m;a'}}
End

Definition is_circle_def:
  is_circle c ⇔ ∃m a . c = circle m a ∧ m ≠ a
End

(* From this definition can be easily deduced, with the help of the axioms of groups III and IV, the known properties of the circle; in particular, the possibility of constructing a circle through any three points not lying in a straight line, as also the congruence of all angles inscribed in the same segment of a circle, and the theorem relating to the angles of an inscribed quadrilateral. *)

(* Circle theorem singleton set *)
Theorem circle_non_trivial[simp]:
  circle m a = {m} ⇔ a = m
Proof
  simp[circle_def] >> iff_tac
  >- (simp[EXTENSION] >> strip_tac >> pop_assum (qspec_then ‘a’ strip_assume_tac) >> metis_tac[segment_refl])
  >> strip_tac >> simp[EXTENSION] >> strip_tac >> iff_tac >- (strip_tac >- metis_tac[segment_not_congruent])
  >> strip_tac >> ‘{m} = {m;x}’ by simp[SET_EQ_SUBSET] >> metis_tac[segment_refl]
QED

(* Future work *)
(* Circle theorems require two right angles are congruent and the sum of interior angles of a triangle is two right angles. *)
(* Theorem all_triangles_cyclic: *)
(*   ∀a b c . ¬collinear {a;b;c} ⇒ ∃w . is_circle w ∧ a ∈ w ∧ b ∈ w ∧ c ∈ w *)
(* Proof *)
(*   cheat *)
(* QED *)

val _ = export_theory();
