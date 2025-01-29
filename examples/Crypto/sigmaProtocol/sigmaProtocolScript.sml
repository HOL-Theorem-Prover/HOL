
(* ------------------------------------------------------------------------- *)
(* Theory: Sigma Protocol                                                    *)
(*                                                                           *)
(* This theory defines and proves properties of Sigma protocols and their    *)
(* combiners.                                                                *)
(* The key components are:                                                   *)
(*                                                                           *)
(* - Abstract Sigma Protocol definition with Statements, Witnesses,          *)
(*   Relation, Commitments, Challenges, and other core functionality         *)
(*                                                                           *)
(* - Protocol Combiners:                                                     *)
(*   - OR combiner for proving knowledge of one of two statements            *)
(*   - AND combiner for proving knowledge of both statements                 *)
(*   - Equality combiner for proving same witness works for two statements   *)
(*                                                                           *)
(* - Properties proven for protocols and combiners:                          *)
(*   - Well-formedness                                                       *)
(*   - Completeness                                                          *)
(*   - Special Soundness                                                     *)
(*   - Simulator Correctness                                                 *)
(*   - Honest Verifier Zero-Knowledge                                        *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

(* Import External Theories *)
open HolKernel boolLib bossLib Parse;
open jcLib;
open ringTheory;
open groupTheory;
open arithmeticTheory;


(* Declare new theory at start *)
val _ = new_theory "sigmaProtocol";

(* Define a symbol for Field sum operation *)
Overload "⊕" = “(GF q).sum.op”;
val _ = set_fixity "⊕" (Infixl 500);

(* Define a symbol for Field subtraction operation *)
Overload "⊖" = “ring_sub (GF q)”;
val _ = set_fixity "⊖" (Infixl 500);

(* Define a symbol for Field multiplication operation *)
Overload "⊗" = “(GF q).prod.op”;
val _ = set_fixity "⊗" (Infixl 600);

(* Define a symbol for Field division operation *)
Overload "⊘" = “field_div (GF q)”;
val _ = set_fixity "⊘" (Infixl 600);


(* Definition of the cross poduct of the groups *)
Definition Gcross_def:
  Gcross g1 g2 = <| carrier:= g1.carrier × g2.carrier;
                    id:= (g1.id, g2.id);
                    op:= λ (a,b) (c,d). (g1.op a c, g2.op b d);
                 |>
End


(* Cross product of Abelian groups is an Abelian group *)
val Gcross_group_thm = store_thm(
  "Gcross_group_thm",
  “AbelianGroup g1 ∧ AbelianGroup g2 ⇒ AbelianGroup (Gcross g1 g2)”,
  rw[] >>
  simp[AbelianGroup_def, group_def_alt, Group_def, Gcross_def, pairTheory.FORALL_PROD] >>
  rpt (strip_tac >>
       gvs[AbelianGroup_def, group_op_element]) >>
  rpt (metis_tac[AbelianGroup_def, group_assoc]) >>
  (‘(∀x1. x1 ∈ g1.carrier ⇒ ∃y1. y1 ∈ g1.carrier ∧ g1.op y1 x1 = g1.id) ∧
    (∀x2. x2 ∈ g2.carrier ⇒ ∃y2. y2 ∈ g2.carrier ∧ g2.op y2 x2 = g2.id)’ by metis_tac[AbelianGroup_def, group_def_alt] >>
   ‘(∃y1. y1 ∈ g1.carrier ∧ g1.op y1 p_1 = g1.id) ∧
    (∃y2. y2 ∈ g2.carrier ∧ g2.op y2 p_2 = g2.id)’ by metis_tac[AbelianGroup_def, group_def_alt] >>
   qabbrev_tac‘y = (y1, y2)’ >>
   ‘(λ(a,b) (c,d). (g1.op a c,g2.op b d)) (y1, y2) (p_1,p_2) = ((g1.op y1 p_1) , (g2.op y2 p_2))’ by rw[] >>
   ‘((g1.op y1 p_1) , (g2.op y2 p_2)) = (g1.id,g2.id)’ by metis_tac[pairTheory.PAIR] >>
   qexists_tac ‘y’ >>
   ‘FST y ∈ g1.carrier ∧ SND y ∈ g2.carrier’ by rw[pairTheory.PAIR, Abbr‘y’] >>
   metis_tac[]));


(* Definition of an Abstract Sigma Protocol -
   a three-move interactive system where the Prover convinces the Verifier of knowledge
   of a secret (witness) for some statement, while not revealing (zero-knowledge) anything else about the secret *)
Datatype: SigmaProtocol = <|

            (* Set of all possible statements that can be proven *)
            Statements: 's set;

            (* Set of all possible witnesses - secret values that prove the statements *)
            Witnesses: 'w set;

            (* Binary relation defining which witnesses prove which statements
       Returns true if witness w proves statement s *)
            Relation: 's -> 'w -> bool;

            (* Set of random values used by the prover to maintain zero-knowledge property *)
            RandomCoins: 'r set;

            (* Set of all possible first messages (commitments to the witness) from prover to verifier.
    Maintain binding property *)
            Commitments: 'c set;

            (* Algebraic group of all possible challenge values sent by verifier to prover.
    Typically this is a finite cyclic group *)
            Challenges: 'e group;

            (* Binary relation defining when two challenges are considered distinct
       Used in the special soundness property *)
            Disjoint: 'e -> 'e -> bool;

            (* Set of all possible responses from prover to verifier's challenge *)
            Responses: 't set;

            (* First prover algorithm that generates the initial commitment
       Takes statement s, witness w, and random coins r
       The witness is needed to ensure the commitment is properly bound to the proof *)
            Prover_0: 's -> 'w -> 'r -> 'c;

            (* Second prover algorithm that generates the response to the challenge
       Takes statement s, witness w, random coins r, commitment c, and challenge e *)
            Prover_1: 's -> 'w -> 'r -> 'c -> 'e -> 't;

            (* Verifier algorithm that checks if a proof transcript is valid
       Takes a tuple of (statement, commitment, challenge, response)
       Returns true if the proof is accepted *)
            HonestVerifier: ('s # 'c # 'e # 't) -> bool;

            (* Knowledge extractor that can compute a valid witness given two accepting transcripts
       with the same commitment but different challenges
       This ensures proof of knowledge property *)
            Extractor: 't -> 't -> 'e -> 'e -> 'w;

            (* Simulator that can generate valid-looking transcripts without knowing the witness
       This ensures zero-knowledge property *)
            Simulator: 's -> 't -> 'e -> ('s # 'c # 'e # 't);

            (* Maps witness and randomness to simulated response
       Used to show equivalence between real and simulated proofs *)
            SimulatorMap: 's -> 'w -> 'e -> 'r -> 't;

            (* Inverse of SimulatorMap - recovers randomness from simulated response
       Used to show simulator is perfect *)
            SimulatorMapInverse: 's -> 'w -> 'e -> 't -> 'r;
          |>
End


(* Helper definition of the Difference Operation between two challenges in the challenge group
   Used to ensure challenge consistency in the OR composition of the protocol *)
Definition SP_csub_def:
  SP_csub sp a b = sp.Challenges.op a (sp.Challenges.inv b)
End


(* OR composition of a sigma protocol that allows proving knowledge of a witness
   for at least one of two statements without revealing which one *)
Definition SP_or_def:
  SP_or sp = <|
    (* Statement pairs - prover will prove knowledge for at least one *)
    Statements:= sp.Statements × sp.Statements;

    (* Witness type remains the same - only need witness for one statement *)
    Witnesses:= sp.Witnesses;

    (* New relation - satisfied if witness proves either statement *)
    Relation:= (λ (s1, s2) w. sp.Relation s1 w ∨ sp.Relation s2 w);

    (* Random coins now include:
       - Original random coins for real proof
       - Response for simulated proof
       - Challenge for simulated proof *)
    RandomCoins:= ((sp.RandomCoins × sp.Responses) × sp.Challenges.carrier);

    (* Need commitments for both statements *)
    Commitments:= (sp.Commitments × sp.Commitments);

    (* Challenge space remains the same *)
    Challenges:= sp.Challenges;

    (* Two challenges are disjoint if they're not equal *)
    Disjoint:= (λ e1 e2. e1 ≠ e2);

    (* Response now includes:
       - Response for first statement
       - Challenge used in simulation
       - Response for second statement *)
    Responses:= ((sp.Responses × sp.Challenges.carrier) × sp.Responses);

    (* First prover algorithm that generates initial commitments
       If we have witness for first statement:
         - Generate real commitment for first statement
         - Simulate proof for second statement
       If we have witness for second statement:
         - Simulate proof for first statement
         - Generate real commitment for second statement *)
    Prover_0:= (λ (s1, s2) w ((r, t),e).
                  if sp.Relation s1 w then
                    let c1 = sp.Prover_0 s1 w r;
                        (s2', c2', e2', t2') = sp.Simulator s2 t e;
                    in (c1, c2')
                  else
                    let (s1', c1', e1', t1') = sp.Simulator s1 t e;
                        c2 = sp.Prover_0 s2 w r;
                    in (c1',c2));

    (* Second prover algorithm that generates responses
       e3 is computed as e1 - e2 to ensure challenge consistency
       If we have witness for first statement:
         - Use simulator for second statement
         - Generate real response for first statement with challenge e3
       If we have witness for second statement:
         - Use simulator for first statement
         - Generate real response for second statement with challenge e3 *)
    Prover_1:= (λ (s1, s2) w ((r,t1),e2) (c1, c2) e1.
                  let   e3 = SP_csub sp e1 e2
                  in
                    if sp.Relation s1 w then
                      let (s2', c2', e2', t2') = sp.Simulator s2 t1 e2;
                          t2 = sp.Prover_1 s1 w r c1 e3;
                      in ((t2, e3), t2')
                    else
                      let  (s1', c1', e1', t1') = sp.Simulator s1 t1 e2;
                           t2 = sp.Prover_1 s2 w r c2 e3;
                      in ((t1', e2), t2));

    (* Verifier checks both proofs are valid and challenges sum correctly *)
    HonestVerifier:= (λ ((s1, s2), (c1, c2), e1, ((t1,e2),t2)).
                        let e3 = SP_csub sp e1 e2
                        in sp.HonestVerifier (s1, c1, e2, t1) ∧
                           sp.HonestVerifier (s2, c2, e3, t2));

    (* Knowledge extractor that can recover witness from two accepting transcripts
       If first challenges differ, extract from first statement responses
       Otherwise extract from second statement responses using computed e2, e4 *)
    Extractor:= (λ ((t1,e1),t2) ((t3,e3),t4) e5 e6.
                   if e1 ≠ e3 then
                     sp.Extractor t1 t3 e1 e3
                   else
                     let e2 = SP_csub sp e5 e1;
                         e4 = SP_csub sp e6 e3;
                     in sp.Extractor t2 t4 e2 e4);

    (* Simulator generates accepting transcripts for both statements
       Uses original simulator twice and ensures challenge consistency *)
    Simulator:= (λ (s1, s2) ((t1,e1),t2) e2.
                   let (s1', c1', e1', t1') = sp.Simulator s1 t1 e1;
                       e3 = SP_csub sp e2 e1;
                       (s2', c2', e2', t2') = sp.Simulator s2 t2 e3;
                   in  ((s1, s2),(c1', c2'),e2,((t1',e1), t2')));

    (* Maps witness and randomness to simulated response
       If proving first statement: simulate second, map first
       If proving second statement: simulate first, map second *)
    SimulatorMap:= (λ (s1, s2) w e1 ((r,t),e2).
                      let e3 = SP_csub sp e1 e2;
                      in
                        if sp.Relation s1 w then
                          let t1 = sp.SimulatorMap s1 w e3 r;
                          in ((t1, e3), t)
                        else
                          let t2 = sp.SimulatorMap s2 w e3 r;
                          in ((t, e2), t2));

    (* Inverse of SimulatorMap - recovers randomness
       Determines which statement the witness proves and
       inverts the appropriate simulation *)
    SimulatorMapInverse:= (λ (s1, s2) w e1 ((t1,e2),t2).
                             let e3 = SP_csub sp e1 e2;
                             in
                               if sp.Relation s1 w then
                                 let r = sp.SimulatorMapInverse s1 w e2 t1;
                                 in ((r,t2),e3)
                               else
                                 let r = sp.SimulatorMapInverse s2 w e3 t2;
                                 in  ((r,t1),e2));
  |>
End


(* AND composition of two sigma protocols S1 and S2 that allows proving knowledge
   of witnesses for both statements simultaneously. This creates a compound sigma protocol
   where both component proofs must be valid *)
Definition SP_and_def:
  SP_and S1 S2 = <|
    (* Statements are pairs - must prove both *)
    Statements:= S1.Statements × S2.Statements;

    (* Need witnesses for both statements *)
    Witnesses:= S1.Witnesses × S2.Witnesses;

    (* Relation holds only if both component relations hold *)
    Relation:= (λ (s1, s2) (w1, w2). S1.Relation s1 w1 ∧ S2.Relation s2 w2);

    (* Need random coins for both proofs *)
    RandomCoins:= (S1.RandomCoins × S2.RandomCoins);

    (* Need commitments for both proofs *)
    Commitments:= (S1.Commitments × S2.Commitments);

    (* Challenge space is the direct product of both challenge groups *)
    Challenges:= Gcross S1.Challenges S2.Challenges;

    (* Two challenge pairs are disjoint if they're disjoint in both components *)
    Disjoint:= λ (a,b) (c,d). S1.Disjoint a c ∧ S2.Disjoint b d;

    (* Need responses for both proofs *)
    Responses:= (S1.Responses × S2.Responses);

    (* First prover algorithm runs both component Prover_0s independently *)
    Prover_0:= (λ (s1, s2) (w1, w2) (r1, r2).
                  (S1.Prover_0 s1 w1 r1, S2.Prover_0 s2 w2 r2));

    (* Second prover algorithm runs both component Prover_1s independently
       with their respective challenges *)
    Prover_1:= (λ (s1, s2) (w1, w2) (r1, r2) (c1, c2) (e1, e2).
                  (S1.Prover_1 s1 w1 r1 c1 e1, S2.Prover_1 s2 w2 r2 c2 e2));

    (* Verifier accepts only if both component verifiers accept *)
    HonestVerifier:= (λ ((s1, s2), (c1, c2), (e1, e2), (t1, t2)).
                        S1.HonestVerifier (s1, c1, e1, t1) ∧
                        S2.HonestVerifier (s2, c2, e2, t2));

    (* Extractor runs both component extractors independently *)
    Extractor:= (λ (t1a, t1b) (t2a, t2b) (e1a, e1b) (e2a, e2b).
                   (S1.Extractor t1a t2a e1a e2a, S2.Extractor t1b t2b e1b e2b));

    (* Simulator runs both component simulators independently and combines results *)
    Simulator:= (λ (s1, s2) (t1, t2) (e1, e2).
                   let (s1', c1', e1', t1') = S1.Simulator s1 t1 e1;
                       (s2', c2', e2', t2') = S2.Simulator s2 t2 e2
                   in
                     ((s1', s2'),(c1', c2'),(e1', e2'),(t1', t2')));

    (* SimulatorMap runs both component maps independently *)
    SimulatorMap:= (λ (s1, s2) (w1, w2) (e1, e2) (r1, r2).
                      (S1.SimulatorMap s1 w1 e1 r1, S2.SimulatorMap s2 w2 e2 r2));

    (* SimulatorMapInverse runs both component inverses independently *)
    SimulatorMapInverse:= (λ (s1, s2) (w1, w2) (e1, e2) (t1, t2).
                             (S1.SimulatorMapInverse s1 w1 e1 t1,
                              S2.SimulatorMapInverse s2 w2 e2 t2));
  |>
End


(* Equality composition of a sigma protocol S1 that proves a witness satisfies
  the same relation for two different statements. This creates a compound protocol
  that proves knowledge of a single witness that works for both statements. *)
Definition SP_eq_def:
  SP_eq S1 = <|
    (* Statement pairs - must prove both with same witness *)
    Statements:= S1.Statements × S1.Statements;

    (* Single witness must work for both statements *)
    Witnesses:= S1.Witnesses;

    (* Relation holds if witness proves both statements *)
    Relation:= (λ (s1, s2) w. S1.Relation s1 w ∧ S1.Relation s2 w);

    (* Use same random coins for both proofs to ensure consistency *)
    RandomCoins:= S1.RandomCoins;

    (* Need commitments for both statements *)
    Commitments:= (S1.Commitments × S1.Commitments);

    (* Use challenge space from original protocol *)
    Challenges:= S1.Challenges;

    (* Use same disjointness relation *)
    Disjoint:= S1.Disjoint;

    (* Single response proves both statements *)
    Responses:= S1.Responses;

    (* First prover algorithm generates commitments for both statements
      using same randomness to ensure consistency *)
    Prover_0:= (λ (s1, s2) w r. (S1.Prover_0 s1 w r, S1.Prover_0 s2 w r));

    (* Second prover algorithm generates single response that works for both
      statements since we used same randomness *)
    Prover_1:= (λ (s1, s2) w r (c1, c2) e.
                  (S1.Prover_1 s1 w r c1 e));

    (* Verifier checks same response validates both proofs *)
    HonestVerifier:= (λ ((s1, s2), (c1, c2), e, t).
                        S1.HonestVerifier (s1, c1, e, t) ∧
                        S1.HonestVerifier (s2, c2, e, t));

    (* Can use original extractor since responses are the same *)
    Extractor:= S1.Extractor;

    (* Simulator generates consistent transcripts for both statements *)
    Simulator:= (λ (s1, s2) t e.
                   let (s1', c1', e1', t1') = S1.Simulator s1 t e;
                       (s2', c2', e2', t2') = S1.Simulator s2 t e
                   in
                     ((s1', s2'),(c1', c2'),e1', t1'));

    (* Can use original simulator map since responses are the same *)
    SimulatorMap:= (λ (s1, s2) w e r.
                      (S1.SimulatorMap s1 w e r));

    (* Can use original simulator map inverse *)
    SimulatorMapInverse:= (λ (s1, s2) w e t.
                             (S1.SimulatorMapInverse s1 w e t));
  |>
End


(* Disjointness relation in the equality composition
   is exactly the same as in the original protocol. *)
val sp_eq_dis_thm = store_thm(
  "sp_eq_dis_thm",
  “(SP_eq sp).Disjoint = sp.Disjoint”,
  rw[] >>
  simp[SP_eq_def]);


(* Well-formedness conditions for a sigma protocol,
  particularly focused on requirements needed for the equality combiner *)
Definition WellFormed_SP_def:
  WellFormed_SP sp ⇔
    (
    (* Challenge space must form an abelian group *)
    (AbelianGroup sp.Challenges) ∧

    (* Disjoint challenges must be different values
      This ensures soundness of the protocol *)
    (∀e1 e2. e1 ∈ sp.Challenges.carrier ∧  e2 ∈ sp.Challenges.carrier ⇒
             (sp.Disjoint e1 e2 ⇒ (e1 ≠ e2))) ∧

    (* First prover message must produce valid commitments
      given well-typed inputs *)
    (∀s w r. s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧ r ∈ sp.RandomCoins ⇒
             sp.Prover_0 s w r ∈ sp.Commitments) ∧

    (* Second prover message must produce valid responses
      given well-typed inputs *)
    (∀s w r c e. s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧ r ∈ sp.RandomCoins ∧
                 c ∈ sp.Commitments ∧ e ∈ sp.Challenges.carrier  ⇒
                 sp.Prover_1 s w r c e ∈ sp.Responses) ∧

    (* Extractor must produce valid witnesses
      given valid responses and challenges *)
    (∀t1 t2 e1 e2. t1 ∈ sp.Responses ∧ t2 ∈ sp.Responses ∧
                   e1 ∈ sp.Challenges.carrier ∧  e2 ∈ sp.Challenges.carrier ⇒
                   sp.Extractor t1 t2 e1 e2 ∈ sp.Witnesses) ∧

    (* Simulator must:
      - Preserve the input statement
      - Preserve the input challenge
      - Preserve the input response
      - Produce valid commitments *)
    (∀s t e s' c' e' t'.
       s ∈ sp.Statements ∧ t ∈ sp.Responses ∧ e ∈ sp.Challenges.carrier ∧
       sp.Simulator s t e = (s', c', e', t') ⇒
       s' = s ∧
       e' = e ∧
       t' = t ∧
       c' ∈ sp.Commitments) ∧

    (* SimulatorMap must produce valid responses
      given well-typed inputs *)
    (∀s w r e. s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧
               r ∈ sp.RandomCoins ∧ e ∈ sp.Challenges.carrier  ⇒
               sp.SimulatorMap s w e r  ∈ sp.Responses) ∧

    (* SimulatorMapInverse must produce valid random coins
      given well-typed inputs *)
    (∀s w t e. s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧
               t ∈ sp.Responses ∧ e ∈ sp.Challenges.carrier  ⇒
               sp.SimulatorMapInverse s w e t  ∈ sp.RandomCoins)
    )
End


(* Well-formedness conditions for a sigma protocol
  specifically for use with the OR combiner. Similar to WellFormed_SP but with
  an additional requirement about the disjointness relation. *)
Definition Or_WellFormed_SP_def:
  Or_WellFormed_SP sp ⇔
    (
    (* Challenge space must form an abelian group *)
    (AbelianGroup sp.Challenges) ∧

    (* Disjoint challenges must be different values *)
    (∀e1 e2. e1 ∈ sp.Challenges.carrier ∧  e2 ∈ sp.Challenges.carrier ⇒
             (sp.Disjoint e1 e2 ⇒ (e1 ≠ e2))) ∧

    (* First prover message must produce valid commitments
      given well-typed inputs *)
    (∀s w r. s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧ r ∈ sp.RandomCoins ⇒
             sp.Prover_0 s w r ∈ sp.Commitments) ∧

    (* Second prover message must produce valid responses
      given well-typed inputs *)
    (∀s w r c e. s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧ r ∈ sp.RandomCoins ∧
                 c ∈ sp.Commitments ∧ e ∈ sp.Challenges.carrier  ⇒
                 sp.Prover_1 s w r c e ∈ sp.Responses) ∧

    (* Extractor must produce valid witnesses
      given valid responses and challenges *)
    (∀t1 t2 e1 e2. t1 ∈ sp.Responses ∧ t2 ∈ sp.Responses ∧
                   e1 ∈ sp.Challenges.carrier ∧  e2 ∈ sp.Challenges.carrier ⇒
                   sp.Extractor t1 t2 e1 e2 ∈ sp.Witnesses) ∧

    (* Simulator must:
      - Preserve the input statement
      - Preserve the input challenge
      - Preserve the input response
      - Produce valid commitments *)
    (∀s t e s' c' e' t'.
       s ∈ sp.Statements ∧ t ∈ sp.Responses ∧ e ∈ sp.Challenges.carrier ∧
       sp.Simulator s t e = (s', c', e', t') ⇒
       s' = s ∧
       e' = e ∧
       t' = t ∧
       c' ∈ sp.Commitments) ∧

    (* SimulatorMap must produce valid responses
      given well-typed inputs *)
    (∀s w r e. s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧
               r ∈ sp.RandomCoins ∧ e ∈ sp.Challenges.carrier  ⇒
               sp.SimulatorMap s w e r  ∈ sp.Responses) ∧

    (* SimulatorMapInverse must produce valid random coins
      given well-typed inputs *)
    (∀s w t e. s ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧
               t ∈ sp.Responses ∧ e ∈ sp.Challenges.carrier  ⇒
               sp.SimulatorMapInverse s w e t  ∈ sp.RandomCoins) ∧

    (* Additional requirement for OR combiner:
      Disjointness is exactly inequality - challenges are disjoint
      if and only if they are different. This is needed to ensure
      proper challenge manipulation in the OR proof. *)
    (∀e1 e2. e1 ∈ sp.Challenges.carrier ∧ e2 ∈ sp.Challenges.carrier ⇒
             (sp.Disjoint e1 e2 ⇔ e1 ≠ e2))
    )
End


(* Well-formedness conditions specifically required for equality composition of sigma protocols.
  These extend the basic well-formedness with additional requirements ensuring responses
  and simulation are independent of the statement being proven. *)
Definition Eq_WellFormed_SP_def:
  Eq_WellFormed_SP sp ⇔
    (
    (* Protocol must satisfy basic well-formedness conditions *)
    WellFormed_SP sp ∧

    (* Prover_1 must:
      - Produce valid responses
      - Generate the same response regardless of which statement is being proven
      This ensures the same witness can be used for both statements *)
    (∀s1 s2 w r c1 c2 e. s1 ∈ sp.Statements ∧
                         s2 ∈ sp.Statements ∧
                         w ∈ sp.Witnesses ∧
                         r ∈ sp.RandomCoins ∧
                         c1 ∈ sp.Commitments ∧
                         c2 ∈ sp.Commitments ∧
                         e ∈ sp.Challenges.carrier  ⇒
                         sp.Prover_1 s1 w r c1 e ∈ sp.Responses ∧
                         sp.Prover_1 s1 w r c1 e = sp.Prover_1 s2 w r c2 e) ∧

    (* SimulatorMap must:
      - Produce valid responses for both statements
      - Generate the same response regardless of statement
      This ensures consistent simulation across both statements *)
    (∀s1 s2 w r e. s1 ∈ sp.Statements ∧
                   s2 ∈ sp.Statements ∧
                   w ∈ sp.Witnesses ∧
                   r ∈ sp.RandomCoins ∧
                   e ∈ sp.Challenges.carrier  ⇒
                   sp.SimulatorMap s1 w e r  ∈ sp.Responses ∧
                   sp.SimulatorMap s2 w e r  ∈ sp.Responses ∧
                   sp.SimulatorMap s1 w e r  =  sp.SimulatorMap s2 w e r ) ∧

    (* SimulatorMapInverse must:
      - Produce valid random coins for both statements
      - Generate the same random coins regardless of statement
      This ensures inverse simulation is also statement-independent *)
    (∀s1 s2 w t e. s1 ∈ sp.Statements ∧
                   s2 ∈ sp.Statements ∧
                   w ∈ sp.Witnesses ∧
                   t ∈ sp.Responses ∧
                   e ∈ sp.Challenges.carrier  ⇒
                   sp.SimulatorMapInverse s1 w e t  ∈ sp.RandomCoins ∧
                   sp.SimulatorMapInverse s2 w e t  ∈ sp.RandomCoins ∧
                   sp.SimulatorMapInverse s1 w e t = sp.SimulatorMapInverse s2 w e t)
    )
End


(* Completeness property for sigma protocols: For any valid statement-witness pair,
  an honest prover following the protocol will always convince an honest verifier.
  This is a fundamental requirement for any proof system. *)
Definition Complete_SP_def:
  Complete_SP sp ⇔
    (* For all valid inputs: *)
    (∀s w r e.
       (* Given well-typed parameters *)
       s ∈ sp.Statements ∧
       w ∈ sp.Witnesses ∧
       r ∈ sp.RandomCoins ∧
       e ∈ sp.Challenges.carrier ∧
       (* And given that witness proves the statement *)
       sp.Relation s w ⇒
       (* Let c be the prover's first message (commitment) *)
       let c = sp.Prover_0 s w r in
         (* Then the verifier must accept the complete transcript where:
             - s is the statement being proven
             - c is the prover's commitment
             - e is the verifier's challenge
             - Prover_1 generates the response based on all previous values *)
         sp.HonestVerifier(s, c, e, sp.Prover_1 s w r c e))
End


(* Special Soundness property for sigma protocols: given two accepting transcripts
  with the same commitment but different challenges, we can extract a valid witness.
  This property ensures knowledge soundness - the prover must "know" the witness. *)
Definition SpecialSoundness_SP_def:
  SpecialSoundness_SP sp ⇔
    ∀s c e1 e2 t1 t2.
      (* Given well-typed parameters *)
      s ∈ sp.Statements ∧
      c ∈ sp.Commitments ∧
      t1 ∈ sp.Responses ∧
      t2 ∈ sp.Responses ∧
      e1 ∈ sp.Challenges.carrier ∧
      e2 ∈ sp.Challenges.carrier ∧
      (* And given two accepting transcripts where:
       - Same statement and commitment
       - Different (disjoint) challenges
       - Both verify correctly *)
      sp.Disjoint e1 e2 ∧
      sp.HonestVerifier(s, c, e1, t1) ∧
      sp.HonestVerifier(s, c, e2, t2) ⇒
      (* Then the extracted witness must be valid for the statement *)
      sp.Relation s (sp.Extractor t1 t2 e1 e2)
End


(* Simulator Correctness property: simulated transcripts must be accepted by
  the honest verifier. This is a basic requirement for zero-knowledge simulation
  - simulated proofs should look valid. *)
Definition SimulatorCorrectness_SP_def:
  SimulatorCorrectness_SP sp ⇔
    ∀s t e.
      (* Given well-typed parameters *)
      s ∈ sp.Statements ∧
      t ∈ sp.Responses ∧
      e ∈ sp.Challenges.carrier ⇒
      (* Simulated transcript must verify *)
      sp.HonestVerifier(sp.Simulator s t e)
End


(* Honest Verifier Zero Knowledge property: for any valid statement-witness pair,
  real proofs are indistinguishable from simulated ones. This ensures the proof
  reveals nothing about the witness beyond its validity. *)
Definition HonestVerifierZeroKnowledge_SP_def:
  HonestVerifierZeroKnowledge_SP sp ⇔
    ∀s w r e t.
      (* Given well-typed parameters and valid statement-witness pair *)
      s ∈ sp.Statements ∧
      w ∈ sp.Witnesses ∧
      r ∈ sp.RandomCoins ∧
      e ∈ sp.Challenges.carrier ∧
      t ∈ sp.Responses ∧
      sp.Relation s w ⇒
      let c = sp.Prover_0 s w r;
          spm = sp.SimulatorMap s w e;
          spmi = sp.SimulatorMapInverse s w e;
      in
        (* Three key properties:
         1. Simulation matches real proofs exactly
         2. SimulatorMapInverse undoes SimulatorMap
         3. SimulatorMap undoes SimulatorMapInverse
         Together these show perfect simulation *)
        sp.Simulator s (spm r) e = (s, c, e, sp.Prover_1 s w r c e) ∧
        spmi(spm r) = r ∧
        spm(spmi t) = t
End


(* AND composition of well-formed sigma protocols is also well-formed.
   This shows the AND combiner preserves well-formedness. *)
val WellFormed_SP_and_thm = store_thm(
  "WellFormed_SP_and_thm",
  “WellFormed_SP sp1 ∧ WellFormed_SP sp2 ⇒ WellFormed_SP (SP_and sp1 sp2)”,
  simp[WellFormed_SP_def, SP_and_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >-
   ‘AbelianGroup (Gcross sp1.Challenges sp2.Challenges)’ by metis_tac[Gcross_group_thm] >>
  rpt (pairarg_tac >> gvs[]) >>
  fs[Gcross_def, pairTheory.PAIR] >>
  gs[WellFormed_SP_def, pairTheory.PAIR] >>
  metis_tac[pairTheory.PAIR]);


(* AND composition of complete sigma protocols is also complete.
   Shows that the AND combiner preserves the ability for honest provers to convince honest verifiers. *)
val Complete_SP_and_thm = store_thm(
  "Complete_SP_and_thm",
  “Complete_SP sp1 ∧ Complete_SP sp2 ⇒ Complete_SP (SP_and sp1 sp2)”,
  simp[Complete_SP_def, SP_and_def, pairTheory.FORALL_PROD] >>
  rpt (strip_tac >> gs[] >> fs[Gcross_def, pairTheory.PAIR]));


(* AND composition of special sound sigma protocols is also special sound.
   Shows that the AND combiner preserves the ability to extract witnesses
   from accepting transcripts with different challenges. *)
val SpecialSoundness_SP_and_thm = store_thm(
  "SpecialSoundness_SP_and_thm",
  “SpecialSoundness_SP sp1 ∧ SpecialSoundness_SP sp2 ⇒ SpecialSoundness_SP (SP_and sp1 sp2)”,
  simp[SpecialSoundness_SP_def, SP_and_def, pairTheory.FORALL_PROD] >>
  rpt (strip_tac >> fs[Gcross_def, pairTheory.PAIR] >> metis_tac[]));


(* AND composition of simulator-correct sigma protocols is also simulator-correct.
  Shows that the AND combiner preserves the ability to generate valid-looking
  simulated transcripts that pass verification. *)
val SimulatorCorrectness_SP_and_thm = store_thm(
  "SimulatorCorrectness_SP_and_thm",
  “SimulatorCorrectness_SP sp1 ∧ SimulatorCorrectness_SP sp2 ⇒ SimulatorCorrectness_SP (SP_and sp1 sp2)”,
  simp[SimulatorCorrectness_SP_def, SP_and_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  ‘p_1'' ∈ sp1.Challenges.carrier ∧ p_2'' ∈ sp2.Challenges.carrier’ by fs[Gcross_def, pairTheory.PAIR] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[]);


(* AND composition of Honest-Verifier Zero-Knowledge (HVZK) sigma protocols is also HVZK,
  given the component protocols are well-formed. This shows the AND combiner
  preserves zero-knowledge simulation capabilities. *)
val HonestVerifierZeroKnowledge_SP_and_thm = store_thm(
  "HonestVerifierZeroKnowledge_SP_and_thm",
  “HonestVerifierZeroKnowledge_SP sp1 ∧ HonestVerifierZeroKnowledge_SP sp2 ∧
   WellFormed_SP sp1 ∧ WellFormed_SP sp2 ⇒ HonestVerifierZeroKnowledge_SP (SP_and sp1 sp2)”,
  simp[HonestVerifierZeroKnowledge_SP_def, SP_and_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >-
   (qabbrev_tac‘s1 = p_1’ >>
    qabbrev_tac‘s2 = p_2’ >>
    qabbrev_tac‘w1 = p_1'’ >>
    qabbrev_tac‘w2 = p_2'’ >>
    qabbrev_tac‘r1 = p_1''’ >>
    qabbrev_tac‘r2 = p_2''’ >>
    qabbrev_tac‘e1 = p_1'³'’ >>
    qabbrev_tac‘e2 = p_2'³'’ >>
    qabbrev_tac‘t1 = p_1'⁴'’ >>
    qabbrev_tac‘t2 = p_2'⁴'’ >>
    ‘e1 ∈ sp1.Challenges.carrier ∧ e2 ∈ sp2.Challenges.carrier’ by fs[Gcross_def, pairTheory.PAIR] >>
    ‘sp1.SimulatorMapInverse s1 w1 e1 (sp1.SimulatorMap s1 w1 e1 r1) = r1 ∧
     sp1.SimulatorMap s1 w1 e1 (sp1.SimulatorMapInverse s1 w1 e1 t1) = t1 ∧
     sp2.SimulatorMapInverse s2 w2 e2 (sp2.SimulatorMap s2 w2 e2 r2) = r2 ∧
     sp2.SimulatorMap s2 w2 e2 (sp2.SimulatorMapInverse s2 w2 e2 t2) = t2’ by metis_tac[] >>
    ‘WellFormed_SP (SP_and sp1 sp2)’ by metis_tac[WellFormed_SP_and_thm] >>
    ‘sp1.Prover_0 s1 w1 r1 ∈ sp1.Commitments ∧ sp2.Prover_0 s2 w2 r2 ∈ sp2.Commitments’ by metis_tac[WellFormed_SP_def] >>
    qabbrev_tac‘c1 = sp1.Prover_0 s1 w1 r1’ >> qabbrev_tac‘c2 = sp2.Prover_0 s2 w2 r2’ >>
    qabbrev_tac‘t11 = sp1.Prover_1 s1 w1 r1 c1 e1’ >>
    qabbrev_tac‘t22 = sp2.Prover_1 s2 w2 r2 c2 e2’ >>
    qabbrev_tac‘t222 = sp2.SimulatorMap s2 w2 e2 r2’ >>
    qabbrev_tac‘t111 = sp1.SimulatorMap s1 w1 e1 r1’ >>
    qabbrev_tac‘x1 = sp1.Simulator s1 t111 e1’ >>
    qabbrev_tac‘x2 = sp2.Simulator s2 t222 e2’ >>
    ‘(sp1.Prover_1 s1 w1 r1 c1 e1) ∈ sp1.Responses’ by metis_tac[WellFormed_SP_def] >>
    ‘t11 ∈ sp1.Responses’ by metis_tac[] >>
    ‘t11 ∈ sp1.Responses ∧ t111 ∈ sp1.Responses ∧ t22 ∈ sp2.Responses ∧ t222 ∈ sp2.Responses’ by metis_tac[WellFormed_SP_def] >>
    ‘sp1.Simulator s1 t111 e1 =  sp1.Simulator s1 (sp1.SimulatorMap s1 w1 e1 r1) e1’ by rw[] >>
    ‘sp1.Simulator s1 (sp1.SimulatorMap s1 w1 e1 r1) e1 =
     (s1,sp1.Prover_0 s1 w1 r1, e1, sp1.Prover_1 s1 w1 r1 (sp1.Prover_0 s1 w1 r1) e1)’ by metis_tac[] >>
    ‘(s1,sp1.Prover_0 s1 w1 r1, e1, sp1.Prover_1 s1 w1 r1 (sp1.Prover_0 s1 w1 r1) e1) = (s1, c1, e1, t11)’ by metis_tac[] >>
    ‘x1 = (s1, c1, e1, t11)’ by gs[] >>

    ‘sp2.Simulator s2 t222 e2 =
     sp2.Simulator s2 (sp2.SimulatorMap s2 w2 e2 r2) e2’ by rw[] >>
    ‘sp2.Simulator s2 (sp2.SimulatorMap s2 w2 e2 r2) e2 =
     (s2,sp2.Prover_0 s2 w2 r2, e2, sp2.Prover_1 s2 w2 r2 (sp2.Prover_0 s2 w2 r2) e2)’ by metis_tac[] >>
    ‘(s2,sp2.Prover_0 s2 w2 r2, e2, sp2.Prover_1 s2 w2 r2 (sp2.Prover_0 s2 w2 r2) e2) = (s2, c2, e2, t22)’ by metis_tac[] >>
    ‘x2 = (s2, c2, e2, t22)’ by metis_tac[] >>
    ‘(λ(s1',c1',e1',t1').(λ(s2',c2',e2',t2'). ((s1',s2'),(c1',c2'),(e1',e2'),t1',t2')) (s2, c2, e2, t22)) (s1, c1, e1, t11) =
     ((s1,s2),(c1,c2),(e1,e2),(t11,t22))’ by rw[] >>
    ‘((s1,s2),(c1,c2),(e1,e2),t11,t22) = (λ(s1',c1',e1',t1'). (λ(s2',c2',e2',t2'). ((s1',s2'),(c1',c2'),(e1',e2'),t1',t2')) x2) x1’ by metis_tac[] >>
    metis_tac[]) >>
  rpt(gs[Gcross_def, pairTheory.PAIR] >> metis_tac[]));


(* Lemma proving SP_csub (challenge subtraction) produces valid challenges.
  This is crucial for OR composition where we need to manipulate challenges
  while ensuring they remain in the challenge group's carrier set. *)
val SP_csub_Lemma = store_thm(
  "SP_csub_Lemma",
  “∀sp x y.
     WellFormed_SP sp ∧
     x ∈ sp.Challenges.carrier ∧
     y ∈ sp.Challenges.carrier ⇒
     SP_csub sp x y ∈ sp.Challenges.carrier”,
  simp[SP_csub_def, SP_or_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  qabbrev_tac‘y1 = sp.Challenges.inv y’ >>
  qabbrev_tac‘Gr = sp.Challenges’ >>
  ‘Group Gr’ by metis_tac[AbelianGroup_def, WellFormed_SP_def] >>
  ‘y1 ∈ Gr.carrier’ by metis_tac[group_inv_element] >>
  ‘Gr.op x y1 ∈ Gr.carrier’ by metis_tac[group_op_element]);


(* Auxiliary tactics *)
val CASES_ON_WITNESS =
(fn () =>
   Cases_on ‘sp1.Relation p_1 w’ >>
 rpt (
   pairarg_tac >>
   gvs[]
   ) >>
 fs[] >>
 metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma] >>
 fs[]
) ();


val PAIR_TAC_METIS_TAC =
(fn () =>
   rpt (pairarg_tac>> gvs[]) >>
 metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]
) ();


(* OR composition preserves well-formedness - if the input protocol sp1
  is well-formed, then its OR composition SP_or sp1 is also well-formed *)
val WellFormed_SP_or_thm = store_thm(
  "WellFormed_SP_or_thm",
  “WellFormed_SP sp1 ⇒ WellFormed_SP (SP_or sp1)”,
  rw[]>>
  simp[WellFormed_SP_def, SP_or_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac>-
   PAIR_TAC_METIS_TAC >>
  rpt(CASES_ON_WITNESS)>-
   (Cases_on ‘p_2 ≠ p_2'' ’ >>
    rpt(fs[] >> metis_tac[WellFormed_SP_def, SP_or_def, SP_csub_Lemma]))>>
  rpt(PAIR_TAC_METIS_TAC)>>
  rpt(CASES_ON_WITNESS));


(* OR composition preserves simulator correctness - if the input protocol sp1
  has correct simulation and is well-formed, then its OR composition SP_or sp1 also produces
  valid simulated transcripts that pass verification. *)
val SimulatorCorrectness_SP_or_thm = store_thm(
  "SimulatorCorrectness_SP_or_thm",
  “SimulatorCorrectness_SP sp1 ∧ WellFormed_SP sp1 ⇒ SimulatorCorrectness_SP (SP_or sp1)”,
  simp[SimulatorCorrectness_SP_def, SP_or_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  qabbrev_tac‘s1 = p_1’ >> qabbrev_tac‘s2 = p_2’ >> qabbrev_tac‘t1 = p_1'’ >>
  qabbrev_tac‘e1 = p_2'’ >> qabbrev_tac‘t2 = p_2''’ >>
  qabbrev_tac‘e2 = (SP_csub sp1 e e1)’ >> qabbrev_tac‘c1 = sp1.Prover_0 s1 w r1’ >>
  ‘e2 ∈ sp1.Challenges.carrier’ by metis_tac[SP_csub_Lemma] >>
  qabbrev_tac‘t3 = sp1.Prover_1 s1 w r1 c1 e2’ >>
  qabbrev_tac‘sa = FST (sp1.Simulator s1 t1 e1)’ >>
  qabbrev_tac‘ca = FST (SND (sp1.Simulator s1 t1 e1))’ >>
  qabbrev_tac‘ea = FST (SND (SND (sp1.Simulator s1 t1 e1)))’ >>
  qabbrev_tac‘ta = SND (SND (SND (sp1.Simulator s1 t1 e1)))’ >>
  ‘sp1.Simulator s1 t1 e1 = (sa, ca, ea, ta)’ by rw[pairTheory.PAIR, Abbr‘sa’, Abbr‘ca’, Abbr‘ea’, Abbr‘ta’] >>
  qabbrev_tac‘sb = FST (sp1.Simulator s2 t2 e2)’ >>
  qabbrev_tac‘cb = FST (SND (sp1.Simulator s2 t2 e2))’ >>
  qabbrev_tac‘eb = FST (SND (SND (sp1.Simulator s2 t2 e2)))’ >>
  qabbrev_tac‘tb = SND (SND (SND (sp1.Simulator s2 t2 e2)))’ >>
  ‘sp1.Simulator s2 t2 e2 = (sb, cb, eb, tb)’ by rw[pairTheory.PAIR, Abbr‘sb’, Abbr‘cb’, Abbr‘eb’, Abbr‘tb’] >>
  gs[] >>
  metis_tac[WellFormed_SP_def]);


(* Lemma proving a key property of challenge subtraction (SP_csub) in the challenge group:
  For any challenges x,y in a well-formed protocol's challenge space, we have
  SP_csub sp x (SP_csub sp x y) = y
  This is like the algebraic identity:
  x - (x-y) = x - x + y = y *)
val SP_csub_Lemma2 = store_thm(
  "SP_csub_Lemma2",
  “∀sp x y z.
     WellFormed_SP sp ∧
     x ∈ sp.Challenges.carrier ∧
     y ∈ sp.Challenges.carrier ⇒
     SP_csub sp x (SP_csub sp x y) = y”,
  simp[SP_csub_def, SP_or_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  qabbrev_tac‘Gr = sp.Challenges’ >>
  ‘AbelianGroup Gr’ by metis_tac[WellFormed_SP_def] >>
  ‘Group Gr’ by metis_tac[AbelianGroup_def] >>
  ‘Gr.inv y ∈ Gr.carrier’ by metis_tac[group_inv_element] >>
  ‘Gr.op x (Gr.inv y) ∈ Gr.carrier’ by metis_tac[group_op_element] >>
  qabbrev_tac‘z = Gr.inv (Gr.op x (Gr.inv y))’ >>
  qabbrev_tac‘s = Gr.inv y’ >>
  ‘Gr.inv s = y’ by metis_tac[group_inv_inv] >>
  ‘Gr.op x s = Gr.op s x’ by metis_tac[AbelianGroup_def] >>
  ‘z = Gr.inv (Gr.op s x)’ by metis_tac[] >>
  ‘Gr.op Gr.id y = y’ by metis_tac[group_lid] >>
  ‘Gr.op x (Gr.inv x) = Gr.id’ by metis_tac[group_rinv] >>
  ‘Gr.op (Gr.op x (Gr.inv x)) y = y’ by metis_tac[] >>
  ‘Gr.inv x ∈ Gr.carrier’ by metis_tac[group_inv_element] >>
  ‘Gr.op x (Gr.op (Gr.inv x) y) = y’ by metis_tac[group_linv_assoc] >>
  ‘Gr.op x (Gr.op (Gr.inv x) (Gr.inv s)) = y’ by metis_tac[] >>
  ‘Gr.inv (Gr.op s x) = Gr.op (Gr.inv x) (Gr.inv s)’ by metis_tac[group_inv_op] >>
  ‘Gr.op x (Gr.inv (Gr.op s x)) = y’ by metis_tac[] >>
  ‘Gr.op x z = y’ by metis_tac[Abbr‘z’]);


(* Lemma proving another key property of challenge subtraction (SP_csub) in the challenge group:
  If e1 ≠ e2 and e3 = e4, then SP_csub sp e1 e3 ≠ SP_csub sp e2 e4
  In other words, if we subtract the same challenge (e3 = e4) from different challenges (e1 ≠ e2),
  we get different results. This is like the algebraic identity:
  If a ≠ b then a - c ≠ b - c *)
val SP_csub_Lemma3 = store_thm(
  "SP_csub_Lemma3",
  “∀sp e1 e2 e3 e4.
     WellFormed_SP sp ∧
     e1 ∈ sp.Challenges.carrier ∧
     e2 ∈ sp.Challenges.carrier ∧
     e3 ∈ sp.Challenges.carrier ∧
     e4 ∈ sp.Challenges.carrier ∧
     e1 ≠ e2 ∧ e3 = e4
     ⇒ (SP_csub sp e1 e3) ≠ (SP_csub sp e2 e4)”,
  rw[] >>
  simp[WellFormed_SP_def, SP_csub_def, SP_or_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  qabbrev_tac‘Gr = sp.Challenges’ >>
  ‘AbelianGroup Gr’ by metis_tac[WellFormed_SP_def] >>
  ‘Group Gr’ by metis_tac[AbelianGroup_def] >>
  ‘e1 = Gr.op (Gr.op e2 (Gr.inv e3)) (Gr.inv (Gr.inv e3))’ by metis_tac[group_lsolve, group_op_element, group_inv_element] >>
  ‘e1 = Gr.op (Gr.op e2 (Gr.inv e3)) e3’ by metis_tac[group_inv_inv] >>
  ‘e1 = Gr.op e2 (Gr.op (Gr.inv e3) e3)’ by metis_tac[group_assoc, group_op_element, group_inv_element] >>
  ‘e1 = Gr.op e2 Gr.id’ by metis_tac[group_linv, group_op_element, group_inv_element] >>
  ‘e1 = e2’ by metis_tac[group_rid, group_op_element, group_inv_element]);


(* OR composition preserves completeness - if the input protocol sp1
  is complete, simulator-correct and well-formed, then its OR composition SP_or sp1 is also complete.
  This shows an honest prover can convince an honest verifier in the OR composition when they
  have a valid witness for either statement. *)
val Complete_SP_or_thm = store_thm(
  "Complete_SP_or_thm",
  “Complete_SP sp1 ∧ SimulatorCorrectness_SP sp1 ∧ WellFormed_SP sp1 ⇒ Complete_SP (SP_or sp1)”,
  rw[]>>
  simp[Complete_SP_def, SP_or_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >-
   (rpt (pairarg_tac>>
         gvs[])>>
    qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>
    qabbrev_tac‘r1 = p_1' ’>>
    qabbrev_tac‘t1 = p_2' ’>>
    qabbrev_tac‘e1 = p_2'' ’>>
    qabbrev_tac‘e2 = (SP_csub sp1 e e1)’>> qabbrev_tac‘c1 = sp1.Prover_0 s1 w r1’>>
    qabbrev_tac‘t3 = sp1.Prover_1 s1 w r1 c1 e2’>>
    ‘e2 ∈ sp1.Challenges.carrier’ by metis_tac[SP_csub_Lemma]>>
    drule_then assume_tac (cj 1 (iffLR Complete_SP_def))>>
    first_assum$ qspecl_then [‘s1’, ‘w’, ‘r1’, ‘e2’] mp_tac>>
    ‘sp1.HonestVerifier (s1,c1,e2,t3)’by metis_tac[]>>
    fs[]>>
    ‘s2 = s2' ∧ e1 = e2'’ by metis_tac[WellFormed_SP_def]>>
    ‘sp1.Simulator s2 t1 e1 = (s2,c2,e1,t2)’by rw[]>>
    ‘SP_csub sp1 e e2 = e1’by metis_tac[SP_csub_Lemma2]>>
    metis_tac[SimulatorCorrectness_SP_def])>-
   (rpt (pairarg_tac>>
         gvs[])>>
    qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>
    qabbrev_tac‘r1 = p_1' ’>>
    qabbrev_tac‘t1 = p_2' ’>>
    qabbrev_tac‘e1 = p_2'' ’>>
    Cases_on ‘sp1.Relation s1 w’ >| [
       ‘((sp1.Prover_1 s1 w r1 c1 (SP_csub sp1 e e1),SP_csub sp1 e e1),t2') =   ((t1,e2),t2)’by metis_tac[]>>
       ‘(sp1.Prover_0 s1 w r1,c2') = (c1, c2)’by metis_tac[]>>
       fs[]>>
       ‘c1 = sp1.Prover_0 s1 w r1’ by metis_tac[Gcross_def, pairTheory.PAIR]>>
       ‘e2 = SP_csub sp1 e e1’by metis_tac[Gcross_def,pairTheory.PAIR]>>
       ‘e2 ∈ sp1.Challenges.carrier’ by metis_tac[SP_csub_Lemma]>>
       ‘t1 = sp1.Prover_1 s1 w r1 c1 e2’by metis_tac[Gcross_def,pairTheory.PAIR]>>
       ‘sp1.HonestVerifier (s1,c1,e2,t1)’by metis_tac[Complete_SP_def]>>
       ‘SP_csub sp1 e e2 = e1’by metis_tac[SP_csub_Lemma2]>>
       ‘s2 = s2' ∧ e1 = e2'’ by metis_tac[WellFormed_SP_def]>> (* Simulator does not change s and e *)
       ‘t2 = t2' ∧ c2 = c2'’by  metis_tac[Gcross_def,pairTheory.PAIR]>>
       ‘ sp1.HonestVerifier (s2,c2,SP_csub sp1 e e2,t2)’by metis_tac[SimulatorCorrectness_SP_def]>>
       fs[],
       ‘(c1',sp1.Prover_0 s2 w r1) = (c1,c2)’by metis_tac[]>>
       ‘((t1',e1),sp1.Prover_1 s2 w r1 c2 (SP_csub sp1 e e1)) = ((t1,e2),t2)’by metis_tac[]>>
       fs[]>>
       ‘c1' = c1 ∧ c2 = sp1.Prover_0 s2 w r1 ∧ t1' = t1 ∧ e1 = e2 ∧ sp1.Prover_1 s2 w r1 c2 (SP_csub sp1 e e1) = t2’
         by  metis_tac[Gcross_def,pairTheory.PAIR]>>
       ‘s1 = s1' ∧ s2 = s2'∧ e1 = e1' ∧ e1 = e2'’ by metis_tac[WellFormed_SP_def]>>
       ‘sp1.HonestVerifier (s1,c1,e2,t1)’by metis_tac[SimulatorCorrectness_SP_def]>>
       qabbrev_tac‘e3 = SP_csub sp1 e e1 ’>>
       ‘e3 = SP_csub sp1 e e2’by rw[]>>
       ‘e3 ∈ sp1.Challenges.carrier’ by metis_tac[SP_csub_Lemma]>>
       ‘sp1.HonestVerifier (s2,c2,e3,t2)’by metis_tac[Complete_SP_def]>>
       gs[]
     ]));


(* OR composition preserves special soundness - given a well-formed
  protocol sp1 with special soundness and challenges that are disjoint iff unequal,
  its OR composition SP_or sp1 also satisfies special soundness.
  Special soundness means we can extract a valid witness from any two accepting transcripts
  with the same commitment but different challenges. *)
val SpecialSoundness_SP_or_thm = store_thm(
  "SpecialSoundness_SP_or_thm",
  “∀sp. WellFormed_SP sp1 ∧
        SpecialSoundness_SP sp1 ∧
        (∀e1 e2. e1 ∈ sp1.Challenges.carrier ∧
                 e2 ∈ sp1.Challenges.carrier ⇒
                 (sp1.Disjoint e1 e2 ⇔ e1 ≠ e2))
        ⇒ SpecialSoundness_SP (SP_or sp1)”,
  rw[] >>
  simp[SpecialSoundness_SP_def, SP_or_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  qabbrev_tac‘s1 = p_1’ >> qabbrev_tac‘s2 = p_2’ >>
  qabbrev_tac‘c1 = p_1'’ >> qabbrev_tac‘c2 = p_2'’ >>
  qabbrev_tac‘t1 = p_1''’ >> qabbrev_tac‘t2 = p_2'³'’ >> qabbrev_tac‘t3 = p_1'³'’ >> qabbrev_tac‘t4 = p_2'⁵'’ >>
  qabbrev_tac‘e3 = p_2''’ >> qabbrev_tac‘e4 = p_2''''’ >>
  qabbrev_tac‘e5 = SP_csub sp1 e1 e3’ >> qabbrev_tac‘e6 = SP_csub sp1 e2 e4’ >>
  ‘e5 ∈ sp1.Challenges.carrier ∧ e6 ∈ sp1.Challenges.carrier’ by metis_tac[SP_csub_Lemma] >>
  Cases_on ‘e3 ≠ e4’ THENL [
      qabbrev_tac‘w = (if e3 ≠ e4 then sp1.Extractor t1 t3 e3 e4
                       else sp1.Extractor t2 t4 e5 e6)’ >>
      ‘w = sp1.Extractor t1 t3 e3 e4’ by metis_tac[] >>
      ‘sp1.Relation s1 w’ by metis_tac[SpecialSoundness_SP_def] >>
      fs[] >>
      rw[],
      qabbrev_tac ‘w = (if sp1.Disjoint e3 e4 then sp1.Extractor t1 t3 e3 e4
                        else sp1.Extractor t2 t4 e5 e6)’ >>
      ‘w = sp1.Extractor t2 t4 e5 e6’ by metis_tac[] >>
      ‘e3 = e4’ by metis_tac[] >>
      ‘e5 ≠ e6’ by metis_tac[SP_csub_Lemma3] >>
      ‘sp1.Disjoint e5 e6’ by metis_tac[] >>
      ‘sp1.Relation s2 w’ by metis_tac[SpecialSoundness_SP_def] >>
      rw[]
    ]);


(* OR composition preserves honest-verifier zero-knowledge (HVZK)
property. When the input protocol is HVZK and well-formed, its OR composition remains HVZK *)
val HonestVerifierZeroKnowledge_SP_or_thm = store_thm(
  "HonestVerifierZeroKnowledge_SP_or_thm",
  “HonestVerifierZeroKnowledge_SP sp ∧ WellFormed_SP sp ⇒ HonestVerifierZeroKnowledge_SP (SP_or sp)”,
  rw[]>>
  simp[HonestVerifierZeroKnowledge_SP_def, SP_or_def, pairTheory.FORALL_PROD]>>
  rpt strip_tac >-
   (rpt (pairarg_tac>>
         gvs[])>>
    qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>
    qabbrev_tac‘r = p_1' ’>> qabbrev_tac‘t1 = p_2' ’>>
    qabbrev_tac‘e1 = p_2'' ’>>
    qabbrev_tac‘t2 = p_1'' ’>>
    qabbrev_tac‘e2 = p_2'³'’>>
    qabbrev_tac‘t3 = p_2'''' ’>>
    qabbrev_tac‘e3 = SP_csub sp e e1’>>
    ‘e3 ∈ sp.Challenges.carrier’by metis_tac[SP_csub_Lemma]>>
    qabbrev_tac‘t4 = sp.SimulatorMap s1 w e3 r’>>
    ‘ t4 ∈ sp.Responses’by metis_tac[WellFormed_SP_def]>>
    ‘SP_csub sp e e3 = e1’by metis_tac[SP_csub_Lemma2]>>
    ‘ sp.Simulator s2 t1 e1 = (s2',c2',e2',t2')’by metis_tac[]>>
    ‘s1 = s1' ∧  t4 = t1' ∧  e3 = e1'’by metis_tac[WellFormed_SP_def]>>
    ‘ s2 = s2'' ∧ t1 = t2'' ∧  e1 = e2''’by metis_tac[WellFormed_SP_def]>>
    ‘ s2 = s2' ∧ t1 = t2' ∧  e1 = e2'’by metis_tac[WellFormed_SP_def]>>
    drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def)>>
    first_assum$ qspecl_then [‘s1’, ‘w’, ‘r’, ‘e3’, ‘t4’] mp_tac>>
    fs[])>-

   (fs[]>>
    qabbrev_tac‘e3 = SP_csub sp e p_2''’>>
    ‘e3 ∈ sp.Challenges.carrier’by metis_tac[SP_csub_Lemma]>>
    ‘p_2'' = SP_csub sp e e3’by metis_tac[SP_csub_Lemma2]>>
    qabbrev_tac‘t4 = sp.SimulatorMap p_1 w e3 p_1'’>>
    ‘ t4 ∈ sp.Responses’by metis_tac[WellFormed_SP_def]>>
    drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def)>>
    first_assum$ qspecl_then [‘p_1’, ‘w’, ‘p_1'’, ‘e3’, ‘t4’] mp_tac>>
    fs[])>-
   (fs[]>>
    qabbrev_tac‘e3 = SP_csub sp e p_2'³'’>>
    ‘e3 ∈ sp.Challenges.carrier’by metis_tac[SP_csub_Lemma]>>
    ‘SP_csub sp e e3 = p_2'³'’by metis_tac[SP_csub_Lemma2]>>
    qabbrev_tac‘r = sp.SimulatorMapInverse p_1 w p_2'³' p_1''’>>
    ‘ r ∈  sp.RandomCoins’by metis_tac[WellFormed_SP_def]>>
    drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def)>>
    first_assum$ qspecl_then [‘p_1’, ‘w’, ‘r’, ‘p_2'³'’, ‘ p_1''’] mp_tac>>
    fs[])>-
   (rpt (pairarg_tac>>
         gvs[])>>
    qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>
    qabbrev_tac‘r = p_1' ’>>
    qabbrev_tac‘t3 = p_2' ’>>
    qabbrev_tac‘e3 = p_2'' ’>>
    qabbrev_tac‘t4 = p_1'' ’>>
    qabbrev_tac‘e4 = p_2'³'’>>
    qabbrev_tac‘t5 = p_2'''' ’>>
    qabbrev_tac‘e5 = SP_csub sp e e1’>>
    qabbrev_tac‘e6 = SP_csub sp e e3’>>
    Cases_on ‘sp.Relation s1 w’ THENL [
       ‘((sp.SimulatorMap s1 w e6 r,e6),t3) = ((t1,e1),t2) ∧  (sp.Prover_0 s1 w r,c2'') = (c1,c2)’by metis_tac[]>>
       fs[]>>
       ‘ t1 = sp.SimulatorMap s1 w e6 r ∧ e6 = e1 ∧ t3 = t2 ∧ sp.Prover_0 s1 w r = c1 ∧ c2'' = c2’by metis_tac[pairTheory.PAIR]>>
       ‘e5 ∈ sp.Challenges.carrier ∧ e6 ∈ sp.Challenges.carrier’by metis_tac[SP_csub_Lemma, WellFormed_SP_def]>>
       ‘e5 = e3’ by metis_tac[SP_csub_Lemma2]>>
       ‘s1 = s1' ∧ t1 = t1' ∧ e1 = e1'’by metis_tac[WellFormed_SP_def]>>
       ‘s2 = s2' ∧ t2 = t2' ∧  e5 = e2'’by metis_tac[WellFormed_SP_def]>>
       ‘s2 = s2'' ∧ t3 = t2'' ∧ e3 = e2''’by metis_tac[WellFormed_SP_def]>>
       ‘s1 = s1'' ∧ t3 = t1'' ∧  e3 = e1''’by metis_tac[WellFormed_SP_def]>>
       fs[]>>
       gvs[]>>
       qabbrev_tac‘c = sp.Prover_0 p_1 w p_1'’>>
       ‘ c ∈ sp.Commitments’by metis_tac[WellFormed_SP_def]>>
       qabbrev_tac‘t = sp.Prover_1 p_1 w p_1' c e1’>>
       ‘t ∈ sp.Responses’by metis_tac[WellFormed_SP_def]>>
       drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def)>>
       first_assum$ qspecl_then [‘p_1’, ‘w’, ‘p_1'’, ‘e1’, ‘t’] mp_tac>>
       fs[]
       ,
       ‘(c1'',sp.Prover_0 s2 w r) = (c1,c2)’by metis_tac[]>>
       fs[]>>
       ‘c1'' = c1 ∧ c2 = sp.Prover_0 s2 w r’by metis_tac[WellFormed_SP_def, pairTheory.PAIR]>>
       ‘((t3,e3),sp.SimulatorMap s2 w e6 r) = ((t1,e1),t2)’by metis_tac[]>>
       ‘t3 = t1 ∧ e3 = e1 ∧ t2 = sp.SimulatorMap s2 w e6 r’by metis_tac[pairTheory.PAIR]>>
       qabbrev_tac‘t6 = sp.Prover_1 s2 w r c2 e6’>>
       ‘e6 ∈ sp.Challenges.carrier’ by metis_tac[SP_csub_Lemma]>>
       ‘ c2 ∈ sp.Commitments’by metis_tac[WellFormed_SP_def]>>
       ‘t6 ∈ sp.Responses’by metis_tac[WellFormed_SP_def]>>
       ‘e5 = e6’ by metis_tac[]>>
       ‘sp.Simulator s1 t1 e1  =  sp.Simulator s1 t3 e3’by metis_tac[]>>
       ‘(s1',c1',e1',t1') = (s1'',c1'',e1'',t1'')’by metis_tac[]>>
       ‘c1' = c1’by rw[]>>
       ‘s1'' = s1' ∧ s1 = s1' ∧ t1 = t1' ∧ t1' = t1'' ∧ e1 = e1' ∧ e1'' = e1'’by metis_tac[pairTheory.PAIR, WellFormed_SP_def]>>
       ‘t2' ∈ sp.Responses’by metis_tac[WellFormed_SP_def]>>
       drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def)>>
       ‘sp.Simulator s2 t2 e6 = (s2, c2, e6, t6)’by metis_tac[]>>
       ‘e5 = e6’by rw[]>>
       ‘sp.Simulator s2 t2 e5  = sp.Simulator s2 t2 e6’by rw[]>>
       ‘(s2',c2',e2',t2') = (s2, c2, e6, t6)’by metis_tac[pairTheory.PAIR, pairTheory.PAIR]>>
       ‘c2 = c2'’by rw[pairTheory.PAIR]>>
       ‘t6 = t2' ’by metis_tac[pairTheory.PAIR, WellFormed_SP_def]>>
       rw[]
     ])>-
   (rpt (pairarg_tac>>
         gvs[])>>
    qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>
    qabbrev_tac‘r = p_1' ’>> qabbrev_tac‘t3 = p_2' ’>>
    qabbrev_tac‘e1 = p_2'' ’>>
    qabbrev_tac‘t4 = p_1'' ’>>
    qabbrev_tac‘e3 = p_2'³'’>>
    qabbrev_tac‘t5 = p_2'''' ’>>
    qabbrev_tac‘e4 = SP_csub sp e e1’>>
    qabbrev_tac‘e5 = SP_csub sp e e2’>>
    ‘e4 ∈ sp.Challenges.carrier’ by metis_tac[SP_csub_Lemma]>>
    Cases_on ‘sp.Relation s1 w’ THENL [
       ‘((sp.SimulatorMap s1 w e4 r,e4),t3) = ((t1,e2),t2)’by metis_tac[]>>
       ‘t1 = sp.SimulatorMap s1 w e4 r ∧ e2 = e4 ∧ t3 = t2’ by rw[pairTheory.PAIR]>>
       ‘e5 = e1’by metis_tac[SP_csub_Lemma2]>>
       ‘e2 ∈  sp.Challenges.carrier ∧ t1 ∈ sp.Responses’by metis_tac[WellFormed_SP_def]>>
       drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def)>>
       ‘sp.SimulatorMapInverse s1 w e2 t1 = r’ by metis_tac[]>>
       fs[]
       ,

       ‘((t3,e1),sp.SimulatorMap s2 w e4 r) = ((t1,e2),t2)’by metis_tac[]>>
       fs[]>>
       metis_tac[pairTheory.PAIR, pairTheory.PAIR, HonestVerifierZeroKnowledge_SP_def]
     ])>-
   (rpt (pairarg_tac>>
         gvs[])>>
    Cases_on ‘sp.Relation p_1 w’ THENL [
       ‘((sp.SimulatorMapInverse p_1 w p_2'³' p_1'',p_2'⁴'), SP_csub sp e p_2'³') = ((r,t),e2)’by metis_tac[]>>
       ‘r = sp.SimulatorMapInverse p_1 w p_2'³' p_1'' ∧ t = p_2'⁴' ∧ e2 = SP_csub sp e p_2'³'’by rw[pairTheory.PAIR]>>
       ‘SP_csub sp e e2 ∈ sp.Challenges.carrier’by metis_tac[SP_csub_Lemma]>>
       drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def)>>
       ‘SP_csub sp e e2 = SP_csub sp e (SP_csub sp e p_2'³')’by rw[]>>
       ‘SP_csub sp e (SP_csub sp e p_2'³') = p_2'³'’by metis_tac[SP_csub_Lemma2]>>
       ‘sp.SimulatorMap p_1 w p_2'³' (sp.SimulatorMapInverse p_1 w p_2'³' p_1'') = p_1''’ by metis_tac[HonestVerifierZeroKnowledge_SP_def]>>
       rw[]
       ,
       qabbrev_tac‘s1 = p_1’>> qabbrev_tac‘s2 = p_2’>>
       qabbrev_tac‘r1 = p_1' ’>> qabbrev_tac‘t3 = p_2' ’>>
       qabbrev_tac‘e1 = p_2'' ’>>
       qabbrev_tac‘t4 = p_1'' ’>>
       qabbrev_tac‘e3 = p_2'³'’>>
       qabbrev_tac‘t5 = p_2'''' ’>>
       qabbrev_tac‘e4 = SP_csub sp e e3’>>
       qabbrev_tac‘e5 = SP_csub sp e e2’>>
       ‘e4 ∈ sp.Challenges.carrier’ by metis_tac[SP_csub_Lemma]>>
       drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def)>>
       ‘((sp.SimulatorMapInverse s2 w e4 t5,t4),e3) = ((r,t),e2)’by metis_tac[]>>
       ‘r = sp.SimulatorMapInverse s2 w e4 t5 ∧ t = t4 ∧ e2 = e3’by rw[pairTheory.PAIR]>>
       ‘e4 = SP_csub sp e e3’by metis_tac[]>>
       ‘e3 = e2’by rw[]>>
       ‘e5 = SP_csub sp e e2’by rw[]>>
       ‘e4 = e5’by rw[]>>
       ‘sp.SimulatorMap s2 w e5 (sp.SimulatorMapInverse s2 w e4 t5) = t5’by metis_tac[HonestVerifierZeroKnowledge_SP_def]>>
       ‘((t,e2),sp.SimulatorMap s2 w e5 r) = ((t4,e3),t5)’suffices_by rw[]>>
       ‘t = t4 ∧ e2 = e3’by rw[]>>
       ‘r = sp.SimulatorMapInverse s2 w e4 t5 ∧ e4 = e5’by rw[]>>
       ‘sp.SimulatorMap s2 w e5 r = t5’by rw[]>>
       rw[]
     ]));


(* Equality composition preserves well-formedness - if the input protocol is
   well-formed, so is its equality composition *)
val WellFormed_SP_eq_thm = store_thm(
  "WellFormed_SP_eq_thm",
  “WellFormed_SP sp ⇒ WellFormed_SP (SP_eq sp)”,
  rw[] >>
  simp[WellFormed_SP_def, SP_eq_def, pairTheory.FORALL_PROD] >>
  rpt (strip_tac >>
       gvs[WellFormed_SP_def, SP_eq_def]) >>
  rpt (rpt (pairarg_tac >> gvs[]) >>
       fs[Gcross_def, pairTheory.PAIR] >>
       gs[WellFormed_SP_def, pairTheory.PAIR] >>
       metis_tac[pairTheory.PAIR]));


(* Stronger well-formedness conditions preserve under equality composition - when
the input protocol satisfies the special equality well-formedness properties,
its equality composition does too. *)
val Eq_WellFormed_SP_eq_thm = store_thm(
  "Eq_WellFormed_SP_eq_thm",
  “Eq_WellFormed_SP sp ⇒ Eq_WellFormed_SP (SP_eq sp)”,
  rw[] >>
  simp[Eq_WellFormed_SP_def, WellFormed_SP_def, SP_eq_def, pairTheory.FORALL_PROD] >>
  rpt (strip_tac >>
       gvs[Eq_WellFormed_SP_def, WellFormed_SP_def, SP_eq_def]) >>
  rpt (rpt (pairarg_tac >> gvs[]) >>
       fs[Gcross_def, pairTheory.PAIR] >>
       gs[Eq_WellFormed_SP_def, WellFormed_SP_def, pairTheory.PAIR] >>
       metis_tac[pairTheory.PAIR]));


(* Simulator correctness preserves under equality composition - if the input protocol
has correct simulation and satisfies equality well-formedness, then its equality
composition also produces valid simulated proofs. *)
val SimulatorCorrectness_SP_eq_thm = store_thm(
  "SimulatorCorrectness_SP_eq_thm",
  “SimulatorCorrectness_SP sp ∧ Eq_WellFormed_SP sp ⇒ SimulatorCorrectness_SP (SP_eq sp)”,
  rw[] >>
  simp[SimulatorCorrectness_SP_def, SP_eq_def, Eq_WellFormed_SP_def, WellFormed_SP_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[SimulatorCorrectness_SP_def, SP_eq_def, Eq_WellFormed_SP_def, WellFormed_SP_def]);


(* Completeness preserves under equality composition - if the input protocol is complete
and satisfies equality well-formedness conditions, then an honest prover can still
convince an honest verifier in the equality composition. *)
val Complete_SP_eq_thm = store_thm(
  "Complete_SP_eq_thm",
  “Complete_SP sp ∧ Eq_WellFormed_SP sp ⇒ Complete_SP (SP_eq sp)”,
  rw[] >>
  simp[Complete_SP_def, SP_eq_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >-
   metis_tac[Complete_SP_def, SP_eq_def, SimulatorCorrectness_SP_def, Eq_WellFormed_SP_def, WellFormed_SP_def] >>
  ‘WellFormed_SP sp’ by metis_tac[Eq_WellFormed_SP_def] >>
  drule_then assume_tac (cj 2 (iffLR Eq_WellFormed_SP_def)) >>
  ‘∀s1 s2 w r c1 c2 e.
     s1 ∈ sp.Statements ∧ s2 ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧
     r ∈ sp.RandomCoins ∧ c1 ∈ sp.Commitments ∧ c2 ∈ sp.Commitments ∧
     e ∈ sp.Challenges.carrier ⇒
     sp.Prover_1 s1 w r c1 e = sp.Prover_1 s2 w r c2 e’ by metis_tac[] >>
  qabbrev_tac‘c1 = sp.Prover_0 p_1 w r’ >>
  qabbrev_tac‘c2 = sp.Prover_0 p_2 w r’ >>
  ‘c1 ∈ sp.Commitments ∧ c2 ∈ sp.Commitments’ by metis_tac[Eq_WellFormed_SP_def, WellFormed_SP_def] >>
  qabbrev_tac‘t1 = sp.Prover_1 p_1 w r c1 e’ >>
  qabbrev_tac‘t2 = sp.Prover_1 p_2 w r c2 e’ >>
  ‘sp.Prover_1 p_1 w r c1 e = sp.Prover_1 p_2 w r c2 e’ by metis_tac[Eq_WellFormed_SP_def, WellFormed_SP_def] >>
  metis_tac[Complete_SP_def]);


(* Special soundness preserves under equality composition - if the input protocol is
specially sound and equality well-formed, its equality composition maintains the
ability to extract witnesses from accepting transcripts. *)
val SpecialSoundness_SP_eq_thm = store_thm(
  "SpecialSoundness_SP_eq_thm",
  “SpecialSoundness_SP sp ∧ Eq_WellFormed_SP sp ⇒ SpecialSoundness_SP (SP_eq sp)”,
  simp[SpecialSoundness_SP_def, SP_eq_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  rpt (metis_tac[SpecialSoundness_SP_def, SP_eq_def, Eq_WellFormed_SP_def]));


(* Honest-verifier zero-knowledge preserves under equality composition - given a complete,
HVZK protocol satisfying equality well-formedness, its equality composition remains
zero-knowledge to honest verifiers.  *)
val HonestVerifierZeroKnowledge_SP_eq_thm = store_thm(
  "HonestVerifierZeroKnowledge_SP_eq_thm",
  “HonestVerifierZeroKnowledge_SP sp ∧ Eq_WellFormed_SP sp ∧ Complete_SP sp ⇒ HonestVerifierZeroKnowledge_SP (SP_eq sp)”,
  rw[] >>
  simp[HonestVerifierZeroKnowledge_SP_def, SP_eq_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >>
  rpt (
    drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def) >>
    first_assum$ qspecl_then [‘p_1’, ‘w’, ‘r’, ‘e’] mp_tac >>
    ‘sp.Simulator p_1 (sp.SimulatorMap p_1 w e r) e = (p_1, sp.Prover_0 p_1 w r, e, sp.Prover_1 p_1 w r (sp.Prover_0 p_1 w r) e)’ by metis_tac[] >>
    ‘sp.Simulator p_1 (sp.SimulatorMap p_1 w e r) e = (s1',c1',e1',t1')’ by metis_tac[] >>
    ‘WellFormed_SP sp’ by metis_tac[Eq_WellFormed_SP_def] >>
    ‘∀s t e s' c' e' t'. s ∈ sp.Statements ∧ t ∈ sp.Responses ∧ e ∈ sp.Challenges.carrier ∧ sp.Simulator s t e = (s', c', e', t') ⇒ s' = s’ by metis_tac[WellFormed_SP_def] >>
    ‘p_1 ∈ sp.Statements ∧ sp.SimulatorMap p_1 w e r ∈ sp.Responses ∧ e ∈ sp.Challenges.carrier’ by metis_tac[WellFormed_SP_def] >>
    metis_tac[]) >-
   (drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def) >>
    first_assum$ qspecl_then [‘p_1’, ‘w’, ‘r’, ‘e’] mp_tac >>
    ‘p_1 ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧ r ∈ sp.RandomCoins ∧ e ∈ sp.Challenges.carrier ∧ sp.Relation p_1 w’ by metis_tac[] >>
    ‘sp.Simulator p_1 (sp.SimulatorMap p_1 w e r) e = (p_1, sp.Prover_0 p_1 w r, e, sp.Prover_1 p_1 w r (sp.Prover_0 p_1 w r) e)’ by metis_tac[] >>
    ‘(s1',c1',e1',t1') = (p_1,sp.Prover_0 p_1 w r,e,sp.Prover_1 p_1 w r (sp.Prover_0 p_1 w r) e)’ by metis_tac[] >>
    ‘FST(SND(s1',c1',e1',t1')) = FST(SND(p_1,sp.Prover_0 p_1 w r,e,sp.Prover_1 p_1 w r (sp.Prover_0 p_1 w r) e))’ by metis_tac[pairTheory.PAIR] >>
    rw[]) >-
   (‘WellFormed_SP sp’ by metis_tac[Eq_WellFormed_SP_def] >>
    ‘∀s1 s2 w r e. s1 ∈ sp.Statements ∧ s2 ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧
                   r ∈ sp.RandomCoins ∧ e ∈ sp.Challenges.carrier ⇒
                   sp.SimulatorMap s1 w e r = sp.SimulatorMap s2 w e r’
      by metis_tac[Eq_WellFormed_SP_def] >>
    drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def) >>
    first_assum$ qspecl_then [‘p_2’, ‘w’, ‘r’, ‘e’] mp_tac >>
    ‘sp.SimulatorMap p_1 w e r = sp.SimulatorMap p_2 w e r’ by metis_tac[] >>
    ‘sp.Simulator p_2 (sp.SimulatorMap p_2 w e r) e = (p_2, sp.Prover_0 p_2 w r, e, sp.Prover_1 p_2 w r (sp.Prover_0 p_2 w r) e)’ by metis_tac[] >>
    gvs[]) >>
  rpt (
    drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def) >>
    first_assum$ qspecl_then [‘p_1’, ‘w’, ‘r’, ‘e’] mp_tac >>
    ‘p_1 ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧ r ∈ sp.RandomCoins ∧ e ∈ sp.Challenges.carrier ∧ sp.Relation p_1 w’ by metis_tac[] >>
    ‘sp.Simulator p_1 (sp.SimulatorMap p_1 w e r) e = (p_1, sp.Prover_0 p_1 w r, e, sp.Prover_1 p_1 w r (sp.Prover_0 p_1 w r) e)’ by metis_tac[] >>
    ‘(s1',c1',e1',t1') = (p_1,sp.Prover_0 p_1 w r,e,sp.Prover_1 p_1 w r (sp.Prover_0 p_1 w r) e)’ by metis_tac[] >>
    ‘FST(SND(s1',c1',e1',t1')) = FST(SND(p_1,sp.Prover_0 p_1 w r,e,sp.Prover_1 p_1 w r (sp.Prover_0 p_1 w r) e))’ by metis_tac[pairTheory.PAIR] >>
    rw[]) >>
  rpt (
    drule_then assume_tac (iffLR HonestVerifierZeroKnowledge_SP_def) >>
    first_assum$ qspecl_then [‘p_1’, ‘w’, ‘r’, ‘e’] mp_tac >>
    ‘p_1 ∈ sp.Statements ∧ w ∈ sp.Witnesses ∧ r ∈ sp.RandomCoins ∧ e ∈ sp.Challenges.carrier ∧ sp.Relation p_1 w’ by metis_tac[] >>
    ‘let c = sp.Prover_0 p_1 w r; spm = sp.SimulatorMap p_1 w e; spmi = sp.SimulatorMapInverse p_1 w e in spmi(spm r) = r’ by metis_tac[] >>
    metis_tac[]));


val _ = export_theory();
