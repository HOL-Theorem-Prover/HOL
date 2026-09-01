(* HolRefute by case study: a hotel key-card trace, adapted from
   Isabelle's Hotel_Example.thy. *)

Theory refuteHotel
Ancestors
  list
Libs
  Refute

Datatype:
  guest = G0 | G1
End

Datatype:
  hkey = K0 | K1 | K2
End

Datatype:
  room = R0
End

Datatype:
  event = CheckIn guest room (hkey # hkey)
        | Enter guest room (hkey # hkey)
        | Exit guest room
End

(* Two guests, three keys, and one room keep the trace search dense while
   retaining the initial key and two freshly issued keys used by the attack. *)

Definition owns_def:
  owns [] r = NONE /\
  owns (e::s) r =
    case e of
      CheckIn g r' c => if r' = r then SOME g else owns s r
    | _ => owns s r
End

Definition currk_def:
  currk [] r = K0 /\
  currk (e::s) r =
    case e of
      CheckIn g r' (k1,k2) =>
        if r' = r then k2 else currk s r
    | _ => currk s r
End

Definition issued_def:
  issued [] = [K0] /\
  issued (e::s) =
    case e of
      CheckIn g r (k1,k2) => k2 :: issued s
    | _ => issued s
End

Definition cards_def:
  cards [] g = [] /\
  cards (e::s) g =
    case e of
      CheckIn g' r c => if g' = g then c :: cards s g else cards s g
    | _ => cards s g
End

Definition roomk_def:
  roomk [] r = K0 /\
  roomk (e::s) r =
    case e of
      Enter g r' (k1,k2) => if r' = r then k2 else roomk s r
    | _ => roomk s r
End

(* Enter recodes the lock to the card's second key unconditionally.  This is
   the modeled lock behavior exposed by the refutations. *)

Definition isin_def:
  isin [] r = [] /\
  isin (e::s) r =
    case e of
      Enter g r' c => if r' = r then g :: isin s r else isin s r
    | Exit g r' =>
        if r' = r then FILTER (\h. h <> g) (isin s r) else isin s r
    | _ => isin s r
End

Definition hotel_def:
  hotel [] = T /\
  hotel (e::s) =
    (hotel s /\
    (case e of
      CheckIn g r (k1,k2) =>
        k1 = currk s r /\ ~MEM k2 (issued s)
    | Enter g r (k1,k2) =>
        MEM (k1,k2) (cards s g) /\
        (roomk s r = k1 \/ roomk s r = k2)
    | Exit g r => MEM g (isin s r)))
End

(* The diagnostic tactic is followed by cheat in deliberately false
   conjectures so that the counterexample remains visible in the build. *)

Theorem the_guest_in_the_room_is_the_owner:
  hotel s /\ MEM g (isin s r) ==> owns s r = SOME g
Proof
  QUICKCHECK_TAC >> cheat
QED

(* The stronger feels-safe conjecture has the same stale-key attack.  After
   the owner checks in and follows a safe-looking entry sequence, an intruder
   can enter with a stale card, so occupancy no longer implies ownership.
   Its executable search is omitted because the adaptive defaults do not
   produce a genuine counterexample. *)

Theorem current_keys_are_issued:
  hotel s ==> MEM (currk s r) (issued s)
Proof
  NARROWING_TAC >>
  Induct_on `s`
  >- simp [currk_def, issued_def]
  >> Cases_on `h`
  >- (PairCases_on `p` >>
      simp [hotel_def, currk_def, issued_def] >>
      metis_tac [])
  >- (PairCases_on `p` >>
      simp [hotel_def, currk_def, issued_def] >>
      metis_tac [])
  >> simp [hotel_def, currk_def, issued_def]
QED

Theorem card_keys_are_issued[local]:
  hotel s /\ MEM (k1,k2) (cards s g) ==>
  MEM k1 (issued s) /\ MEM k2 (issued s)
Proof
  NARROWING_TAC >>
  Induct_on `s`
  >- simp [cards_def]
  >> Cases_on `h`
  >- (PairCases_on `p` >>
      Cases_on `g'` >> Cases_on `g` >>
      simp [hotel_def, cards_def, issued_def] >>
      metis_tac [current_keys_are_issued])
  >- (PairCases_on `p` >>
      Cases_on `g'` >> Cases_on `g` >>
      simp [hotel_def, cards_def, issued_def] >>
      metis_tac [])
  >> gvs [hotel_def, cards_def, issued_def]
QED

Theorem room_keys_are_issued:
  hotel s ==> MEM (roomk s r) (issued s)
Proof
  NARROWING_TAC >>
  Induct_on `s`
  >- simp [roomk_def, issued_def]
  >> Cases_on `h`
  >- (PairCases_on `p` >>
      simp [hotel_def, roomk_def, issued_def] >>
      metis_tac [current_keys_are_issued])
  >- (PairCases_on `p` >>
      simp [hotel_def, roomk_def, issued_def] >>
      metis_tac [card_keys_are_issued])
  >> simp [hotel_def, roomk_def, issued_def]
QED
