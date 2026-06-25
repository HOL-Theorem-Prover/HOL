(* See:
    Paul Blain Levy
    "Call-by-Push-Value: A Subsuming Paradigm", 1999;

    Forster, Kunze and Roth,
    "The weak call-by-value lambda-calculus is reasonable for both time and space", POPL 2020

   for inspiration
 *)
Theory CBPV_Mutual_Recursive
Ancestors
  arithmetic list

(* ==========================
             Syntax
   ========================== *)

(* CBPV terms defined mutual recursively *)
Datatype:
        val = var num | thunk comp ;
        comp = force val | lam comp | app comp val | ret val |
                   seq comp comp | letin val comp | pseq comp comp comp
End

Definition sizeVal_def:
  (sizeVal (var n) = 1 + n) ∧
  (sizeVal (thunk c) = 1 + sizeComp c) ∧
  (sizeComp (force v) = 1 + sizeVal v) ∧
  (sizeComp (lam m) = 1 + sizeComp m) ∧
  (sizeComp (app m v) = 1 + sizeComp m + sizeVal v) ∧
  (sizeComp (ret v) = 1 + sizeVal v) ∧
  (sizeComp (seq m n) = 1 + sizeComp m + sizeComp n) ∧
  (sizeComp (letin v m) = 1 + sizeVal v + sizeComp m) ∧
  (sizeComp (pseq m2 m1 n) = 1 + sizeComp m2 + sizeComp m1 + sizeComp n)
End

(* substVal s k u:
     substitutes all the occurences of (var k) in s with u *)
Definition substVal_def:
  (substVal (var n) k u = if (n = k) then u else (var n)) ∧
  (substVal (thunk m) k u = thunk (substComp m k u)) ∧
  (substComp (force v) k u = force (substVal v k u)) ∧
  (substComp (lam m) k u = lam (substComp m (SUC k) u)) ∧
  (substComp (app m v) k u = app (substComp m k u) (substVal v k u)) ∧
  (substComp (ret v) k u = ret (substVal v k u)) ∧
  (substComp (seq m n) k u = seq (substComp m k u) (substComp n (SUC k) u)) ∧
  (substComp (letin v m) k u = letin (substVal v k u) (substComp m (SUC k) u)) ∧
  (substComp (pseq m2 m1 n) k u = pseq (substComp m2 k u) (substComp m1 k u) (substComp n (SUC (SUC k)) u))
End

val t1 = ``force (thunk (app (lam (ret (var 0))) (var 1)))``

Inductive is_terminal:
        (is_terminal (ret s)) ∧
        (is_terminal (lam t))
End

(* ==========================
      Small-step Semantics
   ========================== *)

Inductive primitive_step:
        (∀m. primitive_step (force (thunk m)) m) ∧
        (∀m m' v. substComp m 0 v = m' ⇒ primitive_step (app (lam m) v) m') ∧
        (∀m m' v. (substComp m 0 v) = m' ⇒ (primitive_step (letin v m) m')) ∧
        (∀n n' v.  (substComp n 0 v) = n' ⇒ (primitive_step (seq (ret v) n) n')) ∧
        (∀v1 v2 n n'.  (substComp (substComp n 0 v1) 1 v2) = n' ⇒ (primitive_step (pseq (ret v2) (ret v1) n) n'))
End

Inductive small_step:
        (∀m m'. primitive_step m m' ⇒ small_step m m') ∧
        (∀m m' v. small_step m m' ⇒ small_step (app m v) (app m' v)) ∧
        (∀m m' n. small_step m m' ⇒ small_step (seq m n) (seq m' n)) ∧
        (∀m1 m1' m2 n. small_step m1 m1' ⇒ small_step (pseq m2 m1 n) (pseq m2 m1' n)) ∧
        (∀v m2 m2' n. small_step m2 m2' ⇒ small_step (pseq m2 (ret v) n) (pseq m2' (ret v) n))
End

(* ==========================
       Big-step Semantics
   ========================== *)

Inductive big_step:
        (∀v. big_step (ret v) (ret v)) ∧
        (∀m. big_step (lam m) (lam m)) ∧
        (∀m m'. big_step m m' ⇒ big_step (force (thunk m)) m') ∧
        (∀m n v n'. (big_step m (lam n) ∧ big_step (substComp n 0 v) n') ⇒
                                 big_step (app m v) n') ∧
        (∀m m' v. big_step (substComp m' 0 v) m ⇒ big_step (letin v m') m)      ∧
        (∀m n n' v. big_step m (ret v) ∧ big_step (substComp n 0 v) n' ⇒
                                 big_step (seq m n) n') ∧
        (∀m1 m2 v1 v2 n n'. big_step m1 (ret v1) ∧ big_step m2 (ret v2) ∧ big_step (substComp (substComp n 0 v1) 1 v2) n' ⇒
                                 big_step (pseq m2 m1 n) n')
End

(* -- Big-Step Semantics with Time Cost -- *)

Inductive timeBS:
[~Lam:]
  (∀s. timeBS (0:num) (lam s) (lam s))
[~Ret:]
  (∀s. timeBS (0:num) (ret s) (ret s))
[~App:]
  (∀m m' v u i k l.
    timeBS i m (lam m') ∧
    timeBS k (substComp m' 0 v) u ∧
    l = i+1+k ⇒
    timeBS l (app m v) u)
[~Seq:]
  (∀m n v u i k l.
    timeBS i m (ret v) ∧
    timeBS k (substComp n 0 v) u ∧
    l = i+1+k ⇒
    timeBS l (seq m n) u)
[~Pseq:]
  (∀m1 m2 v1 v2 n u i j k l.
    timeBS i m1 (ret v1) ∧
    timeBS j m2 (ret v2) ∧
    timeBS k (substComp (substComp n 0 v1) 1 v2) u ∧
    l = i+j+1+k ⇒
    timeBS l (pseq m2 m1 n) u)
[~Letin:]
  (∀m v u k l.
    timeBS k (substComp m 0 v) u ∧
    l = 1+k ⇒
    timeBS l (letin v m) u)
[~Force:]
  (∀m u k l.
    timeBS k m u ∧
    l = 2+k ⇒
    timeBS l (force (thunk m)) u)
End

(* -- Big-Step Semantics with Space Cost -- *)

Inductive spaceBS:
[~Lam:]
  (∀s. spaceBS (sizeComp (lam s)) (lam s) (lam s))
[~Ret:]
  (∀s. spaceBS (sizeComp (ret s)) (ret s) (ret s))
[~App:]
  (∀s s' v u k1 k2 k.
    spaceBS k1 s (lam s') ∧
    spaceBS k2 (substComp s' 0 v) u ∧
    k = MAX (k1 + 1 + sizeVal v) k2 ⇒
    spaceBS k (app s v) u)
[~Seq:]
  (∀s n v u k1 k2 k.
    spaceBS k1 s (ret v) ∧
    spaceBS k2 (substComp n 0 v) u ∧
    k = MAX (k1 + 1 + sizeComp n) k2 ⇒
    spaceBS k (seq s n) u)
[~PSeq:]
  (∀m1 m2 v1 v2 n u k1 k2 k3 k.
    spaceBS k1 m1 (ret v1) ∧
    spaceBS k2 m2 (ret v2) ∧
    spaceBS k3 (substComp (substComp n 0 v1) 1 v2) u ∧
    k = MAX (k1 + sizeComp m2 + 1 + sizeComp n) $ MAX (k2 + sizeVal v1 + 1 + sizeComp n) k3 ⇒
    spaceBS k (pseq m2 m1 n) u)
[~Letin:]
  (∀m v u k0 k.
    spaceBS k0 (substComp m 0 v) u ∧
    k = MAX k0 (1 + sizeVal v + sizeComp m) ⇒
    spaceBS k (letin v m) u)
[~Force:]
  (∀m u k0 k.
    spaceBS k0 m u ∧
    k = MAX k0 (sizeComp m + 2) ⇒
    spaceBS k (force (thunk m)) u)
End

Theorem big_step_iff_spaceBS:
  big_step s s' ⇔ ∃k. spaceBS k s s'
Proof
  eq_tac
  >- (Induct_on `big_step` >> rw[] >> rw[Once spaceBS_cases] >>
      metis_tac[])
  >> Induct_on `spaceBS` >> rw[] >> rw[Once big_step_cases] >>
  metis_tac[]
QED

Theorem spaceBS_ge:
  ∀m s t.
    spaceBS m s t ⇒ sizeComp s ≤ m ∧ sizeComp t ≤ m
Proof
  Induct_on `spaceBS` >> rw[] >>
  rw[sizeVal_def]
QED

Inductive boundVal:
  (∀k n. n < k ⇒ boundVal k (var n)) ∧
  (∀k c. boundComp k c ⇒ boundVal k (thunk c)) ∧
  (∀k c v. boundComp k c ∧ boundVal k v ⇒ boundComp k (app c v)) ∧
  (∀k c. boundComp (SUC k) c ⇒ boundComp k (lam c)) ∧
  (∀k v. boundVal k v ⇒ boundComp k (ret v)) ∧
  (∀k v. boundVal k v ⇒ boundComp k (force v)) ∧
  (∀k m n. boundComp k m ∧ boundComp (SUC k) n ⇒ boundComp k (seq m n)) ∧
  (∀k m1 m2 n. boundComp k m1 ∧ boundComp k m2 ∧ boundComp (SUC (SUC k)) n ⇒ boundComp k (pseq m2 m1 n)) ∧
  (∀k v m. boundVal k v ∧ boundComp (SUC k) m ⇒ boundComp k (letin v m))
End

Definition closedVal_def:
  (closedVal v = boundVal 0 v)
End

Definition closedComp_def:
  (closedComp m = boundComp 0 m)
End

(*----------------------------------
                Bound
  ----------------------------------*)

val val_induction = fetch "-" "val_induction";

Theorem bound_closed_k:
  (∀v k u. boundVal k v ⇒ substVal v k u = v) ∧
  (∀m k u. boundComp k m ⇒ substComp m k u = m)
Proof
  ho_match_mp_tac val_induction >> rw[] >> (* 8 *)
  pop_assum mp_tac >> rw[Once boundVal_cases, Once substVal_def]
QED

Theorem bound_ge:
  (∀v k. boundVal k v ⇒ ∀j. k ≤ j ⇒ boundVal j v) ∧
  (∀m k. boundComp k m ⇒ ∀j. k ≤ j ⇒ boundComp j m)
Proof
  ho_match_mp_tac val_induction >> rw[]
  (* var *)
  >- fs[Once boundVal_cases]
  (* thunk *)
  >- (qpat_x_assum (`boundVal _ _`) mp_tac >>
      rw[Once boundVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      rw[Once boundVal_cases])
  (* force *)
  >- (qpat_x_assum (`boundComp _ _`) mp_tac >>
      rw[Once boundVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      rw[Once boundVal_cases])
     (* lam *)
  >- (qpat_x_assum (`boundComp _ _`) mp_tac >>
      rw[Once boundVal_cases] >>
      first_x_assum drule >> rw[] >>
      rw[Once boundVal_cases])
  (* app *)
  >- (qpat_x_assum (`boundComp _ _`) mp_tac >>
      rw[Once boundVal_cases] >>
      first_x_assum drule_all >> rw[] >>
      first_x_assum drule_all >> rw[] >>
      rw[Once boundVal_cases])
  (* ret *)
  >- (qpat_x_assum (`boundComp _ _`) mp_tac >>
      rw[Once boundVal_cases] >>
      first_x_assum drule >> rw[] >>
      rw[Once boundVal_cases])
  (* seq, letin *)
  >> qpat_x_assum (`boundComp _ _`) mp_tac >>
  rw[Once boundVal_cases] >>
  first_x_assum drule_all >> rw[] >>
  first_x_assum $ drule_at $ Pos hd >> rw[] >>
  rw[Once boundVal_cases]
  >> metis_tac[]
QED

Theorem bound_closed:
  (∀v k u. boundVal 0 v ⇒ substVal v k u = v) ∧
  (∀m k u. boundComp 0 m ⇒ substComp m k u = m)
Proof
  rw[]
  >- (drule (cj 1 bound_ge) >> rw[] >>
      metis_tac[bound_closed_k])
  >> drule (cj 2 bound_ge) >> rw[] >>
  metis_tac[bound_closed_k]
QED
