Theory HeapMachine
Ancestors
  arithmetic option num list CBPV_Mutual_Recursive ProgramHeap

(* ------------------
        Heaps
   ------------------ *)

Type HA = “:num”;

Datatype:
  clos = closC Pro HA
End

Datatype:
  heapEntry = heapEntryC clos HA
End

Type Heap = “:heapEntry list”;

Definition put:
  put H e = (H++[e], LENGTH H)
End

Definition nth_error:
  nth_error 0 (h::_) = SOME h ∧
  nth_error (SUC n) (_::t) = nth_error n t ∧
  nth_error _ _ = NONE
End

Definition get:
  get H alpha = nth_error alpha H
End

Definition extended:
  extended H H' =
    (∀α m. (get H α = SOME m) ⇒ (get H' α = SOME m))
End

Theorem nth_error_Some_lt:
  ∀n H x. nth_error n H = SOME x ⇒ n < LENGTH H
Proof
  Induct_on `n` >> Induct_on `H` >> rw[nth_error, EL, ADD1]
QED

Theorem nth_error_app1:
  ∀l l' n.
  n < LENGTH l ⇒
  nth_error n (l++l') = nth_error n l
Proof
  Induct_on `n` >> rw[nth_error, EL, ADD1] >>
  Induct_on `l` >> rw[nth_error, EL, ADD1] >>
  first_x_assum drule >> rw[] >> metis_tac[nth_error, EL, ADD1]
QED

Theorem nth_error_app2:
  ∀l l' n.
  LENGTH l ≤ n ⇒
  nth_error n (l++l') = nth_error (n-LENGTH l) l'
Proof
  Induct_on `n` >> rw[nth_error, EL, ADD1] >>
  Induct_on `l` >> rw[nth_error, EL, ADD1] >>
  first_x_assum drule >> rw[] >> metis_tac[nth_error, EL, ADD1]
QED

Theorem nth_error_SOME_in_H:
  ∀n H x. nth_error n H = SOME x ⇒ MEM x H
Proof
  Induct_on `n` >> Induct_on `H` >> rw[nth_error]
QED

Theorem nth_error_In:
  ∀l n x.
    nth_error n l = SOME x ⇒ MEM x l
Proof
  metis_tac[nth_error_SOME_in_H]
QED

Theorem get_current:
  ∀H m H' alpha.
    put H m = (H', alpha) ⇒ get H' alpha = SOME m
Proof
  rw[put, get] >>
  `LENGTH H ≤ LENGTH H` by simp[] >>
  drule nth_error_app2 >> rw[] >>
  rw[Once nth_error]
QED

Theorem put_extends:
  ∀H H' m b.
    put H m = (H', b) ⇒ extended H H'
Proof
  rw[put, extended, get] >>
  metis_tac[nth_error_Some_lt, nth_error_app1]
QED

Definition lookup:
  lookup (H: Heap) (alpha:num) (x:num) =
    case (get H alpha) of
      SOME (heapEntryC bd env')
        => (case x of
              0 => SOME bd
            | SUC x' => lookup H env' x')
    | _ => NONE
End
            (* Task stack # Value stack # Heap *)
Type heap_state = ``:clos list # clos list # Heap``;

(* HEAP:= list of heapentry
   heapentry:= closure x number
   closure:= program x number
   program:= list of token (converted from lambda term) *)

(* heap_state x heap_state *)
Inductive heap_step:
[~lam:]
  (∀P P' M a T V H.
    jumpTarget 0 [] P = SOME (M, P')
    ⇒ heap_step (closC (lamT::P) a::T, V, H) (closC P' a::T, closC (lamT::M++[endLamT]) a::V, H))
[~app:]
  (∀a b g P Q H H' c T V.
    put H (heapEntryC g b) = (H', c)
    ⇒ heap_step (closC (appT::P) a::T, g::closC (lamT::Q++[endLamT]) b::V, H) (closC Q c::closC P a::T, V, H'))
[~var:]
  (∀P a x g T V H.
    lookup H a x = SOME g
    ⇒ heap_step (closC (varT x::P) a::T, V, H) (closC P a::T, g::V, H))
[~nilTask:]
  (∀a T V H.
    heap_step (closC [] a::T, V, H) (T, V, H))
[~force:]
  (∀a b P V K T H.
    heap_step (closC (forceT::P) a::T, closC (thunkT::V++[endThunkT]) b::K, H) (closC V b::closC P a::T, K, H))
[~thunk:]
  (∀a P M P' V T H.
    jumpThunk 0 [] P = SOME (M, P')
    ⇒ heap_step (closC (thunkT::P) a::T, V, H) (closC P' a::T, closC (thunkT::M++[endThunkT]) a::V, H))
[~ret:]
  (∀a b P T V K H.
    heap_step (closC (retT::P) a::T, closC V b::K, H) (closC P a::T, closC V b::K, H))
[~seq:]
  (∀a b c P P' M R T V H H'.
    jumpSeq 0 [] P = SOME (M, P')
    ∧ put H (heapEntryC (closC R b) a) = (H', c)
    ⇒ heap_step (closC (seqT::P) a::T, closC R b::V,H) (closC M c::closC P' a::T, V, H'))
[~pseq:]
  (∀a b b' c c' P P' M R R' T V H H'.
    jumpPseq 0 [] P = SOME (M, P')
    ∧ put H (heapEntryC (closC R b) a) = (H', c)
    ∧ put H' (heapEntryC (closC R' b') (LENGTH H)) = (H'',c')
    ⇒ heap_step (closC (pseqT::P) a::T, closC R b::closC R' b'::V,H) (closC M c'::closC P' a::T, V, H''))
[~letin:]
  (∀a c P M P' V T Vs H H'.
    jumpLetin 0 [] P = SOME (M, P')
    ∧ put H (heapEntryC V a) = (H', c)
    ⇒ heap_step (closC (letinT::P) a::T, V::Vs, H) (closC M c::closC P' a::T, Vs, H'))
End

Theorem heap_step_deterministic:
  heap_step s1 s2 ∧ heap_step s1 s3 ⇒ s2 = s3
Proof
  rw[heap_step_cases] >>
  gvs[]
QED

(* map free variables in the given lambda term s into their true values given in the environment *)
(* obtain a new lambda term s' after the substitutions *)
(*
  - Bound: Locally bounded variables remain unchanged;
  - Unbound: Environment a binds free variable n to value s' that can be looked up in H
  - Lam: descends under an abstraction thus increase k by 1 (one more variable is considered bounded in s)
  - App, Thunk, Force, Ret, Seq, Letin: descends under application *)
Inductive unfoldsVal:
[~Bound:]
  (∀H k n.
    n < k ⇒ unfoldsVal H a k (var n) (var n))
[~Unbound:]
  (∀H k b c s' n.
    k ≤ n ∧
    lookup H a (n - k) = SOME (closC (compileVal (thunk c)) b) ∧
    unfoldsVal H b 0 (thunk c) s' ⇒
    unfoldsVal H a k (var n) s')
[~Lam:]
  (∀H k m m'.
    unfoldsComp H a (SUC k) m m' ⇒
    unfoldsComp H a k (lam m) (lam m'))
[~App:]
  (∀H k m m' v v'.
    unfoldsComp H a k m m' ∧
    unfoldsVal H a k v v' ⇒
    unfoldsComp H a k (app m v) (app m' v'))
[~Thunk:]
  (∀H k c c'.
    unfoldsComp H a k c c' ⇒
    unfoldsVal H a k (thunk c) (thunk c'))
[~Force:]
  (∀H k v v'.
    unfoldsVal H a k v v' ⇒
    unfoldsComp H a k (force v) (force v'))
[~Ret:]
  (∀H k v v'.
    unfoldsVal H a k v v' ⇒
    unfoldsComp H a k (ret v) (ret v'))
[~Seq:]
  (∀H k m m' n n'.
    unfoldsComp H a k m m' ∧
    unfoldsComp H a (SUC k) n n' ⇒
    unfoldsComp H a k (seq m n) (seq m' n'))
[~Pseq:]
  (∀H k m1 m1' m2 m2' n n'.
    unfoldsComp H a k m1 m1' ∧
    unfoldsComp H a k m2 m2' ∧
    unfoldsComp H a (SUC $ SUC k) n n' ⇒
    unfoldsComp H a k (pseq m2 m1 n) (pseq m2' m1' n'))
[~Letin:]
  (∀H k v v' m m'.
    unfoldsVal H a k v v' ∧
    unfoldsComp H a (SUC k) m m' ⇒
    unfoldsComp H a k (letin v m) (letin v' m'))
End


Theorem unfolds_bound:
  (∀H a k v v'.
  unfoldsVal H a k v v' ⇒ boundVal k v') ∧
  (∀H a k m m'.
  unfoldsComp H a k m m' ⇒ boundComp k m')
Proof
  ho_match_mp_tac unfoldsVal_ind >> rw[] (* 9 *)
  >- rw[Once boundVal_cases]
  >- (‘0 ≤ k’ by simp[] >> metis_tac[bound_ge])
  >> rw[Once boundVal_cases]
QED

Theorem lookup_extend:
  ∀H H' a x g.
  extended H H' ⇒
  lookup H a x = SOME g ⇒
  lookup H' a x = SOME g
Proof
  Induct_on `x` >> rw[]
  >- (fs[extended] >> fs[lookup] >>
      Cases_on `get H a` >> fs[] >>
      first_x_assum drule >> rw[])
  >> qpat_x_assum `lookup _ _ _ = _` mp_tac >>
  rw[Once lookup] >> rw[Once lookup] >>
  Cases_on `get H a` >> fs[] >>
  rename [`extended H H'`] >>
  `∀alpha m. get H alpha = SOME m ⇒ get H' alpha = SOME m`
             by (qpat_x_assum `extended _ _` mp_tac >> rw[extended]) >>
first_x_assum drule >> rw[] >>
Cases_on `x'` >> fs[] >>
metis_tac[]
QED

Inductive reprCVal:
[~var:]
  (∀H a n s'.
    unfoldsVal H a 0 (var n) s' ⇒
    reprCVal H (closC (compileVal (var n)) a) s')
[~thunk:]
  (∀H a m s'.
    unfoldsVal H a 0 (thunk m) s' ⇒
    reprCVal H (closC (compileVal (thunk m)) a) s')
[~app_lam:]
  (∀H a s c.
    unfoldsComp H a 0 (lam c) s
    ⇒
    reprCComp H (closC (compileComp (lam c)) a) s)
[~app_ret:]
  (∀H a s c.
    unfoldsComp H a 0 (ret (thunk c)) s
    ⇒
    reprCComp H (closC (compileVal (thunk c)) a) s)
End

Theorem reprCValI:
  unfoldsVal H a 0 v s' ⇒ reprCVal H (closC (compileVal v) a) s'
Proof
  strip_tac >> Cases_on ‘v’ >> MAP_FIRST match_mp_tac [reprCVal_var,reprCVal_thunk] >>
  simp[]
QED

Theorem extended_refl[simp]:
  extended H H
Proof
  rw[extended]
QED

Theorem bound_unfolds_id:
  (∀k s.
    boundVal k s ⇒ (∀H a. unfoldsVal H a k s s)) ∧
  (∀k s.
    boundComp k s ⇒ (∀H a. unfoldsComp H a k s s))
Proof
  ho_match_mp_tac boundVal_ind >> rw[] (* 8 *)
  >- fs[Once unfoldsVal_cases, Once boundVal_cases]
  (* Unbound *)
  >> rw[Once unfoldsVal_cases, Once boundVal_cases]
QED

Definition good_heap_def:
  good_heap H =
  ∀a' a n v. get H a = SOME(heapEntryC (closC [varT n] v) a') ⇒ F
End

Theorem nth_error_append:
  nth_error n (H++H') =
  if n < LENGTH H then
    nth_error n H
  else
    nth_error (n - LENGTH H) H'
Proof
  rw[] >> rw[nth_error_app1,nth_error_app2]
QED

Theorem nth_error_cons:
  nth_error n (h::hs) =
  if n = 0 then SOME h else nth_error (n-1) hs
Proof
  Cases_on ‘n’ >> rw[nth_error]
QED

Theorem nth_error_nil:
  nth_error n [] = NONE
Proof
  Cases_on ‘n’ >> rw[nth_error]
QED

Theorem extended_trans:
  extended H H' ∧ extended H' H'' ⇒ extended H H''
Proof
  gvs[extended]
QED

Theorem good_heap_append:
  good_heap (H++H') ⇔ good_heap H ∧ good_heap H'
Proof
  rw[EQ_IMP_THM,good_heap_def,get] >>
  spose_not_then strip_assume_tac >>
  gvs[nth_error_append,AllCaseEqs(),FORALL_AND_THM] >>
  res_tac >>
  imp_res_tac nth_error_Some_lt >>
  gvs[] >>
  PRED_ASSUM is_forall mp_tac >> simp[] >>
  CONV_TAC SWAP_EXISTS_CONV >>
  qexists_tac ‘LENGTH H + a’ >>
  simp[nth_error]
QED

Theorem subst_commute':
  (∀n k. closedVal v ∧ closedVal v' ⇒
   substVal (substVal n k v) (SUC k) v' = substVal (substVal n (SUC k) v') k v)
  ∧
  (∀n k. closedVal v ∧ closedVal v' ⇒
   substComp (substComp n k v) (SUC k) v' = substComp (substComp n (SUC k) v') k v)
Proof
  Induct >>
  rw[substVal_def] >>
  gvs[] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [bound_closed] >>
  gvs[closedVal_def]
QED

Theorem subst_commute:
  closedVal v ∧ closedVal v' ⇒
  substComp (substComp n 0 v) 1 v' = substComp (substComp n 1 v') 0 v
Proof
  metis_tac[subst_commute',ONE]
QED

Theorem unfolds_subst':
  (∀H a k' s s'.
    unfoldsVal H a k' s s' ⇒
    ∀k g a' t'. k' = SUC k ⇒
        get H a' = SOME (heapEntryC g a) ⇒
        reprCVal H g t' ⇒
        good_heap H ⇒
        unfoldsVal H a' k s (substVal s' k t')) ∧
  (∀H a k' s s'.
    unfoldsComp H a k' s s' ⇒
    ∀k g a' t'. k' = SUC k ⇒
         get H a' = SOME (heapEntryC g a) ⇒
         reprCVal H g t' ⇒
         good_heap H ⇒
         unfoldsComp H a' k s (substComp s' k t'))
Proof
  ho_match_mp_tac unfoldsVal_strongind >> rw[]
  (* Bound *)
  >- (rw[Once unfoldsVal_cases] >>
      Cases_on ‘n < k’ >> rw[]
      (* n < k *)
      >- (fs[NOT_LESS] >> fs[get] >> Cases_on `g` >> rw[] >>
          fs[Once reprCVal_cases] >> rw[] >> rw[substVal_def])
      (* n = k *)
      >> fs[NOT_LESS] >> fs[prim_recTheory.LESS_THM] >> rw[] >>
      rw[Once lookup] >> fs[get] >> Cases_on `g` >> rw[] >>
      fs[Once reprCVal_cases] >> rw[]
      >- (gvs[good_heap_def,get,compileVal_def]) >>
      irule_at (Pos hd) EQ_REFL >> simp[substVal_def])
  (* Unbound *)
  >- (rename[‘unfoldsVal H b 0 _ _’, ‘unfoldsVal H a' k (var n) _’] >>
      ‘boundVal k s'’
        by (drule $ cj 1 unfolds_bound >> rw[] >> ‘0 ≤ k’ by simp[] >>
            metis_tac[bound_ge])  >>
      drule $ cj 1 bound_closed_k >> rw[] >>
      rw[Once unfoldsVal_cases] >>
      rw[Once lookup] >>
      ‘∃k'. n - k = SUC k'’
        by intLib.COOPER_TAC >> rw[] >>
      ‘k' = n - SUC k’ by intLib.COOPER_TAC >> rw[] >>
      irule_at (Pos hd) EQ_REFL >> rw[]) >>
  simp[substVal_def,Once unfoldsVal_cases]
QED

Theorem unfolds_subst:
  (∀H s s' t' a a' k g.
    get H a' = SOME (heapEntryC g a) ⇒
    reprCVal H g t' ⇒
    unfoldsVal H a 1 s s' ⇒
    good_heap H ⇒
    unfoldsVal H a' 0 s (substVal s' 0 t')) ∧
  (∀H s s' t' a a' k g.
    get H a' = SOME (heapEntryC g a) ⇒
    reprCVal H g t' ⇒
    unfoldsComp H a 1 s s' ⇒
    good_heap H ⇒
    unfoldsComp H a' 0 s (substComp s' 0 t'))
Proof
  metis_tac[unfolds_subst',ONE]
QED

Theorem unfoldsVal_extended:
  (∀H a n v v'.
     unfoldsVal H a n v v' ⇒
     ∀H'. extended H H' ⇒ unfoldsVal H' a n v v') ∧
  (∀H a n s s'.
     unfoldsComp H a n s s' ⇒
     ∀H'. extended H H' ⇒ unfoldsComp H' a n s s')
Proof
  ho_match_mp_tac unfoldsVal_ind >>
  rw[]
  >- (match_mp_tac unfoldsVal_Bound >> rw[])
  >- (match_mp_tac unfoldsVal_Unbound >>
      imp_res_tac lookup_extend >>
      simp[] >>
      metis_tac[]) >>
  MAP_FIRST match_mp_tac $ CONJUNCTS unfoldsVal_rules >>
  gvs[GSYM ADD_SUC]
QED

Theorem reprC_extend:
  (∀H g s.
     reprCVal H g s ⇒
     ∀H'. extended H H' ⇒
     reprCVal H' g s) ∧
  (∀H g s.
     reprCComp H g s ⇒
     ∀H'. extended H H' ⇒
     reprCComp H' g s)
Proof
  ho_match_mp_tac reprCVal_ind >>
  rw[] >>
  MAP_FIRST match_mp_tac $ CONJUNCTS reprCVal_rules >>
  metis_tac[unfoldsVal_extended]
QED

Theorem closed_simps[simp]:
  (closedComp(ret v) ⇔ closedVal v) ∧
  (closedVal(thunk c) ⇔ closedComp c) ∧
  (closedVal(var k) ⇔ F) ∧
  (closedComp(force v) ⇔ closedVal v) ∧
  (closedComp(app m v) ⇔ closedComp m ∧ closedVal v) ∧
  (closedComp(seq m n) ⇔ closedComp m ∧ boundComp 1 n) ∧
  (closedComp(pseq m2 m1 n) ⇔ closedComp m1 ∧ closedComp m2 ∧ boundComp 2 n) ∧
  (closedComp(letin v n) ⇔ closedVal v ∧ boundComp 1 n)
Proof
  rw[closedComp_def,closedVal_def] >>
  rw[Once boundVal_cases]
QED

Triviality heap_step_seq':
  ∀a b c P P' M R T V H H' VV PP.
       jumpSeq 0 [] P = SOME (M,P') ∧
       put H (heapEntryC (closC R b) a) = (H',c) ∧
       VV = closC R b::V ∧
       PP = closC (seqT::P) a::T
       ⇒
       heap_step (PP,VV,H)
         (closC M c::closC P' a::T,V,H')
Proof
  rpt strip_tac >>
  drule_all heap_step_seq >>
  gvs[]
QED

Theorem boundVal_subst:
  (∀n m n'.
      boundVal n m ∧ n = SUC n' ∧ closedVal v ⇒
      boundVal n' (substVal m n' v)) ∧
  (∀n m n'.
      boundComp n m ∧ n = SUC n' ∧ closedVal v ⇒
      boundComp n' (substComp m n' v))
Proof
  Ho_Rewrite.PURE_REWRITE_TAC
            [GSYM AND_IMP_INTRO,
             GSYM PULL_FORALL
            ] >>
  ho_match_mp_tac boundVal_ind >>
  rw[substVal_def] >> rw[]
  >- (gvs[closedVal_def] >>
      drule_then match_mp_tac $ cj 1 bound_ge >> simp[]) >>
  rw[Once boundVal_cases]
QED

Theorem closedComp_subst:
  boundComp 1 m ∧ closedVal c ⇒
  closedComp (substComp m 0 c)
Proof
  strip_tac >>
  drule $ cj 2 boundVal_subst >>
  simp[] >>
  disch_then drule >>
  simp[closedComp_def]
QED

Theorem boundVal_subst':
  (∀n m n'.
      boundVal n m ∧ n = SUC $ SUC n' ∧ closedVal v ∧ closedVal v' ⇒
      boundVal n' (substVal (substVal m n' v) (SUC n') v')) ∧
  (∀n m n'.
      boundComp n m ∧ n = SUC $ SUC n' ∧ closedVal v ∧ closedVal v' ⇒
      boundComp n' (substComp (substComp m n' v) (SUC n') v'))
Proof
  Ho_Rewrite.PURE_REWRITE_TAC
            [GSYM AND_IMP_INTRO,
             GSYM PULL_FORALL
            ] >>
  ho_match_mp_tac boundVal_ind >>
  rw[substVal_def] >> rw[substVal_def] >> rw[] >>
  gvs[SIMP_RULE std_ss [GSYM closedVal_def, GSYM closedComp_def] bound_closed]
  >- (gvs[closedVal_def] >> drule_then match_mp_tac $ cj 1 bound_ge >> simp[])
  >- (gvs[closedVal_def] >> drule_then match_mp_tac $ cj 1 bound_ge >> simp[]) >>
  rw[Once boundVal_cases]
QED

Theorem closedComp_subst':
  boundComp 2 m ∧ closedVal c ∧ closedVal c' ⇒
  closedComp (substComp (substComp m 0 c) 1 c')
Proof
  rw[closedComp_def] >>
  drule $ cj 2 boundVal_subst' >>
  simp[]
QED

(* --------------------------------
              Time Cost
   -------------------------------- *)

Theorem correctTime':
  ∀H a s0 s k t P T V.
    unfoldsComp H a 0 s0 s ⇒
    timeBS k s t ⇒
    closedComp s ⇒
    good_heap H ⇒
    ∃g l H'.
      reprCComp H' g t ∧
      NRC heap_step l ((closC (compileComp s0++P) a)::T, V, H) ((closC P a)::T, g::V, H') ∧
      l ≤ 10*k + 2 ∧
      extended H H' ∧
      good_heap H'
Proof
  Induct_on ‘timeBS’ >> rw[] (* 7 subgoals *)
  (* lam *)
  >- (gvs[Once unfoldsVal_cases] >>
      irule_at (Pos hd) reprCVal_app_lam >>
      simp[Once unfoldsVal_cases] >>
      first_x_assum $ irule_at $ Pos hd >>
      qexists_tac ‘1’ >>
      rw[Once heap_step_cases,compileVal_def] >>
      metis_tac[jumpTarget_correct_conc])
  (* ret *)
  >- (rename1 ‘ret v’ >>
      subgoal ‘∃c. v = thunk c’
      >- (ntac 3 $ gvs[Once unfoldsVal_cases]) >>
      gvs[] >>
      irule_at (Pos hd) reprCVal_app_ret >>
      ntac 2 $ simp[Once unfoldsVal_cases] >>
      ntac 2 $ gvs [Once unfoldsVal_cases]
      >- (gvs[Once unfoldsVal_cases] >>
          first_x_assum $ irule_at $ Pos hd >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          rw[compileVal_def] >>
          rw[NRC,PULL_EXISTS] >>
          irule_at (Pos hd) heap_step_var >>
          first_x_assum $ irule_at $ Pos hd >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          rw[compileVal_def] >>
          rw[NRC,PULL_EXISTS] >>
          irule_at (Pos hd) heap_step_ret >>
          qexists_tac ‘0’ >>
          simp[]) >>
      first_x_assum $ irule_at $ Pos hd >>
      Q.REFINE_EXISTS_TAC ‘SUC _’ >>
      rw[compileVal_def,NRC,PULL_EXISTS] >>
      irule_at (Pos hd) heap_step_thunk >>
      SIMP_TAC std_ss [jumpThunk_correct,GSYM APPEND_ASSOC,APPEND] >>
      Q.REFINE_EXISTS_TAC ‘SUC _’ >>
      rw[NRC,PULL_EXISTS] >>
      irule_at (Pos hd) heap_step_ret >>
      qexists_tac ‘0’ >>
      simp[])
  (* app *)
  >- (qhdtm_x_assum ‘unfoldsComp’ $ strip_assume_tac o ONCE_REWRITE_RULE[unfoldsVal_cases] >> gvs[] >>
      qhdtm_x_assum ‘unfoldsVal’ $ strip_assume_tac o ONCE_REWRITE_RULE[unfoldsVal_cases] >> gvs[] >>
      simp[compileVal_def] >>
      SIMP_TAC std_ss [GSYM APPEND_ASSOC]
      >- (qmatch_goalsub_abbrev_tac ‘NRC _ _ (closC (_ s0' ++ P') _::_,_,_)’ >>
          last_x_assum $ qspecl_then [‘H’,‘a’,‘s0'’,‘P'’,‘T'’,‘V’] mp_tac >>
          impl_tac >- simp[] >>
          impl_tac >- simp[] >>
          strip_tac >>
          irule_at Any NRC_ADD_I >>
          first_x_assum $ irule_at $ Pos hd >>
          unabbrev_all_tac >>
          simp[] >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          simp[NRC,PULL_EXISTS] >>
          irule_at Any heap_step_var >>
          imp_res_tac lookup_extend >>
          simp[compileVal_def] >>
          CONV_TAC SWAP_EXISTS_CONV >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          simp[NRC,PULL_EXISTS] >>
          qhdtm_x_assum ‘reprCComp’ mp_tac >>
          simp[Once reprCVal_cases] >>
          PURE_ONCE_REWRITE_TAC[unfoldsVal_cases] >>
          rw[] >>
          simp[compileVal_def] >>
          irule_at Any $ SIMP_RULE std_ss [APPEND] heap_step_app >>
          simp[put] >>
          qmatch_goalsub_abbrev_tac ‘(closC (compileComp mc) ma::mT,mV,mH)’ >>
          first_x_assum $ qspecl_then [‘mH’,‘ma’,‘mc’,‘[]’,‘mT’,‘mV’] $ mp_tac o MP_CANON >>
          rename1 ‘extended H H'’ >>
          subgoal ‘extended H' mH’ >>
          unabbrev_all_tac
          >- (rw[extended,get] >>
              imp_res_tac nth_error_Some_lt >>
              rw[nth_error_app1]) >>
          impl_keep_tac
          >- (irule_at Any $ MP_CANON $ cj 2 unfolds_subst >>
              simp[get,nth_error_app2,nth_error] >>
              simp[Once reprCVal_cases,compileVal_def,PULL_EXISTS] >>
              irule_at Any EQ_REFL >>
              conj_tac >- metis_tac[unfoldsVal_extended] >>
              conj_tac >- metis_tac[unfoldsVal_extended] >>
              conj_tac >-
               (match_mp_tac closedComp_subst >>
                simp[] >>
                metis_tac[unfolds_bound]) >>
              gvs[good_heap_append] >>
              simp[good_heap_def,get] >>
              rw[nth_error_cons,nth_error_nil]) >>
          strip_tac >>
          irule_at Any NRC_ADD_I >>
          gvs[] >>
          first_x_assum $ irule_at $ Pos hd >>
          qexists_tac ‘1’ >>
          simp[] >>
          irule_at (Pos hd) heap_step_nilTask >>
          simp[] >>
          metis_tac[extended_trans])
      >- (qmatch_goalsub_abbrev_tac ‘NRC _ _ (closC (_ s0' ++ P') _::_,_,_)’ >>
          last_x_assum $ qspecl_then [‘H’,‘a’,‘s0'’,‘P'’,‘T'’,‘V’] mp_tac >>
          impl_tac >- simp[] >>
          impl_tac >- simp[] >>
          strip_tac >>
          irule_at Any NRC_ADD_I >>
          first_x_assum $ irule_at $ Pos hd >>
          unabbrev_all_tac >>
          simp[] >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          simp[NRC,PULL_EXISTS] >>
          irule_at Any heap_step_thunk >>
          SIMP_TAC std_ss [GSYM APPEND_ASSOC, APPEND, jumpThunk_correct] >>
          CONV_TAC SWAP_EXISTS_CONV >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          simp[NRC,PULL_EXISTS] >>
          qhdtm_x_assum ‘reprCComp’ mp_tac >>
          simp[Once reprCVal_cases] >>
          PURE_ONCE_REWRITE_TAC[unfoldsVal_cases] >>
          rw[] >>
          simp[compileVal_def] >>
          irule_at Any $ SIMP_RULE std_ss [APPEND] heap_step_app >>
          simp[put] >>
          qmatch_goalsub_abbrev_tac ‘(closC (compileComp mc) ma::mT,mV,mH)’ >>
          first_x_assum $ qspecl_then [‘mH’,‘ma’,‘mc’,‘[]’,‘mT’,‘mV’] $ mp_tac o MP_CANON >>
          rename1 ‘extended H H'’ >>
          subgoal ‘extended H' mH’ >>
          unabbrev_all_tac
          >- (rw[extended,get] >>
              imp_res_tac nth_error_Some_lt >>
              rw[nth_error_app1]) >>
          impl_keep_tac
          >- (irule_at Any $ MP_CANON $ cj 2 unfolds_subst >>
              simp[get,nth_error_app2,nth_error] >>
              simp[Once reprCVal_cases,compileVal_def,PULL_EXISTS] >>
              irule_at Any EQ_REFL >>
              conj_tac
              >- (match_mp_tac $ MP_CANON $ cj 1 unfoldsVal_extended >>
                  simp[Once unfoldsVal_cases] >>
                  first_x_assum $ irule_at Any >>
                  metis_tac[unfoldsVal_extended]) >>
              conj_tac >- metis_tac[unfoldsVal_extended] >>
              conj_tac >-
               (match_mp_tac closedComp_subst >>
                simp[] >>
                metis_tac[unfolds_bound]) >>
              gvs[good_heap_append] >>
              simp[good_heap_def,get] >>
              rw[nth_error_cons,nth_error_nil]) >>
          strip_tac >>
          irule_at Any NRC_ADD_I >>
          gvs[] >>
          first_x_assum $ irule_at $ Pos hd >>
          qexists_tac ‘1’ >>
          simp[] >>
          irule_at (Pos hd) heap_step_nilTask >>
          simp[] >>
          metis_tac[extended_trans])
     )
  (* seq *)
  >- (qhdtm_x_assum ‘unfoldsComp’ $ strip_assume_tac o ONCE_REWRITE_RULE[unfoldsVal_cases] >> gvs[] >>
      simp[compileVal_def] >>
      SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      qmatch_goalsub_abbrev_tac ‘NRC _ _ (closC (_ s0' ++ P') _::_,_,_)’ >>
      last_x_assum $ qspecl_then [‘H’,‘a’,‘s0'’,‘P'’,‘T'’,‘V’] mp_tac >>
      impl_tac >- simp[] >>
      impl_tac >- simp[] >>
      strip_tac >>
      irule_at Any NRC_ADD_I >>
      first_x_assum $ irule_at $ Pos hd >>
      unabbrev_all_tac >>
      simp[] >>
      Q.REFINE_EXISTS_TAC ‘SUC _’ >>
      simp[NRC,PULL_EXISTS] >>
      qhdtm_x_assum ‘reprCComp’ mp_tac >>
      simp[Once reprCVal_cases] >>
      PURE_ONCE_REWRITE_TAC[unfoldsVal_cases] >>
      rw[] >>
      simp[compileVal_def] >>
      irule_at Any $ PURE_REWRITE_RULE [APPEND] heap_step_seq' >>
      simp[] >>
      SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,jumpSeq_correct] >>
      simp[put] >>
      qmatch_goalsub_abbrev_tac ‘(closC (compileComp mc) ma::mT,mV,mH)’ >>
      first_x_assum $ qspecl_then [‘mH’,‘ma’,‘mc’,‘[]’,‘mT’,‘mV’] $ mp_tac o MP_CANON >>
      rename1 ‘extended H H'’ >>
      subgoal ‘extended H' mH’ >>
      unabbrev_all_tac
      >- (rw[extended,get] >>
          imp_res_tac nth_error_Some_lt >>
          rw[nth_error_app1]) >>
      impl_keep_tac
      >- (irule_at Any $ MP_CANON $ cj 2 unfolds_subst >>
          simp[get,nth_error_app2,nth_error] >>
          simp[Once reprCVal_cases,compileVal_def,PULL_EXISTS] >>
          irule_at Any EQ_REFL >>
          conj_tac >- metis_tac[unfoldsVal_extended] >>
          conj_tac >- metis_tac[unfoldsVal_extended] >>
          conj_tac >-
           (match_mp_tac closedComp_subst >>
            simp[] >>
            imp_res_tac unfolds_bound >>
            gvs[closedComp_def] >>
            qhdtm_x_assum ‘boundVal’ mp_tac >>
            rw[Once boundVal_cases] >> rw[closedComp_def]) >>
          gvs[good_heap_append] >>
          simp[good_heap_def,get] >>
          rw[nth_error_cons,nth_error_nil]) >>
      strip_tac >>
      irule_at Any NRC_ADD_I >>
      gvs[] >>
      first_x_assum $ irule_at $ Pos hd >>
      qexists_tac ‘1’ >>
      simp[] >>
      irule_at (Pos hd) heap_step_nilTask >>
      simp[] >>
      metis_tac[extended_trans])
  (* pseq *)
  >- (qhdtm_x_assum ‘unfoldsComp’ $ strip_assume_tac o ONCE_REWRITE_RULE[unfoldsVal_cases] >> gvs[] >>
      simp[compileVal_def] >>
      SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      last_x_assum drule >>
      simp[SimpL“$==>”] >>
      qmatch_goalsub_abbrev_tac ‘closC(compileComp _ ++ a1)’ >>
      disch_then(qspecl_then [‘a1’,‘T'’,‘V’] strip_assume_tac) >>
      irule_at Any NRC_ADD_I >>
      first_x_assum $ irule_at $ Pos hd >>
      qunabbrev_tac ‘a1’ >>
      imp_res_tac unfoldsVal_extended >>
      last_x_assum drule >>
      simp[SimpL“$==>”] >>
      qmatch_goalsub_abbrev_tac ‘closC(compileComp _ ++ a1)’ >>
      disch_then(qspecl_then [‘a1’,‘T'’,‘g::V’] strip_assume_tac) >>
      irule_at Any NRC_ADD_I >>
      first_x_assum $ irule_at $ Pos hd >>
      qunabbrev_tac ‘a1’ >>
      irule_at Any $ iffRL $ cj 2 NRC >>
      simp[Once heap_step_cases,PULL_EXISTS] >>
      SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      simp[jumpPseq_correct'] >>
      simp[Once jumpPseq] >>
      simp[put] >>
      qhdtm_x_assum ‘reprCComp’ mp_tac >>
      simp[Once reprCVal_cases] >>
      PURE_ONCE_REWRITE_TAC[unfoldsVal_cases] >>
      simp[] >>
      rw[] >>
      qhdtm_x_assum ‘reprCComp’ mp_tac >>
      simp[Once reprCVal_cases] >>
      PURE_ONCE_REWRITE_TAC[unfoldsVal_cases] >>
      simp[] >>
      rw[] >>
      qmatch_goalsub_abbrev_tac ‘(_,_,H1)’ >>
      sg ‘good_heap H1’
      >- (gvs[good_heap_def,get,Abbr ‘H1’,nth_error_append] >>
          rw[] >>
          rw[oneline nth_error] >>
          rpt(BasicProvers.PURE_TOP_CASE_TAC >> gvs[compileVal_def])) >>
      rename [‘extended H H'’, ‘extended H' H''’] >>
      sg ‘extended H'' H1’
      >- (gvs[Abbr ‘H1’,extended,get,nth_error_append] >>
          rw[] >>
          rw[oneline nth_error] >>
          rpt(BasicProvers.PURE_TOP_CASE_TAC >> gvs[]) >>
          gvs[NOT_LESS] >>
          imp_res_tac nth_error_Some_lt >>
          gvs[]) >>
      last_x_assum $ drule_at $ Pos last >>
      disch_then $ qspecl_then [‘LENGTH H'' + 1’,‘n'’] mp_tac >>
      impl_tac
      >- (reverse conj_asm2_tac
          >- (irule closedComp_subst' >>
              simp[] >>
              imp_res_tac unfolds_bound >>
              gvs[closedVal_def,closedComp_def]) >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[subst_commute] >>
          conj_asm1_tac >-
           (imp_res_tac unfolds_bound >>
            gvs[closedVal_def,closedComp_def]) >>
          irule $ cj 2 unfolds_subst' >>
          simp[] >>
          simp[get,Abbr ‘H1’,nth_error_append] >>
          simp[oneline nth_error] >>
          conj_tac
          >- (irule reprCValI >>
              irule $ cj 1 unfoldsVal_extended >>
              first_x_assum $ irule_at $ Pos last >>
              metis_tac[extended_trans]) >>
          irule $ cj 2 unfolds_subst' >>
          simp[] >>
          simp[get,nth_error_append] >>
          simp[oneline nth_error] >>
          conj_tac
          >- (irule reprCValI >>
              irule $ cj 1 unfoldsVal_extended >>
              first_x_assum $ irule_at $ Pos last >>
              metis_tac[extended_trans]) >>
          irule $ cj 2 unfoldsVal_extended >>
          first_x_assum $ irule_at $ Pos last >>
          metis_tac[extended_trans]) >>
      disch_then $ qspecl_then [‘[]’,‘closC P a::T'’,‘V’] mp_tac >>
      simp[] >>
      strip_tac >>
      irule_at Any NRC_ADD_I >>
      first_x_assum $ irule_at $ Pos hd >>
      irule_at Any $ iffRL $ cj 2 NRC >>
      simp[Once heap_step_cases,PULL_EXISTS] >>
      irule_at Any $ iffRL $ cj 1 NRC >>
      simp[] >>
      metis_tac[extended_trans])
  (* letin *)
  >- (qhdtm_x_assum ‘unfoldsComp’ $ strip_assume_tac o ONCE_REWRITE_RULE[unfoldsVal_cases] >> gvs[] >>
      qhdtm_x_assum ‘unfoldsVal’ $ strip_assume_tac o ONCE_REWRITE_RULE[unfoldsVal_cases] >> gvs[] >>
      simp[compileVal_def] >>
      SIMP_TAC std_ss [GSYM APPEND_ASSOC]
      >- (CONV_TAC SWAP_EXISTS_CONV >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          simp[NRC,PULL_EXISTS] >>
          irule_at Any heap_step_var >>
          simp[] >>
          CONV_TAC SWAP_EXISTS_CONV >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          simp[NRC,PULL_EXISTS] >>
          irule_at Any heap_step_letin >>
          simp[] >>
          SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,jumpLetin_correct] >>
          simp[put] >>
          qmatch_goalsub_abbrev_tac ‘NRC _ _ (closC (_ s0') mA::mT,_,mH)’ >>
          last_x_assum $ qspecl_then [‘mH’,‘mA’,‘s0'’,‘[]’,‘mT’,‘V’] $ mp_tac o MP_CANON >>
          subgoal ‘extended H mH’ >>
          unabbrev_all_tac
          >- (gvs[extended,get,nth_error_append] >>
              rw[] >>
              imp_res_tac nth_error_Some_lt) >>
          impl_keep_tac >-
           (simp[] >>
            reverse $ rpt conj_asm2_tac
            >- (gvs[good_heap_append] >>
                simp[good_heap_def,get] >>
                rw[nth_error_cons,nth_error_nil,compileVal_def])
            >- (match_mp_tac closedComp_subst >>
                simp[]) >>
            match_mp_tac $ MP_CANON $ cj 2 unfolds_subst >>
            simp[get,nth_error_append,nth_error] >>
            conj_tac
            >- (match_mp_tac reprCVal_thunk >>
                match_mp_tac $ MP_CANON $ cj 1 unfoldsVal_extended >>
                metis_tac[]) >>
            match_mp_tac $ MP_CANON $ cj 2 unfoldsVal_extended >>
            first_x_assum $ irule_at $ Pos last >>
            simp[]) >>
          simp[] >>
          strip_tac >>
          irule_at Any NRC_ADD_I >>
          first_x_assum $ irule_at $ Pos hd >>
          unabbrev_all_tac >>
          simp[] >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          simp[NRC,PULL_EXISTS] >>
          irule_at Any heap_step_nilTask >>
          CONV_TAC SWAP_EXISTS_CONV >>
          qexists_tac ‘0’ >> simp[] >>
          metis_tac[extended_trans])
      >- (CONV_TAC SWAP_EXISTS_CONV >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          simp[NRC,PULL_EXISTS] >>
          irule_at Any heap_step_thunk >>
          SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,jumpThunk_correct] >>
          simp[] >>
          CONV_TAC SWAP_EXISTS_CONV >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          simp[NRC,PULL_EXISTS] >>
          irule_at Any heap_step_letin >>
          simp[] >>
          SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,jumpLetin_correct] >>
          simp[put] >>
          qmatch_goalsub_abbrev_tac ‘NRC _ _ (closC (_ s0') mA::mT,_,mH)’ >>
          last_x_assum $ qspecl_then [‘mH’,‘mA’,‘s0'’,‘[]’,‘mT’,‘V’] $ mp_tac o MP_CANON >>
          subgoal ‘extended H mH’ >>
          unabbrev_all_tac
          >- (gvs[extended,get,nth_error_append] >>
              rw[] >>
              imp_res_tac nth_error_Some_lt) >>
          impl_keep_tac >-
           (simp[] >>
            reverse $ rpt conj_asm2_tac
            >- (gvs[good_heap_append] >>
                simp[good_heap_def,get] >>
                rw[nth_error_cons,nth_error_nil,compileVal_def])
            >- (match_mp_tac closedComp_subst >>
                simp[]) >>
            match_mp_tac $ MP_CANON $ cj 2 unfolds_subst >>
            simp[get,nth_error_append,nth_error] >>
            conj_tac
            >- (rw[reprCVal_cases,compileVal_def] >>
                irule_at (Pos hd) EQ_REFL >>
                match_mp_tac $ MP_CANON $ cj 1 unfoldsVal_extended >>
                rw[Once unfoldsVal_cases] >>
                metis_tac[]) >>
            match_mp_tac $ MP_CANON $ cj 2 unfoldsVal_extended >>
            first_x_assum $ irule_at $ Pos last >>
            simp[]) >>
          simp[] >>
          strip_tac >>
          irule_at Any NRC_ADD_I >>
          first_x_assum $ irule_at $ Pos hd >>
          unabbrev_all_tac >>
          simp[] >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          simp[NRC,PULL_EXISTS] >>
          irule_at Any heap_step_nilTask >>
          CONV_TAC SWAP_EXISTS_CONV >>
          qexists_tac ‘0’ >> simp[] >>
          metis_tac[extended_trans])
     )
  (* force *)
  >- (qhdtm_x_assum ‘unfoldsComp’ $ strip_assume_tac o ONCE_REWRITE_RULE[unfoldsVal_cases] >> gvs[] >>
      qhdtm_x_assum ‘unfoldsVal’ $ strip_assume_tac o ONCE_REWRITE_RULE[unfoldsVal_cases] >> gvs[]
      (* var *)
      >- (qhdtm_x_assum ‘unfoldsVal’ $ strip_assume_tac o ONCE_REWRITE_RULE[unfoldsVal_cases] >> gvs[] >>
          simp[compileVal_def] >>
          CONV_TAC SWAP_EXISTS_CONV >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          simp[NRC,PULL_EXISTS] >>
          irule_at Any heap_step_var >>
          simp[compileVal_def] >>
          CONV_TAC SWAP_EXISTS_CONV >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          simp[NRC,PULL_EXISTS] >>
          first_x_assum drule_all >> rw[] >>
          first_x_assum $ qspecl_then [‘[]’, ‘closC P a::T'’, ‘V’] assume_tac >>
          rw[] >>
          first_x_assum $ irule_at $ Pos hd >>
          gvs[] >>
          irule_at Any NRC_ADD_I >>
          first_x_assum $ irule_at $ Pos hd >>
          Q.REFINE_EXISTS_TAC ‘SUC 0’ >>
          simp[NRC,PULL_EXISTS] >>
          irule_at (Pos hd) heap_step_nilTask >>
          metis_tac[heap_step_force, APPEND])
      (* thunk *)
      >- (simp[compileVal_def] >>
          CONV_TAC SWAP_EXISTS_CONV >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          simp[NRC,PULL_EXISTS] >>
          irule_at Any heap_step_thunk >>
          SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,jumpThunk_correct] >>
          CONV_TAC SWAP_EXISTS_CONV >>
          Q.REFINE_EXISTS_TAC ‘SUC _’ >>
          simp[NRC,PULL_EXISTS] >>
          first_x_assum drule_all >> rw[] >>
          first_x_assum $ qspecl_then [‘[]’, ‘closC P a::T'’, ‘V’] assume_tac >>
          rw[] >>
          first_x_assum $ irule_at $ Pos hd >>
          gvs[] >>
          irule_at Any NRC_ADD_I >>
          first_x_assum $ irule_at $ Pos hd >>
          Q.REFINE_EXISTS_TAC ‘SUC 0’ >>
          simp[NRC,PULL_EXISTS] >>
          irule_at (Pos hd) heap_step_nilTask >>
          metis_tac[heap_step_force, APPEND]
         )
     )
QED

Definition init_def:
  init s = ([closC (compileComp s) 0],[],[])
End

Theorem correctTime:
  ∀k s t.
  timeBS k s t ⇒
  closedComp s ⇒
  ∃g H l.
  reprCComp H g t ∧
  NRC heap_step l (init s) ([], [g], H) ∧
  l ≤ 10*k + 3
Proof
  rpt strip_tac >>
  drule_at (Pat ‘timeBS _ _ _’) correctTime' >>
  simp[] >>
  disch_then $ qspecl_then [‘[]’,‘0’,‘s’,‘[]’,‘[]’,‘[]’] mp_tac >>
  impl_tac
  >- (conj_tac
      >- (match_mp_tac $ cj 2 bound_unfolds_id >>
          gvs[closedComp_def]) >>
      gvs[good_heap_def,get,nth_error_nil]) >>
  strip_tac >>
  first_x_assum $ irule_at $ Pos hd >>
  irule_at Any NRC_ADD_I >>
  gvs[init_def] >>
  first_x_assum $ irule_at $ Pos hd >>
  qexists_tac ‘1’ >>
  simp[Once heap_step_cases]
QED

(* --------------------------------
              Space Cost
   -------------------------------- *)

Theorem lookup_el:
  ∀H alpha x e.
    lookup H alpha x = SOME e ⇒
    ∃beta.
      MEM (heapEntryC e beta) H
Proof
  Induct_on `x` >> rw[]
  >- (fs[Once lookup, Once get] >>
      Cases_on `nth_error alpha H` >> fs[] >>
      drule nth_error_In >> rw[] >>
      Cases_on `x` >> fs[] >> rw[] >>
      metis_tac[])
  >> qpat_x_assum `lookup _ _ _ = _` mp_tac >>
  rw[Once lookup] >>
  Cases_on `get H alpha` >> gs[] >>
  Cases_on `x'` >> gs[] >>
  first_x_assum drule >> rw[]
QED

Definition sizeC_def:
  sizeC g =
    case g of
      closC P a => sizeP P + a
End

Definition sizeHE_def:
  sizeHE e =
    case e of
      heapEntryC g b => sizeC g + b
End

Definition sizeH_def:
  sizeH H =
    SUM (MAP sizeHE H)
End

Definition sizeSt_def:
    sizeSt (Ts,V,H) =
      SUM (MAP sizeC Ts) + SUM (MAP sizeC V) + sizeH H
End

Theorem length_H:
  ∀i s T V H.
    NRC heap_step i (init s) (T,V,H) ⇒
    LENGTH H ≤ i*2
Proof
  Induct_on `i` >> rw[ADD1]
  >- fs[init_def]
  >> drule NRC_ADD_E >> rw[relationTheory.O_DEF] >>
  PairCases_on `y` >> gs[] >>
  first_x_assum drule >> rw[] >>
  qpat_x_assum `heap_step _ _` mp_tac >>
  rw[Once heap_step_cases] >> rw[] >>
  fs[put] >> rw[]
QED

Theorem length_TV:
  ∀i s T V H.
    NRC heap_step i (init s) (T,V,H) ⇒
    LENGTH T + LENGTH V <= 1+i
Proof
  Induct_on `i` >> rw[ADD1]
  >- (fs[init_def] >> rw[])
  >> drule NRC_ADD_E >> rw[relationTheory.O_DEF] >>
  PairCases_on `y` >> gs[] >>
  first_x_assum drule >> rw[] >>
  qpat_x_assum `heap_step _ _` mp_tac >>
  rw[Once heap_step_cases] >> rw[] >>
  fs[put] >> rw[]
QED

Theorem list_bound:
  ∀size m A.
    (∀x. MEM x A ⇒ size x ≤ m)
    ⇒ SUM (MAP size A) ≤ LENGTH A * m
Proof
  Induct_on `A` >> rw[] >>
  `∀x. MEM x A ⇒ size x ≤ m` by metis_tac[] >>
  first_x_assum drule >> rw[] >>
  rw[ADD1] >>
  `size h ≤ m` by metis_tac[] >>
  rw[]
QED

Theorem size_clos:
  ∀P a i s T V H.
    NRC heap_step i (init s) (T,V,H) ⇒
    (MEM (closC P a) (T++V) ⇒
     sizeP P ≤ 2*sizeComp s ∧ a ≤ LENGTH H)
    ∧
    (∀beta.
      MEM (heapEntryC (closC P a) beta) H ⇒
      sizeP P ≤ 2*sizeComp s ∧ a ≤ LENGTH H ∧ beta ≤ LENGTH H)
Proof
  simp[sizeP] >>
  Induct_on `i`
  (* base cases *)
  >- (fs[init_def] >> rw[] >> qspec_then ‘s’ assume_tac $ cj 2 sizeP_size >> intLib.COOPER_TAC)
  (* Inductive cases *)
  >> ntac 7 strip_tac >> fs[ADD1] >>
  drule NRC_ADD_E >> simp[relationTheory.O_DEF] >> strip_tac >>
  rename [`heap_step y (T',V,H)`] >>
  PairCases_on `y` >> gs[] >>
  first_x_assum drule >>
  qpat_x_assum `heap_step _ _` mp_tac >>
  simp[Once heap_step_cases] >>
  rpt $ disch_then strip_assume_tac >> gvs[SF DNF_ss]
  (* 11 different heap steps *)
  (* lam *)
  >- (drule jumpTarget_eq >> rw[] >> gs[MEM, sizeT, SUM_APPEND] >> res_tac)
  (* app *)
  >- (rw[] >> res_tac >> fs[put, MEM, sizeT, SUM_APPEND] >> gvs[] >> res_tac >> fs[] >> intLib.COOPER_TAC)
  (* var *)
  >- (rw[] >> res_tac >> drule_then assume_tac lookup_el >> rw[] >> res_tac
      >>  fs[put, MEM, sizeT, SUM_APPEND] >> gvs[] >> res_tac >> fs[] >> intLib.COOPER_TAC)
  (* nil T *)
  >- (rw[] >> gs[MEM, sizeT, SUM_APPEND] >> res_tac)
  (* force *)
  >- (rw[] >> res_tac >> fs[MEM, sizeT, SUM_APPEND] >> gvs[] >> res_tac >> fs[] >> intLib.COOPER_TAC)
  (* thunk *)
  >- (drule jumpThunk_eq >> rw[] >> gs[MEM, sizeT, SUM_APPEND] >> res_tac)
  (* return *)
  >- (rw[] >> res_tac >> fs[MEM, sizeT, SUM_APPEND] >> gvs[] >> res_tac >> fs[] >> intLib.COOPER_TAC)
   (* seq *)
  >- (drule jumpSeq_eq >> rw[] >> gvs[MEM, sizeT, SUM_APPEND, put] >> res_tac >> gvs[])
   (* dseq *)
  >- (drule jumpPseq_eq >> rw[] >> gvs[MEM, sizeT, SUM_APPEND, put] >> res_tac >> gvs[])
  (* letin *)
  >> drule jumpLetin_eq >> rw[] >> gs[MEM, sizeT, SUM_APPEND, put] >> res_tac >> gvs[] >> res_tac >> rw[]
QED

Theorem correctSpace:
  ∀i s T V H.
    NRC heap_step i (init s) (T,V,H) ⇒
    sizeSt (T,V,H) ≤ (3*i + 1) * (4*i+2*sizeComp s)
Proof
  rw[sizeSt_def, sizeH_def] >>
  drule length_H >> rw[] >>
  drule length_TV >> rw[] >>
  irule LESS_EQ_TRANS >>
  irule_at (Pos hd) LESS_EQ_LESS_EQ_MONO >>
  irule_at (Pos hd) list_bound >>
  irule_at Any LESS_EQ_TRANS >>
  irule_at (Pos hd) LESS_EQ_LESS_EQ_MONO >>
  irule_at (Pos hd) list_bound >>
  irule_at Any list_bound >>
  CONV_TAC $ RESORT_EXISTS_CONV rev >>
  qexistsl [‘2*sizeComp s + 4*i’,‘2*sizeComp s + 4*i’,‘2*sizeComp s + 4*i’] >>
  simp[GSYM PULL_EXISTS] >>
  conj_tac
  >- (Cases >> rw[sizeHE_def] >>
      rename [`MEM (heapEntryC c n) H`] >>
      Cases_on `c` >>
      rename [` MEM (heapEntryC (closC l n') n) H`] >>
      gvs[sizeC_def] >>
      drule $ cj 2 size_clos >>
      disch_then drule >>
      rw[]) >>
  conj_tac
  >- (Cases >> rw[sizeC_def] >>
      drule $ cj 1 size_clos >>
      simp[MEM_APPEND,SF DNF_ss] >>
      rw[] >>
      res_tac >>
      intLib.COOPER_TAC) >>
  irule_at Any LESS_EQ_REFL >>
  conj_tac
  >- (Cases >> rw[sizeC_def] >>
      drule $ cj 1 size_clos >>
      simp[MEM_APPEND,SF DNF_ss] >>
      rw[] >>
      res_tac >>
      intLib.COOPER_TAC) >>
  simp[GSYM RIGHT_ADD_DISTRIB]
QED
