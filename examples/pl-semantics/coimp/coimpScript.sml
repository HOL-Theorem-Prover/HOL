(*
  A functional big-step semantics for an extension of the listImp language
  that describes a constrained coroutine mechanism. In particular the coroutines
  are:
    - stackful
    - one-shot
    - asymmetric.

  In addition, the coroutines are NOT first-class in that they can't be moved
  around the program like other values, nor can multiple identifiers be bound to
  the same instance of a coroutine, let alone obtain a copy.
*)

open HolKernel Parse boolLib bossLib;
open stringLib integerTheory finite_mapTheory
open alistTheory arithmeticTheory numTheory;
open impTheory listImpTheory combinTheory;
open optionTheory pred_setTheory listTheory;

val _ = new_theory "coimp";

(* *********TYPES********* *)

Type vname[local] = ``:string``;
Type fname[local] = ``:string``;
Type cname[local] = ``:string``;

Datatype:
  marker = New | Old
End

(* costat to check completion/existence of coroutine *)
Datatype:
  bexp2 = Bc bool | Not bexp2 | And bexp2 bexp2 | Less aexp aexp | CoStat cname
End

Datatype:
    stmt =
    | Assign vname aexp
    | Call fname (aexp list)
    | AssignCall vname fname (aexp list)
    | Return aexp
    (* | TailCall fname (aexp list) *)
    | MakeCo cname fname (aexp list)
    | RunCo cname
    | Yield
    | If bexp2 (stmt list) (stmt list)
    | While bexp2 (stmt list)
    (* could UnWhile be removed as well and pushed into the semantics? *)
    | UnWhile (stmt list) stmt
    (* could remove AssignGhost and push into the semantics *)
    | AssignGhost vname
    | Break
    | Continue
End

Datatype:
  localState =
    <| vars   : vname -> int option
    (* need alist instead of fmap. self reference, so needs to be inductive *)
     ; cos    : (cname, (stmt list # localState) list) alist
     ; coVar  : int
     ; inCo   : bool
    |>
End

Datatype:
  state =
    <| globals    : vname -> int option
     ; functions  : fname -> ((vname list) # (stmt list))
     ; frame      : localState
    |>
End

Datatype:
  result =
  | ResError (* distinction with ResImpossible a bit blurry...TODO refactor *)
  | ResImpossible (* for things that shouldn't occur when well formed *)
  | ResNone
  | ResReturn int
  | ResCont marker ((stmt list # localState) list)
  | ResBreak
  | ResContinue
End

(* *********DEFINITIONS********* *)

Definition insert_alist_def:
  insert_alist l k v = fmap_to_alist ((alist_to_fmap l) |+ (k,v))
End

Definition bval2_def:
  (bval2 (Bc v) s = v) /\
  (bval2 (Not b) s = ~bval2 b s) /\
  (bval2 (And b1 b2) s = (bval2 b1 s /\ bval2 b2 s)) /\
  (bval2 (Less a1 a2) s = (aval a1 (FST s) < aval a2 (FST s))) /\
  (bval2 (CoStat c) s = (SND s) c)
End

(* should unwhile be handled with more nuance because the type doesn't *)
(* enforce that it's second component is a while? *)
Definition break_ok_def:
  (break_ok (Break:stmt) = F) /\
  (break_ok (If b l1 l2) = ((EVERY break_ok l1) /\ (EVERY break_ok l2))) /\
  (break_ok _ = T)
End

Definition continue_ok_def:
  (continue_ok (Continue:stmt) = F) /\
  (continue_ok (If b l1 l2) =
    ((EVERY continue_ok l1) /\ (EVERY continue_ok l2))) /\
  (continue_ok _ = T)
End

(* needs to be folded over a program *)
(* needs to be applied to functions as well *)
Definition syntax_ok_def:
  syntax_ok c = ((break_ok c) /\ (continue_ok c))
End

(* really just for proving termination *)
Definition nu_stmt_size_def:
  nu_stmt_size (Assign _ _) = 3 /\
  (* + 1 for the trailing NIL constructor *)
  nu_stmt_size (Call _ args) = 2 + LENGTH args + 1 /\
  nu_stmt_size (AssignCall _ _ args) = 3 + LENGTH args + 1 /\
  nu_stmt_size (Return _) = 2 /\
  nu_stmt_size (MakeCo _ _ args) = 3 + LENGTH args + 1 /\
  nu_stmt_size (RunCo _) = 2 /\
  nu_stmt_size (Yield) = 2 /\
  nu_stmt_size (If _ l1 l2) = 2 + nu_stmt1_size l1 + nu_stmt1_size l2 /\
  nu_stmt_size (While _ cs) = 2 + nu_stmt1_size cs /\
  nu_stmt_size (UnWhile cs c) = 1 + nu_stmt1_size cs + nu_stmt_size c /\
  nu_stmt_size (AssignGhost _) = 2 /\
  nu_stmt_size Break = 1 /\
  nu_stmt_size Continue = 1 /\
  nu_stmt1_size [] = 1 /\
  nu_stmt1_size $ c::cs = nu_stmt_size c + nu_stmt1_size cs
End

Definition embed_bexp_def:
  embed_bexp ((Bc v):bexp) = ((Bc v):bexp2) /\
  embed_bexp (Not b) = (Not (embed_bexp b)) /\
  embed_bexp (And b1 b2) = (And (embed_bexp b1) (embed_bexp b2)) /\
  embed_bexp (Less a1 a2) = (Less a1 a2)
End

Definition embed_def:
    (embed ((Assign v a):com) = ((Assign v a):stmt)) /\
    (embed (If b c1 c2) = If (embed_bexp b) (embedl c1) (embedl c2)) /\
    (embed (While b c) = While (embed_bexp b) (embedl c)) /\
    (embedl [] = []) /\
    (embedl (c::cs) = (embed c)::(embedl cs))
End

Definition empty_local_def:
  empty_local = <| vars := (\_. NONE); cos := []; coVar := 0; inCo := F |>
End

Definition empty_global_def:
  empty_global =
    <| globals := (\_. NONE); functions := (\_. ([], []));
       frame := empty_local |>
End

(* add distinctness condition to the keys of the alist for convenience *)
Definition frame_ok_def:
  (frame_ok (0:num) f <=> ALL_DISTINCT (MAP FST f.cos) /\
    !c. c ∈ alist_range f.cos ==> EVERY ((EVERY syntax_ok) ∘ FST) c) /\
  (frame_ok t f <=> ALL_DISTINCT (MAP FST f.cos) /\
    !c. c ∈ alist_range f.cos ==> ((EVERY ((EVERY syntax_ok) ∘ FST) c) /\
    (EVERY (frame_ok (t-1) ∘ SND) c)))
End

Definition fun_ok_def:
  fun_ok s = !f. EVERY syntax_ok (SND (s.functions f))
End

(* returns a total function. simplifies semantics *)
(* locals shadow globals *)
Definition get_lookup_def:
  get_lookup s = (\x. case s.frame.vars x of
    | SOME v => v
    | NONE => (case s.globals x of
      | SOME v => v
      | NONE => 0))
End

(* treats completed and non-existent coroutines as the same thing *)
Definition get_co_completion_lookup_def:
  get_co_completion_lookup frame =
    \x. case ALOOKUP frame.cos x of NONE => F | SOME _ => T
End

Definition update_var_def:
  update_var s x v = case s.frame.vars x of
    | SOME _ => s with frame :=
                  (s.frame with vars := (x =+ SOME v) s.frame.vars)
    | NONE => (case s.globals x of
      | SOME _ => s with globals := (x =+ SOME v) s.globals
      | NONE => s with frame :=
                  (s.frame with vars := (x =+ SOME v) s.frame.vars))
End

(* should also be able to prove prog1 not empty *)
Definition smart_coseq_def:
  (smart_coseq _ _ (ResCont Old []) = ResError) /\
  (smart_coseq [] _ (ResCont New frames) = ResCont New frames) /\
  (smart_coseq prog2 (l:localState) (ResCont New frames) =
    ResCont Old ((prog2, l)::frames)) /\
  (smart_coseq prog2 l (ResCont Old ((prog1, l')::frames)) =
    ResCont Old ((prog1 ++ prog2, l')::frames))
End

Definition smart_cowhile_def:
  (smart_cowhile _ _ (ResCont Old []) = ResError) /\
  (smart_cowhile w (l:localState) (ResCont New frames) =
    ResCont Old (([w], l)::frames)) /\
  (smart_cowhile w l (ResCont Old ((p, l')::xs)) =
    ResCont Old (([UnWhile p w], l')::xs))
End

Definition build_fun_state_def:
  (build_fun_state f [] = f) /\
  (build_fun_state f ((x,v)::xs) = build_fun_state ((x =+ SOME v) f) xs)
End

(* ignores length check of zip *)
(* probably want a proof that this doesn't matter for a legal program *)
Definition build_callframe_def:
  build_callframe s f args =
    let
      strict_args = MAP (\x. aval x (get_lookup s)) args;
      (params, _) = s.functions f
    in
      <| vars := build_fun_state (\_. NONE) (ZIP (params, strict_args));
         cos := []; coVar := 0; inCo := s.frame.inCo |>
End

Definition build_cont_def:
  build_cont s fun args =
    let
      strict_args = MAP (\x. aval x (get_lookup s)) args;
      (params, body) = s.functions fun;
      (* ignoring length check on zip *)
      coframe =
        <| vars := build_fun_state (\_. NONE) (ZIP (params, strict_args));
           cos := []; coVar := 0; inCo := T |>
    in
      (body, coframe)
End

Definition from_new_syntax_ok_def:
  from_new_syntax_ok _ [] = T /\ (*vacuous case*)
  from_new_syntax_ok New l = EVERY ((EVERY syntax_ok) ∘ FST) l /\
  from_new_syntax_ok Old (x::xs) = EVERY ((EVERY syntax_ok) ∘ FST) xs
End

(* theorems used for termination of evaluate *)
Theorem nu_stmt_size_pos:
  0 < nu_stmt_size c
Proof
  Cases_on `c` >> simp[nu_stmt_size_def]
QED

Theorem nu_stmt1_size_pos:
  0 < nu_stmt1_size cs
Proof
  Induct_on `cs` >> simp[nu_stmt_size_def]
QED

Definition evaluate_def:
  (pval (0:num) _ s = NONE) /\
  (pval t [] s = SOME (ResNone, s)) /\
  (pval t (c::cs) s = case cval t c s of
    | SOME (ResNone, s') => pval t cs s'
    | SOME (ResCont m frames, s') =>
        SOME (smart_coseq cs s'.frame (ResCont m frames), s')
    | val => val) /\
  (runco (0:num) _ _ = NONE) /\
  (* empty continuation not error to simplify semantics *)
  (runco t [] s = SOME (ResNone, s)) /\
  (runco t ((cs, l)::frames) s = case runco t frames s of
    | SOME (ResNone, s') => pval t cs (s' with frame := l)
      (* coroutine caller responsible for restoring local state *)
    | SOME (ResReturn v, s') => pval t cs (s' with frame := (l with coVar := v))
    | SOME (ResCont m frames', s') => SOME (ResCont New ((cs, l)::frames'), s')
    | v => v) /\
  (cval (0:num) _ s = NONE) /\
  (cval t Break s = SOME (ResBreak, s)) /\
  (cval t Continue s = SOME (ResContinue, s)) /\
  (cval t Yield s =
    SOME (if s.frame.inCo then ResCont New [] else ResNone, s)) /\
  (cval t (Return a) s = SOME (ResReturn (aval a (get_lookup s)), s)) /\
  (cval t (Assign x a) s =
    let v = aval a (get_lookup s)
    in SOME (ResNone, update_var s x v)) /\
  (cval t (If b c1 c2) s =
    pval t (if bval2 b (get_lookup s, get_co_completion_lookup s.frame)
            then c1 else c2) s) /\
  (cval t (While b c) s =
    if bval2 b (get_lookup s, get_co_completion_lookup s.frame)
    then cval (t-1) (UnWhile c (While b c)) s
    else SOME (ResNone, s)) /\
  (*unwhile necessary because of break and continue*)
  (cval t (UnWhile ps (While b cs)) s =
    case pval t ps s of
      | SOME (ResBreak, s') => SOME (ResNone, s')
      | SOME (ResContinue, s') => cval t (While b cs) s'
      | SOME (ResNone, s') => cval t (While b cs) s'
      | SOME (ResCont m frames, s') =>
          SOME (smart_cowhile (While b cs) s'.frame (ResCont m frames), s')
      | v => v) /\
  (cval t (RunCo co) s = case ALOOKUP s.frame.cos co of
    | NONE => SOME (ResError, s)
    | SOME frames => (case runco (t-1) frames s of
      | SOME (ResNone, s') =>
          SOME (ResNone, s' with frame :=
            (s.frame with cos := ADELKEY co s.frame.cos))
      | SOME (ResCont _ frames', s') =>
          SOME (ResNone, s' with frame :=
            (s.frame with cos := AFUPDKEY co (\_. frames') s.frame.cos))
      (*
        For now just discard the return value and fix up the state, though
        might be nice to add a field to retrieve the return value.
        Then I'll need to make a more pronounced distinction between a finished
        coroutine and a non-existent coroutine.
        I'll also have to think about whether a coroutine identifier can be
        rebound.
        For the semantics this might not be problematic but for compilation
        some memory for the old coroutine will need to be cleaned up.
      *)
      | SOME (ResReturn v, s') =>
          SOME (ResNone, s' with frame :=
              (s.frame with cos := ADELKEY co s.frame.cos))
      | SOME (ResBreak, s') => SOME (ResImpossible, s')
      | SOME (ResContinue, s') => SOME (ResImpossible, s')
      | v => OPTION_MAP (\(_, z). (ResError, z)) v)) /\
  (cval t (MakeCo co fun args) s =
    SOME (ResNone, s with frame :=
      (s.frame with cos :=
        (insert_alist s.frame.cos co [build_cont s fun args])))) /\
  (cval t (Call f args) s =
    case pval (t-1) (SND $ s.functions f)
      (s with frame := build_callframe s f args) of
      | SOME (ResNone, s') => SOME (ResNone, s' with frame := s.frame)
      | SOME (ResCont _ frames, s') =>
          SOME (ResCont New frames, s' with frame := s.frame)
      | SOME (ResReturn v, s') => SOME (ResReturn v, s' with frame := s.frame)
      | SOME (ResBreak, s') => SOME (ResImpossible, s')
      | SOME (ResContinue, s') => SOME (ResImpossible, s')
      | v => OPTION_MAP (\(_, z). (ResError, z)) v) /\
  (cval t (AssignCall x f args) s = case cval t (Call f args) s of
    | SOME (ResNone, s') => SOME (ResNone, s')
    | SOME (ResReturn v, s') =>
        SOME (ResNone, update_var s' x v)
    | SOME (ResCont _ frames, s') =>
        SOME (ResCont Old (([AssignGhost x], s.frame)::frames), s')
    | v => v) /\
  (cval t (AssignGhost x) s = SOME (ResNone, update_var s x (s.frame.coVar))) /\
  (cval _ _ s = SOME (ResError, s))
Termination
  WF_REL_TAC `inv_image (measure I LEX measure I) (\r. case r of
    | INL (t, cs, _) => (t, nu_stmt1_size cs)
    | INR (INR (t, c, _)) => (t, nu_stmt_size c)
    | INR (INL (t, fs, _)) => (t, list_size (\(cs, _). nu_stmt1_size cs) fs))`
  >> rw[nu_stmt_size_def, nu_stmt_size_pos, nu_stmt1_size_pos]
End

(* *********THEOREMS********* *)

Theorem smart_coseq_out:
  smart_coseq cs fr (ResCont m l) = ResError \/
  ?m' l'. smart_coseq cs fr (ResCont m l) = ResCont m' l'
Proof
  Cases_on `cs` >> Cases_on `m` >> Cases_on `l` >> simp[smart_coseq_def] >>
  qmatch_goalsub_abbrev_tac `smart_coseq _ _ (ResCont _ (hd::_)) = _` >>
  Cases_on `hd` >> simp[smart_coseq_def]
QED

Theorem build_callframe_ok:
  !s f args. (!k. frame_ok k (build_callframe s f args))
Proof
  rpt gen_tac >> simp[build_callframe_def] >> Cases_on `s.functions f` >>
  Cases_on `k` >> simp[frame_ok_def, alist_range_def]
QED

Theorem build_cont_ok:
  !s f args.
    (!k. frame_ok k s.frame) ==> fun_ok s ==>
    EVERY syntax_ok (FST (build_cont s f args)) /\
    (!k. frame_ok k (SND (build_cont s f args)))
Proof
  rw[build_cont_def] >> Cases_on `s.functions f` >> gvs[]
    >- (gvs[fun_ok_def] >> first_x_assum $ qspec_then `f` assume_tac >> gvs[])
    >- (Cases_on `k` >> simp[frame_ok_def, alist_range_def])
QED

Theorem update_var_preserves:
  (update_var s x v).frame.coVar = s.frame.coVar /\
  (update_var s x v).frame.inCo = s.frame.inCo /\
  (update_var s x v).frame.cos = s.frame.cos /\
  (update_var s x v).functions = s.functions
Proof
  simp[update_var_def] >> rpt CASE_TAC >> simp[]
QED

Theorem update_var_preserves_frame_ok:
  frame_ok t s.frame <=> frame_ok t (update_var s x v).frame
Proof
  Cases_on `t` >> gvs[frame_ok_def, update_var_preserves]
QED

Theorem update_covar_preserves_frame_ok:
  !f v. (!k. frame_ok k f) <=> (!k. frame_ok k (f with coVar := v))
Proof
  rpt gen_tac >> iff_tac >> rw[] >> pop_assum $ qspec_then `k` mp_tac >>
  Cases_on `k` >> simp[frame_ok_def]
QED

Theorem alookup_del_none[simp]:
  ALOOKUP (ADELKEY k al) k = NONE
Proof
  Induct_on `al` >> simp[ADELKEY_def] >> simp[GSYM ADELKEY_def] >>
  Cases_on `h` >> Cases_on `q = k` >> simp[]
QED

Theorem alookup_with_del_same_no_del:
  ALOOKUP (ADELKEY k al) k' = SOME x ==> ALOOKUP al k' = SOME x
Proof
  Induct_on `al` >> simp[ADELKEY_def] >> simp[GSYM ADELKEY_def] >>
  Cases_on `h` >> Cases_on `q = k` >> rw[alookup_del_none]
QED

Theorem distinct_alist_del_subset:
  ALL_DISTINCT (MAP FST al) ==> alist_range (ADELKEY k al) ⊆ alist_range al
Proof
  simp[SUBSET_DEF] >> Induct_on `al` >> simp[ADELKEY_def] >>
  simp[GSYM ADELKEY_def] >> Cases_on `h` >> rw[] >> gvs[] >>
  pop_assum mp_tac >> simp[alist_range_def] >> rw[]
    >- (Cases_on `q = k'` >> fs[] >> qexists `k'` >> simp[] >>
        drule alookup_with_del_same_no_del >> simp[]
    )
    >- (drule alookup_with_del_same_no_del >> rw[] >> drule ALOOKUP_MEM >>
        rw[] >> qsuff_tac `MEM k' (MAP FST al)` >> rw[]
          >- (Cases_on `k = k'` >> gvs[] >> qexists `k'` >> simp[])
          >- (simp[MEM_MAP] >> qexists `(k', x)` >> simp[])
    )
QED

Theorem adel_preserves_distinct:
  ALL_DISTINCT (MAP FST al) ==> ALL_DISTINCT (MAP FST (ADELKEY k al))
Proof
  Induct_on `al` >> simp[ADELKEY_def] >> rw[] >>
  gvs[MEM_MAP, MEM_FILTER, ADELKEY_def]
QED

Theorem delete_co_preseves_frame_ok:
  !f co. frame_ok k f ==> frame_ok k (f with cos := ADELKEY co f.cos)
Proof
  rpt gen_tac >> Cases_on `k` >> simp[frame_ok_def] >> rw[] >>
  drule distinct_alist_del_subset >> disch_then $ qspec_then `co` assume_tac >>
  first_x_assum $ qspec_then `c` assume_tac >>
  gvs[SUBSET_DEF, adel_preserves_distinct]
QED

Theorem evaluate_none[simp]:
    pval 0 cs s = NONE /\ cval 0 c s = NONE /\ runco 0 co s = NONE
Proof
  rw[evaluate_def]
QED

Theorem fun_upd_dist_aux:
  !y. (λx. M (s⦇v ↦ v'⦈ x)) y = (λx. M (s x))⦇v ↦ M (v')⦈ y
Proof
  strip_tac >> simp[UPDATE_def] >> Cases_on `v=y` >> simp[]
QED

Theorem fun_upd_dist:
  (λx. M (s⦇v ↦ v'⦈ x)) = (λx. M (s x))⦇v ↦ M (v')⦈
Proof
  qspecl_then [`(λx. M (s⦇v ↦ v'⦈ x))`, `(λx. M (s x))⦇v ↦ M (v')⦈`]
    assume_tac (GSYM FUN_EQ_THM) >>
  assume_tac fun_upd_dist_aux >> gvs[]
QED

Theorem functions_invariant:
  (!t cs s. pval t cs s <> NONE ==>
    SOME s.functions = OPTION_MAP (state_functions ∘ SND) (pval t cs s)) /\
  (!t co s. runco t co s <> NONE ==>
    SOME s.functions = OPTION_MAP (state_functions ∘ SND) (runco t co s)) /\
  (!t c s. cval t c s <> NONE ==>
    SOME s.functions = OPTION_MAP (state_functions ∘ SND) (cval t c s))
Proof
  ho_match_mp_tac evaluate_ind >> rw[] >>
  gvs[evaluate_def, update_var_preserves] >> pop_assum mp_tac >>
  rpt CASE_TAC >> gvs[update_var_preserves]
QED

(*
    the purpose of this is to get frame_ok requantified in the same
    form at the end of the implication otherwise this is basically just
    the definition.
*)
Theorem frame_ok_dist:
  !f. (!k. frame_ok k f) ==>
    !x. x ∈ alist_range f.cos ==> (EVERY (EVERY syntax_ok ∘ FST) x) /\
    (!k. EVERY ((frame_ok k) ∘ SND) x)
Proof
  rw[] >> last_x_assum $ qspec_then `SUC k` mp_tac >> simp[frame_ok_def] >>
  rw[] >> pop_assum $ qspec_then `x` assume_tac >> gvs[] >>
  qspec_then `frame_ok k` assume_tac ETA_THM >> fs[]
QED

Theorem smart_coseq_preserves_ok:
  EVERY syntax_ok cs ==> (!k. frame_ok k fr) ==>
  EVERY ((EVERY syntax_ok) ∘ FST) l ==> (!k. EVERY ((frame_ok k) ∘ SND) l) ==>
  smart_coseq cs fr (ResCont m l) = ResCont m' l' ==>
  EVERY ((EVERY syntax_ok) ∘ FST) l' /\ (!k. EVERY ((frame_ok k) ∘ SND) l')
Proof
  Cases_on `cs` >> Cases_on `m` >> Cases_on `l` >>
  simp[smart_coseq_def] >> rw[] >> gvs[] >>
  qmatch_asmsub_abbrev_tac `smart_coseq _ _ (ResCont _ (hd::_)) = _` >>
  Cases_on `hd` >> gvs[smart_coseq_def]
QED

Theorem smart_coseq_preserves_frame_ok:
  (!k. frame_ok k fr) ==> (!k. EVERY ((frame_ok k) ∘ SND) l) ==>
  smart_coseq cs fr (ResCont m l) = ResCont m' l' ==>
  (!k. EVERY ((frame_ok k) ∘ SND) l')
Proof
  Cases_on `cs` >> Cases_on `m` >> Cases_on `l` >>
  simp[smart_coseq_def] >> rw[] >> gvs[] >>
  qmatch_asmsub_abbrev_tac `smart_coseq _ _ (ResCont _ (hd::_)) = _` >>
  Cases_on `hd` >> gvs[smart_coseq_def]
QED

Theorem smart_cowhile_preserves_frame_ok:
  (!k. frame_ok k fr) ==> (!k. EVERY ((frame_ok k) ∘ SND) l) ==>
  smart_cowhile w fr (ResCont m l) = ResCont m' l' ==>
  (!k. EVERY ((frame_ok k) ∘ SND) l')
Proof
  Cases_on `m` >> Cases_on `l` >> simp[smart_cowhile_def] >> rw[] >> gvs[] >>
  Cases_on `h` >> gvs[smart_cowhile_def]
QED

Theorem smart_cowhile_preserves_ok:
  syntax_ok w ==> (!k. frame_ok k fr) ==>
  EVERY ((EVERY syntax_ok) ∘ FST) l ==> (!k. EVERY ((frame_ok k) ∘ SND) l) ==>
  smart_cowhile w fr (ResCont m l) = ResCont m' l' ==>
  EVERY ((EVERY syntax_ok) ∘ FST) l' /\ (!k. EVERY ((frame_ok k) ∘ SND) l')
Proof
  Cases_on `m` >> Cases_on `l` >> simp[smart_cowhile_def] >>
  rw[] >> gvs[] >> Cases_on `h` >>
  gvs[smart_cowhile_def, syntax_ok_def, break_ok_def, continue_ok_def]
QED

Theorem smart_coseq_preserves_from_new_syntax_ok:
  from_new_syntax_ok m l ==>
  smart_coseq cs fr (ResCont m l) = ResCont m' l' ==>
  from_new_syntax_ok m' l'
Proof
  Cases_on `cs` >> Cases_on `m` >> Cases_on `l` >>
  simp[smart_coseq_def, from_new_syntax_ok_def] >>
  rw[] >> gvs[from_new_syntax_ok_def] >>
  qmatch_asmsub_abbrev_tac `smart_coseq _ _ (ResCont _ (hd::_)) = _` >>
  Cases_on `hd` >> gvs[smart_coseq_def, from_new_syntax_ok_def]
QED

Theorem smart_cowhile_preserves_from_new_syntax_ok:
  from_new_syntax_ok m l ==>
  smart_cowhile w fr (ResCont m l) = ResCont m' l' ==>
  from_new_syntax_ok m' l'
Proof
  Cases_on `m` >> Cases_on `l` >>
  simp[smart_cowhile_def, from_new_syntax_ok_def] >>
  rw[] >> gvs[from_new_syntax_ok_def] >> Cases_on `h` >>
  gvs[smart_cowhile_def, from_new_syntax_ok_def]
QED

Theorem smart_cowhile_creates_syntax_ok:
  syntax_ok w ==> from_new_syntax_ok m l ==>
  smart_cowhile w fr (ResCont m l) = ResCont m' l' ==>
  EVERY (EVERY syntax_ok ∘ FST) l'
Proof
  Cases_on `m` >> Cases_on `l` >>
  simp[smart_cowhile_def, from_new_syntax_ok_def] >>
  rw[] >> gvs[] >> Cases_on `h` >>
  gvs[smart_cowhile_def, from_new_syntax_ok_def,
      syntax_ok_def, break_ok_def, continue_ok_def]
QED

Theorem safe_co_preserves_frame_ok:
  !l co cos.
    EVERY (EVERY syntax_ok ∘ FST) l ==>
    (!k. EVERY (frame_ok k ∘ SND) l) ==>
    ALL_DISTINCT (MAP FST cos) ==>
    (!c. c ∈ alist_range cos ==>
         EVERY (EVERY syntax_ok ∘ FST) c ∧ (!k. EVERY ((frame_ok k) ∘ SND) c)) ==>
    ALL_DISTINCT (MAP FST (AFUPDKEY co (λ_. l) cos)) /\
    (!c. c ∈ alist_range (AFUPDKEY co (λ_. l) cos) ==>
         (EVERY (EVERY syntax_ok ∘ FST) c) /\ (!k. EVERY ((frame_ok k) ∘ SND) c))
Proof
  rpt gen_tac >> Induct_on `cos`
  >- simp[AFUPDKEY_def] >>
  qx_gen_tac ‘h’ >> Cases_on ‘h’ >>
  rpt (disch_then strip_assume_tac) >>
  qpat_x_assum ‘_ ⇒ _’
               (fn th =>
                  gvs[MEM_MAP, AFUPDKEY_def, alist_range_def, PULL_EXISTS, AllCaseEqs(),
                      DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
                  gvs[AllCaseEqs()] >>
                  assume_tac th) >>
  pop_assum mp_tac >>
  gvs[alist_range_def, PULL_EXISTS, AFUPDKEY_ALOOKUP, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem frame_ok_preserved:
  (!t cs s r z m frs. (!k. frame_ok k s.frame) ==> fun_ok s ==>
    (pval t cs s) = SOME (r, z) ==>
    (!k. frame_ok k z.frame) /\ (r = ResCont m frs ==>
      (!k. EVERY ((frame_ok k) ∘ SND) frs) /\ (from_new_syntax_ok m frs) /\
      (EVERY syntax_ok cs ==> (EVERY ((EVERY syntax_ok) ∘ FST) frs)))) /\
  (!t co s r z m frs. (!k. frame_ok k s.frame) ==> fun_ok s ==>
    (EVERY ((EVERY syntax_ok) ∘ FST) co) ==>
    (!k. EVERY ((frame_ok k) ∘ SND) co) ==> runco t co s = SOME (r, z) ==>
    (!k. frame_ok k z.frame) /\ (r = ResCont m frs ==>
      (EVERY ((EVERY syntax_ok) ∘ FST) frs) /\
      (!k. EVERY ((frame_ok k) ∘ SND) frs))) /\
  (!t c s r z m frs. (!k. frame_ok k s.frame) ==> fun_ok s ==>
    (cval t c s) = SOME (r, z) ==> (!k. frame_ok k z.frame) /\
    (r = ResCont m frs ==> (!k. EVERY ((frame_ok k) ∘ SND) frs) /\
      (from_new_syntax_ok m frs) /\
      (syntax_ok c ==> (EVERY ((EVERY syntax_ok) ∘ FST) frs))))
Proof
  ho_match_mp_tac evaluate_ind >> gvs[evaluate_def] >> rpt CONJ_TAC >>
  rpt gen_tac >> rpt $ disch_then strip_assume_tac >>
  rpt gen_tac >> rpt $ disch_then strip_assume_tac >> pop_assum mp_tac
    >- (rpt CASE_TAC >> rw[] >>
        rename [‘cval (SUC n) c s = SOME (_,r)’] >>
        qspecl_then [`SUC n`, `c`, `s`]
          assume_tac (cj 3 functions_invariant) >>
        gvs[fun_ok_def] >>
        gvs[FORALL_AND_THM]
        >- (drule smart_coseq_preserves_frame_ok >> metis_tac[])
        >- (drule smart_coseq_preserves_from_new_syntax_ok >> metis_tac[])
        >- (drule smart_coseq_preserves_ok >> metis_tac[]))
    >- (rpt CASE_TAC >> rw[] >> gvs[] >>
        rename [‘runco (SUC n) co s = SOME (_, r)’] >>
        qspecl_then [`SUC n`, `co`, `s`]
          assume_tac (cj 2 functions_invariant) >>
        gvs[fun_ok_def, GSYM update_covar_preserves_frame_ok, FORALL_AND_THM])
    >- (CASE_TAC >> rw[from_new_syntax_ok_def])
    >- (simp[GSYM update_var_preserves_frame_ok])
    >- (pop_assum mp_tac >> CASE_TAC >>
        simp[syntax_ok_def, break_ok_def, continue_ok_def, ETA_THM] >> rw[] >>
        qspecl_then [`break_ok`, `continue_ok`, `c1`]
          mp_tac (iffRL EVERY_CONJ) >>
        simp[GSYM syntax_ok_def, ETA_THM] >>
        qspecl_then [`break_ok`, `continue_ok`, `c2`]
          mp_tac (iffRL EVERY_CONJ) >>
        simp[GSYM syntax_ok_def, ETA_THM] >> rw[])
    >- (CASE_TAC >> rw[] >> gvs[FORALL_AND_THM] >>
        gvs[syntax_ok_def, break_ok_def, continue_ok_def])
    >- (rename [‘option_CASE (pval (SUC n) cs s)’] >>
        qspecl_then [`SUC n`, `cs`, `s`]
          assume_tac (cj 1 functions_invariant) >>
        CASE_TAC >> CASE_TAC >> Cases_on `q` >> rw[] >> gvs[fun_ok_def]
          >>~- ([`cval _ _ _ = _`],
                first_x_assum $ qspecl_then [`m`, `frs`] assume_tac >>
                gvs[syntax_ok_def, break_ok_def, continue_ok_def]
          ) >>
        first_x_assum $ qspecl_then [`m'`, `l`] assume_tac >> gvs[]
          >- (drule smart_cowhile_preserves_frame_ok >> metis_tac[])
          >- (drule smart_cowhile_preserves_from_new_syntax_ok >> metis_tac[])
          >- (`syntax_ok (While b cs')`
                by simp[syntax_ok_def, break_ok_def, continue_ok_def] >>
              drule smart_cowhile_creates_syntax_ok >> metis_tac[])
    )
    >- (CASE_TAC >> gvs[]
          >- (rw[] >> gvs[]) >>
        qspec_then `s.frame` assume_tac frame_ok_dist >> gvs[] >>
        pop_assum $ qspec_then `x` assume_tac >>
        gvs[alist_range_def, PULL_EXISTS] >>
        pop_assum $ qspec_then `co` assume_tac >> gvs[] >>
        rpt CASE_TAC >> rw[] >> gvs[delete_co_preseves_frame_ok] >>
        pop_assum $ qspecl_then [`m'`, `l`] assume_tac >> gvs[] >>
        qspec_then `s.frame` assume_tac frame_ok_dist >> gvs[] >>
        last_assum $ qspec_then `0` assume_tac >> gvs[frame_ok_def] >>
        qspecl_then [`l`, `co`, `s.frame.cos`]
          assume_tac safe_co_preserves_frame_ok >>
        gvs[] >> Cases_on `k` >> simp[frame_ok_def] >> metis_tac[]
    )
    >- (rw[] >> Cases_on `k` >> simp[frame_ok_def, insert_alist_def] >>
        pure_rewrite_tac[GSYM $ cj 2 alist_to_fmap_thm] >>
        simp[alist_range_def] >> gen_tac >> disch_then assume_tac >> gvs[] >>
        Cases_on `build_cont s fun args` >> Cases_on `co = k` >> gvs[]
          >>~- ([`ALOOKUP _ _ = _`],
                last_x_assum $ qspec_then `SUC n` assume_tac >>
                gvs[frame_ok_def, alist_range_def, PULL_EXISTS] >> metis_tac[]
          ) >>
        qspecl_then [`s`, `fun`, `args`] assume_tac build_cont_ok >> gvs[]
    )
    >- (rpt CASE_TAC >> disch_then assume_tac >> gvs[fun_ok_def] >>
        qspecl_then [`s`, `f`, `args`] assume_tac build_callframe_ok >>
        gvs[] >> rw[] >>
        last_x_assum $ qspecl_then [`m'`, `frs`] assume_tac >> gvs[] >>
        Cases_on `frs` >> simp[from_new_syntax_ok_def]
    )
    >- (rpt CASE_TAC >> disch_then assume_tac >> gvs[]
        >- (gen_tac >>
            qsuff_tac `frame_ok k (r' with frame := s.frame).frame` >>
            simp[iffLR update_var_preserves_frame_ok]
        )
        >- (disch_then assume_tac >>
            gvs[from_new_syntax_ok_def, syntax_ok_def,
                  break_ok_def, continue_ok_def]
        )
    )
    >- simp[iffLR update_var_preserves_frame_ok]
QED

Theorem ok_imp_no_impossible:
  (!t cs s. (!k. frame_ok k s.frame) ==> fun_ok s ==>
    OPTION_MAP FST (pval t cs s) <> SOME ResImpossible /\
    (EVERY syntax_ok cs ==> OPTION_MAP FST (pval t cs s) <> SOME ResBreak /\
    OPTION_MAP FST (pval t cs s) <> SOME ResContinue)) /\
  (!t co s. (!k. frame_ok k s.frame) ==> fun_ok s ==>
    (EVERY ((EVERY syntax_ok) ∘ FST) co) ==>
    (!k. EVERY ((frame_ok k) ∘ SND) co) ==>
    OPTION_MAP FST (runco t co s) <> SOME ResImpossible /\
    OPTION_MAP FST (runco t co s) <> SOME ResBreak /\
    OPTION_MAP FST (runco t co s) <> SOME ResContinue) /\
  (!t c s. (!k. frame_ok k s.frame) ==> fun_ok s ==>
    OPTION_MAP FST (cval t c s) <> SOME ResImpossible /\
    (syntax_ok c ==> OPTION_MAP FST (cval t c s) <> SOME ResBreak /\
    OPTION_MAP FST (cval t c s) <> SOME ResContinue))
Proof
  ho_match_mp_tac evaluate_ind >> gvs[evaluate_def] >>
  rpt CONJ_TAC >> rpt gen_tac >> rpt $ disch_then assume_tac
    >>~- ([`F`], gvs[syntax_ok_def, break_ok_def, continue_ok_def])
    >- (rpt CASE_TAC >> gvs[]
          >- (qspecl_then [`SUC v14`, `c`, `s`, `ResNone`, `r`]
                assume_tac (cj 3 frame_ok_preserved) >> gvs[] >>
              qspecl_then [`SUC v14`, `c`, `s`]
                assume_tac (cj 3 functions_invariant) >> gvs[fun_ok_def]
          )
          >- (Cases_on `cs` >> Cases_on `m` >>
              Cases_on `l` >> simp[smart_coseq_def] >>
              qmatch_goalsub_abbrev_tac `smart_coseq _ _ (ResCont _ (hd::_))` >>
              Cases_on `hd` >> simp[smart_coseq_def]
          )
    )
    >- (rpt CASE_TAC >> rw[] >> gvs[] >>
        qspecl_then [`SUC v27`, `co`, `s`]
          assume_tac (cj 2 functions_invariant) >> gvs[fun_ok_def] >>
        qspecl_then [`l`, `i`] assume_tac update_covar_preserves_frame_ok >>
        gvs[]
    )
    >- CASE_TAC
    >- (CASE_TAC >> gvs[] >> pop_assum kall_tac >> pop_assum mp_tac >>
        simp[syntax_ok_def, break_ok_def, continue_ok_def, ETA_THM] >>
        disch_then assume_tac >> gvs[] >>
        qspecl_then [`break_ok`, `continue_ok`, `c1`]
          mp_tac (iffRL EVERY_CONJ) >>
        simp[GSYM syntax_ok_def, ETA_THM] >>
        qspecl_then [`break_ok`, `continue_ok`, `c2`]
          mp_tac (iffRL EVERY_CONJ) >>
        simp[GSYM syntax_ok_def, ETA_THM]
    )
    >- (CASE_TAC >> gvs[syntax_ok_def, break_ok_def, continue_ok_def])
    >- (CASE_TAC >> CASE_TAC >> Cases_on `q` >> gvs[]
          >>~- ([`smart_cowhile _ _ _ ≠ _`],
                Cases_on `m` >> Cases_on `l` >> simp[smart_cowhile_def] >>
                Cases_on `h` >> simp[smart_cowhile_def]
          ) >>
        qmatch_asmsub_abbrev_tac `pval _ _ _ = SOME (res, _)` >>
        qspecl_then [`SUC v46`, `cs`, `s`, `res`, `r`]
          assume_tac (cj 1 frame_ok_preserved) >> gvs[] >>
        qspecl_then [`SUC v46`, `cs`, `s`]
          assume_tac (cj 1 functions_invariant) >>
        gvs[fun_ok_def, syntax_ok_def, break_ok_def, continue_ok_def]
    )
    >- (rpt CASE_TAC >> simp[] >>
        pop_assum mp_tac >> pop_assum mp_tac >> simp[] >>
        qspec_then `s.frame` mp_tac frame_ok_dist >>
        simp[alist_range_def, PULL_EXISTS] >>
        disch_then $ qspecl_then [`x`, `co`] assume_tac >>
        Cases_on `runco v47 x s` >> gvs[] >>
        Cases_on `x'` >> gvs[]
    )
    >- (rpt CASE_TAC >> simp[] >> pop_assum mp_tac >>
        qspecl_then [`s`, `f`, `args`] assume_tac build_callframe_ok >>
        gvs[fun_ok_def]
    )
    >- (rpt CASE_TAC >> gvs[])
QED

Theorem embedl_dist:
  embedl (l1 ++ l2) = (embedl l1) ++ (embedl l2)
Proof
  Induct_on `l1` >> simp[embed_def]
QED

Theorem embed_out:
  (!c t s.
    cval t (embed c) s = NONE \/
    ?z. cval t (embed c) s = SOME (ResNone, z)) /\
  (!l t s.
    pval t (embedl l) s = NONE \/
    ?z. pval t (embedl l) s = SOME (ResNone, z))
Proof
  Induct >> Cases_on `t` >> simp[]
    >>~- ([`While _ _`],
          Induct_on `n` >>
          (* SUC 0 = 1 so need to use pure_rewrite_tac first *)
          pure_rewrite_tac[evaluate_def, embed_def] >> simp[] >>
          rpt gen_tac >> CASE_TAC >> simp[evaluate_def] >>
          last_x_assum $ qspecl_then [`SUC n`, `s`] assume_tac >>
          fs[] >> CASE_TAC >>
          last_x_assum $ qspecl_then [`b`, `z`] assume_tac >>
          gvs[embed_def, evaluate_def]
  ) >>
  simp[evaluate_def, embed_def] >> rw[] >>
  last_x_assum $ qspecl_then [`SUC n`, `s`] assume_tac >> gvs[]
QED

(*follows from above*)
Theorem embed_out_corollary:
  (!c t s.
    cval t (embed c) s = NONE \/
    OPTION_MAP FST (cval t (embed c) s) = SOME ResNone) /\
  (!l t s.
    pval t (embedl l) s = NONE \/
    OPTION_MAP FST (pval t (embedl l) s) = SOME ResNone)
Proof
  rw[]
    >- (qspecl_then [`c`, `t`, `s`] mp_tac (cj 1 embed_out) >> rw[] >> simp[])
    >- (qspecl_then [`l`, `t`, `s`] mp_tac (cj 2 embed_out) >> rw[] >> simp[])
QED

Theorem pval_concat:
  !t l1 l2 s. pval t ((embedl l1) ++ (embedl l2)) s =
    OPTION_BIND (pval t (embedl l1) s) (\x. pval t (embedl l2) (SND x))
Proof
  Cases_on `t` >> simp[evaluate_def] >> Induct_on `l1` >>
  simp[embed_def, evaluate_def] >> rpt strip_tac >>
  qspecl_then [`h`, `SUC n`, `s`] assume_tac (cj 1 embed_out) >> fs[]
QED

Theorem preserve_lookup:
  get_lookup (empty_global with globals := (λx. SOME (s x))) = s
Proof
  simp[get_lookup_def, empty_global_def, empty_local_def, ETA_THM]
QED

Theorem preserve_lookup2:
  get_lookup (empty_global with frame :=
    empty_local with vars := (λx. SOME (s x))) = s
Proof
  simp[get_lookup_def, empty_global_def, empty_local_def, ETA_THM]
QED

Theorem preserve_state_conj:
  ((!c t z f.
    (!x. f x <> NONE) ==>
    cval t (embed c) (empty_global with globals := f) = SOME (ResNone, z) ==>
    (!x. z.globals x <> NONE) /\ z = empty_global with globals := z.globals) /\
  (!cs t z f.
    (!x. f x <> NONE) ==>
    pval t (embedl cs) (empty_global with globals := f) = SOME (ResNone, z) ==>
    (!x. z.globals x <> NONE) /\ z = empty_global with globals := z.globals)) /\
  ((!c t z f.
    (!x. f x <> NONE) ==>
    cval t (embed c) (empty_global with frame :=
      empty_local with vars := f) = SOME (ResNone, z) ==>
    (!x. z.frame.vars x <> NONE) /\
    z = empty_global with frame := empty_local with vars := z.frame.vars) /\
  (!cs t z f. (!x. f x <> NONE) ==>
    pval t (embedl cs) (empty_global with frame :=
      empty_local with vars := f) = SOME (ResNone, z) ==>
    (!x. z.frame.vars x <> NONE) /\
    z = empty_global with frame := empty_local with vars := z.frame.vars))
Proof
  conj_tac >> Induct >> Cases_on `t` >> simp[evaluate_def, embed_def] >>
  rpt gen_tac >> disch_then assume_tac
    >>~- ([`While _ _`],
          IF_CASES_TAC >> pop_assum kall_tac >> pop_assum mp_tac >>
          qid_spec_tac `z` >> gvs[] >> qid_spec_tac `f` >> Induct_on `n` >>
          simp[] >> rpt gen_tac >> disch_then assume_tac >>
          qmatch_goalsub_abbrev_tac `cval _ _ stuff` >>
          qspecl_then [`cs`, `SUC n`, `stuff`] assume_tac (cj 2 embed_out) >>
          unabbrev_all_tac >> gvs[evaluate_def] >> IF_CASES_TAC >>
          last_x_assum $ qspecl_then [`SUC n`, `z'`, `f`] assume_tac >> rfs[]
            >>~- ([`~ bval2 _ _`], disch_then assume_tac >> gvs[]) >>
          once_asm_rewrite_tac[] >> pop_assum mp_tac >>
          qmatch_goalsub_abbrev_tac `∀x. stuff x ≠ NONE` >>
          disch_then assume_tac >>
          last_x_assum $ qspecl_then [`stuff`, `z`] assume_tac >>
          unabbrev_all_tac >> rfs[]
    )
    >>~- ([`update_var`],
          gvs[evaluate_def, embed_def, pval_def, empty_global_def,
              empty_local_def, update_var_def, get_lookup_def] >>
          Cases_on `f s` >> rfs[] >> simp[APPLY_UPDATE_THM] >>
          Cases_on `s = x'` >> simp[]
    )
    >>~- ([`get_lookup`],
          IF_CASES_TAC >> gvs[] >>
          rpt (last_x_assum $ qspecl_then [`SUC n`, `z`, `f`] assume_tac) >>
          gvs[]
    ) >>
    qmatch_goalsub_abbrev_tac `cval _ _ stuff` >>
    qspecl_then [`c`, `SUC n`, `stuff`] assume_tac (cj 1 embed_out) >>
    unabbrev_all_tac >> gvs[] >>
    last_x_assum $ qspecl_then [`SUC n`, `z'`, `f`] assume_tac >> rfs[] >>
    once_asm_rewrite_tac[] >> pop_assum mp_tac >>
    qmatch_goalsub_abbrev_tac `∀x. stuff x <> NONE` >>
    rpt $ disch_then assume_tac >>
    last_x_assum $ qspecl_then [`SUC n`, `z`, `stuff`] assume_tac >> rfs[]
QED

(* reforming above theorem for easier use *)
Theorem preserve_state_conj2:
  (!c t z f.
    ((!x. f x <> NONE) ==>
    cval t (embed c) (empty_global with globals := f) = SOME (ResNone, z) ==>
    (!x. z.globals x <> NONE) /\ z = empty_global with globals := z.globals) /\
    ((!x. f x <> NONE) ==>
    cval t (embed c)
      (empty_global with frame := empty_local with vars := f) =
    SOME (ResNone, z) ==>
    (!x. z.frame.vars x <> NONE) /\
    z = empty_global with frame := empty_local with vars := z.frame.vars)) /\
  (!cs t z f.
    ((!x. f x <> NONE) ==>
    pval t (embedl cs) (empty_global with globals := f) = SOME (ResNone, z) ==>
    (!x. z.globals x <> NONE) /\ z = empty_global with globals := z.globals) /\
    ((!x. f x <> NONE) ==>
    pval t (embedl cs)
      (empty_global with frame := empty_local with vars := f) =
    SOME (ResNone, z) ==> (!x. z.frame.vars x <> NONE) /\
    z = empty_global with frame := empty_local with vars := z.frame.vars))
Proof
  conj_tac >> rpt gen_tac
    >- (qspecl_then [`c`,`t`,`z`,`f`] assume_tac (cj 1 preserve_state_conj) >>
        qspecl_then [`c`,`t`,`z`,`f`] assume_tac (cj 3 preserve_state_conj) >>
        simp[]
    )
    >- (qspecl_then [`cs`,`t`,`z`,`f`] assume_tac (cj 2 preserve_state_conj) >>
        qspecl_then [`cs`,`t`,`z`,`f`] assume_tac (cj 4 preserve_state_conj) >>
        simp[]
    )
QED

Theorem bexp_to_bexp2:
  bval b s = bval2 (embed_bexp b) (s, z)
Proof
  Induct_on `b` >> gvs[embed_bexp_def, bval_def, bval2_def]
QED

Theorem embed_while_conj:
  OPTION_MAP ((λf. f.globals) ∘ SND)
          (pval (SUC n) (embedl [While b cs]) z) =
        OPTION_MAP ((λf. f.globals) ∘ SND)
          (cval (SUC n) (While (embed_bexp b) (embedl cs)) z) /\
  OPTION_MAP ((λf. f.frame.vars) ∘ SND)
            (pval (SUC n) (embedl [While b cs]) z) =
          OPTION_MAP ((λf. f.frame.vars) ∘ SND)
            (cval (SUC n) (While (embed_bexp b) (embedl cs)) z)
Proof
  simp[embed_def, evaluate_def] >> IF_CASES_TAC >> simp[] >> conj_tac >>
  qid_spec_tac `z` >> Induct_on `n` >> simp[evaluate_def] >>
  gen_tac >> qspecl_then [`cs`, `SUC n`, `z'`] assume_tac (cj 2 embed_out) >>
  gvs[] >> IF_CASES_TAC >> simp[]
QED

Theorem listImp_to_coimp_conj:
  ((!t c s.
    OPTION_MAP (\f x. SOME $ f x) ((listImp$cval) t c s) =
    OPTION_MAP  ((\f. f.globals) o SND)
      ((coimp$cval) t (embed c)
        (empty_global with globals := (\x. SOME $ s x)))) /\
  (!t cs s.
    OPTION_MAP (\f x. SOME $ f x) ((listImp$pval) t cs s) =
    OPTION_MAP ((\f. f.globals) o SND)
      ((coimp$pval) t (embedl cs)
        (empty_global with globals := (\x. SOME $ s x))))) /\
  ((!t c s.
    OPTION_MAP (\f x. SOME $ f x) ((listImp$cval) t c s) =
    OPTION_MAP  ((\f. f.frame.vars) o SND)
      ((coimp$cval) t (embed c)
        (empty_global with
        frame := (empty_local with vars := (\x. SOME $ s x))))) /\
  (!t cs s.
    OPTION_MAP (\f x. SOME $ f x) ((listImp$pval) t cs s) =
    OPTION_MAP ((\f. f.frame.vars) o SND)
      ((coimp$pval) t (embedl cs)
        (empty_global with
        frame := (empty_local with vars := (\x. SOME $ s x))))))
Proof
  conj_tac >> ho_match_mp_tac pval_ind >> rw[]
    >>~- ([`bval`],
          simp[pval_def, embed_def, evaluate_def, preserve_lookup,
                preserve_lookup2, GSYM bexp_to_bexp2] >>
          CASE_TAC >> simp[embedl_dist, pval_concat] >> Cases_on `v10` >>
          simp[] >> once_rewrite_tac[evaluate_def] >>
          qmatch_goalsub_abbrev_tac `pval _ _ emp` >>
          qspecl_then [`cs`, `SUC n`, `emp`] assume_tac (cj 2 embed_out) >>
          gvs[] >> simp[embed_while_conj]
    )
    >>~- ([`pval _ (embedl (_::_))`],
          qmatch_goalsub_abbrev_tac `pval _ (embedl _) emp` >>
          simp[evaluate_def, embed_def, pval_def] >>
          qspecl_then [`c`, `SUC v26`, `emp`] assume_tac (cj 1 embed_out) >>
          Cases_on `cval (SUC v26) c s` >> gvs[] >>
          qspecl_then [`c`, `SUC v26`, `z'`, `(λx. SOME $ s x)`]
            assume_tac (cj 1 preserve_state_conj2) >>
          rfs[] >> pop_assum mp_tac >> pop_assum (assume_tac o GSYM) >>
          disch_then assume_tac >> once_asm_rewrite_tac[] >> simp[]
    )
    >> gvs[pval_def, embed_def, GSYM bexp_to_bexp2, evaluate_def,
            get_lookup_def, ETA_THM, empty_global_def, empty_local_def,
            update_var_def, fun_upd_dist]
QED

Theorem evaluate_mono:
  (!t1 cs s t2. t1 <= t2 ==> pval t1 cs s <> NONE ==>
    pval t1 cs s = pval t2 cs s) /\
  (!t1 co s t2. t1 <= t2 ==> runco t1 co s <> NONE ==>
    runco t1 co s = runco t2 co s) /\
  (!t1 c s t2. t1 <= t2 ==> cval t1 c s <> NONE ==>
    cval t1 c s = cval t2 c s)
Proof
  ho_match_mp_tac evaluate_ind >> rw[] >> Cases_on `t2` >> gvs[] >>
  pop_assum mp_tac >> simp[evaluate_def] >> CASE_TAC >> gvs[]
    >>~- ([`_ + _`],
          last_x_assum $ qspec_then `n` assume_tac >> rfs[] >>
          CASE_TAC >> gvs[] >> pop_assum $ assume_tac o GSYM >> simp[]
    ) >>
  last_x_assum $ qspec_then `SUC n` assume_tac >> rfs[] >>
  pop_assum $ assume_tac o GSYM >> simp[] >>
  CASE_TAC >> gvs[evaluate_def] >> CASE_TAC >> gvs[] >> CASE_TAC >> gvs[] >>
  last_x_assum $ qspec_then `SUC n` assume_tac >> gvs[evaluate_def]
QED

Theorem co_state:
  (!t cs s cs' l' fs' s'.
    pval t cs s = SOME (ResCont Old ((cs', l')::fs'), s') ==> s'.frame = l') /\
  (!t fs s. runco t fs s = runco t fs s) /\
  (!t c s cs' l' fs' s'.
    cval t c s = SOME (ResCont Old ((cs', l')::fs'), s') ==>
    case c of
      | Call f args =>
          OPTION_MAP (state_frame ∘ SND) (pval (t-1) (SND (s.functions f))
          (s with frame := (build_callframe s f args))) = SOME l'
      | _ => s'.frame = l')
Proof
  ho_match_mp_tac evaluate_ind >> rw[] >> Cases_on `s.functions fun` >>
  gvs[evaluate_def, AllCaseEqs()] >> Cases_on `cs` >> Cases_on `m` >>
  Cases_on `frames` >> gvs[smart_cowhile_def, smart_coseq_def] >>
  qmatch_asmsub_abbrev_tac `_ _ _ (ResCont _ (hd::_)) = _` >>
  Cases_on `hd` >> gvs[smart_coseq_def, smart_cowhile_def] >>
  Cases_on `c` >> gvs[evaluate_def, AllCaseEqs(), smart_coseq_def]
QED

Theorem inco_pres:
  (!t cs s k z.
    k <> ResError ==> k <> ResImpossible ==> pval t cs s = SOME (k, z) ==>
    s.frame.inCo = z.frame.inCo) /\
  (!t co s. runco t co s = runco t co s) /\
  (!t c s k z.
    k <> ResError ==> k <> ResImpossible ==> cval t c s = SOME (k, z) ==>
    s.frame.inCo = z.frame.inCo)
Proof
  ho_match_mp_tac evaluate_ind >> rw[] >>
  gvs[evaluate_def, update_var_preserves] >> pop_assum mp_tac >> rpt CASE_TAC >>
  rw[] >> gvs[evaluate_def, update_var_preserves]
QED

Theorem runco_frame_indifferent:
  !t co s f1 f2.
    co <> [] ==>
    runco t co (s with frame := f1) = runco t co (s with frame := f2)
Proof
  Cases_on `t` >> simp[] >> Induct_on `co` >> simp[] >> rw[] >> Cases_on `h` >>
  simp[evaluate_def] >> Cases_on `co` >> gvs[evaluate_def] >>
  pop_assum $ qspecl_then [`s`, `f1`, `f2`] assume_tac >> simp[]
QED

Theorem rescont_imp_inco:
  (!t cs s m fs z.
    pval t cs s = SOME (ResCont m fs, z) ==> s.frame.inCo /\ z.frame.inCo) /\
  (!t co s. runco t co s = runco t co s) /\
  (!t c s m fs z.
    cval t c s = SOME (ResCont m fs, z) ==> s.frame.inCo /\ z.frame.inCo)
Proof
  ho_match_mp_tac evaluate_ind >> rw[] >> gvs[evaluate_def] >>
  pop_assum mp_tac >> rpt CASE_TAC >> rw[] >> gvs[]
    >- (qspecl_then [`SUC v14`, `c`, `s`, `ResNone`, `r`]
          assume_tac (cj 3 inco_pres) >> simp[])
    >>~- ([`pval (SUC _) _ _ = SOME (_, _)`],
          qmatch_asmsub_abbrev_tac `pval (SUC _) _ _ = SOME (mything, _)` >>
          qspecl_then [`SUC v46`, `cs`, `s`, `mything`, `r`]
            assume_tac (cj 1 inco_pres) >>
          unabbrev_all_tac >>
          simp[]
    )
    >> Cases_on `s.functions f` >> gvs[build_callframe_def]
QED

Theorem call_preserves_frame:
  cval t (Call f args) s = SOME(k, z) ==> k <> ResError ==>
  k <> ResImpossible ==> s.frame = z.frame
Proof
  Cases_on `t` >> simp[evaluate_def] >> rpt CASE_TAC >> rw[] >> simp[]
QED

Theorem call_preserves_frame_gen:
  !t k z. cval t (Call f args) s = SOME(k, z) ==> k <> ResError ==>
  k <> ResImpossible ==> s.frame = z.frame
Proof
  rw[] >> drule call_preserves_frame >> simp[]
QED

(* proof that the set of global variables don't change *)
(* this should then imply that they are SOME iff SOME *)
Theorem set_globals_invariant:
  (!t cs s k z.
    pval t cs s = SOME (k, z) ==>
    !x. ((s.globals x) <> NONE) = ((z.globals x) <> NONE)) /\
  (!t co s k z.
    runco t co s = SOME (k, z) ==>
    !x. ((s.globals x) <> NONE) = ((z.globals x) <> NONE)) /\
  (!t c s k z.
    cval t c s = SOME (k, z) ==>
    !x. ((s.globals x) <> NONE) = ((z.globals x) <> NONE))
Proof
  ho_match_mp_tac evaluate_ind >> rw[] >> pop_assum mp_tac >>
  gvs[evaluate_def, AllCaseEqs(), PULL_EXISTS] >> dsimp[] >>
  rpt strip_tac >> gvs[] >> simp[update_var_def] >>
  rpt CASE_TAC >> rw[] >> simp[APPLY_UPDATE_THM] >>
  iff_tac >> rw[] >> strip_tac >> gvs[]
QED

Theorem assigncall_frame_indifferent:
  cval t (AssignCall x f args) s = SOME(k, z) ==>
  k <> ResError ==> k <> ResImpossible ==>
  z.frame = s.frame \/ ?v. z.frame = (update_var s x v).frame
Proof
  Cases_on `t` >> simp[Once evaluate_def] >> rpt CASE_TAC >> rw[]
    >>~- ([`ResReturn`],
          disj2_tac >> qexists_tac `i` >> qsuff_tac `s.frame = r.frame`
            >- (drule $ cj 3 set_globals_invariant >> rw[] >>
                simp[update_var_def] >> rpt CASE_TAC >> gvs[APPLY_UPDATE_THM] >>
                last_x_assum $ qspec_then `x` assume_tac >> gvs[]
            )
            >- (drule call_preserves_frame >> simp[])
    )
    >> disj1_tac >> drule call_preserves_frame >> simp[]
QED

Theorem safe_ghost:
  cval t (AssignCall x f args) s = SOME (ResCont m (fr::frs), s') ==>
  runco k frs z = SOME (ResReturn v, z') ==>
  SOME v =
    OPTION_MAP (localState_coVar ∘ state_frame ∘ SND) (runco k (fr::frs) z)
Proof
  Cases_on `t` >> simp[evaluate_def] >> rpt CASE_TAC >> rw[] >>
  Cases_on `k` >> gvs[evaluate_def, update_var_preserves]
QED

val _ = export_theory();
