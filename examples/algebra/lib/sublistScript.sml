(* ------------------------------------------------------------------------- *)
(* Sublist Theory                                                            *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "sublist";

(* ------------------------------------------------------------------------- *)


(* val _ = load "lcsymtacs"; *)
open lcsymtacs;

(* val _ = load "jcLib"; *)
open jcLib;

(* val _ = load "SatisfySimps"; (* for SatisfySimps.SATISFY_ss *) *)

(* Get dependent theories *)
(* val _ = load "helperListTheory"; *)
open helperListTheory;

(* open dependent theories *)
open listTheory arithmeticTheory;
open listRangeTheory; (* for listRangeINC_def *)


(* ------------------------------------------------------------------------- *)
(* Sublist Theory Documentation                                              *)
(* ------------------------------------------------------------------------- *)
(* Datatypes and overloads:
   l1 <= l2  = sublist l1 l2
*)
(* Definitions and Theorems (# are exported):

   Sublist:
   sublist_def           |- (!x. [] <= x <=> T) /\ (!t1 h1. h1::t1 <= [] <=> F) /\
                             !t2 t1 h2 h1. h1::t1 <= h2::t2 <=>
                              (h1 = h2) /\ t1 <= t2 \/ h1 <> h2 /\ h1::t1 <= t2
   sublist_nil           |- !p. [] <= p
   sublist_cons          |- !h p q. p <= q <=> h::p <= h::q
   sublist_of_nil        |- !p. p <= [] <=> (p = [])
   sublist_cons_eq       |- !h. (!p q. h::p <= q ==> p <= q) <=> !p q. p <= q ==> p <= h::q
   sublist_cons_remove   |- !h p q. h::p <= q ==> p <= q
   sublist_cons_include  |- !h p q. p <= q ==> p <= h::q
   sublist_length        |- !p q. p <= q ==> LENGTH p <= LENGTH q
   sublist_refl          |- !p. p <= p
   sublist_antisym       |- !p q. p <= q /\ q <= p ==> (p = q)
   sublist_trans         |- !p q r. p <= q /\ q <= r ==> p <= r
   sublist_snoc          |- !h p q. p <= q ==> SNOC h p <= SNOC h q
   sublist_member_sing   |- !ls x. MEM x ls ==> [x] <= ls
   sublist_take          |- !ls n. TAKE n ls <= ls
   sublist_drop          |- !ls n. DROP n ls <= ls
   sublist_tail          |- !ls. ls <> [] ==> TL ls <= ls
   sublist_front         |- !ls. ls <> [] ==> FRONT ls <= ls
   sublist_head_sing     |- !ls. ls <> [] ==> [HD ls] <= ls
   sublist_last_sing     |- !ls. ls <> [] ==> [LAST ls] <= ls
   sublist_every         |- !l ls. l <= ls ==> !P. EVERY P ls ==> EVERY P l

   More sublists:
   sublist_induct          |- !P. (!y. P [] y) /\
                                  (!h x y. P x y /\ x <= y ==> P (h::x) (h::y)) /\
                                  (!h x y. P x y /\ x <= y ==> P x (h::y)) ==> !x y. x <= y ==> P x y
   sublist_append_remove   |- !p q x. x ++ p <= q ==> p <= q
   sublist_append_include  |- !p q x. p <= q ==> p <= x ++ q
   sublist_append_suffix   |- !p q. p <= p ++ q
   sublist_append_prefix   |- !p q. p <= q ++ p
   sublist_prefix          |- !x p q. p <= q <=> x ++ p <= x ++ q
   sublist_prefix_nil      |- !p q. p ++ q <= q ==> (p = [])
   sublist_append_if       |- !p q. p <= q ==> !h. p ++ [h] <= q ++ [h]
   sublist_append_only_if  |- !p q h. p ++ [h] <= q ++ [h] ==> p <= q
   sublist_append_iff      |- !p q h. p <= q <=> p ++ [h] <= q ++ [h]
   sublist_suffix          |- !x p q. p <= q <=> p ++ x <= q ++ x
   sublist_append_pair     |- !a b c d. a <= b /\ c <= d ==> a ++ c <= b ++ d
   sublist_append_extend   |- !h t q. h::t <= q <=> ?x y. (q = x ++ h::y) /\ t <= y

   Applications of sublist:
   MAP_SUBLIST           |- !f p q. p <= q ==> MAP f p <= MAP f q
   SUM_SUBLIST           |- !p q. p <= q ==> SUM p <= SUM q
   listRangeINC_sublist  |- !m n. m < n ==> [m; n] <= [m .. n]
   listRangeLHI_sublist  |- !m n. m + 1 < n ==> [m; n - 1] <= [m ..< n]
*)

(* ------------------------------------------------------------------------- *)
(* Sublist: an order-preserving portion of a list                            *)
(* ------------------------------------------------------------------------- *)

(* Definition of sublist *)
val sublist_def = Define`
    (sublist [] x = T) /\
    (sublist (h1::t1) [] = F) /\
    (sublist (h1::t1) (h2::t2) <=>
       ((h1 = h2) /\ sublist t1 t2 \/ ~(h1 = h2) /\ sublist (h1::t1) t2))
`;

(* Overload sublist by infix operator *)
val _ = overload_on ("<=", ``sublist``);
(*
> sublist_def;
val it = |- (!x. [] <= x <=> T) /\ (!t1 h1. h1::t1 <= [] <=> F) /\
             !t2 t1 h2 h1. h1::t1 <= h2::t2 <=>
                (h1 = h2) /\ t1 <= t2 \/ h1 <> h2 /\ h1::t1 <= t2: thm
*)

(* Theorem: [] <= p *)
(* Proof: by sublist_def *)
val sublist_nil = store_thm(
  "sublist_nil",
  ``!p. [] <= p``,
  rw[sublist_def]);

(* Theorem: p <= q <=> h::p <= h::q *)
(* Proof: by sublist_def *)
val sublist_cons = store_thm(
  "sublist_cons",
  ``!h p q. p <= q <=> h::p <= h::q``,
  rw[sublist_def]);

(* Theorem: p <= [] <=> (p = []) *)
(* Proof:
   If p = [], then [] <= []           by sublist_nil
   If p = h::t, then h::t <= [] = F   by sublist_def
*)
val sublist_of_nil = store_thm(
  "sublist_of_nil",
  ``!p. p <= [] <=> (p = [])``,
  (Cases_on `p` >> rw[sublist_def]));

(* Theorem: (!p q. (h::p) <= q ==> p <= q) = (!p q. p <= q ==> p <= (h::q)) *)
(* Proof:
   If part: (!p q. (h::p) <= q ==> p <= q) ==> (!p q. p <= q ==> p <= (h::q))
               p <= q
        ==> h::p <= h::q     by sublist_cons
        ==>    p <= h::q     by implication
   Only-if part: (!p q. p <= q ==> p <= (h::q)) ==> (!p q. (h::p) <= q ==> p <= q)
            (h::p) <= q
        ==> (h::p) <= (h::q) by implication
        ==>      p <= q      by sublist_cons
*)
val sublist_cons_eq = store_thm(
  "sublist_cons_eq",
  ``!h. (!p q. (h::p) <= q ==> p <= q) = (!p q. p <= q ==> p <= (h::q))``,
  rw[EQ_IMP_THM] >>
  metis_tac[sublist_cons]);

(* Theorem: h::p <= q ==> p <= q *)
(* Proof:
   By induction on q.
   Base: !h p. h::p <= [] ==> p <= []
        True since h::p <= [] = F    by sublist_def

   Step: !h p. h::p <= q ==> p <= q ==>
         !h h' p. h'::p <= h::q ==> p <= h::q
        If p = [], true        by sublist_nil
        If p = h''::t,
            p <= h::q
        <=> (h'' = h) /\ t <= q \/ h'' <> h /\ h''::t <= q   by sublist_def
        If h'' = h, then t <= q        by sublist_def, induction hypothesis
        If h'' <> h, then h''::t <= q  by sublist_def, induction hypothesis
*)
val sublist_cons_remove = store_thm(
  "sublist_cons_remove",
  ``!h p q. h::p <= q ==> p <= q``,
  Induct_on `q` >-
  rw[sublist_def] >>
  rpt strip_tac >>
  (Cases_on `p` >> simp[sublist_def]) >>
  (Cases_on `h'' = h` >> metis_tac[sublist_def]));

(* Theorem: p <= q ==> p <= h::q *)
(* Proof: by sublist_cons_eq, sublist_cons_remove *)
val sublist_cons_include = store_thm(
  "sublist_cons_include",
  ``!h p q. p <= q ==> p <= h::q``,
  metis_tac[sublist_cons_eq, sublist_cons_remove]);

(* Theorem: p <= q ==> LENGTH p <= LENGTH q *)
(* Proof:
   By induction on q.
   Base: !p. p <= [] ==> LENGTH p <= LENGTH []
        Note p = []      by sublist_of_nil
        Thus true        by arithemtic
   Step: !p. p <= q ==> LENGTH p <= LENGTH q ==>
         !h p. p <= h::q ==> LENGTH p <= LENGTH (h::q)
         If p = [], LENGTH p = 0          by LENGTH
            and 0 <= LENGTH (h::q).
         If p = h'::t,
            If h = h',
               (h::t) <= (h::q)
            <=>    t <= q                 by sublist_def, same heads
            ==> LENGTH t <= LENGTH q      by inductive hypothesis
            ==> SUC(LENGTH t) <= SUC(LENGTH q)
              = LENGTH (h::t) <= LENGTH (h::q)
            If ~(h = h'),
                (h'::t) <= (h::q)
            <=> (h'::t) <= q                      by sublist_def, different heads
            ==> LENGTH (h'::t) <= LENGTH q        by inductive hypothesis
            ==> LENGTH (h'::t) <= SUC(LENGTH q)   by arithemtic
              = LENGTH (h'::t) <= LENGTH (h::q)
*)
val sublist_length = store_thm(
  "sublist_length",
  ``!p q. p <= q ==> LENGTH p <= LENGTH q``,
  Induct_on `q` >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `p` >> simp[]) >>
  (Cases_on `h = h'` >> fs[sublist_def]) >>
  `LENGTH (h'::t) <= LENGTH q` by rw[] >>
  `LENGTH t < LENGTH (h'::t)` by rw[LENGTH_TL_LT] >>
  decide_tac);

(* Theorem: [Reflexive] p <= p *)
(* Proof:
   By induction on p.
   Base: [] <= [], true                      by sublist_nil
   Step: p <= p ==> !h. h::p <= h::p, true   by sublist_cons
*)
val sublist_refl = store_thm(
  "sublist_refl",
  ``!p:'a list. p <= p``,
  Induct >-
  rw[sublist_nil] >>
  rw[GSYM sublist_cons]);
(* Faster just by definition *)
val sublist_refl = store_thm(
  "sublist_refl",
  ``!p:'a list. p <= p``,
  Induct >> rw[sublist_def]);

(* Theorem: [Anti-symmetric] !p q. (p <= q) /\ (q <= p) ==> (p = q) *)
(* Proof:
   By induction on q.
   Base: !p. p <= [] /\ [] <= p ==> (p = [])
       Note p <= [] already gives p = []   by sublist_of_nil
   Step: !p. p <= q /\ q <= p ==> (p = q) ==>
         !h p. p <= h::q /\ h::q <= p ==> (p = h::q)
       If p = [], h::q <= [] = F           by sublist_def
       If p = (h'::t),
          If h = h',
              ((h::t) <= (h::q)) /\ ((h::q) <= (h::t))
          <=> (t <= q) and (q <= t)        by sublist_def, same heads
          ==> t = q                        by inductive hypothesis
          <=> (h::t) = (h::q)              by list equality
          If ~(h = h'),
              ((h'::t) <= (h::q)) /\ ((h::q) <= (h'::t))
          <=> ((h'::t) <= q) /\ ((h::q) <= t)      by sublist_def, different heads
          ==> (LENGTH (h'::t) <= LENGTH q) /\
              (LENGTH (h::q) <= LENGTH t)          by sublist_length
          ==> (LENGTh t < LENGTH q) /\
              (LENGTH q < LENGTH t)                by LENGTH_TL_LT
            = F                                    by arithmetic
          Hence the implication is T.
*)
val sublist_antisym = store_thm(
  "sublist_antisym",
  ``!p q:'a list. p <= q /\ q <= p ==> (p = q)``,
  Induct_on `q` >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  Cases_on `p` >-
  fs[sublist_def] >>
  (Cases_on `h' = h` >> fs[sublist_def]) >>
  `LENGTH (h'::t) <= LENGTH q /\ LENGTH (h::q) <= LENGTH t` by rw[sublist_length] >>
  fs[LENGTH_TL_LT]);

(* Theorem [Transitive]: for all lists p, q, r; (p <= q) /\ (q <= r) ==> (p <= r) *)
(* Proof:
   By induction on list r and taking note of cases.
   By induction on r.
   Base: !p q. p <= q /\ q <= [] ==> p <= []
      Note q = []         by sublist_of_nil
        so p = []         by sublist_of_nil
   Step: !p q. p <= q /\ q <= r ==> p <= r ==>
         !h p q. p <= q /\ q <= h::r ==> p <= h::r
      If p = [], true     by sublist_nil
      If p = h'::t, to show:
         h'::t <= q /\ q <= h::r ==>
         (h' = h) /\ t <= r \/
         h' <> h /\ h'::t <= r    by sublist_def
      If q = [], [] <= h::r = F   by sublist_def
      If q = h''::t', this reduces to:
      (1) h' = h'' /\ t <= t' /\ h'' = h /\ t' <= r ==> t <= r
          Note t <= t' /\ t' <= r ==> t <= r     by induction hypothesis
      (2) h' = h'' /\ t <= t' /\ h'' <> h /\ h''::t' <= r ==> h''::t <= r
          Note t <= t' ==> h''::t <= h''::t'     by sublist_cons
          With h''::t' <= r ==> h''::t <= r      by induction hypothesis
      (3) h' <> h'' /\ h'::t <= t' /\ h'' = h /\ t' <= r ==>
          (h' = h) /\ t <= r \/ h' <> h /\ h'::t <= r
          Note h'::t <= t' ==> t <= t'           by sublist_cons_remove
          With t' <= r ==> t <= r                by induction hypothesis
          Or simply h'::t <= t' /\ t' <= r
                    ==> h'::t <= r               by induction hypothesis
          Hence this is true.
      (4) h' <> h'' /\ h'::t <= t' /\ h'' <> h /\ h''::t' <= r ==>
          (h' = h) /\ t <= r \/ h' <> h /\ h'::t <= r
          Same reasoning as (3).
*)
val sublist_trans = store_thm(
  "sublist_trans",
  ``!p q r:'a list. p <= q /\ q <= r ==> p <= r``,
  Induct_on `r` >-
  fs[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `p` >> fs[sublist_def]) >>
  (Cases_on `q` >> fs[sublist_def]) >-
  metis_tac[] >-
  metis_tac[sublist_cons] >-
  metis_tac[sublist_cons_remove] >>
  metis_tac[sublist_cons_remove]);

(* The above theorems show that sublist is a partial ordering. *)

(* Theorem: p <= q ==> SNOC h p <= SNOC h q *)
(* Proof:
   By induction on q.
   Base: !h p. p <= [] ==> SNOC h p <= SNOC h []
       Note p = []                    by sublist_of_nil
       Thus SNOC h [] <= SNOC h []    by sublist_refl
   Step: !h p. p <= q ==> SNOC h p <= SNOC h q ==>
         !h h' p. p <= h::q ==> SNOC h' p <= SNOC h' (h::q)
       If p = [],
          Note [] <= q                by sublist_nil
          Thus SNOC h' []
            <= SNOC h' q              by induction hypothesis
            <= h::SNOC h' q           by sublist_cons_include
             = SNOC h' (h::q)         by SNOC
       If p = h''::t,
          If h = h'',
          Then t <= q                 by sublist_def, same heads
           ==>      SNOC h' t <= SNOC h' q        by induction hypothesis
           ==>   h::SNOC h' t <= h::SNOC h' q     by rw[sublist_cons
            or SNOC h' (h::t) <= SNOC h' (h::q)   by SNOC
            or      SNOC h' p <= SNOC h' (h::q)   by p = h::t
          If h <> h'',
          Then         p <= q              by sublist_def, different heads
           ==> SNOC h' p <= SNOC h' q      by induction hypothesis
           ==> SNOC h' p <= h::SNOC h' q   by sublist_cons_include
*)
val sublist_snoc = store_thm(
  "sublist_snoc",
  ``!h p q. p <= q ==> SNOC h p <= SNOC h q``,
  Induct_on `q` >-
  rw[sublist_of_nil, sublist_refl] >>
  rw[sublist_def] >>
  Cases_on `p` >-
  rw[sublist_nil, sublist_cons_include] >>
  metis_tac[sublist_def, sublist_cons, SNOC]);

(* Theorem: MEM x ls ==> [x] <= ls *)
(* Proof:
   By induction on ls.
   Base: !x. MEM x [] ==> [x] <= []
      True since MEM x [] = F.
   Step: !x. MEM x ls ==> [x] <= ls ==>
         !h x. MEM x (h::ls) ==> [x] <= h::ls
      If x = h,
         Then [h] <= h::ls     by sublist_nil, sublist_cons
      If x <> h,
         Then MEM h ls         by MEM x (h::ls)
          ==> [x] <= ls        by induction hypothesis
          ==> [x] <= h::ls     by sublist_cons_include
*)
val sublist_member_sing = store_thm(
  "sublist_member_sing",
  ``!ls x. MEM x ls ==> [x] <= ls``,
  Induct >-
  rw[] >>
  rw[] >-
  rw[sublist_nil, GSYM sublist_cons] >>
  rw[sublist_cons_include]);

(* Theorem: TAKE n ls <= ls *)
(* Proof:
   By induction on ls.
   Base: !n. TAKE n [] <= []
      LHS = TAKE n [] = []   by TAKE_def
          <= [] = RHS        by sublist_nil
   Step: !n. TAKE n ls <= ls ==> !h n. TAKE n (h::ls) <= h::ls
      If n = 0,
         TAKE 0 (h::ls)
       = []                  by TAKE_def
      <= h::ls               by sublist_nil
      If n <> 0,
         TAKE n (h::ls)
       = h::TAKE (n - 1) ls             by TAKE_def
       Now    TAKE (n - 1) ls <= ls     by induction hypothesis
      Thus h::TAKE (n - 1) ls <= h::ls  by sublist_cons
*)
val sublist_take = store_thm(
  "sublist_take",
  ``!ls n. TAKE n ls <= ls``,
  Induct >-
  rw[sublist_nil] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[sublist_nil] >>
  rw[GSYM sublist_cons]);

(* Theorem: DROP n ls <= ls *)
(* Proof:
   By induction on ls.
   Base: !n. DROP n [] <= []
      LHS = DROP n [] = []   by DROP_def
          <= [] = RHS        by sublist_nil
   Step: !n. DROP n ls <= ls ==> !h n. DROP n (h::ls) <= h::ls
      If n = 0,
         DROP 0 (h::ls)
       = h::ls               by DROP_def
      <= h::ls               by sublist_refl
      If n <> 0,
         DROP n (h::ls)
       = DROP n ls           by DROP_def
      <= ls                  by induction hypothesis
      <= h::ls               by sublist_cons_include
*)
val sublist_drop = store_thm(
  "sublist_drop",
  ``!ls n. DROP n ls <= ls``,
  Induct >-
  rw[sublist_nil] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[sublist_refl] >>
  rw[sublist_cons_include]);

(* Theorem: ls <> [] ==> TL ls <= ls *)
(* Proof:
   Note TL ls = DROP 1 ls    by TAIL_BY_DROP, ls <> []
   Thus TL ls <= ls          by sublist_drop
*)
val sublist_tail = store_thm(
  "sublist_tail",
  ``!ls. ls <> [] ==> TL ls <= ls``,
  rw[TAIL_BY_DROP, sublist_drop]);

(* Theorem: ls <> [] ==> FRONT ls <= ls *)
(* Proof:
   Note FRONT ls = TAKE (LENGTH ls - 1) ls   by FRONT_BY_TAKE
     so FRONT ls <= ls                       by sublist_take
*)
val sublist_front = store_thm(
  "sublist_front",
  ``!ls. ls <> [] ==> FRONT ls <= ls``,
  rw[FRONT_BY_TAKE, sublist_take]);

(* Theorem: ls <> [] ==> [HD ls] <= ls *)
(* Proof: HEAD_MEM, sublist_member_sing *)
val sublist_head_sing = store_thm(
  "sublist_head_sing",
  ``!ls. ls <> [] ==> [HD ls] <= ls``,
  rw[HEAD_MEM, sublist_member_sing]);

(* Theorem: ls <> [] ==> [LAST ls] <= ls *)
(* Proof: LAST_MEM, sublist_member_sing *)
val sublist_last_sing = store_thm(
  "sublist_last_sing",
  ``!ls. ls <> [] ==> [LAST ls] <= ls``,
  rw[LAST_MEM, sublist_member_sing]);

(* Theorem: l <= ls ==> !P. EVERY P ls ==> EVERY P l` *)
(* Proof:
   By induction on ls.
   Base: !l. l <= [] ==> !P. EVERY P [] ==> EVERY P l
        Note l <= [] ==> l = []        by sublist_of_nil
         and EVERY P [] = T            by implication, or EVERY_DEF
   Step:  !l. l <= ls ==> !P. EVERY P ls ==> EVERY P l ==>
          !h l. l <= h::ls ==> !P. EVERY P (h::ls) ==> EVERY P l
         l <= h::ls
        If l = [], then EVERY P [] = T    by EVERY_DEF
        Otherwise, let l = k::t           by list_CASES
        Note EVERY P (h::ls)
         ==> P h /\ EVERY P ls            by EVERY_DEF
        Then k::t <= h::ls
         ==> k = h /\ t <= ls
          or k <> h /\ k::t <= ls         by sublist_def
        For the first case, h = k,
            P k /\ EVERY P t              by induction hypothesis
        ==> EVERY P (k::t) = EVERY P l    by EVERY_DEF
        For the second case, h <> k,
            EVERY P (k::t) = EVERY P l    by induction hypothesis
*)
val sublist_every = store_thm(
  "sublist_every",
  ``!l ls. l <= ls ==> !P. EVERY P ls ==> EVERY P l``,
  Induct_on `ls` >-
  rw[sublist_of_nil] >>
  (Cases_on `l` >> simp[]) >>
  metis_tac[sublist_def, EVERY_DEF]);

(* ------------------------------------------------------------------------- *)
(* More sublists, applying partial order properties                          *)
(* ------------------------------------------------------------------------- *)

(* Observation:
When doing induction proofs on sublists about p <= q,
Always induct on q, then take cases on p.
*)

(* The following induction theorem is already present during definition:
> theorem "sublist_ind";
val it = |- !P. (!x. P [] x) /\ (!h1 t1. P (h1::t1) []) /\
                (!h1 t1 h2 t2. P t1 t2 /\ P (h1::t1) t2 ==> P (h1::t1) (h2::t2)) ==>
            !v v1. P v v1: thm

Just prove it as an exercise.
*)

(* Theorem: [Induction] For any property P satisfying,
   (a) !y. P [] y = T
   (b) !h x y. P x y /\ sublist x y ==> P (h::x) (h::y)
   (c) !h x y. P x y /\ sublist x y ==> P x (h::y)
   then  !x y. sublist x y ==> P x y.
*)
(* Proof:
   By induction on y.
   Base: !x. x <= [] ==> P x []
      Note x = []            by sublist_of_nil
       and P [] [] = T       by given
   Step: !x. x <= y ==> P x y ==>
         !h x. x <= h::y ==> P x (h::y)
      If x = [], then [] <= h::y = F      by sublist_def
      If x = h'::t,
         If h' = h, t <= y                by sublist_def, same heads
            Thus P t y                    by induction hypothesis
             and P t y /\ t <= y ==> P (h::t) (h::y) = P x (h::y)
         If h' <> h, x <= y               by sublist_def, different heads
            Thus P x y                    by induction hypothesis
             and P x y /\ x <= y ==> P x (h::y).
*)
val sublist_induct = store_thm(
  "sublist_induct",
  ``!P. (!y. P [] y) /\
       (!h x y. P x y /\ x <= y ==> P (h::x) (h::y)) /\
       (!h x y. P x y /\ x <= y ==> P x (h::y)) ==>
        !x y. x <= y ==> P x y``,
  ntac 2 strip_tac >>
  Induct_on `y` >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `x` >> fs[sublist_def]));

(* Theorem: [Eliminate append from left]: (x ++ p) <= q ==> sublist p <= q *)
(* Proof:
   By induction on the extra list x.
   The induction step follows from sublist_cons_remove.

   By induction on x.
   Base: !p q. [] ++ p <= q ==> p <= q
       True since [] ++ p = p     by APPEND
   Step: !p q. x ++ p <= q ==> p <= q ==>
         !h p q. h::x ++ p <= q ==> p <= q
            h::x ++ p <= q
        = h::(x ++ p) <= q        by APPEND
       ==>   (x ++ p) <= q        by sublist_cons_remove
       ==>          p <= q        by induction hypothesis
*)
val sublist_append_remove = store_thm(
  "sublist_append_remove",
  ``!p q x. x ++ p <= q ==> p <= q``,
  Induct_on `x` >> metis_tac[sublist_cons_remove, APPEND]);

(* Theorem: [Include append to right] p <= q ==> p <= (x ++ q) *)
(* Proof:
   By induction on list x.
   The induction step follows by sublist_cons_include.

   By induction on x.
   Base: !p q. p <= q ==> p <= [] ++ q
       True since [] ++ q = q     by APPEND
   Step: !p q. p <= q ==> p <= x ++ q ==>
         !h p q. p <= q ==> p <= h::x ++ q
             p <= q
       ==>   p <= x ++ q          by induction hypothesis
       ==>   p <= h::(x ++ q)     by sublist_cons_include
         =   p <= h::x ++ q       by APPEND
*)
val sublist_append_include = store_thm(
  "sublist_append_include",
  ``!p q x. p <= q ==> p <= x ++ q``,
  Induct_on `x` >> metis_tac[sublist_cons_include, APPEND]);

(* Theorem: [append after] p <= (p ++ q) *)
(* Proof:
   By induction on list p, and note that p and (p ++ q) have the same head.
   Base: !q. [] <= [] ++ q, true    by sublist_nil
   Step: !q. p <= p ++ q ==> !h q. h::p <= h::p ++ q
               p <= p ++ q          by induction hypothesis
        ==> h::p <= h::(p ++ q)     by sublist_cons
        ==> h::p <= h::p ++ q       by APPEND
*)
val sublist_append_suffix = store_thm(
  "sublist_append_suffix",
  ``!p q. p <= p ++ q``,
  Induct_on `p` >> rw[sublist_def]);

(* Theorem: [append before] p <= (q ++ p) *)
(* Proof:
   By induction on q.
   Base: !p. p <= [] ++ p
      Note [] ++ p = p       by APPEND
       and p <= p            by sublist_refl
   Step: !p. p <= q ++ p ==> !h p. p <= h::q ++ p
           p <= q ++ p       by induction hypothesis
       ==> p <= h::(q ++ p)  by sublist_cons_include
        =  p <= h::q ++ p    by APPEND
*)
val sublist_append_prefix = store_thm(
  "sublist_append_prefix",
  ``!p q. p <= q ++ p``,
  Induct_on `q` >-
  rw[sublist_refl] >>
  rw[sublist_cons_include]);

(* Theorem: [prefix append] p <= q <=> (x ++ p) <= (x ++ q) *)
(* Proof:
   By induction on x.
   Base: !p q. p <= q <=> [] ++ p <= [] ++ q
      Since [] ++ p = p /\ [] ++ q = q           by APPEND
      This is trivially true.
   Step: !p q. p <= q <=> x ++ p <= x ++ q ==>
         !h p q. p <= q <=> h::x ++ p <= h::x ++ q
         p <= q <=>      x ++ p <= x ++ q        by induction hypothesis
                <=> h::(x ++ p) <= h::(x ++ q)   by sublist_cons
                <=>   h::x ++ p <= h::x ++ q     by APPEND
*)
val sublist_prefix = store_thm(
  "sublist_prefix",
  ``!x p q. p <= q <=> (x ++ p) <= (x ++ q)``,
  Induct_on `x` >> metis_tac[sublist_cons, APPEND]);

(* Theorem: [no append to left] !p q. (p ++ q) <= q ==> p = [] *)
(* Proof:
   By induction on q.
   Base: !p. p ++ [] <= [] ==> (p = [])
      Note p ++ [] = p         by APPEND
       and p <= [] ==> p = []  by sublist_of_nil
   Step: !p. p ++ q <= q ==> (p = []) ==>
         !h p. p ++ h::q <= h::q ==> (p = [])
      If p = [], true trivially.
      If p = h'::t,
          (h'::t) ++ (h::q) <= h::q
         =  h'::(t ++ h::q) <= h::q       by APPEND
         If h' = h,
            Then       t ++ h::q <= q     by sublist_def, same heads
              or (t ++ [h]) ++ q <= q     by APPEND
             ==>     t ++ [h] = []        by induction hypothesis
            which is F, hence h' <> h.
         If h' <> h,
            Then       p ++ h::q <= q     by sublist_def, different heads
              or (p ++ [h]) ++ q <= q     by APPEND
             ==> (p ++ [h]) = []          by induction hypothesis
             which is F, hence neither h' <> h.
         All these shows that p = h'::t is impossible.
*)
val sublist_prefix_nil = store_thm(
  "sublist_prefix_nil",
  ``!p q. (p ++ q) <= q ==> (p = [])``,
  Induct_on `q` >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `p` >> fs[sublist_def]) >| [
    `t ++ h::q = (t ++ [h])++ q` by rw[] >>
    `t ++ [h] <> []` by rw[] >>
    metis_tac[],
    `(t ++ h::q) <= q` by metis_tac[sublist_cons_remove] >>
    `t ++ h::q = (t ++ [h])++ q` by rw[] >>
    `t ++ [h] <> []` by rw[] >>
    metis_tac[]
  ]);

(* Theorem: [tail append - if] p <= q ==> (p ++ [h]) <= (q ++ [h]) *)
(* Proof:
   By sublist induction, this is to show:
   (1) [h] <= q ++ [h]
       Note [h] <= [h]         by sublist_refl
        ==> [h] <= q ++ [h]    by sublist_append_prefix
   (2) h::(p ++ [h']) <= h::(q ++ [h'])
       Note      p ++ [h'] <= q ++ [h']        by induction hypothesis
        ==> h::(p ++ [h']) <= h::(q ++ [h'])   by sublist_cons
   (3) p ++ [h'] <= h::(q ++ [h'])
       Note   p ++ [h'] <= q ++ [h']           by induction hypothesis
        ==>   p ++ [h'] <= h::(q + [h'])       by sublist_cons_include
*)
(* First method *)
val sublist_append_if = store_thm(
  "sublist_append_if",
  ``!p q h. p <= q ==> (p ++ [h]) <= (q ++ [h])``,
  Induct_on `q` >-
  rw[sublist_of_nil, sublist_refl] >>
  rpt strip_tac >>
  (Cases_on `p` >> fs[sublist_def]) >-
  (Cases_on `h' = h` >> rw[sublist_append_prefix]) >>
  metis_tac[APPEND]);
(* Second method -- change goal to match *)
val sublist_append_if = store_thm(
  "sublist_append_if",
  ``!p q. p <= q ==> !h. (p ++ [h]) <= (q ++ [h])``,
  ho_match_mp_tac sublist_induct >>
  rw[] >-
  rw[sublist_refl, sublist_append_prefix] >-
  metis_tac[sublist_cons] >>
  rw[sublist_cons_include]);
(* Third method *)
val sublist_append_if = store_thm(
  "sublist_append_if",
  ``!p q h. p <= q ==> (p ++ [h]) <= (q ++ [h])``,
  rw[sublist_snoc, GSYM SNOC_APPEND]);

(* Theorem: [tail append - only if] p ++ [h] <= q ++ [h] ==> p <= q *)
(* Proof:
   By induction on q.
   Base: !p h. p ++ [h] <= [] ++ [h] ==> p <= []
       Note [] ++ [h] = [h]                  by APPEND
        and p ++ [h] <= [h] ==> p = []       by sublist_prefix_nil
        and [] <= []                         by sublist_nil
   Step: !p h. p ++ [h] <= q ++ [h] ==> p <= q ==>
         !h p h'. p ++ [h'] <= h::q ++ [h'] ==> p <= h::q
       If p = [], [h'] <= h::q ++ [h'] = F    by sublist_def
       If p = h''::t,
          h''::t ++ [h'] = h''::(t ++ [h'])   by APPEND
          If h'' = h',
             Then t ++ [h'] <= q ++ [h']      by sublist_def, same heads
              ==>         t <= q              by induction hypothesis
          If h'' <> h',
             Then h''::t ++ [h'] <= q ++ [h'] by sublist_def, different heads
              ==>         h''::t <= q         by induction hypothesis
*)
val sublist_append_only_if = store_thm(
  "sublist_append_only_if",
  ``!p q h. (p ++ [h]) <= (q ++ [h]) ==> p <= q``,
  Induct_on `q` >-
  metis_tac[sublist_prefix_nil, sublist_nil, APPEND] >>
  rpt strip_tac >>
  (Cases_on `p` >> fs[sublist_def]) >-
  metis_tac[] >>
  `h''::(t ++ [h']) = (h''::t) ++ [h']` by rw[] >>
  metis_tac[]);

(* Theorem: [tail append] p <= q <=> p ++ [h] <= q ++ [h] *)
(* Proof: by sublist_append_if, sublist_append_only_if *)
val sublist_append_iff = store_thm(
  "sublist_append_iff",
  ``!p q h. p <= q <=> (p ++ [h]) <= (q ++ [h])``,
  metis_tac[sublist_append_if, sublist_append_only_if]);

(* Theorem: [suffix append] sublist p q ==> sublist (p ++ x) (q ++ x) *)
(* Proof:
   By induction on x.
   Base: !p q. p <= q <=> p ++ [] <= q ++ []
      True by p ++ [] = p, q ++ [] = q           by APPEND
   Step: !p q. p <= q <=> p ++ x <= q ++ x ==>
         !h p q. p <= q <=> p ++ h::x <= q ++ h::x
                         p <= q
       <=>      (p ++ [h]) <= (q ++ [h])         by sublist_append_iff
       <=> (p ++ [h]) ++ x <= (q ++ [h]) ++ x    by induction hypothesis
       <=>     p ++ (h::x) <= q ++ (h::x)        by APPEND
*)
val sublist_suffix = store_thm(
  "sublist_suffix",
  ``!x p q. p <= q <=> (p ++ x) <= (q ++ x)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  `!z. z ++ h::x = (z ++ [h]) ++ x` by rw[] >>
  metis_tac[sublist_append_iff]);

(* Theorem : (a <= b) /\ (c <= d) ==> (a ++ c) <= (b ++ d) *)
(* Proof:
   Note a ++ c <= a ++ d    by sublist_prefix
    and a ++ d <= b ++ d    by sublist_suffix
    ==> a ++ c <= b ++ d    by sublist_trans
*)
val sublist_append_pair = store_thm(
  "sublist_append_pair",
  ``!a b c d. (a <= b) /\ (c <= d) ==> (a ++ c) <= (b ++ d)``,
  metis_tac[sublist_prefix, sublist_suffix, sublist_trans]);

(* Theorem: [Extended Append, or Decomposition] (h::t) <= q <=> ?x y. (q = x ++ (h::y)) /\ (t <= y) *)
(* Proof:
   By induction on list q.
   Base case is to prove:
     sublist (h::t) []  <=> ?x y. ([] = x ++ (h::y)) /\ (sublist t y)
     Hypothesis sublist (h::t) [] is F by SUBLIST_NIL.
     In the conclusion, [] cannot be decomposed, hence implication is valid.
   Step case is to prove:
     (sublist (h::t) q  <=> ?x y. (q = x ++ (h::y)) /\ (sublist t y)) ==>
     (sublist (h::t) (h'::q)  <=> ?x y. (h'::q = x ++ (h::y)) /\ (sublist t y))
     Applying SUBLIST definition and split the if-and-only-if parts, there are 4 cases:
     When h = h', if part:
       sublist (h::t) (h::q) ==> ?x y. (h::q = x ++ (h::y)) /\ (sublist t y)
       For this case, choose x=[], y=q, and sublist (h::t) (h::q) = sublist t q, by SUBLIST same head.
     When h = h', only-if part:
       ?x y. (h::q = x ++ (h::y)) /\ (sublist t y) ==> sublist (h::t) (h::q)
       Take cases on x.
       When x = [],
         h::q = h::y ==> q = y,
         hence sublist t y = sublist t q ==> sublist (h::t) (h::q) by SUBLIST same head.
       When x = h''::t',
         h::q = (h''::t') ++ (h::y) = h''::(t' ++ (h::y)) ==>
         q = t' ++ (h::y),
         hence sublist t y ==> sublist t q (by SUBLIST_APPENDR_I) ==> sublist (h::t) (h::q).
     When ~(h=h'), if part:
       sublist (h::t) (h'::q) ==> ?x y. (h'::q = x ++ (h::y)) /\ (sublist t y)
       From hypothesis,
             sublist (h::t) (h'::q)
           = sublist (h::t) q           when ~(h=h'), by SUBLIST definition
         ==> ?x1 y1. (q = x1 ++ (h::y1)) /\ (sublist t y1))  by inductive hypothesis
         Now (h'::q) = (h'::(x1 ++ (h::y1)) = (h'::x1) ++ (h::y1) by APPEND associativity
         So taking x = h'::x1, y = y1, this gives the conclusion.
     When ~(h=h'), only-if part:
       ?x y. (h'::q = x ++ (h::y)) /\ (sublist t y) ==> sublist (h::t) (h'::q)
       The case x = [] is impossible by list equality, since ~(h=h').
       Hence x = h'::t', giving:
            q = t'++(h::y) /\ (sublist t y)
          = sublist (h::t) q              by inductive hypothesis (only-if)
        ==> sublist (h::t) (h'::q)        by SUBLIST, different head.
*)
val sublist_append_extend = store_thm(
  "sublist_append_extend",
  ``!h t q. h::t <= q  <=> ?x y. (q = x ++ (h::y)) /\ (t <= y)``,
  ntac 2 strip_tac >>
  Induct >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `h = h'` >> rw[EQ_IMP_THM]) >| [
    `h::q = [] ++ [h] ++ q` by rw[] >>
    metis_tac[sublist_cons],
    `h::t <= h::y` by rw[GSYM sublist_cons] >>
    `x ++ [h] ++ y = x ++ (h::y)` by rw[] >>
    metis_tac[sublist_append_include],
    `h::t <= q` by metis_tac[sublist_def] >>
    metis_tac[APPEND, APPEND_ASSOC],
    `h::t <= h::y` by rw[GSYM sublist_cons] >>
    `x ++ [h] ++ y = x ++ (h::y)` by rw[] >>
    metis_tac[sublist_append_include]
  ]);


(* ------------------------------------------------------------------------- *)
(* Application of sublist.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: p <= q ==> (MAP f p) <= (MAP f q) *)
(* Proof:
   By induction on q.
   Base: !p. p <= [] ==> MAP f p <= MAP f []
         Note p = []       by sublist_of_nil
          and MAP f []     by MAP
           so [] <= []     by sublist_nil
   Step: !p. p <= q ==> MAP f p <= MAP f q ==>
         !h p. p <= h::q ==> MAP f p <= MAP f (h::q)
         If p = [], [] <= h::q = F          by sublist_def
         If p = h'::t,
            If h' = h,
               Then             t <= q             by sublist_def, same heads
                ==>       MAP f t <= MAP f q       by induction hypothesis
                ==>    h::MAP f t <= h::MAP f q    by sublist_cons
                ==>  MAP f (h::t) <= MAP f (h::q)  by MAP
                 or       MAP f p <= MAP f (h::q)  by p = h::t
            If h' <> h,
               Then          p <= q                by sublist_def, different heads
               ==>     MAP f p <= MAP f q          by induction hypothesis
               ==>     MAP f p <= h::MAP f q       by sublist_cons_include
                or     MAP f p <= MAP f (h::q)     by MAP
*)
val MAP_SUBLIST = store_thm(
  "MAP_SUBLIST",
  ``!f p q. p <= q ==> (MAP f p) <= (MAP f q)``,
  strip_tac >>
  Induct_on `q` >-
  rw[sublist_of_nil, sublist_nil] >>
  rpt strip_tac >>
  (Cases_on `p` >> simp[sublist_def]) >>
  metis_tac[sublist_def, sublist_cons_include, MAP]);

(* Theorem: l1 <= l2 ==> SUM l1 <= SUM l2 *)
(* Proof:
   By induction on q.
   Base: !p. p <= [] ==> SUM p <= SUM []
      Note p = []        by sublist_of_nil
       and SUM [] = 0    by SUM
      Hence true.
   Step: !p. p <= q ==> SUM p <= SUM q ==>
         !h p. p <= h::q ==> SUM p <= SUM (h::q)
      If p = [], [] <= h::q = F         by sublist_def
      If p = h'::t,
         If h' = h,
         Then          t <= q           by sublist_def, same heads
          ==>      SUM t <= SUM q       by induction hypothesis
          ==>  h + SUM t <= h + SUM q   by arithmetic
          ==> SUM (h::t) <= SUM (h::q)  by SUM
           or      SUM p <= SUM (h::q)  by p = h::t
         If h' <> h,
         Then          p <= q           by sublist_def, different heads
          ==>      SUM p <= SUM q       by induction hypothesis
          ==>      SUM p <= h + SUM q   by arithmetic
          ==>      SUM p <= SUM (h::q)  by SUM
*)
val SUM_SUBLIST = store_thm(
  "SUM_SUBLIST",
  ``!p q. p <= q ==> SUM p <= SUM q``,
  Induct_on `q` >-
  rw[sublist_of_nil] >>
  rpt strip_tac >>
  (Cases_on `p` >> fs[sublist_def]) >>
  `h' + SUM t <= SUM q` by metis_tac[SUM] >>
  decide_tac);

(* Theorem: m < n ==> [m; n] <= [m .. n] *)
(* Proof:
   By induction on n.
   Base: !m. m < 0 ==> [m; 0] <= [m .. 0], true       by m < 0 = F.
   Step: !m. m < n ==> [m; n] <= [m .. n] ==>
         !m. m < SUC n ==> [m; SUC n] <= [m .. SUC n]
        Note m < SUC n means m <= n.
        If m = n, LHS = [n; SUC n]
                  RHS = [n .. (n + 1)] = [n; SUC n]   by ADD1
                      = LHS, thus true                by sublist_refl
        If m < n,              [m; n] <= [m .. n]     by induction hypothesis
                  SNOC (SUC n) [m; n] <= SNOC (SUC n) [m .. n] by sublist_snoc
                        [m; n; SUC n] <= [m .. SUC n]          by SNOC, listRangeINC_SNOC
           But [m; SUC n] <= [m; n; SUC n]            by sublist_def
           Thus [m; SUC n] <= [m .. SUC n]            by sublist_trans
*)
val listRangeINC_sublist = store_thm(
  "listRangeINC_sublist",
  ``!m n. m < n ==> [m; n] <= [m .. n]``,
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `(m = n) \/ m < n` by decide_tac >| [
    rw[listRangeINC_def, ADD1] >>
    rw[sublist_refl],
    `[m; n] <= [m .. n]` by rw[] >>
    `SNOC (SUC n) [m; n] <= SNOC (SUC n) [m .. n]` by rw[sublist_snoc] >>
    `SNOC (SUC n) [m; n] = [m; n; SUC n]` by rw[] >>
    `SNOC (SUC n) [m .. n] = [m .. SUC n]` by rw[listRangeINC_SNOC, ADD1] >>
    `[m; SUC n] <= [m; n; SUC n]` by rw[sublist_def] >>
    metis_tac[sublist_trans]
  ]);

(* Theorem: m + 1 < n ==> [m; (n - 1)] <= [m ..< n] *)
(* Proof:
   By induction on n.
   Base: !m. m + 1 < 0 ==> [m; 0 - 1] <= [m ..< 0], true  by m + 1 < 0 = F.
   Step: !m. m + 1 < n ==> [m; n - 1] <= [m ..< n] ==>
         !m. m + 1 < SUC n ==> [m; SUC n - 1] <= [m ..< SUC n]
        Note m + 1 < SUC n means m + 1 <= n.
        If m + 1 = n, LHS = [m; SUC n - 1] = [m; n]
                  RHS = [m ..< (n + 1)] = [m; n]          by ADD1
                      = LHS, thus true                    by sublist_refl
        If m + 1 < n,    [m; n - 1] <= [m ..< n]          by induction hypothesis
                  SNOC n [m; n - 1] <= SNOC n [m ..< n]   by sublist_snoc
                      [m; n - 1; n] <= [m ..< SUC n]      by SNOC, listRangeLHI_SNOC, ADD1
           But [m; SUC n - 1] <= [m; n] <= [m; n - 1; n]  by sublist_def
           Thus [m; SUC n - 1] <= [m ..< SUC n]           by sublist_trans
*)
val listRangeLHI_sublist = store_thm(
  "listRangeLHI_sublist",
  ``!m n. m + 1 < n ==> [m; (n - 1)] <= [m ..< n]``,
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `SUC n - 1 = n` by decide_tac >>
  `(m + 1 = n) \/ m + 1 < n` by decide_tac >| [
    rw[listRangeLHI_def, ADD1] >>
    rw[sublist_refl],
    `[m; n - 1] <= [m ..< n]` by rw[] >>
    `SNOC n [m; n - 1] <= SNOC n [m ..< n]` by rw[sublist_snoc] >>
    `SNOC n [m; n - 1] = [m; n - 1; n]` by rw[] >>
    `SNOC n [m ..< n] = [m ..< SUC n]` by rw[listRangeLHI_SNOC, ADD1] >>
    `[m; SUC n - 1] <= [m; n - 1; n]` by rw[sublist_def] >>
    metis_tac[sublist_trans]
  ]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
