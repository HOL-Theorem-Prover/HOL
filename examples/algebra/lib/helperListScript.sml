(* ------------------------------------------------------------------------- *)
(* Helper Theorems - a collection of useful results -- for Lists.            *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "helperList";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory rich_listTheory;

(* val _ = load "helperNumTheory"; *)
open helperNumTheory;

(* val _ = load "helperSetTheory"; *)
open helperSetTheory;

(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open arithmeticTheory dividesTheory gcdTheory;

(* use listRange: [1 .. 3] = [1; 2; 3], [1 ..< 3] = [1; 2] *)
(* val _ = load "listRangeTheory"; *)
open listRangeTheory;
open rich_listTheory; (* for EVERY_REVERSE *)
open indexedListsTheory; (* for findi_def *)


(* ------------------------------------------------------------------------- *)
(* HelperList Documentation                                                  *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   m downto n        = REVERSE [m .. n]
   turn_exp l n      = FUNPOW turn n l
   POSITIVE l        = !x. MEM x l ==> 0 < x
   EVERY_POSITIVE l  = EVERY (\k. 0 < k) l
   MONO f            = !x y. x <= y ==> f x <= f y
   MONO2 f           = !x1 y1 x2 y2. x1 <= x2 /\ y1 <= y2 ==> f x1 y1 <= f x2 y2
   MONO3 f           = !x1 y1 z1 x2 y2 z2. x1 <= x2 /\ y1 <= y2 /\ z1 <= z2 ==> f x1 y1 z1 <= f x2 y2 z2
   RMONO f           = !x y. x <= y ==> f y <= f x
   RMONO2 f          = !x1 y1 x2 y2. x1 <= x2 /\ y1 <= y2 ==> f x2 y2 <= f x1 y1
   RMONO3 f          = !x1 y1 z1 x2 y2 z2. x1 <= x2 /\ y1 <= y2 /\ z1 <= z2 ==> f x2 y2 z2 <= f x1 y1 z1
   MONO_INC ls       = !m n. m <= n /\ n < LENGTH ls ==> EL m ls <= EL n ls
   MONO_DEC ls       = !m n. m <= n /\ n < LENGTH ls ==> EL n ls <= EL m ls
*)

(* Definitions and Theorems (# are exported):

   List Theorems:
   LIST_NOT_NIL     |- !ls. ls <> [] <=> (ls = HD ls::TL ls)
   LIST_HEAD_TAIL   |- !ls. 0 < LENGTH ls <=> (ls = HD ls::TL ls)
   LIST_EQ_HEAD_TAIL|- !p q. p <> [] /\ q <> [] ==> ((p = q) <=> (HD p = HD q) /\ (TL p = TL q))
   LIST_SING_EQ     |- !x y. ([x] = [y]) <=> (x = y)
   LENGTH_NON_NIL   |- !l. 0 < LENGTH l <=> l <> []
   LENGTH_EQ_0      |- !l. (LENGTH l = 0) <=> (l = [])
   LENGTH_EQ_1      |- !l. (LENGTH l = 1) <=> ?x. l = [x]
   LENGTH_SING      |- !x. LENGTH [x] = 1
   LENGTH_TL_LT     |- !ls. ls <> [] ==> LENGTH (TL ls) < LENGTH ls
   SNOC_NIL         |- !x. SNOC x [] = [x]
   SNOC_CONS        |- !x x' l. SNOC x (x'::l) = x'::SNOC x l
   SNOC_LAST_FRONT  |- !l. l <> [] ==> (l = SNOC (LAST l) (FRONT l))
   MAP_COMPOSE      |- !f g l. MAP f (MAP g l) = MAP (f o g) l
   MAP_SING         |- !f x. MAP f [x] = [f x]
   MAP_HD           |- !f ls. ls <> [] ==> HD (MAP f ls) = f (HD ls)
   LAST_EL_CONS     |- !h t. t <> [] ==> LAST t = EL (LENGTH t) (h::t)
   FRONT_LENGTH     |- !l. l <> [] ==> (LENGTH (FRONT l) = PRE (LENGTH l))
   FRONT_EL         |- !l n. l <> [] /\ n < LENGTH (FRONT l) ==> (EL n (FRONT l) = EL n l)
   FRONT_EQ_NIL     |- !l. LENGTH l = 1 ==> FRONT l = []
   FRONT_NON_NIL    |- !l. 1 < LENGTH l ==> FRONT l <> []
   HEAD_MEM         |- !ls. ls <> [] ==> MEM (HD ls) ls
   LAST_MEM         |- !ls. ls <> [] ==> MEM (LAST ls) ls
   LAST_EQ_HD       |- !h t. ~MEM h t /\ LAST (h::t) = h <=> t = []
   MEM_FRONT_NOT_LAST|- !ls. ls <> [] /\ ALL_DISTINCT ls ==> ~MEM (LAST ls) (FRONT ls)
   NIL_NO_MEM       |- !ls. ls = [] <=> !x. ~MEM x ls
   MEM_APPEND_3     |- !l1 x l2 h. MEM h (l1 ++ [x] ++ l2) <=> MEM h (x::(l1 ++ l2))
   DROP_1           |- !h t. DROP 1 (h::t) = t
   FRONT_SING       |- !x. FRONT [x] = []
   TAIL_BY_DROP     |- !ls. ls <> [] ==> TL ls = DROP 1 ls
   FRONT_BY_TAKE    |- !ls. ls <> [] ==> FRONT ls = TAKE (LENGTH ls - 1) ls
   HD_APPEND        |- !h t ls. HD (h::t ++ ls) = h
   EL_TAIL          |- !h t n. 0 <> n ==> (EL (n - 1) t = EL n (h::t))
   MONOLIST_SET_SING|- !c ls. ls <> [] /\ EVERY ($= c) ls ==> SING (set ls)
!  LIST_TO_SET_EVAL |- !t h. set [] = {} /\ set (h::t) = h INSERT set t
   set_list_eq_count|- !ls n. set ls = count n ==> !j. j < LENGTH ls ==> EL j ls < n
   list_to_set_eq_el_image
                    |- !ls. set ls = IMAGE (\j. EL j ls) (count (LENGTH ls))
   all_distinct_list_el_inj
                    |- !ls. ALL_DISTINCT ls ==> INJ (\j. EL j ls) (count (LENGTH ls)) univ(:'a)

   List Reversal:
   REVERSE_SING      |- !x. REVERSE [x] = [x]
   REVERSE_HD        |- !ls. ls <> [] ==> (HD (REVERSE ls) = LAST ls)
   REVERSE_TL        |- !ls. ls <> [] ==> (TL (REVERSE ls) = REVERSE (FRONT ls))

   List Index:
   findi_nil         |- !x. findi x [] = 0
   findi_cons        |- !x h t. findi x (h::t) = if x = h then 0 else 1 + findi x t
   findi_none        |- !ls x. ~MEM x ls ==> findi x ls = LENGTH ls
   findi_APPEND      |- !l1 l2 x. findi x (l1 ++ l2) =
                                  if MEM x l1 then findi x l1 else LENGTH l1 + findi x l2
   findi_EL_iff      |- !ls x n. ALL_DISTINCT ls /\ MEM x ls /\ n < LENGTH ls ==>
                                 (x = EL n ls <=> findi x ls = n)

   Extra List Theorems:
   EVERY_ELEMENT_PROPERTY  |- !p R. EVERY (\c. c IN R) p ==> !k. k < LENGTH p ==> EL k p IN R
   EVERY_MONOTONIC_MAP     |- !l f P Q. (!x. P x ==> (Q o f) x) /\ EVERY P l ==> EVERY Q (MAP f l)
   EVERY_LT_IMP_EVERY_LE   |- !ls n. EVERY (\j. j < n) ls ==> EVERY (\j. j <= n) ls
   ZIP_SNOC         |- !x1 x2 l1 l2. (LENGTH l1 = LENGTH l2) ==>
                                     (ZIP (SNOC x1 l1,SNOC x2 l2) = SNOC (x1,x2) (ZIP (l1,l2)))
   ZIP_MAP_MAP      |- !ls f g. ZIP (MAP f ls,MAP g ls) = MAP (\x. (f x,g x)) ls
   MAP2_MAP_MAP     |- !ls f g1 g2. MAP2 f (MAP g1 ls) (MAP g2 ls) = MAP (\x. f (g1 x) (g2 x)) ls
   EL_APPEND        |- !n l1 l2. EL n (l1 ++ l2) = if n < LENGTH l1 then EL n l1 else EL (n - LENGTH l1) l2
   EL_SPLIT         |- !ls j. j < LENGTH ls ==> ?l1 l2. ls = l1 ++ EL j ls::l2
   EL_SPLIT_2       |- !ls j k. j < k /\ k < LENGTH ls ==> ?l1 l2 l3. ls = l1 ++ EL j ls::l2 ++ EL k ls::l3
   EL_ALL_PROPERTY  |- !h1 t1 h2 t2 P. (LENGTH (h1::t1) = LENGTH (h2::t2)) /\
                         (!k. k < LENGTH (h1::t1) ==> P (EL k (h1::t1)) (EL k (h2::t2))) ==>
                         P h1 h2 /\ !k. k < LENGTH t1 ==> P (EL k t1) (EL k t2)
   APPEND_EQ_APPEND_EQ   |- !l1 l2 m1 m2.
                            (l1 ++ l2 = m1 ++ m2) /\ (LENGTH l1 = LENGTH m1) <=> (l1 = m1) /\ (l2 = m2)
   LUPDATE_LEN           |- !e n l. LENGTH (LUPDATE e n l) = LENGTH l
   LUPDATE_EL            |- !e n l p. p < LENGTH l ==> EL p (LUPDATE e n l) = if p = n then e else EL p l
   LUPDATE_SAME_SPOT     |- !ls n p q. LUPDATE q n (LUPDATE p n ls) = LUPDATE q n ls
   LUPDATE_DIFF_SPOT     |- !ls m n p q. m <> n ==>
                            LUPDATE q n (LUPDATE p m ls) = LUPDATE p m (LUPDATE q n ls)
   EL_LENGTH_APPEND_0    |- !ls h t. EL (LENGTH ls) (ls ++ h::t) = h
   EL_LENGTH_APPEND_1    |- !ls h k t. EL (LENGTH ls + 1) (ls ++ h::k::t) = k
   LUPDATE_APPEND_0      |- !ls a h t. LUPDATE a (LENGTH ls) (ls ++ h::t) = ls ++ a::t
   LUPDATE_APPEND_1      |- !ls b h k t. LUPDATE b (LENGTH ls + 1) (ls ++ h::k::t) = ls ++ h::b::t
   LUPDATE_APPEND_0_1    |- !ls a b h k t. LUPDATE b (LENGTH ls + 1)
                                          (LUPDATE a (LENGTH ls) (ls ++ h::k::t)) = ls ++ a::b::t

   DROP and TAKE:
   DROP_LENGTH_NIL       |- !l. DROP (LENGTH l) l = []
   TL_DROP               |- !ls n. n < LENGTH ls ==> TL (DROP n ls) = DROP n (TL ls)
   TAKE_1_APPEND         |- !x y. x <> [] ==> (TAKE 1 (x ++ y) = TAKE 1 x)
   DROP_1_APPEND         |- !x y. x <> [] ==> (DROP 1 (x ++ y) = DROP 1 x ++ y)
   DROP_SUC              |- !n x. DROP (SUC n) x = DROP 1 (DROP n x)
   TAKE_SUC              |- !n x. TAKE (SUC n) x = TAKE n x ++ TAKE 1 (DROP n x)
   TAKE_SUC_BY_TAKE      |- !k x. k < LENGTH x ==> (TAKE (SUC k) x = SNOC (EL k x) (TAKE k x))
   DROP_BY_DROP_SUC      |- !k x. k < LENGTH x ==> (DROP k x = EL k x::DROP (SUC k) x)
   DROP_HEAD_ELEMENT     |- !ls n. n < LENGTH ls ==> ?u. DROP n ls = [EL n ls] ++ u
   DROP_TAKE_EQ_NIL      |- !ls n. DROP n (TAKE n ls) = []
   TAKE_DROP_SWAP        |- !ls m n. TAKE m (DROP n ls) = DROP n (TAKE (n + m) ls)
   TAKE_LENGTH_APPEND2   |- !l1 l2 x k. TAKE (LENGTH l1) (LUPDATE x (LENGTH l1 + k) (l1 ++ l2)) = l1
   LENGTH_TAKE_LE        |- !n l. LENGTH (TAKE n l) <= LENGTH l
   ALL_DISTINCT_TAKE     |- !ls n. ALL_DISTINCT ls ==> ALL_DISTINCT (TAKE n ls)
   ALL_DISTINCT_TAKE_DROP|- !ls. ALL_DISTINCT ls ==>
                            !k e. MEM e (TAKE k ls) /\ MEM e (DROP k ls) ==> F
   ALL_DISTINCT_SWAP     |- !ls x y. ALL_DISTINCT (x::y::ls) <=> ALL_DISTINCT (y::x::ls)
   ALL_DISTINCT_LAST_EL_IFF
                         |- !ls j. ALL_DISTINCT ls /\ ls <> [] /\ j < LENGTH ls ==>
                                   (EL j ls = LAST ls <=> j + 1 = LENGTH ls)
   ALL_DISTINCT_FRONT    |- !ls. ls <> [] /\ ALL_DISTINCT ls ==> ALL_DISTINCT (FRONT ls)
   ALL_DISTINCT_EL_APPEND
                         |- !ls l1 l2 j. ALL_DISTINCT ls /\ j < LENGTH ls /\
                                         ls = l1 ++ [EL j ls] ++ l2 ==> j = LENGTH l1
   ALL_DISTINCT_APPEND_3 |- !l1 x l2. ALL_DISTINCT (l1 ++ [x] ++ l2) <=> ALL_DISTINCT (x::(l1 ++ l2))
   MEM_SPLIT_APPEND_distinct
                         |- !l. ALL_DISTINCT l ==>
                            !x. MEM x l <=> ?p1 p2. (l = p1 ++ [x] ++ p2) /\ ~MEM x p1 /\ ~MEM x p2
   MEM_SPLIT_TAKE_DROP_first
                         |- !ls x. MEM x ls <=>
                               ?k. k < LENGTH ls /\ x = EL k ls /\
                                   ls = TAKE k ls ++ x::DROP (k + 1) ls /\ ~MEM x (TAKE k ls)
   MEM_SPLIT_TAKE_DROP_last
                         |- !ls x. MEM x ls <=>
                               ?k. k < LENGTH ls /\ x = EL k ls /\
                                   ls = TAKE k ls ++ x::DROP (k + 1) ls /\ ~MEM x (DROP (k + 1) ls)
   MEM_SPLIT_TAKE_DROP_distinct
                         |- !ls. ALL_DISTINCT ls ==>
                             !x. MEM x ls <=>
                             ?k. k < LENGTH ls /\ x = EL k ls /\
                                 ls = TAKE k ls ++ x::DROP (k + 1) ls /\
                                 ~MEM x (TAKE k ls) /\ ~MEM x (DROP (k + 1) ls)

   List Filter:
   FILTER_EL_IMP       |- !P ls l1 l2 x. (let fs = FILTER P ls
                                           in ls = l1 ++ x::l2 /\ P x ==> x = EL (LENGTH (FILTER P l1)) fs)
   FILTER_EL_IFF       |- !P ls l1 l2 x j. (let fs = FILTER P ls
                                             in ALL_DISTINCT ls /\ ls = l1 ++ x::l2 /\ j < LENGTH fs ==>
                                                (x = EL j fs <=> P x /\ j = LENGTH (FILTER P l1)))
   FILTER_HD           |- !P ls l1 l2 x. ls = l1 ++ x::l2 /\ P x /\ FILTER P l1 = [] ==> x = HD (FILTER P ls)
   FILTER_HD_IFF       |- !P ls l1 l2 x. ALL_DISTINCT ls /\ ls = l1 ++ x::l2 /\ P x ==>
                                         (x = HD (FILTER P ls) <=> FILTER P l1 = [])
   FILTER_LAST         |- !P ls l1 l2 x. ls = l1 ++ x::l2 /\ P x /\ FILTER P l2 = [] ==> x = LAST (FILTER P ls)
   FILTER_LAST_IFF     |- !P ls l1 l2 x. ALL_DISTINCT ls /\ ls = l1 ++ x::l2 /\ P x ==>
                                         (x = LAST (FILTER P ls) <=> FILTER P l2 = [])
   FILTER_EL_NEXT      |- !P ls l1 l2 l3 x y. (let fs = FILTER P ls; j = LENGTH (FILTER P l1)
                                                in ls = l1 ++ x::l2 ++ y::l3 /\ P x /\ P y /\ FILTER P l2 = [] ==>
                                                   x = EL j fs /\ y = EL (j + 1) fs)
   FILTER_EL_NEXT_IFF  |- !P ls l1 l2 l3 x y. (let fs = FILTER P ls; j = LENGTH (FILTER P l1)
                                                in ALL_DISTINCT ls /\ ls = l1 ++ x::l2 ++ y::l3 /\ P x /\ P y ==>
                                                   (x = EL j fs /\ y = EL (j + 1) fs <=> FILTER P l2 = []))
   FILTER_EL_NEXT_IDX  |- !P ls l1 l2 l3 x y. (let fs = FILTER P ls
                                                in ALL_DISTINCT ls /\ ls = l1 ++ x::l2 ++ y::l3 /\ P x /\ P y ==>
                                                   (findi y fs = 1 + findi x fs <=> FILTER P l2 = []))

   List Rotation:
   rotate_def              |- !n l. rotate n l = DROP n l ++ TAKE n l
   rotate_shift_element    |- !l n. n < LENGTH l ==> (rotate n l = EL n l::(DROP (SUC n) l ++ TAKE n l))
   rotate_0                |- !l. rotate 0 l = l
   rotate_nil              |- !n. rotate n [] = []
   rotate_full             |- !l. rotate (LENGTH l) l = l
   rotate_suc              |- !l n. n < LENGTH l ==> (rotate (SUC n) l = rotate 1 (rotate n l))
   rotate_same_length      |- !l n. LENGTH (rotate n l) = LENGTH l
   rotate_same_set         |- !l n. set (rotate n l) = set l
   rotate_add              |- !n m l. n + m <= LENGTH l ==> (rotate n (rotate m l) = rotate (n + m) l)
   rotate_lcancel          |- !k l. k < LENGTH l ==> (rotate (LENGTH l - k) (rotate k l) = l)
   rotate_rcancel          |- !k l. k < LENGTH l ==> (rotate k (rotate (LENGTH l - k) l) = l)

   List Turn:
   turn_def         |- !l. turn l = if l = [] then [] else LAST l::FRONT l
   turn_nil         |- turn [] = []
   turn_not_nil     |- !l. l <> [] ==> (turn l = LAST l::FRONT l)
   turn_length      |- !l. LENGTH (turn l) = LENGTH l
   turn_eq_nil      |- !p. (turn p = []) <=> (p = [])
   head_turn        |- !ls. ls <> [] ==> HD (turn ls) = LAST ls
   tail_turn        |- !ls. ls <> [] ==> (TL (turn ls) = FRONT ls)
   turn_snoc        |- !ls x. turn (SNOC x ls) = x::ls
   turn_exp_0       |- !l. turn_exp l 0 = l
   turn_exp_1       |- !l. turn_exp l 1 = turn l
   turn_exp_2       |- !l. turn_exp l 2 = turn (turn l)
   turn_exp_SUC     |- !l n. turn_exp l (SUC n) = turn_exp (turn l) n
   turn_exp_suc     |- !l n. turn_exp l (SUC n) = turn (turn_exp l n)
   turn_exp_length  |- !l n. LENGTH (turn_exp l n) = LENGTH l
   head_turn_exp    |- !ls n. n < LENGTH ls ==>
                              HD (turn_exp ls n) = EL (if n = 0 then 0 else (LENGTH ls - n)) ls

   Unit-List and Mono-List:
   LIST_TO_SET_SING |- !l. (LENGTH l = 1) ==> SING (set l)
   MONOLIST_EQ      |- !l1 l2. SING (set l1) /\ SING (set l2) ==>
                        ((l1 = l2) <=> (LENGTH l1 = LENGTH l2) /\ (set l1 = set l2))
   NON_MONO_TAIL_PROPERTY |- !l. ~SING (set (h::t)) ==> ?h'. MEM h' t /\ h' <> h

   GENLIST Theorems:
   GENLIST_0           |- !f. GENLIST f 0 = []
   GENLIST_1           |- !f. GENLIST f 1 = [f 0]
   GENLIST_EQ          |- !f1 f2 n. (!m. m < n ==> f1 m = f2 m) ==> GENLIST f1 n = GENLIST f2 n
   GENLIST_EQ_NIL      |- !f n. (GENLIST f n = []) <=> (n = 0)
   GENLIST_LAST        |- !f n. LAST (GENLIST f (SUC n)) = f n
   GENLIST_CONSTANT    |- !f n c. (!k. k < n ==> (f k = c)) <=> EVERY (\x. x = c) (GENLIST f n)
   GENLIST_K_CONS      |- !e n. GENLIST (K e) (SUC n) = e::GENLIST (K e) n
   GENLIST_K_ADD       |- !e n m. GENLIST (K e) (n + m) = GENLIST (K e) m ++ GENLIST (K e) n
   GENLIST_K_LESS      |- !f e n. (!k. k < n ==> (f k = e)) ==> (GENLIST f n = GENLIST (K e) n)
   GENLIST_K_RANGE     |- !f e n. (!k. 0 < k /\ k <= n ==> (f k = e)) ==> (GENLIST (f o SUC) n = GENLIST (K e) n)
   GENLIST_K_APPEND    |- !a b c. GENLIST (K c) a ++ GENLIST (K c) b = GENLIST (K c) (a + b)
   GENLIST_K_APPEND_K  |- !c n. GENLIST (K c) n ++ [c] = [c] ++ GENLIST (K c) n
   GENLIST_K_MEM       |- !x c n. 0 < n ==> (MEM x (GENLIST (K c) n) <=> (x = c))
   GENLIST_K_SET       |- !c n. 0 < n ==> (set (GENLIST (K c) n) = {c})
   LIST_TO_SET_SING_IFF|- !ls. ls <> [] ==> (SING (set ls) <=> ?c. ls = GENLIST (K c) (LENGTH ls))

   SUM Theorems:
   SUM_NIL                |- SUM [] = 0
   SUM_CONS               |- !h t. SUM (h::t) = h + SUM t
   SUM_SING               |- !n. SUM [n] = n
   SUM_MULT               |- !s k. k * SUM s = SUM (MAP ($* k) s)
   SUM_RIGHT_ADD_DISTRIB  |- !s m n. (m + n) * SUM s = SUM (MAP ($* m) s) + SUM (MAP ($* n) s)
   SUM_LEFT_ADD_DISTRIB   |- !s m n. SUM s * (m + n) = SUM (MAP ($* m) s) + SUM (MAP ($* n) s)

   SUM_GENLIST            |- !f n. SUM (GENLIST f n) = SIGMA f (count n)
   SUM_DECOMPOSE_FIRST    |- !f n. SUM (GENLIST f (SUC n)) = f 0 + SUM (GENLIST (f o SUC) n)
   SUM_DECOMPOSE_LAST     |- !f n. SUM (GENLIST f (SUC n)) = SUM (GENLIST f n) + f n
   SUM_ADD_GENLIST        |- !a b n. SUM (GENLIST a n) + SUM (GENLIST b n) =
                                     SUM (GENLIST (\k. a k + b k) n)
   SUM_GENLIST_APPEND     |- !a b n. SUM (GENLIST a n ++ GENLIST b n) = SUM (GENLIST (\k. a k + b k) n)
   SUM_DECOMPOSE_FIRST_LAST  |- !f n. 0 < n ==>
                                (SUM (GENLIST f (SUC n)) = f 0 + SUM (GENLIST (f o SUC) (PRE n)) + f n)
   SUM_MOD           |- !n. 0 < n ==> !l. (SUM l) MOD n = (SUM (MAP (\x. x MOD n) l)) MOD n
   SUM_EQ_0          |- !l. (SUM l = 0) <=> EVERY (\x. x = 0) l
   SUM_GENLIST_MOD   |- !n. 0 < n ==> !f. SUM (GENLIST ((\k. f k) o SUC) (PRE n)) MOD n =
                                          SUM (GENLIST ((\k. f k MOD n) o SUC) (PRE n)) MOD n
   SUM_CONSTANT      |- !n x. SUM (GENLIST (\j. x) n) = n * x
   SUM_GENLIST_K     |- !m n. SUM (GENLIST (K m) n) = m * n
   SUM_LE            |- !l1 l2. (LENGTH l1 = LENGTH l2) /\
                                (!k. k < LENGTH l1 ==> EL k l1 <= EL k l2) ==> SUM l1 <= SUM l2
   SUM_LE_MEM        |- !l x. MEM x l ==> x <= SUM l:
   SUM_LE_EL         |- !l n. n < LENGTH l ==> EL n l <= SUM l
   SUM_LE_SUM_EL     |- !l m n. m < n /\ n < LENGTH l ==> EL m l + EL n l <= SUM l
   SUM_DOUBLING_LIST |- !m n. SUM (GENLIST (\j. n * 2 ** j) m) = n * (2 ** m - 1)
   list_length_le_sum|- !ls. EVERY_POSITIVE ls ==> LENGTH ls <= SUM ls
   list_length_eq_sum|- !ls. EVERY_POSITIVE ls /\ LENGTH ls = SUM ls ==> EVERY (\x. x = 1) ls

   Maximum of a List:
   MAX_LIST_def        |- (MAX_LIST [] = 0) /\ !h t. MAX_LIST (h::t) = MAX h (MAX_LIST t)
#  MAX_LIST_NIL        |- MAX_LIST [] = 0
#  MAX_LIST_CONS       |- !h t. MAX_LIST (h::t) = MAX h (MAX_LIST t)
   MAX_LIST_SING       |- !x. MAX_LIST [x] = x
   MAX_LIST_EQ_0       |- !l. (MAX_LIST l = 0) <=> EVERY (\x. x = 0) l
   MAX_LIST_MEM        |- !l. l <> [] ==> MEM (MAX_LIST l) l
   MAX_LIST_PROPERTY   |- !l x. MEM x l ==> x <= MAX_LIST l
   MAX_LIST_TEST       |- !l. l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> y <= x) ==> (x = MAX_LIST l)
   MAX_LIST_LE         |- !h t. MAX_LIST t <= MAX_LIST (h::t)
   MAX_LIST_MONO_MAP   |- !f. (!x y. x <= y ==> f x <= f y) ==>
                              !ls. ls <> [] ==> MAX_LIST (MAP f ls) = f (MAX_LIST ls)

   Minimum of a List:
   MIN_LIST_def          |- !h t. MIN_LIST (h::t) = if t = [] then h else MIN h (MIN_LIST t)
#  MIN_LIST_SING         |- !x. MIN_LIST [x] = x
#  MIN_LIST_CONS         |- !h t. t <> [] ==> (MIN_LIST (h::t) = MIN h (MIN_LIST t))
   MIN_LIST_MEM          |- !l. l <> [] ==> MEM (MIN_LIST l) l
   MIN_LIST_PROPERTY     |- !l. l <> [] ==> !x. MEM x l ==> MIN_LIST l <= x
   MIN_LIST_TEST         |- !l. l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> x <= y) ==> (x = MIN_LIST l)
   MIN_LIST_LE_MAX_LIST  |- !l. l <> [] ==> MIN_LIST l <= MAX_LIST l
   MIN_LIST_LE           |- !h t. t <> [] ==> MIN_LIST (h::t) <= MIN_LIST t
   MIN_LIST_MONO_MAP     |- !f. (!x y. x <= y ==> f x <= f y) ==>
                                !ls. ls <> [] ==> MIN_LIST (MAP f ls) = f (MIN_LIST ls)

   List Nub and Set:
   nub_nil             |- nub [] = []
   nub_cons            |- !x l. nub (x::l) = if MEM x l then nub l else x::nub l
   nub_sing            |- !x. nub [x] = [x]
   nub_all_distinct    |- !l. ALL_DISTINCT (nub l)
   CARD_LIST_TO_SET_EQ           |- !l. CARD (set l) = LENGTH (nub l)
   MONO_LIST_TO_SET              |- !x. set [x] = {x}
   DISTINCT_LIST_TO_SET_EQ_SING  |- !l x. ALL_DISTINCT l /\ (set l = {x}) <=> (l = [x])
   LIST_TO_SET_REDUCTION         |- !l1 l2 h. ~MEM h l1 /\ (set (h::l1) = set l2) ==>
                  ?p1 p2. ~MEM h p1 /\ ~MEM h p2 /\ (nub l2 = p1 ++ [h] ++ p2) /\ (set l1 = set (p1 ++ p2))

   Constant List and Padding:
   PAD_LEFT_NIL      |- !n c. PAD_LEFT c n [] = GENLIST (K c) n
   PAD_RIGHT_NIL     |- !n c. PAD_RIGHT c n [] = GENLIST (K c) n
   PAD_LEFT_LENGTH   |- !n c s. LENGTH (PAD_LEFT c n s) = MAX n (LENGTH s)
   PAD_RIGHT_LENGTH  |- !n c s. LENGTH (PAD_RIGHT c n s) = MAX n (LENGTH s)
   PAD_LEFT_ID       |- !l c n. n <= LENGTH l ==> (PAD_LEFT c n l = l)
   PAD_RIGHT_ID      |- !l c n. n <= LENGTH l ==> (PAD_RIGHT c n l = l)
   PAD_LEFT_0        |- !l c. PAD_LEFT c 0 l = l
   PAD_RIGHT_0       |- !l c. PAD_RIGHT c 0 l = l
   PAD_LEFT_CONS     |- !l n. LENGTH l <= n ==> !c. PAD_LEFT c (SUC n) l = c::PAD_LEFT c n l
   PAD_RIGHT_SNOC    |- !l n. LENGTH l <= n ==> !c. PAD_RIGHT c (SUC n) l = SNOC c (PAD_RIGHT c n l)
   PAD_RIGHT_CONS    |- !h t c n. h::PAD_RIGHT c n t = PAD_RIGHT c (SUC n) (h::t)
   PAD_LEFT_LAST     |- !l c n. l <> [] ==> (LAST (PAD_LEFT c n l) = LAST l)
   PAD_LEFT_EQ_NIL   |- !l c n. (PAD_LEFT c n l = []) <=> (l = []) /\ (n = 0)
   PAD_RIGHT_EQ_NIL  |- !l c n. (PAD_RIGHT c n l = []) <=> (l = []) /\ (n = 0)
   PAD_LEFT_NIL_EQ   |- !n c. 0 < n ==> (PAD_LEFT c n [] = PAD_LEFT c n [c])
   PAD_RIGHT_NIL_EQ  |- !n c. 0 < n ==> (PAD_RIGHT c n [] = PAD_RIGHT c n [c])
   PAD_RIGHT_BY_RIGHT|- !ls c n. PAD_RIGHT c n ls = ls ++ PAD_RIGHT c (n - LENGTH ls) []
   PAD_RIGHT_BY_LEFT |- !ls c n. PAD_RIGHT c n ls = ls ++ PAD_LEFT c (n - LENGTH ls) []
   PAD_LEFT_BY_RIGHT |- !ls c n. PAD_LEFT c n ls = PAD_RIGHT c (n - LENGTH ls) [] ++ ls
   PAD_LEFT_BY_LEFT  |- !ls c n. PAD_LEFT c n ls = PAD_LEFT c (n - LENGTH ls) [] ++ ls

   PROD for List, similar to SUM for List:
   POSITIVE_THM      |- !ls. EVERY_POSITIVE ls <=> POSITIVE ls
#  PROD              |- (PROD [] = 1) /\ !h t. PROD (h::t) = h * PROD t
   PROD_NIL          |- PROD [] = 1
   PROD_CONS         |- !h t. PROD (h::t) = h * PROD t
   PROD_SING         |- !n. PROD [n] = n
   PROD_eval         |- !ls. PROD ls = if ls = [] then 1 else HD ls * PROD (TL ls)
   PROD_eq_1         |- !ls. (PROD ls = 1) <=> !x. MEM x ls ==> (x = 1)
   PROD_SNOC         |- !x l. PROD (SNOC x l) = PROD l * x
   PROD_APPEND       |- !l1 l2. PROD (l1 ++ l2) = PROD l1 * PROD l2
   PROD_MAP_FOLDL    |- !ls f. PROD (MAP f ls) = FOLDL (\a e. a * f e) 1 ls
   PROD_IMAGE_eq_PROD_MAP_SET_TO_LIST  |- !s. FINITE s ==> !f. PI f s = PROD (MAP f (SET_TO_LIST s))
   PROD_ACC_DEF      |- (!acc. PROD_ACC [] acc = acc) /\
                         !h t acc. PROD_ACC (h::t) acc = PROD_ACC t (h * acc)
   PROD_ACC_PROD_LEM |- !L n. PROD_ACC L n = PROD L * n
   PROD_PROD_ACC     |- !L. PROD L = PROD_ACC L 1
   PROD_GENLIST_K    |- !m n. PROD (GENLIST (K m) n) = m ** n
   PROD_CONSTANT     |- !n x. PROD (GENLIST (\j. x) n) = x ** n
   PROD_EQ_0         |- !l. (PROD l = 0) <=> MEM 0 l
   PROD_POS          |- !l. EVERY_POSITIVE l ==> 0 < PROD l
   PROD_POS_ALT      |- !l. POSITIVE l ==> 0 < PROD l
   PROD_SQUARING_LIST|- !m n. PROD (GENLIST (\j. n ** 2 ** j) m) = n ** (2 ** m - 1)

   Range Conjunction and Disjunction:
   every_range_sing    |- !a j. a <= j /\ j <= a <=> (j = a)
   every_range_cons    |- !f a b. a <= b ==>
                                  ((!j. a <= j /\ j <= b ==> f j) <=>
                                   f a /\ !j. a + 1 <= j /\ j <= b ==> f j)
   every_range_split_head
                       |- !f a b. a <= b ==>
                                  ((!j. PRE a <= j /\ j <= b ==> f j) <=>
                                   f (PRE a) /\ !j. a <= j /\ j <= b ==> f j)
   every_range_split_last
                       |- !f a b. a <= b ==>
                                  ((!j. a <= j /\ j <= SUC b ==> f j) <=>
                                    f (SUC b) /\ !j. a <= j /\ j <= b ==> f j)
   every_range_less_ends
                       |- !f a b. a <= b ==>
                                  ((!j. a <= j /\ j <= b ==> f j) <=>
                                   f a /\ f b /\ !j. a < j /\ j < b ==> f j)
   every_range_span_max|- !f a b. a < b /\ f a /\ ~f b ==>
                                  ?m. a <= m /\ m < b /\
                                      (!j. a <= j /\ j <= m ==> f j) /\ ~f (SUC m)
   every_range_span_min|- !f a b. a < b /\ ~f a /\ f b ==>
                                  ?m. a < m /\ m <= b /\
                                      (!j. m <= j /\ j <= b ==> f j) /\ ~f (PRE m)
   exists_range_sing   |- !a. ?j. a <= j /\ j <= a <=> (j = a)
   exists_range_cons   |- !f a b. a <= b ==>
                                  ((?j. a <= j /\ j <= b /\ f j) <=>
                                   f a \/ ?j. a + 1 <= j /\ j <= b /\ f j)

   List Range:
   listRangeINC_to_LHI       |- !m n. [m .. n] = [m ..< SUC n]
   listRangeINC_SET          |- !n. set [1 .. n] = IMAGE SUC (count n)
   listRangeINC_LEN          |- !m n. LENGTH [m .. n] = n + 1 - m
   listRangeINC_NIL          |- !m n. ([m .. n] = []) <=> n + 1 <= m
   listRangeINC_MEM          |- !m n x. MEM x [m .. n] <=> m <= x /\ x <= n
   listRangeINC_EL           |- !m n i. m + i <= n ==> EL i [m .. n] = m + i
   listRangeINC_EVERY        |- !P m n. EVERY P [m .. n] <=> !x. m <= x /\ x <= n ==> P x
   listRangeINC_EXISTS       |- !P m n. EXISTS P [m .. n] <=> ?x. m <= x /\ x <= n /\ P x
   listRangeINC_EVERY_EXISTS |- !P m n. EVERY P [m .. n] <=> ~EXISTS ($~ o P) [m .. n]
   listRangeINC_EXISTS_EVERY |- !P m n. EXISTS P [m .. n] <=> ~EVERY ($~ o P) [m .. n]
   listRangeINC_SNOC         |- !m n. m <= n + 1 ==> ([m .. n + 1] = SNOC (n + 1) [m .. n])
   listRangeINC_FRONT        |- !m n. m <= n + 1 ==> (FRONT [m .. n + 1] = [m .. n])
   listRangeINC_LAST         |- !m n. m <= n ==> (LAST [m .. n] = n)
   listRangeINC_REVERSE      |- !m n. REVERSE [m .. n] = MAP (\x. n - x + m) [m .. n]
   listRangeINC_REVERSE_MAP  |- !f m n. REVERSE (MAP f [m .. n]) = MAP (f o (\x. n - x + m)) [m .. n]
   listRangeINC_MAP_SUC      |- !f m n. MAP f [m + 1 .. n + 1] = MAP (f o SUC) [m .. n]
   listRangeINC_APPEND       |- !a b c. a <= b /\ b <= c ==> ([a .. b] ++ [b + 1 .. c] = [a .. c])
   listRangeINC_SUM          |- !m n. SUM [m .. n] = SUM [1 .. n] - SUM [1 .. m - 1]
   listRangeINC_PROD_pos     |- !m n. 0 < m ==> 0 < PROD [m .. n]
   listRangeINC_PROD         |- !m n. 0 < m /\ m <= n ==> (PROD [m .. n] = PROD [1 .. n] DIV PROD [1 .. m - 1])
   listRangeINC_has_divisors |- !m n x. 0 < n /\ m <= x /\ x divides n ==> MEM x [m .. n]
   listRangeINC_1_n          |- !n. [1 .. n] = GENLIST SUC n
   listRangeINC_MAP          |- !f n. MAP f [1 .. n] = GENLIST (f o SUC) n
   listRangeINC_SUM_MAP      |- !f n. SUM (MAP f [1 .. SUC n]) = f (SUC n) + SUM (MAP f [1 .. n])
   listRangeINC_SPLIT        |- !m n j. m < j /\ j <= n ==> [m .. n] = [m .. j - 1] ++ j::[j + 1 .. n]

   listRangeLHI_to_INC       |- !m n. [m ..< n + 1] = [m .. n]
   listRangeLHI_SET          |- !n. set [0 ..< n] = count n
   listRangeLHI_LEN          |- !m n. LENGTH [m ..< n] = n - m
   listRangeLHI_NIL          |- !m n. [m ..< n] = [] <=> n <= m
   listRangeLHI_MEM          |- !m n x. MEM x [m ..< n] <=> m <= x /\ x < n
   listRangeLHI_EL           |- !m n i. m + i < n ==> EL i [m ..< n] = m + i
   listRangeLHI_EVERY        |- !P m n. EVERY P [m ..< n] <=> !x. m <= x /\ x < n ==> P x
   listRangeLHI_SNOC         |- !m n. m <= n ==> [m ..< n + 1] = SNOC n [m ..< n]
   listRangeLHI_FRONT        |- !m n. m <= n ==> (FRONT [m ..< n + 1] = [m ..< n])
   listRangeLHI_LAST         |- !m n. m <= n ==> (LAST [m ..< n + 1] = n)
   listRangeLHI_REVERSE      |- !m n. REVERSE [m ..< n] = MAP (\x. n - 1 - x + m) [m ..< n]
   listRangeLHI_REVERSE_MAP  |- !f m n. REVERSE (MAP f [m ..< n]) = MAP (f o (\x. n - 1 - x + m)) [m ..< n]
   listRangeLHI_MAP_SUC      |- !f m n. MAP f [m + 1 ..< n + 1] = MAP (f o SUC) [m ..< n]
   listRangeLHI_APPEND       |- !a b c. a <= b /\ b <= c ==> [a ..< b] ++ [b ..< c] = [a ..< c]
   listRangeLHI_SUM          |- !m n. SUM [m ..< n] = SUM [1 ..< n] - SUM [1 ..< m]
   listRangeLHI_PROD_pos     |- !m n. 0 < m ==> 0 < PROD [m ..< n]
   listRangeLHI_PROD         |- !m n. 0 < m /\ m <= n ==> PROD [m ..< n] = PROD [1 ..< n] DIV PROD [1 ..< m]
   listRangeLHI_has_divisors |- !m n x. 0 < n /\ m <= x /\ x divides n ==> MEM x [m ..< n + 1]
   listRangeLHI_0_n          |- !n. [0 ..< n] = GENLIST I n
   listRangeLHI_MAP          |- !f n. MAP f [0 ..< n] = GENLIST f n
   listRangeLHI_SUM_MAP      |- !f n. SUM (MAP f [0 ..< SUC n]) = f n + SUM (MAP f [0 ..< n])
   listRangeLHI_SPLIT        |- !m n j. m <= j /\ j < n ==> [m ..< n] = [m ..< j] ++ j::[j + 1 ..< n]

   listRangeINC_ALL_DISTINCT       |- !m n. ALL_DISTINCT [m .. n]
   listRangeINC_EVERY_split_head   |- !P m n. m <= n ==> (EVERY P [m - 1 .. n] <=> P (m - 1) /\ EVERY P [m .. n])
   listRangeINC_EVERY_split_last   |- !P m n. m <= n ==> (EVERY P [m .. n + 1] <=> P (n + 1) /\ EVERY P [m .. n])
   listRangeINC_EVERY_less_last    |- !P m n. m <= n ==> (EVERY P [m .. n] <=> P n /\ EVERY P [m ..< n])
   listRangeINC_EVERY_span_max     |- !P m n. m < n /\ P m /\ ~P n ==>
                                              ?k. m <= k /\ k < n /\ EVERY P [m .. k] /\ ~P (SUC k)
   listRangeINC_EVERY_span_min     |- !P m n. m < n /\ ~P m /\ P n ==>
                                              ?k. m < k /\ k <= n /\ EVERY P [k .. n] /\ ~P (PRE k)

   List Summation and Product:
   sum_1_to_n_eq_tri_n       |- !n. SUM [1 .. n] = tri n
   sum_1_to_n_eqn            |- !n. SUM [1 .. n] = HALF (n * (n + 1))
   sum_1_to_n_double         |- !n. TWICE (SUM [1 .. n]) = n * (n + 1)
   prod_1_to_n_eq_fact_n     |- !n. PROD [1 .. n] = FACT n
   power_predecessor_eqn     |- !t n. t ** n - 1 = (t - 1) * SUM (MAP (\j. t ** j) [0 ..< n])
   geometric_sum_eqn         |- !t n. 1 < t ==> SUM (MAP (\j. t ** j) [0 ..< n]) = (t ** n - 1) DIV (t - 1)
   geometric_sum_eqn_alt     |- !t n. 1 < t ==> SUM (MAP (\j. t ** j) [0 .. n]) = (t ** (n + 1) - 1) DIV (t - 1)
   arithmetic_sum_eqn        |- !n. SUM [1 ..< n] = HALF (n * (n - 1))
   arithmetic_sum_eqn_alt    |- !n. SUM [1 .. n] = HALF (n * (n + 1))
   SUM_GENLIST_REVERSE       |- !f n. SUM (GENLIST (\j. f (n - j)) n) = SUM (MAP f [1 .. n])
   SUM_IMAGE_count           |- !f n. SIGMA f (count n) = SUM (MAP f [0 ..< n])
   SUM_IMAGE_upto            |- !f n. SIGMA f (count (SUC n)) = SUM (MAP f [0 .. n])

   MAP of function with 3 list arguments:
   MAP3_DEF    |- (!t3 t2 t1 h3 h2 h1 f.
                    MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3) /\
                  (!z y f. MAP3 f [] y z = []) /\
                  (!z v5 v4 f. MAP3 f (v4::v5) [] z = []) /\
                   !v5 v4 v13 v12 f. MAP3 f (v4::v5) (v12::v13) [] = []
   MAP3        |- (!f. MAP3 f [] [] [] = []) /\
                   !f h1 t1 h2 t2 h3 t3.
                    MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3
   LENGTH_MAP3 |- !lx ly lz f. LENGTH (MAP3 f lx ly lz) = MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz)
   EL_MAP3     |- !lx ly lz n. n < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
                  !f. EL n (MAP3 f lx ly lz) = f (EL n lx) (EL n ly) (EL n lz)
   MEM_MAP2    |- !f x l1 l2. MEM x (MAP2 f l1 l2) ==>
                  ?y1 y2. x = f y1 y2 /\ MEM y1 l1 /\ MEM y2 l2
   MEM_MAP3    |- !f x l1 l2 l3. MEM x (MAP3 f l1 l2 l3) ==>
                  ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 l1 /\ MEM y2 l2 /\ MEM y3 l3
   SUM_MAP_K   |- !ls c. SUM (MAP (K c) ls) = c * LENGTH ls
   SUM_MAP_K_LE|- !ls a b. a <= b ==> SUM (MAP (K a) ls) <= SUM (MAP (K b) ls)
   SUM_MAP2_K  |- !lx ly c. SUM (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly)
   SUM_MAP3_K  |- !lx ly lz c. SUM (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz)

   Bounds on Lists:
   SUM_UPPER        |- !ls. SUM ls <= MAX_LIST ls * LENGTH ls
   SUM_LOWER        |- !ls. MIN_LIST ls * LENGTH ls <= SUM ls
   SUM_MAP_LE       |- !f g ls. EVERY (\x. f x <= g x) ls ==> SUM (MAP f ls) <= SUM (MAP g ls)
   SUM_MAP_LT       |- !f g ls. EVERY (\x. f x < g x) ls /\ ls <> [] ==> SUM (MAP f ls) < SUM (MAP g ls)
   MEM_MAP_UPPER    |- !f. MONO f ==> !ls e. MEM e (MAP f ls) ==> e <= f (MAX_LIST ls)
   MEM_MAP2_UPPER   |- !f. MONO2 f ==>!lx ly e. MEM e (MAP2 f lx ly) ==> e <= f (MAX_LIST lx) (MAX_LIST ly)
   MEM_MAP3_UPPER   |- !f. MONO3 f ==>
                           !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> e <= f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz)
   MEM_MAP_LOWER    |- !f. MONO f ==> !ls e. MEM e (MAP f ls) ==> f (MIN_LIST ls) <= e
   MEM_MAP2_LOWER   |- !f. MONO2 f ==> !lx ly e. MEM e (MAP2 f lx ly) ==> f (MIN_LIST lx) (MIN_LIST ly) <= e
   MEM_MAP3_LOWER   |- !f. MONO3 f ==>
                           !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> f (MIN_LIST lx) (MIN_LIST ly) (MIN_LIST lz) <= e
   MAX_LIST_MAP_LE  |- !f g. (!x. f x <= g x) ==>
                       !ls. MAX_LIST (MAP f ls) <= MAX_LIST (MAP g ls)
   MIN_LIST_MAP_LE  |- !f g. (!x. f x <= g x) ==>
                       !ls. MIN_LIST (MAP f ls) <= MIN_LIST (MAP g ls)
   MAP_LE           |- !f g. (!x. f x <= g x) ==> !ls n. EL n (MAP f ls) <= EL n (MAP g ls)
   MAP2_LE          |- !f g. (!x y. f x y <= g x y) ==>
                       !lx ly n. EL n (MAP2 f lx ly) <= EL n (MAP2 g lx ly)
   MAP3_LE          |- !f g. (!x y z. f x y z <= g x y z) ==>
                       !lx ly lz n. EL n (MAP3 f lx ly lz) <= EL n (MAP3 g lx ly lz)
   SUM_MONO_MAP     |- !f1 f2. (!x. f1 x <= f2 x) ==> !ls. SUM (MAP f1 ls) <= SUM (MAP f2 ls)
   SUM_MONO_MAP2    |- !f1 f2. (!x y. f1 x y <= f2 x y) ==>
                               !lx ly. SUM (MAP2 f1 lx ly) <= SUM (MAP2 f2 lx ly)
   SUM_MONO_MAP3    |- !f1 f2. (!x y z. f1 x y z <= f2 x y z) ==>
                               !lx ly lz. SUM (MAP3 f1 lx ly lz) <= SUM (MAP3 f2 lx ly lz)
   SUM_MAP_UPPER    |- !f. MONO f ==> !ls. SUM (MAP f ls) <= f (MAX_LIST ls) * LENGTH ls
   SUM_MAP2_UPPER   |- !f. MONO2 f ==>
                       !lx ly. SUM (MAP2 f lx ly) <= f (MAX_LIST lx) (MAX_LIST ly) * LENGTH (MAP2 f lx ly)
   SUM_MAP3_UPPER   |- !f. MONO3 f ==>
                       !lx ly lz. SUM (MAP3 f lx ly lz) <= f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz) * LENGTH (MAP3 f lx ly lz)

   Increasing and decreasing list bounds:
   MONO_INC_NIL        |- MONO_INC []
   MONO_INC_CONS       |- !h t. MONO_INC (h::t) ==> MONO_INC t
   MONO_INC_HD         |- !h t x. MONO_INC (h::t) /\ MEM x t ==> h <= x
   MONO_DEC_NIL        |- MONO_DEC []
   MONO_DEC_CONS       |- !h t. MONO_DEC (h::t) ==> MONO_DEC t
   MONO_DEC_HD         |- !h t x. MONO_DEC (h::t) /\ MEM x t ==> x <= h
   GENLIST_MONO_INC    |- !f n. MONO f ==> MONO_INC (GENLIST f n)
   GENLIST_MONO_DEC    |- !f n. RMONO f ==> MONO_DEC (GENLIST f n)
   MAX_LIST_MONO_INC   |- !ls. ls <> [] /\ MONO_INC ls ==> MAX_LIST ls = LAST ls
   MAX_LIST_MONO_DEC   |- !ls. ls <> [] /\ MONO_DEC ls ==> MAX_LIST ls = HD ls
   MIN_LIST_MONO_INC   |- !ls. ls <> [] /\ MONO_INC ls ==> MIN_LIST ls = HD ls
   MIN_LIST_MONO_DEC   |- !ls. ls <> [] /\ MONO_DEC ls ==> MIN_LIST ls = LAST ls
   listRangeINC_MONO_INC  |- !m n. MONO_INC [m .. n]
   listRangeLHI_MONO_INC  |- !m n. MONO_INC [m ..< n]

   List Dilation:

   List Dilation (Multiplicative):
   MDILATE_def    |- (!e n. MDILATE e n [] = []) /\
        !e n h t. MDILATE e n (h::t) = if t = [] then [h] else h::GENLIST (K e) (PRE n) ++ MDILATE e n t
#  MDILATE_NIL    |- !e n. MDILATE e n [] = []
#  MDILATE_SING   |- !e n x. MDILATE e n [x] = [x]
   MDILATE_CONS   |- !e n h t. MDILATE e n (h::t) =
                               if t = [] then [h] else h::GENLIST (K e) (PRE n) ++ MDILATE e n t
   MDILATE_1      |- !l e. MDILATE e 1 l = l
   MDILATE_0      |- !l e. MDILATE e 0 l = l
   MDILATE_LENGTH        |- !l e n. LENGTH (MDILATE e n l) =
                              if n = 0 then LENGTH l else if l = [] then 0 else SUC (n * PRE (LENGTH l))
   MDILATE_LENGTH_LOWER  |- !l e n. LENGTH l <= LENGTH (MDILATE e n l)
   MDILATE_LENGTH_UPPER  |- !l e n. 0 < n ==> LENGTH (MDILATE e n l) <= SUC (n * PRE (LENGTH l))
   MDILATE_EL     |- !l e n k. k < LENGTH (MDILATE e n l) ==>
              (EL k (MDILATE e n l) = if n = 0 then EL k l else if k MOD n = 0 then EL (k DIV n) l else e)
   MDILATE_EQ_NIL |- !l e n. (MDILATE e n l = []) <=> (l = [])
   MDILATE_LAST   |- !l e n. LAST (MDILATE e n l) = LAST l

   List Dilation (Additive):
   DILATE_def       |- (!n m e. DILATE e n m [] = []) /\
                       (!n m h e. DILATE e n m [h] = [h]) /\
                       !v9 v8 n m h e. DILATE e n m (h::v8::v9) =
                        h:: (TAKE n (v8::v9) ++ GENLIST (K e) m ++ DILATE e n m (DROP n (v8::v9)))
#  DILATE_NIL       |- !n m e. DILATE e n m [] = []
#  DILATE_SING      |- !n m h e. DILATE e n m [h] = [h]
   DILATE_CONS      |- !n m h t e. DILATE e n m (h::t) =
                        if t = [] then [h] else h::(TAKE n t ++ GENLIST (K e) m ++ DILATE e n m (DROP n t))
   DILATE_0_CONS    |- !n h t e. DILATE e 0 n (h::t) =
                        if t = [] then [h] else h::(GENLIST (K e) n ++ DILATE e 0 n t)
   DILATE_0_0       |- !l e. DILATE e 0 0 l = l
   DILATE_0_SUC     |- !l e n. DILATE e 0 (SUC n) l = DILATE e n 1 (DILATE e 0 n l)
   DILATE_0_LENGTH  |- !l e n. LENGTH (DILATE e 0 n l) = if l = [] then 0 else SUC (SUC n * PRE (LENGTH l))
   DILATE_0_LENGTH_LOWER  |- !l e n. LENGTH l <= LENGTH (DILATE e 0 n l)
   DILATE_0_LENGTH_UPPER   |- !l e n. LENGTH (DILATE e 0 n l) <= SUC (SUC n * PRE (LENGTH l))
   DILATE_0_EL      |- !l e n k. k < LENGTH (DILATE e 0 n l) ==>
                        (EL k (DILATE e 0 n l) = if k MOD SUC n = 0 then EL (k DIV SUC n) l else e)
   DILATE_0_EQ_NIL  |- !l e n. (DILATE e 0 n l = []) <=> (l = [])
   DILATE_0_LAST    |- !l e n. LAST (DILATE e 0 n l) = LAST l

*)

(* ------------------------------------------------------------------------- *)
(* List Theorems                                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ls <> [] <=> (ls = HD ls::TL ls) *)
(* Proof:
   If part: ls <> [] ==> (ls = HD ls::TL ls)
       ls <> []
   ==> ?h t. ls = h::t         by list_CASES
   ==> ls = (HD ls)::(TL ls)   by HD, TL
   Only-if part: (ls = HD ls::TL ls) ==> ls <> []
   This is true                by NOT_NIL_CONS
*)
val LIST_NOT_NIL = store_thm(
  "LIST_NOT_NIL",
  ``!ls. ls <> [] <=> (ls = HD ls::TL ls)``,
  metis_tac[list_CASES, HD, TL, NOT_NIL_CONS]);

(* NOT_NIL_EQ_LENGTH_NOT_0  |- x <> [] <=> 0 < LENGTH x *)

(* Theorem: 0 < LENGTH ls <=> (ls = HD ls::TL ls) *)
(* Proof:
   If part: 0 < LENGTH ls ==> (ls = HD ls::TL ls)
      Note LENGTH ls <> 0                       by arithmetic
        so ~(NULL l)                            by NULL_LENGTH
        or ls = HD ls :: TL ls                  by CONS
   Only-if part: (ls = HD ls::TL ls) ==> 0 < LENGTH ls
      Note LENGTH ls = SUC (LENGTH (TL ls))     by LENGTH
       but 0 < SUC (LENGTH (TL ls))             by SUC_POS
*)
val LIST_HEAD_TAIL = store_thm(
  "LIST_HEAD_TAIL",
  ``!ls. 0 < LENGTH ls <=> (ls = HD ls::TL ls)``,
  metis_tac[LIST_NOT_NIL, NOT_NIL_EQ_LENGTH_NOT_0]);

(* Theorem: p <> [] /\ q <> [] ==> ((p = q) <=> ((HD p = HD q) /\ (TL p = TL q))) *)
(* Proof: by cases on p and cases on q, CONS_11 *)
val LIST_EQ_HEAD_TAIL = store_thm(
  "LIST_EQ_HEAD_TAIL",
  ``!p q. p <> [] /\ q <> [] ==>
         ((p = q) <=> ((HD p = HD q) /\ (TL p = TL q)))``,
  (Cases_on `p` >> Cases_on `q` >> fs[]));

(* Theorem: [x] = [y] <=> x = y *)
(* Proof: by EQ_LIST and notation. *)
val LIST_SING_EQ = store_thm(
  "LIST_SING_EQ",
  ``!x y. ([x] = [y]) <=> (x = y)``,
  rw_tac bool_ss[]);

(* Note: There is LENGTH_NIL, but no LENGTH_NON_NIL *)

(* Theorem: 0 < LENGTH l <=> l <> [] *)
(* Proof:
   Since  (LENGTH l = 0) <=> (l = [])   by LENGTH_NIL
   l <> [] <=> LENGTH l <> 0,
            or 0 < LENGTH l             by NOT_ZERO_LT_ZERO
*)
val LENGTH_NON_NIL = store_thm(
  "LENGTH_NON_NIL",
  ``!l. 0 < LENGTH l <=> l <> []``,
  metis_tac[LENGTH_NIL, NOT_ZERO_LT_ZERO]);

(* val LENGTH_EQ_0 = save_thm("LENGTH_EQ_0", LENGTH_EQ_NUM |> CONJUNCT1); *)
val LENGTH_EQ_0 = save_thm("LENGTH_EQ_0", LENGTH_NIL);
(* > val LENGTH_EQ_0 = |- !l. (LENGTH l = 0) <=> (l = []): thm *)

(* Theorem: (LENGTH l = 1) <=> ?x. l = [x] *)
(* Proof:
   If part: (LENGTH l = 1) ==> ?x. l = [x]
     Since LENGTH l <> 0, l <> []  by LENGTH_NIL
        or ?h t. l = h::t          by list_CASES
       and LENGTH t = 0            by LENGTH
        so t = []                  by LENGTH_NIL
     Hence l = [x]
   Only-if part: (l = [x]) ==> (LENGTH l = 1)
     True by LENGTH.
*)
val LENGTH_EQ_1 = store_thm(
  "LENGTH_EQ_1",
  ``!l. (LENGTH l = 1) <=> ?x. l = [x]``,
  rw[EQ_IMP_THM] >| [
    `LENGTH l <> 0` by decide_tac >>
    `?h t. l = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    `SUC (LENGTH t) = 1` by metis_tac[LENGTH] >>
    `LENGTH t = 0` by decide_tac >>
    metis_tac[LENGTH_NIL],
    rw[]
  ]);

(* Theorem: LENGTH [x] = 1 *)
(* Proof: by LENGTH, ONE. *)
val LENGTH_SING = store_thm(
  "LENGTH_SING",
  ``!x. LENGTH [x] = 1``,
  rw_tac bool_ss[LENGTH, ONE]);

(* Theorem: ls <> [] ==> LENGTH (TL ls) < LENGTH ls *)
(* Proof: by LENGTH_TL, LENGTH_EQ_0 *)
val LENGTH_TL_LT = store_thm(
  "LENGTH_TL_LT",
  ``!ls. ls <> [] ==> LENGTH (TL ls) < LENGTH ls``,
  metis_tac[LENGTH_TL, LENGTH_EQ_0, NOT_ZERO_LT_ZERO, DECIDE``n <> 0 ==> n - 1 < n``]);

val SNOC_NIL = save_thm("SNOC_NIL", SNOC |> CONJUNCT1);
(* > val SNOC_NIL = |- !x. SNOC x [] = [x]: thm *)
val SNOC_CONS = save_thm("SNOC_CONS", SNOC |> CONJUNCT2);
(* > val SNOC_CONS = |- !x x' l. SNOC x (x'::l) = x'::SNOC x l: thm *)

(* Theorem: l <> [] ==> (l = SNOC (LAST l) (FRONT l)) *)
(* Proof:
     l
   = FRONT l ++ [LAST l]      by APPEND_FRONT_LAST, l <> []
   = SNOC (LAST l) (FRONT l)  by SNOC_APPEND
*)
val SNOC_LAST_FRONT = store_thm(
  "SNOC_LAST_FRONT",
  ``!l. l <> [] ==> (l = SNOC (LAST l) (FRONT l))``,
  rw[APPEND_FRONT_LAST]);

(* Theorem alias *)
val MAP_COMPOSE = save_thm("MAP_COMPOSE", MAP_MAP_o);
(* val MAP_COMPOSE = |- !f g l. MAP f (MAP g l) = MAP (f o g) l: thm *)

(* Theorem: MAP f [x] = [f x] *)
(* Proof: by MAP *)
val MAP_SING = store_thm(
  "MAP_SING",
  ``!f x. MAP f [x] = [f x]``,
  rw[]);

(* listTheory.MAP_TL  |- !l f. MAP f (TL l) = TL (MAP f l) *)

(* Theorem: ls <> [] ==> HD (MAP f ls) = f (HD ls) *)
(* Proof:
   Note 0 < LENGTH ls              by LENGTH_NON_NIL
        HD (MAP f ls)
      = EL 0 (MAP f ls)            by EL
      = f (EL 0 ls)                by EL_MAP, 0 < LENGTH ls
      = f (HD ls)                  by EL
*)
Theorem MAP_HD:
  !ls f. ls <> [] ==> HD (MAP f ls) = f (HD ls)
Proof
  metis_tac[EL_MAP, EL, LENGTH_NON_NIL]
QED


(*
LAST_EL  |- !ls. ls <> [] ==> LAST ls = EL (PRE (LENGTH ls)) ls
*)

(* Theorem: t <> [] ==> (LAST t = EL (LENGTH t) (h::t)) *)
(* Proof:
   Note LENGTH t <> 0                      by LENGTH_EQ_0
     or 0 < LENGTH t
        LAST t
      = EL (PRE (LENGTH t)) t              by LAST_EL
      = EL (SUC (PRE (LENGTH t))) (h::t)   by EL
      = EL (LENGTH t) (h::t)               bu SUC_PRE, 0 < LENGTH t
*)
val LAST_EL_CONS = store_thm(
  "LAST_EL_CONS",
  ``!h t. t <> [] ==> (LAST t = EL (LENGTH t) (h::t))``,
  rpt strip_tac >>
  `0 < LENGTH t` by metis_tac[LENGTH_EQ_0, NOT_ZERO_LT_ZERO] >>
  `LAST t = EL (PRE (LENGTH t)) t` by rw[LAST_EL] >>
  `_ = EL (SUC (PRE (LENGTH t))) (h::t)` by rw[] >>
  metis_tac[SUC_PRE]);

(* Theorem alias *)
val FRONT_LENGTH = save_thm ("FRONT_LENGTH", LENGTH_FRONT);
(* val FRONT_LENGTH = |- !l. l <> [] ==> (LENGTH (FRONT l) = PRE (LENGTH l)): thm *)

(* Theorem: l <> [] /\ n < LENGTH (FRONT l) ==> (EL n (FRONT l) = EL n l) *)
(* Proof: by EL_FRONT, NULL *)
val FRONT_EL = store_thm(
  "FRONT_EL",
  ``!l n. l <> [] /\ n < LENGTH (FRONT l) ==> (EL n (FRONT l) = EL n l)``,
  metis_tac[EL_FRONT, NULL, list_CASES]);

(* Theorem: (LENGTH l = 1) ==> (FRONT l = []) *)
(* Proof:
   Note ?x. l = [x]     by LENGTH_EQ_1
     FRONT l
   = FRONT [x]          by above
   = []                 by FRONT_DEF
*)
val FRONT_EQ_NIL = store_thm(
  "FRONT_EQ_NIL",
  ``!l. (LENGTH l = 1) ==> (FRONT l = [])``,
  rw[LENGTH_EQ_1] >>
  rw[FRONT_DEF]);

(* Theorem: 1 < LENGTH l ==> FRONT l <> [] *)
(* Proof:
   Note LENGTH l <> 0          by 1 < LENGTH l
   Thus ?h s. l = h::s         by list_CASES
     or 1 < 1 + LENGTH s
     so 0 < LENGTH s           by arithmetic
   Thus ?k t. s = k::t         by list_CASES
      FRONT l
    = FRONT (h::k::t)
    = h::FRONT (k::t)          by FRONT_CONS
    <> []                      by list_CASES
*)
val FRONT_NON_NIL = store_thm(
  "FRONT_NON_NIL",
  ``!l. 1 < LENGTH l ==> FRONT l <> []``,
  rpt strip_tac >>
  `LENGTH l <> 0` by decide_tac >>
  `?h s. l = h::s` by metis_tac[list_CASES, LENGTH_EQ_0] >>
  `LENGTH l = 1 + LENGTH s` by rw[] >>
  `LENGTH s <> 0` by decide_tac >>
  `?k t. s = k::t` by metis_tac[list_CASES, LENGTH_EQ_0] >>
  `FRONT l = h::FRONT (k::t)` by fs[FRONT_CONS] >>
  fs[]);

(* Theorem: ls <> [] ==> MEM (HD ls) ls *)
(* Proof:
   Note ls = h::t      by list_CASES
        MEM (HD (h::t)) (h::t)
    <=> MEM h (h::t)   by HD
    <=> T              by MEM
*)
val HEAD_MEM = store_thm(
  "HEAD_MEM",
  ``!ls. ls <> [] ==> MEM (HD ls) ls``,
  (Cases_on `ls` >> simp[]));

(* Theorem: ls <> [] ==> MEM (LAST ls) ls *)
(* Proof:
   By induction on ls.
   Base: [] <> [] ==> MEM (LAST []) []
      True by [] <> [] = F.
   Step: ls <> [] ==> MEM (LAST ls) ls ==>
         !h. h::ls <> [] ==> MEM (LAST (h::ls)) (h::ls)
      If ls = [],
             MEM (LAST [h]) [h]
         <=> MEM h [h]          by LAST_DEF
         <=> T                  by MEM
      If ls <> [],
             MEM (LAST [h::ls]) (h::ls)
         <=> MEM (LAST ls) (h::ls)             by LAST_DEF
         <=> LAST ls = h \/ MEM (LAST ls) ls   by MEM
         <=> LAST ls = h \/ T                  by induction hypothesis
         <=> T                                 by logical or
*)
val LAST_MEM = store_thm(
  "LAST_MEM",
  ``!ls. ls <> [] ==> MEM (LAST ls) ls``,
  Induct >-
  decide_tac >>
  (Cases_on `ls = []` >> rw[LAST_DEF]));

(* Idea: the last equals the head when there is no tail. *)

(* Theorem: ~MEM h t /\ LAST (h::t) = h <=> t = [] *)
(* Proof:
   If part: ~MEM h t /\ LAST (h::t) = h ==> t = []
      By contradiction, suppose t <> [].
      Then h = LAST (h::t) = LAST t            by LAST_CONS_cond, t <> []
        so MEM h t                             by LAST_MEM
      This contradicts ~MEM h t.
   Only-if part: t = [] ==> ~MEM h t /\ LAST (h::t) = h
      Note MEM h [] = F, so ~MEM h [] = T      by MEM
       and LAST [h] = h                        by LAST_CONS
*)
Theorem LAST_EQ_HD:
  !h t. ~MEM h t /\ LAST (h::t) = h <=> t = []
Proof
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  metis_tac[LAST_CONS_cond, LAST_MEM]
QED

(* Theorem: ls <> [] /\ ALL_DISTINCT ls ==> ~MEM (LAST ls) (FRONT ls) *)
(* Proof:
   Let k = LENGTH ls.
   Then 0 < k                                  by LENGTH_EQ_0, NOT_ZERO
    and LENGTH (FRONT ls) = PRE k              by LENGTH_FRONT, ls <> []
     so ?n. n < PRE k /\
        LAST ls = EL n (FRONT ls)              by MEM_EL
                = EL n ls                      by FRONT_EL, ls <> []
    but LAST ls = EL (PRE k) ls                by LAST_EL, ls <> []
   Thus n = PRE k                              by ALL_DISTINCT_EL_IMP
   This contradicts n < PRE k                  by arithmetic
*)
Theorem MEM_FRONT_NOT_LAST:
  !ls. ls <> [] /\ ALL_DISTINCT ls ==> ~MEM (LAST ls) (FRONT ls)
Proof
  rpt strip_tac >>
  qabbrev_tac `k = LENGTH ls` >>
  `0 < k` by metis_tac[LENGTH_EQ_0, NOT_ZERO] >>
  `LENGTH (FRONT ls) = PRE k` by fs[LENGTH_FRONT, Abbr`k`] >>
  fs[MEM_EL] >>
  `LAST ls = EL n ls` by fs[FRONT_EL] >>
  `LAST ls = EL (PRE k) ls` by rfs[LAST_EL, Abbr`k`] >>
  `n < k /\ PRE k < k` by decide_tac >>
  `n = PRE k` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  decide_tac
QED

(* Theorem: ls = [] <=> !x. ~MEM x ls *)
(* Proof:
   If part: !x. ~MEM x [], true    by MEM
   Only-if part: !x. ~MEM x ls ==> ls = []
      By contradiction, suppose ls <> [].
      Then ?h t. ls = h::t         by list_CASES
       and MEM h ls                by MEM
      which contradicts !x. ~MEM x ls.
*)
Theorem NIL_NO_MEM:
  !ls. ls = [] <=> !x. ~MEM x ls
Proof
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  metis_tac[list_CASES, MEM]
QED

(*
el_append3
|- !l1 x l2. EL (LENGTH l1) (l1 ++ [x] ++ l2) = x
*)

(* Theorem: MEM h (l1 ++ [x] ++ l2) <=> MEM h (x::(l1 ++ l2)) *)
(* Proof:
       MEM h (l1 ++ [x] ++ l2)
   <=> MEM h l1 \/ h = x \/ MEM h l2     by MEM, MEM_APPEND
   <=> h = x \/ MEM h l1 \/ MEM h l2
   <=> h = x \/ MEM h (l1 ++ l2)         by MEM_APPEND
   <=> MEM h (x::(l1 + l2))              by MEM
*)
Theorem MEM_APPEND_3:
  !l1 x l2 h. MEM h (l1 ++ [x] ++ l2) <=> MEM h (x::(l1 ++ l2))
Proof
  rw[] >>
  metis_tac[]
QED

(* Theorem: DROP 1 (h::t) = t *)
(* Proof: DROP_def *)
val DROP_1 = store_thm(
  "DROP_1",
  ``!h t. DROP 1 (h::t) = t``,
  rw[]);

(* Theorem: FRONT [x] = [] *)
(* Proof: FRONT_def *)
val FRONT_SING = store_thm(
  "FRONT_SING",
  ``!x. FRONT [x] = []``,
  rw[]);

(* Theorem: ls <> [] ==> (TL ls = DROP 1 ls) *)
(* Proof:
   Note ls = h::t        by list_CASES
     so TL (h::t)
      = t                by TL
      = DROP 1 (h::t)    by DROP_def
*)
val TAIL_BY_DROP = store_thm(
  "TAIL_BY_DROP",
  ``!ls. ls <> [] ==> (TL ls = DROP 1 ls)``,
  Cases_on `ls` >-
  decide_tac >>
  rw[]);

(* Theorem: ls <> [] ==> (FRONT ls = TAKE (LENGTH ls - 1) ls) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] ==> FRONT [] = TAKE (LENGTH [] - 1) []
      True by [] <> [] = F.
   Step: ls <> [] ==> FRONT ls = TAKE (LENGTH ls - 1) ls ==>
         !h. h::ls <> [] ==> FRONT (h::ls) = TAKE (LENGTH (h::ls) - 1) (h::ls)
      If ls = [],
           FRONT [h]
         = []                          by FRONT_SING
         = TAKE 0 [h]                  by TAKE_0
         = TAKE (LENGTH [h] - 1) [h]   by LENGTH_SING
      If ls <> [],
           FRONT (h::ls)
         = h::FRONT ls                        by FRONT_DEF
         = h::TAKE (LENGTH ls - 1) ls         by induction hypothesis
         = TAKE (LENGTH (h::ls) - 1) (h::ls)  by TAKE_def
*)
val FRONT_BY_TAKE = store_thm(
  "FRONT_BY_TAKE",
  ``!ls. ls <> [] ==> (FRONT ls = TAKE (LENGTH ls - 1) ls)``,
  Induct >-
  decide_tac >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `LENGTH ls <> 0` by rw[] >>
  rw[FRONT_DEF]);

(* Theorem: HD (h::t ++ ls) = h *)
(* Proof:
     HD (h::t ++ ls)
   = HD (h::(t ++ ls))     by APPEND
   = h                     by HD
*)
Theorem HD_APPEND:
  !h t ls. HD (h::t ++ ls) = h
Proof
  simp[]
QED

(* Theorem: 0 <> n ==> (EL (n-1) t = EL n (h::t)) *)
(* Proof:
   Note n = SUC k for some k         by num_CASES
     so EL k t = EL (SUC k) (h::t)   by EL_restricted
*)
Theorem EL_TAIL:
  !h t n. 0 <> n ==> (EL (n-1) t = EL n (h::t))
Proof
  rpt strip_tac >>
  `n = SUC (n - 1)` by decide_tac >>
  metis_tac[EL_restricted]
QED

(* Idea: If all elements are the same, the set is SING. *)

(* Theorem: ls <> [] /\ EVERY ($= c) ls ==> SING (set ls) *)
(* Proof:
   Note set ls = {c}       by LIST_TO_SET_EQ_SING
   thus SING (set ls)      by SING_DEF
*)
Theorem MONOLIST_SET_SING:
  !c ls. ls <> [] /\ EVERY ($= c) ls ==> SING (set ls)
Proof
  metis_tac[LIST_TO_SET_EQ_SING, SING_DEF]
QED

(*
> EVAL ``set [3;3;3]``;
val it = |- set [3; 3; 3] = set [3; 3; 3]: thm
*)

(* Put LIST_TO_SET into compute *)
(* Near: put to helperList *)
Theorem LIST_TO_SET_EVAL[compute] = LIST_TO_SET |> GEN_ALL;
(* val LIST_TO_SET_EVAL = |- !t h. set [] = {} /\ set (h::t) = h INSERT set t: thm *)
(* cannot add to computeLib directly LIST_TO_SET, which is not in current theory. *)

(*
> EVAL ``set [3;3;3]``;
val it = |- set [3; 3; 3] = {3}: thm
*)

(* Theorem: set ls = count n ==> !j. j < LENGTH ls ==> EL j ls < n *)
(* Proof:
   Note MEM (EL j ls) ls       by EL_MEM
     so EL j ls IN (count n)   by set ls = count n
     or EL j ls < n            by IN_COUNT
*)
Theorem set_list_eq_count:
  !ls n. set ls = count n ==> !j. j < LENGTH ls ==> EL j ls < n
Proof
  metis_tac[EL_MEM, IN_COUNT]
QED

(* Theorem: set ls = IMAGE (\j. EL j ls) (count (LENGTH ls)) *)
(* Proof:
   Let f = \j. EL j ls, n = LENGTH ls.
       x IN IMAGE f (count n)
   <=> ?j. x = f j /\ j IN (count n)     by IN_IMAGE
   <=> ?j. x = EL j ls /\ j < n          by notation, IN_COUNT
   <=> MEM x ls                          by MEM_EL
   <=> x IN set ls                       by notation
   Thus set ls = IMAGE f (count n)       by EXTENSION
*)
Theorem list_to_set_eq_el_image:
  !ls. set ls = IMAGE (\j. EL j ls) (count (LENGTH ls))
Proof
  rw[EXTENSION] >>
  metis_tac[MEM_EL]
QED

(* Theorem: ALL_DISTINCT ls ==> INJ (\j. EL j ls) (count (LENGTH ls)) univ(:num) *)
(* Proof:
   By INJ_DEF this is to show:
   (1) EL j ls IN univ(:'a), true  by IN_UNIV, function type
   (2) !x y. x < LENGTH ls /\ y < LENGTH ls /\ EL x ls = EL y ls ==> x = y
       This is true                by ALL_DISTINCT_EL_IMP, ALL_DISTINCT ls
*)
Theorem all_distinct_list_el_inj:
  !ls. ALL_DISTINCT ls ==> INJ (\j. EL j ls) (count (LENGTH ls)) univ(:'a)
Proof
  rw[INJ_DEF, ALL_DISTINCT_EL_IMP]
QED

(* ------------------------------------------------------------------------- *)
(* List Reversal.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Overload for REVERSE [m .. n] *)
val _ = overload_on ("downto", ``\n m. REVERSE [m .. n]``);
val _ = set_fixity "downto" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: REVERSE [x] = [x] *)
(* Proof:
      REVERSE [x]
    = [] ++ [x]       by REVERSE_DEF
    = [x]             by APPEND
*)
val REVERSE_SING = store_thm(
  "REVERSE_SING",
  ``!x. REVERSE [x] = [x]``,
  rw[]);

(* Theorem: ls <> [] ==> (HD (REVERSE ls) = LAST ls) *)
(* Proof:
      HD (REVERSE ls)
    = HD (REVERSE (SNOC (LAST ls) (FRONT ls)))   by SNOC_LAST_FRONT
    = HD (LAST ls :: (REVERSE (FRONT ls))        by REVERSE_SNOC
    = LAST ls                                    by HD
*)
Theorem REVERSE_HD:
  !ls. ls <> [] ==> (HD (REVERSE ls) = LAST ls)
Proof
  metis_tac[SNOC_LAST_FRONT, REVERSE_SNOC, HD]
QED

(* Theorem: ls <> [] ==> (TL (REVERSE ls) = REVERSE (FRONT ls)) *)
(* Proof:
      TL (REVERSE ls)
    = TL (REVERSE (SNOC (LAST ls) (FRONT ls)))   by SNOC_LAST_FRONT
    = TL (LAST ls :: (REVERSE (FRONT ls))        by REVERSE_SNOC
    = REVERSE (FRONT ls)                         by TL
*)
Theorem REVERSE_TL:
  !ls. ls <> [] ==> (TL (REVERSE ls) = REVERSE (FRONT ls))
Proof
  metis_tac[SNOC_LAST_FRONT, REVERSE_SNOC, TL]
QED

(* ------------------------------------------------------------------------- *)
(* List Index.                                                               *)
(* ------------------------------------------------------------------------- *)

(* Extract theorems for findi *)

Theorem findi_nil = findi_def |> CONJUNCT1;
(* val findi_nil = |- !x. findi x [] = 0: thm *)

Theorem findi_cons = findi_def |> CONJUNCT2;
(* val findi_cons = |- !x h t. findi x (h::t) = if x = h then 0 else 1 + findi x t: thm *)

(* Theorem: ~MEM x ls ==> findi x ls = LENGTH ls *)
(* Proof:
   By induction on ls.
   Base: ~MEM x [] ==> findi x [] = LENGTH []
         findi x []
       = 0                         by findi_nil
       = LENGTH []                 by LENGTH
   Step:  ~MEM x ls ==> findi x ls = LENGTH ls ==>
         !h. ~MEM x (h::ls) ==> findi x (h::ls) = LENGTH (h::ls)
       Note ~MEM x (h::ls)
        ==> x <> h /\ ~MEM x ls    by MEM
       Thus findi x (h::ls)
          = 1 + findi x ls         by findi_cons
          = 1 + LENGTH ls          by induction hypothesis
          = SUC (LENGTH ls)        by ADD1
          = LENGTH (h::ls)         by LENGTH
*)
Theorem findi_none:
  !ls x. ~MEM x ls ==> findi x ls = LENGTH ls
Proof
  rpt strip_tac >>
  Induct_on `ls` >-
  simp[findi_nil] >>
  simp[findi_cons]
QED

(* Theorem: findi x (l1 ++ l2) = if MEM x l1 then findi x l1 else LENGTH l1 + findi x l2 *)
(* Proof:
   By induction on l1.
   Base: findi x ([] ++ l2) = if MEM x [] then findi x [] else LENGTH [] + findi x l2
      Note MEM x [] = F            by MEM
        so findi x ([] ++ l2)
         = findi x l2              by APPEND
         = 0 + findi x l2          by ADD
         = LENGTH [] + findi x l2  by LENGTH
   Step: findi x (l1 ++ l2) = if MEM x l1 then findi x l1 else LENGTH l1 + findi x l2 ==>
         !h. findi x (h::l1 ++ l2) = if MEM x (h::l1) then findi x (h::l1)
                                     else LENGTH (h::l1) + findi x l2

      Note findi x (h::l1 ++ l2)
         = if x = h then 0 else 1 + findi x (l1 ++ l2)     by findi_cons

      Case: MEM x (h::l1).
      To show: findi x (h::l1 ++ l2) = findi x (h::l1).
      Note MEM x (h::l1)
       <=> x = h \/ MEM x l1       by MEM
      If x = h,
           findi x (h::l1 ++ l2)
         = 0 = findi x (h::l1)     by findi_cons
      If x <> h, then MEM x l1.
           findi x (h::l1 ++ l2)
         = 1 + findi x (l1 ++ l2)  by x <> h
         = 1 + findi x l1          by induction hypothesis
         = findi x (h::l1)         by findi_cons

      Case: ~MEM x (h::l1).
      To show: findi x (h::l1 ++ l2) = LENGTH (h::l1) + findi x l2.
      Note ~MEM x (h::l1)
       <=> x <> h /\ ~MEM x l1     by MEM
           findi x (h::l1 ++ l2)
         = 1 + findi x (l1 ++ l2)  by x <> h
         = 1 + (LENGTH l1 + findi x l2)        by induction hypothesis
         = (1 + LENGTH l1) + findi x l2        by arithmetic
         = LENGTH (h::l1) + findi x l2         by LENGTH
*)
Theorem findi_APPEND:
  !l1 l2 x. findi x (l1 ++ l2) = if MEM x l1 then findi x l1 else LENGTH l1 + findi x l2
Proof
  rpt strip_tac >>
  Induct_on `l1` >-
  simp[] >>
  (rw[findi_cons] >> fs[])
QED

(* Theorem: ALL_DISTINCT ls /\ MEM x ls /\ n < LENGTH ls ==> (x = EL n ls <=> findi x ls = n) *)
(* Proof:
   If part: x = EL n ls ==> findi x ls = n
      Given ALL_DISTINCT ls /\ n < LENGTH ls
      This is true             by findi_EL
   Only-if part: findi x ls = n ==> x = EL n ls
      Given MEM x ls
      This is true             by EL_findi
*)
Theorem findi_EL_iff:
  !ls x n. ALL_DISTINCT ls /\ MEM x ls /\ n < LENGTH ls ==> (x = EL n ls <=> findi x ls = n)
Proof
  metis_tac[findi_EL, EL_findi]
QED

(* ------------------------------------------------------------------------- *)
(* Extra List Theorems                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: EVERY (\c. c IN R) p ==> !k. k < LENGTH p ==> EL k p IN R *)
(* Proof: by EVERY_EL. *)
val EVERY_ELEMENT_PROPERTY = store_thm(
  "EVERY_ELEMENT_PROPERTY",
  ``!p R. EVERY (\c. c IN R) p ==> !k. k < LENGTH p ==> EL k p IN R``,
  rw[EVERY_EL]);

(* Theorem: (!x. P x ==> (Q o f) x) /\ EVERY P l ==> EVERY Q (MAP f l) *)
(* Proof:
   Since !x. P x ==> (Q o f) x,
         EVERY P l
     ==> EVERY Q o f l         by EVERY_MONOTONIC
     ==> EVERY Q (MAP f l)     by EVERY_MAP
*)
val EVERY_MONOTONIC_MAP = store_thm(
  "EVERY_MONOTONIC_MAP",
  ``!l f P Q. (!x. P x ==> (Q o f) x) /\ EVERY P l ==> EVERY Q (MAP f l)``,
  metis_tac[EVERY_MONOTONIC, EVERY_MAP]);

(* Theorem: EVERY (\j. j < n) ls ==> EVERY (\j. j <= n) ls *)
(* Proof: by EVERY_EL, arithmetic. *)
val EVERY_LT_IMP_EVERY_LE = store_thm(
  "EVERY_LT_IMP_EVERY_LE",
  ``!ls n. EVERY (\j. j < n) ls ==> EVERY (\j. j <= n) ls``,
  simp[EVERY_EL, LESS_IMP_LESS_OR_EQ]);

(* Theorem: LENGTH l1 = LENGTH l2 ==> ZIP (SNOC x1 l1, SNOC x2 l2) = SNOC (x1, x2) ZIP (l1, l2) *)
(* Proof:
   By induction on l1,
   Base case: !l2. (LENGTH [] = LENGTH l2) ==> (ZIP (SNOC x1 [],SNOC x2 l2) = SNOC (x1,x2) (ZIP ([],l2)))
     Since LENGTH l2 = LENGTH [] = 0, l2 = []      by LENGTH_NIL
       ZIP (SNOC x1 [],SNOC x2 [])
     = ZIP ([x1], [x2])              by SNOC
     = ([x1], [x2])                  by ZIP
     = SNOC ([x1], [x2]) []          by SNOC
     = SNOC ([x1], [x2]) ZIP ([][])  by ZIP
   Step case: !h l2. (LENGTH (h::l1) = LENGTH l2) ==> (ZIP (SNOC x1 (h::l1),SNOC x2 l2) = SNOC (x1,x2) (ZIP (h::l1,l2)))
     Expand by LENGTH_CONS, this is to show:
       ZIP (h::(l1 ++ [x1]),h'::l' ++ [x2]) = ZIP (h::l1,h'::l') ++ [(x1,x2)]
       ZIP (h::(l1 ++ [x1]),h'::l' ++ [x2])
     = (h, h') :: ZIP (l1 ++ [x1],l' ++ [x2])       by ZIP
     = (h, h') :: ZIP (SNOC x1 l1, SNOC x2 l')      by SNOC
     = (h, h') :: SNOC (x1, x2) (ZIP (l1, l'))      by induction hypothesis
     = (h, h') :: ZIP (l1, l') ++ [(x1, x2)]        by SNOC
     = ZIP (h::l1, h'::l') ++ [(x1, x2)]            by ZIP
*)
val ZIP_SNOC = store_thm(
  "ZIP_SNOC",
  ``!x1 x2 l1 l2. (LENGTH l1 = LENGTH l2) ==> (ZIP (SNOC x1 l1, SNOC x2 l2) = SNOC (x1, x2) (ZIP (l1, l2)))``,
  ntac 2 strip_tac >>
  Induct_on `l1` >-
  rw[] >>
  rw[LENGTH_CONS] >>
  `ZIP (h::(l1 ++ [x1]),h'::l' ++ [x2]) = (h, h') :: ZIP (l1 ++ [x1],l' ++ [x2])` by rw[] >>
  `_ = (h, h') :: ZIP (SNOC x1 l1, SNOC x2 l')` by rw[] >>
  `_ = (h, h') :: SNOC (x1, x2) (ZIP (l1, l'))` by metis_tac[] >>
  `_ = (h, h') :: ZIP (l1, l') ++ [(x1, x2)]` by rw[] >>
  `_ = ZIP (h::l1, h'::l') ++ [(x1, x2)]` by rw[] >>
  metis_tac[]);

(* MAP_ZIP_SAME  |- !ls f. MAP f (ZIP (ls,ls)) = MAP (\x. f (x,x)) ls *)

(* Theorem: ZIP ((MAP f ls), (MAP g ls)) = MAP (\x. (f x, g x)) ls *)
(* Proof:
     ZIP ((MAP f ls), (MAP g ls))
   = MAP (\(x, y). (f x, y)) (ZIP (ls, (MAP g ls)))                    by ZIP_MAP
   = MAP (\(x, y). (f x, y)) (MAP (\(x, y). (x, g y)) (ZIP (ls, ls)))  by ZIP_MAP
   = MAP (\(x, y). (f x, y)) (MAP (\j. (\(x, y). (x, g y)) (j,j)) ls)  by MAP_ZIP_SAME
   = MAP (\(x, y). (f x, y)) o (\j. (\(x, y). (x, g y)) (j,j)) ls      by MAP_COMPOSE
   = MAP (\x. (f x, g x)) ls                                           by FUN_EQ_THM
*)
val ZIP_MAP_MAP = store_thm(
  "ZIP_MAP_MAP",
  ``!ls f g. ZIP ((MAP f ls), (MAP g ls)) = MAP (\x. (f x, g x)) ls``,
  rw[ZIP_MAP, MAP_COMPOSE] >>
  qabbrev_tac `f1 = \p. (f (FST p),SND p)` >>
  qabbrev_tac `f2 = \x. (x,g x)` >>
  qabbrev_tac `f3 = \x. (f x,g x)` >>
  `f1 o f2 = f3` by rw[FUN_EQ_THM, Abbr`f1`, Abbr`f2`, Abbr`f3`] >>
  rw[]);

(* Theorem: MAP2 f (MAP g1 ls) (MAP g2 ls) = MAP (\x. f (g1 x) (g2 x)) ls *)
(* Proof:
   Let k = LENGTH ls.
     Note LENGTH (MAP g1 ls) = k      by LENGTH_MAP
      and LENGTH (MAP g2 ls) = k      by LENGTH_MAP
     MAP2 f (MAP g1 ls) (MAP g2 ls)
   = MAP (UNCURRY f) (ZIP ((MAP g1 ls), (MAP g2 ls)))      by MAP2_MAP
   = MAP (UNCURRY f) (MAP (\x. (g1 x, g2 x)) ls)           by ZIP_MAP_MAP
   = MAP ((UNCURRY f) o (\x. (g1 x, g2 x))) ls             by MAP_COMPOSE
   = MAP (\x. f (g1 x) (g2 y)) ls                          by FUN_EQ_THM
*)
val MAP2_MAP_MAP = store_thm(
  "MAP2_MAP_MAP",
  ``!ls f g1 g2. MAP2 f (MAP g1 ls) (MAP g2 ls) = MAP (\x. f (g1 x) (g2 x)) ls``,
  rw[MAP2_MAP, ZIP_MAP_MAP, MAP_COMPOSE] >>
  qabbrev_tac `f1 = UNCURRY f o (\x. (g1 x,g2 x))` >>
  qabbrev_tac `f2 = \x. f (g1 x) (g2 x)` >>
  `f1 = f2` by rw[FUN_EQ_THM, Abbr`f1`, Abbr`f2`] >>
  rw[]);

(* Theorem: EL n (l1 ++ l2) = if n < LENGTH l1 then EL n l1 else EL (n - LENGTH l1) l2 *)
(* Proof: by EL_APPEND1, EL_APPEND2 *)
val EL_APPEND = store_thm(
  "EL_APPEND",
  ``!n l1 l2. EL n (l1 ++ l2) = if n < LENGTH l1 then EL n l1 else EL (n - LENGTH l1) l2``,
  rw[EL_APPEND1, EL_APPEND2]);

(* Theorem: j < LENGTH ls ==> ?l1 l2. ls = l1 ++ (EL j ls)::l2 *)
(* Proof:
   Let x = EL j ls.
   Then MEM x ls                   by EL_MEM, j < LENGTH ls
     so ?l1 l2. l = l1 ++ x::l2    by MEM_SPLIT
   Pick these l1 and l2.
*)
Theorem EL_SPLIT:
  !ls j. j < LENGTH ls ==> ?l1 l2. ls = l1 ++ (EL j ls)::l2
Proof
  metis_tac[EL_MEM, MEM_SPLIT]
QED

(* Theorem: j < k /\ k < LENGTH ls ==>
            ?l1 l2 l3. ls = l1 ++ (EL j ls)::l2 ++ (EL k ls)::l3 *)
(* Proof:
   Let a = EL j ls,
       b = EL k ls.
   Note j < LENGTH ls          by j < k, k < LENGTH ls
     so MEM a ls /\ MEM b ls   by MEM_EL

    Now ls
      = TAKE k ls ++ DROP k ls                 by TAKE_DROP
      = TAKE k ls ++ b::(DROP (k+1) ls)        by DROP_EL_CONS
    Let lt = TAKE k ls.
    Then LENGTH lt = k                         by LENGTH_TAKE
     and a = EL j lt                           by EL_TAKE
     and lt
       = TAKE j lt ++ DROP j lt                by TAKE_DROP
       = TAKE j lt ++ a::(DROP (j+1) lt)       by DROP_EL_CONS
    Pick l1 = TAKE j lt, l2 = DROP (j+1) lt, l3 = DROP (k+1) ls.
*)
Theorem EL_SPLIT_2:
  !ls j k. j < k /\ k < LENGTH ls ==>
           ?l1 l2 l3. ls = l1 ++ (EL j ls)::l2 ++ (EL k ls)::l3
Proof
  rpt strip_tac >>
  qabbrev_tac `a = EL j ls` >>
  qabbrev_tac `b = EL k ls` >>
  `j < LENGTH ls` by decide_tac >>
  `MEM a ls /\ MEM b ls` by metis_tac[MEM_EL] >>
  `ls = TAKE k ls ++ b::(DROP (k+1) ls)` by metis_tac[TAKE_DROP, DROP_EL_CONS] >>
  qabbrev_tac `lt = TAKE k ls` >>
  `LENGTH lt = k` by simp[Abbr`lt`] >>
  `a = EL j lt` by simp[EL_TAKE, Abbr`a`, Abbr`lt`] >>
  `lt = TAKE j lt ++ a::(DROP (j+1) lt)` by metis_tac[TAKE_DROP, DROP_EL_CONS] >>
  metis_tac[]
QED

(* Theorem: (LENGTH (h1::t1) = LENGTH (h2::t2)) /\
            (!k. k < LENGTH (h1::t1) ==> P (EL k (h1::t1)) (EL k (h2::t2))) ==>
           (P h1 h2) /\ (!k. k < LENGTH t1 ==> P (EL k t1) (EL k t2)) *)
(* Proof:
   Put k = 0,
   Then LENGTH (h1::t1) = SUC (LENGTH t1)     by LENGTH
                        > 0                   by SUC_POS
    and P (EL 0 (h1::t1)) (EL 0 (h2::t2))     by implication, 0 < LENGTH (h1::t1)
     or P HD (h1::t1) HD (h2::t2)             by EL
     or P h1 h2                               by HD
   Note k < LENGTH t1
    ==> k + 1 < SUC (LENGTH t1)                           by ADD1
              = LENGTH (h1::t1)                           by LENGTH
   Thus P (EL (k + 1) (h1::t1)) (EL (k + 1) (h2::t2))     by implication
     or P (EL (PRE (k + 1) t1)) (EL (PRE (k + 1)) t2)     by EL_CONS
     or P (EL k t1) (EL k t2)                             by PRE, ADD1
*)
val EL_ALL_PROPERTY = store_thm(
  "EL_ALL_PROPERTY",
  ``!h1 t1 h2 t2 P. (LENGTH (h1::t1) = LENGTH (h2::t2)) /\
     (!k. k < LENGTH (h1::t1) ==> P (EL k (h1::t1)) (EL k (h2::t2))) ==>
     (P h1 h2) /\ (!k. k < LENGTH t1 ==> P (EL k t1) (EL k t2))``,
  rpt strip_tac >| [
    `0 < LENGTH (h1::t1)` by metis_tac[LENGTH, SUC_POS] >>
    metis_tac[EL, HD],
    `k + 1 < SUC (LENGTH t1)` by decide_tac >>
    `k + 1 < LENGTH (h1::t1)` by metis_tac[LENGTH] >>
    `0 < k + 1 /\ (PRE (k + 1) = k)` by decide_tac >>
    metis_tac[EL_CONS]
  ]);

(* Theorem: (l1 ++ l2 = m1 ++ m2) /\ (LENGTH l1 = LENGTH m1) <=> (l1 = m1) /\ (l2 = m2) *)
(* Proof:
   By APPEND_EQ_APPEND,
   ?l. (l1 = m1 ++ l) /\ (m2 = l ++ l2) \/ ?l. (m1 = l1 ++ l) /\ (l2 = l ++ m2).
   Thus this is to show:
   (1) LENGTH (m1 ++ l) = LENGTH m1 ==> m1 ++ l = m1, true since l = [] by LENGTH_APPEND, LENGTH_NIL
   (2) LENGTH (m1 ++ l) = LENGTH m1 ==> l2 = l ++ l2, true since l = [] by LENGTH_APPEND, LENGTH_NIL
   (3) LENGTH l1 = LENGTH (l1 ++ l) ==> l1 = l1 ++ l, true since l = [] by LENGTH_APPEND, LENGTH_NIL
   (4) LENGTH l1 = LENGTH (l1 ++ l) ==> l ++ m2 = m2, true since l = [] by LENGTH_APPEND, LENGTH_NIL
*)
val APPEND_EQ_APPEND_EQ = store_thm(
  "APPEND_EQ_APPEND_EQ",
  ``!l1 l2 m1 m2. (l1 ++ l2 = m1 ++ m2) /\ (LENGTH l1 = LENGTH m1) <=> (l1 = m1) /\ (l2 = m2)``,
  rw[APPEND_EQ_APPEND] >>
  rw[EQ_IMP_THM] >-
  fs[] >-
  fs[] >-
 (fs[] >>
  `LENGTH l = 0` by decide_tac >>
  fs[]) >>
  fs[] >>
  `LENGTH l = 0` by decide_tac >>
  fs[]);

(*
LUPDATE_SEM     |- (!e n l. LENGTH (LUPDATE e n l) = LENGTH l) /\
                    !e n l p. p < LENGTH l ==> EL p (LUPDATE e n l) = if p = n then e else EL p l
EL_LUPDATE      |- !ys x i k. EL i (LUPDATE x k ys) = if i = k /\ k < LENGTH ys then x else EL i ys
LENGTH_LUPDATE  |- !x n ys. LENGTH (LUPDATE x n ys) = LENGTH ys
*)

(* Extract useful theorem from LUPDATE semantics *)
val LUPDATE_LEN = save_thm("LUPDATE_LEN", LUPDATE_SEM |> CONJUNCT1);
(* val LUPDATE_LEN = |- !e n l. LENGTH (LUPDATE e n l) = LENGTH l: thm *)
val LUPDATE_EL = save_thm("LUPDATE_EL", LUPDATE_SEM |> CONJUNCT2);
(* val LUPDATE_EL = |- !e n l p. p < LENGTH l ==> EL p (LUPDATE e n l) = if p = n then e else EL p l: thm *)

(* Theorem: LUPDATE q n (LUPDATE p n ls) = LUPDATE q n ls *)
(* Proof:
   Let l1 = LUPDATE q n (LUPDATE p n ls), l2 = LUPDATE q n ls.
   By LIST_EQ, this is to show:
   (1) LENGTH l1 = LENGTH l2
         LENGTH l1
       = LENGTH (LUPDATE q n (LUPDATE p n ls))  by notation
       = LENGTH (LUPDATE p n ls)                by LUPDATE_LEN
       = ls                                     by LUPDATE_LEN
       = LENGTH (LUPDATE q n ls)                by LUPDATE_LEN
       = LENGTH l2                              by notation
   (2) !x. x < LENGTH l1 ==> EL x l1 = EL x l2
         EL x l1
       = EL x (LUPDATE q n (LUPDATE p n ls))    by notation
       = if x = n then q else EL x (LUPDATE p n ls)            by LUPDATE_EL
       = if x = n then q else (if x = n then p else EL x ls)   by LUPDATE_EL
       = if x = n then q else EL x ls           by simplification
       = EL x (LUPDATE q n ls)                  by LUPDATE_EL
       = EL x l2                                by notation
*)
val LUPDATE_SAME_SPOT = store_thm(
  "LUPDATE_SAME_SPOT",
  ``!ls n p q. LUPDATE q n (LUPDATE p n ls) = LUPDATE q n ls``,
  rpt strip_tac >>
  qabbrev_tac `l1 = LUPDATE q n (LUPDATE p n ls)` >>
  qabbrev_tac `l2 = LUPDATE q n ls` >>
  `LENGTH l1 = LENGTH l2` by rw[LUPDATE_LEN, Abbr`l1`, Abbr`l2`] >>
  `!x. x < LENGTH l1 ==> (EL x l1 = EL x l2)` by fs[LUPDATE_EL, Abbr`l1`, Abbr`l2`] >>
  rw[LIST_EQ]);

(* Theorem: m <> n ==>
     (LUPDATE q n (LUPDATE p m ls) = LUPDATE p m (LUPDATE q n ls)) *)
(* Proof:
   Let l1 = LUPDATE q n (LUPDATE p m ls),
       l2 = LUPDATE p m (LUPDATE q n ls).
       LENGTH l1
     = LENGTH (LUPDATE q n (LUPDATE p m ls))  by notation
     = LENGTH (LUPDATE p m ls)                by LUPDATE_LEN
     = LENGTH ls                              by LUPDATE_LEN
     = LENGTH (LUPDATE q n ls)                by LUPDATE_LEN
     = LENGTH (LUPDATE p m (LUPDATE q n ls))  by LUPDATE_LEN
     = LENGTH l2                              by notation
      !x. x < LENGTH l1 ==>
      EL x l1
    = EL x ((LUPDATE q n (LUPDATE p m ls))    by notation
    = EL x ls  if x <> n, x <> m, or p if x = m, q if x = n
                                              by LUPDATE_EL
      EL x l2
    = EL x ((LUPDATE p m (LUPDATE q n ls))    by notation
    = EL x ls  if x <> m, x <> n, or q if x = n, p if x = m
                                              by LUPDATE_EL
    = EL x l1
   Hence l1 = l2                              by LIST_EQ
*)
val LUPDATE_DIFF_SPOT = store_thm(
  "LUPDATE_DIFF_SPOT",
  `` !ls m n p q. m <> n ==>
     (LUPDATE q n (LUPDATE p m ls) = LUPDATE p m (LUPDATE q n ls))``,
  rpt strip_tac >>
  qabbrev_tac `l1 = LUPDATE q n (LUPDATE p m ls)` >>
  qabbrev_tac `l2 = LUPDATE p m (LUPDATE q n ls)` >>
  irule LIST_EQ >>
  rw[LUPDATE_EL, Abbr`l1`, Abbr`l2`]);

(* Theorem: EL (LENGTH ls) (ls ++ h::t) = h *)
(* Proof:
   Let l2 = h::t.
   Note ~NULL l2                      by NULL
     so EL (LENGTH ls) (ls ++ h::t)
      = EL (LENGTH ls) (ls ++ l2)     by notation
      = HD l2                         by EL_LENGTH_APPEND
      = HD (h::t) = h                 by notation
*)
val EL_LENGTH_APPEND_0 = store_thm(
  "EL_LENGTH_APPEND_0",
  ``!ls h t. EL (LENGTH ls) (ls ++ h::t) = h``,
  rw[EL_LENGTH_APPEND]);

(* Theorem: EL (LENGTH ls + 1) (ls ++ h::k::t) = k *)
(* Proof:
   Let l1 = ls ++ [h].
   Then LENGTH l1 = LENGTH ls + 1    by LENGTH
   Note ls ++ h::k::t = l1 ++ k::t   by APPEND
        EL (LENGTH ls + 1) (ls ++ h::k::t)
      = EL (LENGTH l1) (l1 ++ k::t)  by above
      = k                            by EL_LENGTH_APPEND_0
*)
val EL_LENGTH_APPEND_1 = store_thm(
  "EL_LENGTH_APPEND_1",
  ``!ls h k t. EL (LENGTH ls + 1) (ls ++ h::k::t) = k``,
  rpt strip_tac >>
  qabbrev_tac `l1 = ls ++ [h]` >>
  `LENGTH l1 = LENGTH ls + 1` by rw[Abbr`l1`] >>
  `ls ++ h::k::t = l1 ++ k::t` by rw[Abbr`l1`] >>
  metis_tac[EL_LENGTH_APPEND_0]);

(* Theorem: LUPDATE a (LENGTH ls) (ls ++ (h::t)) = ls ++ (a::t) *)
(* Proof:
     LUPDATE a (LENGTH ls) (ls ++ h::t)
   = ls ++ LUPDATE a (LENGTH ls - LENGTH ls) (h::t)   by LUPDATE_APPEND2
   = ls ++ LUPDATE a 0 (h::t)                         by arithmetic
   = ls ++ (a::t)                                     by LUPDATE_def
*)
val LUPDATE_APPEND_0 = store_thm(
  "LUPDATE_APPEND_0",
  ``!ls a h t. LUPDATE a (LENGTH ls) (ls ++ (h::t)) = ls ++ (a::t)``,
  rw_tac std_ss[LUPDATE_APPEND2, LUPDATE_def]);

(* Theorem: LUPDATE b (LENGTH ls + 1) (ls ++ h::k::t) = ls ++ h::b::t *)
(* Proof:
     LUPDATE b (LENGTH ls + 1) (ls ++ h::k::t)
   = ls ++ LUPDATE b (LENGTH ls + 1 - LENGTH ls) (h::k::t)   by LUPDATE_APPEND2
   = ls ++ LUPDATE b 1 (h::k::t)                      by arithmetic
   = ls ++ (h::b::t)                                  by LUPDATE_def
*)
val LUPDATE_APPEND_1 = store_thm(
  "LUPDATE_APPEND_1",
  ``!ls b h k t. LUPDATE b (LENGTH ls + 1) (ls ++ h::k::t) = ls ++ h::b::t``,
  rpt strip_tac >>
  `LUPDATE b 1 (h::k::t) = h::LUPDATE b 0 (k::t)` by rw[GSYM LUPDATE_def] >>
  `_ = h::b::t` by rw[LUPDATE_def] >>
  `LUPDATE b (LENGTH ls + 1) (ls ++ h::k::t) =
    ls ++ LUPDATE b (LENGTH ls + 1 - LENGTH ls) (h::k::t)` by metis_tac[LUPDATE_APPEND2, DECIDE``n <= n + 1``] >>
  fs[]);

(* Theorem: LUPDATE b (LENGTH ls + 1)
              (LUPDATE a (LENGTH ls) (ls ++ h::k::t)) = ls ++ a::b::t *)
(* Proof:
   Let l1 = LUPDATE a (LENGTH ls) (ls ++ h::k::t)
          = ls ++ a::k::t       by LUPDATE_APPEND_0
     LUPDATE b (LENGTH ls + 1) l1
   = LUPDATE b (LENGTH ls + 1) (ls ++ a::k::t)
   = ls ++ a::b::t              by LUPDATE_APPEND2_1
*)
val LUPDATE_APPEND_0_1 = store_thm(
  "LUPDATE_APPEND_0_1",
  ``!ls a b h k t.
    LUPDATE b (LENGTH ls + 1)
      (LUPDATE a (LENGTH ls) (ls ++ h::k::t)) = ls ++ a::b::t``,
  rw_tac std_ss[LUPDATE_APPEND_0, LUPDATE_APPEND_1]);

(* ------------------------------------------------------------------------- *)
(* DROP and TAKE                                                             *)
(* ------------------------------------------------------------------------- *)

(* Note: There is TAKE_LENGTH_ID, but no DROP_LENGTH_NIL, now have DROP_LENGTH_TOO_LONG *)

(* Theorem: DROP (LENGTH l) l = [] *)
(* Proof:
   By induction on l.
   Base case: DROP (LENGTH []) [] = []
      True by DROP_def: DROP n [] = [].
   Step case: DROP (LENGTH l) l = [] ==>
              !h. DROP (LENGTH (h::l)) (h::l) = []
    Since LENGTH (h::l) = SUC (LENGTH l)  by LENGTH
       so LENGTH (h::l) <> 0              by NOT_SUC
      and SUC (LENGTH l) - 1 = LENGTH l   by SUC_SUB1
      DROP (LENGTH (h::l) (h::l)
    = DROP (LENGTH l) l                   by DROP_def
    = []                                  by induction hypothesis
*)
val DROP_LENGTH_NIL = store_thm(
  "DROP_LENGTH_NIL",
  ``!l. DROP (LENGTH l) l = []``,
  Induct >> rw[]);

(* listTheory.HD_DROP  |- !n l. n < LENGTH l ==> HD (DROP n l) = EL n l *)

(* Theorem: n < LENGTH ls ==> TL (DROP n ls) = DROP n (TL ls) *)
(* Proof:
   Note 0 < LENGTH ls, so ls <> []             by LENGTH_NON_NIL
     so ?h t. ls = h::t                        by NOT_NIL_CONS
        TL (DROP n ls)
      = TL (EL n ls::DROP (SUC n) ls)          by DROP_CONS_EL
      = DROP (SUC n) ls                        by TL
      = DROP (SUC n) (h::t)                    by above
      = DROP n t                               by DROP
      = DROP n (TL ls)                         by TL
*)
Theorem TL_DROP:
  !ls n. n < LENGTH ls ==> TL (DROP n ls) = DROP n (TL ls)
Proof
  rpt strip_tac >>
  `0 < LENGTH ls` by decide_tac >>
  `TL (DROP n ls) = TL (EL n ls::DROP (SUC n) ls)` by simp[DROP_CONS_EL] >>
  `_ = DROP (SUC n) ls` by simp[] >>
  `_ = DROP (SUC n) (HD ls::TL ls)` by metis_tac[LIST_HEAD_TAIL] >>
  simp[]
QED

(* Theorem: x <> [] ==> (TAKE 1 (x ++ y) = TAKE 1 x) *)
(* Proof:
   x <> [] means ?h t. x = h::t    by list_CASES
     TAKE 1 (x ++ y)
   = TAKE 1 ((h::t) ++ y)
   = TAKE 1 (h:: t ++ y)      by APPEND
   = h::TAKE 0 (t ++ y)       by TAKE_def
   = h::TAKE 0 t              by TAKE_0
   = TAKE 1 (h::t)            by TAKE_def
*)
val TAKE_1_APPEND = store_thm(
  "TAKE_1_APPEND",
  ``!x y. x <> [] ==> (TAKE 1 (x ++ y) = TAKE 1 x)``,
  Cases_on `x`>> rw[]);

(* Theorem: x <> [] ==> (DROP 1 (x ++ y) = (DROP 1 x) ++ y) *)
(* Proof:
   x <> [] means ?h t. x = h::t    by list_CASES
     DROP 1 (x ++ y)
   = DROP 1 ((h::t) ++ y)
   = DROP 1 (h:: t ++ y)      by APPEND
   = DROP 0 (t ++ y)          by DROP_def
   = t ++ y                   by DROP_0
   = (DROP 1 (h::t)) ++ y     by DROP_def
*)
val DROP_1_APPEND = store_thm(
  "DROP_1_APPEND",
  ``!x y. x <> [] ==> (DROP 1 (x ++ y) = (DROP 1 x) ++ y)``,
  Cases_on `x` >> rw[]);

(* Theorem: DROP (SUC n) x = DROP 1 (DROP n x) *)
(* Proof:
   By induction on x.
   Base case: !n. DROP (SUC n) [] = DROP 1 (DROP n [])
     LHS = DROP (SUC n) []  = []  by DROP_def
     RHS = DROP 1 (DROP n [])
         = DROP 1 []              by DROP_def
         = [] = LHS               by DROP_def
   Step case: !n. DROP (SUC n) x = DROP 1 (DROP n x) ==>
              !h n. DROP (SUC n) (h::x) = DROP 1 (DROP n (h::x))
     If n = 0,
     LHS = DROP (SUC 0) (h::x)
         = DROP 1 (h::x)          by ONE
     RHS = DROP 1 (DROP 0 (h::x))
         = DROP 1 (h::x) = LHS    by DROP_0
     If n <> 0,
     LHS = DROP (SUC n) (h::x)
         = DROP n x               by DROP_def
     RHS = DROP 1 (DROP n (h::x)
         = DROP 1 (DROP (n-1) x)  by DROP_def
         = DROP (SUC (n-1)) x     by induction hypothesis
         = DROP n x = LHS         by SUC (n-1) = n, n <> 0.
*)
val DROP_SUC = store_thm(
  "DROP_SUC",
  ``!n x. DROP (SUC n) x = DROP 1 (DROP n x)``,
  Induct_on `x` >>
  rw[DROP_def] >>
  `n = SUC (n-1)` by decide_tac >>
  metis_tac[]);

(* Theorem: TAKE (SUC n) x = (TAKE n x) ++ (TAKE 1 (DROP n x)) *)
(* Proof:
   By induction on x.
   Base case: !n. TAKE (SUC n) [] = TAKE n [] ++ TAKE 1 (DROP n [])
     LHS = TAKE (SUC n) [] = []    by TAKE_def
     RHS = TAKE n [] ++ TAKE 1 (DROP n [])
         = [] ++ TAKE 1 []         by TAKE_def, DROP_def
         = TAKE 1 []               by APPEND
         = [] = LHS                by TAKE_def
   Step case: !n. TAKE (SUC n) x = TAKE n x ++ TAKE 1 (DROP n x) ==>
              !h n. TAKE (SUC n) (h::x) = TAKE n (h::x) ++ TAKE 1 (DROP n (h::x))
     If n = 0,
     LHS = TAKE (SUC 0) (h::x)
         = TAKE 1 (h::x)           by ONE
     RHS = TAKE 0 (h::x) ++ TAKE 1 (DROP 0 (h::x))
         = [] ++ TAKE 1 (h::x)     by TAKE_def, DROP_def
         = TAKE 1 (h::x) = LHS     by APPEND
     If n <> 0,
     LHS = TAKE (SUC n) (h::x)
         = h :: TAKE n x           by TAKE_def
     RHS = TAKE n (h::x) ++ TAKE 1 (DROP n (h::x))
         = (h:: TAKE (n-1) x) ++ TAKE 1 (DROP (n-1) x)   by TAKE_def, DROP_def, n <> 0.
         = h :: (TAKE (n-1) x ++ TAKE 1 (DROP (n-1) x))  by APPEND
         = h :: TAKE (SUC (n-1)) x  by induction hypothesis
         = h :: TAKE n x            by SUC (n-1) = n, n <> 0.
*)
val TAKE_SUC = store_thm(
  "TAKE_SUC",
  ``!n x. TAKE (SUC n) x = (TAKE n x) ++ (TAKE 1 (DROP n x))``,
  Induct_on `x` >>
  rw[TAKE_def, DROP_def] >>
  `n = SUC (n-1)` by decide_tac >>
  metis_tac[]);

(* Theorem: k < LENGTH x ==> (TAKE (SUC k) x = SNOC (EL k x) (TAKE k x)) *)
(* Proof:
   By induction on k.
   Base case: !x. 0 < LENGTH x ==> (TAKE (SUC 0) x = SNOC (EL 0 x) (TAKE 0 x))
         0 < LENGTH x
     ==> ?h t. x = h::t   by LENGTH_NIL, list_CASES
     LHS = TAKE (SUC 0) x
         = TAKE 1 (h::t)   by ONE
         = h::TAKE 0 t     by TAKE_def
         = h::[]           by TAKE_0
         = [h]
         = SNOC h []       by SNOC
         = SNOC h (TAKE 0 (h::t))             by TAKE_0
         = SNOC (EL 0 (h::t)) (TAKE 0 (h::t)) by EL
         = RHS
   Step case: !x. k < LENGTH x ==> (TAKE (SUC k) x = SNOC (EL k x) (TAKE k x)) ==>
     !x. SUC k < LENGTH x ==> (TAKE (SUC (SUC k)) x = SNOC (EL (SUC k) x) (TAKE (SUC k) x))
     Since 0 < SUC k                        by prim_recTheory.LESS_0
           0 < LENGTH x                     by LESS_TRANS
       ==> ?h t. x = h::t                   by LENGTH_NIL, list_CASES
       and LENGTH (h::t) = SUC (LENGTH t)   by LENGTH
     hence k < LENGTH t                     by LESS_MONO_EQ
     LHS = TAKE (SUC (SUC k)) (h::t)
         = h :: TAKE (SUC k) t              by TAKE_def
         = h :: SNOC (EL k t) (TAKE k t)    by induction hypothesis, k < LENGTH t.
         = SNOC (EL k t) (h :: TAKE k t)    by SNOC
         = SNOC (EL (SUC k) (h::t)) (h :: TAKE k t)         by EL_restricted
         = SNOC (EL (SUC k) (h::t)) (TAKE (SUC k) (h::t))   by TAKE_def
         = RHS
*)
val TAKE_SUC_BY_TAKE = store_thm(
  "TAKE_SUC_BY_TAKE",
  ``!k x. k < LENGTH x ==> (TAKE (SUC k) x = SNOC (EL k x) (TAKE k x))``,
  Induct_on `k` >| [
    rpt strip_tac >>
    `LENGTH x <> 0` by decide_tac >>
    `?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    rw[],
    rpt strip_tac >>
    `LENGTH x <> 0` by decide_tac >>
    `?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    `k < LENGTH t` by metis_tac[LENGTH, LESS_MONO_EQ] >>
    rw_tac std_ss[TAKE_def, SNOC, EL_restricted]
  ]);

(* Theorem: k < LENGTH x ==> (DROP k x = (EL k x) :: (DROP (SUC k) x)) *)
(* Proof:
   By induction on k.
   Base case: !x. 0 < LENGTH x ==> (DROP 0 x = EL 0 x::DROP (SUC 0) x)
         0 < LENGTH x
     ==> ?h t. x = h::t   by LENGTH_NIL, list_CASES
     LHS = DROP 0 (h::t)
         = h::t                            by DROP_0
         = (EL 0 (h::t))::t                by EL
         = (EL 0 (h::t))::(DROP 1 (h::t))  by DROP_def
         = EL 0 x::DROP (SUC 0) x          by ONE
         = RHS
   Step case: !x. k < LENGTH x ==> (DROP k x = EL k x::DROP (SUC k) x) ==>
              !x. SUC k < LENGTH x ==> (DROP (SUC k) x = EL (SUC k) x::DROP (SUC (SUC k)) x)
     Since 0 < SUC k                        by prim_recTheory.LESS_0
           0 < LENGTH x                     by LESS_TRANS
       ==> ?h t. x = h::t                   by LENGTH_NIL, list_CASES
       and LENGTH (h::t) = SUC (LENGTH t)   by LENGTH
     hence k < LENGTH t                     by LESS_MONO_EQ
     LHS = DROP (SUC k) (h::t)
         = DROP k t                         by DROP_def
         = EL k x::DROP (SUC k) x           by induction hypothesis
         = EL k t :: DROP (SUC (SUC k)) (h::t)           by DROP_def
         = EL (SUC k) (h::t)::DROP (SUC (SUC k)) (h::t)  by EL
         = RHS
*)
val DROP_BY_DROP_SUC = store_thm(
  "DROP_BY_DROP_SUC",
  ``!k x. k < LENGTH x ==> (DROP k x = (EL k x) :: (DROP (SUC k) x))``,
  Induct_on `k` >| [
    rpt strip_tac >>
    `LENGTH x <> 0` by decide_tac >>
    `?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    rw[],
    rpt strip_tac >>
    `LENGTH x <> 0` by decide_tac >>
    `?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    `k < LENGTH t` by metis_tac[LENGTH, LESS_MONO_EQ] >>
    rw[]
  ]);

(* Theorem: n < LENGTH ls ==> ?u. DROP n ls = [EL n ls] ++ u *)
(* Proof:
   By induction on n.
   Base: !ls. 0 < LENGTH ls ==> ?u. DROP 0 ls = [EL 0 ls] ++ u
       Note LENGTH ls <> 0        by 0 < LENGTH ls
        ==> ls <> []              by LENGTH_NIL
        ==> ?h t. ls = h::t       by list_CASES
         DROP 0 ls
       = ls                       by DROP_0
       = [h] ++ t                 by ls = h::t, CONS_APPEND
       = [EL 0 ls] ++ t           by EL
       Take u = t.
   Step: !ls. n < LENGTH ls ==> ?u. DROP n ls = [EL n ls] ++ u ==>
         !ls. SUC n < LENGTH ls ==> ?u. DROP (SUC n) ls = [EL (SUC n) ls] ++ u
       Note LENGTH ls <> 0                  by SUC n < LENGTH ls
        ==> ?h t. ls = h::t                 by list_CASES, LENGTH_NIL
        Now LENGTH ls = SUC (LENGTH t)      by LENGTH
        ==> n < LENGTH t                    by SUC n < SUC (LENGTH t)
       Thus ?u. DROP n t = [EL n t] ++ u    by induction hypothesis

         DROP (SUC n) ls
       = DROP (SUC n) (h::t)                by ls = h::t
       = DROP n t                           by DROP_def
       = [EL n t] ++ u                      by above
       = [EL (SUC n) (h::t)] ++ u           by EL_restricted
       Take this u.
*)
val DROP_HEAD_ELEMENT = store_thm(
  "DROP_HEAD_ELEMENT",
  ``!ls n. n < LENGTH ls ==> ?u. DROP n ls = [EL n ls] ++ u``,
  Induct_on `n` >| [
    rpt strip_tac >>
    `LENGTH ls <> 0` by decide_tac >>
    `?h t. ls = h::t` by metis_tac[list_CASES, LENGTH_NIL] >>
    rw[],
    rw[] >>
    `LENGTH ls <> 0` by decide_tac >>
    `?h t. ls = h::t` by metis_tac[list_CASES, LENGTH_NIL] >>
    `LENGTH ls = SUC (LENGTH t)` by rw[] >>
    `n < LENGTH t` by decide_tac >>
    `?u. DROP n t = [EL n t] ++ u` by rw[] >>
    rw[]
  ]);

(* Theorem: DROP n (TAKE n ls) = [] *)
(* Proof:
   If n <= LENGTH ls,
      Then LENGTH (TAKE n ls) = n           by LENGTH_TAKE_EQ
      Thus DROP n (TAKE n ls) = []          by DROP_LENGTH_TOO_LONG
   If LENGTH ls < n
      Then LENGTH (TAKE n ls) = LENGTH ls   by LENGTH_TAKE_EQ
      Thus DROP n (TAKE n ls) = []          by DROP_LENGTH_TOO_LONG
*)
val DROP_TAKE_EQ_NIL = store_thm(
  "DROP_TAKE_EQ_NIL",
  ``!ls n. DROP n (TAKE n ls) = []``,
  rw[LENGTH_TAKE_EQ, DROP_LENGTH_TOO_LONG]);

(* Theorem: TAKE m (DROP n ls) = DROP n (TAKE (n + m) ls) *)
(* Proof:
   If n <= LENGTH ls,
      Then LENGTH (TAKE n ls) = n                       by LENGTH_TAKE_EQ, n <= LENGTH ls
        DROP n (TAKE (n + m) ls)
      = DROP n (TAKE n ls ++ TAKE m (DROP n ls))        by TAKE_SUM
      = DROP n (TAKE n ls) ++ DROP (n - LENGTH (TAKE n ls)) (TAKE m (DROP n ls))  by DROP_APPEND
      = [] ++ DROP (n - LENGTH (TAKE n ls)) (TAKE m (DROP n ls))     by DROP_TAKE_EQ_NIL
      = DROP (n - LENGTH (TAKE n ls)) (TAKE m (DROP n ls))           by APPEND
      = DROP 0 (TAKE m (DROP n ls))                                  by above
      = TAKE m (DROP n ls)                                           by DROP_0
   If LENGTH ls < n,
      Then DROP n ls = []         by DROP_LENGTH_TOO_LONG
       and TAKE (n + m) ls = ls   by TAKE_LENGTH_TOO_LONG
        DROP n (TAKE (n + m) ls)
      = DROP n ls                 by TAKE_LENGTH_TOO_LONG
      = []                        by DROP_LENGTH_TOO_LONG
      = TAKE m []                 by TAKE_nil
      = TAKE m (DROP n ls)        by DROP_LENGTH_TOO_LONG
*)
val TAKE_DROP_SWAP = store_thm(
  "TAKE_DROP_SWAP",
  ``!ls m n. TAKE m (DROP n ls) = DROP n (TAKE (n + m) ls)``,
  rpt strip_tac >>
  Cases_on `n <= LENGTH ls` >| [
    qabbrev_tac `x = TAKE m (DROP n ls)` >>
    `DROP n (TAKE (n + m) ls) = DROP n (TAKE n ls ++ x)` by rw[TAKE_SUM, Abbr`x`] >>
    `_ = DROP n (TAKE n ls) ++ DROP (n - LENGTH (TAKE n ls)) x` by rw[DROP_APPEND] >>
    `_ = DROP (n - LENGTH (TAKE n ls)) x` by rw[DROP_TAKE_EQ_NIL] >>
    `_ = DROP 0 x` by rw[LENGTH_TAKE_EQ] >>
    rw[],
    `DROP n ls = []` by rw[DROP_LENGTH_TOO_LONG] >>
    `TAKE (n + m) ls = ls` by rw[TAKE_LENGTH_TOO_LONG] >>
    rw[]
  ]);

(* Theorem: TAKE (LENGTH l1) (LUPDATE x (LENGTH l1 + k) (l1 ++ l2)) = l1 *)
(* Proof:
      TAKE (LENGTH l1) (LUPDATE x (LENGTH l1 + k) (l1 ++ l2))
    = TAKE (LENGTH l1) (l1 ++ LUPDATE x k l2)      by LUPDATE_APPEND2
    = l1                                           by TAKE_LENGTH_APPEND
*)
val TAKE_LENGTH_APPEND2 = store_thm(
  "TAKE_LENGTH_APPEND2",
  ``!l1 l2 x k. TAKE (LENGTH l1) (LUPDATE x (LENGTH l1 + k) (l1 ++ l2)) = l1``,
  rw_tac std_ss[LUPDATE_APPEND2, TAKE_LENGTH_APPEND]);

(* Theorem: LENGTH (TAKE n l) <= LENGTH l *)
(* Proof: by LENGTH_TAKE_EQ *)
val LENGTH_TAKE_LE = store_thm(
  "LENGTH_TAKE_LE",
  ``!n l. LENGTH (TAKE n l) <= LENGTH l``,
  rw[LENGTH_TAKE_EQ]);

(* Theorem: ALL_DISTINCT ls ==> ALL_DISTINCT (TAKE n ls) *)
(* Proof:
   By induction on ls.
   Base: !n. ALL_DISTINCT [] ==> ALL_DISTINCT (TAKE n [])
             ALL_DISTINCT (TAKE n [])
         <=> ALL_DISTINCT []       by TAKE_nil
         <=> T                     by ALL_DISTINCT
   Step: !n. ALL_DISTINCT ls ==> ALL_DISTINCT (TAKE n ls) ==>
         !h n. ALL_DISTINCT (h::ls) ==> ALL_DISTINCT (TAKE n (h::ls))
         If n = 0,
             ALL_DISTINCT (TAKE 0 (h::ls))
         <=> ALL_DISTINCT []       by TAKE_0
         <=> T                     by ALL_DISTINCT
         If n <> 0,
             ALL_DISTINCT (TAKE n (h::ls))
         <=> ALL_DISTINCT (h::TAKE (n - 1) ls) by TAKE_def
         <=> ~MEM h (TAKE (n - 1) ls) /\ ALL_DISTINCT (TAKE (n - 1) ls)
                                               by ALL_DISTINCT
         <=> ~MEM h (TAKE (n - 1) ls) /\ T     by induction hypothesis
         <=> T                                 by MEM_TAKE, ALL_DISTINCT
*)
Theorem ALL_DISTINCT_TAKE:
  !ls n. ALL_DISTINCT ls ==> ALL_DISTINCT (TAKE n ls)
Proof
  Induct >-
  simp[] >>
  rw[] >>
  (Cases_on `n = 0` >> simp[]) >>
  metis_tac[MEM_TAKE]
QED

(* Theorem: ALL_DISTINCT ls ==>
            !k e. MEM e (TAKE k ls) /\ MEM e (DROP k ls) ==> F *)
(* Proof:
   By induction on ls.
   Base: ALL_DISTINCT [] ==> !k e. MEM e (TAKE k []) /\ MEM e (DROP k []) ==> F
         MEM e (TAKE k []) = MEM e [] = F      by TAKE_nil, MEM
         MEM e (DROP k []) = MEM e [] = F      by DROP_nil, MEM
   Step: ALL_DISTINCT ls ==>
             !k e. MEM e (TAKE k ls) /\ MEM e (DROP k ls) ==> F ==>
         !h. ALL_DISTINCT (h::ls) ==>
             !k e. MEM e (TAKE k (h::ls)) /\ MEM e (DROP k (h::ls)) ==> F
         Note ~MEM h ls /\ ALL_DISTINCT ls     by ALL_DISTINCT
         If k = 0,
                MEM e (TAKE 0 (h::ls))
            <=> MEM e [] = F                   by TAKE_0, MEM
            hence true.
         If k <> 0,
                MEM e (TAKE k (h::ls))
            <=> MEM e (h::TAKE (k - 1) ls)       by TAKE_def, k <> 0
            <=> e = h \/ MEM e (TAKE (k - 1) ls) by MEM
              MEM e (DROP k (h::ls))
            <=> MEM e (DROP (k - 1) ls)          by DROP_def, k <> 0
            ==> MEM e ls                         by MEM_DROP_IMP
            If e = h,
               this contradicts ~MEM h ls.
            If MEM e (TAKE (k - 1) ls)
               this contradicts the induction hypothesis.
*)
Theorem ALL_DISTINCT_TAKE_DROP:
  !ls. ALL_DISTINCT ls ==>
   !k e. MEM e (TAKE k ls) /\ MEM e (DROP k ls) ==> F
Proof
  Induct >-
  simp[] >>
  rw[] >>
  Cases_on `k = 0` >-
  fs[] >>
  spose_not_then strip_assume_tac >>
  rfs[] >-
  metis_tac[MEM_DROP_IMP] >>
  metis_tac[]
QED

(* Theorem: ALL_DISTINCT (x::y::ls) <=> ALL_DISTINCT (y::x::ls) *)
(* Proof:
   If x = y, this is trivial.
   If x <> y,
       ALL_DISTINCT (x::y::ls)
   <=> (x <> y /\ ~MEM x ls) /\ ~MEM y ls /\ ALL_DISTINCT ls   by ALL_DISTINCT
   <=> (y <> x /\ ~MEM y ls) /\ ~MEM x ls /\ ALL_DISTINCT ls
   <=> ALL_DISTINCT (y::x::ls)                                 by ALL_DISTINCT
*)
Theorem ALL_DISTINCT_SWAP:
  !ls x y. ALL_DISTINCT (x::y::ls) <=> ALL_DISTINCT (y::x::ls)
Proof
  rw[] >>
  metis_tac[]
QED

(* Theorem: ALL_DISTINCT ls /\ ls <> [] /\ j < LENGTH ls ==> (EL j ls = LAST ls <=> j + 1 = LENGTH ls) *)
(* Proof:
   Note 0 < LENGTH ls                          by LENGTH_EQ_0
       EL j ls = LAST ls
   <=> EL j ls = EL (PRE (LENGTH ls)) ls       by LAST_EL
   <=> j = PRE (LENGTH ls)                     by ALL_DISTINCT_EL_IMP, j < LENGTH ls
   <=> j + 1 = LENGTH ls                       by SUC_PRE, ADD1, 0 < LENGTH ls
*)
Theorem ALL_DISTINCT_LAST_EL_IFF:
  !ls j. ALL_DISTINCT ls /\ ls <> [] /\ j < LENGTH ls ==> (EL j ls = LAST ls <=> j + 1 = LENGTH ls)
Proof
  rw[LAST_EL] >>
  `0 < LENGTH ls` by metis_tac[LENGTH_EQ_0, NOT_ZERO] >>
  `PRE (LENGTH ls) + 1 = LENGTH ls` by decide_tac >>
  `EL j ls = EL (PRE (LENGTH ls)) ls <=> j = PRE (LENGTH ls)` by fs[ALL_DISTINCT_EL_IMP] >>
  simp[]
QED

(* Theorem: ls <> [] /\ ALL_DISTINCT ls ==> ALL_DISTINCT (FRONT ls) *)
(* Proof:
   Let k = LENGTH ls.
       ALL_DISTINCT ls
   ==> ALL_DISTINCT (TAKE (k - 1) ls)          by ALL_DISTINCT_TAKE
   ==> ALL_DISTINCT (FRONT ls)                 by FRONT_BY_TAKE, ls <> []
*)
Theorem ALL_DISTINCT_FRONT:
  !ls. ls <> [] /\ ALL_DISTINCT ls ==> ALL_DISTINCT (FRONT ls)
Proof
  simp[ALL_DISTINCT_TAKE, FRONT_BY_TAKE]
QED

(* Theorem: ALL_DISTINCT ls /\ j < LENGTH ls /\ ls = l1 ++ [EL j ls] ++ l2 ==> j = LENGTH l1 *)
(* Proof:
   Note EL j ls = EL (LENGTH l1) ls            by el_append3
    and LENGTH l1 < LENGTH ls                  by LENGTH_APPEND
     so j = LENGTH l1                          by ALL_DISTINCT_EL_IMP
*)
Theorem ALL_DISTINCT_EL_APPEND:
  !ls l1 l2 j. ALL_DISTINCT ls /\ j < LENGTH ls /\ ls = l1 ++ [EL j ls] ++ l2 ==> j = LENGTH l1
Proof
  rpt strip_tac >>
  `EL j ls = EL (LENGTH l1) ls` by metis_tac[el_append3] >>
  `LENGTH ls = LENGTH l1 + 1 + LENGTH l2` by metis_tac[LENGTH_APPEND, LENGTH_SING] >>
  `LENGTH l1 < LENGTH ls` by decide_tac >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED

(* Theorem: ALL_DISTINCT (l1 ++ [x] ++ l2) <=> ALL_DISTINCT (x::(l1 ++ l2)) *)
(* Proof:
   By induction on l1.
   Base: ALL_DISTINCT ([] ++ [x] ++ l2) <=> ALL_DISTINCT (x::([] ++ l2))
             ALL_DISTINCT ([] ++ [x] ++ l2)
         <=> ALL_DISTINCT (x::l2)                  by APPEND_NIL
         <=> ALL_DISTINCT (x::([] ++ l2))          by APPEND_NIL
   Step: ALL_DISTINCT (l1 ++ [x] ++ l2) <=> ALL_DISTINCT (x::(l1 ++ l2)) ==>
         !h. ALL_DISTINCT (h::l1 ++ [x] ++ l2) <=> ALL_DISTINCT (x::(h::l1 ++ l2))

             ALL_DISTINCT (h::l1 ++ [x] ++ l2)
         <=> ALL_DISTINCT (h::(l1 ++ [x] ++ l2))   by APPEND
         <=> ~MEM h (l1 ++ [x] ++ l2) /\
             ALL_DISTINCT (l1 ++ [x] ++ l2)        by ALL_DISTINCT
         <=> ~MEM h (l1 ++ [x] ++ l2) /\
             ALL_DISTINCT (x::(l1 ++ l2))          by induction hypothesis
         <=> ~MEM h (x::(l1 ++ l2)) /\
             ALL_DISTINCT (x::(l1 ++ l2))          by MEM_APPEND_3
         <=> ALL_DISTINCT (h::x::(l1 ++ l2))       by ALL_DISTINCT
         <=> ALL_DISTINCT (x::h::(l1 ++ l2))       by ALL_DISTINCT_SWAP
         <=> ALL_DISTINCT (x::(h::l1 ++ l2))       by APPEND
*)
Theorem ALL_DISTINCT_APPEND_3:
  !l1 x l2. ALL_DISTINCT (l1 ++ [x] ++ l2) <=> ALL_DISTINCT (x::(l1 ++ l2))
Proof
  rpt strip_tac >>
  Induct_on `l1` >-
  simp[] >>
  rpt strip_tac >>
  `ALL_DISTINCT (h::l1 ++ [x] ++ l2) <=> ALL_DISTINCT (h::(l1 ++ [x] ++ l2))` by rw[] >>
  `_ = (~MEM h (l1 ++ [x] ++ l2) /\ ALL_DISTINCT (l1 ++ [x] ++ l2))` by rw[] >>
  `_ = (~MEM h (l1 ++ [x] ++ l2) /\ ALL_DISTINCT (x::(l1 ++ l2)))` by rw[] >>
  `_ = (~MEM h (x::(l1 ++ l2)) /\ ALL_DISTINCT (x::(l1 ++ l2)))` by rw[MEM_APPEND_3] >>
  `_ = ALL_DISTINCT (h::x::(l1 ++ l2))` by rw[] >>
  `_ = ALL_DISTINCT (x::h::(l1 ++ l2))` by rw[ALL_DISTINCT_SWAP] >>
  `_ = ALL_DISTINCT (x::(h::l1 ++ l2))` by metis_tac[APPEND] >>
  simp[]
QED

(* Theorem: ALL_DISTINCT l ==> !x. MEM x l <=> ?p1 p2. (l = p1 ++ [x] ++ p2) /\ ~MEM x p1 /\ ~MEM x p2 *)
(* Proof:
   If part: MEM x l ==> ?p1 p2. (l = p1 ++ [x] ++ p2) /\ ~MEM x p1 /\ ~MEM x p2
      Note ?p1 p2. (l = p1 ++ [x] ++ p2) /\ ~MEM x p2    by MEM_SPLIT_APPEND_last
       Now ALL_DISTINCT (p1 ++ [x])              by ALL_DISTINCT_APPEND, ALL_DISTINCT l
       But MEM x [x]                             by MEM
        so ~MEM x p1                             by ALL_DISTINCT_APPEND

   Only-if part: MEM x (p1 ++ [x] ++ p2), true   by MEM_APPEND
*)
Theorem MEM_SPLIT_APPEND_distinct:
  !l. ALL_DISTINCT l ==> !x. MEM x l <=> ?p1 p2. (l = p1 ++ [x] ++ p2) /\ ~MEM x p1 /\ ~MEM x p2
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[MEM_SPLIT_APPEND_last, ALL_DISTINCT_APPEND, MEM] >>
  rw[]
QED

(* Theorem: MEM x ls <=>
            ?k. k < LENGTH ls /\ x = EL k ls /\
                ls = TAKE k ls ++ x::DROP (k+1) ls /\ ~MEM x (TAKE k ls) *)
(* Proof:
   If part: MEM x ls ==> ?k. k < LENGTH ls /\ x = EL k ls /\
                         ls = TAKE k ls ++ x::DROP (k+1) ls /\ ~MEM x (TAKE k ls)
      Note ?pfx sfx. ls = pfx ++ [x] ++ sfx /\ ~MEM x pfx
                                   by MEM_SPLIT_APPEND_first
      Take k = LENGTH pfx.
      Then k < LENGTH ls           by LENGTH_APPEND
       and EL k ls
         = EL k (pfx ++ [x] ++ sfx)
         = x                       by el_append3
       and TAKE k ls ++ x::DROP (k+1) ls
         = TAKE k (pfx ++ [x] ++ sfx) ++
           [x] ++
           DROP (k+1) ((pfx ++ [x] ++ sfx))
         = pfx ++ [x] ++           by TAKE_APPEND1
           (DROP (k+1)(pfx + [x])
           ++ sfx                  by DROP_APPEND1
         = pfx ++ [x] ++ sfx       by DROP_LENGTH_NIL
         = ls
       and TAKE k ls = pfx         by TAKE_APPEND1
   Only-if part: k < LENGTH ls /\ ls = TAKE k ls ++ [EL k ls] ++ DROP (k + 1) ls /\
                 ~MEM (EL k ls) (TAKE k ls) ==> MEM (EL k ls) ls
       This is true                by EL_MEM, just need k < LENGTH ls
*)
Theorem MEM_SPLIT_TAKE_DROP_first:
  !ls x. MEM x ls <=>
      ?k. k < LENGTH ls /\ x = EL k ls /\
          ls = TAKE k ls ++ x::DROP (k+1) ls /\ ~MEM x (TAKE k ls)
Proof
  rw[EQ_IMP_THM] >| [
    imp_res_tac MEM_SPLIT_APPEND_first >>
    qexists_tac `LENGTH pfx` >>
    rpt strip_tac >-
    fs[] >-
    fs[el_append3] >-
    fs[TAKE_APPEND1, DROP_APPEND1] >>
    `TAKE (LENGTH pfx) ls = pfx` by rw[TAKE_APPEND1] >>
    fs[],
    fs[EL_MEM]
  ]
QED

(* Theorem: MEM x ls <=>
            ?k. k < LENGTH ls /\ x = EL k ls /\
                ls = TAKE k ls ++ x::DROP (k+1) ls /\ ~MEM x (DROP (k+1) ls) *)
(* Proof:
   If part: MEM x ls ==> ?k. k < LENGTH ls /\ x = EL k ls /\
                         ls = TAKE k ls ++ x::DROP (k+1) ls /\ ~MEM x (DROP (k+1) ls)
      Note ?pfx sfx. ls = pfx ++ [x] ++ sfx /\ ~MEM x sfx
                                   by MEM_SPLIT_APPEND_last
      Take k = LENGTH pfx.
      Then k < LENGTH ls           by LENGTH_APPEND
       and EL k ls
         = EL k (pfx ++ [x] ++ sfx)
         = x                       by el_append3
       and TAKE k ls ++ x::DROP (k+1) ls
         = TAKE k (pfx ++ [x] ++ sfx) ++
           [x] ++
           DROP (k+1) ((pfx ++ [x] ++ sfx))
         = pfx ++ [x] ++           by TAKE_APPEND1
           (DROP (k+1)(pfx + [x])
           ++ sfx                  by DROP_APPEND1
         = pfx ++ [x] ++ sfx       by DROP_LENGTH_NIL
         = ls
       and DROP (k + 1) ls) = sfx  by DROP_APPEND1, DROP_LENGTH_NIL
   Only-if part: k < LENGTH ls /\ ls = TAKE k ls ++ [EL k ls] ++ DROP (k + 1) ls /\
                 ~MEM (EL k ls) (DROP (k+1) ls)) ==> MEM (EL k ls) ls
       This is true                by EL_MEM, just need k < LENGTH ls
*)
Theorem MEM_SPLIT_TAKE_DROP_last:
  !ls x. MEM x ls <=>
      ?k. k < LENGTH ls /\ x = EL k ls /\
          ls = TAKE k ls ++ x::DROP (k+1) ls /\ ~MEM x (DROP (k+1) ls)
Proof
  rw[EQ_IMP_THM] >| [
    imp_res_tac MEM_SPLIT_APPEND_last >>
    qexists_tac `LENGTH pfx` >>
    rpt strip_tac >-
    fs[] >-
    fs[el_append3] >-
    fs[TAKE_APPEND1, DROP_APPEND1] >>
    `DROP (LENGTH pfx + 1) ls = sfx` by rw[DROP_APPEND1] >>
    fs[],
    fs[EL_MEM]
  ]
QED

(* Theorem: ALL_DISTINCT ls ==>
           !x. MEM x ls <=>
           ?k. k < LENGTH ls /\ x = EL k ls /\
               ls = TAKE k ls ++ x::DROP (k+1) ls /\
               ~MEM x (TAKE k ls) /\ ~MEM x (DROP (k+1) ls) *)
(* Proof:
   If part: MEM x ls ==> ?k. k < LENGTH ls /\ x = EL k ls /\
                         ls = TAKE k ls ++ x::DROP (k+1) ls /\
                          ~MEM x (TAKE k ls) /\ ~MEM x (DROP (k+1) ls)
      Note ?p1 p2. ls = p1 ++ [x] ++ p2 /\ ~MEM x p1 /\ ~MEM x p2
                                   by MEM_SPLIT_APPEND_distinct
      Take k = LENGTH p1.
      Then k < LENGTH ls           by LENGTH_APPEND
       and EL k ls
         = EL k (p1 ++ [x] ++ p2)
         = x                       by el_append3
       and TAKE k ls ++ x::DROP (k+1) ls
         = TAKE k (p1 ++ [x] ++ p2) ++
           [x] ++
           DROP (k+1) ((p1 ++ [x] ++ p2))
         = p1 ++ [x] ++            by TAKE_APPEND1
           (DROP (k+1)(p1 + [x])
           ++ p2                   by DROP_APPEND1
         = p1 ++ [x] ++ p2         by DROP_LENGTH_NIL
         = ls
       and TAKE k ls = p1          by TAKE_APPEND1
       and DROP (k + 1) ls) = p2   by DROP_APPEND1, DROP_LENGTH_NIL
   Only-if part: k < LENGTH ls /\ ls = TAKE k ls ++ [EL k ls] ++ DROP (k + 1) ls /\
                  ~MEM (EL k ls) (TAKE k ls) /\ ~MEM (EL k ls) (DROP (k+1) ls)) ==> MEM (EL k ls) ls
       This is true                by EL_MEM, just need k < LENGTH ls
*)
Theorem MEM_SPLIT_TAKE_DROP_distinct:
  !ls. ALL_DISTINCT ls ==>
    !x. MEM x ls <=>
    ?k. k < LENGTH ls /\ x = EL k ls /\
        ls = TAKE k ls ++ x::DROP (k+1) ls /\
         ~MEM x (TAKE k ls) /\ ~MEM x (DROP (k+1) ls)
Proof
  rw[EQ_IMP_THM] >| [
    `?p1 p2. ls = p1 ++ [x] ++ p2 /\ ~MEM x p1 /\ ~MEM x p2` by rw[GSYM MEM_SPLIT_APPEND_distinct] >>
    qexists_tac `LENGTH p1` >>
    rpt strip_tac >-
    fs[] >-
    fs[el_append3] >-
    fs[TAKE_APPEND1, DROP_APPEND1] >-
    rfs[TAKE_APPEND1] >>
    `DROP (LENGTH p1 + 1) ls = p2` by rw[DROP_APPEND1] >>
    fs[],
    fs[EL_MEM]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* List Filter.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Idea: the j-th element of FILTER must have j elements filtered beforehand. *)

(* Theorem: let fs = FILTER P ls in ls = l1 ++ x::l2 /\ P x ==>
            x = EL (LENGTH (FILTER P l1)) fs *)
(* Proof:
   Let l3 = x::l2, then ls = l1 ++ l3.
   Let j = LENGTH (FILTER P l1).
     EL j fs
   = EL j (FILTER P ls)                        by given
   = EL j (FILTER P l1 ++ FILTER P l3)         by FILTER_APPEND_DISTRIB
   = EL 0 (FILTER P l3)                        by EL_APPEND, j = LENGTH (FILTER P l1)
   = EL 0 (FILTER P (x::l2))                   by notation
   = EL 0 (x::FILTER P l2)                     by FILTER, P x
   = x                                         by HD
*)
Theorem FILTER_EL_IMP:
  !P ls l1 l2 x. let fs = FILTER P ls in ls = l1 ++ x::l2 /\ P x ==>
                 x = EL (LENGTH (FILTER P l1)) fs
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `l3 = x::l2` >>
  qabbrev_tac `j = LENGTH (FILTER P l1)` >>
  `EL j fs = EL j (FILTER P l1 ++ FILTER P l3)` by simp[FILTER_APPEND_DISTRIB, Abbr`fs`] >>
  `_ = EL 0 (FILTER P (x::l2))` by simp[EL_APPEND, Abbr`j`, Abbr`l3`] >>
  fs[]
QED

(* Theorem: let fs = FILTER P ls in ALL_DISTINCT ls /\ ls = l1 ++ x::l2 /\ j < LENGTH fs ==>
            (x = EL j fs <=> P x /\ j = LENGTH (FILTER P l1)) *)
(* Proof:
   Let k = LENGTH (FILTER P l1).
   If part: j < LENGTH fs /\ x = EL j fs ==> P x /\ j = k
      Note j < LENGTH fs /\ x = EL j fs        by given
       ==> MEM x fs                            by MEM_EL
       ==> P x                                 by MEM_FILTER
      Thus x = EL k fs                         by FILTER_EL_IMP
      Let l3 = x::l2, then ls = l1 ++ l3.
      Then FILTER P l3 = x :: FILTER P l2      by FILTER
        or FILTER P l3 <> []                   by NOT_NIL_CONS
        or LENGTH (FILTER P l3) <> 0           by LENGTH_EQ_0, [1]

           LENGTH fs
         = LENGTH (FILTER P ls)                by notation
         = LENGTH (FILTER P l1 ++ FILTER P l3) by FILTER_APPEND_DISTRIB
         = k + LENGTH (FILTER P l3)            by LENGTH_APPEND
      Thus k < LENGTH fs                       by [1]

      Note ALL_DISTINCT ls
       ==> ALL_DISTINCT fs                     by FILTER_ALL_DISTINCT
      With x = EL j fs = EL k fs               by above
       and j < LENGTH fs /\ k < LENGTH fs      by above
       ==>           j = k                     by ALL_DISTINCT_EL_IMP

   Only-if part: j < LENGTH fs /\ P x /\ j = k ==> x = EL j fs
      This is true                             by FILTER_EL_IMP
*)
Theorem FILTER_EL_IFF:
  !P ls l1 l2 x j. let fs = FILTER P ls in ALL_DISTINCT ls /\ ls = l1 ++ x::l2 /\ j < LENGTH fs ==>
                   (x = EL j fs <=> P x /\ j = LENGTH (FILTER P l1))
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `k = LENGTH (FILTER P l1)` >>
  simp[EQ_IMP_THM] >>
  ntac 2 strip_tac >| [
    `MEM x fs` by metis_tac[MEM_EL] >>
    `P x` by fs[MEM_FILTER, Abbr`fs`] >>
    qabbrev_tac `ls = l1 ++ x::l2` >>
    `EL j fs = EL k fs` by metis_tac[FILTER_EL_IMP] >>
    qabbrev_tac `l3 = x::l2` >>
    `FILTER P l3 = x :: FILTER P l2` by simp[Abbr`l3`] >>
    `LENGTH (FILTER P l3) <> 0` by fs[] >>
    `fs = FILTER P l1 ++ FILTER P l3` by fs[FILTER_APPEND_DISTRIB, Abbr`fs`, Abbr`ls`] >>
    `LENGTH fs = k + LENGTH (FILTER P l3)` by fs[Abbr`k`] >>
    `k < LENGTH fs` by decide_tac >>
    `ALL_DISTINCT fs` by simp[FILTER_ALL_DISTINCT, Abbr`fs`] >>
    metis_tac[ALL_DISTINCT_EL_IMP],
    metis_tac[FILTER_EL_IMP]
  ]
QED

(* Derive theorems for head = (EL 0 fs) *)

(* Theorem: ls = l1 ++ x::l2 /\ P x /\ FILTER P l1 = [] ==> x = HD (FILTER P ls) *)
(* Proof:
   Note FILTER P l1 = []           by given
    ==> LENGTH (FILTER P l1) = 0   by LENGTH
   Thus x = EL 0 (FILTER P ls)     by FILTER_EL_IMP
          = HD (FILTER P ls)       by EL
*)
Theorem FILTER_HD:
  !P ls l1 l2 x. ls = l1 ++ x::l2 /\ P x /\ FILTER P l1 = [] ==> x = HD (FILTER P ls)
Proof
  metis_tac[LENGTH, FILTER_EL_IMP, EL]
QED

(* Theorem: ALL_DISTINCT ls /\ ls = l1 ++ x::l2 /\ P x ==>
            (x = HD (FILTER P ls) <=> FILTER P l1 = []) *)
(* Proof:
   Let fs = FILTER P ls.
   Note MEM x ls                   by MEM_APPEND, MEM
    and P x ==> fs <> []           by MEM_FILTER, NIL_NO_MEM
     so 0 < LENGTH fs              by LENGTH_EQ_0
   Thus x = HD fs
          = EL 0 fs                by EL
    <=> LENGTH (FILTER P l1) = 0   by FILTER_EL_IFF
    <=> FILTER P l1 = []           by LENGTH_EQ_0
*)
Theorem FILTER_HD_IFF:
  !P ls l1 l2 x. ALL_DISTINCT ls /\ ls = l1 ++ x::l2 /\ P x ==>
                 (x = HD (FILTER P ls) <=> FILTER P l1 = [])
Proof
  rpt strip_tac >>
  qabbrev_tac `fs = FILTER P ls` >>
  `MEM x ls` by metis_tac[MEM_APPEND, MEM] >>
  `MEM x fs` by fs[MEM_FILTER, Abbr`fs`] >>
  `0 < LENGTH fs` by metis_tac[NIL_NO_MEM, LENGTH_EQ_0, NOT_ZERO] >>
  metis_tac[FILTER_EL_IFF, EL, LENGTH_EQ_0]
QED

(* Derive theorems for last = (EL (LENGTH fs - 1) fs) *)

(* Theorem: ls = l1 ++ x::l2 /\ P x /\ FILTER P l2 = [] ==>
            x = LAST (FILTER P ls) *)
(* Proof:
   Let fs = FILTER P ls,
        k = LENGTH fs.
   Note MEM x ls                   by MEM_APPEND, MEM
    and P x ==> fs <> []           by MEM_FILTER, NIL_NO_MEM
     so 0 < LENGTH fs = k          by LENGTH_EQ_0

   Note FILTER P l2 = []           by given
    ==> LENGTH (FILTER P l2) = 0   by LENGTH
    k = LENGTH fs
      = LENGTH (FILTER P ls)       by notation
      = LENGTH (FILTER P l1) + 1   by FILTER_APPEND_DISTRIB, ONE
     or LENGTH (FILTER P l1) = PRE k
   Thus x = EL (PRE k) fs          by FILTER_EL_IMP
          = LAST fs                by LAST_EL, fs <> []
*)
Theorem FILTER_LAST:
  !P ls l1 l2 x. ls = l1 ++ x::l2 /\ P x /\ FILTER P l2 = [] ==>
                 x = LAST (FILTER P ls)
Proof
  rpt strip_tac >>
  qabbrev_tac `fs = FILTER P ls` >>
  qabbrev_tac `k = LENGTH fs` >>
  `MEM x ls` by metis_tac[MEM_APPEND, MEM] >>
  `MEM x fs` by fs[MEM_FILTER, Abbr`fs`] >>
  `fs <> [] /\ 0 < k` by metis_tac[NIL_NO_MEM, LENGTH_EQ_0, NOT_ZERO] >>
  `k = LENGTH (FILTER P l1) + 1` by fs[FILTER_APPEND_DISTRIB, Abbr`k`, Abbr`fs`] >>
  `LENGTH (FILTER P l1) = PRE k` by decide_tac >>
  metis_tac[FILTER_EL_IMP, LAST_EL]
QED

(* Theorem: ALL_DISTINCT ls /\ ls = l1 ++ x::l2 /\ P x ==>
            (x = LAST (FILTER P ls) <=> FILTER P l2 = []) *)
(* Proof:
   Let fs = FILTER P ls,
        k = LENGTH fs,
        j = LENGTH (FILTER P l1).
   Note MEM x ls                   by MEM_APPEND, MEM
    and P x ==> fs <> []           by MEM_FILTER, NIL_NO_MEM
     so 0 < LENGTH fs = k          by LENGTH_EQ_0
    and PRE k < k                  by arithmetic

    k = LENGTH fs
      = LENGTH (FILTER P ls)                   by notation
      = j + 1 + LENGTH (FILTER P l2)           by FILTER_APPEND_DISTRIB, ONE
     so j = PRE k <=> LENGTH (FILTER P l2) = 0 by arithmetic

   Thus x = LAST fs
          = EL (PRE k) fs          by LAST_EL
    <=> PRE k = j                  by FILTER_EL_IFF
    <=> LENGTH (FILTER P l2) = 0   by above
    <=> FILTER P l2 = []           by LENGTH_EQ_0
*)
Theorem FILTER_LAST_IFF:
  !P ls l1 l2 x. ALL_DISTINCT ls /\ ls = l1 ++ x::l2 /\ P x ==>
                 (x = LAST (FILTER P ls) <=> FILTER P l2 = [])
Proof
  rpt strip_tac >>
  qabbrev_tac `fs = FILTER P ls` >>
  qabbrev_tac `k = LENGTH fs` >>
  qabbrev_tac `j = LENGTH (FILTER P l1)` >>
  `MEM x ls` by metis_tac[MEM_APPEND, MEM] >>
  `MEM x fs` by fs[MEM_FILTER, Abbr`fs`] >>
  `fs <> [] /\ 0 < k` by metis_tac[NIL_NO_MEM, LENGTH_EQ_0, NOT_ZERO] >>
  `k = j + 1 + LENGTH (FILTER P l2)` by fs[FILTER_APPEND_DISTRIB, Abbr`fs`, Abbr`k`, Abbr`j`] >>
  `PRE k < k /\ (j = PRE k <=> LENGTH (FILTER P l2) = 0)` by decide_tac >>
  metis_tac[FILTER_EL_IFF, LAST_EL, LENGTH_EQ_0]
QED

(* Idea: for FILTER over a range, the range between successive filter elements is filtered. *)

(* Theorem: let fs = FILTER P ls; j = LENGTH (FILTER P l1) in
            ls = l1 ++ x::l2 ++ y::l3 /\ P x /\ P y /\ FILTER P l2 = [] ==>
            x = EL j fs /\ y = EL (j + 1) fs *)
(* Proof:
   Let l4 = y::l3, then
       ls = l1 ++ x::l2 ++ l4
          = l1 ++ x::(l2 ++ l4)                by APPEND_ASSOC_CONS
   Thus x = EL j fs                            by FILTER_EL_IMP

   Now let l5 = l1 ++ x::l2,
           k = LENGTH (FILTER P l5).
   Then ls = l5 ++ y::l3                       by APPEND_ASSOC
    and y = EL k fs                            by FILTER_EL_IMP

   Note FILTER P l5
      = FILTER P l1 ++ FILTER P (x::l2)        by FILTER_APPEND_DISTRIB
      = FILTER P l1 ++ x :: FILTER P l2        by FILTER
      = FILTER P l1 ++ [x]                     by FILTER P l2 = []
    and k = LENGTH (FILTER P l5)
          = LENGTH (FILTER P l1 ++ [x])        by above
          = j + 1                              by LENGTH_APPEND
*)
Theorem FILTER_EL_NEXT:
  !P ls l1 l2 l3 x y. let fs = FILTER P ls; j = LENGTH (FILTER P l1) in
                      ls = l1 ++ x::l2 ++ y::l3 /\ P x /\ P y /\ FILTER P l2 = [] ==>
                      x = EL j fs /\ y = EL (j + 1) fs
Proof
  rw_tac std_ss[] >| [
    qabbrev_tac `l4 = y::l3` >>
    qabbrev_tac `ls = l1 ++ x::l2 ++ l4` >>
    `ls = l1 ++ x::(l2 ++ l4)` by simp[Abbr`ls`] >>
    metis_tac[FILTER_EL_IMP],
    qabbrev_tac `l5 = l1 ++ x::l2` >>
    qabbrev_tac `ls = l5 ++ y::l3` >>
    `FILTER P l5 = FILTER P l1 ++ [x]` by fs[FILTER_APPEND_DISTRIB, Abbr`l5`] >>
    `LENGTH (FILTER P l5) = j + 1` by fs[Abbr`j`] >>
    metis_tac[FILTER_EL_IMP]
  ]
QED

(* Theorem: let fs = FILTER P ls; j = LENGTH (FILTER P l1) in
             ALL_DISTINCT ls /\ ls = l1 ++ x::l2 ++ y::l3 /\ P x /\ P y ==>
             (x = EL j fs /\ y = EL (j + 1) fs <=> FILTER P l2 = []) *)
(* Proof:
   Note fs = FILTER P ls
           = FILTER P (l1 ++ x::l2 ++ y::l3)   by given
           = FILTER P l1 ++
             x :: FILTER P l2 ++
             y :: FILTER P l3                  by FILTER_APPEND_DISTRIB, FILTER
   Thus LENGTH fs
      = j + SUC (LENGTH (FILTER P l2))
          + SUC (LENGTH (FILTER P l3))         by LENGTH_APPEND
     or j + 2 <= LENGTH fs                     by arithmetic
     or j < LENGTH fs, j + 1 < LENGTH fs       by inequality

   Let l4 = y::l3, then
       ls = l1 ++ x::l2 ++ l4
          = l1 ++ x::(l2 ++ l4)                by APPEND_ASSOC_CONS
   Thus x = EL j fs                            by FILTER_EL_IFF, j < LENGTH fs

   Now let l5 = l1 ++ x::l2,
           k = LENGTH (FILTER P l5).
   Then ls = l5 ++ y::l3                       by APPEND_ASSOC
    and fs = FILTER P l5 ++
             y :: FILTER P l3                  by FILTER_APPEND_DISTRIB, FILTER
     so LENGTH fs = k + SUC (LENGTH P l3)      by LENGTH_APPEND
   Thus k < LENGTH fs
    and y = EL k fs                            by FILTER_EL_IFF

   Also FILTER P l5 = FILTER P l1 ++
                      x :: FILTER P l2         by FILTER_APPEND_DISTRIB, FILTER
     so k = j + SUC (LENGTH (FILTER P l2))     by LENGTH_APPEND
   Thus k = j + 1
    <=> LENGTH (FILTER P l2) = 0               by arithmetic

   Note ALL_DISTINCT fs                        by FILTER_ALL_DISTINCT
     so EL k fs = EL (j + 1) fs
    <=> k = j + 1
    <=> LENGTH (FILTER P l2) = 0               by above
    <=> FILTER P l2 = []                       by LENGTH_EQ_0
*)
Theorem FILTER_EL_NEXT_IFF:
  !P ls l1 l2 l3 x y. let fs = FILTER P ls; j = LENGTH (FILTER P l1) in
                      ALL_DISTINCT ls /\ ls = l1 ++ x::l2 ++ y::l3 /\ P x /\ P y ==>
                      (x = EL j fs /\ y = EL (j + 1) fs <=> FILTER P l2 = [])
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `ls = l1 ++ x::l2 ++ y::l3` >>
  `j + 2 <= LENGTH fs` by
  (`fs = FILTER P l1 ++ x::FILTER P l2 ++ y::FILTER P l3` by simp[FILTER_APPEND_DISTRIB, Abbr`fs`, Abbr`ls`] >>
  `LENGTH fs = j + SUC (LENGTH (FILTER P l2)) + SUC (LENGTH (FILTER P l3))` by fs[Abbr`j`] >>
  decide_tac) >>
  `j < LENGTH fs` by decide_tac >>
  qabbrev_tac `l4 = y::l3` >>
  `ls = l1 ++ x::(l2 ++ l4)` by simp[Abbr`ls`] >>
  `x = EL j fs` by metis_tac[FILTER_EL_IFF] >>
  qabbrev_tac `l5 = l1 ++ x::l2` >>
  qabbrev_tac `k = LENGTH (FILTER P l5)` >>
  `ls = l5 ++ y::l3` by simp[Abbr`l5`, Abbr`ls`] >>
  `k < LENGTH fs /\ (k = j + 1 <=> FILTER P l2 = [])` by
    (`fs = FILTER P l5 ++ y::FILTER P l3` by rfs[FILTER_APPEND_DISTRIB, Abbr`fs`] >>
  `LENGTH fs = k + SUC (LENGTH (FILTER P l3))` by fs[Abbr`k`] >>
  `FILTER P l5 = FILTER P l1 ++ x :: FILTER P l2` by rfs[FILTER_APPEND_DISTRIB, Abbr`l5`] >>
  `k = j + SUC (LENGTH (FILTER P l2))` by fs[Abbr`k`, Abbr`j`] >>
  simp[]) >>
  `y = EL k fs` by metis_tac[FILTER_EL_IFF] >>
  `j + 1 < LENGTH fs` by decide_tac >>
  `ALL_DISTINCT fs` by simp[FILTER_ALL_DISTINCT, Abbr`fs`] >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED

(* Theorem: let fs = FILTER P ls in
            ALL_DISTINCT ls /\ ls = l1 ++ x::l2 ++ y::l3 /\ P x /\ P y ==>
            (findi y fs = 1 + findi x fs <=> FILTER P l2 = []) *)
(* Proof:
   Let j = LENGTH (FILTER P l1).

   Note fs = FILTER P l1 ++ x::FILTER P l2 ++
                            y::FILTER P l3     by FILTER_APPEND_DISTRIB
   Thus LENGTH fs = j +
                    SUC (LENGTH (FILTER P l2)) +
                    SUC (LENGTH (FILTER P l3)) by LENGTH_APPEND
     or j + 2 <= LENGTH fs                     by arithmetic
     or j < LENGTH fs /\ j + 1 < LENGTH fs     by j + 2 <= LENGTH fs

   Let l4 = y::l3,
   Then ls = l1 ++ x::l2 ++ l4
           = l1 ++ x::(l2 ++ l4)               by APPEND_ASSOC_CONS
    ==> x = EL j fs                            by FILTER_EL_IMP

   Note ALL_DISTINCT fs                        by FILTER_ALL_DISTINCT
    and MEM x ls /\ MEM y ls                   by MEM_APPEND
     so MEM x fs /\ MEM y fs                   by MEM_FILTER
    and x = EL j fs <=> findi x fs = j            by findi_EL_iff
    and y = EL (j + 1) fs <=> findi y fs = j + 1  by findi_EL_iff

        FILTER P l2 = []
     <=> x = EL j fs /\ y = EL (j + 1) fs      by FILTER_EL_NEXT_IFF
     <=> findi y fs = 1 + findi x fs           by above
*)
Theorem FILTER_EL_NEXT_IDX:
  !P ls l1 l2 l3 x y. let fs = FILTER P ls in
                      ALL_DISTINCT ls /\ ls = l1 ++ x::l2 ++ y::l3 /\ P x /\ P y ==>
                      (findi y fs = 1 + findi x fs <=> FILTER P l2 = [])
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `ls = l1 ++ x::l2 ++ y::l3` >>
  qabbrev_tac `j = LENGTH (FILTER P l1)` >>
  `j + 2 <= LENGTH fs` by
  (`fs = FILTER P l1 ++ x::FILTER P l2 ++ y::FILTER P l3` by simp[FILTER_APPEND_DISTRIB, Abbr`fs`, Abbr`ls`] >>
  `LENGTH fs = j + SUC (LENGTH (FILTER P l2)) + SUC (LENGTH (FILTER P l3))` by fs[Abbr`j`] >>
  decide_tac) >>
  `j < LENGTH fs /\ j + 1 < LENGTH fs` by decide_tac >>
  `x = EL j fs` by
    (qabbrev_tac `l4 = y::l3` >>
  `ls = l1 ++ x::(l2 ++ l4)` by simp[Abbr`ls`] >>
  metis_tac[FILTER_EL_IMP]) >>
  `MEM x ls /\ MEM y ls` by fs[Abbr`ls`] >>
  `MEM x fs /\ MEM y fs` by fs[MEM_FILTER, Abbr`fs`] >>
  `ALL_DISTINCT fs` by simp[FILTER_ALL_DISTINCT, Abbr`fs`] >>
  `x = EL j fs <=> findi x fs = j` by fs[findi_EL_iff] >>
  `y = EL (j + 1) fs <=> findi y fs = 1 + j` by fs[findi_EL_iff] >>
  metis_tac[FILTER_EL_NEXT_IFF]
QED

(* ------------------------------------------------------------------------- *)
(* List Rotation.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Define rotation of a list *)
val rotate_def = Define `
  rotate n l = DROP n l ++ TAKE n l
`;

(* Theorem: Rotate shifts element
            rotate n l = EL n l::(DROP (SUC n) l ++ TAKE n l) *)
(* Proof:
   h h t t t t t t  --> t t t t t h h
       k                k
   TAKE 2 x = h h
   DROP 2 x = t t t t t t
              k
   DROP 2 x ++ TAKE 2 x   has element k at front.

   Proof: by induction on l.
   Base case: !n. n < LENGTH [] ==> (DROP n [] = EL n []::DROP (SUC n) [])
     Since n < LENGTH [] = 0 is F, this is true.
   Step case: !h n. n < LENGTH (h::l) ==> (DROP n (h::l) = EL n (h::l)::DROP (SUC n) (h::l))
     i.e. n <> 0 /\ n < SUC (LENGTH l) ==> DROP (n - 1) l = EL n (h::l)::DROP n l  by DROP_def
     n <> 0 means ?j. n = SUC j < SUC (LENGTH l), so j < LENGTH l.
     LHS = DROP (SUC j - 1) l
         = DROP j l                    by SUC j - 1 = j
         = EL j l :: DROP (SUC j) l    by induction hypothesis
     RHS = EL (SUC j) (h::l) :: DROP (SUC (SUC j)) (h::l)
         = EL j l :: DROP (SUC j) l    by EL, DROP_def
         = LHS
*)
Theorem rotate_shift_element:
  !l n. n < LENGTH l ==> (rotate n l = EL n l::(DROP (SUC n) l ++ TAKE n l))
Proof
  rw[rotate_def] >>
  pop_assum mp_tac >>
  qid_spec_tac `n` >>
  Induct_on `l` >- rw[] >>
  rw[DROP_def] >> Cases_on `n` >> fs[]
QED

(* Theorem: rotate 0 l = l *)
(* Proof:
     rotate 0 l
   = DROP 0 l ++ TAKE 0 l   by rotate_def
   = l ++ []                by DROP_def, TAKE_def
   = l                      by APPEND
*)
val rotate_0 = store_thm(
  "rotate_0",
  ``!l. rotate 0 l = l``,
  rw[rotate_def]);

(* Theorem: rotate n [] = [] *)
(* Proof:
     rotate n []
   = DROP n [] ++ TAKE n []   by rotate_def
   = [] ++ []                 by DROP_def, TAKE_def
   = []                       by APPEND
*)
val rotate_nil = store_thm(
  "rotate_nil",
  ``!n. rotate n [] = []``,
  rw[rotate_def]);

(* Theorem: rotate (LENGTH l) l = l *)
(* Proof:
     rotate (LENGTH l) l
   = DROP (LENGTH l) l ++ TAKE (LENGTH l) l   by rotate_def
   = [] ++ TAKE (LENGTH l) l                  by DROP_LENGTH_NIL
   = [] ++ l                                  by TAKE_LENGTH_ID
   = l
*)
val rotate_full = store_thm(
  "rotate_full",
  ``!l. rotate (LENGTH l) l = l``,
  rw[rotate_def, DROP_LENGTH_NIL]);

(* Theorem: n < LENGTH l ==> rotate (SUC n) l = rotate 1 (rotate n l) *)
(* Proof:
   Since n < LENGTH l, l <> [] by LENGTH_NIL.
   Thus  DROP n l <> []  by DROP_EQ_NIL  (need n < LENGTH l)
   Expand by rotate_def, this is to show:
   DROP (SUC n) l ++ TAKE (SUC n) l = DROP 1 (DROP n l ++ TAKE n l) ++ TAKE 1 (DROP n l ++ TAKE n l)
   LHS = DROP (SUC n) l ++ TAKE (SUC n) l
       = DROP 1 (DROP n l) ++ (TAKE n l ++ TAKE 1 (DROP n l))             by DROP_SUC, TAKE_SUC
   Since DROP n l <> []  from above,
   RHS = DROP 1 (DROP n l ++ TAKE n l) ++ TAKE 1 (DROP n l ++ TAKE n l)
       = DROP 1 (DROP n l) ++ (TAKE n l ++ TAKE 1 (DROP n l))             by DROP_1_APPEND, TAKE_1_APPEND
       = LHS
*)
val rotate_suc = store_thm(
  "rotate_suc",
  ``!l n. n < LENGTH l ==> (rotate (SUC n) l = rotate 1 (rotate n l))``,
  rpt strip_tac >>
  `LENGTH l <> 0` by decide_tac >>
  `l <> []` by metis_tac[LENGTH_NIL] >>
  `DROP n l <> []` by simp[DROP_EQ_NIL] >>
  rw[rotate_def, DROP_1_APPEND, TAKE_1_APPEND, DROP_SUC, TAKE_SUC]);

(* Theorem: Rotate keeps LENGTH (of necklace): LENGTH (rotate n l) = LENGTH l *)
(* Proof:
     LENGTH (rotate n l)
   = LENGTH (DROP n l ++ TAKE n l)           by rotate_def
   = LENGTH (DROP n l) + LENGTH (TAKE n l)   by LENGTH_APPEND
   = LENGTH (TAKE n l) + LENGTH (DROP n l)   by arithmetic
   = LENGTH (TAKE n l ++ DROP n l)           by LENGTH_APPEND
   = LENGTH l                                by TAKE_DROP
*)
val rotate_same_length = store_thm(
  "rotate_same_length",
  ``!l n. LENGTH (rotate n l) = LENGTH l``,
  rpt strip_tac >>
  `LENGTH (rotate n l) = LENGTH (DROP n l ++ TAKE n l)` by rw[rotate_def] >>
  `_ = LENGTH (DROP n l) + LENGTH (TAKE n l)` by rw[] >>
  `_ = LENGTH (TAKE n l) + LENGTH (DROP n l)` by rw[ADD_COMM] >>
  `_ = LENGTH (TAKE n l ++ DROP n l)` by rw[] >>
  rw_tac std_ss[TAKE_DROP]);

(* Theorem: Rotate keeps SET (of elements): set (rotate n l) = set l *)
(* Proof:
     set (rotate n l)
   = set (DROP n l ++ TAKE n l)            by rotate_def
   = set (DROP n l) UNION set (TAKE n l)   by LIST_TO_SET_APPEND
   = set (TAKE n l) UNION set (DROP n l)   by UNION_COMM
   = set (TAKE n l ++ DROP n l)            by LIST_TO_SET_APPEND
   = set l                                 by TAKE_DROP
*)
val rotate_same_set = store_thm(
  "rotate_same_set",
  ``!l n. set (rotate n l) = set l``,
  rpt strip_tac >>
  `set (rotate n l) = set (DROP n l ++ TAKE n l)` by rw[rotate_def] >>
  `_ = set (DROP n l) UNION set (TAKE n l)` by rw[] >>
  `_ = set (TAKE n l) UNION set (DROP n l)` by rw[UNION_COMM] >>
  `_ = set (TAKE n l ++ DROP n l)` by rw[] >>
  rw_tac std_ss[TAKE_DROP]);

(* Theorem: n + m <= LENGTH l ==> rotate n (rotate m l) = rotate (n + m) l *)
(* Proof:
   By induction on n.
   Base case: !m l. 0 + m <= LENGTH l ==> (rotate 0 (rotate m l) = rotate (0 + m) l)
       rotate 0 (rotate m l)
     = rotate m l                by rotate_0
     = rotate (0 + m) l          by ADD
   Step case: !m l. SUC n + m <= LENGTH l ==> (rotate (SUC n) (rotate m l) = rotate (SUC n + m) l)
       rotate (SUC n) (rotate m l)
     = rotate 1 (rotate n (rotate m l))    by rotate_suc
     = rotate 1 (rotate (n + m) l)         by induction hypothesis
     = rotate (SUC (n + m)) l              by rotate_suc
     = rotate (SUC n + m) l                by ADD_CLAUSES
*)
val rotate_add = store_thm(
  "rotate_add",
  ``!n m l. n + m <= LENGTH l ==> (rotate n (rotate m l) = rotate (n + m) l)``,
  Induct >-
  rw[rotate_0] >>
  rw[] >>
  `LENGTH (rotate m l) = LENGTH l` by rw[rotate_same_length] >>
  `LENGTH (rotate (n + m) l) = LENGTH l` by rw[rotate_same_length] >>
  `n < LENGTH l /\ n + m < LENGTH l /\ n + m <= LENGTH l` by decide_tac >>
  rw[rotate_suc, ADD_CLAUSES]);

(* Theorem: !k. k < LENGTH l ==> rotate (LENGTH l - k) (rotate k l) = l *)
(* Proof:
   Since k < LENGTH l
     LENGTH 1 - k + k = LENGTH l <= LENGTH l   by EQ_LESS_EQ
     rotate (LENGTH l - k) (rotate k l)
   = rotate (LENGTH l - k + k) l        by rotate_add
   = rotate (LENGTH l) l                by arithmetic
   = l                                  by rotate_full
*)
val rotate_lcancel = store_thm(
  "rotate_lcancel",
  ``!k l. k < LENGTH l ==> (rotate (LENGTH l - k) (rotate k l) = l)``,
  rpt strip_tac >>
  `LENGTH l - k + k = LENGTH l` by decide_tac >>
  `LENGTH l <= LENGTH l` by rw[] >>
  rw[rotate_add, rotate_full]);

(* Theorem: !k. k < LENGTH l ==> rotate k (rotate (LENGTH l - k) l) = l *)
(* Proof:
   Since k < LENGTH l
     k + (LENGTH 1 - k) = LENGTH l <= LENGTH l   by EQ_LESS_EQ
     rotate k  (rotate (LENGTH l - k) l)
   = rotate (k + (LENGTH l - k)) l      by rotate_add
   = rotate (LENGTH l) l                by arithmetic
   = l                                  by rotate_full
*)
val rotate_rcancel = store_thm(
  "rotate_rcancel",
  ``!k l. k < LENGTH l ==> (rotate k (rotate (LENGTH l - k) l) = l)``,
  rpt strip_tac >>
  `k + (LENGTH l - k) = LENGTH l` by decide_tac >>
  `LENGTH l <= LENGTH l` by rw[] >>
  rw[rotate_add, rotate_full]);

(* ------------------------------------------------------------------------- *)
(* List Turn                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Define a rotation turn of a list (like a turnstile) *)
val turn_def = Define`
    turn l = if l = [] then [] else ((LAST l) :: (FRONT l))
`;

(* Theorem: turn [] = [] *)
(* Proof: by turn_def *)
val turn_nil = store_thm(
  "turn_nil",
  ``turn [] = []``,
  rw[turn_def]);

(* Theorem: l <> [] ==> (turn l = (LAST l) :: (FRONT l)) *)
(* Proof: by turn_def *)
val turn_not_nil = store_thm(
  "turn_not_nil",
  ``!l. l <> [] ==> (turn l = (LAST l) :: (FRONT l))``,
  rw[turn_def]);

(* Theorem: LENGTH (turn l) = LENGTH l *)
(* Proof:
   If l = [],
        LENGTH (turn []) = LENGTH []     by turn_def
   If l <> [],
      Then LENGTH l <> 0                 by LENGTH_NIL
        LENGTH (turn l)
      = LENGTH ((LAST l) :: (FRONT l))   by turn_def
      = SUC (LENGTH (FRONT l))           by LENGTH
      = SUC (PRE (LENGTH l))             by LENGTH_FRONT
      = LENGTH l                         by SUC_PRE, 0 < LENGTH l
*)
val turn_length = store_thm(
  "turn_length",
  ``!l. LENGTH (turn l) = LENGTH l``,
  metis_tac[turn_def, list_CASES, LENGTH, LENGTH_FRONT_CONS, SUC_PRE, NOT_ZERO_LT_ZERO]);

(* Theorem: (turn p = []) <=> (p = []) *)
(* Proof:
       turn p = []
   <=> LENGTH (turn p) = 0     by LENGTH_NIL
   <=> LENGTH p = 0            by turn_length
   <=> p = []                  by LENGTH_NIL
*)
val turn_eq_nil = store_thm(
  "turn_eq_nil",
  ``!p. (turn p = []) <=> (p = [])``,
  metis_tac[turn_length, LENGTH_NIL]);

(* Theorem: ls <> [] ==> (HD (turn ls) = LAST ls) *)
(* Proof:
     HD (turn ls)
   = HD (LAST ls :: FRONT ls)    by turn_def, ls <> []
   = LAST ls                     by HD
*)
val head_turn = store_thm(
  "head_turn",
  ``!ls. ls <> [] ==> (HD (turn ls) = LAST ls)``,
  rw[turn_def]);

(* Theorem: ls <> [] ==> (TL (turn ls) = FRONT ls) *)
(* Proof:
     TL (turn ls)
   = TL (LAST ls :: FRONT ls)  by turn_def, ls <> []
   = FRONT ls                  by TL
*)
Theorem tail_turn:
  !ls. ls <> [] ==> (TL (turn ls) = FRONT ls)
Proof
  rw[turn_def]
QED

(* Theorem: turn (SNOC x ls) = x :: ls *)
(* Proof:
   Note (SNOC x ls) <> []                    by NOT_SNOC_NIL
     turn (SNOC x ls)
   = LAST (SNOC x ls) :: FRONT (SNOC x ls)   by turn_def
   = x :: FRONT (SNOC x ls)                  by LAST_SNOC
   = x :: ls                                 by FRONT_SNOC
*)
Theorem turn_snoc:
  !ls x. turn (SNOC x ls) = x :: ls
Proof
  metis_tac[NOT_SNOC_NIL, turn_def, LAST_SNOC, FRONT_SNOC]
QED

(* Overload repeated turns *)
val _ = overload_on("turn_exp", ``\l n. FUNPOW turn n l``);

(* Theorem: turn_exp l 0 = l *)
(* Proof:
     turn_exp l 0
   = FUNPOW turn 0 l    by notation
   = l                  by FUNPOW
*)
val turn_exp_0 = store_thm(
  "turn_exp_0",
  ``!l. turn_exp l 0 = l``,
  rw[]);

(* Theorem: turn_exp l 1 = turn l *)
(* Proof:
     turn_exp l 1
   = FUNPOW turn 1 l    by notation
   = turn l             by FUNPOW
*)
val turn_exp_1 = store_thm(
  "turn_exp_1",
  ``!l. turn_exp l 1 = turn l``,
  rw[]);

(* Theorem: turn_exp l 2 = turn (turn l) *)
(* Proof:
     turn_exp l 2
   = FUNPOW turn 2 l         by notation
   = turn (FUNPOW turn 1 l)  by FUNPOW_SUC
   = turn (turn_exp l 1)     by notation
   = turn (turn l)           by turn_exp_1
*)
val turn_exp_2 = store_thm(
  "turn_exp_2",
  ``!l. turn_exp l 2 = turn (turn l)``,
  metis_tac[FUNPOW_SUC, turn_exp_1, TWO]);

(* Theorem: turn_exp l (SUC n) = turn_exp (turn l) n *)
(* Proof:
     turn_exp l (SUC n)
   = FUNPOW turn (SUC n) l    by notation
   = FUNPOW turn n (turn l)   by FUNPOW
   = turn_exp (turn l) n      by notation
*)
val turn_exp_SUC = store_thm(
  "turn_exp_SUC",
  ``!l n. turn_exp l (SUC n) = turn_exp (turn l) n``,
  rw[FUNPOW]);

(* Theorem: turn_exp l (SUC n) = turn (turn_exp l n) *)
(* Proof:
     turn_exp l (SUC n)
   = FUNPOW turn (SUC n) l    by notation
   = turn (FUNPOW turn n l)   by FUNPOW_SUC
   = turn (turn_exp l n)      by notation
*)
val turn_exp_suc = store_thm(
  "turn_exp_suc",
  ``!l n. turn_exp l (SUC n) = turn (turn_exp l n)``,
  rw[FUNPOW_SUC]);

(* Theorem: LENGTH (turn_exp l n) = LENGTH l *)
(* Proof:
   By induction on n.
   Base: LENGTH (turn_exp l 0) = LENGTH l
      True by turn_exp l 0 = l         by turn_exp_0
   Step: LENGTH (turn_exp l n) = LENGTH l ==> LENGTH (turn_exp l (SUC n)) = LENGTH l
        LENGTH (turn_exp l (SUC n))
      = LENGTH (turn (turn_exp l n))   by turn_exp_suc
      = LENGTH (turn_exp l n)          by turn_length
      = LENGTH l                       by induction hypothesis
*)
val turn_exp_length = store_thm(
  "turn_exp_length",
  ``!l n. LENGTH (turn_exp l n) = LENGTH l``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[turn_exp_suc, turn_length]);

(* Theorem: n < LENGTH ls ==>
            (HD (turn_exp ls n) = EL (if n = 0 then 0 else LENGTH ls - n) ls) *)
(* Proof:
   By induction on n.
   Base: !ls. 0 < LENGTH ls ==>
              HD (turn_exp ls 0) = EL 0 ls
           HD (turn_exp ls 0)
         = HD ls                 by FUNPOW_0
         = EL 0 ls               by EL
   Step: !ls. n < LENGTH ls ==> HD (turn_exp ls n) = EL (if n = 0 then 0 else (LENGTH ls - n)) ls ==>
         !ls. SUC n < LENGTH ls ==> HD (turn_exp ls (SUC n)) = EL (LENGTH ls - SUC n) ls
         Let k = LENGTH ls, then SUC n < k
         Note LENGTH (FRONT ls) = PRE k     by FRONT_LENGTH
          and n < PRE k                     by SUC n < k
         Also LENGTH (turn ls) = k          by turn_length
           so n < k                         by n < SUC n, SUC n < k
         Note ls <> []                      by k <> 0

           HD (turn_exp ls (SUC n))
         = HD (turn_exp (turn ls) n)                    by turn_exp_SUC
         = EL (if n = 0 then 0 else (LENGTH (turn ls) - n)) (turn ls)
                                                        by induction hypothesis, apply to (turn ls)
         = EL (if n = 0 then 0 else (k - n) (turn ls))  by above

         If n = 0,
         = EL 0 (turn ls)
         = LAST ls                           by turn_def
         = EL (PRE k) ls                     by LAST_EL
         = EL (k - SUC 0) ls                 by ONE
         If n <> 0
         = EL (k - n) (turn ls)
         = EL (k - n) (LAST ls :: FRONT ls)  by turn_def
         = EL (k - n - 1) (FRONT ls)         by EL
         = EL (k - n - 1) ls                 by FRONT_EL, k - n - 1 < PRE k, n <> 0
         = EL (k - SUC n) ls                 by arithmetic
*)
val head_turn_exp = store_thm(
  "head_turn_exp",
  ``!ls n. n < LENGTH ls ==>
         (HD (turn_exp ls n) = EL (if n = 0 then 0 else LENGTH ls - n) ls)``,
  (Induct_on `n` >> simp[]) >>
  rpt strip_tac >>
  qabbrev_tac `k = LENGTH ls` >>
  `n < k` by rw[Abbr`k`] >>
  `LENGTH (turn ls) = k` by rw[turn_length, Abbr`k`] >>
  `HD (turn_exp ls (SUC n)) = HD (turn_exp (turn ls) n)` by rw[turn_exp_SUC] >>
  `_ = EL (if n = 0 then 0 else (k - n)) (turn ls)` by rw[] >>
  `k <> 0` by decide_tac >>
  `ls <> []` by metis_tac[LENGTH_NIL] >>
  (Cases_on `n = 0` >> fs[]) >| [
    `PRE k = k - 1` by decide_tac >>
    rw[head_turn, LAST_EL],
    `k - n = SUC (k - SUC n)` by decide_tac >>
    rw[turn_def, Abbr`k`] >>
    `LENGTH (FRONT ls) = PRE (LENGTH ls)` by rw[FRONT_LENGTH] >>
    `n < PRE (LENGTH ls)` by decide_tac >>
    rw[FRONT_EL]
  ]);

(* ------------------------------------------------------------------------- *)
(* Unit-List and Mono-List                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (LENGTH l = 1) ==> SING (set l) *)
(* Proof:
   Since ?x. l = [x]   by LENGTH_EQ_1
         set l = {x}   by LIST_TO_SET_DEF
      or SING (set l)  by SING_DEF
*)
val LIST_TO_SET_SING = store_thm(
  "LIST_TO_SET_SING",
  ``!l. (LENGTH l = 1) ==> SING (set l)``,
  rw[LENGTH_EQ_1, SING_DEF] >>
  `set [x] = {x}` by rw[] >>
  metis_tac[]);

(* Mono-list Theory: a mono-list is a list l with SING (set l) *)

(* Theorem: Two mono-lists are equal if their lengths and sets are equal.
            SING (set l1) /\ SING (set l2) ==>
            ((l1 = l2) <=> (LENGTH l1 = LENGTH l2) /\ (set l1 = set l2)) *)
(* Proof:
   By induction on l1.
   Base case: !l2. SING (set []) /\ SING (set l2) ==>
              (([] = l2) <=> (LENGTH [] = LENGTH l2) /\ (set [] = set l2))
     True by SING (set []) is False, by SING_EMPTY.
   Step case: !l2. SING (set l1) /\ SING (set l2) ==>
              ((l1 = l2) <=> (LENGTH l1 = LENGTH l2) /\ (set l1 = set l2)) ==>
              !h l2. SING (set (h::l1)) /\ SING (set l2) ==>
              ((h::l1 = l2) <=> (LENGTH (h::l1) = LENGTH l2) /\ (set (h::l1) = set l2))
     This is to show:
     (1) 1 = LENGTH l2 /\ {h} = set l2 ==>
         ([h] = l2) <=> (SUC (LENGTH []) = LENGTH l2) /\ (h INSERT set [] = set l2)
         If-part, l2 = [h],
              LENGTH l2 = 1 = SUC 0 = SUC (LENGTH [])   by LENGTH, ONE
          and set l2 = set [h] = {h} = h INSERT set []  by LIST_TO_SET
         Only-if part, LENGTH l2 = SUC 0 = 1            by ONE
            Then ?x. l2 = [x]                           by LENGTH_EQ_1
              so set l2 = {x} = {h}                     by LIST_TO_SET
              or x = h, hence l2 = [h]                  by EQUAL_SING
     (2) set l1 = {h} /\ SING (set l2) ==>
         (h::l1 = l2) <=> (SUC (LENGTH l1) = LENGTH l2) /\ (h INSERT set l1 = set l2)
         If part, h::l1 = l2.
            Then LENGTH l2 = LENGTH (h::l1) = SUC (LENGTH l1)  by LENGTH
             and set l2 = set (h::l1) = h INSERT set l1        by LIST_TO_SET
         Only-if part, SUC (LENGTH l1) = LENGTH l2.
            Since 0 < SUC (LENGTH l1)   by prim_recTheory.LESS_0
                  0 < LENGTH l2         by LESS_TRANS
               so ?k t. l2 = k::t       by LENGTH_NON_NIL, list_CASES
            Since LENGTH l2 = SUC (LENGTH t)   by LENGTH
                  LENGTH l1 = LENGTH t         by prim_recTheory.INV_SUC_EQ
              and set l2 = k INSERT set t      by LIST_TO_SET
            Given SING (set l2),
            either (set t = {}), or (set t = {k})  by SING_INSERT
            If set t = {},
               then t = []              by LIST_TO_SET_EQ_EMPTY
                and l1 = []             by LENGTH_NIL, LENGTH l1 = LENGTH t.
                 so set l1 = {}         by LIST_TO_SET_EQ_EMPTY
            contradicting set l1 = {h}  by NOT_SING_EMPTY
            If set t = {k},
               then set l2 = set t      by ABSORPTION, set l2 = k INSERT set {k}.
                 or k = h               by IN_SING
                 so l1 = t              by induction hypothesis
             giving l2 = h::l1
*)
Theorem MONOLIST_EQ:
  !l1 l2. SING (set l1) /\ SING (set l2) ==>
          ((l1 = l2) <=> (LENGTH l1 = LENGTH l2) /\ (set l1 = set l2))
Proof
  Induct >> rw[NOT_SING_EMPTY, SING_INSERT] >| [
    Cases_on `l2` >> rw[] >>
    full_simp_tac (srw_ss()) [SING_INSERT, EQUAL_SING] >>
    rw[LENGTH_NIL, NOT_SING_EMPTY, EQUAL_SING] >> metis_tac[],
    Cases_on `l2` >> rw[] >>
    full_simp_tac (srw_ss()) [SING_INSERT, LENGTH_NIL, NOT_SING_EMPTY,
                              EQUAL_SING] >>
    metis_tac[]
  ]
QED

(* Theorem: A non-mono-list has at least one element in tail that is distinct from its head.
           ~SING (set (h::t)) ==> ?h'. h' IN set t /\ h' <> h *)
(* Proof:
   By SING_INSERT, this is to show:
      t <> [] /\ set t <> {h} ==> ?h'. MEM h' t /\ h' <> h
   Now, t <> [] ==> set t <> {}   by LIST_TO_SET_EQ_EMPTY
     so ?e. e IN set t            by MEMBER_NOT_EMPTY
     hence MEM e t,
       and MEM x t <=/=> (x = h)  by EXTENSION
   Therefore, e <> h, so take h' = e.
*)
val NON_MONO_TAIL_PROPERTY = store_thm(
  "NON_MONO_TAIL_PROPERTY",
  ``!l. ~SING (set (h::t)) ==> ?h'. h' IN set t /\ h' <> h``,
  rw[SING_INSERT] >>
  `set t <> {}` by metis_tac[LIST_TO_SET_EQ_EMPTY] >>
  `?e. e IN set t` by metis_tac[MEMBER_NOT_EMPTY] >>
  full_simp_tac (srw_ss())[EXTENSION] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* GENLIST Theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: GENLIST f 0 = [] *)
(* Proof: by GENLIST *)
val GENLIST_0 = store_thm(
  "GENLIST_0",
  ``!f. GENLIST f 0 = []``,
  rw[]);

(* Theorem: GENLIST f 1 = [f 0] *)
(* Proof:
      GENLIST f 1
    = GENLIST f (SUC 0)          by ONE
    = SNOC (f 0) (GENLIST f 0)   by GENLIST
    = SNOC (f 0) []              by GENLIST
    = [f 0]                      by SNOC
*)
val GENLIST_1 = store_thm(
  "GENLIST_1",
  ``!f. GENLIST f 1 = [f 0]``,
  rw[]);

(* Theorem alias *)
Theorem GENLIST_EQ =
   listTheory.GENLIST_CONG |> GEN ``n:num`` |> GEN ``f2:num -> 'a``
                           |> GEN ``f1:num -> 'a``;
(*
val GENLIST_EQ = |- !f1 f2 n. (!m. m < n ==> f1 m = f2 m) ==> GENLIST f1 n = GENLIST f2 n: thm
*)

(* Theorem: (GENLIST f n = []) <=> (n = 0) *)
(* Proof:
   If part: GENLIST f n = [] ==> n = 0
      By contradiction, suppose n <> 0.
      Then LENGTH (GENLIST f n) = n <> 0  by LENGTH_GENLIST
      This contradicts LENGTH [] = 0.
   Only-if part: GENLIST f 0 = [], true   by GENLIST_0
*)
val GENLIST_EQ_NIL = store_thm(
  "GENLIST_EQ_NIL",
  ``!f n. (GENLIST f n = []) <=> (n = 0)``,
  rw[EQ_IMP_THM] >>
  metis_tac[LENGTH_GENLIST, LENGTH_NIL]);

(* Theorem: LAST (GENLIST f (SUC n)) = f n *)
(* Proof:
     LAST (GENLIST f (SUC n))
   = LAST (SNOC (f n) (GENLIST f n))  by GENLIST
   = f n                              by LAST_SNOC
*)
val GENLIST_LAST = store_thm(
  "GENLIST_LAST",
  ``!f n. LAST (GENLIST f (SUC n)) = f n``,
  rw[GENLIST]);

(* Note:

- EVERY_MAP;
> val it = |- !P f l. EVERY P (MAP f l) <=> EVERY (\x. P (f x)) l : thm
- EVERY_GENLIST;
> val it = |- !n. EVERY P (GENLIST f n) <=> !i. i < n ==> P (f i) : thm
- MAP_GENLIST;
> val it = |- !f g n. MAP f (GENLIST g n) = GENLIST (f o g) n : thm
*)

(* Note: the following can use EVERY_GENLIST. *)

(* Theorem: !k. (k < n ==> f k = c) <=> EVERY (\x. x = c) (GENLIST f n) *)
(* Proof: by induction on n.
   Base case: !c. (!k. k < 0 ==> (f k = c)) <=> EVERY (\x. x = c) (GENLIST f 0)
     Since GENLIST f 0 = [], this is true as no k < 0.
   Step case: (!k. k < n ==> (f k = c)) <=> EVERY (\x. x = c) (GENLIST f n) ==>
              (!k. k < SUC n ==> (f k = c)) <=> EVERY (\x. x = c) (GENLIST f (SUC n))
         EVERY (\x. x = c) (GENLIST f (SUC n))
     <=> EVERY (\x. x = c) (SNOC (f n) (GENLIST f n))  by GENLIST
     <=> EVERY (\x. x = c) (GENLIST f n) /\ (f n = c)  by EVERY_SNOC
     <=> (!k. k < n ==> (f k = c)) /\ (f n = c)        by induction hypothesis
     <=> !k. k < SUC n ==> (f k = c)
*)
val GENLIST_CONSTANT = store_thm(
  "GENLIST_CONSTANT",
  ``!f n c. (!k. k < n ==> (f k = c)) <=> EVERY (\x. x = c) (GENLIST f n)``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[EVERY_DEF, GENLIST, EVERY_SNOC, EQ_IMP_THM] >-
  metis_tac[prim_recTheory.LESS_SUC] >>
  Cases_on `k = n` >-
  rw_tac std_ss[] >>
  metis_tac[prim_recTheory.LESS_THM]);

(* Theorem: GENLIST (K e) (SUC n) = e :: GENLIST (K e) n *)
(* Proof:
     GENLIST (K e) (SUC n)
   = (K e) 0::GENLIST ((K e) o SUC) n   by GENLIST_CONS
   = e :: GENLIST ((K e) o SUC) n       by K_THM
   = e :: GENLIST (K e) n               by K_o_THM
*)
val GENLIST_K_CONS = save_thm("GENLIST_K_CONS",
    SIMP_CONV (srw_ss()) [GENLIST_CONS] ``GENLIST (K e) (SUC n)`` |> GEN ``n:num`` |> GEN ``e``);
(* val GENLIST_K_CONS = |- !e n. GENLIST (K e) (SUC n) = e::GENLIST (K e) n: thm  *)

(* Theorem: GENLIST (K e) (n + m) = GENLIST (K e) m ++ GENLIST (K e) n *)
(* Proof:
   Note (\t. e) = K e    by FUN_EQ_THM
     GENLIST (K e) (n + m)
   = GENLIST (K e) m ++ GENLIST (\t. (K e) (t + m)) n    by GENLIST_APPEND
   = GENLIST (K e) m ++ GENLIST (\t. e) n                by K_THM
   = GENLIST (K e) m ++ GENLIST (K e) n                  by above
*)
val GENLIST_K_ADD = store_thm(
  "GENLIST_K_ADD",
  ``!e n m. GENLIST (K e) (n + m) = GENLIST (K e) m ++ GENLIST (K e) n``,
  rpt strip_tac >>
  `(\t. e) = K e` by rw[FUN_EQ_THM] >>
  rw[GENLIST_APPEND] >>
  metis_tac[]);

(* Theorem: (!k. k < n ==> (f k = e)) ==> (GENLIST f n = GENLIST (K e) n) *)
(* Proof:
   By induction on n.
   Base: GENLIST f 0 = GENLIST (K e) 0
        GENLIST f 0
      = []                          by GENLIST_0
      = GENLIST (K e) 0             by GENLIST_0
   Step: GENLIST f n = GENLIST (K e) n ==>
         GENLIST f (SUC n) = GENLIST (K e) (SUC n)
        GENLIST f (SUC n)
      = SNOC (f n) (GENLIST f n)    by GENLIST
      = SNOC e (GENLIST f n)        by applying f to n
      = SNOC e (GENLIST (K e) n)    by induction hypothesis
      = GENLIST (K e) (SUC n)       by GENLIST
*)
val GENLIST_K_LESS = store_thm(
  "GENLIST_K_LESS",
  ``!f e n. (!k. k < n ==> (f k = e)) ==> (GENLIST f n = GENLIST (K e) n)``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[GENLIST]);

(* Theorem: (!k. 0 < k /\ k <= n ==> (f k = e)) ==> (GENLIST (f o SUC) n = GENLIST (K e) n) *)
(* Proof:
   Base: GENLIST (f o SUC) 0 = GENLIST (K e) 0
         GENLIST (f o SUC) 0
       = []                                by GENLIST_0
       = GENLIST (K e) 0                   by GENLIST_0
   Step: GENLIST (f o SUC) n = GENLIST (K e) n ==>
         GENLIST (f o SUC) (SUC n) = GENLIST (K e) (SUC n)
         GENLIST (f o SUC) (SUC n)
       = SNOC (f n) (GENLIST (f o SUC) n)  by GENLIST
       = SNOC e (GENLIST (f o SUC) n)      by applying f to n
       = SNOC e GENLIST (K e) n            by induction hypothesis
       = GENLIST (K e) (SUC n)             by GENLIST
*)
val GENLIST_K_RANGE = store_thm(
  "GENLIST_K_RANGE",
  ``!f e n. (!k. 0 < k /\ k <= n ==> (f k = e)) ==> (GENLIST (f o SUC) n = GENLIST (K e) n)``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[GENLIST]);

(* Theorem: GENLIST (K c) a ++ GENLIST (K c) b = GENLIST (K c) (a + b) *)
(* Proof:
   Note (\t. c) = K c           by FUN_EQ_THM
     GENLIST (K c) (a + b)
   = GENLIST (K c) (b + a)                              by ADD_COMM
   = GENLIST (K c) a ++ GENLIST (\t. (K c) (t + a)) b   by GENLIST_APPEND
   = GENLIST (K c) a ++ GENLIST (\t. c) b               by applying constant function
   = GENLIST (K c) a ++ GENLIST (K c) b                 by GENLIST_FUN_EQ
*)
val GENLIST_K_APPEND = store_thm(
  "GENLIST_K_APPEND",
  ``!a b c. GENLIST (K c) a ++ GENLIST (K c) b = GENLIST (K c) (a + b)``,
  rpt strip_tac >>
  `(\t. c) = K c` by rw[FUN_EQ_THM] >>
  `GENLIST (K c) (a + b) = GENLIST (K c) (b + a)` by rw[] >>
  `_ = GENLIST (K c) a ++ GENLIST (\t. (K c) (t + a)) b` by rw[GENLIST_APPEND] >>
  rw[GENLIST_FUN_EQ]);

(* Theorem: GENLIST (K c) n ++ [c] = [c] ++ GENLIST (K c) n *)
(* Proof:
     GENLIST (K c) n ++ [c]
   = GENLIST (K c) n ++ GENLIST (K c) 1      by GENLIST_1
   = GENLIST (K c) (n + 1)                   by GENLIST_K_APPEND
   = GENLIST (K c) (1 + n)                   by ADD_COMM
   = GENLIST (K c) 1 ++ GENLIST (K c) n      by GENLIST_K_APPEND
   = [c] ++ GENLIST (K c) n                  by GENLIST_1
*)
val GENLIST_K_APPEND_K = store_thm(
  "GENLIST_K_APPEND_K",
  ``!c n. GENLIST (K c) n ++ [c] = [c] ++ GENLIST (K c) n``,
  metis_tac[GENLIST_K_APPEND, GENLIST_1, ADD_COMM, combinTheory.K_THM]);

(* Theorem: 0 < n ==> (MEM x (GENLIST (K c) n) <=> (x = c)) *)
(* Proof:
       MEM x (GENLIST (K c) n
   <=> ?m. m < n /\ (x = (K c) m)    by MEM_GENLIST
   <=> ?m. m < n /\ (x = c)          by K_THM
   <=> (x = c)                       by taking m = 0, 0 < n
*)
Theorem GENLIST_K_MEM:
  !x c n. 0 < n ==> (MEM x (GENLIST (K c) n) <=> (x = c))
Proof
  metis_tac[MEM_GENLIST, combinTheory.K_THM]
QED

(* Theorem: 0 < n ==> (set (GENLIST (K c) n) = {c}) *)
(* Proof:
   By induction on n.
   Base: 0 < 0 ==> (set (GENLIST (K c) 0) = {c})
      Since 0 < 0 = F, hence true.
   Step: 0 < n ==> (set (GENLIST (K c) n) = {c}) ==>
         0 < SUC n ==> (set (GENLIST (K c) (SUC n)) = {c})
      If n = 0,
        set (GENLIST (K c) (SUC 0)
      = set (GENLIST (K c) 1          by ONE
      = set [(K c) 0]                 by GENLIST_1
      = set [c]                       by K_THM
      = {c}                           by LIST_TO_SET
      If n <> 0, 0 < n.
        set (GENLIST (K c) (SUC n)
      = set (SNOC ((K c) n) (GENLIST (K c) n))     by GENLIST
      = set (SNOC c (GENLIST (K c) n)              by K_THM
      = c INSERT set (GENLIST (K c) n)             by LIST_TO_SET_SNOC
      = c INSERT {c}                               by induction hypothesis
      = {c}                                        by IN_INSERT
 *)
Theorem GENLIST_K_SET:
  !c n. 0 < n ==> (set (GENLIST (K c) n) = {c})
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  simp[] >>
  (Cases_on `n = 0` >> simp[]) >>
  `0 < n` by decide_tac >>
  simp[GENLIST, LIST_TO_SET_SNOC]
QED

(* Theorem: ls <> [] ==> (SING (set ls) <=> ?c. ls = GENLIST (K c) (LENGTH ls)) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] ==> (SING (set []) <=> ?c. [] = GENLIST (K c) (LENGTH []))
     Since [] <> [] = F, hence true.
   Step: ls <> [] ==> (SING (set ls) <=> ?c. ls = GENLIST (K c) (LENGTH ls)) ==>
         !h. h::ls <> [] ==>
             (SING (set (h::ls)) <=> ?c. h::ls = GENLIST (K c) (LENGTH (h::ls)))
     Note h::ls <> [] = T.
     If part: SING (set (h::ls)) ==> ?c. h::ls = GENLIST (K c) (LENGTH (h::ls))
        Note SING (set (h::ls)) means
             set ls = {h}                by LIST_TO_SET_DEF, IN_SING
         Let n = LENGTH ls, 0 < n        by LENGTH_NON_NIL
        Note ls <> []                    by LIST_TO_SET, IN_SING, MEMBER_NOT_EMPTY
         and SING (set ls)               by SING_DEF
         ==> ?c. ls = GENLIST (K c) n    by induction hypothesis
          so set ls = {c}                by GENLIST_K_SET, 0 < n
         ==> h = c                       by IN_SING
           GENLIST (K c) (LENGTH (h::ls)
         = (K c) h :: ls                 by GENLIST_K_CONS
         = c :: ls                       by K_THM
         = h::ls                         by h = c
     Only-if part: ?c. h::ls = GENLIST (K c) (LENGTH (h::ls)) ==> SING (set (h::ls))
           set (h::ls)
         = set (GENLIST (K c) (LENGTH (h::ls)))        by given
         = set ((K c) h :: GENLIST (K c) (LENGTH ls))  by GENLIST_K_CONS
         = set (c :: GENLIST (K c) (LENGTH ls))        by K_THM
         = c INSERT set (GENLIST (K c) (LENGTH ls))    by LIST_TO_SET
         = c INSERT {c}                                by GENLIST_K_SET
         = {c}                                         by IN_INSERT
         Hence SING (set (h::ls))                      by SING_DEF
*)
Theorem LIST_TO_SET_SING_IFF:
  !ls. ls <> [] ==> (SING (set ls) <=> ?c. ls = GENLIST (K c) (LENGTH ls))
Proof
  Induct >-
  simp[] >>
  (rw[EQ_IMP_THM] >> simp[]) >| [
    qexists_tac `h` >>
    qabbrev_tac `n = LENGTH ls` >>
    `ls <> []` by metis_tac[LIST_TO_SET, IN_SING, MEMBER_NOT_EMPTY] >>
    `SING (set ls)` by fs[SING_DEF] >>
    fs[] >>
    `0 < n` by metis_tac[LENGTH_NON_NIL] >>
    `h = c` by metis_tac[GENLIST_K_SET, IN_SING] >>
    simp[GENLIST_K_CONS],
    spose_not_then strip_assume_tac >>
    fs[GENLIST_K_CONS] >>
    `0 < LENGTH ls` by metis_tac[LENGTH_NON_NIL] >>
    metis_tac[GENLIST_K_SET]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* SUM Theorems                                                              *)
(* ------------------------------------------------------------------------- *)

(* Defined: SUM for summation of list = sequence *)

(* Theorem: SUM [] = 0 *)
(* Proof: by definition. *)
val SUM_NIL = save_thm("SUM_NIL", SUM |> CONJUNCT1);
(* > val SUM_NIL = |- SUM [] = 0 : thm *)

(* Theorem: SUM h::t = h + SUM t *)
(* Proof: by definition. *)
val SUM_CONS = save_thm("SUM_CONS", SUM |> CONJUNCT2);
(* val SUM_CONS = |- !h t. SUM (h::t) = h + SUM t: thm *)

(* Theorem: SUM [n] = n *)
(* Proof: by SUM *)
val SUM_SING = store_thm(
  "SUM_SING",
  ``!n. SUM [n] = n``,
  rw[]);

(* Theorem: SUM (s ++ t) = SUM s + SUM t *)
(* Proof: by induction on s *)
(*
val SUM_APPEND = store_thm(
  "SUM_APPEND",
  ``!s t. SUM (s ++ t) = SUM s + SUM t``,
  Induct_on `s` >-
  rw[] >>
  rw[ADD_ASSOC]);
*)
(* There is already a SUM_APPEND in up-to-date listTheory *)

(* Theorem: constant multiplication: k * SUM s = SUM (k * s)  *)
(* Proof: by induction on s.
   Base case: !k. k * SUM [] = SUM (MAP ($* k) [])
     LHS = k * SUM [] = k * 0 = 0         by SUM_NIL, MULT_0
         = SUM []                         by SUM_NIL
         = SUM (MAP ($* k) []) = RHS      by MAP
   Step case: !k. k * SUM s = SUM (MAP ($* k) s) ==>
              !h k. k * SUM (h::s) = SUM (MAP ($* k) (h::s))
     LHS = k * SUM (h::s)
         = k * (h + SUM s)                by SUM_CONS
         = k * h + k * SUM s              by LEFT_ADD_DISTRIB
         = k * h + SUM (MAP ($* k) s)     by induction hypothesis
         = SUM (k * h :: (MAP ($* k) s))  by SUM_CONS
         = SUM (MAP ($* k) (h::s))        by MAP
         = RHS
*)
val SUM_MULT = store_thm(
  "SUM_MULT",
  ``!s k. k * SUM s = SUM (MAP ($* k) s)``,
  Induct_on `s` >-
  metis_tac[SUM, MAP, MULT_0] >>
  metis_tac[SUM, MAP, LEFT_ADD_DISTRIB]);

(* Theorem: (m + n) * SUM s = SUM (m * s) + SUM (n * s)  *)
(* Proof: generalization of
- RIGHT_ADD_DISTRIB;
> val it = |- !m n p. (m + n) * p = m * p + n * p : thm
     (m + n) * SUM s
   = m * SUM s + n * SUM s                               by RIGHT_ADD_DISTRIB
   = SUM (MAP (\x. m * x) s) + SUM (MAP (\x. n * x) s)   by SUM_MULT
*)
val SUM_RIGHT_ADD_DISTRIB = store_thm(
  "SUM_RIGHT_ADD_DISTRIB",
  ``!s m n. (m + n) * SUM s = SUM (MAP ($* m) s) + SUM (MAP ($* n) s)``,
  metis_tac[RIGHT_ADD_DISTRIB, SUM_MULT]);

(* Theorem: (SUM s) * (m + n) = SUM (m * s) + SUM (n * s)  *)
(* Proof: generalization of
- LEFT_ADD_DISTRIB;
> val it = |- !m n p. p * (m + n) = p * m + p * n : thm
     (SUM s) * (m + n)
   = (m + n) * SUM s                           by MULT_COMM
   = SUM (MAP ($* m) s) + SUM (MAP ($* n) s)   by SUM_RIGHT_ADD_DISTRIB
*)
val SUM_LEFT_ADD_DISTRIB = store_thm(
  "SUM_LEFT_ADD_DISTRIB",
  ``!s m n. (SUM s) * (m + n) = SUM (MAP ($* m) s) + SUM (MAP ($* n) s)``,
  metis_tac[SUM_RIGHT_ADD_DISTRIB, MULT_COMM]);


(*
- EVAL ``GENLIST I 4``;
> val it = |- GENLIST I 4 = [0; 1; 2; 3] : thm
- EVAL ``GENLIST SUC 4``;
> val it = |- GENLIST SUC 4 = [1; 2; 3; 4] : thm
- EVAL ``GENLIST (\k. binomial 4 k) 5``;
> val it = |- GENLIST (\k. binomial 4 k) 5 = [1; 4; 6; 4; 1] : thm
- EVAL ``GENLIST (\k. binomial 5 k) 6``;
> val it = |- GENLIST (\k. binomial 5 k) 6 = [1; 5; 10; 10; 5; 1] : thm
- EVAL ``GENLIST (\k. binomial 10 k) 11``;
> val it = |- GENLIST (\k. binomial 10 k) 11 = [1; 10; 45; 120; 210; 252; 210; 120; 45; 10; 1] : thm
*)

(* Theorems on GENLIST:

- GENLIST;
> val it = |- (!f. GENLIST f 0 = []) /\
               !f n. GENLIST f (SUC n) = SNOC (f n) (GENLIST f n) : thm
- NULL_GENLIST;
> val it = |- !n f. NULL (GENLIST f n) <=> (n = 0) : thm
- GENLIST_CONS;
> val it = |- GENLIST f (SUC n) = f 0::GENLIST (f o SUC) n : thm
- EL_GENLIST;
> val it = |- !f n x. x < n ==> (EL x (GENLIST f n) = f x) : thm
- EXISTS_GENLIST;
> val it = |- !n. EXISTS P (GENLIST f n) <=> ?i. i < n /\ P (f i) : thm
- EVERY_GENLIST;
> val it = |- !n. EVERY P (GENLIST f n) <=> !i. i < n ==> P (f i) : thm
- MAP_GENLIST;
> val it = |- !f g n. MAP f (GENLIST g n) = GENLIST (f o g) n : thm
- GENLIST_APPEND;
> val it = |- !f a b. GENLIST f (a + b) = GENLIST f b ++ GENLIST (\t. f (t + b)) a : thm
- HD_GENLIST;
> val it = |- HD (GENLIST f (SUC n)) = f 0 : thm
- TL_GENLIST;
> val it = |- !f n. TL (GENLIST f (SUC n)) = GENLIST (f o SUC) n : thm
- HD_GENLIST_COR;
> val it = |- !n f. 0 < n ==> (HD (GENLIST f n) = f 0) : thm
- GENLIST_FUN_EQ;
> val it = |- !n f g. (GENLIST f n = GENLIST g n) <=> !x. x < n ==> (f x = g x) : thm

*)

(* Theorem: SUM (GENLIST f n) = SIGMA f (count n) *)
(* Proof:
   By induction on n.
   Base: SUM (GENLIST f 0) = SIGMA f (count 0)

         SUM (GENLIST f 0)
       = SUM []                by GENLIST_0
       = 0                     by SUM_NIL
       = SIGMA f {}            by SUM_IMAGE_THM
       = SIGMA f (count 0)     by COUNT_0

   Step: SUM (GENLIST f n) = SIGMA f (count n) ==>
         SUM (GENLIST f (SUC n)) = SIGMA f (count (SUC n))

         SUM (GENLIST f (SUC n))
       = SUM (SNOC (f n) (GENLIST f n))   by GENLIST
       = f n + SUM (GENLIST f n)          by SUM_SNOC
       = f n + SIGMA f (count n)          by induction hypothesis
       = f n + SIGMA f (count n DELETE n) by IN_COUNT, DELETE_NON_ELEMENT
       = SIGMA f (n INSERT count n)       by SUM_IMAGE_THM, FINITE_COUNT
       = SIGMA f (count (SUC n))          by COUNT_SUC
*)
val SUM_GENLIST = store_thm(
  "SUM_GENLIST",
  ``!f n. SUM (GENLIST f n) = SIGMA f (count n)``,
  strip_tac >>
  Induct >-
  rw[SUM_IMAGE_THM] >>
  `SUM (GENLIST f (SUC n)) = SUM (SNOC (f n) (GENLIST f n))` by rw[GENLIST] >>
  `_ = f n + SUM (GENLIST f n)` by rw[SUM_SNOC] >>
  `_ = f n + SIGMA f (count n)` by rw[] >>
  `_ = f n + SIGMA f (count n DELETE n)`
    by metis_tac[IN_COUNT, prim_recTheory.LESS_REFL, DELETE_NON_ELEMENT] >>
  `_ = SIGMA f (n INSERT count n)` by rw[SUM_IMAGE_THM] >>
  `_ = SIGMA f (count (SUC n))` by rw[COUNT_SUC] >>
  decide_tac);

(* Theorem: SUM (k=0..n) f(k) = f(0) + SUM (k=1..n) f(k)  *)
(* Proof:
     SUM (GENLIST f (SUC n))
   = SUM (f 0 :: GENLIST (f o SUC) n)   by GENLIST_CONS
   = f 0 + SUM (GENLIST (f o SUC) n)    by SUM definition.
*)
val SUM_DECOMPOSE_FIRST = store_thm(
  "SUM_DECOMPOSE_FIRST",
  ``!f n. SUM (GENLIST f (SUC n)) = f 0 + SUM (GENLIST (f o SUC) n)``,
  metis_tac[GENLIST_CONS, SUM]);

(* Theorem: SUM (k=0..n) f(k) = SUM (k=0..(n-1)) f(k) + f n *)
(* Proof:
     SUM (GENLIST f (SUC n))
   = SUM (SNOC (f n) (GENLIST f n))  by GENLIST definition
   = SUM ((GENLIST f n) ++ [f n])    by SNOC_APPEND
   = SUM (GENLIST f n) + SUM [f n]   by SUM_APPEND
   = SUM (GENLIST f n) + f n         by SUM definition: SUM (h::t) = h + SUM t, and SUM [] = 0.
*)
val SUM_DECOMPOSE_LAST = store_thm(
  "SUM_DECOMPOSE_LAST",
  ``!f n. SUM (GENLIST f (SUC n)) = SUM (GENLIST f n) + f n``,
  rpt strip_tac >>
  `SUM (GENLIST f (SUC n)) = SUM (SNOC (f n) (GENLIST f n))` by metis_tac[GENLIST] >>
  `_ = SUM ((GENLIST f n) ++ [f n])` by metis_tac[SNOC_APPEND] >>
  `_ = SUM (GENLIST f n) + SUM [f n]` by metis_tac[SUM_APPEND] >>
  rw[SUM]);

(* Theorem: SUM (GENLIST a n) + SUM (GENLIST b n) = SUM (GENLIST (\k. a k + b k) n) *)
(* Proof: by induction on n.
   Base case: !a b. SUM (GENLIST a 0) + SUM (GENLIST b 0) = SUM (GENLIST (\k. a k + b k) 0)
     Since GENLIST f 0 = []    by GENLIST
       and SUM [] = 0          by SUM_NIL
     This is just 0 + 0 = 0, true by arithmetic.
   Step case: !a b. SUM (GENLIST a n) + SUM (GENLIST b n) =
                    SUM (GENLIST (\k. a k + b k) n) ==>
              !a b. SUM (GENLIST a (SUC n)) + SUM (GENLIST b (SUC n)) =
                    SUM (GENLIST (\k. a k + b k) (SUC n))
       SUM (GENLIST a (SUC n)) + SUM (GENLIST b (SUC n)
     = (SUM (GENLIST a n) + a n) + (SUM (GENLIST b n) + b n)  by SUM_DECOMPOSE_LAST
     = SUM (GENLIST a n) + SUM (GENLIST b n) + (a n + b n)    by arithmetic
     = SUM (GENLIST (\k. a k + b k) n) + (a n + b n)          by induction hypothesis
     = SUM (GENLIST (\k. a k + b k) (SUC n))                  by SUM_DECOMPOSE_LAST
*)
val SUM_ADD_GENLIST = store_thm(
  "SUM_ADD_GENLIST",
  ``!a b n. SUM (GENLIST a n) + SUM (GENLIST b n) = SUM (GENLIST (\k. a k + b k) n)``,
  Induct_on `n` >-
  rw[] >>
  rw[SUM_DECOMPOSE_LAST]);

(* Theorem: SUM (GENLIST a n ++ GENLIST b n) = SUM (GENLIST (\k. a k + b k) n) *)
(* Proof:
     SUM (GENLIST a n ++ GENLIST b n)
   = SUM (GENLIST a n) + SUM (GENLIST b n)  by SUM_APPEND
   = SUM (GENLIST (\k. a k + b k) n)        by SUM_ADD_GENLIST
*)
val SUM_GENLIST_APPEND = store_thm(
  "SUM_GENLIST_APPEND",
  ``!a b n. SUM (GENLIST a n ++ GENLIST b n) = SUM (GENLIST (\k. a k + b k) n)``,
  metis_tac[SUM_APPEND, SUM_ADD_GENLIST]);

(* Theorem: 0 < n ==> SUM (GENLIST f (SUC n)) = f 0 + SUM (GENLIST (f o SUC) (PRE n)) + f n *)
(* Proof:
     SUM (GENLIST f (SUC n))
   = SUM (GENLIST f n) + f n                       by SUM_DECOMPOSE_LAST
   = SUM (GENLIST f (SUC m)) + f n                 by n = SUC m, 0 < n
   = f 0 + SUM (GENLIST (f o SUC) m) + f n         by SUM_DECOMPOSE_FIRST
   = f 0 + SUM (GENLIST (f o SUC) (PRE n)) + f n   by PRE_SUC_EQ
*)
val SUM_DECOMPOSE_FIRST_LAST = store_thm(
  "SUM_DECOMPOSE_FIRST_LAST",
  ``!f n. 0 < n ==> (SUM (GENLIST f (SUC n)) = f 0 + SUM (GENLIST (f o SUC) (PRE n)) + f n)``,
  metis_tac[SUM_DECOMPOSE_LAST, SUM_DECOMPOSE_FIRST, SUC_EXISTS, PRE_SUC_EQ]);

(* Theorem: (SUM l) MOD n = (SUM (MAP (\x. x MOD n) l)) MOD n *)
(* Proof: by list induction.
   Base case: SUM [] MOD n = SUM (MAP (\x. x MOD n) []) MOD n
      true by SUM [] = 0, MAP f [] = 0, and 0 MOD n = 0.
   Step case: SUM l MOD n = SUM (MAP (\x. x MOD n) l) MOD n ==>
              !h. SUM (h::l) MOD n = SUM (MAP (\x. x MOD n) (h::l)) MOD n
      SUM (h::l) MOD n
    = (h + SUM l) MOD n                                           by SUM
    = (h MOD n + (SUM l) MOD n) MOD n                             by MOD_PLUS
    = (h MOD n + SUM (MAP (\x. x MOD n) l) MOD n) MOD n           by induction hypothesis
    = ((h MOD n) MOD n + SUM (MAP (\x. x MOD n) l) MOD n) MOD n   by MOD_MOD
    = ((h MOD n + SUM (MAP (\x. x MOD n) l)) MOD n) MOD n         by MOD_PLUS
    = (h MOD n + SUM (MAP (\x. x MOD n) l)) MOD n                 by MOD_MOD
    = (SUM (h MOD n ::(MAP (\x. x MOD n) l))) MOD n               by SUM
    = (SUM (MAP (\x. x MOD n) (h::l))) MOD n                      by MAP
*)
val SUM_MOD = store_thm(
  "SUM_MOD",
  ``!n. 0 < n ==> !l. (SUM l) MOD n = (SUM (MAP (\x. x MOD n) l)) MOD n``,
  rpt strip_tac >>
  Induct_on `l` >-
  rw[] >>
  rpt strip_tac >>
  `SUM (h::l) MOD n = (h MOD n + (SUM l) MOD n) MOD n` by rw_tac std_ss[SUM, MOD_PLUS] >>
  `_ = ((h MOD n) MOD n + SUM (MAP (\x. x MOD n) l) MOD n) MOD n` by rw_tac std_ss[MOD_MOD] >>
  rw[MOD_PLUS]);

(* Theorem: SUM l = 0 <=> l = EVERY (\x. x = 0) l *)
(* Proof: by induction on l.
   Base case: (SUM [] = 0) <=> EVERY (\x. x = 0) []
      true by SUM [] = 0 and GENLIST f 0 = [].
   Step case: (SUM l = 0) <=> EVERY (\x. x = 0) l ==>
              !h. (SUM (h::l) = 0) <=> EVERY (\x. x = 0) (h::l)
       SUM (h::l) = 0
   <=> h + SUM l = 0                  by SUM
   <=> h = 0 /\ SUM l = 0             by ADD_EQ_0
   <=> h = 0 /\ EVERY (\x. x = 0) l   by induction hypothesis
   <=> EVERY (\x. x = 0) (h::l)       by EVERY_DEF
*)
val SUM_EQ_0 = store_thm(
  "SUM_EQ_0",
  ``!l. (SUM l = 0) <=> EVERY (\x. x = 0) l``,
  Induct >>
  rw[]);

(* Theorem: SUM (GENLIST ((\k. f k) o SUC) (PRE n)) MOD n =
            SUM (GENLIST ((\k. f k MOD n) o SUC) (PRE n)) MOD n *)
(* Proof:
     SUM (GENLIST ((\k. f k) o SUC) (PRE n)) MOD n
   = SUM (MAP (\x. x MOD n) (GENLIST ((\k. f k) o SUC) (PRE n))) MOD n  by SUM_MOD
   = SUM (GENLIST ((\x. x MOD n) o ((\k. f k) o SUC)) (PRE n)) MOD n    by MAP_GENLIST
   = SUM (GENLIST ((\x. x MOD n) o (\k. f k) o SUC) (PRE n)) MOD n      by composition associative
   = SUM (GENLIST ((\k. f k MOD n) o SUC) (PRE n)) MOD n                by composition
*)
val SUM_GENLIST_MOD = store_thm(
  "SUM_GENLIST_MOD",
  ``!n. 0 < n ==> !f. SUM (GENLIST ((\k. f k) o SUC) (PRE n)) MOD n = SUM (GENLIST ((\k. f k MOD n) o SUC) (PRE n)) MOD n``,
  rpt strip_tac >>
  `SUM (GENLIST ((\k. f k) o SUC) (PRE n)) MOD n =
    SUM (MAP (\x. x MOD n) (GENLIST ((\k. f k) o SUC) (PRE n))) MOD n` by metis_tac[SUM_MOD] >>
  rw_tac std_ss[MAP_GENLIST, combinTheory.o_ASSOC, combinTheory.o_ABS_L]);

(* Theorem: SUM (GENLIST (\j. x) n) = n * x *)
(* Proof:
   By induction on n.
   Base case: !x. SUM (GENLIST (\j. x) 0) = 0 * x
       SUM (GENLIST (\j. x) 0)
     = SUM []                   by GENLIST
     = 0                        by SUM
     = 0 * x                    by MULT
   Step case: !x. SUM (GENLIST (\j. x) n) = n * x ==>
              !x. SUM (GENLIST (\j. x) (SUC n)) = SUC n * x
       SUM (GENLIST (\j. x) (SUC n))
     = SUM (SNOC x (GENLIST (\j. x) n))   by GENLIST
     = SUM (GENLIST (\j. x) n) + x        by SUM_SNOC
     = n * x + x                          by induction hypothesis
     = SUC n * x                          by MULT
*)
val SUM_CONSTANT = store_thm(
  "SUM_CONSTANT",
  ``!n x. SUM (GENLIST (\j. x) n) = n * x``,
  Induct >-
  rw[] >>
  rw_tac std_ss[GENLIST, SUM_SNOC, MULT]);

(* Theorem: SUM (GENLIST (K m) n) = m * n *)
(* Proof:
   By induction on n.
   Base: SUM (GENLIST (K m) 0) = m * 0
        SUM (GENLIST (K m) 0)
      = SUM []                 by GENLIST
      = 0                      by SUM
      = m * 0                  by MULT_0
   Step: SUM (GENLIST (K m) n) = m * n ==> SUM (GENLIST (K m) (SUC n)) = m * SUC n
        SUM (GENLIST (K m) (SUC n))
      = SUM (SNOC m (GENLIST (K m) n))    by GENLIST
      = SUM (GENLIST (K m) n) + m         by SUM_SNOC
      = m * n + m                         by induction hypothesis
      = m + m * n                         by ADD_COMM
      = m * SUC n                         by MULT_SUC
*)
val SUM_GENLIST_K = store_thm(
  "SUM_GENLIST_K",
  ``!m n. SUM (GENLIST (K m) n) = m * n``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[GENLIST, SUM_SNOC, MULT_SUC]);

(* Theorem: (LENGTH l1 = LENGTH l2) /\ (!k. k <= LENGTH l1 ==> EL k l1 <= EL k l2) ==> SUM l1 <= SUM l2 *)
(* Proof:
   By induction on l1.
   Base: LENGTH [] = LENGTH l2 ==> SUM [] <= SUM l2
       Note l2 = []               by LENGTH_EQ_0
         so SUM [] = SUM []
         or SUM [] <= SUM l2      by EQ_LESS_EQ
   Step: !l2. (LENGTH l1 = LENGTH l2) /\ ... ==> SUM l1 <= SUM l2 ==>
         (LENGTH (h::l1) = LENGTH l2) /\ ... ==> SUM h::l1 <= SUM l2
       Note l2 <> []              by LENGTH_EQ_0
         so ?h1 t2. l2 = h1::t1   by list_CASES
        and LENGTH l1 = LENGTH t1 by LENGTH
            SUM (h::l1)
          = h + SUM l1            by SUM_CONS
          <= h1 + SUM t1          by EL_ALL_PROPERTY, induction hypothesis
           = SUM l2               by SUM_CONS
*)
val SUM_LE = store_thm(
  "SUM_LE",
  ``!l1 l2. (LENGTH l1 = LENGTH l2) /\ (!k. k < LENGTH l1 ==> EL k l1 <= EL k l2) ==>
           SUM l1 <= SUM l2``,
  Induct >-
  metis_tac[LENGTH_EQ_0, EQ_LESS_EQ] >>
  rpt strip_tac >>
  `?h1 t1. l2 = h1::t1` by metis_tac[LENGTH_EQ_0, list_CASES] >>
  `LENGTH l1 = LENGTH t1` by metis_tac[LENGTH, SUC_EQ] >>
  `SUM (h::l1) = h + SUM l1` by rw[SUM_CONS] >>
  `SUM l2 = h1 + SUM t1` by rw[SUM_CONS] >>
  `(h <= h1) /\ SUM l1 <= SUM t1` by metis_tac[EL_ALL_PROPERTY] >>
  decide_tac);

(* Theorem: MEM x l ==> x <= SUM l *)
(* Proof:
   By induction on l.
   Base: !x. MEM x [] ==> x <= SUM []
      True since MEM x [] = F              by MEM
   Step: !x. MEM x l ==> x <= SUM l ==> !h x. MEM x (h::l) ==> x <= SUM (h::l)
      If x = h,
         Then h <= h + SUM l = SUM (h::l)  by SUM
      If x <> h,
         Then MEM x l                      by MEM
          ==> x <= SUM l                   by induction hypothesis
           or x <= h + SUM l = SUM (h::l)  by SUM
*)
val SUM_LE_MEM = store_thm(
  "SUM_LE_MEM",
  ``!l x. MEM x l ==> x <= SUM l``,
  Induct >-
  rw[] >>
  rw[] >-
  decide_tac >>
  `x <= SUM l` by rw[] >>
  decide_tac);

(* Theorem: n < LENGTH l ==> (EL n l) <= SUM l *)
(* Proof: by SUM_LE_MEM, MEM_EL *)
val SUM_LE_EL = store_thm(
  "SUM_LE_EL",
  ``!l n. n < LENGTH l ==> (EL n l) <= SUM l``,
  metis_tac[SUM_LE_MEM, MEM_EL]);

(* Theorem: m < n /\ n < LENGTH l ==> (EL m l) + (EL n l) <= SUM l *)
(* Proof:
   By induction on l.
   Base: !m n. m < n /\ n < LENGTH [] ==> EL m [] + EL n [] <= SUM []
      True since n < LENGTH [] = F              by LENGTH
   Step: !m n. m < LENGTH l /\ n < LENGTH l ==> EL m l + EL n l <= SUM l ==>
         !h m n. m < LENGTH (h::l) /\ n < LENGTH (h::l) ==> EL m (h::l) + EL n (h::l) <= SUM (h::l)
      Note 0 < n, or n <> 0             by m < n
        so ?k. n = SUC k            by num_CASES
       and k < LENGTH l             by SUC k < SUC (LENGTH l)
       and EL n (h::l) = EL k l     by EL_restricted
      If m = 0,
         Then EL m (h::l) = h       by EL_restricted
          and EL k l <= SUM l       by SUM_LE_EL
         Thus EL m (h::l) + EL n (h::l)
            = h + SUM l
            = SUM (h::l)            by SUM
      If m <> 0,
         Then ?j. m = SUC j         by num_CASES
          and j < k                 by SUC j < SUC k
          and EL m (h::l) = EL j l  by EL_restricted
         Thus EL m (h::l) + EL n (h::l)
            = EL j l + EL k l       by above
           <= SUM l                 by induction hypothesis
           <= h + SUM l             by arithmetic
            = SUM (h::l)            by SUM
*)
val SUM_LE_SUM_EL = store_thm(
  "SUM_LE_SUM_EL",
  ``!l m n. m < n /\ n < LENGTH l ==> (EL m l) + (EL n l) <= SUM l``,
  Induct >-
  rw[] >>
  rw[] >>
  `n <> 0` by decide_tac >>
  `?k. n = SUC k` by metis_tac[num_CASES] >>
  `k < LENGTH l` by decide_tac >>
  `EL n (h::l) = EL k l` by rw[] >>
  Cases_on `m = 0` >| [
    `EL m (h::l) = h` by rw[] >>
    `EL k l <= SUM l` by rw[SUM_LE_EL] >>
    decide_tac,
    `?j. m = SUC j` by metis_tac[num_CASES] >>
    `j < k` by decide_tac >>
    `EL m (h::l) = EL j l` by rw[] >>
    `EL j l + EL k l <= SUM l` by rw[] >>
    decide_tac
  ]);

(* Theorem: SUM (GENLIST (\j. n * 2 ** j) m) = n * (2 ** m - 1) *)
(* Proof:
   The computation is:
       n + (n * 2) + (n * 4) + ... + (n * (2 ** (m - 1)))
     = n * (1 + 2 + 4 + ... + 2 ** (m - 1))
     = n * (2 ** m - 1)

   By induction on m.
   Base: SUM (GENLIST (\j. n * 2 ** j) 0) = n * (2 ** 0 - 1)
      LHS = SUM (GENLIST (\j. n * 2 ** j) 0)
          = SUM []                by GENLIST_0
          = 0                     by PROD
      RHS = n * (1 - 1)           by EXP_0
          = n * 0 = 0 = LHS       by MULT_0
   Step: SUM (GENLIST (\j. n * 2 ** j) m) = n * (2 ** m - 1) ==>
         SUM (GENLIST (\j. n * 2 ** j) (SUC m)) = n * (2 ** SUC m - 1)
         SUM (GENLIST (\j. n * 2 ** j) (SUC m))
       = SUM (SNOC (n * 2 ** m) (GENLIST (\j. n * 2 ** j) m))   by GENLIST
       = SUM (GENLIST (\j. n * 2 ** j) m) + (n * 2 ** m)        by SUM_SNOC
       = n * (2 ** m - 1) + n * 2 ** m                          by induction hypothesis
       = n * (2 ** m - 1 + 2 ** m)                              by LEFT_ADD_DISTRIB
       = n * (2 * 2 ** m - 1)                                   by arithmetic
       = n * (2 ** SUC m - 1)                                   by EXP
*)
val SUM_DOUBLING_LIST = store_thm(
  "SUM_DOUBLING_LIST",
  ``!m n. SUM (GENLIST (\j. n * 2 ** j) m) = n * (2 ** m - 1)``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[] >>
  qabbrev_tac `f = \j. n * 2 ** j` >>
  `SUM (GENLIST f (SUC m)) = SUM (SNOC (n * 2 ** m) (GENLIST f m))` by rw[GENLIST, Abbr`f`] >>
  `_ = SUM (GENLIST f m) + (n * 2 ** m)` by rw[SUM_SNOC] >>
  `_ = n * (2 ** m - 1) + n * 2 ** m` by rw[] >>
  `_ = n * (2 ** m - 1 + 2 ** m)` by rw[LEFT_ADD_DISTRIB] >>
  rw[EXP]);


(* Idea: key theorem, almost like pigeonhole principle. *)

(* List equivalent sum theorems. This is an example of digging out theorems. *)

(* Theorem: EVERY (\x. 0 < x) ls ==> LENGTH ls <= SUM ls *)
(* Proof:
   Let P = (\x. 0 < x).
   By induction on list ls.
   Base: EVERY P [] ==> LENGTH [] <= SUM []
      Note EVERY P [] = T      by EVERY_DEF
       and LENGTH [] = 0       by LENGTH
       and SUM [] = 0          by SUM
      Hence true.
   Step: EVERY P ls ==> LENGTH ls <= SUM ls ==>
         !h. EVERY P (h::ls) ==> LENGTH (h::ls) <= SUM (h::ls)
      Note 0 < h /\ EVERY P ls by EVERY_DEF
           LENGTH (h::ls)
         = 1 + LENGTH ls       by LENGTH
        <= 1 + SUM ls          by induction hypothesis
        <= h + SUM ls          by 0 < h
         = SUM (h::ls)         by SUM
*)
Theorem list_length_le_sum:
  !ls. EVERY (\x. 0 < x) ls ==> LENGTH ls <= SUM ls
Proof
  Induct >-
  rw[] >>
  rw[] >>
  `1 <= h` by decide_tac >>
  fs[]
QED

(* Theorem: EVERY (\x. 0 < x) ls /\ LENGTH ls = SUM ls ==> EVERY (\x. x = 1) ls *)
(* Proof:
   Let P = (\x. 0 < x), Q = (\x. x = 1).
   By induction on list ls.
   Base: EVERY P [] /\ LENGTH [] = SUM [] ==> EVERY Q []
      Note EVERY Q [] = T      by EVERY_DEF
      Hence true.
   Step: EVERY P ls /\ LENGTH ls = SUM ls ==> EVERY Q ls ==>
         !h. EVERY P (h::ls) /\ LENGTH (h::ls) = SUM (h::ls) ==> EVERY Q (h::ls)
      Note 0 < h /\ EVERY P ls by EVERY_DEF
      LHS = LENGTH (h::ls)
          = 1 + LENGTH ls      by LENGTH
         <= 1 + SUM ls         by list_length_le_sum
      RHS = SUM (h::ls)
          = h + SUM ls         by SUM
      Thus h + SUM ls <= 1 + SUM ls
       or h <= 1               by arithmetic
      giving h = 1             by 0 < h
      Thus LENGTH ls = SUM ls  by arithmetic
       and EVERY Q ls          by induction hypothesis
        or EVERY Q (h::ls)     by EVERY_DEF, h = 1
*)
Theorem list_length_eq_sum:
  !ls. EVERY (\x. 0 < x) ls /\ LENGTH ls = SUM ls ==> EVERY (\x. x = 1) ls
Proof
  Induct >-
  rw[] >>
  rpt strip_tac >>
  fs[] >>
  `LENGTH ls <= SUM ls` by rw[list_length_le_sum] >>
  `h + LENGTH ls <= SUC (LENGTH ls)` by fs[] >>
  `h = 1` by decide_tac >>
  `SUM ls = LENGTH ls` by fs[] >>
  simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Maximum of a List                                                         *)
(* ------------------------------------------------------------------------- *)

(* Define MAX of a list *)
val MAX_LIST_def = Define`
    (MAX_LIST [] = 0) /\
    (MAX_LIST (h::t) = MAX h (MAX_LIST t))
`;

(* export simple recursive definition *)
(* val _ = export_rewrites["MAX_LIST_def"]; *)

(* Theorem: MAX_LIST [] = 0 *)
(* Proof: by MAX_LIST_def *)
val MAX_LIST_NIL = save_thm("MAX_LIST_NIL", MAX_LIST_def |> CONJUNCT1);
(* val MAX_LIST_NIL = |- MAX_LIST [] = 0: thm *)

(* Theorem: MAX_LIST (h::t) = MAX h (MAX_LIST t) *)
(* Proof: by MAX_LIST_def *)
val MAX_LIST_CONS = save_thm("MAX_LIST_CONS", MAX_LIST_def |> CONJUNCT2);
(* val MAX_LIST_CONS = |- !h t. MAX_LIST (h::t) = MAX h (MAX_LIST t): thm *)

(* export simple results *)
val _ = export_rewrites["MAX_LIST_NIL", "MAX_LIST_CONS"];

(* Theorem: MAX_LIST [x] = x *)
(* Proof:
     MAX_LIST [x]
   = MAX x (MAX_LIST [])   by MAX_LIST_CONS
   = MAX x 0               by MAX_LIST_NIL
   = x                     by MAX_0
*)
val MAX_LIST_SING = store_thm(
  "MAX_LIST_SING",
  ``!x. MAX_LIST [x] = x``,
  rw[]);

(* Theorem: (MAX_LIST l = 0) <=> EVERY (\x. x = 0) l *)
(* Proof:
   By induction on l.
   Base: (MAX_LIST [] = 0) <=> EVERY (\x. x = 0) []
      LHS: MAX_LIST [] = 0, true           by MAX_LIST_NIL
      RHS: EVERY (\x. x = 0) [], true      by EVERY_DEF
   Step: (MAX_LIST l = 0) <=> EVERY (\x. x = 0) l ==>
         !h. (MAX_LIST (h::l) = 0) <=> EVERY (\x. x = 0) (h::l)
          MAX_LIST (h::l) = 0
      <=> MAX h (MAX_LIST l) = 0           by MAX_LIST_CONS
      <=> (h = 0) /\ (MAX_LIST l = 0)      by MAX_EQ_0
      <=> (h = 0) /\ EVERY (\x. x = 0) l   by induction hypothesis
      <=> EVERY (\x. x = 0) (h::l)         by EVERY_DEF
*)
val MAX_LIST_EQ_0 = store_thm(
  "MAX_LIST_EQ_0",
  ``!l. (MAX_LIST l = 0) <=> EVERY (\x. x = 0) l``,
  Induct >>
  rw[MAX_EQ_0]);

(* Theorem: l <> [] ==> MEM (MAX_LIST l) l *)
(* Proof:
   By induction on l.
   Base: [] <> [] ==> MEM (MAX_LIST []) []
      Trivially true by [] <> [] = F.
   Step: l <> [] ==> MEM (MAX_LIST l) l ==>
         !h. h::l <> [] ==> MEM (MAX_LIST (h::l)) (h::l)
      If l = [],
         Note MAX_LIST [h] = h         by MAX_LIST_SING
          and MEM h [h]                by MEM
         Hence true.
      If l <> [],
         Let x = MAX_LIST (h::l)
               = MAX h (MAX_LIST l)    by MAX_LIST_CONS
         ==> x = h \/ x = MAX_LIST l   by MAX_CASES
         If x = h, MEM x (h::l)        by MEM
         If x = MAX_LIST l, MEM x l    by induction hypothesis
*)
val MAX_LIST_MEM = store_thm(
  "MAX_LIST_MEM",
  ``!l. l <> [] ==> MEM (MAX_LIST l) l``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[] >>
  rw[] >>
  metis_tac[MAX_CASES]);

(* Theorem: MEM x l ==> x <= MAX_LIST l *)
(* Proof:
   By induction on l.
   Base: !x. MEM x [] ==> x <= MAX_LIST []
     Trivially true since MEM x [] = F             by MEM
   Step: !x. MEM x l ==> x <= MAX_LIST l ==> !h x. MEM x (h::l) ==> x <= MAX_LIST (h::l)
     Note MEM x (h::l) means (x = h) \/ MEM x l    by MEM
      and MAX_LIST (h::l) = MAX h (MAX_LIST l)     by MAX_LIST_CONS
     If x = h, x <= MAX h (MAX_LIST l)             by MAX_LE
     If MEM x l, x <= MAX_LIST l                   by induction hypothesis
     or          x <= MAX h (MAX_LIST l)           by MAX_LE, LESS_EQ_TRANS
*)
val MAX_LIST_PROPERTY = store_thm(
  "MAX_LIST_PROPERTY",
  ``!l x. MEM x l ==> x <= MAX_LIST l``,
  Induct >-
  rw[] >>
  rw[MAX_LIST_CONS] >-
  decide_tac >>
  rw[]);

(* Theorem: l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> y <= x) ==> (x = MAX_LIST l) *)
(* Proof:
   Let m = MAX_LIST l.
   Since MEM x l /\ x <= m     by MAX_LIST_PROPERTY
     and MEM m l ==> m <= x    by MAX_LIST_MEM, implication, l <> []
   Hence x = m                 by EQ_LESS_EQ
*)
val MAX_LIST_TEST = store_thm(
  "MAX_LIST_TEST",
  ``!l. l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> y <= x) ==> (x = MAX_LIST l)``,
  metis_tac[MAX_LIST_MEM, MAX_LIST_PROPERTY, EQ_LESS_EQ]);

(* Theorem: MAX_LIST t <= MAX_LIST (h::t) *)
(* Proof:
   Note MAX_LIST (h::t) = MAX h (MAX_LIST t)   by MAX_LIST_def
    and MAX_LIST t <= MAX h (MAX_LIST t)       by MAX_IS_MAX
   Thus MAX_LIST t <= MAX_LIST (h::t)
*)
val MAX_LIST_LE = store_thm(
  "MAX_LIST_LE",
  ``!h t. MAX_LIST t <= MAX_LIST (h::t)``,
  rw_tac std_ss[MAX_LIST_def]);

(* Theorem: (!x y. x <= y ==> f x <= f y) ==>
           !ls. ls <> [] ==> (MAX_LIST (MAP f ls) = f (MAX_LIST ls)) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] ==> MAX_LIST (MAP f []) = f (MAX_LIST [])
      True by [] <> [] = F.
   Step: ls <> [] ==> MAX_LIST (MAP f ls) = f (MAX_LIST ls) ==>
         !h. h::ls <> [] ==> MAX_LIST (MAP f (h::ls)) = f (MAX_LIST (h::ls))
      If ls = [],
         MAX_LIST (MAP f [h])
       = MAX_LIST [f h]             by MAP
       = f h                        by MAX_LIST_def
       = f (MAX_LIST [h])           by MAX_LIST_def
      If ls <> [],
         MAX_LIST (MAP f (h::ls))
       = MAX_LIST (f h::MAP f ls)        by MAP
       = MAX (f h) MAX_LIST (MAP f ls)   by MAX_LIST_def
       = MAX (f h) (f (MAX_LIST ls))     by induction hypothesis
       = f (MAX h (MAX_LIST ls))         by MAX_SWAP
       = f (MAX_LIST (h::ls))            by MAX_LIST_def
*)
val MAX_LIST_MONO_MAP = store_thm(
  "MAX_LIST_MONO_MAP",
  ``!f. (!x y. x <= y ==> f x <= f y) ==>
   !ls. ls <> [] ==> (MAX_LIST (MAP f ls) = f (MAX_LIST ls))``,
  rpt strip_tac >>
  Induct_on `ls` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  rw[MAX_SWAP]);

(* ------------------------------------------------------------------------- *)
(* Minimum of a List                                                         *)
(* ------------------------------------------------------------------------- *)

(* Define MIN of a list *)
val MIN_LIST_def = Define`
    MIN_LIST (h::t) = if t = [] then h else MIN h (MIN_LIST t)
`;

(* Theorem: MIN_LIST [x] = x *)
(* Proof: by MIN_LIST_def *)
val MIN_LIST_SING = store_thm(
  "MIN_LIST_SING",
  ``!x. MIN_LIST [x] = x``,
  rw[MIN_LIST_def]);

(* Theorem: t <> [] ==> (MIN_LIST (h::t) = MIN h (MIN_LIST t)) *)
(* Proof: by MIN_LIST_def *)
val MIN_LIST_CONS = store_thm(
  "MIN_LIST_CONS",
  ``!h t. t <> [] ==> (MIN_LIST (h::t) = MIN h (MIN_LIST t))``,
  rw[MIN_LIST_def]);

(* export simple results *)
val _ = export_rewrites["MIN_LIST_SING", "MIN_LIST_CONS"];

(* Theorem: l <> [] ==> MEM (MIN_LIST l) l *)
(* Proof:
   By induction on l.
   Base: [] <> [] ==> MEM (MIN_LIST []) []
      Trivially true by [] <> [] = F.
   Step: l <> [] ==> MEM (MIN_LIST l) l ==>
         !h. h::l <> [] ==> MEM (MIN_LIST (h::l)) (h::l)
      If l = [],
         Note MIN_LIST [h] = h         by MIN_LIST_SING
          and MEM h [h]                by MEM
         Hence true.
      If l <> [],
         Let x = MIN_LIST (h::l)
               = MIN h (MIN_LIST l)    by MIN_LIST_CONS
         ==> x = h \/ x = MIN_LIST l   by MIN_CASES
         If x = h, MEM x (h::l)        by MEM
         If x = MIN_LIST l, MEM x l    by induction hypothesis
*)
val MIN_LIST_MEM = store_thm(
  "MIN_LIST_MEM",
  ``!l. l <> [] ==> MEM (MIN_LIST l) l``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[] >>
  rw[] >>
  metis_tac[MIN_CASES]);

(* Theorem: l <> [] ==> !x. MEM x l ==> (MIN_LIST l) <= x *)
(* Proof:
   By induction on l.
   Base: [] <> [] ==> ...
     Trivially true since [] <> [] = F
   Step: l <> [] ==> !x. MEM x l ==> MIN_LIST l <= x ==>
         !h. h::l <> [] ==> !x. MEM x (h::l) ==> MIN_LIST (h::l) <= x
     Note MEM x (h::l) means (x = h) \/ MEM x l    by MEM
     If l = [],
        MEM x [h] means x = h                      by MEM
        and MIN_LIST [h] = h, hence true           by MIN_LIST_SING
     If l <> [],
        MIN_LIST (h::l) = MIN h (MIN_LIST l)       by MIN_LIST_CONS
        If x = h, MIN h (MIN_LIST l) <= x          by MIN_LE
        If MEM x l, MIN_LIST l <= x                by induction hypothesis
        or          MIN h (MIN_LIST l) <= x        by MIN_LE, LESS_EQ_TRANS
*)
val MIN_LIST_PROPERTY = store_thm(
  "MIN_LIST_PROPERTY",
  ``!l. l <> [] ==> !x. MEM x l ==> (MIN_LIST l) <= x``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l = []` >-
  fs[MIN_LIST_SING, MEM] >>
  fs[MIN_LIST_CONS, MEM]);

(* Theorem: l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> x <= y) ==> (x = MIN_LIST l) *)
(* Proof:
   Let m = MIN_LIST l.
   Since MEM x l /\ m <= x     by MIN_LIST_PROPERTY
     and MEM m l ==> x <= m    by MIN_LIST_MEM, implication, l <> []
   Hence x = m                 by EQ_LESS_EQ
*)
val MIN_LIST_TEST = store_thm(
  "MIN_LIST_TEST",
  ``!l. l <> [] ==> !x. MEM x l /\ (!y. MEM y l ==> x <= y) ==> (x = MIN_LIST l)``,
  metis_tac[MIN_LIST_MEM, MIN_LIST_PROPERTY, EQ_LESS_EQ]);

(* Theorem: l <> [] ==> MIN_LIST l <= MAX_LIST l *)
(* Proof:
   Since MEM (MIN_LIST l) l          by MIN_LIST_MEM
      so MIN_LIST l <= MAX_LIST l    by MAX_LIST_PROPERTY
*)
val MIN_LIST_LE_MAX_LIST = store_thm(
  "MIN_LIST_LE_MAX_LIST",
  ``!l. l <> [] ==> MIN_LIST l <= MAX_LIST l``,
  rw[MIN_LIST_MEM, MAX_LIST_PROPERTY]);

(* Theorem: t <> [] ==> MIN_LIST (h::t) <= MIN_LIST t *)
(* Proof:
   Note MIN_LIST (h::t) = MIN h (MIN_LIST t)   by MIN_LIST_def, t <> []
    and MIN h (MIN_LIST t) <= MIN_LIST t       by MIN_IS_MIN
   Thus MIN_LIST (h::t) <= MIN_LIST t
*)
val MIN_LIST_LE = store_thm(
  "MIN_LIST_LE",
  ``!h t. t <> [] ==> MIN_LIST (h::t) <= MIN_LIST t``,
  rw_tac std_ss[MIN_LIST_def]);

(* Theorem: (!x y. x <= y ==> f x <= f y) ==>
           !ls. ls <> [] ==> (MIN_LIST (MAP f ls) = f (MIN_LIST ls)) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] ==> MIN_LIST (MAP f []) = f (MIN_LIST [])
      True by [] <> [] = F.
   Step: ls <> [] ==> MIN_LIST (MAP f ls) = f (MIN_LIST ls) ==>
         !h. h::ls <> [] ==> MIN_LIST (MAP f (h::ls)) = f (MIN_LIST (h::ls))
      If ls = [],
         MIN_LIST (MAP f [h])
       = MIN_LIST [f h]             by MAP
       = f h                        by MIN_LIST_def
       = f (MIN_LIST [h])           by MIN_LIST_def
      If ls <> [],
         MIN_LIST (MAP f (h::ls))
       = MIN_LIST (f h::MAP f ls)        by MAP
       = MIN (f h) MIN_LIST (MAP f ls)   by MIN_LIST_def
       = MIN (f h) (f (MIN_LIST ls))     by induction hypothesis
       = f (MIN h (MIN_LIST ls))         by MIN_SWAP
       = f (MIN_LIST (h::ls))            by MIN_LIST_def
*)
val MIN_LIST_MONO_MAP = store_thm(
  "MIN_LIST_MONO_MAP",
  ``!f. (!x y. x <= y ==> f x <= f y) ==>
   !ls. ls <> [] ==> (MIN_LIST (MAP f ls) = f (MIN_LIST ls))``,
  rpt strip_tac >>
  Induct_on `ls` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  rw[MIN_SWAP]);

(* ------------------------------------------------------------------------- *)
(* List Nub and Set                                                          *)
(* ------------------------------------------------------------------------- *)

(* Note:
> nub_def;
|- (nub [] = []) /\ !x l. nub (x::l) = if MEM x l then nub l else x::nub l
*)

(* Theorem: nub [] = [] *)
(* Proof: by nub_def *)
val nub_nil = save_thm("nub_nil", nub_def |> CONJUNCT1);
(* val nub_nil = |- nub [] = []: thm *)

(* Theorem: nub (x::l) = if MEM x l then nub l else x::nub l *)
(* Proof: by nub_def *)
val nub_cons = save_thm("nub_cons", nub_def |> CONJUNCT2);
(* val nub_cons = |- !x l. nub (x::l) = if MEM x l then nub l else x::nub l: thm *)

(* Theorem: nub [x] = [x] *)
(* Proof:
     nub [x]
   = nub (x::[])   by notation
   = x :: nub []   by nub_cons, MEM x [] = F
   = x ::[]        by nub_nil
   = [x]           by notation
*)
val nub_sing = store_thm(
  "nub_sing",
  ``!x. nub [x] = [x]``,
  rw[nub_def]);

(* Theorem: ALL_DISTINCT (nub l) *)
(* Proof:
   By induction on l.
   Base: ALL_DISTINCT (nub [])
         ALL_DISTINCT (nub [])
     <=> ALL_DISTINCT []               by nub_nil
     <=> T                             by ALL_DISTINCT
   Step: ALL_DISTINCT (nub l) ==> !h. ALL_DISTINCT (nub (h::l))
     If MEM h l,
        Then nub (h::l) = nub l        by nub_cons
        Thus ALL_DISTINCT (nub l)      by induction hypothesis
         ==> ALL_DISTINCT (nub (h::l))
     If ~(MEM h l),
        Then nub (h::l) = h:nub l      by nub_cons
        With ALL_DISTINCT (nub l)      by induction hypothesis
         ==> ALL_DISTINCT (h::nub l)   by ALL_DISTINCT, ~(MEM h l)
          or ALL_DISTINCT (nub (h::l))
*)
val nub_all_distinct = store_thm(
  "nub_all_distinct",
  ``!l. ALL_DISTINCT (nub l)``,
  Induct >-
  rw[nub_nil] >>
  rw[nub_cons]);

(* Theorem: CARD (set l) = LENGTH (nub l) *)
(* Proof:
   Note set (nub l) = set l    by nub_set
    and ALL_DISTINCT (nub l)   by nub_all_distinct
        CARD (set l)
      = CARD (set (nub l))     by above
      = LENGTH (nub l)         by ALL_DISTINCT_CARD_LIST_TO_SET, ALL_DISTINCT (nub l)
*)
val CARD_LIST_TO_SET_EQ = store_thm(
  "CARD_LIST_TO_SET_EQ",
  ``!l. CARD (set l) = LENGTH (nub l)``,
  rpt strip_tac >>
  `set (nub l) = set l` by rw[nub_set] >>
  `ALL_DISTINCT (nub l)` by rw[nub_all_distinct] >>
  rw[GSYM ALL_DISTINCT_CARD_LIST_TO_SET]);

(* Theorem: set [x] = {x} *)
(* Proof:
     set [x]
   = x INSERT set []              by LIST_TO_SET
   = x INSERT {}                  by LIST_TO_SET
   = {x}                          by INSERT_DEF
*)
val MONO_LIST_TO_SET = store_thm(
  "MONO_LIST_TO_SET",
  ``!x. set [x] = {x}``,
  rw[]);

(* Theorem: ALL_DISTINCT l /\ (set l = {x}) <=> (l = [x]) *)
(* Proof:
   If part: ALL_DISTINCT l /\ set l = {x} ==> l = [x]
      Note set l = {x}
       ==> l <> [] /\ EVERY ($= x) l   by LIST_TO_SET_EQ_SING
      Let P = (S= x).
      Note l <> [] ==> ?h t. l = h::t  by list_CASES
        so h = x /\ EVERY P t             by EVERY_DEF
       and ~(MEM h t) /\ ALL_DISTINCT t   by ALL_DISTINCT
      By contradiction, suppose l <> [x].
      Then t <> [] ==> ?u v. t = u::v     by list_CASES
       and MEM u t                        by MEM
       but u = h                          by EVERY_DEF
       ==> MEM h t, which contradicts ~(MEM h t).

   Only-if part: l = [x] ==> ALL_DISTINCT l /\ set l = {x}
       Note ALL_DISTINCT [x] = T     by ALL_DISTINCT_SING
        and set [x] = {x}            by MONO_LIST_TO_SET
*)
val DISTINCT_LIST_TO_SET_EQ_SING = store_thm(
  "DISTINCT_LIST_TO_SET_EQ_SING",
  ``!l x. ALL_DISTINCT l /\ (set l = {x}) <=> (l = [x])``,
  rw[EQ_IMP_THM] >>
  qabbrev_tac `P = ($= x)` >>
  `!y. P y ==> (y = x)` by rw[Abbr`P`] >>
  `l <> [] /\ EVERY P l` by metis_tac[LIST_TO_SET_EQ_SING, Abbr`P`] >>
  `?h t. l = h::t` by metis_tac[list_CASES] >>
  `(h = x) /\ (EVERY P t)` by metis_tac[EVERY_DEF] >>
  `~(MEM h t) /\ ALL_DISTINCT t` by metis_tac[ALL_DISTINCT] >>
  spose_not_then strip_assume_tac >>
  `t <> []` by rw[] >>
  `?u v. t = u::v` by metis_tac[list_CASES] >>
  `MEM u t` by rw[] >>
  metis_tac[EVERY_DEF]);

(* Theorem: ~(MEM h l1) /\ (set (h::l1) = set l2) ==>
            ?p1 p2. ~(MEM h p1) /\ ~(MEM h p2) /\ (nub l2 = p1 ++ [h] ++ p2) /\ (set l1 = set (p1 ++ p2)) *)
(* Proof:
   Note MEM h (h::l1)          by MEM
     or h IN set (h::l1)       by notation
     so h IN set l2            by given
     or h IN set (nub l2)      by nub_set
     so MEM h (nub l2)         by notation
     or ?p1 p2. nub l2 = p1 ++ [h] ++ h2
     and  ~(MEM h p1) /\ ~(MEM h p2)           by MEM_SPLIT_APPEND_distinct
   Remaining goal: set l1 = set (p1 ++ p2)

   Step 1: show set l1 SUBSET set (p1 ++ p2)
       Let x IN set l1.
       Then MEM x l1 ==> MEM x (h::l1)   by MEM
         so x IN set (h::l1)
         or x IN set l2                  by given
         or x IN set (nub l2)            by nub_set
         or MEM x (nub l2)               by notation
        But h <> x  since MEM x l1 but ~MEM h l1
         so MEM x (p1 ++ p2)             by MEM, MEM_APPEND
         or x IN set (p1 ++ p2)          by notation
        Thus l1 SUBSET set (p1 ++ p2)    by SUBSET_DEF

   Step 2: show set (p1 ++ p2) SUBSET set l1
       Let x IN set (p1 ++ p2)
        or MEM x (p1 ++ p2)              by notation
        so MEM x (nub l2)                by MEM, MEM_APPEND
        or x IN set (nub l2)             by notation
       ==> x IN set l2                   by nub_set
        or x IN set (h::l1)              by given
        or MEM x (h::l1)                 by notation
       But x <> h                        by MEM_APPEND, MEM x (p1 ++ p2) but ~(MEM h p1) /\ ~(MEM h p2)
       ==> MEM x l1                      by MEM
        or x IN set l1                   by notation
      Thus set (p1 ++ p2) SUBSET set l1  by SUBSET_DEF

  Thus set l1 = set (p1 ++ p2)           by SUBSET_ANTISYM
*)
val LIST_TO_SET_REDUCTION = store_thm(
  "LIST_TO_SET_REDUCTION",
  ``!l1 l2 h. ~(MEM h l1) /\ (set (h::l1) = set l2) ==>
   ?p1 p2. ~(MEM h p1) /\ ~(MEM h p2) /\ (nub l2 = p1 ++ [h] ++ p2) /\ (set l1 = set (p1 ++ p2))``,
  rpt strip_tac >>
  `MEM h (nub l2)` by metis_tac[MEM, nub_set] >>
  qabbrev_tac `l = nub l2` >>
  `?n. n < LENGTH l /\ (h = EL n l)` by rw[GSYM MEM_EL] >>
  `ALL_DISTINCT l` by rw[nub_all_distinct, Abbr`l`] >>
  `?p1 p2. (l = p1 ++ [h] ++ p2) /\ ~MEM h p1 /\ ~MEM h p2` by rw[GSYM MEM_SPLIT_APPEND_distinct] >>
  qexists_tac `p1` >>
  qexists_tac `p2` >>
  rpt strip_tac >-
  rw[] >>
  `set l1 SUBSET set (p1 ++ p2) /\ set (p1 ++ p2) SUBSET set l1` suffices_by metis_tac[SUBSET_ANTISYM] >>
  rewrite_tac[SUBSET_DEF] >>
  rpt strip_tac >-
  metis_tac[MEM_APPEND, MEM, nub_set] >>
  metis_tac[MEM_APPEND, MEM, nub_set]);

(* ------------------------------------------------------------------------- *)
(* List Padding                                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: PAD_LEFT c n [] = GENLIST (K c) n *)
(* Proof: by PAD_LEFT *)
val PAD_LEFT_NIL = store_thm(
  "PAD_LEFT_NIL",
  ``!n c. PAD_LEFT c n [] = GENLIST (K c) n``,
  rw[PAD_LEFT]);

(* Theorem: PAD_RIGHT c n [] = GENLIST (K c) n *)
(* Proof: by PAD_RIGHT *)
val PAD_RIGHT_NIL = store_thm(
  "PAD_RIGHT_NIL",
  ``!n c. PAD_RIGHT c n [] = GENLIST (K c) n``,
  rw[PAD_RIGHT]);

(* Theorem: LENGTH (PAD_LEFT c n s) = MAX n (LENGTH s) *)
(* Proof:
     LENGTH (PAD_LEFT c n s)
   = LENGTH (GENLIST (K c) (n - LENGTH s) ++ s)           by PAD_LEFT
   = LENGTH (GENLIST (K c) (n - LENGTH s)) + LENGTH s     by LENGTH_APPEND
   = n - LENGTH s + LENGTH s                              by LENGTH_GENLIST
   = MAX n (LENGTH s)                                     by MAX_DEF
*)
val PAD_LEFT_LENGTH = store_thm(
  "PAD_LEFT_LENGTH",
  ``!n c s. LENGTH (PAD_LEFT c n s) = MAX n (LENGTH s)``,
  rw[PAD_LEFT, MAX_DEF]);

(* Theorem: LENGTH (PAD_RIGHT c n s) = MAX n (LENGTH s) *)
(* Proof:
     LENGTH (PAD_LEFT c n s)
   = LENGTH (s ++ GENLIST (K c) (n - LENGTH s))           by PAD_RIGHT
   = LENGTH s + LENGTH (GENLIST (K c) (n - LENGTH s))     by LENGTH_APPEND
   = LENGTH s + (n - LENGTH s)                            by LENGTH_GENLIST
   = MAX n (LENGTH s)                                     by MAX_DEF
*)
val PAD_RIGHT_LENGTH = store_thm(
  "PAD_RIGHT_LENGTH",
  ``!n c s. LENGTH (PAD_RIGHT c n s) = MAX n (LENGTH s)``,
  rw[PAD_RIGHT, MAX_DEF]);

(* Theorem: n <= LENGTH l ==> (PAD_LEFT c n l = l) *)
(* Proof:
   Note n - LENGTH l = 0       by n <= LENGTH l
     PAD_LEFT c (LENGTH l) l
   = GENLIST (K c) 0 ++ l      by PAD_LEFT
   = [] ++ l                   by GENLIST
   = l                         by APPEND
*)
val PAD_LEFT_ID = store_thm(
  "PAD_LEFT_ID",
  ``!l c n. n <= LENGTH l ==> (PAD_LEFT c n l = l)``,
  rpt strip_tac >>
  `n - LENGTH l = 0` by decide_tac >>
  rw[PAD_LEFT]);

(* Theorem: n <= LENGTH l ==> (PAD_RIGHT c n l = l) *)
(* Proof:
   Note n - LENGTH l = 0       by n <= LENGTH l
     PAD_RIGHT c (LENGTH l) l
   = ll ++ GENLIST (K c) 0     by PAD_RIGHT
   = [] ++ l                   by GENLIST
   = l                         by APPEND_NIL
*)
val PAD_RIGHT_ID = store_thm(
  "PAD_RIGHT_ID",
  ``!l c n. n <= LENGTH l ==> (PAD_RIGHT c n l = l)``,
  rpt strip_tac >>
  `n - LENGTH l = 0` by decide_tac >>
  rw[PAD_RIGHT]);

(* Theorem: PAD_LEFT c 0 l = l *)
(* Proof: by PAD_LEFT_ID *)
val PAD_LEFT_0 = store_thm(
  "PAD_LEFT_0",
  ``!l c. PAD_LEFT c 0 l = l``,
  rw_tac std_ss[PAD_LEFT_ID]);

(* Theorem: PAD_RIGHT c 0 l = l *)
(* Proof: by PAD_RIGHT_ID *)
val PAD_RIGHT_0 = store_thm(
  "PAD_RIGHT_0",
  ``!l c. PAD_RIGHT c 0 l = l``,
  rw_tac std_ss[PAD_RIGHT_ID]);

(* Theorem: LENGTH l <= n ==> !c. PAD_LEFT c (SUC n) l = c:: PAD_LEFT c n l *)
(* Proof:
     PAD_LEFT c (SUC n) l
   = GENLIST (K c) (SUC n - LENGTH l) ++ l         by PAD_LEFT
   = GENLIST (K c) (SUC (n - LENGTH l)) ++ l       by LENGTH l <= n
   = SNOC c (GENLIST (K c) (n - LENGTH l)) ++ l    by GENLIST
   = (GENLIST (K c) (n - LENGTH l)) ++ [c] ++ l    by SNOC_APPEND
   = [c] ++ (GENLIST (K c) (n - LENGTH l)) ++ l    by GENLIST_K_APPEND_K
   = [c] ++ ((GENLIST (K c) (n - LENGTH l)) ++ l)  by APPEND_ASSOC
   = [c] ++ PAD_LEFT c n l                         by PAD_LEFT
   = c :: PAD_LEFT c n l                           by CONS_APPEND
*)
val PAD_LEFT_CONS = store_thm(
  "PAD_LEFT_CONS",
  ``!l n. LENGTH l <= n ==> !c. PAD_LEFT c (SUC n) l = c:: PAD_LEFT c n l``,
  rpt strip_tac >>
  qabbrev_tac `m = LENGTH l` >>
  `SUC n - m = SUC (n - m)` by decide_tac >>
  `PAD_LEFT c (SUC n) l = GENLIST (K c) (SUC n - m) ++ l` by rw[PAD_LEFT, Abbr`m`] >>
  `_ = SNOC c (GENLIST (K c) (n - m)) ++ l` by rw[GENLIST] >>
  `_ = (GENLIST (K c) (n - m)) ++ [c] ++ l` by rw[SNOC_APPEND] >>
  `_ = [c] ++ (GENLIST (K c) (n - m)) ++ l` by rw[GENLIST_K_APPEND_K] >>
  `_ = [c] ++ ((GENLIST (K c) (n - m)) ++ l)` by rw[APPEND_ASSOC] >>
  `_ = [c] ++ PAD_LEFT c n l` by rw[PAD_LEFT] >>
  `_ = c :: PAD_LEFT c n l` by rw[] >>
  rw[]);

(* Theorem: LENGTH l <= n ==> !c. PAD_RIGHT c (SUC n) l = SNOC c (PAD_RIGHT c n l) *)
(* Proof:
     PAD_RIGHT c (SUC n) l
   = l ++ GENLIST (K c) (SUC n - LENGTH l)         by PAD_RIGHT
   = l ++ GENLIST (K c) (SUC (n - LENGTH l))       by LENGTH l <= n
   = l ++ SNOC c (GENLIST (K c) (n - LENGTH l))    by GENLIST
   = SNOC c (l ++ (GENLIST (K c) (n - LENGTH l)))  by APPEND_SNOC
   = SNOC c (PAD_RIGHT c n l)                      by PAD_RIGHT
*)
val PAD_RIGHT_SNOC = store_thm(
  "PAD_RIGHT_SNOC",
  ``!l n. LENGTH l <= n ==> !c. PAD_RIGHT c (SUC n) l = SNOC c (PAD_RIGHT c n l)``,
  rpt strip_tac >>
  qabbrev_tac `m = LENGTH l` >>
  `SUC n - m = SUC (n - m)` by decide_tac >>
  rw[PAD_RIGHT, GENLIST, APPEND_SNOC]);

(* Theorem: h :: PAD_RIGHT c n t = PAD_RIGHT c (SUC n) (h::t) *)
(* Proof:
     h :: PAD_RIGHT c n t
   = h :: (t ++ GENLIST (K c) (n - LENGTH t))          by PAD_RIGHT
   = (h::t) ++ GENLIST (K c) (n - LENGTH t)            by APPEND
   = (h::t) ++ GENLIST (K c) (SUC n - LENGTH (h::t))   by LENGTH
   = PAD_RIGHT c (SUC n) (h::t)                        by PAD_RIGHT
*)
val PAD_RIGHT_CONS = store_thm(
  "PAD_RIGHT_CONS",
  ``!h t c n. h :: PAD_RIGHT c n t = PAD_RIGHT c (SUC n) (h::t)``,
  rw[PAD_RIGHT]);

(* Theorem: l <> [] ==> (LAST (PAD_LEFT c n l) = LAST l) *)
(* Proof:
   Note ?h t. l = h::t     by list_CASES
     LAST (PAD_LEFT c n l)
   = LAST (GENLIST (K c) (n - LENGTH (h::t)) ++ (h::t))   by PAD_LEFT
   = LAST (h::t)           by LAST_APPEND_CONS
   = LAST l                by notation
*)
val PAD_LEFT_LAST = store_thm(
  "PAD_LEFT_LAST",
  ``!l c n. l <> [] ==> (LAST (PAD_LEFT c n l) = LAST l)``,
  rpt strip_tac >>
  `?h t. l = h::t` by metis_tac[list_CASES] >>
  rw[PAD_LEFT, LAST_APPEND_CONS]);

(* Theorem: (PAD_LEFT c n l = []) <=> ((l = []) /\ (n = 0)) *)
(* Proof:
       PAD_LEFT c n l = []
   <=> GENLIST (K c) (n - LENGTH l) ++ l = []        by PAD_LEFT
   <=> GENLIST (K c) (n - LENGTH l) = [] /\ l = []   by APPEND_eq_NIL
   <=> GENLIST (K c) n = [] /\ l = []                by LENGTH l = 0
   <=> n = 0 /\ l = []                               by GENLIST_EQ_NIL
*)
val PAD_LEFT_EQ_NIL = store_thm(
  "PAD_LEFT_EQ_NIL",
  ``!l c n. (PAD_LEFT c n l = []) <=> ((l = []) /\ (n = 0))``,
  rw[PAD_LEFT, EQ_IMP_THM] >>
  fs[GENLIST_EQ_NIL]);

(* Theorem: (PAD_RIGHT c n l = []) <=> ((l = []) /\ (n = 0)) *)
(* Proof:
       PAD_RIGHT c n l = []
   <=> l ++ GENLIST (K c) (n - LENGTH l) = []        by PAD_RIGHT
   <=> l = [] /\ GENLIST (K c) (n - LENGTH l) = []   by APPEND_eq_NIL
   <=> l = [] /\ GENLIST (K c) n = []                by LENGTH l = 0
   <=> l = [] /\ n = 0                               by GENLIST_EQ_NIL
*)
val PAD_RIGHT_EQ_NIL = store_thm(
  "PAD_RIGHT_EQ_NIL",
  ``!l c n. (PAD_RIGHT c n l = []) <=> ((l = []) /\ (n = 0))``,
  rw[PAD_RIGHT, EQ_IMP_THM] >>
  fs[GENLIST_EQ_NIL]);

(* Theorem: 0 < n ==> (PAD_LEFT c n [] = PAD_LEFT c n [c]) *)
(* Proof:
      PAD_LEFT c n []
    = GENLIST (K c) n          by PAD_LEFT, APPEND_NIL
    = GENLIST (K c) (SUC k)    by n = SUC k, 0 < n
    = SNOC c (GENLIST (K c) k) by GENLIST, (K c) k = c
    = GENLIST (K c) k ++ [c]   by SNOC_APPEND
    = PAD_LEFT c n [c]         by PAD_LEFT
*)
val PAD_LEFT_NIL_EQ = store_thm(
  "PAD_LEFT_NIL_EQ",
  ``!n c. 0 < n ==> (PAD_LEFT c n [] = PAD_LEFT c n [c])``,
  rw[PAD_LEFT] >>
  `SUC (n - 1) = n` by decide_tac >>
  qabbrev_tac `f = (K c):num -> 'a` >>
  `f (n - 1) = c` by rw[Abbr`f`] >>
  metis_tac[SNOC_APPEND, GENLIST]);

(* Theorem: 0 < n ==> (PAD_RIGHT c n [] = PAD_RIGHT c n [c]) *)
(* Proof:
      PAD_RIGHT c n []
    = GENLIST (K c) n                by PAD_RIGHT
    = GENLIST (K c) (SUC (n - 1))    by 0 < n
    = c :: GENLIST (K c) (n - 1)     by GENLIST_K_CONS
    = [c] ++ GENLIST (K c) (n - 1)   by CONS_APPEND
    = PAD_RIGHT c (SUC (n - 1)) [c]  by PAD_RIGHT
    = PAD_RIGHT c n [c]              by 0 < n
*)
val PAD_RIGHT_NIL_EQ = store_thm(
  "PAD_RIGHT_NIL_EQ",
  ``!n c. 0 < n ==> (PAD_RIGHT c n [] = PAD_RIGHT c n [c])``,
  rw[PAD_RIGHT] >>
  `SUC (n - 1) = n` by decide_tac >>
  metis_tac[GENLIST_K_CONS]);

(* Theorem: PAD_RIGHT c n ls = ls ++ PAD_RIGHT c (n - LENGTH ls) [] *)
(* Proof:
     PAD_RIGHT c n ls
   = ls ++ GENLIST (K c) (n - LENGTH ls)                by PAD_RIGHT
   = ls ++ ([] ++ GENLIST (K c) ((n - LENGTH ls) - 0)   by APPEND_NIL, LENGTH
   = ls ++ PAD_RIGHT c (n - LENGTH ls) []               by PAD_RIGHT
*)
val PAD_RIGHT_BY_RIGHT = store_thm(
  "PAD_RIGHT_BY_RIGHT",
  ``!ls c n. PAD_RIGHT c n ls = ls ++ PAD_RIGHT c (n - LENGTH ls) []``,
  rw[PAD_RIGHT]);

(* Theorem: PAD_RIGHT c n ls = ls ++ PAD_LEFT c (n - LENGTH ls) [] *)
(* Proof:
     PAD_RIGHT c n ls
   = ls ++ GENLIST (K c) (n - LENGTH ls)                by PAD_RIGHT
   = ls ++ (GENLIST (K c) ((n - LENGTH ls) - 0) ++ [])  by APPEND_NIL, LENGTH
   = ls ++ PAD_LEFT c (n - LENGTH ls) []               by PAD_LEFT
*)
val PAD_RIGHT_BY_LEFT = store_thm(
  "PAD_RIGHT_BY_LEFT",
  ``!ls c n. PAD_RIGHT c n ls = ls ++ PAD_LEFT c (n - LENGTH ls) []``,
  rw[PAD_RIGHT, PAD_LEFT]);

(* Theorem: PAD_LEFT c n ls = (PAD_RIGHT c (n - LENGTH ls) []) ++ ls *)
(* Proof:
     PAD_LEFT c n ls
   = GENLIST (K c) (n - LENGTH ls) ++ ls               by PAD_LEFT
   = ([] ++ GENLIST (K c) ((n - LENGTH ls) - 0) ++ ls  by APPEND_NIL, LENGTH
   = (PAD_RIGHT c (n - LENGTH ls) []) ++ ls            by PAD_RIGHT
*)
val PAD_LEFT_BY_RIGHT = store_thm(
  "PAD_LEFT_BY_RIGHT",
  ``!ls c n. PAD_LEFT c n ls = (PAD_RIGHT c (n - LENGTH ls) []) ++ ls``,
  rw[PAD_RIGHT, PAD_LEFT]);

(* Theorem: PAD_LEFT c n ls = (PAD_LEFT c (n - LENGTH ls) []) ++ ls *)
(* Proof:
     PAD_LEFT c n ls
   = GENLIST (K c) (n - LENGTH ls) ++ ls                 by PAD_LEFT
   = ((GENLIST (K c) ((n - LENGTH ls) - 0) ++ []) ++ ls  by APPEND_NIL, LENGTH
   = (PAD_LEFT c (n - LENGTH ls) []) ++ ls               by PAD_LEFT
*)
val PAD_LEFT_BY_LEFT = store_thm(
  "PAD_LEFT_BY_LEFT",
  ``!ls c n. PAD_LEFT c n ls = (PAD_LEFT c (n - LENGTH ls) []) ++ ls``,
  rw[PAD_LEFT]);

(* ------------------------------------------------------------------------- *)
(* PROD for List, similar to SUM for List                                    *)
(* ------------------------------------------------------------------------- *)

(* Overload a positive list *)
val _ = overload_on("POSITIVE", ``\l. !x. MEM x l ==> 0 < x``);
val _ = overload_on("EVERY_POSITIVE", ``\l. EVERY (\k. 0 < k) l``);

(* Theorem: EVERY_POSITIVE ls <=> POSITIVE ls *)
(* Proof: by EVERY_MEM *)
val POSITIVE_THM = store_thm(
  "POSITIVE_THM",
  ``!ls. EVERY_POSITIVE ls <=> POSITIVE ls``,
  rw[EVERY_MEM]);

(* Note: For product of a number list, any zero element will make the product 0. *)

(* Define PROD, similar to SUM *)
val PROD = new_recursive_definition
      {name = "PROD",
       rec_axiom = list_Axiom,
       def = ``(PROD [] = 1) /\
          (!h t. PROD (h::t) = h * PROD t)``};

(* export simple definition *)
val _ = export_rewrites["PROD"];

(* Extract theorems from definition *)
val PROD_NIL = save_thm("PROD_NIL", PROD |> CONJUNCT1);
(* val PROD_NIL = |- PROD [] = 1: thm *)

val PROD_CONS = save_thm("PROD_CONS", PROD |> CONJUNCT2);
(* val PROD_CONS = |- !h t. PROD (h::t) = h * PROD t: thm *)

(* Theorem: PROD [n] = n *)
(* Proof: by PROD *)
val PROD_SING = store_thm(
  "PROD_SING",
  ``!n. PROD [n] = n``,
  rw[]);

(* Theorem: PROD ls = if ls = [] then 1 else (HD ls) * PROD (TL ls) *)
(* Proof: by PROD *)
val PROD_eval = store_thm(
  "PROD_eval[compute]", (* put in computeLib *)
  ``!ls. PROD ls = if ls = [] then 1 else (HD ls) * PROD (TL ls)``,
  metis_tac[PROD, list_CASES, HD, TL]);

(* enable PROD computation -- use [compute] above. *)
(* val _ = computeLib.add_persistent_funs ["PROD_eval"]; *)

(* Theorem: (PROD ls = 1) = !x. MEM x ls ==> (x = 1) *)
(* Proof:
   By induction on ls.
   Base: (PROD [] = 1) <=> !x. MEM x [] ==> (x = 1)
      LHS: PROD [] = 1 is true          by PROD
      RHS: is true since MEM x [] = F   by MEM
   Step: (PROD ls = 1) <=> !x. MEM x ls ==> (x = 1) ==>
         !h. (PROD (h::ls) = 1) <=> !x. MEM x (h::ls) ==> (x = 1)
      Note 1 = PROD (h::ls)                     by given
             = h * PROD ls                      by PROD
      Thus h = 1 /\ PROD ls = 1                 by MULT_EQ_1
        or h = 1 /\ !x. MEM x ls ==> (x = 1)    by induction hypothesis
        or !x. MEM x (h::ls) ==> (x = 1)        by MEM
*)
val PROD_eq_1 = store_thm(
  "PROD_eq_1",
  ``!ls. (PROD ls = 1) = !x. MEM x ls ==> (x = 1)``,
  Induct >>
  rw[] >>
  metis_tac[]);

(* Theorem: PROD (SNOC x l) = (PROD l) * x *)
(* Proof:
   By induction on l.
   Base: PROD (SNOC x []) = PROD [] * x
        PROD (SNOC x [])
      = PROD [x]                by SNOC
      = x                       by PROD
      = 1 * x                   by MULT_LEFT_1
      = PROD [] * x             by PROD
   Step: PROD (SNOC x l) = PROD l * x ==> !h. PROD (SNOC x (h::l)) = PROD (h::l) * x
        PROD (SNOC x (h::l))
      = PROD (h:: SNOC x l)     by SNOC
      = h * PROD (SNOC x l)     by PROD
      = h * (PROD l * x)        by induction hypothesis
      = (h * PROD l) * x        by MULT_ASSOC
      = PROD (h::l) * x         by PROD
*)
val PROD_SNOC = store_thm(
  "PROD_SNOC",
  ``!x l. PROD (SNOC x l) = (PROD l) * x``,
  strip_tac >>
  Induct >>
  rw[]);

(* Theorem: PROD (APPEND l1 l2) = PROD l1 * PROD l2 *)
(* Proof:
   By induction on l1.
   Base: PROD ([] ++ l2) = PROD [] * PROD l2
         PROD ([] ++ l2)
       = PROD l2                   by APPEND
       = 1 * PROD l2               by MULT_LEFT_1
       = PROD [] * PROD l2         by PROD
   Step: !l2. PROD (l1 ++ l2) = PROD l1 * PROD l2 ==> !h l2. PROD (h::l1 ++ l2) = PROD (h::l1) * PROD l2
         PROD (h::l1 ++ l2)
       = PROD (h::(l1 ++ l2))      by APPEND
       = h * PROD (l1 ++ l2)       by PROD
       = h * (PROD l1 * PROD l2)   by induction hypothesis
       = (h * PROD l1) * PROD l2   by MULT_ASSOC
       = PROD (h::l1) * PROD l2    by PROD
*)
val PROD_APPEND = store_thm(
  "PROD_APPEND",
  ``!l1 l2. PROD (APPEND l1 l2) = PROD l1 * PROD l2``,
  Induct >> rw[]);

(* Theorem: PROD (MAP f ls) = FOLDL (\a e. a * f e) 1 ls *)
(* Proof:
   By SNOC_INDUCT |- !P. P [] /\ (!l. P l ==> !x. P (SNOC x l)) ==> !l. P l
   Base: PROD (MAP f []) = FOLDL (\a e. a * f e) 1 []
         PROD (MAP f [])
       = PROD []                     by MAP
       = 1                           by PROD
       = FOLDL (\a e. a * f e) 1 []  by FOLDL
   Step: !f. PROD (MAP f ls) = FOLDL (\a e. a * f e) 1 ls ==>
         PROD (MAP f (SNOC x ls)) = FOLDL (\a e. a * f e) 1 (SNOC x ls)
         PROD (MAP f (SNOC x ls))
       = PROD (SNOC (f x) (MAP f ls))                      by MAP_SNOC
       = PROD (MAP f ls) * (f x)                           by PROD_SNOC
       = (FOLDL (\a e. a * f e) 1 ls) * (f x)              by induction hypothesis
       = (\a e. a * f e) (FOLDL (\a e. a * f e) 1 ls) x    by function application
       = FOLDL (\a e. a * f e) 1 (SNOC x ls)               by FOLDL_SNOC
*)
val PROD_MAP_FOLDL = store_thm(
  "PROD_MAP_FOLDL",
  ``!ls f. PROD (MAP f ls) = FOLDL (\a e. a * f e) 1 ls``,
  HO_MATCH_MP_TAC SNOC_INDUCT >>
  rpt strip_tac >-
  rw[] >>
  rw[MAP_SNOC, PROD_SNOC, FOLDL_SNOC]);

(* Theorem: FINITE s ==> !f. PI f s = PROD (MAP f (SET_TO_LIST s)) *)
(* Proof:
     PI f s
   = ITSET (\e acc. f e * acc) s 1                            by PROD_IMAGE_DEF
   = FOLDL (combin$C (\e acc. f e * acc)) 1 (SET_TO_LIST s)   by ITSET_eq_FOLDL_SET_TO_LIST, FINITE s
   = FOLDL (\a e. a * f e) 1 (SET_TO_LIST s)                  by FUN_EQ_THM
   = PROD (MAP f (SET_TO_LIST s))                             by PROD_MAP_FOLDL
*)
val PROD_IMAGE_eq_PROD_MAP_SET_TO_LIST = store_thm(
  "PROD_IMAGE_eq_PROD_MAP_SET_TO_LIST",
  ``!s. FINITE s ==> !f. PI f s = PROD (MAP f (SET_TO_LIST s))``,
  rw[PROD_IMAGE_DEF] >>
  rw[ITSET_eq_FOLDL_SET_TO_LIST, PROD_MAP_FOLDL] >>
  rpt AP_THM_TAC >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM]);

(* Define PROD using accumulator *)
val PROD_ACC_DEF = Lib.with_flag (Defn.def_suffix, "_DEF") Define
  `(PROD_ACC [] acc = acc) /\
   (PROD_ACC (h::t) acc = PROD_ACC t (h * acc))`;

(* Theorem: PROD_ACC L n = PROD L * n *)
(* Proof:
   By induction on L.
   Base: !n. PROD_ACC [] n = PROD [] * n
        PROD_ACC [] n
      = n                 by PROD_ACC_DEF
      = 1 * n             by MULT_LEFT_1
      = PROD [] * n       by PROD
   Step: !n. PROD_ACC L n = PROD L * n ==> !h n. PROD_ACC (h::L) n = PROD (h::L) * n
        PROD_ACC (h::L) n
      = PROD_ACC L (h * n)   by PROD_ACC_DEF
      = PROD L * (h * n)     by induction hypothesis
      = (PROD L * h) * n     by MULT_ASSOC
      = (h * PROD L) * n     by MULT_COMM
      = PROD (h::L) * n      by PROD
*)
val PROD_ACC_PROD_LEM = store_thm(
  "PROD_ACC_PROD_LEM",
  ``!L n. PROD_ACC L n = PROD L * n``,
  Induct >>
  rw[PROD_ACC_DEF]);
(* proof SUM_ACC_SUM_LEM *)
val PROD_ACC_PROD_LEM = store_thm
("PROD_ACC_SUM_LEM",
 ``!L n. PROD_ACC L n = PROD L * n``,
 Induct THEN RW_TAC arith_ss [PROD_ACC_DEF, PROD]);

(* Theorem: PROD L = PROD_ACC L 1 *)
(* Proof: Put n = 1 in PROD_ACC_PROD_LEM *)
Theorem PROD_PROD_ACC[compute]:
  !L. PROD L = PROD_ACC L 1
Proof
  rw[PROD_ACC_PROD_LEM]
QED

(* EVAL ``PROD [1; 2; 3; 4]``; --> 24 *)

(* Theorem: PROD (GENLIST (K m) n) = m ** n *)
(* Proof:
   By induction on n.
   Base: PROD (GENLIST (K m) 0) = m ** 0
        PROD (GENLIST (K m) 0)
      = PROD []                by GENLIST
      = 1                      by PROD
      = m ** 0                 by EXP
   Step: PROD (GENLIST (K m) n) = m ** n ==> PROD (GENLIST (K m) (SUC n)) = m ** SUC n
        PROD (GENLIST (K m) (SUC n))
      = PROD (SNOC m (GENLIST (K m) n))    by GENLIST
      = PROD (GENLIST (K m) n) * m         by PROD_SNOC
      = m ** n * m                         by induction hypothesis
      = m * m ** n                         by MULT_COMM
      = m * SUC n                          by EXP
*)
val PROD_GENLIST_K = store_thm(
  "PROD_GENLIST_K",
  ``!m n. PROD (GENLIST (K m) n) = m ** n``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[GENLIST, PROD_SNOC, EXP]);

(* Same as PROD_GENLIST_K, formulated slightly different. *)

(* Theorem: PPROD (GENLIST (\j. x) n) = x ** n *)
(* Proof:
   Note (\j. x) = K x             by FUN_EQ_THM
        PROD (GENLIST (\j. x) n)
      = PROD (GENLIST (K x) n)    by GENLIST_FUN_EQ
      = x ** n                    by PROD_GENLIST_K
*)
val PROD_CONSTANT = store_thm(
  "PROD_CONSTANT",
  ``!n x. PROD (GENLIST (\j. x) n) = x ** n``,
  rpt strip_tac >>
  `(\j. x) = K x` by rw[FUN_EQ_THM] >>
  metis_tac[PROD_GENLIST_K, GENLIST_FUN_EQ]);

(* Theorem: (PROD l = 0) <=> MEM 0 l *)
(* Proof:
   By induction on l.
   Base: (PROD [] = 0) <=> MEM 0 []
      LHS = F    by PROD_NIL, 1 <> 0
      RHS = F    by MEM
   Step: (PROD l = 0) <=> MEM 0 l ==> !h. (PROD (h::l) = 0) <=> MEM 0 (h::l)
      Note PROD (h::l) = h * PROD l     by PROD_CONS
      Thus PROD (h::l) = 0
       ==> h = 0 \/ PROD l = 0          by MULT_EQ_0
      If h = 0, then MEM 0 (h::l)       by MEM
      If PROD l = 0, then MEM 0 l       by induction hypothesis
                       or MEM 0 (h::l)  by MEM
*)
val PROD_EQ_0 = store_thm(
  "PROD_EQ_0",
  ``!l. (PROD l = 0) <=> MEM 0 l``,
  Induct >-
  rw[] >>
  metis_tac[PROD_CONS, MULT_EQ_0, MEM]);

(* Theorem: EVERY (\x. 0 < x) l ==> 0 < PROD l *)
(* Proof:
   By contradiction, suppose PROD l = 0.
   Then MEM 0 l              by PROD_EQ_0
     or 0 < 0 = F            by EVERY_MEM
*)
val PROD_POS = store_thm(
  "PROD_POS",
  ``!l. EVERY (\x. 0 < x) l ==> 0 < PROD l``,
  metis_tac[EVERY_MEM, PROD_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: POSITIVE l ==> 0 < PROD l *)
(* Proof: PROD_POS, EVERY_MEM *)
val PROD_POS_ALT = store_thm(
  "PROD_POS_ALT",
  ``!l. POSITIVE l ==> 0 < PROD l``,
  rw[PROD_POS, EVERY_MEM]);

(* Theorem: PROD (GENLIST (\j. n ** 2 ** j) m) = n ** (2 ** m - 1) *)
(* Proof:
   The computation is:
       n * (n ** 2) * (n ** 4) * ... * (n ** (2 ** (m - 1)))
     = n ** (1 + 2 + 4 + ... + 2 ** (m - 1))
     = n ** (2 ** m - 1)

   By induction on m.
   Base: PROD (GENLIST (\j. n ** 2 ** j) 0) = n ** (2 ** 0 - 1)
      LHS = PROD (GENLIST (\j. n ** 2 ** j) 0)
          = PROD []                by GENLIST_0
          = 1                      by PROD
      RHS = n ** (1 - 1)           by EXP_0
          = n ** 0 = 1 = LHS       by EXP_0
   Step: PROD (GENLIST (\j. n ** 2 ** j) m) = n ** (2 ** m - 1) ==>
         PROD (GENLIST (\j. n ** 2 ** j) (SUC m)) = n ** (2 ** SUC m - 1)
         PROD (GENLIST (\j. n ** 2 ** j) (SUC m))
       = PROD (SNOC (n ** 2 ** m) (GENLIST (\j. n ** 2 ** j) m))   by GENLIST
       = PROD (GENLIST (\j. n ** 2 ** j) m) * (n ** 2 ** m)        by PROD_SNOC
       = n ** (2 ** m - 1) * n ** 2 ** m                           by induction hypothesis
       = n ** (2 ** m - 1 + 2 ** m)                                by EXP_ADD
       = n ** (2 * 2 ** m - 1)                                     by arithmetic
       = n ** (2 ** SUC m - 1)                                     by EXP
*)
val PROD_SQUARING_LIST = store_thm(
  "PROD_SQUARING_LIST",
  ``!m n. PROD (GENLIST (\j. n ** 2 ** j) m) = n ** (2 ** m - 1)``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[] >>
  qabbrev_tac `f = \j. n ** 2 ** j` >>
  `PROD (GENLIST f (SUC m)) = PROD (SNOC (n ** 2 ** m) (GENLIST f m))` by rw[GENLIST, Abbr`f`] >>
  `_ = PROD (GENLIST f m) * (n ** 2 ** m)` by rw[PROD_SNOC] >>
  `_ = n ** (2 ** m - 1) * n ** 2 ** m` by rw[] >>
  `_ = n ** (2 ** m - 1 + 2 ** m)` by rw[EXP_ADD] >>
  rw[EXP]);

(* ------------------------------------------------------------------------- *)
(* Range Conjunction and Disjunction                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: a <= j /\ j <= a <=> (j = a) *)
(* Proof: trivial by arithmetic. *)
val every_range_sing = store_thm(
  "every_range_sing",
  ``!a j. a <= j /\ j <= a <=> (j = a)``,
  decide_tac);

(* Theorem: a <= b ==>
    ((!j. a <= j /\ j <= b ==> f j) <=> (f a /\ !j. a + 1 <= j /\ j <= b ==> f j)) *)
(* Proof:
   If part: !j. a <= j /\ j <= b ==> f j ==>
              f a /\ !j. a + 1 <= j /\ j <= b ==> f j
      This is trivial since a + 1 = SUC a.
   Only-if part: f a /\ !j. a + 1 <= j /\ j <= b ==> f j ==>
                 !j. a <= j /\ j <= b ==> f j
      Note a <= j <=> a = j or a < j      by arithmetic
      If a = j, this is trivial.
      If a < j, then a + 1 <= j, also trivial.
*)
val every_range_cons = store_thm(
  "every_range_cons",
  ``!f a b. a <= b ==>
    ((!j. a <= j /\ j <= b ==> f j) <=> (f a /\ !j. a + 1 <= j /\ j <= b ==> f j))``,
  rw[EQ_IMP_THM] >>
  `(a = j) \/ (a < j)` by decide_tac >-
  fs[] >>
  fs[]);

(* Theorem: a <= b ==> ((!j. PRE a <= j /\ j <= b ==> f j) <=> (f (PRE a) /\ !j. a <= j /\ j <= b ==> f j)) *)
(* Proof:
       !j. PRE a <= j /\ j <= b ==> f j
   <=> !j. (PRE a = j \/ a <= j) /\ j <= b ==> f j             by arithmetic
   <=> !j. (j = PRE a ==> f j) /\ a <= j /\ j <= b ==> f j     by RIGHT_AND_OVER_OR, DISJ_IMP_THM
   <=> !j. a <= j /\ j <= b ==> f j /\ f (PRE a)
*)
Theorem every_range_split_head:
  !f a b. a <= b ==>
          ((!j. PRE a <= j /\ j <= b ==> f j) <=> (f (PRE a) /\ !j. a <= j /\ j <= b ==> f j))
Proof
  rpt strip_tac >>
  `!j. PRE a <= j <=> PRE a = j \/ a <= j` by decide_tac >>
  metis_tac[]
QED

(* Theorem: a <= b ==> ((!j. a <= j /\ j <= SUC b ==> f j) <=> (f (SUC b) /\ !j. a <= j /\ j <= b ==> f j)) *)
(* Proof:
       !j. a <= j /\ j <= SUC b ==> f j
   <=> !j. a <= j /\ (j <= b \/ j = SUC b) ==> f j             by arithmetic
   <=> !j. a <= j /\ j <= b ==> f j /\ (j = SUC b ==> f j)     by LEFT_AND_OVER_OR, DISJ_IMP_THM
   <=> !j. a <= j /\ j <= b ==> f j /\ f (SUC b)
*)
Theorem every_range_split_last:
  !f a b. a <= b ==>
          ((!j. a <= j /\ j <= SUC b ==> f j) <=> (f (SUC b) /\ !j. a <= j /\ j <= b ==> f j))
Proof
  rpt strip_tac >>
  `!j. j <= SUC b <=> j <= b \/ j = SUC b` by decide_tac >>
  metis_tac[]
QED

(* Theorem: a <= b ==> ((!j. a <= j /\ j <= b ==> f j) <=> (f a /\ f b /\ !j. a < j /\ j < b ==> f j)) *)
(* Proof:
       !j. a <= j /\ j <= b ==> f j
   <=> !j. (a < j \/ a = j) /\ (j < b \/ j = b) ==> f j                  by arithmetic
   <=> !j. a = j ==> f j /\ j = b ==> f j /\ !j. a < j /\ j < b ==> f j  by LEFT_AND_OVER_OR, DISJ_IMP_THM
   <=> f a /\ f b /\ !j. a < j /\ j < b ==> f j
*)
Theorem every_range_less_ends:
  !f a b. a <= b ==>
          ((!j. a <= j /\ j <= b ==> f j) <=> (f a /\ f b /\ !j. a < j /\ j < b ==> f j))
Proof
  rpt strip_tac >>
  `!m n. m <= n <=> m < n \/ m = n` by decide_tac >>
  metis_tac[]
QED

(* Theorem: a < b /\ f a /\ ~f b ==>
            ?m. a <= m /\ m < b /\ (!j. a <= j /\ j <= m ==> f j) /\ ~f (SUC m) *)
(* Proof:
   Let s = {p | a <= p /\ p < b /\ (!j. a <= j /\ j <= p ==> f j)}
   Pick m = MAX_SET s.
   Note f a ==> a IN s             by every_range_sing
     so s <> {}                    by MEMBER_NOT_EMPTY
   Also s SUBSET (count b)         by SUBSET_DEF
     so FINITE s                   by FINITE_COUNT, SUBSET_FINITE
    ==> m IN s                     by MAX_SET_IN_SET
   Thus a <= m /\ m < b /\ (!j. a <= j /\ j <= m ==> f j)
   It remains to show: ~f (SUC m).
   By contradiction, suppose f (SUC m).
   Since m < b, SUC m <= b.
   But ~f b, so SUC m <> b         by given
   Thus a <= m < SUC m, and SUC m < b,
    and !j. a <= j /\ j <= SUC m ==> f j)
    ==> SUC m IN s                 by every_range_split_last
   Then SUC m <= m                 by X_LE_MAX_SET
   which is impossible             by LESS_SUC
*)
Theorem every_range_span_max:
  !f a b. a < b /\ f a /\ ~f b ==>
          ?m. a <= m /\ m < b /\ (!j. a <= j /\ j <= m ==> f j) /\ ~f (SUC m)
Proof
  rpt strip_tac >>
  qabbrev_tac `s = {p | a <= p /\ p < b /\ (!j. a <= j /\ j <= p ==> f j)}` >>
  qabbrev_tac `m = MAX_SET s` >>
  qexists_tac `m` >>
  `a IN s` by fs[every_range_sing, Abbr`s`] >>
  `s SUBSET (count b)` by fs[SUBSET_DEF, Abbr`s`] >>
  `FINITE s /\ s <> {}` by metis_tac[FINITE_COUNT, SUBSET_FINITE, MEMBER_NOT_EMPTY] >>
  `m IN s` by fs[MAX_SET_IN_SET, Abbr`m`] >>
  rfs[Abbr`s`] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `s = {p | a <= p /\ p < b /\ (!j. a <= j /\ j <= p ==> f j)}` >>
  `SUC m <> b` by metis_tac[] >>
  `a <= SUC m /\ SUC m < b` by decide_tac >>
  `SUC m IN s` by fs[every_range_split_last, Abbr`s`] >>
  `SUC m <= m` by simp[X_LE_MAX_SET, Abbr`m`] >>
  decide_tac
QED

(* Theorem: a < b /\ ~f a /\ f b ==>
           ?m. a < m /\ m <= b /\ (!j. m <= j /\ j <= b ==> f j) /\ ~f (PRE m) *)
(* Proof:
   Let s = {p | a < p /\ p <= b /\ (!j. p <= j /\ j <= b ==> f j)}
   Pick m = MIN_SET s.
   Note f b ==> b IN s             by every_range_sing
     so s <> {}                    by MEMBER_NOT_EMPTY
    ==> m IN s                     by MIN_SET_IN_SET
   Thus a < m /\ m <= b /\ (!j. m <= j /\ j <= b ==> f j)
   It remains to show: ~f (PRE m).
   By contradiction, suppose f (PRE m).
   Since a < m, a <= PRE m.
   But ~f a, so PRE m <> a         by given
   Thus a < PRE m, and PRE m <= b,
    and !j. PRE m <= j /\ j <= b ==> f j)
    ==> PRE m IN s                 by every_range_split_head
   Then m <= PRE m                 by MIN_SET_PROPERTY
   which is impossible             by PRE_LESS, a < m ==> 0 < m
*)
Theorem every_range_span_min:
  !f a b. a < b /\ ~f a /\ f b ==>
          ?m. a < m /\ m <= b /\ (!j. m <= j /\ j <= b ==> f j) /\ ~f (PRE m)
Proof
  rpt strip_tac >>
  qabbrev_tac `s = {p | a < p /\ p <= b /\ (!j. p <= j /\ j <= b ==> f j)}` >>
  qabbrev_tac `m = MIN_SET s` >>
  qexists_tac `m` >>
  `b IN s` by fs[every_range_sing, Abbr`s`] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `m IN s` by fs[MIN_SET_IN_SET, Abbr`m`] >>
  rfs[Abbr`s`] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `s = {p | a < p /\ p <= b /\ (!j. p <= j /\ j <= b ==> f j)}` >>
  `PRE m <> a` by metis_tac[] >>
  `a < PRE m /\ PRE m <= b` by decide_tac >>
  `PRE m IN s` by fs[every_range_split_head, Abbr`s`] >>
  `m <= PRE m` by simp[MIN_SET_PROPERTY, Abbr`m`] >>
  decide_tac
QED

(* Theorem: ?j. a <= j /\ j <= a <=> (j = a) *)
(* Proof: trivial by arithmetic. *)
val exists_range_sing = store_thm(
  "exists_range_sing",
  ``!a. ?j. a <= j /\ j <= a <=> (j = a)``,
  metis_tac[LESS_EQ_REFL]);

(* Theorem: a <= b ==>
    ((?j. a <= j /\ j <= b /\ f j) <=> (f a \/ ?j. a + 1 <= j /\ j <= b /\ f j)) *)
(* Proof:
   If part: ?j. a <= j /\ j <= b /\ f j ==>
              f a \/ ?j. a + 1 <= j /\ j <= b /\ f j
      This is trivial since a + 1 = SUC a.
   Only-if part: f a /\ ?j. a + 1 <= j /\ j <= b /\ f j ==>
                 ?j. a <= j /\ j <= b /\ f j
      Note a <= j <=> a = j or a < j      by arithmetic
      If a = j, this is trivial.
      If a < j, then a + 1 <= j, also trivial.
*)
val exists_range_cons = store_thm(
  "exists_range_cons",
  ``!f a b. a <= b ==>
    ((?j. a <= j /\ j <= b /\ f j) <=> (f a \/ ?j. a + 1 <= j /\ j <= b /\ f j))``,
  rw[EQ_IMP_THM] >| [
    `(a = j) \/ (a < j)` by decide_tac >-
    fs[] >>
    `a + 1 <= j` by decide_tac >>
    metis_tac[],
    metis_tac[LESS_EQ_REFL],
    `a <= j` by decide_tac >>
    metis_tac[]
  ]);

(* ------------------------------------------------------------------------- *)
(* List Range                                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [m .. n] = [m ..< SUC n] *)
(* Proof:
   = [m .. n]
   = GENLIST (\i. m + i) (n + 1 - m)     by listRangeINC_def
   = [m ..< (n + 1)]                     by listRangeLHI_def
   = [m ..< SUC n]                       by ADD1
*)
Theorem listRangeINC_to_LHI:
  !m n. [m .. n] = [m ..< SUC n]
Proof
  rw[listRangeLHI_def, listRangeINC_def, ADD1]
QED

(* Theorem: set [1 .. n] = IMAGE SUC (count n) *)
(* Proof:
       x IN set [1 .. n]
   <=> 1 <= x /\ x <= n                  by listRangeINC_MEM
   <=> 0 < x /\ PRE x < n                by arithmetic
   <=> 0 < SUC (PRE x) /\ PRE x < n      by SUC_PRE, 0 < x
   <=> x IN IMAGE SUC (count n)          by IN_COUNT, IN_IMAGE
*)
Theorem listRangeINC_SET:
  !n. set [1 .. n] = IMAGE SUC (count n)
Proof
  rw[EXTENSION, EQ_IMP_THM] >>
  `0 < x /\ PRE x < n` by decide_tac >>
  metis_tac[SUC_PRE]
QED

(* Theorem: LENGTH [m .. n] = n + 1 - m *)
(* Proof:
     LENGTH [m .. n]
   = LENGTH (GENLIST (\i. m + i) (n + 1 - m))  by listRangeINC_def
   = n + 1 - m                                 by LENGTH_GENLIST
*)
val listRangeINC_LEN = store_thm(
  "listRangeINC_LEN",
  ``!m n. LENGTH [m .. n] = n + 1 - m``,
  rw[listRangeINC_def]);

(* Theorem: ([m .. n] = []) <=> (n + 1 <= m) *)
(* Proof:
              [m .. n] = []
   <=> LENGTH [m .. n] = 0         by LENGTH_NIL
   <=>       n + 1 - m = 0         by listRangeINC_LEN
   <=>          n + 1 <= m         by arithmetic
*)
val listRangeINC_NIL = store_thm(
  "listRangeINC_NIL",
  ``!m n. ([m .. n] = []) <=> (n + 1 <= m)``,
  metis_tac[listRangeINC_LEN, LENGTH_NIL, DECIDE``(n + 1 - m = 0) <=> (n + 1 <= m)``]);

(* Rename a theorem *)
val listRangeINC_MEM = save_thm("listRangeINC_MEM",
    MEM_listRangeINC |> GEN ``x:num`` |> GEN ``n:num`` |> GEN ``m:num``);
(*
val listRangeINC_MEM = |- !m n x. MEM x [m .. n] <=> m <= x /\ x <= n: thm
*)

(*
EL_listRangeLHI
|- lo + i < hi ==> EL i [lo ..< hi] = lo + i
*)

(* Theorem: m + i <= n ==> (EL i [m .. n] = m + i) *)
(* Proof: by listRangeINC_def *)
val listRangeINC_EL = store_thm(
  "listRangeINC_EL",
  ``!m n i. m + i <= n ==> (EL i [m .. n] = m + i)``,
  rw[listRangeINC_def]);

(* Theorem: EVERY P [m .. n] <=> !x. m <= x /\ x <= n ==> P x *)
(* Proof:
       EVERY P [m .. n]
   <=> !x. MEM x [m .. n] ==> P x      by EVERY_MEM
   <=> !x. m <= x /\ x <= n ==> P x    by MEM_listRangeINC
*)
val listRangeINC_EVERY = store_thm(
  "listRangeINC_EVERY",
  ``!P m n. EVERY P [m .. n] <=> !x. m <= x /\ x <= n ==> P x``,
  rw[EVERY_MEM, MEM_listRangeINC]);

(* Theorem: EXISTS P [m .. n] <=> ?x. m <= x /\ x <= n /\ P x *)
(* Proof:
       EXISTS P [m .. n]
   <=> ?x. MEM x [m .. n] /\ P x      by EXISTS_MEM
   <=> ?x. m <= x /\ x <= n /\ P e    by MEM_listRangeINC
*)
val listRangeINC_EXISTS = store_thm(
  "listRangeINC_EXISTS",
  ``!P m n. EXISTS P [m .. n] <=> ?x. m <= x /\ x <= n /\ P x``,
  metis_tac[EXISTS_MEM, MEM_listRangeINC]);

(* Theorem: EVERY P [m .. n] <=> ~(EXISTS ($~ o P) [m .. n]) *)
(* Proof:
       EVERY P [m .. n]
   <=> !x. m <= x /\ x <= n ==> P x        by listRangeINC_EVERY
   <=> ~(?x. m <= x /\ x <= n /\ ~(P x))   by negation
   <=> ~(EXISTS ($~ o P) [m .. m])         by listRangeINC_EXISTS
*)
val listRangeINC_EVERY_EXISTS = store_thm(
  "listRangeINC_EVERY_EXISTS",
  ``!P m n. EVERY P [m .. n] <=> ~(EXISTS ($~ o P) [m .. n])``,
  rw[listRangeINC_EVERY, listRangeINC_EXISTS]);

(* Theorem: EXISTS P [m .. n] <=> ~(EVERY ($~ o P) [m .. n]) *)
(* Proof:
       EXISTS P [m .. n]
   <=> ?x. m <= x /\ x <= m /\ P x           by listRangeINC_EXISTS
   <=> ~(!x. m <= x /\ x <= n ==> ~(P x))    by negation
   <=> ~(EVERY ($~ o P) [m .. n])            by listRangeINC_EVERY
*)
val listRangeINC_EXISTS_EVERY = store_thm(
  "listRangeINC_EXISTS_EVERY",
  ``!P m n. EXISTS P [m .. n] <=> ~(EVERY ($~ o P) [m .. n])``,
  rw[listRangeINC_EXISTS, listRangeINC_EVERY]);

(* Theorem: m <= n + 1 ==> ([m .. (n + 1)] = SNOC (n + 1) [m .. n]) *)
(* Proof:
     [m .. (n + 1)]
   = GENLIST (\i. m + i) ((n + 1) + 1 - m)                      by listRangeINC_def
   = GENLIST (\i. m + i) (1 + (n + 1 - m))                      by arithmetic
   = GENLIST (\i. m + i) (n + 1 - m) ++ GENLIST (\t. (\i. m + i) (t + n + 1 - m)) 1  by GENLIST_APPEND
   = [m .. n] ++ GENLIST (\t. (\i. m + i) (t + n + 1 - m)) 1    by listRangeINC_def
   = [m .. n] ++ [(\t. (\i. m + i) (t + n + 1 - m)) 0]          by GENLIST_1
   = [m .. n] ++ [m + n + 1 - m]                                by function evaluation
   = [m .. n] ++ [n + 1]                                        by arithmetic
   = SNOC (n + 1) [m .. n]                                      by SNOC_APPEND
*)
val listRangeINC_SNOC = store_thm(
  "listRangeINC_SNOC",
  ``!m n. m <= n + 1 ==> ([m .. (n + 1)] = SNOC (n + 1) [m .. n])``,
  rw[listRangeINC_def] >>
  `(n + 2 - m = 1 + (n + 1 - m)) /\ (n + 1 - m + m = n + 1)` by decide_tac >>
  rw_tac std_ss[GENLIST_APPEND, GENLIST_1]);

(* Theorem: m <= n + 1 ==> (FRONT [m .. (n + 1)] = [m .. n]) *)
(* Proof:
     FRONT [m .. (n + 1)]
   = FRONT (SNOC (n + 1) [m .. n]))    by listRangeINC_SNOC
   = [m .. n]                          by FRONT_SNOC
*)
Theorem listRangeINC_FRONT:
  !m n. m <= n + 1 ==> (FRONT [m .. (n + 1)] = [m .. n])
Proof
  simp[listRangeINC_SNOC, FRONT_SNOC]
QED

(* Theorem: m <= n ==> (LAST [m .. n] = n) *)
(* Proof:
   Let ls = [m .. n]
   Note ls <> []                   by listRangeINC_NIL
     so LAST ls
      = EL (PRE (LENGTH ls)) ls    by LAST_EL
      = EL (PRE (n + 1 - m)) ls    by listRangeINC_LEN
      = EL (n - m) ls              by arithmetic
      = n                          by listRangeINC_EL
   Or
      LAST [m .. n]
    = LAST (GENLIST (\i. m + i) (n + 1 - m))   by listRangeINC_def
    = LAST (GENLIST (\i. m + i) (SUC (n - m))  by arithmetic, m <= n
    = (\i. m + i) (n - m)                      by GENLIST_LAST
    = m + (n - m)                              by function application
    = n                                        by m <= n
   Or
    If n = 0, then m <= 0 means m = 0.
      LAST [0 .. 0] = LAST [0] = 0 = n   by LAST_DEF
    Otherwise n = SUC k.
      LAST [m .. n]
    = LAST (SNOC n [m .. k])             by listRangeINC_SNOC, ADD1
    = n                                  by LAST_SNOC
*)
Theorem listRangeINC_LAST:
  !m n. m <= n ==> (LAST [m .. n] = n)
Proof
  rpt strip_tac >>
  Cases_on `n` >-
  fs[] >>
  metis_tac[listRangeINC_SNOC, LAST_SNOC, ADD1]
QED

(* Theorem: REVERSE [m .. n] = MAP (\x. n - x + m) [m .. n] *)
(* Proof:
     REVERSE [m .. n]
   = REVERSE (GENLIST (\i. m + i) (n + 1 - m))              by listRangeINC_def
   = GENLIST (\x. (\i. m + i) (PRE (n + 1 - m) - x)) (n + 1 - m)   by REVERSE_GENLIST
   = GENLIST (\x. (\i. m + i) (n - m - x)) (n + 1 - m)      by PRE
   = GENLIST (\x. (m + n - m - x) (n + 1 - m)               by function application
   = GENLIST (\x. n - x) (n + 1 - m)                        by arithmetic

     MAP (\x. n - x + m) [m .. n]
   = MAP (\x. n - x + m) (GENLIST (\i. m + i) (n + 1 - m))  by listRangeINC_def
   = GENLIST ((\x. n - x + m) o (\i. m + i)) (n + 1 - m)    by MAP_GENLIST
   = GENLIST (\i. n - (m + i) + m) (n + 1 - m)              by function composition
   = GENLIST (\i. n - i) (n + 1 - m)                        by arithmetic
*)
val listRangeINC_REVERSE = store_thm(
  "listRangeINC_REVERSE",
  ``!m n. REVERSE [m .. n] = MAP (\x. n - x + m) [m .. n]``,
  rpt strip_tac >>
  `(\m'. PRE (n + 1 - m) - m' + m) = ((\x. n - x + m) o (\i. i + m))` by rw[FUN_EQ_THM, combinTheory.o_THM] >>
  rw[listRangeINC_def, REVERSE_GENLIST, MAP_GENLIST]);

(* Theorem: REVERSE (MAP f [m .. n]) = MAP (f o (\x. n - x + m)) [m .. n] *)
(* Proof:
    REVERSE (MAP f [m .. n])
  = MAP f (REVERSE [m .. n])                by MAP_REVERSE
  = MAP f (MAP (\x. n - x + m) [m .. n])    by listRangeINC_REVERSE
  = MAP (f o (\x. n - x + m)) [m .. n]      by MAP_MAP_o
*)
val listRangeINC_REVERSE_MAP = store_thm(
  "listRangeINC_REVERSE_MAP",
  ``!f m n. REVERSE (MAP f [m .. n]) = MAP (f o (\x. n - x + m)) [m .. n]``,
  metis_tac[MAP_REVERSE, listRangeINC_REVERSE, MAP_MAP_o]);

(* Theorem: MAP f [(m + 1) .. (n + 1)] = MAP (f o SUC) [m .. n] *)
(* Proof:
   Note (\i. (m + 1) + i) = SUC o (\i. (m + i))                 by FUN_EQ_THM
     MAP f [(m + 1) .. (n + 1)]
   = MAP f (GENLIST (\i. (m + 1) + i) ((n + 1) + 1 - (m + 1)))  by listRangeINC_def
   = MAP f (GENLIST (\i. (m + 1) + i) (n + 1 - m))              by arithmetic
   = MAP f (GENLIST (SUC o (\i. (m + i))) (n + 1 - m))          by above
   = MAP (f o SUC) (GENLIST (\i. (m + i)) (n + 1 - m))          by MAP_GENLIST
   = MAP (f o SUC) [m .. n]                                     by listRangeINC_def
*)
val listRangeINC_MAP_SUC = store_thm(
  "listRangeINC_MAP_SUC",
  ``!f m n. MAP f [(m + 1) .. (n + 1)] = MAP (f o SUC) [m .. n]``,
  rpt strip_tac >>
  `(\i. (m + 1) + i) = SUC o (\i. (m + i))` by rw[FUN_EQ_THM] >>
  rw[listRangeINC_def, MAP_GENLIST]);

(* Theorem: a <= b /\ b <= c ==> ([a .. b] ++ [(b + 1) .. c] = [a .. c]) *)
(* Proof:
   By listRangeINC_def, this is to show:
      GENLIST (\i. a + i) (b + 1 - a) ++ GENLIST (\i. b + (i + 1)) (c - b) = GENLIST (\i. a + i) (c + 1 - a)
   Let f = \i. a + i.
   Note (\t. f (t + (b + 1 - a))) = (\i. b + (i + 1))     by FUN_EQ_THM
   Thus GENLIST (\i. b + (i + 1)) (c - b) = GENLIST (\t. f (t + (b + 1 - a))) (c - b)  by GENLIST_FUN_EQ
   Now (c - b) + (b + 1 - a) = c + 1 - a                   by a <= b /\ b <= c
   The result follows                                      by GENLIST_APPEND
*)
val listRangeINC_APPEND = store_thm(
  "listRangeINC_APPEND",
  ``!a b c. a <= b /\ b <= c ==> ([a .. b] ++ [(b + 1) .. c] = [a .. c])``,
  rw[listRangeINC_def] >>
  qabbrev_tac `f = \i. a + i` >>
  `(\t. f (t + (b + 1 - a))) = (\i. b + (i + 1))` by rw[FUN_EQ_THM, Abbr`f`] >>
  `GENLIST (\i. b + (i + 1)) (c - b) = GENLIST (\t. f (t + (b + 1 - a))) (c - b)` by rw[GSYM GENLIST_FUN_EQ] >>
  `(c - b) + (b + 1 - a) = c + 1 - a` by decide_tac >>
  metis_tac[GENLIST_APPEND]);

(* Theorem: SUM [m .. n] = SUM [1 .. n] - SUM [1 .. (m - 1)] *)
(* Proof:
   If m = 0,
      Then [1 .. (m-1)] = [1 .. 0] = []   by listRangeINC_EMPTY
           SUM [0 .. n]
         = SUM (0::[1 .. n])              by listRangeINC_CONS
         = 0 + SUM [1 .. n]               by SUM_CONS
         = SUM [1 .. n] - 0               by arithmetic
         = SUM [1 .. n] - SUM []          by SUM_NIL
   If m = 1,
      Then [1 .. (m-1)] = [1 .. 0] = []   by listRangeINC_EMPTY
           SUM [1 .. n]
         = SUM [1 .. n] - 0               by arithmetic
         = SUM [1 .. n] - SUM []          by SUM_NIL
   Otherwise 1 < m, or 1 <= m - 1.
   If n < m,
      Then SUM [m .. n] = 0               by listRangeINC_EMPTY
      If n = 0,
         Then SUM [1 .. 0] = 0            by listRangeINC_EMPTY
          and 0 - SUM [1 .. (m - 1)] = 0  by integer subtraction
      If n <> 0,
         Then 1 <= n /\ n <= m - 1        by arithmetic
          ==> [1 .. m - 1] =
              [1 .. n] ++ [(n + 1) .. (m - 1)]         by listRangeINC_APPEND
           or SUM [1 .. m - 1]
            = SUM [1 .. n] + SUM [(n + 1) .. (m - 1)]  by SUM_APPEND
         Thus SUM [1 .. n] - SUM [1 .. m - 1] = 0      by subtraction
   If ~(n < m), then m <= n.
      Note m - 1 < n /\ (m - 1 + 1 = m)                by arithmetic
      Thus [1 .. n] = [1 .. (m - 1)] ++ [m .. n]       by listRangeINC_APPEND
        or SUM [1 .. n]
         = SUM [1 .. (m - 1)] + SUM [m .. n]           by SUM_APPEND
      The result follows                               by subtraction
*)
val listRangeINC_SUM = store_thm(
  "listRangeINC_SUM",
  ``!m n. SUM [m .. n] = SUM [1 .. n] - SUM [1 .. (m - 1)]``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[listRangeINC_EMPTY, listRangeINC_CONS] >>
  Cases_on `m = 1` >-
  rw[listRangeINC_EMPTY] >>
  Cases_on `n < m` >| [
    Cases_on `n = 0` >-
    rw[listRangeINC_EMPTY] >>
    `1 <= n /\ n <= m - 1` by decide_tac >>
    `[1 .. m - 1] = [1 .. n] ++ [(n + 1) .. (m - 1)]` by rw[listRangeINC_APPEND] >>
    `SUM [1 .. m - 1] = SUM [1 .. n] + SUM [(n + 1) .. (m - 1)]` by rw[GSYM SUM_APPEND] >>
    `SUM [m .. n] = 0` by rw[listRangeINC_EMPTY] >>
    decide_tac,
    `1 <= m - 1 /\ m - 1 <= n /\ (m - 1 + 1 = m)` by decide_tac >>
    `[1 .. n] = [1 .. (m - 1)] ++ [m .. n]` by metis_tac[listRangeINC_APPEND] >>
    `SUM [1 .. n] = SUM [1 .. (m - 1)] + SUM [m .. n]` by rw[GSYM SUM_APPEND] >>
    decide_tac
  ]);

(* Theorem: 0 < m ==> 0 < PROD [m .. n] *)
(* Proof:
   Note MEM 0 [m .. n] = F        by MEM_listRangeINC
   Thus PROD [m .. n] <> 0        by PROD_EQ_0
   The result follows.
   or
   Note EVERY_POSITIVE [m .. n]   by listRangeINC_EVERY
   Thus 0 < PROD [m .. n]         by PROD_POS
*)
val listRangeINC_PROD_pos = store_thm(
  "listRangeINC_PROD_pos",
  ``!m n. 0 < m ==> 0 < PROD [m .. n]``,
  rw[PROD_POS, listRangeINC_EVERY]);

(* Theorem: 0 < m /\ m <= n ==> (PROD [m .. n] = PROD [1 .. n] DIV PROD [1 .. (m - 1)]) *)
(* Proof:
   If m = 1,
      Then [1 .. (m-1)] = [1 .. 0] = []   by listRangeINC_EMPTY
           PROD [1 .. n]
         = PROD [1 .. n] DIV 1            by DIV_ONE
         = PROD [1 .. n] DIV PROD []      by PROD_NIL
   If m <> 1, then 1 <= m                 by m <> 0, m <> 1
   Note 1 <= m - 1 /\ m - 1 < n /\ (m - 1 + 1 = m)            by arithmetic
   Thus [1 .. n] = [1 .. (m - 1)] ++ [m .. n]                 by listRangeINC_APPEND
     or PROD [1 .. n] = PROD [1 .. (m - 1)] * PROD [m .. n]   by PROD_POS
    Now 0 < PROD [1 .. (m - 1)]                               by listRangeINC_PROD_pos
   The result follows                                         by MULT_TO_DIV
*)
val listRangeINC_PROD = store_thm(
  "listRangeINC_PROD",
  ``!m n. 0 < m /\ m <= n ==> (PROD [m .. n] = PROD [1 .. n] DIV PROD [1 .. (m - 1)])``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[listRangeINC_EMPTY] >>
  `1 <= m - 1 /\ m - 1 <= n /\ (m - 1 + 1 = m)` by decide_tac >>
  `[1 .. n] = [1 .. (m - 1)] ++ [m .. n]` by metis_tac[listRangeINC_APPEND] >>
  `PROD [1 .. n] = PROD [1 .. (m - 1)] * PROD [m .. n]` by rw[GSYM PROD_APPEND] >>
  `0 < PROD [1 .. (m - 1)]` by rw[listRangeINC_PROD_pos] >>
  metis_tac[MULT_TO_DIV]);

(* Theorem: 0 < n /\ m <= x /\ x divides n ==> MEM x [m .. n] *)
(* Proof:
   Note x divdes n ==> x <= n     by DIVIDES_LE, 0 < n
     so MEM x [m .. n]            by listRangeINC_MEM
*)
val listRangeINC_has_divisors = store_thm(
  "listRangeINC_has_divisors",
  ``!m n x. 0 < n /\ m <= x /\ x divides n ==> MEM x [m .. n]``,
  rw[listRangeINC_MEM, DIVIDES_LE]);

(* Theorem: [1 .. n] = GENLIST SUC n *)
(* Proof: by listRangeINC_def *)
val listRangeINC_1_n = store_thm(
  "listRangeINC_1_n",
  ``!n. [1 .. n] = GENLIST SUC n``,
  rpt strip_tac >>
  `(\i. i + 1) = SUC` by rw[FUN_EQ_THM] >>
  rw[listRangeINC_def]);

(* Theorem: MAP f [1 .. n] = GENLIST (f o SUC) n *)
(* Proof:
     MAP f [1 .. n]
   = MAP f (GENLIST SUC n)     by listRangeINC_1_n
   = GENLIST (f o SUC) n       by MAP_GENLIST
*)
val listRangeINC_MAP = store_thm(
  "listRangeINC_MAP",
  ``!f n. MAP f [1 .. n] = GENLIST (f o SUC) n``,
  rw[listRangeINC_1_n, MAP_GENLIST]);

(* Theorem: SUM (MAP f [1 .. (SUC n)]) = f (SUC n) + SUM (MAP f [1 .. n]) *)
(* Proof:
      SUM (MAP f [1 .. (SUC n)])
    = SUM (MAP f (SNOC (SUC n) [1 .. n]))       by listRangeINC_SNOC
    = SUM (SNOC (f (SUC n)) (MAP f [1 .. n]))   by MAP_SNOC
    = f (SUC n) + SUM (MAP f [1 .. n])          by SUM_SNOC
*)
val listRangeINC_SUM_MAP = store_thm(
  "listRangeINC_SUM_MAP",
  ``!f n. SUM (MAP f [1 .. (SUC n)]) = f (SUC n) + SUM (MAP f [1 .. n])``,
  rw[listRangeINC_SNOC, MAP_SNOC, SUM_SNOC, ADD1]);

(* Theorem: m < j /\ j <= n ==> [m .. n] = [m .. j-1] ++ j::[j+1 .. n] *)
(* Proof:
   Note m < j implies m <= j-1.
     [m .. n]
   = [m .. j-1] ++ [j .. n]        by listRangeINC_APPEND, m <= j-1
   = [m .. j-1] ++ j::[j+1 .. n]   by listRangeINC_CONS, j <= n
*)
Theorem listRangeINC_SPLIT:
  !m n j. m < j /\ j <= n ==> [m .. n] = [m .. j-1] ++ j::[j+1 .. n]
Proof
  rpt strip_tac >>
  `m <= j - 1 /\ j - 1 <= n /\ (j - 1) + 1 = j` by decide_tac >>
  `[m .. n] = [m .. j-1] ++ [j .. n]` by metis_tac[listRangeINC_APPEND] >>
  simp[listRangeINC_CONS]
QED

(* Theorem: [m ..< (n + 1)] = [m .. n] *)
(* Proof:
     [m ..< (n + 1)]
   = GENLIST (\i. m + i) (n + 1 - m)     by listRangeLHI_def
   = [m .. n]                            by listRangeINC_def
*)
Theorem listRangeLHI_to_INC:
  !m n. [m ..< (n + 1)] = [m .. n]
Proof
  rw[listRangeLHI_def, listRangeINC_def]
QED

(* Theorem: set [0 ..< n] = count n *)
(* Proof:
       x IN set [0 ..< n]
   <=> 0 <= x /\ x < n         by listRangeLHI_MEM
   <=> x < n                   by arithmetic
   <=> x IN count n            by IN_COUNT
*)
Theorem listRangeLHI_SET:
  !n. set [0 ..< n] = count n
Proof
  simp[EXTENSION]
QED

(* Theorem alias *)
Theorem  listRangeLHI_LEN = LENGTH_listRangeLHI |> GEN_ALL |> SPEC ``m:num`` |> SPEC ``n:num`` |> GEN_ALL;
(* val listRangeLHI_LEN = |- !n m. LENGTH [m ..< n] = n - m: thm *)

(* Theorem: ([m ..< n] = []) <=> n <= m *)
(* Proof:
   If n = 0, LHS = T, RHS = T    hence true.
   If n <> 0, then n = SUC k     by num_CASES
       [m ..< n] = []
   <=> [m ..< SUC k] = []        by n = SUC k
   <=> [m .. k] = []             by listRangeLHI_to_INC
   <=> k + 1 <= m                by listRangeINC_NIL
   <=>     n <= m                by ADD1
*)
val listRangeLHI_NIL = store_thm(
  "listRangeLHI_NIL",
  ``!m n. ([m ..< n] = []) <=> n <= m``,
  rpt strip_tac >>
  Cases_on `n` >-
  rw[listRangeLHI_def] >>
  rw[listRangeLHI_to_INC, listRangeINC_NIL, ADD1]);

(* Theorem: MEM x [m ..< n] <=> m <= x /\ x < n *)
(* Proof: by MEM_listRangeLHI *)
val listRangeLHI_MEM = store_thm(
  "listRangeLHI_MEM",
  ``!m n x. MEM x [m ..< n] <=> m <= x /\ x < n``,
  rw[MEM_listRangeLHI]);

(* Theorem: m + i < n ==> EL i [m ..< n] = m + i *)
(* Proof: EL_listRangeLHI *)
val listRangeLHI_EL = store_thm(
  "listRangeLHI_EL",
  ``!m n i. m + i < n ==> (EL i [m ..< n] = m + i)``,
  rw[EL_listRangeLHI]);

(* Theorem: EVERY P [m ..< n] <=> !x. m <= x /\ x < n ==> P x *)
(* Proof:
       EVERY P [m ..< n]
   <=> !x. MEM x [m ..< n] ==> P e      by EVERY_MEM
   <=> !x. m <= x /\ x < n ==> P e    by MEM_listRangeLHI
*)
val listRangeLHI_EVERY = store_thm(
  "listRangeLHI_EVERY",
  ``!P m n. EVERY P [m ..< n] <=> !x. m <= x /\ x < n ==> P x``,
  rw[EVERY_MEM, MEM_listRangeLHI]);

(* Theorem: m <= n ==> ([m ..< n + 1] = SNOC n [m ..< n]) *)
(* Proof:
   If n = 0,
      Then m = 0               by m <= n
      LHS = [0 ..< 1] = [0]
      RHS = SNOC 0 [0 ..< 0]
          = SNOC 0 []          by listRangeLHI_def
          = [0] = LHS          by SNOC
   If n <> 0,
      Then n = (n - 1) + 1     by arithmetic
       [m ..< n + 1]
     = [m .. n]                by listRangeLHI_to_INC
     = SNOC n [m .. n - 1]     by listRangeINC_SNOC, m <= (n - 1) + 1
     = SNOC n [m ..< n]        by listRangeLHI_to_INC
*)
val listRangeLHI_SNOC = store_thm(
  "listRangeLHI_SNOC",
  ``!m n. m <= n ==> ([m ..< n + 1] = SNOC n [m ..< n])``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `m = 0` by decide_tac >>
    rw[listRangeLHI_def],
    `n = (n - 1) + 1` by decide_tac >>
    `[m ..< n + 1] = [m .. n]` by rw[listRangeLHI_to_INC] >>
    `_ = SNOC n [m .. n - 1]` by metis_tac[listRangeINC_SNOC] >>
    `_ = SNOC n [m ..< n]` by rw[GSYM listRangeLHI_to_INC] >>
    rw[]
  ]);

(* Theorem: m <= n ==> (FRONT [m .. < n + 1] = [m .. <n]) *)
(* Proof:
     FRONT [m ..< n + 1]
   = FRONT (SNOC n [m ..< n]))     by listRangeLHI_SNOC
   = [m ..< n]                     by FRONT_SNOC
*)
Theorem listRangeLHI_FRONT:
  !m n. m <= n ==> (FRONT [m ..< n + 1] = [m ..< n])
Proof
  simp[listRangeLHI_SNOC, FRONT_SNOC]
QED

(* Theorem: m <= n ==> (LAST [m ..< n + 1] = n) *)
(* Proof:
      LAST [m ..< n + 1]
    = LAST (SNOC n [m ..< n])      by listRangeLHI_SNOC
    = n                            by LAST_SNOC
*)
Theorem listRangeLHI_LAST:
  !m n. m <= n ==> (LAST [m ..< n + 1] = n)
Proof
  simp[listRangeLHI_SNOC, LAST_SNOC]
QED

(* Theorem: REVERSE [m ..< n] = MAP (\x. n - 1 - x + m) [m ..< n] *)
(* Proof:
   If n = 0,
      LHS = REVERSE []            by listRangeLHI_def
          = []                    by REVERSE_DEF
          = MAP f [] = RHS        by MAP
   If n <> 0,
      Then n = k + 1 for some k   by num_CASES, ADD1
        REVERSE [m ..< n]
      = REVERSE [m .. k]                   by listRangeLHI_to_INC
      = MAP (\x. k - x + m) [m .. k]       by listRangeINC_REVERSE
      = MAP (\x. n - 1 - x + m) [m ..< n]  by listRangeLHI_to_INC
*)
val listRangeLHI_REVERSE = store_thm(
  "listRangeLHI_REVERSE",
  ``!m n. REVERSE [m ..< n] = MAP (\x. n - 1 - x + m) [m ..< n]``,
  rpt strip_tac >>
  Cases_on `n` >-
  rw[listRangeLHI_def] >>
  `REVERSE [m ..< SUC n'] = REVERSE [m .. n']` by rw[listRangeLHI_to_INC, ADD1] >>
  `_ = MAP (\x. n' - x + m) [m .. n']` by rw[listRangeINC_REVERSE] >>
  `_ = MAP (\x. n' - x + m) [m ..< (SUC n')]` by rw[GSYM listRangeLHI_to_INC, ADD1] >>
  rw[]);

(* Theorem: REVERSE (MAP f [m ..< n]) = MAP (f o (\x. n - 1 - x + m)) [m ..< n] *)
(* Proof:
    REVERSE (MAP f [m ..< n])
  = MAP f (REVERSE [m ..< n])                    by MAP_REVERSE
  = MAP f (MAP (\x. n - 1 - x + m) [m ..< n])    by listRangeLHI_REVERSE
  = MAP (f o (\x. n - 1 - x + m)) [m ..< n]      by MAP_MAP_o
*)
val listRangeLHI_REVERSE_MAP = store_thm(
  "listRangeLHI_REVERSE_MAP",
  ``!f m n. REVERSE (MAP f [m ..< n]) = MAP (f o (\x. n - 1 - x + m)) [m ..< n]``,
  metis_tac[MAP_REVERSE, listRangeLHI_REVERSE, MAP_MAP_o]);

(* Theorem: MAP f [(m + 1) ..< (n + 1)] = MAP (f o SUC) [m ..< n] *)
(* Proof:
   Note (\i. (m + 1) + i) = SUC o (\i. (m + i))             by FUN_EQ_THM
     MAP f [(m + 1) ..< (n + 1)]
   = MAP f (GENLIST (\i. (m + 1) + i) ((n + 1) - (m + 1)))  by listRangeLHI_def
   = MAP f (GENLIST (\i. (m + 1) + i) (n - m))              by arithmetic
   = MAP f (GENLIST (SUC o (\i. (m + i))) (n - m))          by above
   = MAP (f o SUC) (GENLIST (\i. (m + i)) (n - m))          by MAP_GENLIST
   = MAP (f o SUC) [m ..< n]                                by listRangeLHI_def
*)
val listRangeLHI_MAP_SUC = store_thm(
  "listRangeLHI_MAP_SUC",
  ``!f m n. MAP f [(m + 1) ..< (n + 1)] = MAP (f o SUC) [m ..< n]``,
  rpt strip_tac >>
  `(\i. (m + 1) + i) = SUC o (\i. (m + i))` by rw[FUN_EQ_THM] >>
  rw[listRangeLHI_def, MAP_GENLIST]);


(* Theorem: a <= b /\ b <= c ==> [a ..< b] ++ [b ..< c] = [a ..< c] *)
(* Proof:
   If a = b,
       LHS = [a ..< a] ++ [a ..< c]
           = [] ++ [a ..< c]        by listRangeLHI_def
           = [a ..< c] = RHS        by APPEND
   If a <> b,
      Then a < b,                   by a <= b
        so b <> 0, and c <> 0       by b <= c
      Let b = b' + 1, c = c' + 1    by num_CASES, ADD1
      Then a <= b' /\ b' <= c.
        [a ..< b] ++ [b ..< c]
      = [a .. b'] ++ [b' + 1 .. c']   by listRangeLHI_to_INC
      = [a .. c']                     by listRangeINC_APPEND
      = [a ..< c]                     by listRangeLHI_to_INC
*)
val listRangeLHI_APPEND = store_thm(
  "listRangeLHI_APPEND",
  ``!a b c. a <= b /\ b <= c ==> ([a ..< b] ++ [b ..< c] = [a ..< c])``,
  rpt strip_tac >>
  `(a = b) \/ (a < b)` by decide_tac >-
  rw[listRangeLHI_def] >>
  `b <> 0 /\ c <> 0` by decide_tac >>
  `?b' c'. (b = b' + 1) /\ (c = c' + 1)` by metis_tac[num_CASES, ADD1] >>
  `a <= b' /\ b' <= c` by decide_tac >>
  `[a ..< b] ++ [b ..< c] = [a .. b'] ++ [b' + 1 .. c']` by rw[listRangeLHI_to_INC] >>
  `_ = [a .. c']` by rw[listRangeINC_APPEND] >>
  `_ = [a ..< c]` by rw[GSYM listRangeLHI_to_INC] >>
  rw[]);

(* Theorem: SUM [m ..< n] = SUM [1 ..< n] - SUM [1 ..< m] *)
(* Proof:
   If n = 0,
      LHS = SUM [m ..< 0] = SUM [] = 0        by listRangeLHI_EMPTY
      RHS = SUM [1 ..< 0] - SUM [1 ..< m]
          = SUM [] - SUM [1 ..< m]            by listRangeLHI_EMPTY
          = 0 - SUM [1 ..< m] = 0 = LHS       by integer subtraction
   If m = 0,
      LHS = SUM [0 ..< n]
          = SUM (0 :: [1 ..< n])              by listRangeLHI_CONS
          = 0 + SUM [1 ..< n]                 by SUM
          = SUM [1 ..< n]                     by arithmetic
      RHS = SUM [1 ..< n] - SUM [1 ..< 0]     by integer subtraction
          = SUM [1 ..< n] - SUM []            by listRangeLHI_EMPTY
          = SUM [1 ..< n] - 0                 by SUM
          = LHS
   Otherwise,
      n <> 0, and m <> 0.
      Let n = n' + 1, m = m' + 1              by num_CASES, ADD1
         SUM [m ..< n]
       = SUM [m .. n']                        by listRangeLHI_to_INC
       = SUM [1 .. n'] - SUM [1 .. m - 1]     by listRangeINC_SUM
       = SUM [1 .. n'] - SUM [1 .. m']        by m' = m - 1
       = SUM [1 ..< n] - SUM [1 ..< m]        by listRangeLHI_to_INC
*)
val listRangeLHI_SUM = store_thm(
  "listRangeLHI_SUM",
  ``!m n. SUM [m ..< n] = SUM [1 ..< n] - SUM [1 ..< m]``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[listRangeLHI_EMPTY] >>
  Cases_on `m = 0` >-
  rw[listRangeLHI_EMPTY, listRangeLHI_CONS] >>
  `?n' m'. (n = n' + 1) /\ (m = m' + 1)` by metis_tac[num_CASES, ADD1] >>
  `SUM [m ..< n] = SUM [m .. n']` by rw[listRangeLHI_to_INC] >>
  `_ = SUM [1 .. n'] - SUM [1 .. m - 1]` by rw[GSYM listRangeINC_SUM] >>
  `_ = SUM [1 .. n'] - SUM [1 .. m']` by rw[] >>
  `_ = SUM [1 ..< n] - SUM [1 ..< m]` by rw[GSYM listRangeLHI_to_INC] >>
  rw[]);

(* Theorem: 0 < m ==> 0 < PROD [m ..< n] *)
(* Proof:
   Note MEM 0 [m ..< n] = F        by MEM_listRangeLHI
   Thus PROD [m ..< n] <> 0        by PROD_EQ_0
   The result follows.
   or,
   Note EVERY_POSITIVE [m ..< n]   by listRangeLHI_EVERY
   Thus 0 < PROD [m ..< n]         by PROD_POS
*)
val listRangeLHI_PROD_pos = store_thm(
  "listRangeLHI_PROD_pos",
  ``!m n. 0 < m ==> 0 < PROD [m ..< n]``,
  rw[PROD_POS, listRangeLHI_EVERY]);

(* Theorem: 0 < m /\ m <= n ==> (PROD [m ..< n] = PROD [1 ..< n] DIV PROD [1 ..< m]) *)
(* Proof:
   Note n <> 0                    by 0 < m /\ m <= n
   Let m = m' + 1, n = n' + 1     by num_CASES, ADD1
   If m = n,
      Note 0 < PROD [1 ..< n]     by listRangeLHI_PROD_pos
      LHS = PROD [n ..< n]
          = PROD [] = 1           by listRangeLHI_EMPTY
      RHS = PROD [1 ..< n] DIV PROD [1 ..< n]
          = 1                     by DIVMOD_ID, 0 < PROD [1 ..< n]
   If m <> n,
      Then m < n, or m <= n'      by arithmetic
        PROD [m ..< n]
      = PROD [m .. n']                          by listRangeLHI_to_INC
      = PROD [1 .. n'] DIV PROD [1 .. m - 1]    by listRangeINC_PROD, m <= n'
      = PROD [1 .. n'] DIV PROD [1 .. m']       by m' = m - 1
      = PROD [1 ..< n] DIV PROD [1 ..< m]       by listRangeLHI_to_INC
*)
val listRangeLHI_PROD = store_thm(
  "listRangeLHI_PROD",
  ``!m n. 0 < m /\ m <= n ==> (PROD [m ..< n] = PROD [1 ..< n] DIV PROD [1 ..< m])``,
  rpt strip_tac >>
  `m <> 0 /\ n <> 0` by decide_tac >>
  `?n' m'. (n = n' + 1) /\ (m = m' + 1)` by metis_tac[num_CASES, ADD1] >>
  Cases_on `m = n` >| [
    `0 < PROD [1 ..< n]` by rw[listRangeLHI_PROD_pos] >>
    rfs[listRangeLHI_EMPTY, DIVMOD_ID],
    `m <= n'` by decide_tac >>
    `PROD [m ..< n] = PROD [m .. n']` by rw[listRangeLHI_to_INC] >>
    `_ = PROD [1 .. n'] DIV PROD [1 .. m - 1]` by rw[GSYM listRangeINC_PROD] >>
    `_ = PROD [1 .. n'] DIV PROD [1 .. m']` by rw[] >>
    `_ = PROD [1 ..< n] DIV PROD [1 ..< m]` by rw[GSYM listRangeLHI_to_INC] >>
    rw[]
  ]);

(* Theorem: 0 < n /\ m <= x /\ x divides n ==> MEM x [m ..< n + 1] *)
(* Proof:
   Note the condition implies:
        MEM x [m .. n]         by listRangeINC_has_divisors
      = MEM x [m ..< n + 1]    by listRangeLHI_to_INC
*)
val listRangeLHI_has_divisors = store_thm(
  "listRangeLHI_has_divisors",
  ``!m n x. 0 < n /\ m <= x /\ x divides n ==> MEM x [m ..< n + 1]``,
  metis_tac[listRangeINC_has_divisors, listRangeLHI_to_INC]);

(* Theorem: [0 ..< n] = GENLIST I n *)
(* Proof: by listRangeINC_def *)
val listRangeLHI_0_n = store_thm(
  "listRangeLHI_0_n",
  ``!n. [0 ..< n] = GENLIST I n``,
  rpt strip_tac >>
  `(\i:num. i) = I` by rw[FUN_EQ_THM] >>
  rw[listRangeLHI_def]);

(* Theorem: MAP f [0 ..< n] = GENLIST f n *)
(* Proof:
     MAP f [0 ..< n]
   = MAP f (GENLIST I n)     by listRangeLHI_0_n
   = GENLIST (f o I) n       by MAP_GENLIST
   = GENLIST f n             by I_THM
*)
val listRangeLHI_MAP = store_thm(
  "listRangeLHI_MAP",
  ``!f n. MAP f [0 ..< n] = GENLIST f n``,
  rw[listRangeLHI_0_n, MAP_GENLIST]);

(* Theorem: SUM (MAP f [0 ..< (SUC n)]) = f n + SUM (MAP f [0 ..< n]) *)
(* Proof:
      SUM (MAP f [0 ..< (SUC n)])
    = SUM (MAP f (SNOC n [0 ..< n]))       by listRangeLHI_SNOC
    = SUM (SNOC (f n) (MAP f [0 ..< n]))   by MAP_SNOC
    = f n + SUM (MAP f [0 ..< n])          by SUM_SNOC
*)
val listRangeLHI_SUM_MAP = store_thm(
  "listRangeLHI_SUM_MAP",
  ``!f n. SUM (MAP f [0 ..< (SUC n)]) = f n + SUM (MAP f [0 ..< n])``,
  rw[listRangeLHI_SNOC, MAP_SNOC, SUM_SNOC, ADD1]);

(* Theorem: m <= j /\ j < n ==> [m ..< n] = [m ..< j] ++ j::[j+1 ..< n] *)
(* Proof:
   Note j < n implies j <= n.
     [m ..< n]
   = [m ..< j] ++ [j ..< n]        by listRangeLHI_APPEND, j <= n
   = [m ..< j] ++ j::[j+1 ..< n]   by listRangeLHI_CONS, j < n
*)
Theorem listRangeLHI_SPLIT:
  !m n j. m <= j /\ j < n ==> [m ..< n] = [m ..< j] ++ j::[j+1 ..< n]
Proof
  rpt strip_tac >>
  `[m ..< n] = [m ..< j] ++ [j ..< n]` by simp[listRangeLHI_APPEND] >>
  simp[listRangeLHI_CONS]
QED

(* listRangeTheory.listRangeLHI_ALL_DISTINCT  |- ALL_DISTINCT [lo ..< hi] *)

(* Theorem: ALL_DISTINCT [m .. n] *)
(* Proof:
       ALL_DISTINCT [m .. n]
   <=> ALL_DISTINCT [m ..< n + 1]              by listRangeLHI_to_INC
   <=> T                                       by listRangeLHI_ALL_DISTINCT
*)
Theorem listRangeINC_ALL_DISTINCT:
  !m n. ALL_DISTINCT [m .. n]
Proof
  metis_tac[listRangeLHI_to_INC, listRangeLHI_ALL_DISTINCT]
QED

(* Theorem:  m <= n ==> EVERY P [m - 1 .. n] <=> (P (m - 1) /\ EVERY P [m ..n]) *)
(* Proof:
       EVERY P [m - 1 .. n]
   <=> !x. m - 1 <= x /\ x <= n ==> P x                by listRangeINC_EVERY
   <=> !x. (m - 1 = x \/ m <= x) /\ x <= n ==> P x     by arithmetic
   <=> !x. (x = m - 1 ==> P x) /\ m <= x /\ x <= n ==> P x
                                                       by RIGHT_AND_OVER_OR, DISJ_IMP_THM
   <=> P (m - 1) /\ EVERY P [m .. n]                   by listRangeINC_EVERY
*)
Theorem listRangeINC_EVERY_split_head:
  !P m n. m <= n ==> (EVERY P [m - 1 .. n] <=> P (m - 1) /\ EVERY P [m ..n])
Proof
  rw[listRangeINC_EVERY] >>
  `!x. m <= x + 1 <=> m - 1 = x \/ m <= x` by decide_tac >>
  (rw[EQ_IMP_THM] >> metis_tac[])
QED

(* Theorem: m <= n ==> (EVERY P [m .. (n + 1)] <=> P (n + 1) /\ EVERY P [m .. n]) *)
(* Proof:
       EVERY P [m .. (n + 1)]
   <=> !x. m <= x /\ x <= n + 1 ==> P x                by listRangeINC_EVERY
   <=> !x. m <= x /\ (x <= n \/ x = n + 1) ==> P x     by arithmetic
   <=> !x. m <= x /\ x <= n ==> P x /\ P (n + 1)       by LEFT_AND_OVER_OR, DISJ_IMP_THM
   <=> P (n + 1) /\ EVERY P [m .. n]                   by listRangeINC_EVERY
*)
Theorem listRangeINC_EVERY_split_last:
  !P m n. m <= n ==> (EVERY P [m .. (n + 1)] <=> P (n + 1) /\ EVERY P [m .. n])
Proof
  rw[listRangeINC_EVERY] >>
  `!x. x <= n + 1 <=> x <= n \/ x = n + 1` by decide_tac >>
  metis_tac[]
QED

(* Theorem: m <= n ==> (EVERY P [m .. n] <=> P n /\ EVERY P [m ..< n]) *)
(* Proof:
       EVERY P [m .. n]
   <=> !x. m <= x /\ x <= n ==> P x                by listRangeINC_EVERY
   <=> !x. m <= x /\ (x < n \/ x = n) ==> P x      by arithmetic
   <=> !x. m <= x /\ x < n ==> P x /\ P n          by LEFT_AND_OVER_OR, DISJ_IMP_THM
   <=> P n /\ EVERY P [m ..< n]                    by listRangeLHI_EVERY
*)
Theorem listRangeINC_EVERY_less_last:
  !P m n. m <= n ==> (EVERY P [m .. n] <=> P n /\ EVERY P [m ..< n])
Proof
  rw[listRangeINC_EVERY, listRangeLHI_EVERY] >>
  `!x. x <= n <=> x < n \/ x = n` by decide_tac >>
  metis_tac[]
QED

(* Theorem: m < n /\ P m /\ ~P n ==>
            ?k. m <= k /\ k < n /\ EVERY P [m .. k] /\ ~P (SUC k) *)
(* Proof:
       m < n /\ P m /\ ~P n
   ==> ?k. m <= k /\ k < m /\
       (!j. m <= j /\ j <= k ==> P j) /\ ~P (SUC k)    by every_range_span_max
   ==> ?k. m <= k /\ k < m /\
       EVERY P [m .. k] /\ ~P (SUC k)                  by listRangeINC_EVERY
*)
Theorem listRangeINC_EVERY_span_max:
  !P m n. m < n /\ P m /\ ~P n ==>
          ?k. m <= k /\ k < n /\ EVERY P [m .. k] /\ ~P (SUC k)
Proof
  simp[listRangeINC_EVERY, every_range_span_max]
QED

(* Theorem: m < n /\ ~P m /\ P n ==>
            ?k. m < k /\ k <= n /\ EVERY P [k .. n] /\ ~P (PRE k) *)
(* Proof:
       m < n /\ P m /\ ~P n
   ==> ?k. m < k /\ k <= n /\
       (!j. k <= j /\ j <= n ==> P j) /\ ~P (PRE k)    by every_range_span_min
   ==> ?k. m < k /\ k <= n /\
       EVERY P [k .. n] /\ ~P (PRE k)                  by listRangeINC_EVERY
*)
Theorem listRangeINC_EVERY_span_min:
  !P m n. m < n /\ ~P m /\ P n ==>
          ?k. m < k /\ k <= n /\ EVERY P [k .. n] /\ ~P (PRE k)
Proof
  simp[listRangeINC_EVERY, every_range_span_min]
QED

(* ------------------------------------------------------------------------- *)
(* List Summation and Product                                                *)
(* ------------------------------------------------------------------------- *)

(*
> numpairTheory.tri_def;
val it = |- tri 0 = 0 /\ !n. tri (SUC n) = SUC n + tri n: thm
*)

(* Theorem: SUM [1 .. n] = tri n *)
(* Proof:
   By induction on n,
   Base: SUM [1 .. 0] = tri 0
         SUM [1 .. 0]
       = SUM []          by listRangeINC_EMPTY
       = 0               by SUM_NIL
       = tri 0           by tri_def
   Step: SUM [1 .. n] = tri n ==> SUM [1 .. SUC n] = tri (SUC n)
         SUM [1 .. SUC n]
       = SUM (SNOC (SUC n) [1 .. n])     by listRangeINC_SNOC, 1 < n
       = SUM [1 .. n] + (SUC n)          by SUM_SNOC
       = tri n + (SUC n)                 by induction hypothesis
       = tri (SUC n)                     by tri_def
*)
val sum_1_to_n_eq_tri_n = store_thm(
  "sum_1_to_n_eq_tri_n",
  ``!n. SUM [1 .. n] = tri n``,
  Induct >-
  rw[listRangeINC_EMPTY, SUM_NIL, numpairTheory.tri_def] >>
  rw[listRangeINC_SNOC, ADD1, SUM_SNOC, numpairTheory.tri_def]);

(* Theorem: SUM [1 .. n] = HALF (n * (n + 1)) *)
(* Proof:
     SUM [1 .. n]
   = tri n                by sum_1_to_n_eq_tri_n
   = HALF (n * (n + 1))   by tri_formula
*)
val sum_1_to_n_eqn = store_thm(
  "sum_1_to_n_eqn",
  ``!n. SUM [1 .. n] = HALF (n * (n + 1))``,
  rw[sum_1_to_n_eq_tri_n, numpairTheory.tri_formula]);

(* Theorem: 2 * SUM [1 .. n] = n * (n + 1) *)
(* Proof:
   Note EVEN (n * (n + 1))         by EVEN_PARTNERS
     or 2 divides (n * (n + 1))    by EVEN_ALT
   Thus n * (n + 1)
      = ((n * (n + 1)) DIV 2) * 2  by DIV_MULT_EQ
      = (SUM [1 .. n]) * 2         by sum_1_to_n_eqn
      = 2 * SUM [1 .. n]           by MULT_COMM
*)
val sum_1_to_n_double = store_thm(
  "sum_1_to_n_double",
  ``!n. 2 * SUM [1 .. n] = n * (n + 1)``,
  rpt strip_tac >>
  `2 divides (n * (n + 1))` by rw[EVEN_PARTNERS, GSYM EVEN_ALT] >>
  metis_tac[sum_1_to_n_eqn, DIV_MULT_EQ, MULT_COMM, DECIDE``0 < 2``]);

(* Theorem: PROD [1 .. n] = FACT n *)
(* Proof:
   By induction on n,
   Base: PROD [1 .. 0] = FACT 0
         PROD [1 .. 0]
       = PROD []          by listRangeINC_EMPTY
       = 1                by PROD_NIL
       = FACT 0           by FACT
   Step: PROD [1 .. n] = FACT n ==> PROD [1 .. SUC n] = FACT (SUC n)
         PROD [1 .. SUC n] = FACT (SUC n)
       = PROD (SNOC (SUC n) [1 .. n])     by listRangeINC_SNOC, 1 < n
       = PROD [1 .. n] * (SUC n)          by PROD_SNOC
       = (FACT n) * (SUC n)               by induction hypothesis
       = FACT (SUC n)                     by FACT
*)
val prod_1_to_n_eq_fact_n = store_thm(
  "prod_1_to_n_eq_fact_n",
  ``!n. PROD [1 .. n] = FACT n``,
  Induct >-
  rw[listRangeINC_EMPTY, PROD_NIL, FACT] >>
  rw[listRangeINC_SNOC, ADD1, PROD_SNOC, FACT]);

(* This is numerical version of:
poly_cyclic_cofactor  |- !r. Ring r /\ #1 <> #0 ==> !n. unity n = unity 1 * cyclic n
*)
(* Theorem: (t ** n - 1 = (t - 1) * SUM (MAP (\j. t ** j) [0 ..< n])) *)
(* Proof:
   Let f = (\j. t ** j).
   By induction on n.
   Base: t ** 0 - 1 = (t - 1) * SUM (MAP f [0 ..< 0])
         LHS = t ** 0 - 1 = 0           by EXP_0
         RHS = (t - 1) * SUM (MAP f [0 ..< 0])
             = (t - 1) * SUM []         by listRangeLHI_EMPTY
             = (t - 1) * 0 = 0          by SUM
   Step: t ** n - 1 = (t - 1) * SUM (MAP f [0 ..< n]) ==>
         t ** SUC n - 1 = (t - 1) * SUM (MAP f [0 ..< SUC n])
       If t = 0,
          LHS = 0 ** SUC n - 1 = 0              by EXP_0
          RHS = (0 - 1) * SUM (MAP f [0 ..< SUC n])
              = 0 * SUM (MAP f [0 ..< SUC n])   by integer subtraction
              = 0 = LHS
       If t <> 0,
          Then 0 < t ** n                       by EXP_POS
            or 1 <= t ** n                      by arithmetic
            so (t ** n - 1) + (t * t ** n - t ** n) = t * t ** n - 1
            (t - 1) * SUM (MAP (\j. t ** j) [0 ..< (SUC n)])
          = (t - 1) * SUM (MAP (\j. t ** j) [0 ..< n + 1])        by ADD1
          = (t - 1) * SUM (MAP (\j. t ** j) (SNOC n [0 ..< n]))   by listRangeLHI_SNOC
          = (t - 1) * SUM (SNOC (t ** n) (MAP f [0 ..< n]))       by MAP_SNOC
          = (t - 1) * (SUM (MAP f [0 ..< n]) + t ** n)            by SUM_SNOC
          = (t - 1) * SUM (MAP f [0 ..< n]) + (t - 1) * t ** n    by RIGHT_ADD_DISTRIB
          = (t ** n - 1) + (t - 1) * t ** n                       by induction hypothesis
          = t ** SUC n - 1                                        by EXP
*)
val power_predecessor_eqn = store_thm(
  "power_predecessor_eqn",
  ``!t n. t ** n - 1 = (t - 1) * SUM (MAP (\j. t ** j) [0 ..< n])``,
  rpt strip_tac >>
  qabbrev_tac `f = \j. t ** j` >>
  Induct_on `n` >-
  rw[EXP_0, Abbr`f`] >>
  Cases_on `t = 0` >-
  rw[ZERO_EXP, Abbr`f`] >>
  `(t ** n - 1) + (t * t ** n - t ** n) = t * t ** n - 1` by
  (`0 < t` by decide_tac >>
  `0 < t ** n` by rw[EXP_POS] >>
  `1 <= t ** n` by decide_tac >>
  `t ** n <= t * t ** n` by rw[] >>
  decide_tac) >>
  `(t - 1) * SUM (MAP f [0 ..< (SUC n)]) = (t - 1) * SUM (MAP f [0 ..< n + 1])` by rw[ADD1] >>
  `_ = (t - 1) * SUM (MAP f (SNOC n [0 ..< n]))` by rw[listRangeLHI_SNOC] >>
  `_ = (t - 1) * SUM (SNOC (t ** n) (MAP f [0 ..< n]))` by rw[MAP_SNOC, Abbr`f`] >>
  `_ = (t - 1) * (SUM (MAP f [0 ..< n]) + t ** n)` by rw[SUM_SNOC] >>
  `_ = (t - 1) * SUM (MAP f [0 ..< n]) + (t - 1) * t ** n` by rw[RIGHT_ADD_DISTRIB] >>
  `_ = (t ** n - 1) + (t - 1) * t ** n` by rw[] >>
  `_ = (t ** n - 1) + (t * t ** n - t ** n)` by rw[LEFT_SUB_DISTRIB] >>
  `_ = t * t ** n - 1` by rw[] >>
  `_ =  t ** SUC n - 1 ` by rw[GSYM EXP] >>
  rw[]);

(* Above is the formal proof of the following observation for any base:
        9 = 9 * 1
       99 = 9 * 11
      999 = 9 * 111
     9999 = 9 * 1111
    99999 = 8 * 11111
   etc.

  This asserts:
     (t ** n - 1) = (t - 1) * (1 + t + t ** 2 + ... + t ** (n-1))
  or  1 + t + t ** 2 + ... + t ** (n - 1) = (t ** n - 1) DIV (t - 1),
  which is the sum of the geometric series.
*)

(* Theorem: 1 < t ==> (SUM (MAP (\j. t ** j) [0 ..< n]) = (t ** n - 1) DIV (t - 1)) *)
(* Proof:
   Note 0 < t - 1                     by 1 < t
    Let s = SUM (MAP (\j. t ** j) [0 ..< n]).
   Then (t ** n - 1) = (t - 1) * s    by power_predecessor_eqn
   Thus s = (t ** n - 1) DIV (t - 1)  by MULT_TO_DIV, 0 < t - 1
*)
val geometric_sum_eqn = store_thm(
  "geometric_sum_eqn",
  ``!t n. 1 < t ==> (SUM (MAP (\j. t ** j) [0 ..< n]) = (t ** n - 1) DIV (t - 1))``,
  rpt strip_tac >>
  `0 < t - 1` by decide_tac >>
  rw_tac std_ss[power_predecessor_eqn, MULT_TO_DIV]);

(* Theorem: 1 < t ==> (SUM (MAP (\j. t ** j) [0 .. n]) = (t ** (n + 1) - 1) DIV (t - 1)) *)
(* Proof:
     SUM (MAP (\j. t ** j) [0 .. n])
   = SUM (MAP (\j. t ** j) [0 ..< n + 1])   by listRangeLHI_to_INC
   = (t ** (n + 1) - 1) DIV (t - 1)         by geometric_sum_eqn
*)
val geometric_sum_eqn_alt = store_thm(
  "geometric_sum_eqn_alt",
  ``!t n. 1 < t ==> (SUM (MAP (\j. t ** j) [0 .. n]) = (t ** (n + 1) - 1) DIV (t - 1))``,
  rw_tac std_ss[GSYM listRangeLHI_to_INC, geometric_sum_eqn]);

(* Theorem: SUM [1 ..< n] = HALF (n * (n - 1)) *)
(* Proof:
   If n = 0,
      LHS = SUM [1 ..< 0]
          = SUM [] = 0                by listRangeLHI_EMPTY
      RHS = HALF (0 * (0 - 1))
          = 0 = LHS                   by arithmetic
   If n <> 0,
      Then n = (n - 1) + 1            by arithmetic, n <> 0
        SUM [1 ..< n]
      = SUM [1 .. n - 1]              by listRangeLHI_to_INC
      = HALF ((n - 1) * (n - 1 + 1))  by sum_1_to_n_eqn
      = HALF (n * (n - 1))            by arithmetic
*)
val arithmetic_sum_eqn = store_thm(
  "arithmetic_sum_eqn",
  ``!n. SUM [1 ..< n] = HALF (n * (n - 1))``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[listRangeLHI_EMPTY] >>
  `n = (n - 1) + 1` by decide_tac >>
  `SUM [1 ..< n] = SUM [1 .. n - 1]` by rw[GSYM listRangeLHI_to_INC] >>
  `_ = HALF ((n - 1) * (n - 1 + 1))` by rw[sum_1_to_n_eqn] >>
  `_ = HALF (n * (n - 1))` by rw[] >>
  rw[]);

(* Theorem alias *)
val arithmetic_sum_eqn_alt = save_thm("arithmetic_sum_eqn_alt", sum_1_to_n_eqn);
(* val arithmetic_sum_eqn_alt = |- !n. SUM [1 .. n] = HALF (n * (n + 1)): thm *)

(* Theorem: SUM (GENLIST (\j. f (n - j)) n) = SUM (MAP f [1 .. n]) *)
(* Proof:
     SUM (GENLIST (\j. f (n - j)) n)
   = SUM (REVERSE (GENLIST (\j. f (n - j)) n))     by SUM_REVERSE
   = SUM (GENLIST (\j. f (n - (PRE n - j))) n)     by REVERSE_GENLIST
   = SUM (GENLIST (\j. f (1 + j)) n)               by LIST_EQ, SUB_SUB
   = SUM (GENLIST (f o SUC) n)                     by FUN_EQ_THM
   = SUM (MAP f [1 .. n])                          by listRangeINC_MAP
*)
val SUM_GENLIST_REVERSE = store_thm(
  "SUM_GENLIST_REVERSE",
  ``!f n. SUM (GENLIST (\j. f (n - j)) n) = SUM (MAP f [1 .. n])``,
  rpt strip_tac >>
  `GENLIST (\j. f (n - (PRE n - j))) n = GENLIST (f o SUC) n` by
  (irule LIST_EQ >>
  rw[] >>
  `n + x - PRE n = SUC x` by decide_tac >>
  simp[]) >>
  qabbrev_tac `g = \j. f (n - j)` >>
  `SUM (GENLIST g n) = SUM (REVERSE (GENLIST g n))` by rw[SUM_REVERSE] >>
  `_ = SUM (GENLIST (\j. g (PRE n - j)) n)` by rw[REVERSE_GENLIST] >>
  `_ = SUM (GENLIST (f o SUC) n)` by rw[Abbr`g`] >>
  `_ = SUM (MAP f [1 .. n])` by rw[listRangeINC_MAP] >>
  decide_tac);
(* Note: locate here due to use of listRangeINC_MAP *)

(* Theorem: SIGMA f (count n) = SUM (MAP f [0 ..< n]) *)
(* Proof:
     SIGMA f (count n)
   = SUM (GENLIST f n)         by SUM_GENLIST
   = SUM (MAP f [0 ..< n])     by listRangeLHI_MAP
*)
Theorem SUM_IMAGE_count:
  !f n. SIGMA f (count n) = SUM (MAP f [0 ..< n])
Proof
  simp[SUM_GENLIST, listRangeLHI_MAP]
QED
(* Note: locate here due to use of listRangeINC_MAP *)

(* Theorem: SIGMA f (count (SUC n)) = SUM (MAP f [0 .. n]) *)
(* Proof:
     SIGMA f (count (SUC n))
   = SUM (GENLIST f (SUC n))       by SUM_GENLIST
   = SUM (MAP f [0 ..< (SUC n)])   by SUM_IMAGE_count
   = SUM (MAP f [0 .. n])          by listRangeINC_to_LHI
*)
Theorem SUM_IMAGE_upto:
  !f n. SIGMA f (count (SUC n)) = SUM (MAP f [0 .. n])
Proof
  simp[SUM_GENLIST, SUM_IMAGE_count, listRangeINC_to_LHI]
QED

(* ------------------------------------------------------------------------- *)
(* MAP of function with 3 list arguments                                     *)
(* ------------------------------------------------------------------------- *)

(* Define MAP3 similar to MAP2 in listTheory. *)
val dDefine = Lib.with_flag (Defn.def_suffix, "_DEF") Define;
val MAP3_DEF = dDefine`
  (MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3) /\
  (MAP3 f x y z = [])`;
val _ = export_rewrites["MAP3_DEF"];
val MAP3 = store_thm ("MAP3",
``(!f. MAP3 f [] [] [] = []) /\
  (!f h1 t1 h2 t2 h3 t3. MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3)``,
  METIS_TAC[MAP3_DEF]);

(*
LENGTH_MAP   |- !l f. LENGTH (MAP f l) = LENGTH l
LENGTH_MAP2  |- !xs ys. LENGTH (MAP2 f xs ys) = MIN (LENGTH xs) (LENGTH ys)
*)

(* Theorem: LENGTH (MAP3 f lx ly lz) = MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) *)
(* Proof:
   By induction on lx.
   Base: !ly lz f. LENGTH (MAP3 f [] ly lz) = MIN (MIN (LENGTH []) (LENGTH ly)) (LENGTH lz)
      LHS = LENGTH [] = 0                         by MAP3, LENGTH
      RHS = MIN (MIN 0 (LENGTH ly)) (LENGTH lz)   by LENGTH
          = MIN 0 (LENGTH lz) = 0 = LHS           by MIN_DEF
   Step: !ly lz f. LENGTH (MAP3 f lx ly lz) = MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
         !h ly lz f. LENGTH (MAP3 f (h::lx) ly lz) = MIN (MIN (LENGTH (h::lx)) (LENGTH ly)) (LENGTH lz)
      If ly = [],
         LHS = LENGTH (MAP3 f (h::lx) [] lz) = 0  by MAP3, LENGTH
         RHS = MIN (MIN (LENGTH (h::lx)) (LENGTH [])) (LENGTH lz)
             = MIN 0 (LENGTH lz) = 0 = LHS        by MIN_DEF
      Otherwise, ly = h'::t.
      If lz = [],
         LHS = LENGTH (MAP3 f (h::lx) (h'::t) []) = 0  by MAP3, LENGTH
         RHS = MIN (MIN (LENGTH (h::lx)) (LENGTH (h'::t))) (LENGTH [])
             = 0 = LHS                                 by MIN_DEF
      Otherwise, lz = h''::t'.
         LHS = LENGTH (MAP3 f (h::lx) (h'::t) (h''::t'))
             = LENGTH (f h' h''::MAP3 lx t t'')        by MAP3
             = SUC (LENGTH MAP3 lx t t'')              by LENGTH
             = SUC (MIN (MIN (LENGTH lx) (LENGTH t)) (LENGTH t''))   by induction hypothesis
         RHS = MIN (MIN (LENGTH (h::lx)) (LENGTH (h'::t))) (LENGTH (h''::t'))
             = MIN (MIN (SUC (LENGTH lx)) (SUC (LENGTH t))) (SUC (LENGTH t'))  by LENGTH
             = MIN (SUC (MIN (LENGTH lx) (LENGTH t))) (SUC (LESS_TWICE t'))    by MIN_DEF
             = SUC (MIN (MIN (LENGTH lx) (LENGTH t)) (LENGTH t'')) = LHS       by MIN_DEF
*)
val LENGTH_MAP3 = store_thm(
  "LENGTH_MAP3",
  ``!lx ly lz f. LENGTH (MAP3 f lx ly lz) = MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz)``,
  Induct_on `lx` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ly` >-
  rw[] >>
  Cases_on `lz` >-
  rw[] >>
  rw[MIN_DEF]);

(*
EL_MAP   |- !n l. n < LENGTH l ==> !f. EL n (MAP f l) = f (EL n l)
EL_MAP2  |- !ts tt n. n < MIN (LENGTH ts) (LENGTH tt) ==> (EL n (MAP2 f ts tt) = f (EL n ts) (EL n tt))
*)

(* Theorem: n < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
           !f. EL n (MAP3 f lx ly lz) = f (EL n lx) (EL n ly) (EL n lz) *)
(* Proof:
   By induction on n.
   Base: !lx ly lz. 0 < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
         !f. EL 0 (MAP3 f lx ly lz) = f (EL 0 lx) (EL 0 ly) (EL 0 lz)
      Note ?x tx. lx = x::tx             by LENGTH_EQ_0, list_CASES
       and ?y ty. ly = y::ty             by LENGTH_EQ_0, list_CASES
       and ?z tz. lz = z::tz             by LENGTH_EQ_0, list_CASES
          EL 0 (MAP3 f lx ly lz)
        = EL 0 (MAP3 f (x::lx) (y::ty) (z::tz))
        = EL 0 (f x y z::MAP3 f tx ty tz)    by MAP3
        = f x y z                            by EL
        = f (EL 0 lx) (EL 0 ly) (EL 0 lz)    by EL
   Step: !lx ly lz. n < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
             !f. EL n (MAP3 f lx ly lz) = f (EL n lx) (EL n ly) (EL n lz) ==>
         !lx ly lz. SUC n < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
             !f. EL (SUC n) (MAP3 f lx ly lz) = f (EL (SUC n) lx) (EL (SUC n) ly) (EL (SUC n) lz)
      Note ?x tx. lx = x::tx             by LENGTH_EQ_0, list_CASES
       and ?y ty. ly = y::ty             by LENGTH_EQ_0, list_CASES
       and ?z tz. lz = z::tz             by LENGTH_EQ_0, list_CASES
      Also n < LENGTH tx /\ n < LENGTH ty /\ n < LENGTH tz    by LENGTH
      Thus n < MIN (MIN (LENGTH tx) (LENGTH ty)) (LENGTH tz)  by MIN_DEF
          EL (SUC n) (MAP3 f lx ly lz)
        = EL (SUC n) (MAP3 f (x::lx) (y::ty) (z::tz))
        = EL (SUC n) (f x y z::MAP3 f tx ty tz)    by MAP3
        = EL n (MAP3 f tx ty tz)                   by EL
        = f (EL n tx) (EL n ty) (EL n tz)          by induction hypothesis
        = f (EL (SUC n) lx) (EL (SUC n) ly) (EL (SUC n) lz)
                                                   by EL
*)
val EL_MAP3 = store_thm(
  "EL_MAP3",
  ``!lx ly lz n. n < MIN (MIN (LENGTH lx) (LENGTH ly)) (LENGTH lz) ==>
   !f. EL n (MAP3 f lx ly lz) = f (EL n lx) (EL n ly) (EL n lz)``,
  Induct_on `n` >| [
    rw[] >>
    `?x tx. lx = x::tx` by metis_tac[LENGTH_EQ_0, list_CASES, NOT_ZERO_LT_ZERO] >>
    `?y ty. ly = y::ty` by metis_tac[LENGTH_EQ_0, list_CASES, NOT_ZERO_LT_ZERO] >>
    `?z tz. lz = z::tz` by metis_tac[LENGTH_EQ_0, list_CASES, NOT_ZERO_LT_ZERO] >>
    rw[],
    rw[] >>
    `!a. SUC n < a ==> a <> 0` by decide_tac >>
    `?x tx. lx = x::tx` by metis_tac[LENGTH_EQ_0, list_CASES] >>
    `?y ty. ly = y::ty` by metis_tac[LENGTH_EQ_0, list_CASES] >>
    `?z tz. lz = z::tz` by metis_tac[LENGTH_EQ_0, list_CASES] >>
    `n < LENGTH tx /\ n < LENGTH ty /\ n < LENGTH tz` by fs[] >>
    rw[]
  ]);

(*
MEM_MAP  |- !l f x. MEM x (MAP f l) <=> ?y. x = f y /\ MEM y l
*)

(* Theorem: MEM x (MAP2 f l1 l2) ==> ?y1 y2. x = f y1 y2 /\ MEM y1 l1 /\ MEM y2 l2 *)
(* Proof:
   By induction on l1.
   Base: !l2. MEM x (MAP2 f [] l2) ==> ?y1 y2. x = f y1 y2 /\ MEM y1 [] /\ MEM y2 l2
      Note MAP2 f [] l2 = []         by MAP2_DEF
       and MEM x [] = F, hence true  by MEM
   Step: !l2. MEM x (MAP2 f l1 l2) ==> ?y1 y2. x = f y1 y2 /\ MEM y1 l1 /\ MEM y2 l2 ==>
         !h l2. MEM x (MAP2 f (h::l1) l2) ==> ?y1 y2. x = f y1 y2 /\ MEM y1 (h::l1) /\ MEM y2 l2
      If l2 = [],
         Then MEM x (MAP2 f (h::l1) []) = F, hence true    by MEM
      Otherwise, l2 = h'::t,
         to show: MEM x (MAP2 f (h::l1) (h'::t)) ==> ?y1 y2. x = f y1 y2 /\ MEM y1 (h::l1) /\ MEM y2 (h'::t)
         Note MAP2 f (h::l1) (h'::t)
            = (f h h')::MAP2 f l1 t                      by MAP2
         Thus x = f h h'  or MEM x (MAP2 f l1 t)         by MEM
         If x = f h h',
            Take y1 = h, y2 = h', and the result follows by MEM
         If MEM x (MAP2 f l1 t)
            Then ?y1 y2. x = f y1 y2 /\ MEM y1 l1 /\ MEM y2 t   by induction hypothesis
            Take this y1 and y2, the result follows      by MEM
*)
val MEM_MAP2 = store_thm(
  "MEM_MAP2",
  ``!f x l1 l2. MEM x (MAP2 f l1 l2) ==> ?y1 y2. (x = f y1 y2) /\ MEM y1 l1 /\ MEM y2 l2``,
  ntac 2 strip_tac >>
  Induct_on `l1` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l2` >-
  fs[] >>
  fs[] >-
  metis_tac[] >>
  metis_tac[MEM]);

(* Theorem: MEM x (MAP3 f l1 l2 l3) ==> ?y1 y2 y3. (x = f y1 y2 y3) /\ MEM y1 l1 /\ MEM y2 l2 /\ MEM y3 l3 *)
(* Proof:
   By induction on l1.
   Base: !l2 l3. MEM x (MAP3 f [] l2 l3) ==> ...
      Note MAP3 f [] l2 l3 = [], and MEM x [] = F, hence true.
   Step: !l2 l3. MEM x (MAP3 f l1 l2 l3) ==>
                 ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 l1 /\ MEM y2 l2 /\ MEM y3 l3 ==>
         !h l2 l3. MEM x (MAP3 f (h::l1) l2 l3) ==>
                 ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 (h::l1) /\ MEM y2 l2 /\ MEM y3 l3
      If l2 = [],
         Then MEM x (MAP3 f (h::l1) [] l3) = MEM x [] = F, hence true   by MAP3_DEF
      Otherwise, l2 = h'::t,
         to show: MEM x (MAP3 f (h::l1) (h'::t) l3) ==>
                  ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 (h::l1) /\ MEM y2 (h'::t) /\ MEM y3 l3
         If l3 = [],
            Then MEM x (MAP3 f (h::l1) l2 []) = MEM x [] = F, hence true   by MAP3_DEF
         Otherwise, l3 = h''::t',
            to show: MEM x (MAP3 f (h::l1) (h'::t) (h''::t')) ==>
                     ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 (h::l1) /\ MEM y2 (h'::t) /\ MEM y3 (h''::t')

         Note MAP3 f (h::l1) (h'::t) (h''::t')
            = (f h h' h'')::MAP3 f l1 t t'              by MAP3
         Thus x = f h h' h''  or MEM x (MAP3 f l1 t t') by MEM
         If x = f h h' h'',
            Take y1 = h, y2 = h', y3 = h'' and the result follows by MEM
         If MEM x (MAP3 f l1 t t')
            Then ?y1 y2 y3. x = f y1 y2 y3 /\ MEM y1 t /\ MEM y2 l2 /\ MEM y3 t'
                                                         by induction hypothesis
            Take this y1, y2 and y3, the result follows  by MEM
*)
val MEM_MAP3 = store_thm(
  "MEM_MAP3",
  ``!f x l1 l2 l3. MEM x (MAP3 f l1 l2 l3) ==>
   ?y1 y2 y3. (x = f y1 y2 y3) /\ MEM y1 l1 /\ MEM y2 l2 /\ MEM y3 l3``,
  ntac 2 strip_tac >>
  Induct_on `l1` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l2` >-
  fs[] >>
  Cases_on `l3` >-
  fs[] >>
  fs[] >-
  metis_tac[] >>
  metis_tac[MEM]);

(* Theorem: SUM (MAP (K c) ls) = c * LENGTH ls *)
(* Proof:
   By induction on ls.
   Base: !c. SUM (MAP (K c) []) = c * LENGTH []
      LHS = SUM (MAP (K c) [])
          = SUM [] = 0             by MAP, SUM
      RHS = c * LENGTH []
          = c * 0 = 0 = LHS        by LENGTH
   Step: !c. SUM (MAP (K c) ls) = c * LENGTH ls ==>
         !h c. SUM (MAP (K c) (h::ls)) = c * LENGTH (h::ls)
        SUM (MAP (K c) (h::ls))
      = SUM (c :: MAP (K c) ls)    by MAP
      = c + SUM (MAP (K c) ls)     by SUM
      = c + c * LENGTH ls          by induction hypothesis
      = c * (1 + LENGTH ls)        by RIGHT_ADD_DISTRIB
      = c * (SUC (LENGTH ls))      by ADD1
      = c * LENGTH (h::ls)         by LENGTH
*)
val SUM_MAP_K = store_thm(
  "SUM_MAP_K",
  ``!ls c. SUM (MAP (K c) ls) = c * LENGTH ls``,
  Induct >-
  rw[] >>
  rw[ADD1]);

(* Theorem: a <= b ==> SUM (MAP (K a) ls) <= SUM (MAP (K b) ls) *)
(* Proof:
      SUM (MAP (K a) ls)
    = a * LENGTH ls             by SUM_MAP_K
   <= b * LENGTH ls             by a <= b
    = SUM (MAP (K b) ls)        by SUM_MAP_K
*)
val SUM_MAP_K_LE = store_thm(
  "SUM_MAP_K_LE",
  ``!ls a b. a <= b ==> SUM (MAP (K a) ls) <= SUM (MAP (K b) ls)``,
  rw[SUM_MAP_K]);

(* Theorem: SUM (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly) *)
(* Proof:
   By induction on lx.
   Base: !ly c. SUM (MAP2 (\x y. c) [] ly) = c * LENGTH (MAP2 (\x y. c) [] ly)
      LHS = SUM (MAP2 (\x y. c) [] ly)
          = SUM [] = 0             by MAP2_DEF, SUM
      RHS = c * LENGTH (MAP2 (\x y. c) [] ly)
          = c * 0 = 0 = LHS        by MAP2_DEF, LENGTH
   Step: !ly c. SUM (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly) ==>
         !h ly c. SUM (MAP2 (\x y. c) (h::lx) ly) = c * LENGTH (MAP2 (\x y. c) (h::lx) ly)
      If ly = [],
         to show: SUM (MAP2 (\x y. c) (h::lx) []) = c * LENGTH (MAP2 (\x y. c) (h::lx) [])
         LHS = SUM (MAP2 (\x y. c) (h::lx) [])
             = SUM [] = 0          by MAP2_DEF, SUM
         RHS = c * LENGTH (MAP2 (\x y. c) (h::lx) [])
             = c * 0 = 0 = LHS     by MAP2_DEF, LENGTH
      Otherwise, ly = h'::t,
        to show: SUM (MAP2 (\x y. c) (h::lx) (h'::t)) = c * LENGTH (MAP2 (\x y. c) (h::lx) (h'::t))

           SUM (MAP2 (\x y. c) (h::lx) (h'::t))
         = SUM (c :: MAP2 (\x y. c) lx t)               by MAP2_DEF
         = c + SUM (MAP2 (\x y. c) lx t)                by SUM
         = c + c * LENGTH (MAP2 (\x y. c) lx t)         by induction hypothesis
         = c * (1 + LENGTH (MAP2 (\x y. c) lx t)        by RIGHT_ADD_DISTRIB
         = c * (SUC (LENGTH (MAP2 (\x y. c) lx t))      by ADD1
         = c * LENGTH (MAP2 (\x y. c) (h::lx) (h'::t))  by LENGTH
*)
val SUM_MAP2_K = store_thm(
  "SUM_MAP2_K",
  ``!lx ly c. SUM (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ly` >-
  rw[] >>
  rw[ADD1, MIN_DEF]);

(* Theorem: SUM (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz) *)
(* Proof:
   By induction on lx.
   Base: !ly lz c. SUM (MAP3 (\x y z. c) [] ly lz) = c * LENGTH (MAP3 (\x y z. c) [] ly lz)
      LHS = SUM (MAP3 (\x y z. c) [] ly lz)
          = SUM [] = 0             by MAP3_DEF, SUM
      RHS = c * LENGTH (MAP3 (\x y z. c) [] ly lz)
          = c * 0 = 0 = LHS        by MAP3_DEF, LENGTH
   Step: !ly lz c. SUM (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz) ==>
         !h ly lz c. SUM (MAP3 (\x y z. c) (h::lx) ly lz) = c * LENGTH (MAP3 (\x y z. c) (h::lx) ly lz)
      If ly = [],
         to show: SUM (MAP3 (\x y z. c) (h::lx) [] lz) = c * LENGTH (MAP3 (\x y z. c) (h::lx) [] lz)
         LHS = SUM (MAP3 (\x y z. c) (h::lx) [] lz)
             = SUM [] = 0          by MAP3_DEF, SUM
         RHS = c * LENGTH (MAP3 (\x y z. c) (h::lx) [] lz)
             = c * 0 = 0 = LHS     by MAP3_DEF, LENGTH
      Otherwise, ly = h'::t,
        to show: SUM (MAP3 (\x y z. c) (h::lx) (h'::t) lz) = c * LENGTH (MAP3 (\x y z. c) (h::lx) (h'::t) lz)
        If lz = [],
           to show: SUM (MAP3 (\x y z. c) (h::lx) (h'::t) []) = c * LENGTH (MAP3 (\x y z. c) (h::lx) (h'::t) [])
           LHS = SUM (MAP3 (\x y z. c) (h::lx) (h'::t) [])
               = SUM [] = 0                  by MAP3_DEF, SUM
           RHS = c * LENGTH (MAP3 (\x y z. c) (h::lx) (h'::t) [])
               = c * 0 = 0                   by MAP3_DEF, LENGTH
        Otherwise, lz = h''::t',
           to show: SUM (MAP3 (\x y z. c) (h::lx) (h'::t) (h''::t')) = c * LENGTH (MAP3 (\x y z. c) (h::lx) (h'::t) (h''::t'))
              SUM (MAP3 (\x y z. c) (h::lx) (h'::t) (h''::t'))
            = SUM (c :: MAP3 (\x y z. c) lx t t')                      by MAP3_DEF
            = c + SUM (MAP3 (\x y z. c) lx t t')                       by SUM
            = c + c * LENGTH (MAP3 (\x y z. c) lx t t')                by induction hypothesis
            = c * (1 + LENGTH (MAP3 (\x y z. c) lx t t')               by RIGHT_ADD_DISTRIB
            = c * (SUC (LENGTH (MAP3 (\x y z. c) lx t t'))             by ADD1
            = c * LENGTH (MAP3 (\x y z. c) (h::lx) (h'::t) (h''::t'))  by LENGTH
*)
val SUM_MAP3_K = store_thm(
  "SUM_MAP3_K",
  ``!lx ly lz c. SUM (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ly` >-
  rw[] >>
  Cases_on `lz` >-
  rw[] >>
  rw[ADD1]);

(* ------------------------------------------------------------------------- *)
(* Bounds on Lists                                                           *)
(* ------------------------------------------------------------------------- *)

(* Overload non-decreasing functions with different arity. *)
val _ = overload_on("MONO", ``\f:num -> num. !x y. x <= y ==> f x <= f y``);
val _ = overload_on("MONO2", ``\f:num -> num -> num. !x1 y1 x2 y2. x1 <= x2 /\ y1 <= y2 ==> f x1 y1 <= f x2 y2``);
val _ = overload_on("MONO3", ``\f:num -> num -> num -> num. !x1 y1 z1 x2 y2 z2. x1 <= x2 /\ y1 <= y2 /\ z1 <= z2 ==> f x1 y1 z1 <= f x2 y2 z2``);

(* Overload non-increasing functions with different arity. *)
val _ = overload_on("RMONO", ``\f:num -> num. !x y. x <= y ==> f y <= f x``);
val _ = overload_on("RMONO2", ``\f:num -> num -> num. !x1 y1 x2 y2. x1 <= x2 /\ y1 <= y2 ==> f x2 y2 <= f x1 y1``);
val _ = overload_on("RMONO3", ``\f:num -> num -> num -> num. !x1 y1 z1 x2 y2 z2. x1 <= x2 /\ y1 <= y2 /\ z1 <= z2 ==> f x2 y2 z2 <= f x1 y1 z1``);


(* Theorem: SUM ls <= (MAX_LIST ls) * LENGTH ls *)
(* Proof:
   By induction on ls.
   Base: SUM [] <= MAX_LIST [] * LENGTH []
      LHS = SUM [] = 0          by SUM
      RHS = MAX_LIST [] * LENGTH []
          = 0 * 0 = 0           by MAX_LIST, LENGTH
      Hence true.
   Step: SUM ls <= MAX_LIST ls * LENGTH ls ==>
         !h. SUM (h::ls) <= MAX_LIST (h::ls) * LENGTH (h::ls)
        SUM (h::ls)
      = h + SUM ls                                       by SUM
     <= h + MAX_LIST ls * LENGTH ls                      by induction hypothesis
     <= MAX_LIST (h::ls) + MAX_LIST ls * LENGTH ls       by MAX_LIST_PROPERTY
     <= MAX_LIST (h::ls) + MAX_LIST (h::ls) * LENGTH ls  by MAX_LIST_LE
      = MAX_LIST (h::ls) * (1 + LENGTH ls)               by LEFT_ADD_DISTRIB
      = MAX_LIST (h::ls) * LENGTH (h::ls)                by LENGTH
*)
val SUM_UPPER = store_thm(
  "SUM_UPPER",
  ``!ls. SUM ls <= (MAX_LIST ls) * LENGTH ls``,
  Induct_on `ls` >-
  rw[] >>
  strip_tac >>
  `SUM (h::ls) <= h + MAX_LIST ls * LENGTH ls` by rw[] >>
  `h + MAX_LIST ls * LENGTH ls <= MAX_LIST (h::ls) + MAX_LIST ls * LENGTH ls` by rw[] >>
  `MAX_LIST (h::ls) + MAX_LIST ls * LENGTH ls <= MAX_LIST (h::ls) + MAX_LIST (h::ls) * LENGTH ls` by rw[] >>
  `MAX_LIST (h::ls) + MAX_LIST (h::ls) * LENGTH ls = MAX_LIST (h::ls) * (1 + LENGTH ls)` by rw[] >>
  `_ = MAX_LIST (h::ls) * LENGTH (h::ls)` by rw[] >>
  decide_tac);

(* Theorem: (MIN_LIST ls) * LENGTH ls <= SUM ls *)
(* Proof:
   By induction on ls.
   Base: MIN_LIST [] * LENGTH [] <= SUM []
      LHS = (MIN_LIST []) * LENGTH [] = 0     by LENGTH
      RHS = SUM [] = 0                        by SUM
      Hence true.
   Step: MIN_LIST ls * LENGTH ls <= SUM ls ==>
         !h. MIN_LIST (h::ls) * LENGTH (h::ls) <= SUM (h::ls)
      If ls = [],
         LHS = (MIN_LIST [h]) * LENGTH [h]
             = h * 1 = h             by MIN_LIST_def, LENGTH
         RHS = SUM [h] = h           by SUM
         Hence true.
      If ls <> [],
          MIN_LIST (h::ls) * LENGTH (h::ls)
        = (MIN h (MIN_LIST ls)) * (1 + LENGTH ls)   by MIN_LIST_def, LENGTH
        = (MIN h (MIN_LIST ls)) + (MIN h (MIN_LIST ls)) * LENGTH ls
                                                    by RIGHT_ADD_DISTRIB
       <= h + (MIN_LIST ls) * LENGTH ls             by MIN_IS_MIN
       <= h + SUM ls                                by induction hypothesis
        = SUM (h::ls)                               by SUM
*)
val SUM_LOWER = store_thm(
  "SUM_LOWER",
  ``!ls. (MIN_LIST ls) * LENGTH ls <= SUM ls``,
  Induct_on `ls` >-
  rw[] >>
  strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `MIN_LIST (h::ls) * LENGTH (h::ls) = (MIN h (MIN_LIST ls)) * (1 + LENGTH ls)` by rw[] >>
  `_ = (MIN h (MIN_LIST ls)) + (MIN h (MIN_LIST ls)) * LENGTH ls` by rw[] >>
  `(MIN h (MIN_LIST ls)) <= h` by rw[] >>
  `(MIN h (MIN_LIST ls)) * LENGTH ls <= (MIN_LIST ls) * LENGTH ls` by rw[] >>
  rw[]);

(* Theorem: EVERY (\x. f x <= g x) ls ==> SUM (MAP f ls) <= SUM (MAP g ls) *)
(* Proof:
   By induction on ls.
   Base: EVERY (\x. f x <= g x) [] ==> SUM (MAP f []) <= SUM (MAP g [])
         EVERY (\x. f x <= g x) [] = T    by EVERY_DEF
           SUM (MAP f [])
         = SUM []                         by MAP
         = SUM (MAP g [])                 by MAP
   Step: EVERY (\x. f x <= g x) ls ==> SUM (MAP f ls) <= SUM (MAP g ls) ==>
         !h. EVERY (\x. f x <= g x) (h::ls) ==> SUM (MAP f (h::ls)) <= SUM (MAP g (h::ls))
         Note f h <= g h /\
              EVERY (\x. f x <= g x) ls   by EVERY_DEF
           SUM (MAP f (h::ls))
         = SUM (f h :: MAP f ls)          by MAP
         = f h + SUM (MAP f ls)           by SUM
        <= g h + SUM (MAP g ls)           by above, induction hypothesis
         = SUM (g h :: MAP g ls)          by SUM
         = SUM (MAP g (h::ls))            by MAP
*)
val SUM_MAP_LE = store_thm(
  "SUM_MAP_LE",
  ``!f g ls. EVERY (\x. f x <= g x) ls ==> SUM (MAP f ls) <= SUM (MAP g ls)``,
  rpt strip_tac >>
  Induct_on `ls` >>
  rw[] >>
  rw[] >>
  fs[]);

(* Theorem: EVERY (\x. f x < g x) ls /\ ls <> [] ==> SUM (MAP f ls) < SUM (MAP g ls) *)
(* Proof:
   By induction on ls.
   Base: EVERY (\x. f x <= g x) [] /\ [] <> [] ==> SUM (MAP f []) <= SUM (MAP g [])
         True since [] <> [] = F.
   Step: EVERY (\x. f x <= g x) ls ==> ls <> [] ==> SUM (MAP f ls) <= SUM (MAP g ls) ==>
         !h. EVERY (\x. f x <= g x) (h::ls) ==> h::ls <> [] ==> SUM (MAP f (h::ls)) <= SUM (MAP g (h::ls))
         Note f h < g h /\
              EVERY (\x. f x < g x) ls    by EVERY_DEF

         If ls = [],
           SUM (MAP f [h])
         = SUM (f h)          by MAP
         = f h                by SUM
         < g h                by above
         = SUM (g h)          by SUM
         = SUM (MAP g [h])    by MAP

         If ls <> [],
           SUM (MAP f (h::ls))
         = SUM (f h :: MAP f ls)          by MAP
         = f h + SUM (MAP f ls)           by SUM
         < g h + SUM (MAP g ls)           by induction hypothesis
         = SUM (g h :: MAP g ls)          by SUM
         = SUM (MAP g (h::ls))            by MAP
*)
val SUM_MAP_LT = store_thm(
  "SUM_MAP_LT",
  ``!f g ls. EVERY (\x. f x < g x) ls /\ ls <> [] ==> SUM (MAP f ls) < SUM (MAP g ls)``,
  rpt strip_tac >>
  Induct_on `ls` >>
  rw[] >>
  rw[] >>
  (Cases_on `ls = []` >> fs[]));

(*
MAX_LIST_PROPERTY  |- !l x. MEM x l ==> x <= MAX_LIST l
MIN_LIST_PROPERTY  |- !l. l <> [] ==> !x. MEM x l ==> MIN_LIST l <= x
*)

(* Theorem: MONO f  ==> !ls e. MEM e (MAP f ls) ==> e <= f (MAX_LIST ls) *)
(* Proof:
   Note ?y. (e = f y) /\ MEM y ls    by MEM_MAP
    and   y <= MAX_LIST ls           by MAX_LIST_PROPERTY
   Thus f y <= f (MAX_LIST ls)       by given
     or   e <= f (MAX_LIST ls)       by e = f y
*)
val MEM_MAP_UPPER = store_thm(
  "MEM_MAP_UPPER",
  ``!f. MONO f ==> !ls e. MEM e (MAP f ls) ==> e <= f (MAX_LIST ls)``,
  rpt strip_tac >>
  `?y. (e = f y) /\ MEM y ls` by rw[GSYM MEM_MAP] >>
  `y <= MAX_LIST ls` by rw[MAX_LIST_PROPERTY] >>
  rw[]);

(* Theorem: MONO2 f ==> !lx ly e. MEM e (MAP2 f lx ly) ==> e <= f (MAX_LIST lx) (MAX_LIST ly) *)
(* Proof:
   Note ?ex ey. (e = f ex ey) /\
                MEM ex lx /\ MEM ey ly    by MEM_MAP2
    and ex <= MAX_LIST lx                 by MAX_LIST_PROPERTY
    and ey <= MAX_LIST ly                 by MAX_LIST_PROPERTY
   The result follows by the non-decreasing condition on f.
*)
val MEM_MAP2_UPPER = store_thm(
  "MEM_MAP2_UPPER",
  ``!f. MONO2 f ==> !lx ly e. MEM e (MAP2 f lx ly) ==> e <= f (MAX_LIST lx) (MAX_LIST ly)``,
  metis_tac[MEM_MAP2, MAX_LIST_PROPERTY]);

(* Theorem: MONO3 f ==>
   !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> e <= f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz) *)
(* Proof:
   Note ?ex ey ez. (e = f ex ey ez) /\
                   MEM ex lx /\ MEM ey ly /\ MEM ez lz  by MEM_MAP3
    and ex <= MAX_LIST lx                 by MAX_LIST_PROPERTY
    and ey <= MAX_LIST ly                 by MAX_LIST_PROPERTY
    and ez <= MAX_LIST lz                 by MAX_LIST_PROPERTY
   The result follows by the non-decreasing condition on f.
*)
val MEM_MAP3_UPPER = store_thm(
  "MEM_MAP3_UPPER",
  ``!f. MONO3 f ==>
   !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> e <= f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz)``,
  metis_tac[MEM_MAP3, MAX_LIST_PROPERTY]);

(* Theorem: MONO f ==> !ls e. MEM e (MAP f ls) ==> f (MIN_LIST ls) <= e *)
(* Proof:
   Note ?y. (e = f y) /\ MEM y ls    by MEM_MAP
    and ls <> []                     by MEM, MEM y ls
   then     MIN_LIST ls <= y         by MIN_LIST_PROPERTY, ls <> []
   Thus f (MIN_LIST ls) <= f y       by given
     or f (MIN_LIST ls) <= e         by e = f y
*)
val MEM_MAP_LOWER = store_thm(
  "MEM_MAP_LOWER",
  ``!f. MONO f ==> !ls e. MEM e (MAP f ls) ==> f (MIN_LIST ls) <= e``,
  rpt strip_tac >>
  `?y. (e = f y) /\ MEM y ls` by rw[GSYM MEM_MAP] >>
  `ls <> []` by metis_tac[MEM] >>
  `MIN_LIST ls <= y` by rw[MIN_LIST_PROPERTY] >>
  rw[]);

(* Theorem: MONO2 f ==>
            !lx ly e. MEM e (MAP2 f lx ly) ==> f (MIN_LIST lx) (MIN_LIST ly) <= e *)
(* Proof:
   Note ?ex ey. (e = f ex ey) /\
                MEM ex lx /\ MEM ey ly   by MEM_MAP2
    and lx <> [] /\ ly <> []             by MEM
    and MIN_LIST lx <= ex                by MIN_LIST_PROPERTY
    and MIN_LIST ly <= ey                by MIN_LIST_PROPERTY
   The result follows by the non-decreasing condition on f.
*)
val MEM_MAP2_LOWER = store_thm(
  "MEM_MAP2_LOWER",
  ``!f. MONO2 f ==>
   !lx ly e. MEM e (MAP2 f lx ly) ==> f (MIN_LIST lx) (MIN_LIST ly) <= e``,
  metis_tac[MEM_MAP2, MEM, MIN_LIST_PROPERTY]);

(* Theorem: MONO3 f ==>
   !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> f (MIN_LIST lx) (MIN_LIST ly) (MIN_LIST lz) <= e *)
(* Proof:
   Note ?ex ey ez. (e = f ex ey ez) /\
                MEM ex lx /\ MEM ey ly /\ MEM ez lz  by MEM_MAP3
    and lx <> [] /\ ly <> [] /\ lz <> [] by MEM
    and MIN_LIST lx <= ex                by MIN_LIST_PROPERTY
    and MIN_LIST ly <= ey                by MIN_LIST_PROPERTY
    and MIN_LIST lz <= ez                by MIN_LIST_PROPERTY
   The result follows by the non-decreasing condition on f.
*)
val MEM_MAP3_LOWER = store_thm(
  "MEM_MAP3_LOWER",
  ``!f. MONO3 f ==>
   !lx ly lz e. MEM e (MAP3 f lx ly lz) ==> f (MIN_LIST lx) (MIN_LIST ly) (MIN_LIST lz) <= e``,
  rpt strip_tac >>
  `?ex ey ez. (e = f ex ey ez) /\ MEM ex lx /\ MEM ey ly /\ MEM ez lz` by rw[MEM_MAP3] >>
  `lx <> [] /\ ly <> [] /\ lz <> []` by metis_tac[MEM] >>
  rw[MIN_LIST_PROPERTY]);

(* Theorem: (!x. f x <= g x) ==> !ls. MAX_LIST (MAP f ls) <= MAX_LIST (MAP g ls) *)
(* Proof:
   By induction on ls.
   Base: MAX_LIST (MAP f []) <= MAX_LIST (MAP g [])
      LHS = MAX_LIST (MAP f []) = MAX_LIST []    by MAP
      RHS = MAX_LIST (MAP g []) = MAX_LIST []    by MAP
      Hence true.
   Step: MAX_LIST (MAP f ls) <= MAX_LIST (MAP g ls) ==>
         !h. MAX_LIST (MAP f (h::ls)) <= MAX_LIST (MAP g (h::ls))
        MAX_LIST (MAP f (h::ls))
      = MAX_LIST (f h::MAP f ls)                 by MAP
      = MAX (f h) (MAX_LIST (MAP f ls))          by MAX_LIST_def
     <= MAX (f h) (MAX_LIST (MAP g ls))          by induction hypothesis
     <= MAX (g h) (MAX_LIST (MAP g ls))          by properties of f, g
      = MAX_LIST (g h::MAP g ls)                 by MAX_LIST_def
      = MAX_LIST (MAP g (h::ls))                 by MAP
*)
val MAX_LIST_MAP_LE = store_thm(
  "MAX_LIST_MAP_LE",
  ``!f g. (!x. f x <= g x) ==> !ls. MAX_LIST (MAP f ls) <= MAX_LIST (MAP g ls)``,
  rpt strip_tac >>
  Induct_on `ls` >-
  rw[] >>
  rw[]);

(* Theorem: (!x. f x <= g x) ==> !ls. MIN_LIST (MAP f ls) <= MIN_LIST (MAP g ls) *)
(* Proof:
   By induction on ls.
   Base: MIN_LIST (MAP f []) <= MIN_LIST (MAP g [])
      LHS = MIN_LIST (MAP f []) = MIN_LIST []    by MAP
      RHS = MIN_LIST (MAP g []) = MIN_LIST []    by MAP
      Hence true.
   Step: MIN_LIST (MAP f ls) <= MIN_LIST (MAP g ls) ==>
         !h. MIN_LIST (MAP f (h::ls)) <= MIN_LIST (MAP g (h::ls))
      If ls = [],
        MIN_LIST (MAP f [h])
      = MIN_LIST [f h]                           by MAP
      = f h                                      by MIN_LIST_def
     <= g h                                      by properties of f, g
      = MIN_LIST [g h]                           by MIN_LIST_def
      = MIN_LIST (MAP g [h])                     by MAP
      Otherwise ls <> [],
        MIN_LIST (MAP f (h::ls))
      = MIN_LIST (f h::MAP f ls)                 by MAP
      = MIN (f h) (MIN_LIST (MAP f ls))          by MIN_LIST_def
     <= MIN (g h) (MIN_LIST (MAP g ls))          by MIN_LE_PAIR, induction hypothesis
      = MIN_LIST (g h::MAP g ls)                 by MIN_LIST_def
      = MIN_LIST (MAP g (h::ls))                 by MAP
*)
val MIN_LIST_MAP_LE = store_thm(
  "MIN_LIST_MAP_LE",
  ``!f g. (!x. f x <= g x) ==> !ls. MIN_LIST (MAP f ls) <= MIN_LIST (MAP g ls)``,
  rpt strip_tac >>
  Induct_on `ls` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[MIN_LIST_def] >>
  rw[MIN_LIST_def, MIN_LE_PAIR]);

(* Theorem: (!x. f x <= g x) ==> !ls n. EL n (MAP f ls) <= EL n (MAP g ls) *)
(* Proof:
   By induction on ls.
   Base: !n. EL n (MAP f []) <= EL n (MAP g [])
      LHS = EL n [] = RHS             by MAP
   Step: !n. EL n (MAP f ls) <= EL n (MAP g ls) ==>
         !h n. EL n (MAP f (h::ls)) <= EL n (MAP g (h::ls))
      If n = 0,
          EL 0 (MAP f (h::ls))
        = EL 0 (f h::MAP f ls)        by MAP
        = f h                         by EL
       <= g h                         by given
        = EL 0 (g h::MAP g ls)        by EL
        = EL 0 (MAP g (h::ls))        by MAP
      If n <> 0, then n = SUC k       by num_CASES
         EL n (MAP f (h::ls))
       = EL (SUC k) (f h::MAP f ls)   by MAP
       = EL k (MAP f ls)              by EL
      <= EL k (MAP g ls)              by induction hypothesis
       = EL (SUC k) (g h::MAP g ls)   by EL
       = EL n (MAP g (h::ls))         by MAP
*)
val MAP_LE = store_thm(
  "MAP_LE",
  ``!(f:num -> num) g. (!x. f x <= g x) ==> !ls n. EL n (MAP f ls) <= EL n (MAP g ls)``,
  ntac 3 strip_tac >>
  Induct_on `ls` >-
  rw[] >>
  Cases_on `n` >-
  rw[] >>
  rw[]);

(* Theorem: (!x y. f x y <= g x y) ==> !lx ly n. EL n (MAP2 f lx ly) <= EL n (MAP2 g lx ly) *)
(* Proof:
   By induction on lx.
   Base: !ly n. EL n (MAP2 f [] ly) <= EL n (MAP2 g [] ly)
      LHS = EL n [] = RHS             by MAP2_DEF
   Step: !ly n. EL n (MAP2 f lx ly) <= EL n (MAP2 g lx ly) ==>
         !h ly n. EL n (MAP2 f (h::lx) ly) <= EL n (MAP2 g (h::lx) ly)
      If ly = [],
         to show: EL n (MAP2 f (h::lx) []) <= EL n (MAP2 g (h::lx) [])
         True since LHS = EL n [] = RHS         by MAP2_DEF
      Otherwise, ly = h'::t.
         to show: EL n (MAP2 f (h::lx) (h'::t)) <= EL n (MAP2 g (h::lx) (h'::t))
         If n = 0,
             EL 0 (MAP2 f (h::lx) (h'::t))
           = EL 0 (f h h'::MAP2 f lx t)        by MAP2
           = f h h'                            by EL
          <= g h h'                            by given
           = EL 0 (g h h'::MAP2 g lx t)        by EL
           = EL 0 (MAP2 g (h::lx) (h'::t))     by MAP2
         If n <> 0, then n = SUC k             by num_CASES
            EL n (MAP2 f (h::lx) (h'::t))
          = EL (SUC k) (f h h'::MAP2 f lx t)   by MAP2
          = EL k (MAP2 f lx t)                 by EL
         <= EL k (MAP2 g lx t)                 by induction hypothesis
          = EL (SUC k) (g h h'::MAP2 g lx t)   by EL
          = EL n (MAP2 g (h::lx) (h'::t))      by MAP2
*)
val MAP2_LE = store_thm(
  "MAP2_LE",
  ``!(f:num -> num -> num) g. (!x y. f x y <= g x y) ==>
   !lx ly n. EL n (MAP2 f lx ly) <= EL n (MAP2 g lx ly)``,
  ntac 3 strip_tac >>
  Induct_on `lx` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ly` >-
  rw[] >>
  Cases_on `n` >-
  rw[] >>
  rw[]);

(* Theorem: (!x y z. f x y z <= g x y z) ==>
            !lx ly lz n. EL n (MAP3 f lx ly lz) <= EL n (MAP3 g lx ly lz) *)
(* Proof:
   By induction on lx.
   Base: !ly lz n. EL n (MAP3 f [] ly lz) <= EL n (MAP3 g [] ly lz)
      LHS = EL n [] = RHS             by MAP3_DEF
   Step: !ly lz n. EL n (MAP3 f lx ly lz) <= EL n (MAP3 g lx ly lz) ==>
         !h ly lz n. EL n (MAP3 f (h::lx) ly lz) <= EL n (MAP3 g (h::lx) ly lz)
      If ly = [],
         to show: EL n (MAP3 f (h::lx) [] lz) <= EL n (MAP3 g (h::lx) [] lz)
         True since LHS = EL n [] = RHS          by MAP3_DEF
      Otherwise, ly = h'::t.
         to show: EL n (MAP3 f (h::lx) (h'::t) lz) <= EL n (MAP3 g (h::lx) (h'::t) lz)
         If lz = [],
            to show: EL n (MAP3 f (h::lx) (h'::t) []) <= EL n (MAP3 g (h::lx) (h'::t) [])
            True since LHS = EL n [] = RHS       by MAP3_DEF
         Otherwise, lz = h''::t'.
            to show: EL n (MAP3 f (h::lx) (h'::t) (h''::t')) <= EL n (MAP3 g (h::lx) (h'::t) (h''::t'))
            If n = 0,
                EL 0 (MAP3 f (h::lx) (h'::t) (h''::t'))
              = EL 0 (f h h' h''::MAP3 f lx t t')        by MAP3
              = f h h' h''                               by EL
             <= g h h' h''                               by given
              = EL 0 (g h h' h''::MAP3 g lx t t')        by EL
              = EL 0 (MAP3 g (h::lx) (h'::t) (h''::t'))  by MAP3
            If n <> 0, then n = SUC k                    by num_CASES
               EL n (MAP3 f (h::lx) (h'::t) (h''::t'))
             = EL (SUC k) (f h h' h''::MAP3 f lx t t')   by MAP3
             = EL k (MAP3 f lx t t')                     by EL
            <= EL k (MAP3 g lx t t')                     by induction hypothesis
             = EL (SUC k) (g h h' h''::MAP3 g lx t t')   by EL
             = EL n (MAP3 g (h::lx) (h'::t) (h''::t'))   by MAP3
*)
val MAP3_LE = store_thm(
  "MAP3_LE",
  ``!(f:num -> num -> num -> num) g. (!x y z. f x y z <= g x y z) ==>
   !lx ly lz n. EL n (MAP3 f lx ly lz) <= EL n (MAP3 g lx ly lz)``,
  ntac 3 strip_tac >>
  Induct_on `lx` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ly` >-
  rw[] >>
  Cases_on `lz` >-
  rw[] >>
  Cases_on `n` >-
  rw[] >>
  rw[]);

(*
SUM_MAP_PLUS       |- !f g ls. SUM (MAP (\x. f x + g x) ls) = SUM (MAP f ls) + SUM (MAP g ls)
SUM_MAP_PLUS_ZIP   |- !ls1 ls2. LENGTH ls1 = LENGTH ls2 /\ (!x y. f (x,y) = g x + h y) ==>
                                SUM (MAP f (ZIP (ls1,ls2))) = SUM (MAP g ls1) + SUM (MAP h ls2)
*)

(* Theorem: (!x. f1 x <= f2 x) ==> !ls. SUM (MAP f1 ls) <= SUM (MAP f2 ls) *)
(* Proof:
   By SUM_LE, this is to show:
   (1) !k. k < LENGTH (MAP f1 ls) ==> EL k (MAP f1 ls) <= EL k (MAP f2 ls)
       This is true                by EL_MAP
   (2) LENGTH (MAP f1 ls) = LENGTH (MAP f2 ls)
       This is true                by LENGTH_MAP
*)
val SUM_MONO_MAP = store_thm(
  "SUM_MONO_MAP",
  ``!f1 f2. (!x. f1 x <= f2 x) ==> !ls. SUM (MAP f1 ls) <= SUM (MAP f2 ls)``,
  rpt strip_tac >>
  irule SUM_LE >>
  rw[EL_MAP]);

(* Theorem: (!x y. f1 x y <= f2 x y) ==> !lx ly. SUM (MAP2 f1 lx ly) <= SUM (MAP2 f2 lx ly) *)
(* Proof:
   By SUM_LE, this is to show:
   (1) !k. k < LENGTH (MAP2 f1 lx ly) ==> EL k (MAP2 f1 lx ly) <= EL k (MAP2 f2 lx ly)
       This is true                by EL_MAP2, LENGTH_MAP2
   (2) LENGTH (MAP2 f1 lx ly) = LENGTH (MAP2 f2 lx ly)
       This is true                by LENGTH_MAP2
*)
val SUM_MONO_MAP2 = store_thm(
  "SUM_MONO_MAP2",
  ``!f1 f2. (!x y. f1 x y <= f2 x y) ==> !lx ly. SUM (MAP2 f1 lx ly) <= SUM (MAP2 f2 lx ly)``,
  rpt strip_tac >>
  irule SUM_LE >>
  rw[EL_MAP2]);

(* Theorem: (!x y z. f1 x y z <= f2 x y z) ==> !lx ly lz. SUM (MAP3 f1 lx ly lz) <= SUM (MAP3 f2 lx ly lz) *)
(* Proof:
   By SUM_LE, this is to show:
   (1) !k. k < LENGTH (MAP3 f1 lx ly lz) ==> EL k (MAP3 f1 lx ly lz) <= EL k (MAP3 f2 lx ly lz)
       This is true                by EL_MAP3, LENGTH_MAP3
   (2)LENGTH (MAP3 f1 lx ly lz) = LENGTH (MAP3 f2 lx ly lz)
       This is true                by LENGTH_MAP3
*)
val SUM_MONO_MAP3 = store_thm(
  "SUM_MONO_MAP3",
  ``!f1 f2. (!x y z. f1 x y z <= f2 x y z) ==>
   !lx ly lz. SUM (MAP3 f1 lx ly lz) <= SUM (MAP3 f2 lx ly lz)``,
  rpt strip_tac >>
  irule SUM_LE >>
  rw[EL_MAP3, LENGTH_MAP3]);

(* Theorem: MONO f ==> !ls. SUM (MAP f ls) <= f (MAX_LIST ls) * LENGTH ls *)
(* Proof:
   Let c = f (MAX_LIST ls).

   Claim: SUM (MAP f ls) <= SUM (MAP (K c) ls)
   Proof: By SUM_LE, this is to show:
          (1) LENGTH (MAP f ls) = LENGTH (MAP (K c) ls)
              This is true                           by LENGTH_MAP
          (2) !k. k < LENGTH (MAP f ls) ==> EL k (MAP f ls) <= EL k (MAP (K c) ls)
              Note EL k (MAP f ls) = f (EL k ls)     by EL_MAP
               and EL k (MAP (K c) ls)
                 = (K c) (EL k ls)                   by EL_MAP
                 = c                                 by K_THM
               Now MEM (EL k ls) ls                  by EL_MEM
                so EL k ls <= MAX_LIST ls            by MAX_LIST_PROPERTY
              Thus f (EL k ls) <= c                  by property of f

   Note SUM (MAP (K c) ls) = c * LENGTH ls           by SUM_MAP_K
   Thus SUM (MAP f ls) <= c * LENGTH ls              by Claim
*)
val SUM_MAP_UPPER = store_thm(
  "SUM_MAP_UPPER",
  ``!f. MONO f ==> !ls. SUM (MAP f ls) <= f (MAX_LIST ls) * LENGTH ls``,
  rpt strip_tac >>
  qabbrev_tac `c = f (MAX_LIST ls)` >>
  `SUM (MAP f ls) <= SUM (MAP (K c) ls)` by
  ((irule SUM_LE >> rw[]) >>
  rw[EL_MAP, EL_MEM, MAX_LIST_PROPERTY, Abbr`c`]) >>
  `SUM (MAP (K c) ls) = c * LENGTH ls` by rw[SUM_MAP_K] >>
  decide_tac);

(* Theorem: MONO2 f ==>
            !lx ly. SUM (MAP2 f lx ly) <= (f (MAX_LIST lx) (MAX_LIST ly)) * LENGTH (MAP2 f lx ly) *)
(* Proof:
   Let c = f (MAX_LIST lx) (MAX_LIST ly).

   Claim: SUM (MAP2 f lx ly) <= SUM (MAP2 (\x y. c) lx ly)
   Proof: By SUM_LE, this is to show:
          (1) LENGTH (MAP2 f lx ly) = LENGTH (MAP2 (\x y. c) lx ly)
              This is true                           by LENGTH_MAP2
          (2) !k. k < LENGTH (MAP2 f lx ly) ==> EL k (MAP2 f lx ly) <= EL k (MAP2 (\x y. c) lx ly)
              Note EL k (MAP2 f lx ly)
                 = f (EL k lx) (EL k ly)             by EL_MAP2
               and EL k (MAP2 (\x y. c) lx ly)
                 = (\x y. c) (EL k lx) (EL k ly)     by EL_MAP2
                 = c                                 by function application
              Note k < LENGTH lx, k < LENGTH ly      by LENGTH_MAP2
               Now MEM (EL k lx) lx                  by EL_MEM
               and MEM (EL k ly) ly                  by EL_MEM
                so EL k lx <= MAX_LIST lx            by MAX_LIST_PROPERTY
               and EL k ly <= MAX_LIST ly            by MAX_LIST_PROPERTY
              Thus f (EL k lx) (EL k ly) <= c        by property of f

   Note SUM (MAP (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly)  by SUM_MAP2_K
    and LENGTH (MAP2 (\x y. c) lx ly) = LENGTH (MAP2 f lx ly)          by LENGTH_MAP2
   Thus SUM (MAP f lx ly) <= c * LENGTH (MAP2 f lx ly)                 by Claim
*)
val SUM_MAP2_UPPER = store_thm(
  "SUM_MAP2_UPPER",
  ``!f. MONO2 f ==>
   !lx ly. SUM (MAP2 f lx ly) <= (f (MAX_LIST lx) (MAX_LIST ly)) * LENGTH (MAP2 f lx ly)``,
  rpt strip_tac >>
  qabbrev_tac `c = f (MAX_LIST lx) (MAX_LIST ly)` >>
  `SUM (MAP2 f lx ly) <= SUM (MAP2 (\x y. c) lx ly)` by
  ((irule SUM_LE >> rw[]) >>
  rw[EL_MAP2, EL_MEM, MAX_LIST_PROPERTY, Abbr`c`]) >>
  `SUM (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 (\x y. c) lx ly)` by rw[SUM_MAP2_K, Abbr`c`] >>
  `c * LENGTH (MAP2 (\x y. c) lx ly) = c * LENGTH (MAP2 f lx ly)` by rw[] >>
  decide_tac);

(* Theorem: MONO3 f ==>
           !lx ly lz. SUM (MAP3 f lx ly lz) <=
                      f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz) * LENGTH (MAP3 f lx ly lz) *)
(* Proof:
   Let c = f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz).

   Claim: SUM (MAP3 f lx ly lz) <= SUM (MAP3 (\x y z. c) lx ly lz)
   Proof: By SUM_LE, this is to show:
          (1) LENGTH (MAP3 f lx ly lz) = LENGTH (MAP3 (\x y z. c) lx ly lz)
              This is true                           by LENGTH_MAP3
          (2) !k. k < LENGTH (MAP3 f lx ly lz) ==> EL k (MAP3 f lx ly lz) <= EL k (MAP3 (\x y z. c) lx ly lz)
              Note EL k (MAP3 f lx ly lz)
                 = f (EL k lx) (EL k ly) (EL k lz)   by EL_MAP3
               and EL k (MAP3 (\x y z. c) lx ly lz)
                 = (\x y z. c) (EL k lx) (EL k ly) (EL k lz)  by EL_MAP3
                 = c                                 by function application
              Note k < LENGTH lx, k < LENGTH ly, k < LENGTH lz
                                                     by LENGTH_MAP3
               Now MEM (EL k lx) lx                  by EL_MEM
               and MEM (EL k ly) ly                  by EL_MEM
               and MEM (EL k lz) lz                  by EL_MEM
                so EL k lx <= MAX_LIST lx            by MAX_LIST_PROPERTY
               and EL k ly <= MAX_LIST ly            by MAX_LIST_PROPERTY
               and EL k lz <= MAX_LIST lz            by MAX_LIST_PROPERTY
              Thus f (EL k lx) (EL k ly) (EL k lz) <= c  by property of f

   Note SUM (MAP (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz)   by SUM_MAP3_K
    and LENGTH (MAP3 (\x y z. c) lx ly lz) = LENGTH (MAP3 f lx ly lz)             by LENGTH_MAP3
   Thus SUM (MAP f lx ly lz) <= c * LENGTH (MAP3 f lx ly lz)                      by Claim
*)
val SUM_MAP3_UPPER = store_thm(
  "SUM_MAP3_UPPER",
  ``!f. MONO3 f ==>
   !lx ly lz. SUM (MAP3 f lx ly lz) <= f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz) * LENGTH (MAP3 f lx ly lz)``,
  rpt strip_tac >>
  qabbrev_tac `c = f (MAX_LIST lx) (MAX_LIST ly) (MAX_LIST lz)` >>
  `SUM (MAP3 f lx ly lz) <= SUM (MAP3 (\x y z. c) lx ly lz)` by
  (`LENGTH (MAP3 f lx ly lz) = LENGTH (MAP3 (\x y z. c) lx ly lz)` by rw[LENGTH_MAP3] >>
  (irule SUM_LE >> rw[]) >>
  fs[LENGTH_MAP3] >>
  rw[EL_MAP3, EL_MEM, MAX_LIST_PROPERTY, Abbr`c`]) >>
  `SUM (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 (\x y z. c) lx ly lz)` by rw[SUM_MAP3_K] >>
  `c * LENGTH (MAP3 (\x y z. c) lx ly lz) = c * LENGTH (MAP3 f lx ly lz)` by rw[LENGTH_MAP3] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Increasing and decreasing list bounds                                     *)
(* ------------------------------------------------------------------------- *)

(* Overload increasing list and decreasing list *)
val _ = overload_on("MONO_INC",
          ``\ls:num list. !m n. m <= n /\ n < LENGTH ls ==> EL m ls <= EL n ls``);
val _ = overload_on("MONO_DEC",
          ``\ls:num list. !m n. m <= n /\ n < LENGTH ls ==> EL n ls <= EL m ls``);

(* Theorem: MONO_INC []*)
(* Proof: no member to falsify. *)
Theorem MONO_INC_NIL:
  MONO_INC []
Proof
  simp[]
QED

(* Theorem: MONO_INC (h::t) ==> MONO_INC t *)
(* Proof:
   This is to show: m <= n /\ n < LENGTH t ==> EL m t <= EL n t
   Note m <= n <=> SUC m <= SUC n              by arithmetic
    and n < LENGTH t <=> SUC n < LENGTH (h::t) by LENGTH
   Thus EL (SUC m) (h::t) <= EL (SUC n) (h::t) by MONO_INC (h::t)
     or            EL m t <= EL n t            by EL
*)
Theorem MONO_INC_CONS:
  !h t. MONO_INC (h::t) ==> MONO_INC t
Proof
  rw[] >>
  first_x_assum (qspecl_then [`SUC m`, `SUC n`] strip_assume_tac) >>
  rfs[]
QED

(* Theorem: MONO_INC (h::t) /\ MEM x t ==> h <= x *)
(* Proof:
   Note MEM x t
    ==> ?n. n < LENGTH t /\ x = EL n t         by MEM_EL
     or SUC n < SUC (LENGTH t)                 by inequality
    Now 0 < SUC n, or 0 <= SUC n,
    and SUC n < SUC (LENGTH t) = LENGTH (h::t) by LENGTH
     so EL 0 (h::t) <= EL (SUC n) (h::t)       by MONO_INC (h::t)
     or           h <= EL n t = x              by EL
*)
Theorem MONO_INC_HD:
  !h t x. MONO_INC (h::t) /\ MEM x t ==> h <= x
Proof
  rpt strip_tac >>
  fs[MEM_EL] >>
  last_x_assum (qspecl_then [`0`,`SUC n`] strip_assume_tac) >>
  rfs[]
QED

(* Theorem: MONO_DEC []*)
(* Proof: no member to falsify. *)
Theorem MONO_DEC_NIL:
  MONO_DEC []
Proof
  simp[]
QED

(* Theorem: MONO_DEC (h::t) ==> MONO_DEC t *)
(* Proof:
   This is to show: m <= n /\ n < LENGTH t ==> EL n t <= EL m t
   Note m <= n <=> SUC m <= SUC n              by arithmetic
    and n < LENGTH t <=> SUC n < LENGTH (h::t) by LENGTH
   Thus EL (SUC n) (h::t) <= EL (SUC m) (h::t) by MONO_DEC (h::t)
     or            EL n t <= EL m t            by EL
*)
Theorem MONO_DEC_CONS:
  !h t. MONO_DEC (h::t) ==> MONO_DEC t
Proof
  rw[] >>
  first_x_assum (qspecl_then [`SUC m`, `SUC n`] strip_assume_tac) >>
  rfs[]
QED

(* Theorem: MONO_DEC (h::t) /\ MEM x t ==> x <= h *)
(* Proof:
   Note MEM x t
    ==> ?n. n < LENGTH t /\ x = EL n t         by MEM_EL
     or SUC n < SUC (LENGTH t)                 by inequality
    Now 0 < SUC n, or 0 <= SUC n,
    and SUC n < SUC (LENGTH t) = LENGTH (h::t) by LENGTH
     so EL (SUC n) (h::t) <= EL 0 (h::t)       by MONO_DEC (h::t)
     or        x = EL n t <= h                 by EL
*)
Theorem MONO_DEC_HD:
  !h t x. MONO_DEC (h::t) /\ MEM x t ==> x <= h
Proof
  rpt strip_tac >>
  fs[MEM_EL] >>
  last_x_assum (qspecl_then [`0`,`SUC n`] strip_assume_tac) >>
  rfs[]
QED

(* Theorem: MONO f ==> MONO_INC (GENLIST f n) *)
(* Proof:
   Let ls = GENLIST f n.
   Then LENGTH ls = n                 by LENGTH_GENLIST
    and !k. k < n ==> EL k ls = f k   by EL_GENLIST
   Thus MONO_INC ls
*)
val GENLIST_MONO_INC = store_thm(
  "GENLIST_MONO_INC",
  ``!f:num -> num n. MONO f ==> MONO_INC (GENLIST f n)``,
  rw[]);

(* Theorem: RMONO f ==> MONO_DEC (GENLIST f n) *)
(* Proof:
   Let ls = GENLIST f n.
   Then LENGTH ls = n                 by LENGTH_GENLIST
    and !k. k < n ==> EL k ls = f k   by EL_GENLIST
   Thus MONO_DEC ls
*)
val GENLIST_MONO_DEC = store_thm(
  "GENLIST_MONO_DEC",
  ``!f:num -> num n. RMONO f ==> MONO_DEC (GENLIST f n)``,
  rw[]);

(* Theorem: ls <> [] /\ (!m n. m <= n ==> EL m ls <= EL n ls) ==> (MAX_LIST ls = LAST ls) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] /\ MONO_INC [] ==> MAX_LIST [] = LAST []
       Note [] <> [] = F, hence true.
   Step: ls <> [] /\ MONO_INC ls ==> MAX_LIST ls = LAST ls ==>
         !h. h::ls <> [] /\ MONO_INC (h::ls) ==> MAX_LIST (h::ls) = LAST (h::ls)
       If ls = [],
         LHS = MAX_LIST [h] = h        by MAX_LIST_def
         RHS = LAST [h] = h = LHS      by LAST_DEF
       If ls <> [],
         Note h <= LAST ls             by LAST_EL_CONS, increasing property
          and MONO_INC ls              by EL, m <= n ==> SUC m <= SUC n
         MAX_LIST (h::ls)
       = MAX h (MAX_LIST ls)           by MAX_LIST_def
       = MAX h (LAST ls)               by induction hypothesis
       = LAST ls                       by MAX_DEF, h <= LAST ls
       = LAST (h::ls)                  by LAST_DEF
*)
val MAX_LIST_MONO_INC = store_thm(
  "MAX_LIST_MONO_INC",
  ``!ls. ls <> [] /\ MONO_INC ls ==> (MAX_LIST ls = LAST ls)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `h <= LAST ls` by
  (`LAST ls = EL (LENGTH ls) (h::ls)` by rw[LAST_EL_CONS] >>
  `h = EL 0 (h::ls)` by rw[] >>
  `LENGTH ls < LENGTH (h::ls)` by rw[] >>
  metis_tac[DECIDE``0 <= n``]) >>
  `MONO_INC ls` by
    (rpt strip_tac >>
  `SUC m <= SUC n` by decide_tac >>
  `EL (SUC m) (h::ls) <= EL (SUC n) (h::ls)` by rw[] >>
  fs[]) >>
  rw[MAX_DEF, LAST_DEF]);

(* Theorem: ls <> [] /\ MONO_DEC ls ==> (MAX_LIST ls = HD ls) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] /\ MONO_DEC [] ==> MAX_LIST [] = HD []
       Note [] <> [] = F, hence true.
   Step: ls <> [] /\ MONO_DEC ls ==> MAX_LIST ls = HD ls ==>
         !h. h::ls <> [] /\ MONO_DEC (h::ls) ==> MAX_LIST (h::ls) = HD (h::ls)
       If ls = [],
         LHS = MAX_LIST [h] = h        by MAX_LIST_def
         RHS = HD [h] = h = LHS        by HD
       If ls <> [],
         Note HD ls <= h               by HD, decreasing property
          and MONO_DEC ls              by EL, m <= n ==> SUC m <= SUC n
         MAX_LIST (h::ls)
       = MAX h (MAX_LIST ls)           by MAX_LIST_def
       = MAX h (HD ls)                 by induction hypothesis
       = h                             by MAX_DEF, HD ls <= h
       = HD (h::ls)                    by HD
*)
val MAX_LIST_MONO_DEC = store_thm(
  "MAX_LIST_MONO_DEC",
  ``!ls. ls <> [] /\ MONO_DEC ls ==> (MAX_LIST ls = HD ls)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `HD ls <= h` by
  (`HD ls = EL 1 (h::ls)` by rw[] >>
  `h = EL 0 (h::ls)` by rw[] >>
  `0 < LENGTH ls` by metis_tac[LENGTH_EQ_0, NOT_ZERO_LT_ZERO] >>
  `1 < LENGTH (h::ls)` by rw[] >>
  metis_tac[DECIDE``0 <= 1``]) >>
  `MONO_DEC ls` by
    (rpt strip_tac >>
  `SUC m <= SUC n` by decide_tac >>
  `EL (SUC n) (h::ls) <= EL (SUC m) (h::ls)` by rw[] >>
  fs[]) >>
  rw[MAX_DEF]);

(* Theorem: ls <> [] /\ MONO_INC ls ==> (MIN_LIST ls = HD ls) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] /\ MONO_INC [] ==> MIN_LIST [] = HD []
       Note [] <> [] = F, hence true.
   Step: ls <> [] /\ MONO_INC ls ==> MIN_LIST ls = HD ls ==>
         !h. h::ls <> [] /\ MONO_INC (h::ls) ==> MIN_LIST (h::ls) = HD (h::ls)
       If ls = [],
         LHS = MIN_LIST [h] = h        by MIN_LIST_def
         RHS = HD [h] = h = LHS        by HD
       If ls <> [],
         Note h <= HD ls               by HD, increasing property
          and MONO_INC ls              by EL, m <= n ==> SUC m <= SUC n
         MIN_LIST (h::ls)
       = MIN h (MIN_LIST ls)           by MIN_LIST_def
       = MIN h (HD ls)                 by induction hypothesis
       = h                             by MIN_DEF, h <= HD ls
       = HD (h::ls)                    by HD
*)
val MIN_LIST_MONO_INC = store_thm(
  "MIN_LIST_MONO_INC",
  ``!ls. ls <> [] /\ MONO_INC ls ==> (MIN_LIST ls = HD ls)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `h <= HD ls` by
  (`HD ls = EL 1 (h::ls)` by rw[] >>
  `h = EL 0 (h::ls)` by rw[] >>
  `0 < LENGTH ls` by metis_tac[LENGTH_EQ_0, NOT_ZERO_LT_ZERO] >>
  `1 < LENGTH (h::ls)` by rw[] >>
  metis_tac[DECIDE``0 <= 1``]) >>
  `MONO_INC ls` by
    (rpt strip_tac >>
  `SUC m <= SUC n` by decide_tac >>
  `EL (SUC m) (h::ls) <= EL (SUC n) (h::ls)` by rw[] >>
  fs[]) >>
  rw[MIN_DEF]);

(* Theorem: ls <> [] /\ MONO_DEC ls ==> (MIN_LIST ls = LAST ls) *)
(* Proof:
   By induction on ls.
   Base: [] <> [] /\ MONO_DEC [] ==> MIN_LIST [] = LAST []
       Note [] <> [] = F, hence true.
   Step: ls <> [] /\ MONO_DEC ls ==> MIN_LIST ls = LAST ls ==>
         !h. h::ls <> [] /\ MONO_DEC (h::ls) ==> MAX_LIST (h::ls) = LAST (h::ls)
       If ls = [],
         LHS = MIN_LIST [h] = h        by MIN_LIST_def
         RHS = LAST [h] = h = LHS      by LAST_DEF
       If ls <> [],
         Note LAST ls <= h             by LAST_EL_CONS, decreasing property
          and MONO_DEC ls              by EL, m <= n ==> SUC m <= SUC n
         MIN_LIST (h::ls)
       = MIN h (MIN_LIST ls)           by MIN_LIST_def
       = MIN h (LAST ls)               by induction hypothesis
       = LAST ls                       by MIN_DEF, LAST ls <= h
       = LAST (h::ls)                  by LAST_DEF
*)
val MIN_LIST_MONO_DEC = store_thm(
  "MIN_LIST_MONO_DEC",
  ``!ls. ls <> [] /\ MONO_DEC ls ==> (MIN_LIST ls = LAST ls)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `ls = []` >-
  rw[] >>
  `LAST ls <= h` by
  (`LAST ls = EL (LENGTH ls) (h::ls)` by rw[LAST_EL_CONS] >>
  `h = EL 0 (h::ls)` by rw[] >>
  `LENGTH ls < LENGTH (h::ls)` by rw[] >>
  metis_tac[DECIDE``0 <= n``]) >>
  `MONO_DEC ls` by
    (rpt strip_tac >>
  `SUC m <= SUC n` by decide_tac >>
  `EL (SUC n) (h::ls) <= EL (SUC m) (h::ls)` by rw[] >>
  fs[]) >>
  rw[MIN_DEF, LAST_DEF]);

(* Theorem: MONO_INC [m .. n] *)
(* Proof:
   This is to show:
        !j k. j <= k /\ k < LENGTH [m .. n] ==> EL j [m .. n] <= EL k [m .. n]
   Note LENGTH [m .. n] = n + 1 - m            by listRangeINC_LEN
     so m + j <= n                             by j < LENGTH [m .. n]
    ==> EL j [m .. n] = m + j                  by listRangeINC_EL
   also m + k <= n                             by k < LENGTH [m .. n]
    ==> EL k [m .. n] = m + k                  by listRangeINC_EL
   Thus EL j [m .. n] <= EL k [m .. n]         by arithmetic
*)
Theorem listRangeINC_MONO_INC:
  !m n. MONO_INC [m .. n]
Proof
  simp[listRangeINC_EL, listRangeINC_LEN]
QED

(* Theorem: MONO_INC [m ..< n] *)
(* Proof:
   This is to show:
        !j k. j <= k /\ k < LENGTH [m ..< n] ==> EL j [m ..< n] <= EL k [m ..< n]
   Note LENGTH [m ..< n] = n - m               by listRangeLHI_LEN
     so m + j < n                              by j < LENGTH [m ..< n]
    ==> EL j [m ..< n] = m + j                 by listRangeLHI_EL
   also m + k < n                              by k < LENGTH [m ..< n]
    ==> EL k [m ..< n] = m + k                 by listRangeLHI_EL
   Thus EL j [m ..< n] <= EL k [m ..< n]       by arithmetic
*)
Theorem listRangeLHI_MONO_INC:
  !m n. MONO_INC [m ..< n]
Proof
  simp[listRangeLHI_EL]
QED

(* ------------------------------------------------------------------------- *)
(* List Dilation                                                             *)
(* ------------------------------------------------------------------------- *)

(*
Use the concept of dilating a list.

Let p = [1;2;3], that is, p = 1 + 2x + 3x^2.
Then q = peval p (x^3) is just q = 1 + 2(x^3) + 3(x^3)^2 = [1;0;0;2;0;0;3]

DILATE 3 [] = []
DILATE 3 (h::t) = [h;0;0] ++ MDILATE 3 t

val DILATE_3_DEF = Define`
   (DILATE_3 [] = []) /\
   (DILATE_3 (h::t) = [h;0;0] ++ (MDILATE_3 t))
`;
> EVAL ``DILATE_3 [1;2;3]``;
val it = |- MDILATE_3 [1; 2; 3] = [1; 0; 0; 2; 0; 0; 3; 0; 0]: thm

val DILATE_3_DEF = Define`
   (DILATE_3 [] = []) /\
   (DILATE_3 [h] = [h]) /\
   (DILATE_3 (h::t) = [h;0;0] ++ (MDILATE_3 t))
`;
> EVAL ``DILATE_3 [1;2;3]``;
val it = |- MDILATE_3 [1; 2; 3] = [1; 0; 0; 2; 0; 0; 3]: thm
*)

(* ------------------------------------------------------------------------- *)
(* List Dilation (Multiplicative)                                            *)
(* ------------------------------------------------------------------------- *)

(* Note:
   It would be better to define:  MDILATE e n l = inserting n (e)'s,
   that is, using GENLIST (K e) n, so that only MDILATE e 0 l = l.
   However, the intention is to have later, for polynomials:
       peval p (X ** n) = pdilate n p
   and since X ** 1 = X, and peval p X = p,
   it is desirable to have MDILATE e 1 l = l, with the definition below.

   However, the multiplicative feature at the end destroys such an application.
*)

(* Dilate a list with an element e, for a factor n (n <> 0) *)
val MDILATE_def = Define`
   (MDILATE e n [] = []) /\
   (MDILATE e n (h::t) = if t = [] then [h] else (h:: GENLIST (K e) (PRE n)) ++ (MDILATE e n t))
`;
(*
> EVAL ``MDILATE 0 2 [1;2;3]``;
val it = |- MDILATE 0 2 [1; 2; 3] = [1; 0; 2; 0; 3]: thm
> EVAL ``MDILATE 0 3 [1;2;3]``;
val it = |- MDILATE 0 3 [1; 2; 3] = [1; 0; 0; 2; 0; 0; 3]: thm
> EVAL ``MDILATE #0 3 [a;b;#1]``;
val it = |- MDILATE #0 3 [a; b; #1] = [a; #0; #0; b; #0; #0; #1]: thm
*)

(* Theorem: MDILATE e n [] = [] *)
(* Proof: by MDILATE_def *)
val MDILATE_NIL = store_thm(
  "MDILATE_NIL",
  ``!e n. MDILATE e n [] = []``,
  rw[MDILATE_def]);

(* export simple result *)
val _ = export_rewrites["MDILATE_NIL"];

(* Theorem: MDILATE e n [x] = [x] *)
(* Proof: by MDILATE_def *)
val MDILATE_SING = store_thm(
  "MDILATE_SING",
  ``!e n x. MDILATE e n [x] = [x]``,
  rw[MDILATE_def]);

(* export simple result *)
val _ = export_rewrites["MDILATE_SING"];

(* Theorem: MDILATE e n (h::t) =
            if t = [] then [h] else (h:: GENLIST (K e) (PRE n)) ++ (MDILATE e n t) *)
(* Proof: by MDILATE_def *)
val MDILATE_CONS = store_thm(
  "MDILATE_CONS",
  ``!e n h t. MDILATE e n (h::t) =
    if t = [] then [h] else (h:: GENLIST (K e) (PRE n)) ++ (MDILATE e n t)``,
  rw[MDILATE_def]);

(* Theorem: MDILATE e 1 l = l *)
(* Proof:
   By induction on l.
   Base: !e. MDILATE e 1 [] = [], true     by MDILATE_NIL
   Step: !e. MDILATE e 1 l = l ==> !h e. MDILATE e 1 (h::l) = h::l
      If l = [],
        MDILATE e 1 [h]
      = [h]                                by MDILATE_SING
      If l <> [],
        MDILATE e 1 (h::l)
      = (h:: GENLIST (K e) (PRE 1)) ++ (MDILATE e n l)   by MDILATE_CONS
      = (h:: GENLIST (K e) (PRE 1)) ++ l   by induction hypothesis
      = (h:: GENLIST (K e) 0) ++ l         by PRE
      = [h] ++ l                           by GENLIST_0
      = h::l                               by CONS_APPEND
*)
val MDILATE_1 = store_thm(
  "MDILATE_1",
  ``!l e. MDILATE e 1 l = l``,
  Induct_on `l` >>
  rw[MDILATE_def]);

(* Theorem: MDILATE e 0 l = l *)
(* Proof:
   By induction on l, and note GENLIST (K e) (PRE 0) = GENLIST (K e) 0 = [].
*)
val MDILATE_0 = store_thm(
  "MDILATE_0",
  ``!l e. MDILATE e 0 l = l``,
  Induct_on `l` >> rw[MDILATE_def]);

(* Theorem: LENGTH (MDILATE e n l) =
            if n = 0 then LENGTH l else if l = [] then 0 else SUC (n * PRE (LENGTH l)) *)
(* Proof:
   If n = 0,
      Then MDILATE e 0 l = l       by MDILATE_0
      Hence true.
   If n <> 0,
      Then 0 < n                   by NOT_ZERO_LT_ZERO
   By induction on l.
   Base: LENGTH (MDILATE e n []) = if n = 0 then LENGTH [] else if [] = [] then 0 else SUC (n * PRE (LENGTH []))
       LENGTH (MDILATE e n [])
     = LENGTH []                   by MDILATE_NIL
     = 0                           by LENGTH_NIL
   Step: LENGTH (MDILATE e n l) = if n = 0 then LENGTH l else if l = [] then 0 else SUC (n * PRE (LENGTH l)) ==>
         !h. LENGTH (MDILATE e n (h::l)) = if n = 0 then LENGTH (h::l) else if h::l = [] then 0 else SUC (n * PRE (LENGTH (h::l)))
       Note h::l = [] <=> F           by NOT_CONS_NIL
       If l = [],
         LENGTH (MDILATE e n [h])
       = LENGTH [h]                   by MDILATE_SING
       = 1                            by LENGTH_EQ_1
       = SUC 0                        by ONE
       = SUC (n * 0)                  by MULT_0
       = SUC (n * (PRE (LENGTH [h]))) by LENGTH_EQ_1, PRE_SUC_EQ
       If l <> [],
         Then LENGTH l <> 0           by LENGTH_NIL
         LENGTH (MDILATE e n (h::l))
       = LENGTH (h:: GENLIST (K e) (PRE n) ++ MDILATE e n l)          by MDILATE_CONS
       = LENGTH (h:: GENLIST (K e) (PRE n)) + LENGTH (MDILATE e n l)  by LENGTH_APPEND
       = n + LENGTH (MDILATE e n l)       by LENGTH_GENLIST
       = n + SUC (n * PRE (LENGTH l))     by induction hypothesis
       = SUC (n + n * PRE (LENGTH l))     by ADD_SUC
       = SUC (n * SUC (PRE (LENGTH l)))   by MULT_SUC
       = SUC (n * LENGTH l)               by SUC_PRE, 0 < LENGTH l
       = SUC (n * PRE (LENGTH (h::l)))    by LENGTH, PRE_SUC_EQ
*)
val MDILATE_LENGTH = store_thm(
  "MDILATE_LENGTH",
  ``!l e n. LENGTH (MDILATE e n l) =
   if n = 0 then LENGTH l else if l = [] then 0 else SUC (n * PRE (LENGTH l))``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[MDILATE_0] >>
  `0 < n` by decide_tac >>
  Induct_on `l` >-
  rw[] >>
  rw[MDILATE_def] >>
  `LENGTH l <> 0` by metis_tac[LENGTH_NIL] >>
  `0 < LENGTH l` by decide_tac >>
  `PRE n + SUC (n * PRE (LENGTH l)) = SUC (PRE n) + n * PRE (LENGTH l)` by rw[] >>
  `_ = n + n * PRE (LENGTH l)` by decide_tac >>
  `_ = n * SUC (PRE (LENGTH l))` by rw[MULT_SUC] >>
  `_ = n * LENGTH l` by metis_tac[SUC_PRE] >>
  decide_tac);

(* Theorem: LENGTH l <= LENGTH (MDILATE e n l) *)
(* Proof:
   If n = 0,
        LENGTH (MDILATE e 0 l)
      = LENGTH l                       by MDILATE_LENGTH
      >= LENGTH l
   If l = [],
        LENGTH (MDILATE e n [])
      = LENGTH []                      by MDILATE_NIL
      >= LENGTH []
   If l <> [],
      Then ?h t. l = h::t              by list_CASES
        LENGTH (MDILATE e n (h::t))
      = SUC (n * PRE (LENGTH (h::t)))  by MDILATE_LENGTH
      = SUC (n * PRE (SUC (LENGTH t))) by LENGTH
      = SUC (n * LENGTH t)             by PRE
      = n * LENGTH t + 1               by ADD1
      >= LENGTH t + 1                  by LE_MULT_CANCEL_LBARE, 0 < n
      = SUC (LENGTH t)                 by ADD1
      = LENGTH (h::t)                  by LENGTH
*)
val MDILATE_LENGTH_LOWER = store_thm(
  "MDILATE_LENGTH_LOWER",
  ``!l e n. LENGTH l <= LENGTH (MDILATE e n l)``,
  rw[MDILATE_LENGTH] >>
  `?h t. l = h::t` by metis_tac[list_CASES] >>
  rw[]);

(* Theorem: 0 < n ==> LENGTH (MDILATE e n l) <= SUC (n * PRE (LENGTH l)) *)
(* Proof:
   Since n <> 0,
   If l = [],
        LENGTH (MDILATE e n [])
      = LENGTH []                  by MDILATE_NIL
      = 0                          by LENGTH_NIL
        SUC (n * PRE (LENGTH []))
      = SUC (n * PRE 0)            by LENGTH_NIL
      = SUC 0                      by PRE, MULT_0
      > 0                          by LESS_SUC
   If l <> [],
        LENGTH (MDILATE e n l)
      = SUC (n * PRE (LENGTH l))   by MDILATE_LENGTH, n <> 0
*)
val MDILATE_LENGTH_UPPER = store_thm(
  "MDILATE_LENGTH_UPPER",
  ``!l e n. 0 < n ==> LENGTH (MDILATE e n l) <= SUC (n * PRE (LENGTH l))``,
  rw[MDILATE_LENGTH]);

(* Theorem: k < LENGTH (MDILATE e n l) ==>
            (EL k (MDILATE e n l) = if n = 0 then EL k l else if k MOD n = 0 then EL (k DIV n) l else e) *)
(* Proof:
   If n = 0,
      Then MDILATE e 0 l = l     by MDILATE_0
      Hence true trivially.
   If n <> 0,
      Then 0 < n                 by NOT_ZERO_LT_ZERO
   By induction on l.
   Base: !k. k < LENGTH (MDILATE e n []) ==>
         (EL k (MDILATE e n []) = if n = 0 then EL k [] else if k MOD n = 0 then EL (k DIV n) [] else e)
      Note LENGTH (MDILATE e n [])
         = LENGTH []         by MDILATE_NIL
         = 0                 by LENGTH_NIL
      Thus k < 0 <=> F       by NOT_ZERO_LT_ZERO
   Step: !k. k < LENGTH (MDILATE e n l) ==> (EL k (MDILATE e n l) = if n = 0 then EL k l else if k MOD n = 0 then EL (k DIV n) l else e) ==>
         !h k. k < LENGTH (MDILATE e n (h::l)) ==> (EL k (MDILATE e n (h::l)) = if n = 0 then EL k (h::l) else if k MOD n = 0 then EL (k DIV n) (h::l) else e)
      Note LENGTH (MDILATE e n [h]) = 1    by MDILATE_SING
       and LENGTH (MDILATE e n (h::l))
         = SUC (n * PRE (LENGTH (h::l)))   by MDILATE_LENGTH, n <> 0
         = SUC (n * PRE (SUC (LENGTH l)))  by LENGTH
         = SUC (n * LENGTH l)              by PRE

      If l = [],
        Then MDILATE e n [h] = [h]         by MDILATE_SING
         and LENGTH (MDILATE e n [h]) = 1  by LENGTH
          so k < 1 means k = 0.
         and 0 DIV n = 0                   by ZERO_DIV, 0 < n
         and 0 MOD n = 0                   by ZERO_MOD, 0 < n
        Thus EL k [h] = EL (k DIV n) [h].

      If l <> [],
        Let t = h::GENLIST (K e) (PRE n)
        Note LENGTH t = n                  by LENGTH_GENLIST
        If k < n,
           Then k MOD n = k                by LESS_MOD, k < n
             EL k (MDILATE e n (h::l))
           = EL k (t ++ MDILATE e n l)     by MDILATE_CONS
           = EL k t                        by EL_APPEND, k < LENGTH t
           If k = 0,
              EL 0 t
            = EL 0 (h:: GENLIST (K e) (PRE n))  by notation of t
            = h
            = EL (0 DIV n) (h::l)          by EL, HD
           If k <> 0,
              EL k t
            = EL k (h:: GENLIST (K e) (PRE n))    by notation of t
            = EL (PRE k) (GENLIST (K e) (PRE n))  by EL_CONS
            = (K e) (PRE k)                by EL_GENLIST, PRE k < PRE n
            = e                            by application of K
        If ~(k < n), n <= k.
           Given k < LENGTH (MDILATE e n (h::l))
              or k < SUC (n * LENGTH l)    by above
             ==> k - n < SUC (n * LENGTH l) - n      by n <= k
                       = SUC (n * LENGTH l - n)      by SUB
                       = SUC (n * (LENGTH l - 1))    by LEFT_SUB_DISTRIB
                       = SUC (n * PRE (LENGTH l))    by PRE_SUB1
              or k - n < LENGTH (MDILATE e n l)      by MDILATE_LENGTH
            Thus (k - n) MOD n = k MOD n             by SUB_MOD
             and (k - n) DIV n = k DIV n - 1         by SUB_DIV
          If k MOD n = 0,
             Note 0 < k DIV n                        by DIVIDES_MOD_0, DIV_POS
             EL k (t ++ MDILATE e n l)
           = EL (k - n) (MDILATE e n l)              by EL_APPEND, n <= k
           = EL (k DIV n - 1) l                      by induction hypothesis, (k - n) MOD n = 0
           = EL (PRE (k DIV n)) l                    by PRE_SUB1
           = EL (k DIV n) (h::l)                     by EL_CONS, 0 < k DIV n
          If k MOD n <> 0,
             EL k (t ++ MDILATE e n l)
           = EL (k - n) (MDILATE e n l)              by EL_APPEND, n <= k
           = e                                       by induction hypothesis, (k - n) MOD n <> 0
*)
val MDILATE_EL = store_thm(
  "MDILATE_EL",
  ``!l e n k. k < LENGTH (MDILATE e n l) ==>
      (EL k (MDILATE e n l) = if n = 0 then EL k l else if k MOD n = 0 then EL (k DIV n) l else e)``,
  ntac 3 strip_tac >>
  Cases_on `n = 0` >-
  rw[MDILATE_0] >>
  `0 < n` by decide_tac >>
  Induct_on `l` >-
  rw[] >>
  rpt strip_tac >>
  `LENGTH (MDILATE e n [h]) = 1` by rw[MDILATE_SING] >>
  `LENGTH (MDILATE e n (h::l)) = SUC (n * LENGTH l)` by rw[MDILATE_LENGTH] >>
  qabbrev_tac `t = h:: GENLIST (K e) (PRE n)` >>
  `!k. k < 1 <=> (k = 0)` by decide_tac >>
  rw_tac std_ss[MDILATE_def] >-
  metis_tac[ZERO_DIV] >-
  metis_tac[ZERO_MOD] >-
 (rw_tac std_ss[EL_APPEND] >| [
    `LENGTH t = n` by rw[Abbr`t`] >>
    `k MOD n = k` by rw[LESS_MOD] >>
    `!x. EL 0 (h::x) = h` by rw[] >>
    metis_tac[ZERO_DIV],
    `LENGTH t = n` by rw[Abbr`t`] >>
    `k - n < LENGTH (MDILATE e n l)` by rw[MDILATE_LENGTH] >>
    `(k - n) MOD n = k MOD n` by rw[SUB_MOD] >>
    `(k - n) DIV n = k DIV n - 1` by rw[GSYM SUB_DIV] >>
    `0 < k DIV n` by rw[DIVIDES_MOD_0, DIV_POS] >>
    `EL (k - n) (MDILATE e n l) = EL (k DIV n - 1) l` by rw[] >>
    `_ = EL (PRE (k DIV n)) l` by rw[PRE_SUB1] >>
    `_ = EL (k DIV n) (h::l)` by rw[EL_CONS] >>
    rw[]
  ]) >>
  rw_tac std_ss[EL_APPEND] >| [
    `LENGTH t = n` by rw[Abbr`t`] >>
    `k MOD n = k` by rw[LESS_MOD] >>
    `0 < k /\ PRE k < PRE n` by decide_tac >>
    `EL k t = EL (PRE k) (GENLIST (K e) (PRE n))` by rw[EL_CONS, Abbr`t`] >>
    `_ = e` by rw[] >>
    rw[],
    `LENGTH t = n` by rw[Abbr`t`] >>
    `k - n < LENGTH (MDILATE e n l)` by rw[MDILATE_LENGTH] >>
    `n <= k` by decide_tac >>
    `(k - n) MOD n = k MOD n` by rw[SUB_MOD] >>
    `EL (k - n) (MDILATE e n l) = e` by rw[] >>
    rw[]
  ]);

(* This is a milestone theorem. *)

(* Theorem: (MDILATE e n l = []) <=> (l = []) *)
(* Proof:
   If part: MDILATE e n l = [] ==> l = []
      By contradiction, suppose l <> [].
      If n = 0,
         Then MDILATE e 0 l = l     by MDILATE_0
         This contradicts MDILATE e 0 l = [].
      If n <> 0,
         Then LENGTH (MDILATE e n l)
            = SUC (n * PRE (LENGTH l))  by MDILATE_LENGTH
            <> 0                    by SUC_NOT
         So (MDILATE e n l) <> []   by LENGTH_NIL
         This contradicts MDILATE e n l = []
   Only-if part: l = [] ==> MDILATE e n l = []
      True by MDILATE_NIL
*)
val MDILATE_EQ_NIL = store_thm(
  "MDILATE_EQ_NIL",
  ``!l e n. (MDILATE e n l = []) <=> (l = [])``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  Cases_on `n = 0` >| [
    `MDILATE e 0 l = l` by rw[GSYM MDILATE_0] >>
    metis_tac[],
    `LENGTH (MDILATE e n l) = SUC (n * PRE (LENGTH l))` by rw[MDILATE_LENGTH] >>
    `LENGTH (MDILATE e n l) <> 0` by decide_tac >>
    metis_tac[LENGTH_EQ_0]
  ]);

(* Theorem: LAST (MDILATE e n l) = LAST l *)
(* Proof:
   If l = [],
        LAST (MDILATE e n [])
      = LAST []                by MDILATE_NIL
   If l <> [],
      If n = 0,
        LAST (MDILATE e 0 l)
      = LAST l                 by MDILATE_0
      If n <> 0, then 0 < m    by LESS_0
        Then MDILATE e n l <> []             by MDILATE_EQ_NIL
          or LENGTH (MDILATE e n l) <> 0     by LENGTH_NIL
        Note PRE (LENGTH (MDILATE e n l))
           = PRE (SUC (n * PRE (LENGTH l)))  by MDILATE_LENGTH
           = n * PRE (LENGTH l)              by PRE
        Let k = PRE (LENGTH (MDILATE e n l)).
        Then k < LENGTH (MDILATE e n l)      by PRE x < x
         and k MOD n = 0                     by MOD_EQ_0, MULT_COMM, 0 < n
         and k DIV n = PRE (LENGTH l)        by MULT_DIV, MULT_COMM

        LAST (MDILATE e n l)
      = EL k (MDILATE e n l)                 by LAST_EL
      = EL (k DIV n) l                       by MDILATE_EL
      = EL (PRE (LENGTH l)) l                by above
      = LAST l                               by LAST_EL
*)
val MDILATE_LAST = store_thm(
  "MDILATE_LAST",
  ``!l e n. LAST (MDILATE e n l) = LAST l``,
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[] >>
  Cases_on `n = 0` >-
  rw[MDILATE_0] >>
  `0 < n` by decide_tac >>
  `MDILATE e n l <> []` by rw[MDILATE_EQ_NIL] >>
  `LENGTH (MDILATE e n l) <> 0` by metis_tac[LENGTH_NIL] >>
  qabbrev_tac `k = PRE (LENGTH (MDILATE e n l))` >>
  rw[LAST_EL] >>
  `k = n * PRE (LENGTH l)` by rw[MDILATE_LENGTH, Abbr`k`] >>
  `k MOD n = 0` by metis_tac[MOD_EQ_0, MULT_COMM] >>
  `k DIV n = PRE (LENGTH l)` by metis_tac[MULT_DIV, MULT_COMM] >>
  `k < LENGTH (MDILATE e n l)` by rw[Abbr`k`] >>
  rw[MDILATE_EL]);

(*
Succesive dilation:

> EVAL ``MDILATE #0 3 [a; b; c]``;
val it = |- MDILATE #0 3 [a; b; c] = [a; #0; #0; b; #0; #0; c]: thm
> EVAL ``MDILATE #0 4 [a; b; c]``;
val it = |- MDILATE #0 4 [a; b; c] = [a; #0; #0; #0; b; #0; #0; #0; c]: thm
> EVAL ``MDILATE #0 1 (MDILATE #0 3 [a; b; c])``;
val it = |- MDILATE #0 1 (MDILATE #0 3 [a; b; c]) = [a; #0; #0; b; #0; #0; c]: thm
> EVAL ``MDILATE #0 2 (MDILATE #0 3 [a; b; c])``;
val it = |- MDILATE #0 2 (MDILATE #0 3 [a; b; c]) = [a; #0; #0; #0; #0; #0; b; #0; #0; #0; #0; #0; c]: thm
> EVAL ``MDILATE #0 2 (MDILATE #0 2 [a; b; c])``;
val it = |- MDILATE #0 2 (MDILATE #0 2 [a; b; c]) = [a; #0; #0; #0; b; #0; #0; #0; c]: thm
> EVAL ``MDILATE #0 2 (MDILATE #0 2 [a; b; c]) = MDILATE #0 4 [a; b; c]``;
val it = |- (MDILATE #0 2 (MDILATE #0 2 [a; b; c]) = MDILATE #0 4 [a; b; c]) <=> T: thm
> EVAL ``MDILATE #0 2 (MDILATE #0 3 [a; b; c]) = MDILATE #0 5 [a; b; c]``;
val it = |- (MDILATE #0 2 (MDILATE #0 3 [a; b; c]) = MDILATE #0 5 [a; b; c]) <=> F: thm
> EVAL ``MDILATE #0 2 (MDILATE #0 3 [a; b; c]) = MDILATE #0 6 [a; b; c]``;
val it = |- (MDILATE #0 2 (MDILATE #0 3 [a; b; c]) = MDILATE #0 6 [a; b; c]) <=> T: thm

So successive dilation is related to product, or factorisation, or primes:
MDILATE e m (MDILATE e n l) = MDILATE e (m * n) l, for 0 < m, 0 < n.

*)

(* ------------------------------------------------------------------------- *)
(* List Dilation (Additive)                                                  *)
(* ------------------------------------------------------------------------- *)

(* Dilate by inserting m zeroes, at position n of tail *)
Definition DILATE_def:
  (DILATE e n m [] = []) /\
  (DILATE e n m [h] = [h]) /\
  (DILATE e n m (h::t) = h:: (TAKE n t ++ (GENLIST (K e) m) ++ DILATE e n m (DROP n t)))
Termination
  WF_REL_TAC `measure (λ(a,b,c,d). LENGTH d)` >>
  rw[LENGTH_DROP]
End

(*
> EVAL ``DILATE 0 0 1 [1;2;3]``;
val it = |- DILATE 0 0 1 [1; 2; 3] = [1; 0; 2; 0; 3]: thm
> EVAL ``DILATE 0 0 2 [1;2;3]``;
val it = |- DILATE 0 0 2 [1; 2; 3] = [1; 0; 0; 2; 0; 0; 3]: thm
> EVAL ``DILATE 0 1 1 [1;2;3]``;
val it = |- DILATE 0 1 1 [1; 2; 3] = [1; 2; 0; 3]: thm
> EVAL ``DILATE 0 1 1 (DILATE 0 0 1 [1;2;3])``;
val it = |- DILATE 0 1 1 (DILATE 0 0 1 [1; 2; 3]) = [1; 0; 0; 2; 0; 0; 3]: thm
>  EVAL ``DILATE 0 0 3 [1;2;3]``;
val it = |- DILATE 0 0 3 [1; 2; 3] = [1; 0; 0; 0; 2; 0; 0; 0; 3]: thm
> EVAL ``DILATE 0 1 1 (DILATE 0 0 2 [1;2;3])``;
val it = |- DILATE 0 1 1 (DILATE 0 0 2 [1; 2; 3]) = [1; 0; 0; 0; 2; 0; 0; 0; 0; 3]: thm
> EVAL ``DILATE 0 0 3 [1;2;3] = DILATE 0 2 1 (DILATE 0 0 2 [1;2;3])``;
val it = |- (DILATE 0 0 3 [1; 2; 3] = DILATE 0 2 1 (DILATE 0 0 2 [1; 2; 3])) <=> T: thm

> EVAL ``DILATE 0 0 0 [1;2;3]``;
val it = |- DILATE 0 0 0 [1; 2; 3] = [1; 2; 3]: thm
> EVAL ``DILATE 1 0 0 [1;2;3]``;
val it = |- DILATE 1 0 0 [1; 2; 3] = [1; 2; 3]: thm
> EVAL ``DILATE 1 0 1 [1;2;3]``;
val it = |- DILATE 1 0 1 [1; 2; 3] = [1; 1; 2; 1; 3]: thm
> EVAL ``DILATE 1 1 1 [1;2;3]``;
val it = |- DILATE 1 1 1 [1; 2; 3] = [1; 2; 1; 3]: thm
> EVAL ``DILATE 1 1 2 [1;2;3]``;
val it = |- DILATE 1 1 2 [1; 2; 3] = [1; 2; 1; 1; 3]: thm
> EVAL ``DILATE 1 1 3 [1;2;3]``;
val it = |- DILATE 1 1 3 [1; 2; 3] = [1; 2; 1; 1; 1; 3]: thm
*)

(* Theorem: DILATE e n m [] = [] *)
(* Proof: by DILATE_def *)
val DILATE_NIL = save_thm("DILATE_NIL", DILATE_def |> CONJUNCT1);
(* val DILATE_NIL = |- !n m e. DILATE e n m [] = []: thm *)

(* export simple result *)
val _ = export_rewrites["DILATE_NIL"];

(* Theorem: DILATE e n m [h] = [h] *)
(* Proof: by DILATE_def *)
val DILATE_SING = save_thm("DILATE_SING", DILATE_def |> CONJUNCT2 |> CONJUNCT1);
(* val DILATE_SING = |- !n m h e. DILATE e n m [h] = [h]: thm *)

(* export simple result *)
val _ = export_rewrites["DILATE_SING"];

(* Theorem: DILATE e n m (h::t) =
            if t = [] then [h] else h:: (TAKE n t ++ (GENLIST (K e) m) ++ DILATE e n m (DROP n t)) *)
(* Proof: by DILATE_def, list_CASES *)
val DILATE_CONS = store_thm(
  "DILATE_CONS",
  ``!n m h t e. DILATE e n m (h::t) =
    if t = [] then [h] else h:: (TAKE n t ++ (GENLIST (K e) m) ++ DILATE e n m (DROP n t))``,
  metis_tac[DILATE_def, list_CASES]);

(* Theorem: DILATE e 0 n (h::t) = if t = [] then [h] else h::(GENLIST (K e) n ++ DILATE e 0 n t) *)
(* Proof:
   If t = [],
     DILATE e 0 n (h::t) = [h]    by DILATE_CONS
   If t <> [],
     DILATE e 0 n (h::t)
   = h:: (TAKE 0 t ++ (GENLIST (K e) n) ++ DILATE e 0 n (DROP 0 t))  by DILATE_CONS
   = h:: ([] ++ (GENLIST (K e) n) ++ DILATE e 0 n t)                 by TAKE_0, DROP_0
   = h:: (GENLIST (K e) n ++ DILATE e 0 n t)                         by APPEND
*)
val DILATE_0_CONS = store_thm(
  "DILATE_0_CONS",
  ``!n h t e. DILATE e 0 n (h::t) = if t = [] then [h] else h::(GENLIST (K e) n ++ DILATE e 0 n t)``,
  rw[DILATE_CONS]);

(* Theorem: DILATE e 0 0 l = l *)
(* Proof:
   By induction on l.
   Base: DILATE e 0 0 [] = [], true         by DILATE_NIL
   Step: DILATE e 0 0 l = l ==> !h. DILATE e 0 0 (h::l) = h::l
      If l = [],
         DILATE e 0 0 [h] = [h]             by DILATE_SING
      If l <> [],
         DILATE e 0 0 (h::l)
       = h::(GENLIST (K e) 0 ++ DILATE e 0 0 l)   by DILATE_0_CONS
       = h::([] ++ DILATE e 0 0 l)                by GENLIST_0
       = h:: DILATE e 0 0 l                       by APPEND
       = h::l                                     by induction hypothesis
*)
val DILATE_0_0 = store_thm(
  "DILATE_0_0",
  ``!l e. DILATE e 0 0 l = l``,
  Induct >>
  rw[DILATE_0_CONS]);

(* Theorem: DILATE e 0 (SUC n) l = DILATE e n 1 (DILATE e 0 n l) *)
(* Proof:
   If n = 0,
      DILATE e 0 1 l = DILATE e 0 1 (DILATE e 0 0 l)   by DILATE_0_0
   If n <> 0,
      GENLIST (K e) n <> []       by LENGTH_GENLIST, LENGTH_NIL
   By induction on l.
   Base: DILATE e 0 (SUC n) [] = DILATE e n 1 (DILATE e 0 n [])
      DILATE e 0 (SUC n) [] = []                  by DILATE_NIL
        DILATE e n 1 (DILATE e 0 n [])
      = DILATE e n 1 [] = []                      by DILATE_NIL
   Step: DILATE e 0 (SUC n) l = DILATE e n 1 (DILATE e 0 n l) ==>
         !h. DILATE e 0 (SUC n) (h::l) = DILATE e n 1 (DILATE e 0 n (h::l))
      If l = [],
        DILATE e 0 (SUC n) [h] = [h]       by DILATE_SING
          DILATE e n 1 (DILATE e 0 n [h])
        = DILATE e n 1 [h] = [h]           by DILATE_SING
      If l <> [],
          DILATE e 0 (SUC n) (h::l)
        = h::(GENLIST (K e) (SUC n) ++ DILATE e 0 (SUC n) l)                by DILATE_0_CONS
        = h::(GENLIST (K e) (SUC n) ++ DILATE e n 1 (DILATE e 0 n l))       by induction hypothesis

        Note LENGTH (GENLIST (K e) n) = n                 by LENGTH_GENLIST
          so (GENLIST (K e) n ++ DILATE e 0 n l) <> []    by APPEND_eq_NIL, LENGTH_NIL [1]
         and TAKE n (GENLIST (K e) n ++ DILATE e 0 n l) = GENLIST (K e) n   by TAKE_LENGTH_APPEND [2]
         and DROP n (GENLIST (K e) n ++ DILATE e 0 n l) = DILATE e 0 n l    by DROP_LENGTH_APPEND [3]
         and GENLIST (K e) (SUC n)
           = GENLIST (K e) (1 + n)                        by SUC_ONE_ADD
           = GENLIST (K e) n ++ GENLIST (K e) 1           by GENLIST_K_ADD [4]

          DILATE e n 1 (DILATE e 0 n (h::l))
        = DILATE e n 1 (h::(GENLIST (K e) n ++ DILATE e 0 n l))             by DILATE_0_CONS
        = h::(TAKE n (GENLIST (K e) n ++ DILATE e 0 n l) ++ GENLIST (K e) 1 ++
               DILATE e n 1 (DROP n (GENLIST (K e) n ++ DILATE e 0 n l)))   by DILATE_CONS, [1]
        = h::(GENLIST (K e) n ++ GENLIST (K e) 1 ++ DILATE e n 1 (DILATE e 0 n l))   by above [2], [3]
        = h::(GENLIST (K e) (SUC n) ++ DILATE e n 1 (DILATE e 0 n l))       by above [4]
*)
val DILATE_0_SUC = store_thm(
  "DILATE_0_SUC",
  ``!l e n. DILATE e 0 (SUC n) l = DILATE e n 1 (DILATE e 0 n l)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[DILATE_0_0] >>
  Induct_on `l` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[DILATE_SING] >>
  qabbrev_tac `a = GENLIST (K e) n ++ DILATE e 0 n l` >>
  `LENGTH (GENLIST (K e) n) = n` by rw[] >>
  `a <> []` by metis_tac[APPEND_eq_NIL, LENGTH_NIL] >>
  `TAKE n a = GENLIST (K e) n` by metis_tac[TAKE_LENGTH_APPEND] >>
  `DROP n a = DILATE e 0 n l` by metis_tac[DROP_LENGTH_APPEND] >>
  `GENLIST (K e) (SUC n) = GENLIST (K e) n ++ GENLIST (K e) 1` by rw_tac std_ss[SUC_ONE_ADD, GENLIST_K_ADD] >>
  metis_tac[DILATE_0_CONS, DILATE_CONS]);

(* Theorem: LENGTH (DILATE e 0 n l) = if l = [] then 0 else SUC (SUC n * PRE (LENGTH l)) *)
(* Proof:
   By induction on l.
   Base: LENGTH (DILATE e 0 n []) = 0
         LENGTH (DILATE e 0 n [])
       = LENGTH []                       by DILATE_NIL
       = 0                               by LENGTH_NIL
   Step: LENGTH (DILATE e 0 n l) = if l = [] then 0 else SUC (SUC n * PRE (LENGTH l)) ==>
         !h. LENGTH (DILATE e 0 n (h::l)) = SUC (SUC n * PRE (LENGTH (h::l)))
       If l = [],
          LENGTH (DILATE e 0 n [h])
        = LENGTH [h]                     by DILATE_SING
        = 1                              by LENGTH
          SUC (SUC n * PRE (LENGTH [h])
        = SUC (SUC n * PRE 1)            by LENGTH
        = SUC (SUC n * 0)                by PRE_SUB1
        = SUC 0                          by MULT_0
        = 1                              by ONE
       If l <> [],
          Note LENGTH l <> 0             by LENGTH_NIL
          LENGTH (DILATE e 0 n (h::l))
        = LENGTH (h::(GENLIST (K e) n ++ DILATE e 0 n l))           by DILATE_0_CONS
        = SUC (LENGTH (GENLIST (K e) n ++ DILATE e 0 n l))          by LENGTH
        = SUC (LENGTH (GENLIST (K e) n) + LENGTH (DILATE e 0 n l))  by LENGTH_APPEND
        = SUC (n + LENGTH (DILATE e 0 n l))        by LENGTH_GENLIST
        = SUC (n + SUC (SUC n * PRE (LENGTH l)))   by induction hypothesis
        = SUC (SUC (n + SUC n * PRE (LENGTH l)))   by ADD_SUC
        = SUC (SUC n  + SUC n * PRE (LENGTH l))    by ADD_COMM, ADD_SUC
        = SUC (SUC n * SUC (PRE (LENGTH l)))       by MULT_SUC
        = SUC (SUC n * LENGTH l)                   by SUC_PRE, 0 < LENGTH l
        = SUC (SUC n * PRE (LENGTH (h::l)))        by LENGTH, PRE_SUC_EQ
*)
val DILATE_0_LENGTH = store_thm(
  "DILATE_0_LENGTH",
  ``!l e n. LENGTH (DILATE e 0 n l) = if l = [] then 0 else SUC (SUC n * PRE (LENGTH l))``,
  Induct >-
  rw[] >>
  rw_tac std_ss[LENGTH] >>
  Cases_on `l = []` >-
  rw[] >>
  `0 < LENGTH l` by metis_tac[LENGTH_NIL, NOT_ZERO_LT_ZERO] >>
  `LENGTH (DILATE e 0 n (h::l)) = LENGTH (h::(GENLIST (K e) n ++ DILATE e 0 n l))` by rw[DILATE_0_CONS] >>
  `_ = SUC (LENGTH (GENLIST (K e) n ++ DILATE e 0 n l))` by rw[] >>
  `_ = SUC (n + LENGTH (DILATE e 0 n l))` by rw[] >>
  `_ = SUC (n + SUC (SUC n * PRE (LENGTH l)))` by rw[] >>
  `_ = SUC (SUC (n + SUC n * PRE (LENGTH l)))` by rw[] >>
  `_ = SUC (SUC n + SUC n * PRE (LENGTH l))` by rw[] >>
  `_ = SUC (SUC n * SUC (PRE (LENGTH l)))` by rw[MULT_SUC] >>
  `_ = SUC (SUC n * LENGTH l)` by rw[SUC_PRE] >>
  rw[]);

(* Theorem: LENGTH l <= LENGTH (DILATE e 0 n l) *)
(* Proof:
   If l = [],
        LENGTH (DILATE e 0 n [])
      = LENGTH []                      by DILATE_NIL
      >= LENGTH []
   If l <> [],
      Then ?h t. l = h::t              by list_CASES
        LENGTH (DILATE e 0 n (h::t))
      = SUC (SUC n * PRE (LENGTH (h::t)))  by DILATE_0_LENGTH
      = SUC (SUC n * PRE (SUC (LENGTH t))) by LENGTH
      = SUC (SUC n * LENGTH t)             by PRE
      = SUC n * LENGTH t + 1               by ADD1
      >= LENGTH t + 1                  by LE_MULT_CANCEL_LBARE, 0 < SUC n
      = SUC (LENGTH t)                 by ADD1
      = LENGTH (h::t)                  by LENGTH
*)
val DILATE_0_LENGTH_LOWER = store_thm(
  "DILATE_0_LENGTH_LOWER",
  ``!l e n. LENGTH l <= LENGTH (DILATE e 0 n l)``,
  rw[DILATE_0_LENGTH] >>
  `?h t. l = h::t` by metis_tac[list_CASES] >>
  rw[]);

(* Theorem: LENGTH (DILATE e 0 n l) <= SUC (SUC n * PRE (LENGTH l)) *)
(* Proof:
   If l = [],
        LENGTH (DILATE e 0 n [])
      = LENGTH []                      by DILATE_NIL
      = 0                              by LENGTH_NIL
        SUC (SUC n * PRE (LENGTH []))
      = SUC (SUC n * PRE 0)            by LENGTH_NIL
      = SUC 0                          by PRE, MULT_0
      > 0                              by LESS_SUC
   If l <> [],
        LENGTH (DILATE e 0 n l)
      = SUC (SUC n * PRE (LENGTH l))   by DILATE_0_LENGTH
*)
val DILATE_0_LENGTH_UPPER = store_thm(
  "DILATE_0_LENGTH_UPPER",
  ``!l e n. LENGTH (DILATE e 0 n l) <= SUC (SUC n * PRE (LENGTH l))``,
  rw[DILATE_0_LENGTH]);

(* Theorem: k < LENGTH (DILATE e 0 n l) ==>
            (EL k (DILATE e 0 n l) = if k MOD (SUC n) = 0 then EL (k DIV (SUC n)) l else e) *)
(* Proof:
   Let m = SUC n, then 0 < m.
   By induction on l.
   Base: !k. k < LENGTH (DILATE e 0 n []) ==> (EL k (DILATE e 0 n []) = if k MOD m = 0 then EL (k DIV m) [] else e)
      Note LENGTH (DILATE e 0 n [])
         = LENGTH []         by DILATE_NIL
         = 0                 by LENGTH_NIL
      Thus k < 0 <=> F       by NOT_ZERO_LT_ZERO
   Step: !k. k < LENGTH (DILATE e 0 n l) ==> (EL k (DILATE e 0 n l) = if k MOD m = 0 then EL (k DIV m) l else e) ==>
         !h k. k < LENGTH (DILATE e 0 n (h::l)) ==> (EL k (DILATE e 0 n (h::l)) = if k MOD m = 0 then EL (k DIV m) (h::l) else e)
      Note LENGTH (DILATE e 0 n [h]) = 1    by DILATE_SING
       and LENGTH (DILATE e 0 n (h::l))
         = SUC (m * PRE (LENGTH (h::l)))    by DILATE_0_LENGTH, n <> 0
         = SUC (m * PRE (SUC (LENGTH l)))   by LENGTH
         = SUC (m * LENGTH l)               by PRE

      If l = [],
        Then DILATE e 0 n [h] = [h]         by DILATE_SING
         and LENGTH (DILATE e 0 n [h]) = 1  by LENGTH
          so k < 1 means k = 0.
         and 0 DIV m = 0                    by ZERO_DIV, 0 < m
         and 0 MOD m = 0                    by ZERO_MOD, 0 < m
        Thus EL k [h] = EL (k DIV m) [h].

      If l <> [],
        Let t = h:: GENLIST (K e) n.
        Note LENGTH t = SUC n = m           by LENGTH_GENLIST
        If k < m,
           Then k MOD m = k                 by LESS_MOD, k < m
             EL k (DILATE e 0 n (h::l))
           = EL k (t ++ DILATE e 0 n l)     by DILATE_0_CONS
           = EL k t                         by EL_APPEND, k < LENGTH t
           If k = 0, i.e. k MOD m = 0.
              EL 0 t
            = EL 0 (h:: GENLIST (K e) (PRE n))  by notation of t
            = h
            = EL (0 DIV m) (h::l)           by EL, HD
           If k <> 0, i.e. k MOD m <> 0.
              EL k t
            = EL k (h:: GENLIST (K e) n)    by notation of t
            = EL (PRE k) (GENLIST (K e) n)  by EL_CONS
            = (K e) (PRE k)                 by EL_GENLIST, PRE k < PRE m = n
            = e                             by application of K
        If ~(k < m), then m <= k.
           Given k < LENGTH (DILATE e 0 n (h::l))
              or k < SUC (m * LENGTH l)              by above
             ==> k - m < SUC (m * LENGTH l) - m      by m <= k
                       = SUC (m * LENGTH l - m)      by SUB
                       = SUC (m * (LENGTH l - 1))    by LEFT_SUB_DISTRIB
                       = SUC (m * PRE (LENGTH l))    by PRE_SUB1
              or k - m < LENGTH (MDILATE e n l)      by MDILATE_LENGTH
            Thus (k - m) MOD m = k MOD m             by SUB_MOD
             and (k - m) DIV m = k DIV m - 1         by SUB_DIV
          If k MOD m = 0,
             Note 0 < k DIV m                        by DIVIDES_MOD_0, DIV_POS
             EL k (t ++ DILATE e 0 n l)
           = EL (k - m) (DILATE e 0 n l)             by EL_APPEND, m <= k
           = EL (k DIV m - 1) l                      by induction hypothesis, (k - m) MOD m = 0
           = EL (PRE (k DIV m)) l                    by PRE_SUB1
           = EL (k DIV m) (h::l)                     by EL_CONS, 0 < k DIV m
          If k MOD m <> 0,
             EL k (t ++ DILATE e 0 n l)
           = EL (k - m) (DILATE e 0 n l)             by EL_APPEND, n <= k
           = e                                       by induction hypothesis, (k - m) MOD n <> 0
*)
Theorem DILATE_0_EL:
  !l e n k. k < LENGTH (DILATE e 0 n l) ==>
     (EL k (DILATE e 0 n l) = if k MOD (SUC n) = 0 then EL (k DIV (SUC n)) l else e)
Proof
  ntac 3 strip_tac >>
  `0 < SUC n` by decide_tac >>
  qabbrev_tac `m = SUC n` >>
  Induct_on `l` >-
  rw[] >>
  rpt strip_tac >>
  `LENGTH (DILATE e 0 n [h]) = 1` by rw[DILATE_SING] >>
  `LENGTH (DILATE e 0 n (h::l)) = SUC (m * LENGTH l)` by rw[DILATE_0_LENGTH, Abbr`m`] >>
  Cases_on `l = []` >| [
    `k = 0` by rw[] >>
    `k MOD m = 0` by rw[] >>
    `k DIV m = 0` by rw[ZERO_DIV] >>
    rw_tac std_ss[DILATE_SING],
    qabbrev_tac `t = h::GENLIST (K e) n` >>
    `DILATE e 0 n (h::l) = t ++ DILATE e 0 n l` by rw[DILATE_0_CONS, Abbr`t`] >>
    `m = LENGTH t` by rw[Abbr`t`] >>
    Cases_on `k < m` >| [
      `k MOD m = k` by rw[] >>
      `EL k (DILATE e 0 n (h::l)) = EL k t` by rw[EL_APPEND] >>
      Cases_on `k = 0` >| [
        `EL 0 t = h` by rw[Abbr`t`] >>
        rw[ZERO_DIV],
        `PRE m = n` by rw[Abbr`m`] >>
        `PRE k < n` by decide_tac >>
        `EL k t = EL (PRE k) (GENLIST (K e) n)` by rw[EL_CONS, Abbr`t`] >>
        `_ = (K e) (PRE k)` by rw[EL_GENLIST] >>
        rw[]
      ],
      `m <= k` by decide_tac >>
      `EL k (t ++ DILATE e 0 n l) = EL (k - m) (DILATE e 0 n l)` by simp[EL_APPEND] >>
      `k - m < LENGTH (DILATE e 0 n l)` by rw[DILATE_0_LENGTH] >>
      `(k - m) MOD m = k MOD m` by simp[SUB_MOD] >>
      `(k - m) DIV m = k DIV m - 1` by simp[SUB_DIV] >>
      Cases_on `k MOD m = 0` >| [
        `0 < k DIV m` by rw[DIVIDES_MOD_0, DIV_POS] >>
        `EL (k - m) (DILATE e 0 n l) = EL (k DIV m - 1) l` by rw[] >>
        `_ = EL (PRE (k DIV m)) l` by rw[PRE_SUB1] >>
        `_ = EL (k DIV m) (h::l)` by rw[EL_CONS] >>
        rw[],
        `EL (k - m) (DILATE e 0 n l)  = e` by rw[] >>
        rw[]
      ]
    ]
  ]
QED

(* This is a milestone theorem. *)

(* Theorem: (DILATE e 0 n l = []) <=> (l = []) *)
(* Proof:
   If part: DILATE e 0 n l = [] ==> l = []
      By contradiction, suppose l <> [].
      If n = 0,
         Then DILATE e n 0 l = l     by DILATE_0_0
         This contradicts DILATE e n 0 l = [].
      If n <> 0,
         Then LENGTH (DILATE e 0 n l)
            = SUC (SUC n * PRE (LENGTH l))  by DILATE_0_LENGTH
            <> 0                     by SUC_NOT
         So (DILATE e 0 n l) <> []   by LENGTH_NIL
         This contradicts DILATE e 0 n l = []
   Only-if part: l = [] ==> DILATE e 0 n l = []
      True by DILATE_NIL
*)
val DILATE_0_EQ_NIL = store_thm(
  "DILATE_0_EQ_NIL",
  ``!l e n. (DILATE e 0 n l = []) <=> (l = [])``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  Cases_on `n = 0` >| [
    `DILATE e 0 0 l = l` by rw[GSYM DILATE_0_0] >>
    metis_tac[],
    `LENGTH (DILATE e 0 n l) = SUC (SUC n * PRE (LENGTH l))` by rw[DILATE_0_LENGTH] >>
    `LENGTH (DILATE e 0 n l) <> 0` by decide_tac >>
    metis_tac[LENGTH_EQ_0]
  ]);

(* Theorem: LAST (DILATE e 0 n l) = LAST l *)
(* Proof:
   If l = [],
        LAST (DILATE e 0 n [])
      = LAST []                by DILATE_NIL
   If l <> [],
      If n = 0,
        LAST (DILATE e 0 0 l)
      = LAST l                 by DILATE_0_0
      If n <> 0,
        Then DILATE e 0 n l <> []            by DILATE_0_EQ_NIL
          or LENGTH (DILATE e 0 n l) <> 0    by LENGTH_NIL
        Let m = SUC n, then 0 < m            by LESS_0
        Note PRE (LENGTH (DILATE e 0 n l))
           = PRE (SUC (m * PRE (LENGTH l)))  by DILATE_0_LENGTH
           = m * PRE (LENGTH l)              by PRE
        Let k = PRE (LENGTH (DILATE e 0 n l)).
        Then k < LENGTH (DILATE e 0 n l)     by PRE x < x
         and k MOD m = 0                     by MOD_EQ_0, MULT_COMM, 0 < m
         and k DIV m = PRE (LENGTH l)        by MULT_DIV, MULT_COMM

        LAST (DILATE e 0 n l)
      = EL k (DILATE e 0 n l)                by LAST_EL
      = EL (k DIV m) l                       by DILATE_0_EL
      = EL (PRE (LENGTH l)) l                by above
      = LAST l                               by LAST_EL
*)
val DILATE_0_LAST = store_thm(
  "DILATE_0_LAST",
  ``!l e n. LAST (DILATE e 0 n l) = LAST l``,
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[] >>
  Cases_on `n = 0` >-
  rw[DILATE_0_0] >>
  `0 < n` by decide_tac >>
  `DILATE e 0 n l <> []` by rw[DILATE_0_EQ_NIL] >>
  `LENGTH (DILATE e 0 n l) <> 0` by metis_tac[LENGTH_NIL] >>
  qabbrev_tac `k = PRE (LENGTH (DILATE e 0 n l))` >>
  rw[LAST_EL] >>
  `0 < SUC n` by decide_tac >>
  qabbrev_tac `m = SUC n` >>
  `k = m * PRE (LENGTH l)` by rw[DILATE_0_LENGTH, Abbr`k`, Abbr`m`] >>
  `k MOD m = 0` by metis_tac[MOD_EQ_0, MULT_COMM] >>
  `k DIV m = PRE (LENGTH l)` by metis_tac[MULT_DIV, MULT_COMM] >>
  `k < LENGTH (DILATE e 0 n l)` by simp[Abbr`k`] >>
  Q.RM_ABBREV_TAC ‘k’ >>
  rw[DILATE_0_EL]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
