(*---------------------------------------------------------------------------
                        Packages in HOL-Omega
                        Peter Vincent Homeier
                           August 11, 2011
 ---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------

   This file contains examples of uses of packages and existential types,
   as described in chapter 24 of "Types and Programming Languages"
   by Benjamin C. Pierce, MIT Press, 2002.

   Existential types provide a means for abstraction and modularity,
   where a implementation of a data structure can hide its particular
   representation, and only present an abstract view to uses of the
   data structure.

   The syntax of existential types and packages is different from
   that used in Pierce's book.  Here is a table of correspondances,
   where in Pierce's notation, X is a type variable, S and T are
   arbitrary types, t is an arbitrary term, and x is a term variable,
   and in HOL-Omega's notation, 'a is a type variable, σ stands for 
   an arbitrary type, and x is a term variable.
   In both notations, p is a package, and tm is an arbitrary term.

                                 Pierce                 HOL-Omega
                                 ------                 ---------
      Existential type           {∃X,T}                  ∃'a. σ
      Package introduction       {*S,t}               pack (:σ, tm)
      Package elimination    let {X,x}=p in tm    let (:'a, x) = p in tm

   The addition of packages to HOL-Omega has necessitated one change
   which is not backwards compatible with HOL4: the name "pack" is now
   a reserved keyword, and cannot be used for variable names by the parser.

  ---------------------------------------------------------------------------*)

structure packageScript =
struct

open HolKernel Parse boolLib bossLib

val _ = new_theory "package";

local open combinTheory pred_setLib bagLib in end;

val _ = set_trace "Unicode" 0;
val _ = set_trace "types" 1;


(* Existential types: *)

val ety1 = ``:?'a. 'a -> 'a``;
val ety1_vars = type_vars ety1;

val ety2 = ``:?'a. 'a -> 'b``;
val ety2_vars = type_vars ety2;

val ety2' = mk_exist_type(gamma, gamma --> beta);
val check = eq_ty ety2 ety2';

val (bvar,body) = dest_exist_type ety2;

val ety3 = list_mk_exist_type ([alpha,gamma], alpha --> beta --> gamma);
val (ety3_bvars,ety3_body) = strip_exist_type ety3;


(* Creating packages: *)

(* Example 1: Simple package examples from Pierce, Ch.24.1, page 364-5. *)

val pkg1 = ``pack (:num, (5, \x:num. SUC x))``;
val pkg1_ty = type_of pkg1;

val pkg2 = ``pack (:num, (5, \x:num. SUC x)) : ?'x. 'x # ('x -> num)``;
val pkg2_ty = type_of pkg2;

val pkg3 = ``pack (:num, 0) : ?'x. 'x``;
val pkg3_ty = type_of pkg3;

val pkg4 = ``pack (:bool, T) : ?'x. 'x``;
val pkg4_ty = type_of pkg4;

val check = eq_ty pkg3_ty pkg4_ty;

val pkg5 =
    ``pack (:num, (0, \x:num. SUC x)) : ?'x. 'x # ('x -> num)``;
val pkg5_ty = type_of pkg5;

val pkg6 =
    ``pack (:bool, (T, \x:bool. 0)) : ?'x. 'x # ('x -> num)``;
val pkg6_ty = type_of pkg6;

val check = eq_ty pkg5_ty pkg6_ty;


(* Using packages *)

fun eval ths = QCONV (SIMP_CONV (srw_ss()) ths);

val unpkg5 = ``let (:'x, t:'x # ('x -> num)) = ^pkg5 in (SND t) (FST t)``;

val unpkg5_res = eval [] unpkg5;

val unpkg6 = ``let (:'x, t:'x # ('x -> num)) = ^pkg6 in (SND t) (FST t)``;
val unpkg6_res = eval [] unpkg6;

val unpkg5a = ``let (:'x, t:'x # ('x -> num)) = ^pkg5 in (\y:'x. (SND t) y) (FST t)``;
val unpkg5a_res = eval [] unpkg5a;


(* Packages can be used to simulate objects, as   *)
(* abstract data types hiding the representation. *)
(* From Pierce, chapter 24, page 369.             *)

val _ = Hol_datatype
       `counter_recd1 =
                     <| new : 'a;
                        get : 'a -> num;
                        inc : 'a -> 'a
                      |>`;

val counter_kind = kind_of ``:counter_recd1``;

val counterADT =
       ``pack ( :num,
                <| new := 1;
                   get := \i:num. i;
                   inc := \i:num. SUC i
                |> ) : ?'a. 'a counter_recd1``;

val counterADT_type = type_of counterADT; (* note: an existential type *)

val counter_ex1 =
  ``let (:'Counter,counter) = ^counterADT in
    counter.get (counter.inc counter.new)``;

val ex1_res = eval[] counter_ex1;

val counter_ex2 =
  ``let (:'Counter,counter) = ^counterADT in
    let add3 = \c:'Counter. counter.inc (counter.inc (counter.inc c)) in
    counter.get (add3 counter.new)``;

val ex2_res = eval[LET_DEF] counter_ex2;

val _ = Hol_datatype
       `flipflop_recd1 =
                     <| new    : 'a;
                        read   : 'a -> bool;
                        toggle : 'a -> 'a;
                        reset  : 'a -> 'a
                      |>`;
val flipflop_recd1_kd = kind_of ``:flipflop_recd1``;

val counter_ex3 =
  ``let (:'Counter,counter) = ^counterADT in

    let (:'FlipFlop,flipflop) =
        pack(:'Counter,
             <| new    := counter.new;
                read   := \c:'Counter. EVEN (counter.get c);
                toggle := \c:'Counter. counter.inc c;
                reset  := \c:'Counter. counter.new
             |>) : ?'a. 'a flipflop_recd1   in

    flipflop.read (flipflop.toggle (flipflop.toggle flipflop.new))``;

val ex3_res = eval[] counter_ex3;



(* Packages can also be used to simulate objects,     *)
(* in an object-oriented style hiding their contents. *)
(* From Pierce, pp. 372-373                           *)

val _ = Hol_datatype
       `cntr_methods2 =
                     <| get : 'x -> num;
                        inc : 'x -> 'x
                      |>`;

val _ = Hol_datatype
       `counter_recd2 =
                     <| state   : 'x;
                        methods : 'x cntr_methods2
                      |>`;


(* Example of a counter object containing the number 5: *)

val _ = type_abbrev ("Counter", Type `: ?'x. 'x counter_recd2`);

val c_def = Define
   `c = pack (:num,
               <| state := 5;
                  methods := <| get := \x:num. x;
                                inc := \x:num. SUC x |>
               |>)
        : ?'x. 'x counter_recd2 `;

val counter_ex4 = ``let (:'x,body) = c in body.methods.get(body.state)``;

val ex4_res = eval[c_def] counter_ex4;

val sendget_def =
   Define `sendget = \c: Counter.
                       let (:'x, body) = c in
                       body.methods.get(body.state)`;

val sendget_ty = type_of ``sendget``;

val c1_def = Define
   `c1 = let (:'x, body) = c
         in pack (: 'x,
               <| state := body.methods.inc(body.state);
                  methods := body.methods
               |> )`;

val c1_ty = type_of ``c1``;

val ex5_res = eval[c_def,c1_def] ``c1``;

val sendinc_def = Define
   `sendinc = \c: Counter.
                let (:'x, body) = c in
                     pack(: 'x,
                       <| state := body.methods.inc(body.state);
                          methods := body.methods
                       |> )`;

val sendinc_ty = type_of ``sendinc``;

val ex6_res = eval[c_def,sendinc_def] ``sendinc c``;

val add3_def = Define
   `add3 = \c:Counter. sendinc (sendinc (sendinc c))`;

val add3_ty = type_of ``add3``;

val add3_rk = rank_of_term ``add3``; (* the rank is 1 *)

val ex7 = ``let (:'x,body) = add3 c in body.methods.get(body.state)``;

val ex7_res = eval[c_def,sendinc_def,add3_def] ex7;



(* ------------------------------------------------------------ *)
(* Example 3: different packages with the same existential type *)
(*            can easily be swapped for each other              *)
(*            without affecting code that depends on them       *)
(* ------------------------------------------------------------ *)

val _ = Hol_datatype
       `collection = <| empty  : !'b. 'b 'a;
                        add    : !'b. 'b -> 'b 'a -> 'b 'a;
                        volume : !'b. 'b 'a -> num |>`;

(* ------------------------------------------------------------ *)
(* Note that a collection is parameterized by a type operator   *)
(*       'a : ty => ty.                                         *)
(* We will specialize 'a as several different operators.        *)
(* ------------------------------------------------------------ *)

(* --------------------------- *)
(* A package built using lists *)
(* --------------------------- *)

val list_recd  = ``<| empty   := \:'a. []:'a list;
                      add     := \:'a. CONS:'a -> 'a list -> 'a list;
                      volume  := \:'a. LENGTH:'a list -> num |>``;

val list_recdty = type_of list_recd;

val pack_list_col = ``pack (:list, ^list_recd)``;
val pack_list_col_ty = type_of pack_list_col;

(* note that the type ``:list`` does not appear within
   the type of pack_list_col *)

val unpack_list_col = ``let (:'coll, recd:'coll collection) = ^pack_list_col in
                          recd.volume (recd.add T (recd.add T recd.empty))``;

val ex6 = eval[] unpack_list_col; (* yields 2 *)


(* -------------------------- *)
(* A package built using sets *)
(* -------------------------- *)

val set_recd =``<| empty   := \:'a. {}:'a -> bool;
                   add     := \:'a. $INSERT:'a -> ('a -> bool) -> 'a -> bool;
                   volume  := \:'a. CARD:('a -> bool) -> num |>``;

val pack_set_col = ``pack(:\'a.'a -> bool, ^set_recd)``;
val pack_set_col_ty = type_of pack_set_col;

val unpack_set_col = ``let (:'coll, recd:'coll collection) = ^pack_set_col in
                         recd.volume (recd.add T (recd.add T recd.empty))``;

val ex7 = eval[] unpack_set_col; (* yields 1 *)


(* -------------------------- *)
(* A package built using bags *)
(* -------------------------- *)

local open bagTheory in
val BAG_CARD_THM = BAG_CARD_THM
val FINITE_BAG_THM = FINITE_BAG_THM
end

val bag_recd =``<| empty   := \:'a. {||}:'a -> num;
                   add     := \:'a. BAG_INSERT:'a -> ('a -> num) -> 'a -> num;
                   volume  := \:'a. BAG_CARD:('a -> num) -> num |>``;

val pack_bag_col = ``pack (:\'a.'a -> num, ^bag_recd)``;
val pack_bag_col_ty = type_of pack_bag_col;

val unpack_bag_col = ``let (:'coll, recd:'coll collection) = ^pack_bag_col in
                         recd.volume (recd.add T (recd.add T recd.empty))``;

val ex8 = eval[BAG_CARD_THM,FINITE_BAG_THM] unpack_bag_col; (* yields 2 *)


(* ------------------------------------------------------------------- *)
(* A function that takes any collection package, creates a collection  *)
(* of booleans by inserting T twice, and returns the resulting volume. *)
(* ------------------------------------------------------------------- *)

val add2col_def = Define
   `add2col (m : ?'col. 'col collection) =
       let (:'C, recd:'C collection) = m in
                         recd.volume (recd.add T (recd.add T recd.empty))`;

val add2list_tm = ``add2col ^pack_list_col``;
val add2set_tm  = ``add2col ^pack_set_col``;
val add2bag_tm  = ``add2col ^pack_bag_col``;


val add2list_th = save_thm("add2list_th",
       eval[add2col_def] add2list_tm);

val add2set_th  = save_thm("add2set_th",
       eval [add2col_def] add2set_tm);

val add2bag_th  = save_thm("add2bag_th",
       eval [add2col_def,BAG_CARD_THM,FINITE_BAG_THM] add2bag_tm);


(* ------------------------------------------------------------------- *)
(* The following example is inspired by David Walker's notes for his   *)
(* Programming Languages course.                                       *)
(*                                                                     *)
(* An algorithm for scheduling processes from those ready to run       *)
(* is represented in two ways: 1) as a list, where newly paused        *)
(* processes are added to the front, and the next process to run       *)
(* is selected from the rear, and 2) as a pair of lists, where         *)
(* new processes are added to the first list at the front, and         *)
(* where a process to run is removed from the second list at its front *)
(* unless it is empty, where the second list becomes the reverse of    *)
(* the first list, and the first list becomes the empty list.          *)
(*                                                                     *)
(* The properties that each representation must obey allow are listed  *)
(* in is_scheduling_q.                                                 *)
(* ------------------------------------------------------------------- *)

val _ = Hol_datatype
       `sched_q_opers = <| emptyq : !'b. 'b 'a;
                           insert : !'b. 'b -> 'b 'a -> 'b 'a;
                           remove : !'b. 'b 'a -> 'b # 'b 'a;
                           count  : !'b. 'b -> 'b 'a -> num  |>`;

val is_scheduling_q_def = Define
   `is_scheduling_q (ops:'a sched_q_opers) =
      (!:'b. !(x:'b). ops.count x (ops.emptyq[:'b:]) = 0) /\
      (!:'b. !(q:'b 'a) (x:'b) (y:'b).
                ops.count x (ops.insert y q) =
                  if x = y then ops.count x q + 1
                           else ops.count x q) /\
      (!:'b. !q:'b 'a.
              if (!x:'b. ops.count x q = 0) then T else
                let (y, q') = ops.remove q in
                !x:'b. ops.count x q = ops.count x (ops.insert y q'))`;

val _ = Hol_datatype
       `sched_q = <| this : 'b 'a;
                     ops  : 'a sched_q_opers  |>`;

open listTheory;

val COUNT_DEF = Define
  `(COUNT (x:'a) [] = 0) /\
   (COUNT x (y::ys) = if x = y then COUNT x ys + 1
                               else COUNT x ys)`;

val ALL_COUNT_ZERO = store_thm(
   "ALL_COUNT_ZERO",
   ``!xs. (!x:'a. COUNT x xs = 0) = (xs = [])``,
   Induct
   THEN REWRITE_TAC [COUNT_DEF]
   THEN GEN_TAC
   THEN REWRITE_TAC [NOT_CONS_NIL]
   THEN CONV_TAC NOT_FORALL_CONV
   THEN EXISTS_TAC ``h:'a``
   THEN SIMP_TAC arith_ss []
  );

val ALL_COUNT_ZERO_2 = store_thm(
   "ALL_COUNT_ZERO_2",
   ``!xs ys. (!x:'a. (COUNT x xs = 0) /\ (COUNT x ys = 0)) = (xs = []) /\ (ys = [])``,
   CONV_TAC (DEPTH_CONV FORALL_AND_CONV)
   THEN REWRITE_TAC [ALL_COUNT_ZERO]
  );

val COUNT_LAST = store_thm(
   "COUNT_LAST",
   ``!xs. ~(xs = []:'a list) ==>
          (COUNT (LAST xs) xs = COUNT (LAST xs) (FRONT xs) + 1)``,
   Induct
   THEN REWRITE_TAC [NOT_CONS_NIL]
   THEN GEN_TAC
   THEN ONCE_REWRITE_TAC [FRONT_DEF]
   THEN COND_CASES_TAC
   THENL
     [ ASM_REWRITE_TAC [COUNT_DEF,LAST_DEF],

       RES_TAC
       THEN ASM_REWRITE_TAC [COUNT_DEF,LAST_DEF]
       THEN SRW_TAC [ARITH_ss] []
     ]
  );

val COUNT_FRONT = store_thm(
   "COUNT_FRONT",
   ``!xs (x:'a). ~(xs = []) ==> ~(x = LAST xs) ==>
                 (COUNT x (FRONT xs) = COUNT x xs)``,
   Induct
   THEN REWRITE_TAC [NOT_CONS_NIL]
   THEN REPEAT GEN_TAC
   THEN REWRITE_TAC [FRONT_DEF,LAST_DEF]
   THEN COND_CASES_TAC
   THENL
     [ DISCH_TAC
       THEN ASM_REWRITE_TAC [COUNT_DEF],

       DISCH_TAC
       THEN RES_TAC
       THEN ASM_REWRITE_TAC [COUNT_DEF]
     ]
  );

val COUNT_APPEND = store_thm(
   "COUNT_APPEND",
   ``!xs ys (x:'a). COUNT x (xs ++ ys) = COUNT x xs + COUNT x ys``,
   Induct
   THEN ASM_SIMP_TAC list_ss [COUNT_DEF]
   THEN REPEAT GEN_TAC
   THEN COND_CASES_TAC
   THEN ASM_SIMP_TAC arith_ss []
  );

val COUNT_REVERSE = store_thm(
   "COUNT_REVERSE",
   ``!xs (x:'a). COUNT x (REVERSE xs) = COUNT x xs``,
   Induct
   THEN ASM_SIMP_TAC list_ss [COUNT_DEF,COUNT_APPEND]
   THEN REPEAT GEN_TAC
   THEN COND_CASES_TAC
   THEN ASM_SIMP_TAC arith_ss []
  );

val reference_q_def = Define
   `reference_q =
      <| this := [] : num list;
         ops  := <| emptyq := \:'b. [] : 'b list;
                    insert := \:'b. \(x:'b) xs. CONS x xs;
                    remove := \:'b. \xs:'b list. (LAST xs, FRONT xs);
                    count  := \:'b. \(x:'b) xs. COUNT x xs
                  |>
       |>`;

val reference_q_is_scheduling_q = store_thm(
   "reference_q_is_scheduling_q",
   ``is_scheduling_q reference_q.ops``,
   SRW_TAC [ARITH_ss] [reference_q_def,is_scheduling_q_def,COUNT_DEF]
   THEN REWRITE_TAC [ALL_COUNT_ZERO]
   THEN STRIP_ASSUME_TAC (ISPEC ``q:'b list`` list_CASES)
   THEN ASM_REWRITE_TAC [NOT_CONS_NIL]
   THEN GEN_TAC
   THEN SIMP_TAC list_ss [GSYM COUNT_LAST]
   THEN COND_CASES_TAC
   THEN SRW_TAC [] [COUNT_FRONT]
  );

val sched_queue_ty = ``:?'a:ty => ty. ('a,num)sched_q``;
val sched_queue_ty' = ty_antiq sched_queue_ty;

val reference_q_pkg = ``pack(:list, reference_q) : ^sched_queue_ty'``;

(* The following attempt to define REMOVE fails:

val REMOVE_def = Define
  `(REMOVE (xs:'a list) ([]:'a list) = REMOVE [] (REVERSE xs)) /\
   (REMOVE xs (y::ys) = (y, (xs,ys)))`;

One way to define REMOVE is by

val REMOVE_defn = Hol_defn "REMOVE"
  `(REMOVE [] [] = (ARB, ([],[]))) /\
   (REMOVE (xs:'a list) ([]:'a list) = REMOVE [] (REVERSE xs)) /\
   (REMOVE xs (y::ys) = (y, (xs,ys)))`;

> val REMOVE_defn =
    HOL function definition (recursive)
    
    Equation(s) :
     [..]
    |- REMOVE ([] :α list) ([] :α list) =
       ((ARB :α),([] :α list),([] :α list))
     [..]
    |- REMOVE ((v2 :α)::(v3 :α list)) ([] :α list) =
       REMOVE ([] :α list) (REVERSE (v2::v3))
     [..]
    |- REMOVE ([] :α list) ((y :α)::(ys :α list)) = (y,([] :α list),ys)
     [..]
    |- REMOVE ((v4 :α)::(v5 :α list)) ((y :α)::(ys :α list)) = (y,v4::v5,ys)
    
    Induction :
     [..]
    |- ∀(P :α list -> α list -> bool).
         P ([] :α list) ([] :α list) ∧
         (∀(v2 :α) (v3 :α list).
            P ([] :α list) (REVERSE (v2::v3)) ⇒ P (v2::v3) ([] :α list)) ∧
         (∀(y :α) (ys :α list). P ([] :α list) (y::ys)) ∧
         (∀(v4 :α) (v5 :α list) (y :α) (ys :α list). P (v4::v5) (y::ys)) ⇒
         ∀(v :α list) (v1 :α list). P v v1
    
    Termination conditions :
      0. ∀(v3 :α list) (v2 :α).
           (R :α list # α list -> α list # α list -> bool)
             (([] :α list),REVERSE (v2::v3)) (v2::v3,([] :α list))
      1. WF (R :α list # α list -> α list # α list -> bool)
     : defn

Then

Defn.tgoal REMOVE_defn;
e (WF_REL_TAC `measure (\(xs,ys). LENGTH xs)`);
e (SIMP_TAC list_ss []);


val (REMOVE_def,REMOVE_ind) =
  Defn.tprove (REMOVE_defn,
    WF_REL_TAC `measure (\(xs,ys). LENGTH xs)`
    THEN SIMP_TAC list_ss []
  );

*)

(* from which we can finally create the following definition: *)

val REMOVE_def =
  tDefine "REMOVE"
   `(REMOVE [] [] = (ARB, ([],[]))) /\
    (REMOVE (xs:'a list) ([]:'a list) = REMOVE [] (REVERSE xs)) /\
    (REMOVE xs (y::ys) = (y, (xs,ys)))`
  (WF_REL_TAC `measure (\(xs,ys). LENGTH xs)`
   THEN SIMP_TAC list_ss []);

val REMOVE_ind = theorem "REMOVE_ind";

val REMOVE_CONS = store_thm(
   "REMOVE_CONS",
   ``!xs ys (y:'a). REMOVE xs (y::ys) = (y,(xs,ys))``,
   Cases
   THEN REWRITE_TAC [REMOVE_def]
  );

val REVERSE_CONS_NOT_NIL = store_thm(
   "REVERSE_CONS_NOT_NIL",
   ``!xs (x:'a). ~(REVERSE (x::xs) = [])``,
   SIMP_TAC list_ss []
  );

val REMOVE_COUNT = store_thm(
   "REMOVE_COUNT",
   ``!xs ys (u:'a) us vs.
        (REMOVE xs ys = (u,(us,vs))) ==>
        ~((xs = []) /\ (ys = [])) ==>
          !z. COUNT z xs + COUNT z ys =
              if z = u then COUNT z us + COUNT z vs + 1
                       else COUNT z us + COUNT z vs``,
   HO_MATCH_MP_TAC REMOVE_ind
   THEN REPEAT CONJ_TAC
   THEN REPEAT GEN_TAC
   THEN SIMP_TAC list_ss [REMOVE_def,COUNT_DEF,COUNT_APPEND,COUNT_REVERSE]
   THEN CONV_TAC (RATOR_CONV (ONCE_DEPTH_CONV SYM_CONV))
   THEN STRIP_TAC
   THEN GEN_TAC
   THEN COND_CASES_TAC
   THEN ASM_SIMP_TAC arith_ss [COUNT_DEF]
  );


val efficient_q_def = Define
   `efficient_q =
      <| this := ([] : num list, [] : num list);
         ops  := <| emptyq := \:'b. ([] : 'b list, [] : 'b list);
                    insert := \:'b. \x (xs,ys). (CONS x xs, ys);
                    remove := \:'b. \(xs,ys). REMOVE xs ys;
                    count  := \:'b. \x (xs,ys). COUNT x xs + COUNT x ys
                  |>
       |>`;

val efficient_q_pkg = ``pack(:\'a. 'a list # 'a list, efficient_q)
                          : ^sched_queue_ty'``;

val check = eq_ty (type_of reference_q_pkg) (type_of efficient_q_pkg);

local open pairLib in end;

val efficient_q_is_scheduling_q = store_thm(
   "efficient_q_is_scheduling_q",
   ``is_scheduling_q efficient_q.ops``,
   SRW_TAC [ARITH_ss] [efficient_q_def,is_scheduling_q_def,COUNT_DEF]
   THEN REPEAT (POP_ASSUM MP_TAC)
   THEN PairCases_on `q`
   THEN SRW_TAC [ARITH_ss] [COUNT_DEF]
   THEN REWRITE_TAC [ALL_COUNT_ZERO_2]
   THEN POP_ASSUM MP_TAC
   THEN Cases_on `q0`
   THEN Cases_on `q1`
   THEN PairCases_on `q'`
   THEN DISCH_TAC
   THEN IMP_RES_THEN MP_TAC REMOVE_COUNT
   THEN SRW_TAC [] [COUNT_DEF]
   THEN COND_CASES_TAC
   THEN ASM_SIMP_TAC arith_ss []
  );

(* Implementation of scheduling stack *)

val stack_q_def = Define
   `stack_q =
      <| this := [] : num list;
         ops  := <| emptyq := \:'b. [] : 'b list;
                    insert := \:'b. \x xs. CONS x xs;
                    remove := \:'b. \xs. (HD xs,TL xs);
                    count  := \:'b. \x xs. COUNT x xs
                  |>
       |>`;

val stack_q_is_scheduling_q = store_thm(
   "stack_q_is_scheduling_q",
   ``is_scheduling_q stack_q.ops``,
   SRW_TAC [] [stack_q_def,is_scheduling_q_def,COUNT_DEF]
   THEN Cases_on `q`
   THEN SRW_TAC [] [COUNT_DEF]
  );

val stack_q_pkg = ``pack(:list, stack_q) : ^sched_queue_ty'``;


(* Operations on scheduling queue packages *)

(* Not allowed:

val thisp_def = Define
   `thisp (p:^sched_queue_ty') =
      let (:'a,q) = p in
        q.this`;
*)

val insertp_def = Define
   `insertp i (p:^sched_queue_ty') =
      let (:'a,q) = p in
        pack(:'a, <| this := q.ops.insert i q.this;
                     ops  := q.ops |> )`;

val emptyp_def = Define
   `emptyp (p:^sched_queue_ty') =
      let (:'a,q) = p in
        pack(:'a, <| this := q.ops.emptyq [:num:];
                     ops  := q.ops |> )`;

val removep_def = Define
   `removep (p:^sched_queue_ty') =
      let (:'a,q) = p in
      let (x,this') = q.ops.remove q.this in
        (x, pack(:'a, <| this := this';
                         ops  := q.ops |>))`;

val countp_def = Define
   `countp i (p:^sched_queue_ty') =
      let (:'a,q) = p in
      q.ops.count i q.this`;

val is_scheduling_p_def = Define
   `is_scheduling_p (p : ?'b. ('b,'a)sched_q) =
      let (:'a,q) = p in
      is_scheduling_q q.ops`;

val reference_p_def = Define
   `reference_p = pack(:list, reference_q) : ^sched_queue_ty'`;

val reference_p_is_scheduling_p = store_thm(
   "reference_p_is_scheduling_p",
   ``is_scheduling_p reference_p``,
   SIMP_TAC bool_ss [is_scheduling_p_def,reference_p_def,reference_q_is_scheduling_q]
  );

val efficient_p_def = Define
   `efficient_p = pack(:\'a. 'a list # 'a list, efficient_q) : ^sched_queue_ty'`;

val efficient_p_is_scheduling_p = store_thm(
   "efficient_p_is_scheduling_p",
   ``is_scheduling_p efficient_p``,
   SIMP_TAC bool_ss [is_scheduling_p_def,efficient_p_def,efficient_q_is_scheduling_q]
  );

val stack_p_def = Define
   `stack_p = pack(:list, stack_q) : ^sched_queue_ty'`;

val stack_p_is_scheduling_p = store_thm(
   "stack_p_is_scheduling_p",
   ``is_scheduling_p stack_p``,
   SIMP_TAC bool_ss [is_scheduling_p_def,stack_p_def,stack_q_is_scheduling_q]
  );

val scheduling_p_props = store_thm(
   "scheduling_p_props",
   ``!(p: ^sched_queue_ty').
        is_scheduling_p p ==>
        (!x. countp x (emptyp p) = 0) /\
        (!x y. countp x (insertp y p) =
               if x = y then countp x p + 1
                        else countp x p) /\
        (~(!x. countp x p = 0) ==>
               let (y,p') = removep p
               in !x. countp x p = countp x (insertp y p'))``,
   GEN_TAC
   THEN REWRITE_TAC [is_scheduling_p_def]
   THEN STRIP_ASSUME_TAC (ISPEC ``p:^sched_queue_ty'`` PACK_ONTO_AX)
   THEN ASM_REWRITE_TAC []
   THEN SIMP_TAC bool_ss []
   THEN REWRITE_TAC [is_scheduling_q_def]
   THEN REPEAT STRIP_TAC
   THENL
     [ SRW_TAC [] [countp_def,emptyp_def],

       SRW_TAC [] [countp_def,insertp_def],

       POP_ASSUM MP_TAC
       THEN SRW_TAC [] [countp_def,removep_def,insertp_def]
       THEN FIRST_ASSUM (MP_TAC o Q.SPEC `t.this` o TY_SPEC ``:num``)
       THEN COND_CASES_TAC
       THENL
         [ POP_ASSUM (STRIP_ASSUME_TAC o SPEC ``x:num``),

           SRW_TAC [] [LET_DEF]
         ]
     ]
  );

val emptyp_prop = store_thm(
   "emptyp_prop",
   ``!(p: ^sched_queue_ty').
        is_scheduling_p p ==>
        !x. countp x (emptyp p) = 0``,
   SIMP_TAC bool_ss [scheduling_p_props]
  );

val insertp_prop = store_thm(
   "insertp_prop",
   ``!(p: ^sched_queue_ty').
        is_scheduling_p p ==>
        !x y. countp x (insertp y p) =
               if x = y then countp x p + 1
                        else countp x p``,
   SIMP_TAC bool_ss [scheduling_p_props]
  );

val removep_prop = store_thm(
   "removep_prop",
   ``!(p: ^sched_queue_ty').
        is_scheduling_p p ==>
        ~(!x. countp x p = 0) ==>
               let (y,p') = removep p
               in !x. countp x p = countp x (insertp y p')``,
   SIMP_TAC bool_ss [scheduling_p_props]
  );

val _ = set_trace "types" 0;

val reference_p_props = save_thm(
   "reference_p_props",
   MATCH_MP scheduling_p_props reference_p_is_scheduling_p);

val efficient_p_props = save_thm(
   "efficient_p_props",
   MATCH_MP scheduling_p_props efficient_p_is_scheduling_p);

val stack_p_props = save_thm(
   "stack_p_props",
   MATCH_MP scheduling_p_props stack_p_is_scheduling_p);


val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "package";

val _ = export_theory();

end; (* structure packageScript *)

