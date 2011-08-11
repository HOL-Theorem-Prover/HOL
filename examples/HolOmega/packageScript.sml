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

   The syntax of existential types and packages is different from that used
   in Pierce's book.  Here is a table of correspondances,
   where in Pierce's notation, X is a type variable, S and T are
   arbitrary types, t is an arbitrary term, and x is a term variable,
   and in HOL-Omega's notation, 'a is a type variable, σ stands for 
   an arbitrary type, and x is a term variable.
   In both notations, p is a package, and tm is an arbitrary term.

                                 Pierce                 HOL-Omega
                                 -----                  ---------
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

val _ = set_trace "types" 1;

val _ = new_theory "package";

local open combinTheory pred_setLib bagLib in end;


(* Existential types: *)

val ety1 = ``:?'a. 'a -> 'a``;
val ety1_vars = type_vars ety1;

val ety2 = ``:?'a. 'a -> 'b``;
val ety2_vars = type_vars ety2;

val ety3 = ``:?'a 'c. 'a -> 'b -> 'c``;
val ety3_vars = type_vars ety3;
val (ety3_bvars,ety3_body) = strip_exist_type ety3;


(* Creating packages: *)

(* Example 1: Simple package examples from Pierce, Ch.24.1, page 364-5. *)

val package = ``pack (:num, (5, \x:num. SUC x))``;
val package_ty = type_of package;

val package1 = ``pack (:num, (5, \x:num. SUC x)) : ?'x. 'x # ('x -> num)``;
val package1_ty = type_of package1;

val package2 = ``pack (:num, 0) : ?'x. 'x``;
val package2_ty = type_of package2;

val package3 = ``pack (:bool, T) : ?'x. 'x``;
val package3_ty = type_of package3;

val package4 = ``pack (:num, (0, \x:num. SUC x)) : ?'x. 'x # ('x -> num)``;
val package4_ty = type_of package4;

val package5 = ``pack (:bool, (T, \x:bool. 0)) : ?'x. 'x # ('x -> num)``;
val package5_ty = type_of package5;


(* Using packages *)

fun eval ths tm = QCONV (SIMP_CONV (srw_ss()) ths) tm;

val unpacktm4 = ``let (:'x, x:'x # ('x -> num)) = ^package4 in (SND x) (FST x)``;
val unpacktm4_res = eval[] unpacktm4;

val unpacktm5 = ``let (:'x, x:'x # ('x -> num)) = ^package5 in (SND x) (FST x)``;
val unpacktm5_res = eval[] unpacktm5;

val unpacktm4a = ``let (:'x, x:'x # ('x -> num)) = ^package4 in (\y:'x. (SND x) y) (FST x)``;
val unpacktm4a_res = eval[] unpacktm4a;

(* Create a datatype that simulates an object with access methods included. *)

val packtm1 =
  ``pack(: list, \:'elem. LENGTH:'elem list -> num)``;
val packty1 = type_of packtm1;

val packtm1' =
 ``(pack(: list,
         \:'elem. LENGTH:'elem list -> num)) :?'c. !'elem. 'elem 'c -> num``;
val packty1' = type_of packtm1';

val unpacktm1' =
  ``let (:'coll, size:!'a. 'a 'coll -> num) = ^packtm1' in T``;

val unpacktm1'' =
  ``let (:'coll:ty=>ty, size:!'a. 'a 'coll -> num)
        = pack(: list,
               \:'elem. LENGTH:'elem list -> num)
    in T``;

val res1 = HO_REWR_CONV UNPACK_PACK_AX unpacktm1'';
val res2 = SIMP_CONV bool_ss [] unpacktm1'';
val res3 = eval[] unpacktm1'';


(* Packages can be used to simulate objects, as   *)
(* abstract data types hiding the representation. *)
(* From Pierce, chapter 24, page 369.             *)

val _ = Hol_datatype
       `counter_recd1 =
                     <| new : 'a;
                        get : 'a -> num;
                        inc : 'a -> 'a
                      |>`;

val counter_kind = kind_of ``:counter_recd1``

val counterADT = ``pack ( :num,
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
        : ?'x:ty:0. 'x counter_recd2 `;

val counter_obj_ex4 = ``let (:'x,body) = c in body.methods.get(body.state)``;

val ex4_res = eval[c_def] counter_obj_ex4;

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

val sendinc_def =
   Define `sendinc = \c: Counter.
                      let (:'x, body) = c in
                            pack(: 'x,
                              <| state := body.methods.inc(body.state);
                                 methods := body.methods
                              |> )`;

val sendinc_ty = type_of ``sendinc``;

val add3_def = Define
   `add3 = \c:Counter. sendinc (sendinc (sendinc c))`;

val add3_ty = type_of ``add3``;

val add3_rk = rank_of_term ``add3``; (* the rank is 1 *)

val unpack_add3_c = ``let (:'x,body) = add3 c in body.methods.get(body.state)``;

val unpack_add3_c_val = eval[c_def,sendinc_def,add3_def] unpack_add3_c;



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


val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "package";

val _ = export_theory();

end; (* structure packageScript *)

