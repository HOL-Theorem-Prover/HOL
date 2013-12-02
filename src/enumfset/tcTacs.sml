(* File: tcTacs.sml. Author: F. Lockwood Morris. Begun 6 Aug 2013.    *)

(* Conversions culminating in TC_CONV, applicable to a term of the    *)    
(* form  (FMAP_TO_RELN (FMAPAL ... ))^+  (with  ENUMERAL-sets as      *)
(* the map values), which it proves equal to one of the form          *)
(* (FMAP_TO_RELN (FMAPAL ......... )), alternatively applicable to a  *)
(* term of the form (FMAP_TO_RELN (fmap [(.,{...}); ... ]))^+, again  *)
(* proving it equal to a term of the same form without the ^+ .       *)

structure tcTacs :> tcTacs =
struct
(* comment out load before Holmaking *)
(* app load ["pred_setTheory", "totoTacs", "enumTacs", "fmapalTacs",
             "tcTheory", "numLib"]; *)

open Parse HolKernel boolLib bossLib;
val _ = set_trace "Unicode" 0;

open enumTacs fmapalTacs tcTheory;

val AR = ASM_REWRITE_TAC [];
fun ulist x = [x];

val ERR = mk_HOL_ERR "tcTacs";
val _ = intLib.deprecate_int ();

(* A conversion to translate the most convenient explicit representation,
   namely ``fmap [(a1, {v11; ... ; v1m1}); ... ; (an, {vn1; ... ; vnmn})]``,
   of a set-valued fmap to an ENUMERAL-valued FMAPAL, given a conversion
   for working out the total order on elements, and the name of the order.
   FMAP_TO_RELN g, where g has the form of a result from ENUF_CONV, is our
   standard explicit representation of a binary relation. *)

fun ENUF_CONV keyconv keyord =
RAND_CONV (MAP_ELEM_CONV (RAND_CONV
               (TO_set_CONV NO_CONV THENC
                set_TO_ENUMERAL_CONV keyconv keyord))) THENC
fmap_TO_FMAPAL_CONV keyconv keyord;

(* ******************************************************************** *)
(* The main recursive workhorse will be TC_ITER_CONV, but there is      *)
(* set_up work to be done first; specifically we expect to have         *)
(* TC_CONV keyconv = PRE_TC_CONV keyconv THENC                          *)
(*                   RAND_CONV (TC_ITER_CONV keyconv) .                 *)
(* ******************************************************************** *)

val EMPTY_UNION_EQN = prove (``!sd:'a set. sd = {} UNION sd``,
REWRITE_TAC [pred_setTheory.UNION_EMPTY]);

(* Catholic PRE_TC_CONV, works for fmap or FMAPAL terms. *)

fun PRE_TC_CONV keyconv Aplus =
let val A = rand Aplus;
    val hypb = ISPEC A subTC_EMPTY;
    val hypa =
        SYM ((FDOM_CONV THENC
              TO_set_CONV keyconv THENC
              REWR_CONV EMPTY_UNION_EQN) ``FDOM ^(rand A)``)
in MATCH_MP TC_ITER_THM (CONJ hypa hypb) end;

fun TC_MOD_CONV keyconv =
REWR_CONV TC_MOD THENC
RATOR_CONV (RATOR_CONV (RAND_CONV (IN_CONV keyconv))) THENC COND_CONV THENC
TRY_CONV (UNION_CONV keyconv);

val [tc_iter_NIL, tc_iter_CONS] = CONJUNCTS TC_ITER;

(* tc_iter_NIL = |- !r. TC_ITER [] r = r
   tc_iter_CONS =
   |- !x d r. TC_ITER (x::d) r = TC_ITER d (TC_MOD x (r ' x) o_f r) *)

fun TC_ITER_CONV keyconv =
let fun tci t =
((REWR_CONV tc_iter_CONS THENC
  RAND_CONV (LAND_CONV (RAND_CONV (FAPPLY_CONV keyconv)) THENC
             o_f_CONV (TC_MOD_CONV keyconv)) THENC
  tci) ORELSEC
 REWR_CONV tc_iter_NIL) t
in tci end;

fun TC_CONV keyconv = PRE_TC_CONV keyconv THENC
                      RAND_CONV (TC_ITER_CONV keyconv);

(* *** examples for debugging and timing: *** *)
(* ******************************************
open numLib totoTacs;
val cormenex = ``[(2, {4; 3}); (3, {2}); (4, {3; 1}); (1, {})]``;
    ENUF_CONV numto_CONV ``numto``
    ``fmap [(2, set [4; 3]); (3, set [2]); (4, set [3; 1]); (1, set [])]``;
val corfmap = rand (concl (ENUF_CONV numto_CONV ``numto`` ``fmap ^cormenex``));

   val Aplus = ``(FMAP_TO_RELN ^corfmap)^+``;
   val keyconv = numto_CONV; 

   PRE_TC_CONV keyconv ``(FMAP_TO_RELN ^corfmap)^+``; 
   PRE_TC_CONV NO_CONV ``(FMAP_TO_RELN (fmap ^cormenex))^+``; 

   val s123 = rand (concl (DISPLAY_TO_ENUMERAL_CONV
                           numto_CONV ``numto`` ``{1; 2; 3}``));
   val s345 = rand (concl (DISPLAY_TO_ENUMERAL_CONV
                           numto_CONV ``numto`` ``{5; 4; 3}``));
   TC_MOD_CONV numto_CONV ``TC_MOD 5 ^s123 ^s345``;
   TC_MOD_CONV numto_CONV ``TC_MOD 5 ^s345 ^s123``; 
   val t123 = ``{1; 2; 3}``;
   val t345 = ``{5; 4; 3}``;
   TC_MOD_CONV REDUCE_CONV ``TC_MOD 5 ^t123 ^t345``;
   TC_MOD_CONV REDUCE_CONV ``TC_MOD 5 ^t345 ^t123``;

   val tcit =
   rand (rand (concl (PRE_TC_CONV keyconv ``(FMAP_TO_RELN ^corfmap)^+``)));
   TC_ITER_CONV keyconv tcit;
  val tins = rand (rand (concl (PRE_TC_CONV NO_CONV
                                 ``(FMAP_TO_RELN (fmap ^cormenex))^+``)));
   TC_ITER_CONV REDUCE_CONV tins;

   Count.apply (TC_CONV numto_CONV) ``(FMAP_TO_RELN ^corfmap)^+``;
                                           (*runtime:  0.036s, Prims:    7038*)
   val one_to_ten = ``fmap [(1,{4}); (2,{6}); (3,{1}); (4,{5}); (5,{9});
                            (6,{8}); (8,{10}); (9,{2}); (10,{7})]``;
   val one_ten_chain = rand (concl (
       Count.apply (ENUF_CONV numto_CONV ``numto``) one_to_ten));
                                           (*runtime:  0.008s, Prims:    2699*)

val small_tc = rand (concl (
   Count.apply (TC_CONV numto_CONV) ``(FMAP_TO_RELN ^one_ten_chain)^+``));
                                           (*runtime:  0.164s, Prims:   24049*)

   Count.apply (TC_CONV REDUCE_CONV) ``(FMAP_TO_RELN ^one_to_ten)^+``;
                                           (*runtime:  0.052s, Prims:   18127*)
   rand (concl (Count.apply 
     (RAND_CONV (FMAPAL_TO_fmap_CONV numto_CONV) THENC
                 RAND_CONV (MAP_ELEM_CONV (RAND_CONV
                   (ENUMERAL_TO_DISPLAY_CONV numto_CONV))))
              small_tc));

val ls = rand (rand (concl (FMAPAL_TO_fmap_CONV numto_CONV (rand small_tc))));

rand (concl
      (MAP_ELEM_CONV (RAND_CONV (ENUMERAL_TO_DISPLAY_CONV numto_CONV)) ls));

val beer_bottles = ``fmap
[(99,{98}); (98,{97}); (97,{96}); (96,{95}); (95,{94});
 (94,{93}); (93,{92}); (92,{91}); (91,{90}); (90,{89});
 (89,{88}); (88,{87}); (87,{86}); (86,{85}); (85,{84});
 (84,{83}); (83,{82}); (82,{81}); (81,{80}); (80,{79});
 (79,{78}); (78,{77}); (77,{76}); (76,{75}); (75,{74});
 (74,{73}); (73,{72}); (72,{71}); (71,{70}); (70,{69});
 (69,{68}); (68,{67}); (67,{66}); (66,{65}); (65,{64});
 (64,{63}); (63,{62}); (62,{61}); (61,{60}); (60,{59});
 (59,{58}); (58,{57}); (57,{56}); (56,{55}); (55,{54});
 (54,{53}); (53,{52}); (52,{51}); (51,{50}); (50,{49});
 (49,{48}); (48,{47}); (47,{46}); (46,{45}); (45,{44});
 (44,{43}); (43,{42}); (42,{41}); (41,{40}); (40,{39});
 (39,{38}); (38,{37}); (37,{36}); (36,{35}); (35,{34});
 (34,{33}); (33,{32}); (32,{31}); (31,{30}); (30,{29});
 (29,{28}); (28,{27}); (27,{26}); (26,{25}); (25,{24});
 (24,{23}); (23,{22}); (22,{21}); (21,{20}); (20,{19});
 (19,{18}); (18,{17}); (17,{16}); (16,{15}); (15,{14});
 (14,{13}); (13,{12}); (12,{11}); (11,{10}); (10,{9}); (9,{8});
 (8,{7}); (7,{6}); (6,{5}); (5,{4}); (4,{3}); (3,{2}); (2,{1}); (1,{0})]``;

val beer_chain = rand (concl (
 Count.apply (ENUF_CONV numto_CONV ``numto``) beer_bottles));
                                          (*runtime:  0.196s, Prims:   41576*)

 val beer_tc_fmapal = rand (rand (concl (
 Count.apply (TC_CONV numto_CONV) ``(FMAP_TO_RELN ^beer_chain)^+``)));
                                          (*runtime: 11.941s, Prims: 2455910*)
              (* reduced from 2526365 without use of OL_bt, bt_to_list_CONV *)
 Count.apply (FMAPAL_TO_fmap_CONV numto_CONV)
              beer_tc_fmapal;
              (*runtime: 0.032s, Prims: 7728 *)
rand (concl
 (Count.apply (MAP_ELEM_CONV (RAND_CONV (ENUMERAL_TO_DISPLAY_CONV numto_CONV)))
  (rand (rand (concl (FMAPAL_TO_fmap_CONV numto_CONV beer_tc_fmapal))))));
                   (*runtime: 3.256s, Prims: 418538*)
(* Unreasonable amount of work converting, but one can finally read the
   output and see that it is correct. *)

 Count.apply (FAPPLY_CONV numto_CONV) ``^beer_tc_fmapal ' 50``;
                                          (*runtime:  0.004s,  Prims:    250*)

(* |- (FMAP_TO_RELN
      (FMAPAL numto
         (node
            (node
               (node (node nt (1,ENUMERAL numto (node nt 0 nt)) nt)
                  (2,ENUMERAL numto (node nt 1 nt))
                  (node nt (3,ENUMERAL numto (node nt 2 nt)) nt))

...
                        (node
                           (node nt (97,ENUMERAL numto (node nt 96 nt))
                              nt) (98,ENUMERAL numto (node nt 97 nt))
                           (node nt (99,ENUMERAL numto (node nt 98 nt))
                              nt)))))))))^+ =
   FMAP_TO_RELN
     (FMAPAL numto
        (node
           (node
              (node (node nt (1,ENUMERAL numto (node nt 0 nt)) nt)
                 (2,ENUMERAL numto (node nt 0 (node nt 1 nt)))
                 (node nt
                    (3,
                     ENUMERAL numto
                       (node (node nt 0 nt) 1 (node nt 2 nt))) nt))
...
                                               (node (node nt 92 nt) 93
                                                  (node nt 94 nt)) 95
                                               (node (node nt 96 nt) 97
                                                  (node nt 98 nt))))))))
                             nt)))))))) *)

val beer_tc_fmap =  rand (rand (concl (Count.apply (TC_CONV REDUCE_CONV)
                                ``(FMAP_TO_RELN ^beer_bottles)^+``)));
                                          (*runtime: 44.783s,Prims:23956961*)

(* |- (FMAP_TO_RELN
      (fmap
         [(99,{98}); (98,{97}); (97,{96}); (96,{95}); (95,{94});
          (94,{93}); (93,{92}); (92,{91}); (91,{90}); (90,{89});
...
          (8,{7}); (7,{6}); (6,{5}); (5,{4}); (4,{3}); (3,{2}); (2,{1});
          (1,{0})]))^+ =
   FMAP_TO_RELN
     (fmap
        [(99,
          {98; 97; 96; 95; 94; 93; 92; 91; 90; 89; 88; 87; 86; 85; 84;
           83; 82; 81; 80; 79; 78; 77; 76; 75; 74; 73; 72; 71; 70; 69;
...
         (5,{4; 3; 2; 1; 0}); (4,{3; 2; 1; 0}); (3,{2; 1; 0});
         (2,{1; 0}); (1,{0})]): *)

Count.apply (FAPPLY_CONV REDUCE_CONV) ``^beer_tc_fmap ' 50``;
                                             (*runtime: 0.016s, Prims: 4077*)
**************************** *)
end;
