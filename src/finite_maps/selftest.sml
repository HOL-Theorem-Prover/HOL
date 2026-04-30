open HolKernel Parse boolLib bossLib sptreeSyntax sptreeLib testutils
open totoTheory  totoTacs tcTacs enumTacs fmapalTacs;
open alist_treeLib patriciaLib

fun optionToString f NONE = "NONE"
  | optionToString f (SOME x) = "SOME("^f x^")"
fun pairToString f g (x,y) = "(" ^ f x ^ ", " ^ g y ^ ")"

val _ = app tpp ["fm⟨k⟩", "fm⟨k1 ↦ v1; k2 ↦ v2⟩"]

val _ = tprint "Check that finite maps have plausible size in TypeBase"
val _ = require_msg
          (check_result (fn (t,th) => null (free_vars t)))
          (pairToString term_to_string thm_to_string) TypeBase.size_of
          “:'a |-> 'b”

fun testeval (s, t, expected) =
  let
    val _ = tprint s
  in
    require_msg (check_result (aconv expected)) term_to_string
                (rhs o concl o EVAL) t
  end

val _ = tprint "sptreeSyntax.fromList"
val tm1 =
    fromList (List.tabulate (100, fn i => numSyntax.term_of_int (2 * i)))
             handle HOL_ERR _ => (die "FAILED"; boolSyntax.T)
val _ = OK()
val _ = tprint "sptreeSytax.fromAList"
val tm2 =
    fromAList
      (List.tabulate
         (100, fn i => (Arbnum.fromInt (2 * i), numSyntax.term_of_int i)))
      handle HOL_ERR _ => (die "FAILED"; boolSyntax.T)
val _ = OK()


val _ = app testeval [
  ("EVAL fromAList",
    ``fromAList [(23746, a:num); (73246, b); (912, c); (0, d)] =
      fromAList [(0, d); (73246, b); (23746, a:num); (912, c)]``,
    boolSyntax.T),
  ("EVAL fromList",
   ``fromList [a;b;c;d:num]``,
   ``BS (LS c) (a:num) (BS LN b (LS d))``),
  ("EVAL wf o fromList", ``wf ^tm1``, boolSyntax.T),
  ("EVAL wf o fromAList", ``wf ^tm2``, boolSyntax.T),
  ("EVAL mapi",
   ``mapi (arithmetic$+) (fromList [1;2;3]) =
     fromList [1;3;5]``,
   boolSyntax.T),
  ("EVAL toSortedAList",
   ``toSortedAList (fromAList [(23940, a:num); (22, b); (1, c); (234, d)]) =
     [(1, c); (22, b); (234, d); (23940, a)]``,
   boolSyntax.T),
  ("EVAL toSortedAList fromList",
   ``toSortedAList (fromList [239n; 1; 4; 123; 5]) =
     [(0, 239); (1, 1); (2, 4); (3, 123); (4, 5)]``,
   boolSyntax.T)
]

val _ = tprint "Testing TeX form of finite map printing"
val _ = require_msg
          (check_result (equal "\\alpha{} \\HOLTokenMapto{} \\beta{}"))
          String.toString
          (PP.pp_to_string 70 EmitTeX.pp_type_as_tex) “:'a |-> 'b”



val _ = temp_add_sptree_printer ()
val _ = remove_sptree_printer ()
val _ = temp_add_sptree_printer ()

fun tpp' (i,out) =
  tpp_expected {testf = standard_tpp_message, input = i, output = out}
val _ = app tpp' [
  ("BS (LS c) (a:num) (BS LN b (LS d))", "sptree$fromList [a; b; c; d]"),
  ("BS LN (a:num) (BS LN b (LS d))", "sptree$fromAList [(0,a); (1,b); (3,d)]")
]


(* File: enumfDemo Author: F. Lockwood Morris created: 17 Dec. 2013 *)

(* A small example exercising much of the finite-sets-and-maps package
   via computation of a transitive closure of a relation whose element
   type is string # num. *)

(* Start with the Hasse diagram of the relation of lineal descent
   on nine of the Romanov emperors. *)

val RomHasse =
``fmap [(("PETER", 1), {("PETER", 3)});
        (("PETER", 3), {("PAUL", 1)});
        (("CATHERINE", 2), {("PAUL", 1)});
        (("PAUL", 1), {("ALEXANDER", 1); ("NICHOLAS", 1)});
        (("NICHOLAS", 1), {("ALEXANDER", 2)});
        (("ALEXANDER", 2), {("ALEXANDER", 3)});
        (("ALEXANDER", 3), {("NICHOLAS", 2)})]``;

val tsarto_CONV = lextoto_CONV stringto_CONV numto_CONV;

val RomH = ENUF_CONV tsarto_CONV ``stringto lextoto numto`` RomHasse;

val tsar_tc = ``(FMAP_TO_RELN ^(rand (concl RomH)))^+``;

val tsar_anc_thm = Count.apply (TC_CONV tsarto_CONV) tsar_tc;
(* 21401 primitive inferences *)

val tsar_enum_fmap = Count.apply (FMAPAL_TO_fmap_CONV tsarto_CONV)
              (rand (rand (concl tsar_anc_thm)));
(* 912 primitive inferences *)

val alist =
rand (concl
 (Count.apply (MAP_ELEM_CONV (RAND_CONV (ENUMERAL_TO_DISPLAY_CONV tsarto_CONV)))
  (rand (rand (concl tsar_enum_fmap)))));
(* 3665 primitive inferences *)

(* Find that the transitive closure holds of a particular pair *)

val tcpair = let
  val tc_fmapal = rand (rand (concl tsar_anc_thm))
  val testNic2 = ``("NICHOLAS", 2) IN (^tc_fmapal ' ("PETER", 1))``
in
  (Count.apply (RAND_CONV (FAPPLY_CONV tsarto_CONV)) (* 178 prim infs *) THENC
   Count.apply (IN_CONV tsarto_CONV) (* 221 prim infs *)) testNic2
end;

(* Same example the asymptotically slow way, with no trees. *)

val TSAR_EQ_CONV =
  REWR_CONV pairTheory.PAIR_EQ THENC
  RATOR_CONV (RAND_CONV stringLib.string_EQ_CONV) THENC
  numLib.REDUCE_CONV

val tsar_anc_no_trees =
    Count.apply (TC_CONV TSAR_EQ_CONV) ``(FMAP_TO_RELN ^RomHasse)^+``;
(* 15254 primitive inferences *)

(* Find that the transitive closure holds of a particular pair *)

val tcpair' = let
  val tc_fmap = rand (rand (concl tsar_anc_no_trees))
  val testNic2 = ``("NICHOLAS", 2) IN (^tc_fmap ' ("PETER", 1))``
in
  (Count.apply (RAND_CONV (FAPPLY_CONV TSAR_EQ_CONV)) (* 66 prim infs *) THENC
   Count.apply (IN_CONV TSAR_EQ_CONV) (* 473 prim infs *)) testNic2
end;

(* ----------------------------------------------------------------------
   enumTacs convolution tests, ported from a comment block at the
   bottom of enumTacs.sml.  These exercise the public API.  The
   original block also tested private helpers not exported from
   enumTacs (REVERS_CONV, smerge_CONV, incr_smerge_CONV,
   incr_sbuild_CONV, smerge_out_CONV, incr_ssort_CONV, sinter_CONV,
   sdiff_CONV, bt_to_ol_lb_ub_CONV, bt_to_ol_ub_CONV,
   bt_to_ol_lb_CONV, bt_to_ol_CONV); those tests stay behind the
   structure boundary.

   Expected outputs were captured by running each conversion in HOL
   once and baked in here so the build catches regressions in
   downstream behaviour, not just exceptions.
   ---------------------------------------------------------------------- *)

(* For functions whose result is a theorem but not a |- input = output
   rewrite (e.g. OWL_TO_ENUMERAL : thm -> thm, OWL_UNION etc.), check
   that the resulting concl is alpha-equivalent to a captured target. *)
fun thmCheck nm expected k =
  (tprint nm;
   require_msg (check_result (fn th => aconv (concl th) expected))
               thm_to_string k ())

val blco = ``BL_CONS 5 (onebl 7 nt (zerbl (onebl 11
                  (node (node nt 8 nt) 9 (node nt 10 nt)) nbl)))``;
val _ = convtest ("BL_CONS_CONV/blco", BL_CONS_CONV, blco,
  ``zerbl (onebl 5 (node nt 7 nt)
            (onebl 11 (node (node nt 8 nt) 9 (node nt 10 nt)) nbl))``);

val ltb = ``list_to_bl [(1,()); (2,()); (3,()); (4,())]``;
val _ = convtest ("list_to_bl_CONV/ltb", list_to_bl_CONV, ltb,
  ``zerbl (zerbl (onebl (1,())
            (node (node nt (2,()) nt) (3,()) (node nt (4,()) nt)) nbl))``);

val _ = convtest ("set_TO_ENUMERAL_CONV/setlist",
  set_TO_ENUMERAL_CONV numto_CONV ``numto``,
  ``set [10; 9; 8; 7; 6; 5; 4; 3; 2; 1]``,
  ``ENUMERAL numto
      (node (node nt 1 (node nt 2 nt)) 3
        (node (node (node nt 4 nt) 5 (node nt 6 nt)) 7
          (node (node nt 8 nt) 9 (node nt 10 nt))))``);

val bltt = ``bl_to_bt (onebl (1,()) nt
        (zerbl
           (onebl (3,())
              (node (node nt (5,()) nt) (7,()) (node nt (9,()) nt))
              nbl)))``;
val _ = convtest ("bl_to_bt_CONV/bltt", bl_to_bt_CONV, bltt,
  ``node (node nt (1,()) nt) (3,())
      (node (node nt (5,()) nt) (7,()) (node nt (9,()) nt))``);

val _ = convtest ("list_to_bt_CONV/ltbt", list_to_bt_CONV,
  ``list_to_bt [(1,()); (2,()); (3,()); (4,())]``,
  ``node nt (1,())
      (node (node nt (2,()) nt) (3,()) (node nt (4,()) nt))``);

val _ = convtest ("DISPLAY_TO_set_CONV/small", DISPLAY_TO_set_CONV,
  ``{5; 4; 6; 3; 3; 2}``,
  ``set [5; 4; 6; 3; 3; 2]``);

val _ = convtest ("DISPLAY_TO_ENUMERAL_CONV/dups",
  DISPLAY_TO_ENUMERAL_CONV numto_CONV ``numto``,
  ``{3; 4; 6; 7; 7; 7; 7; 3; 3}``,
  ``ENUMERAL numto (node nt 3 (node (node nt 4 nt) 6 (node nt 7 nt)))``);

val _ = convtest ("DISPLAY_TO_ENUMERAL_CONV/eights",
  DISPLAY_TO_ENUMERAL_CONV numto_CONV ``numto``,
  ``{5; 6; 4; 8; 8; 8; 3; 1}``,
  ``ENUMERAL numto
      (node (node nt 1 (node nt 3 nt)) 4
        (node (node nt 5 nt) 6 (node nt 8 nt)))``);

val s50 = ``{10;19;18;17;16;15;14;13;12;11;
       40;41;42;43;44;45;56;57;48;49;50;59;58;57;56;55;54;53;52;51;
       99;98;96;93;89;84;80;82;85;88;92;95;97;81;83;87;92;91;90;94}``;
val _ = convtest ("DISPLAY_TO_ENUMERAL_CONV/s50",
  DISPLAY_TO_ENUMERAL_CONV numto_CONV ``numto``, s50,
  ``ENUMERAL numto
      (node (node (node (node (node nt 10 nt) 11 (node nt 12 nt)) 13
                          (node (node nt 14 nt) 15 (node nt 16 nt))) 17
                  (node (node (node nt 18 nt) 19 (node nt 40 nt)) 41
                          (node (node nt 42 nt) 43 (node nt 44 nt)))) 45
              (node (node (node (node (node nt 48 nt) 49 (node nt 50 nt)) 51
                                  (node (node nt 52 nt) 53 (node nt 54 nt))) 55
                          (node (node (node nt 56 nt) 57 (node nt 58 nt)) 59
                                  (node (node nt 80 nt) 81 (node nt 82 nt)))) 83
                      (node (node (node (node nt 84 nt) 85 (node nt 87 nt)) 88
                                    (node (node nt 89 nt) 90 (node nt 91 nt))) 92
                              (node (node (node nt 93 nt) 94 (node nt 95 nt)) 96
                                      (node (node nt 97 nt) 98
                                              (node nt 99 nt))))))``);
val _ = convtest ("DISPLAY_TO_ENUMERAL_CONV/qs50",
  DISPLAY_TO_ENUMERAL_CONV qk_numto_CONV ``qk_numto``, s50,
  ``ENUMERAL qk_numto
      (node (node (node (node (node nt 15 nt) 95 (node nt 55 nt)) 87
                          (node (node nt 11 nt) 19 (node nt 99 nt))) 51
                  (node (node (node nt 83 nt) 43 (node nt 59 nt)) 91
                          (node (node nt 17 nt) 97 (node nt 49 nt)))) 81
              (node (node (node (node (node nt 41 nt) 57 (node nt 89 nt)) 13
                                  (node (node nt 53 nt) 85 (node nt 45 nt))) 93
                          (node (node (node nt 16 nt) 96 (node nt 48 nt)) 80
                                  (node (node nt 40 nt) 56 (node nt 88 nt)))) 12
                      (node (node (node (node nt 52 nt) 84 (node nt 44 nt)) 92
                                    (node (node nt 10 nt) 18 (node nt 98 nt))) 50
                              (node (node (node nt 82 nt) 42 (node nt 58 nt)) 90
                                      (node (node nt 14 nt) 54
                                              (node nt 94 nt))))))``);

val _ = convtest ("IN_CONV/apft", IN_CONV numto_CONV,
  ``5 IN ENUMERAL numto (node nt 5 nt)``, ``T``);
val _ = convtest ("IN_CONV/apgt", IN_CONV numto_CONV,
  ``6 IN ENUMERAL numto (node nt 5 nt)``, ``F``);
val _ = convtest ("IN_CONV/red5", IN_CONV numLib.REDUCE_CONV,
  ``5 IN {3; 5; 2}``, ``T``);
val _ = convtest ("IN_CONV/red6", IN_CONV numLib.REDUCE_CONV,
  ``6 IN {3; 5; 2}``, ``F``);

val fake = ASSUME ``OWL numto {5; 4; 3} [3; 4; 5]``;
val _ = thmCheck "OWL_TO_ENUMERAL/fake"
  ``{5; 4; 3} = ENUMERAL numto (node (node nt 3 nt) 4 (node nt 5 nt))``
  (fn () => OWL_TO_ENUMERAL fake);

val _ = convtest ("bt_to_list_CONV/btlin", bt_to_list_CONV,
  ``bt_to_list_ac
      (node (node nt 1 nt) 2
            (node (node nt 3 nt) 4 (node nt 5 nt)))
      []``,
  ``[1; 2; 3; 4; 5]``);

val tet = rand (concl (DISPLAY_TO_ENUMERAL_CONV
                         numto_CONV ``numto`` ``{4;1;3;5;2}``));
val owa = ENUMERAL_TO_OWL numto_CONV tet;
val _ = thmCheck "ENUMERAL_TO_OWL/tet"
  ``OWL numto
      (ENUMERAL numto (node (node nt 1 nt) 2
                              (node (node nt 3 nt) 4 (node nt 5 nt))))
      [1; 2; 3; 4; 5]``
  (fn () => owa);

val _ = convtest ("ENUMERAL_TO_set_CONV/tet",
  ENUMERAL_TO_set_CONV numto_CONV, tet, ``set [1; 2; 3; 4; 5]``);
val _ = convtest ("ENUMERAL_TO_DISPLAY_CONV/tet",
  ENUMERAL_TO_DISPLAY_CONV numto_CONV, tet, ``{1; 2; 3; 4; 5}``);

val _ = convtest ("TO_set_CONV/tet", TO_set_CONV numto_CONV, tet,
  ``set [1; 2; 3; 4; 5]``);
val _ = convtest ("TO_set_CONV/disp", TO_set_CONV NO_CONV,
  ``{5; 4; 3; 2; 1}``, ``set [5; 4; 3; 2; 1]``);
val _ = convtest ("TO_set_CONV/setl", TO_set_CONV NO_CONV,
  ``set [5; 4; 3; 2; 1]``, ``set [5; 4; 3; 2; 1]``);
val _ = convtest ("set_TO_DISPLAY_CONV/setl", set_TO_DISPLAY_CONV,
  ``set [5;4;3;2;1]``, ``{5; 4; 3; 2; 1}``);

val owb = ENUMERAL_TO_OWL numto_CONV
            (rand (concl (DISPLAY_TO_ENUMERAL_CONV
                            numto_CONV ``numto`` ``{0;3;1;8}``)));
val _ = thmCheck "ENUMERAL_TO_OWL/owb"
  ``OWL numto
      (ENUMERAL numto (node nt 0 (node (node nt 1 nt) 3 (node nt 8 nt))))
      [0; 1; 3; 8]``
  (fn () => owb);

val _ = thmCheck "OWL_UNION/owa-owb"
  ``OWL numto
      (ENUMERAL numto (node (node nt 1 nt) 2
                              (node (node nt 3 nt) 4 (node nt 5 nt)))
       UNION
       ENUMERAL numto (node nt 0
                              (node (node nt 1 nt) 3 (node nt 8 nt))))
      [0; 1; 2; 3; 4; 5; 8]``
  (fn () => OWL_UNION numto_CONV owa owb);

val _ = thmCheck "OWL_UNION/owb-owa"
  ``OWL numto
      (ENUMERAL numto (node nt 0
                              (node (node nt 1 nt) 3 (node nt 8 nt)))
       UNION
       ENUMERAL numto (node (node nt 1 nt) 2
                              (node (node nt 3 nt) 4 (node nt 5 nt))))
      [0; 1; 2; 3; 4; 5; 8]``
  (fn () => OWL_UNION numto_CONV owb owa);

val wet = rand (concl (DISPLAY_TO_ENUMERAL_CONV
                         numto_CONV ``numto`` ``{8;3;1;0}``));
val _ = convtest ("UNION_CONV/utwet", UNION_CONV numto_CONV,
  ``^tet UNION ^wet``,
  ``ENUMERAL numto (node (node (node nt 0 nt) 1 (node nt 2 nt)) 3
                          (node (node nt 4 nt) 5 (node nt 8 nt)))``);
val _ = convtest ("UNION_CONV/red", UNION_CONV numLib.REDUCE_CONV,
  ``{1;5} UNION {3;2}``, ``{1; 5; 3; 2}``);

val _ = thmCheck "OWL_INTER/owa-owb"
  ``OWL numto
      (ENUMERAL numto (node (node nt 1 nt) 2
                              (node (node nt 3 nt) 4 (node nt 5 nt)))
       INTER
       ENUMERAL numto (node nt 0
                              (node (node nt 1 nt) 3 (node nt 8 nt))))
      [1; 3]``
  (fn () => OWL_INTER numto_CONV owa owb);

val _ = convtest ("INTER_CONV/itwet", INTER_CONV numto_CONV,
  ``^tet INTER ^wet``,
  ``ENUMERAL numto (node nt 1 (node nt 3 nt))``);

val _ = thmCheck "OWL_DIFF/owa-owb"
  ``OWL numto
      (ENUMERAL numto (node (node nt 1 nt) 2
                              (node (node nt 3 nt) 4 (node nt 5 nt)))
       DIFF
       ENUMERAL numto (node nt 0
                              (node (node nt 1 nt) 3 (node nt 8 nt))))
      [2; 4; 5]``
  (fn () => OWL_DIFF numto_CONV owa owb);

val _ = convtest ("SET_DIFF_CONV/itwetD", SET_DIFF_CONV numto_CONV,
  ``^tet DIFF ^wet``,
  ``ENUMERAL numto (node (node nt 2 nt) 4 (node nt 5 nt))``);

val ta = rand (concl (DISPLAY_TO_ENUMERAL_CONV
                        numto_CONV ``numto`` ``{4;1;3;5;2}``));
val tb = rand (concl (DISPLAY_TO_ENUMERAL_CONV
                        numto_CONV ``numto`` ``{3; 4; 6; 7; 3}``));
val tc = rand (concl (DISPLAY_TO_ENUMERAL_CONV
                        numto_CONV ``numto`` ``{5; 6; 4; 8; 3; 1}``));

val _ = thmCheck "SET_EXPR_TO_OWL/uniinter"
  ``OWL numto
      (ENUMERAL numto (node (node nt 1 nt) 2
                              (node (node nt 3 nt) 4 (node nt 5 nt)))
       UNION
       ENUMERAL numto (node nt 3
                              (node (node nt 4 nt) 6 (node nt 7 nt)))
       INTER
       ENUMERAL numto (node (node nt 1 (node nt 3 nt)) 4
                              (node (node nt 5 nt) 6 (node nt 8 nt))))
      [1; 2; 3; 4; 5; 6]``
  (fn () => SET_EXPR_TO_OWL numto_CONV
              ``(^ta) UNION (^tb) INTER (^tc)``);

val _ = convtest ("SET_EXPR_CONV/uniinter", SET_EXPR_CONV numto_CONV,
  ``(^ta) UNION (^tb) INTER (^tc)``,
  ``ENUMERAL numto (node (node nt 1 (node nt 2 nt)) 3
                          (node (node nt 4 nt) 5 (node nt 6 nt)))``);
val _ = convtest ("SET_EXPR_CONV/unidiff", SET_EXPR_CONV numto_CONV,
  ``(^tb) UNION (^tc) DIFF (^ta)``,
  ``ENUMERAL numto (node (node nt 6 nt) 7 (node nt 8 nt))``);
val _ = convtest ("SET_EXPR_CONV/idta", SET_EXPR_CONV numto_CONV, ta,
  ``ENUMERAL numto (node (node nt 1 nt) 2
                          (node (node nt 3 nt) 4 (node nt 5 nt)))``);

val _ = thmCheck "set_TO_OWL/setl"
  ``OWL numto (set [5; 3; 3; 3; 4; 2; 3; 1]) [1; 2; 3; 4; 5]``
  (fn () => set_TO_OWL numto_CONV ``numto``
              ``set [5; 3; 3; 3; 4; 2; 3; 1]``);
val _ = thmCheck "set_TO_OWL/disp"
  ``OWL numto {5; 3; 3; 3; 4; 2; 3; 1} [1; 2; 3; 4; 5]``
  (fn () => set_TO_OWL numto_CONV ``numto``
              ``{5; 3; 3; 3; 4; 2; 3; 1}``);
