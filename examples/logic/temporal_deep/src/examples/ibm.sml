(*
quietdec := true;

val home_dir = (concat Globals.HOLDIR "/examples/temporal_deep/");
loadPath := (concat home_dir "src/deep_embeddings") ::
            (concat home_dir "src/translations") ::
            (concat home_dir "src/model_check") ::
            (concat home_dir "src/tools") ::
            (concat hol_dir "examples/PSL/path") ::
            (concat hol_dir "examples/PSL/1.1/official-semantics") :: !loadPath;

map load
 ["full_ltlTheory", "arithmeticTheory", "automaton_formulaTheory", "xprop_logicTheory", "prop_logicTheory",
  "infinite_pathTheory", "tuerk_tacticsLib", "symbolic_semi_automatonTheory", "listTheory", "pred_setTheory",
  "temporal_deep_mixedTheory", "pred_setTheory", "rich_listTheory", "set_lemmataTheory", "pairTheory",
  "ltl_to_automaton_formulaTheory",
  "numLib", "listLib", "translationsLib", "rltlTheory",
  "rltl_to_ltlTheory", "psl_to_rltlTheory", "UnclockedSemanticsTheory",
  "SyntacticSugarTheory", "congLib", "temporal_deep_simplificationsLib",
  "modelCheckLib", "ibmLib"];
*)

open HolKernel boolLib bossLib  full_ltlTheory arithmeticTheory automaton_formulaTheory xprop_logicTheory prop_logicTheory
     infinite_pathTheory tuerk_tacticsLib symbolic_semi_automatonTheory listTheory pred_setTheory
     temporal_deep_mixedTheory pred_setTheory rich_listTheory set_lemmataTheory pairTheory rltlTheory
     ltl_to_automaton_formulaTheory numLib listLib translationsLib rltl_to_ltlTheory psl_to_rltlTheory UnclockedSemanticsTheory
     SyntacticSugarTheory congLib temporal_deep_simplificationsLib
     modelCheckLib ibmLib;


(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)

(*
Inputs:

0 aa
1 bb
2 cc
3 dd


assert G (aa -> next_event(bb)(cc before dd));
*)

val psl = ``
F_ALWAYS (F_IMPLIES(F_STRONG_BOOL (B_PROP (0:num)),
                    F_STRONG_NEXT_EVENT (B_PROP 1,
                                         F_STRONG_BEFORE (
                                            F_STRONG_BOOL (B_PROP 2),
                                            F_STRONG_BOOL (B_PROP 3)
                                         ))
                   )
         )``;



(*
MODULE main
# 2 envs1
  VAR aa: boolean;
# 2 envs1
  VAR bb: boolean;
# 2 envs1
  VAR cc: boolean;
# 2 envs1
  VAR dd: boolean;
  VAR sat_x1: 0..11;
  ASSIGN init(sat_x1) := ((11 union 8) union 2) union 1;
  ASSIGN next(sat_x1) := case
    sat_x1 = 1: ((1 union 11) union 8) union 2;
    (sat_x1 = 2) & (!spec_define_13): (3 union 7) union 4;
    (sat_x1 = 3) & spec_define_10: (3 union 7) union 4;
    (sat_x1 = 4) & (bb & ((!((!dd) & cc)) & (!dd))): 5 union 6;
    (sat_x1 = 5) & ((!((!dd) & cc)) & (!dd)): 5 union 6;
    (sat_x1 = 6) & ((!((!dd) & cc)) & dd): 0;
    (sat_x1 = 7) & (bb & ((!((!dd) & cc)) & dd)): 0;
    (sat_x1 = 8) & (aa & (bb & ((!((!dd) & cc)) & (!dd)))): 9 union 10;
    (sat_x1 = 9) & ((!((!dd) & cc)) & (!dd)): 9 union 10;
    1: 0;
    esac;
  DEFINE spec_define_13:= (!spec_define_11) | bb;
  DEFINE spec_define_10:= (!bb);
  DEFINE spec_define_11:= aa;
  DEFINE spec_define_0:= (!(((sat_x1 = 6) & ((!((!dd) & cc)) & dd)) | (((sat_x1 = 7) & (bb & ((!((!dd) & cc)) & dd))) | (((sat_x1 = 10) & ((!((!dd) & cc)) & dd)) | ((sat_x1 = 11) & (aa & (bb & ((!((!dd) & cc)) & dd))))))));
  DEFINE spec_define_1:= (!(((sat_x1 = 6) & ((!dd) & cc)) | (((sat_x1 = 7) & (bb & ((!dd) & cc))) | (((sat_x1 = 10) & ((!dd) & cc)) | ((sat_x1 = 11) & (aa & (bb & ((!dd) & cc))))))));
  DEFINE spec_define_2:= spec_define_14;
  DEFINE spec_define_14:= (!((!dd) & cc));
  DEFINE spec_define_3:= spec_define_15;
  DEFINE spec_define_15:= dd & (!((!dd) & cc));
  DEFINE spec_define_4:= (!spec_define_10);
  DEFINE spec_define_5:= spec_define_10;
  DEFINE spec_define_6:= spec_define_11;
  DEFINE spec_define_7:= spec_define_14;
  DEFINE spec_define_8:= (!spec_define_14);
  DEFINE spec_define_9:= (!spec_define_10);
  DEFINE spec_define_12:= (!spec_define_11);
  DEFINE spec_define_16:= (!spec_define_10);
  DEFINE spec_define_17:= spec_define_10;
  DEFINE spec_define_18:= spec_define_11;
...
*)

val pre_A = ``symbolic_semi_automaton (INTERVAL_SET 4 7)

          (P_BIGOR [X11; X8; X2; X1])

          (XP_BIGCOND [
            (XP_CURRENT X1,
             XP_NEXT (P_BIGOR [X1; X11; X8; X2]));

            (XP_CURRENT (P_AND(X2, P_NOT (P_OR (P_NOT (P_PROP 0), P_PROP 1)))),
             XP_NEXT (P_BIGOR [X3; X7; X4]));

            (XP_CURRENT (P_AND(X3, (P_NOT (P_PROP 1)))),
             XP_NEXT (P_BIGOR [X3; X7; X4]));

            (XP_CURRENT (P_AND(X4, (P_AND (P_PROP 1, P_AND(P_NOT(P_AND(P_NOT (P_PROP 3), P_PROP 2)),  P_NOT (P_PROP 3)))))),
             XP_NEXT (P_BIGOR [X5; X6]));

            (XP_CURRENT (P_AND(X5, (P_AND(P_NOT(P_AND(P_NOT (P_PROP 3), P_PROP 2)),  P_NOT (P_PROP 3))))),
             XP_NEXT (P_BIGOR [X5; X6]));

            (XP_CURRENT (P_AND(X6, (P_AND(P_NOT(P_AND(P_NOT (P_PROP 3), P_PROP 2)), (P_PROP 3))))),
             XP_NEXT X0);

            (XP_CURRENT (P_AND(X7, (P_AND (P_PROP 1, P_AND(P_NOT(P_AND(P_NOT (P_PROP 3), P_PROP 2)),  P_PROP 3))))),
             XP_NEXT X0);

            (XP_CURRENT (P_AND(X8, (P_AND (P_PROP 0, P_AND (P_PROP 1, P_AND(P_NOT(P_AND(P_NOT (P_PROP 3), P_PROP 2)),  P_NOT (P_PROP 3))))))),
             XP_NEXT (P_BIGOR [X9; X10]));

            (XP_CURRENT (P_AND(X9, (P_AND(P_NOT(P_AND(P_NOT (P_PROP 3), P_PROP 2)),  P_NOT (P_PROP 3))))),
             XP_NEXT (P_BIGOR [X9; X10]));

            (XP_TRUE,
             XP_NEXT X0)
          ])``

(*
SPECNEV       AG( ! (

((((( sat_x1)  = (
    6)))  & ((( !(( ! dd)  & (
    cc)))  & ( dd)))))  |

((

  ((((( sat_x1)  = ( 7
   )))  & ((( bb)  & ((( !
   (( ! dd)  & ( cc)))  & ( dd
   )))))))

  |
   ((
      (((
   (( sat_x1)  = ( 10)))  & ((( !
   (( ! dd)  & ( cc)))  & ( dd
   )))))  |

      ((((( sat_x1)  = (
    11)))  & ((( aa)  & (((
    bb)  & ((( !(( ! dd)  & (
    cc)))  & ( dd))))))
   )))

  ))


)))
)

*)

val pre_p = ``P_NOT (P_BIGOR [
          P_AND (X6, P_AND (P_NOT(P_AND(P_NOT (P_PROP 3), P_PROP 2)), P_PROP (3:num)));

          P_AND (X7, P_AND(P_PROP 1, P_AND (P_NOT(P_AND(P_NOT (P_PROP 3), P_PROP 2)), P_PROP 3)));

          P_AND (X10, P_AND (P_NOT(P_AND(P_NOT (P_PROP 3), P_PROP 2)), P_PROP 3));

          P_AND (X11, P_AND (P_PROP 0, P_AND (P_PROP 1, P_AND (P_NOT(P_AND(P_NOT (P_PROP 3), P_PROP 2)), P_PROP 3))))
        ])``

(*
State variables

4-7, binary encoding of the states, i.e.

sat_x1 = 0 =  NOT 7 /\ NOT 6 /\ NOT 5 /\ NOT 4
sat_x1 = 1 :  NOT 7 /\ NOT 6 /\ NOT 5 /\     4
sat_x1 = 2 :  NOT 7 /\ NOT 6 /\     5 /\ NOT 4
sat_x1 = 3 :  NOT 7 /\ NOT 6 /\     5 /\     4
sat_x1 = 4 :  NOT 7 /\     6 /\ NOT 5 /\ NOT 4
*)

fun inst_enc s t b1 b2 b3 b4 =
  let
    val x1 = if (b1 = 1) then ``P_PROP (7:num)`` else ``P_NOT (P_PROP (7:num))``
    val x2 = if (b2 = 1) then ``P_PROP (6:num)`` else ``P_NOT (P_PROP (6:num))``
    val x3 = if (b3 = 1) then ``P_PROP (5:num)`` else ``P_NOT (P_PROP (5:num))``
    val x4 = if (b4 = 1) then ``P_PROP (4:num)`` else ``P_NOT (P_PROP (4:num))``

    val l = mk_list ([x1,x2,x3,x4], type_of x1)
    val replace = mk_comb (``P_BIGAND:num prop_logic list -> num prop_logic``, l)

    val var = mk_var (s, type_of replace);
  in
    subst [var |-> replace] t
  end

fun inst_all t =
  let
    val r = t;
    val r = inst_enc "X0"  r 0 0 0 0;
    val r = inst_enc "X1"  r 0 0 0 1;
    val r = inst_enc "X2"  r 0 0 1 0;
    val r = inst_enc "X3"  r 0 0 1 1;
    val r = inst_enc "X4"  r 0 1 0 0;
    val r = inst_enc "X5"  r 0 1 0 1;
    val r = inst_enc "X6"  r 0 1 1 0;
    val r = inst_enc "X7"  r 0 1 1 1;
    val r = inst_enc "X8"  r 1 0 0 0;
    val r = inst_enc "X9"  r 1 0 0 1;
    val r = inst_enc "X10" r 1 0 1 0;
    val r = inst_enc "X11" r 1 0 1 1;
    val r = inst_enc "X12" r 1 1 0 0;
    val r = inst_enc "X13" r 1 1 0 1;
    val r = inst_enc "X14" r 1 1 1 0;
    val r = inst_enc "X15" r 1 1 1 1;

    val r_equiv_thm = SIMP_CONV list_ss [XP_BIGCOND_def, P_BIGAND_def, P_BIGOR_def,
      XP_NEXT_THM, XP_CURRENT_THM, XP_BIGAND_def, XP_BIGOR_def] r
    val r = rhs (concl r_equiv_thm)
  in
    r
  end;


val A = inst_all pre_A;
val p = inst_all pre_p;



val psl = ``
F_ALWAYS (F_IMPLIES(F_WEAK_BOOL (B_PROP (0:num)),
                    F_WEAK_NEXT_EVENT (B_PROP 1,
                                         F_WEAK_BEFORE (
                                            F_WEAK_BOOL (B_PROP 2),
                                            F_WEAK_BOOL (B_PROP 3)
                                         ))
                   )
         )``;




(*


val thm = time (model_check_ibm true A p) psl (*ca. 12 s*)
val thm = time (model_check_ibm false A p) psl (*ca. 30 min*)

val thm = time (ibm_to_ks A p) psl
val ks = lhs (concl thm)
val problem = rhs (concl thm)


val file_st = TextIO.openOut("/home/tt291/Desktop/test4.smv");


val problem_string = term_to_string problem;
val string_list = String.fields (fn x=> (x = #"\n")) problem_string
val _ = map (fn x => TextIO.output(file_st, "-- "^x^"\n")) string_list;
val _ = TextIO.output(file_st, "\n\n");
val _ = TextIO.flushOut file_st;


val vars = fair_empty_ks2smv_string ks file_st;
val _ = TextIO.closeOut file_st;

val thm_impl = time (model_check_ibm A p) psl

*)

