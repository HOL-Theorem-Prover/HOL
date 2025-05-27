(* ===================================================================== *)
(* VERSION       : 7.0                                                   *)
(* FILE          : tactics.sml                                           *)
(* DESCRIPTION   : General purpose tactics for obj library.              *)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier                                 *)
(* DATE          : October 19, 2000                                      *)
(* COPYRIGHT     : Copyright (c) 2000 by Peter Vincent Homeier           *)
(*                                                                       *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* This file contains new tactics of general usefulness.                 *)
(* --------------------------------------------------------------------- *)

structure tactics :> tactics =
struct


open HolKernel Parse boolLib;

(* --------------------------------------------------------------------- *)
(* Need conditional rewriting.                                           *)
(* --------------------------------------------------------------------- *)
open dep_rewrite;
open listTheory;
open PairedLambda;


(* --------------------------------------------------------------------- *)
(* Load the Hol 98 specific customization.                               *)
(* --------------------------------------------------------------------- *)
(*
open hol98specific;

See what is needed from the following:

open listTheory;
open Let_conv;
open Num_induct;

fun close_theory () = ();

val define_type = Define_type.define_type;

val stdIn = TextIO.stdIn;
val stdOut = TextIO.stdOut;
val input_line = TextIO.input;
val output = TextIO.output;
val openIn = TextIO.openIn;
(* val openString = TextIO.openString; CURRENTLY UNSUPPORTED *)

val print_term = Hol_pp.print_term;
val print_type = Hol_pp.print_type;

fun print_string s = TextIO.output(TextIO.stdOut,s);

val list_to_vector = Vector.fromList;

val list_to_array = Array.fromList;

fun ordof (s,n) = Char.ord(String.sub(s,n));

fun time f =
    let val cputimer = Timer.startCPUTimer ()
    in
        let val res = f ()
            val {usr,sys,gc} = Timer.checkCPUTimer cputimer
        in
            print_string "\n";
            print_string ("CPU: usr: " ^ Time.toString usr ^ " s    ");
            print_string (     "sys: " ^ Time.toString sys ^ " s    ");
            print_string (      "gc: " ^ Time.toString gc  ^ " s\n");
            res
        end
    end;

val now = Time.now;

val time_to_string = Time.toString;

val sub_time = Time.-;

val system = fn (s:string) => ();

*)


fun print_newline() = print "\n";
fun print_theorem th = (print (thm_to_string th); print_newline());
fun print_terms []        = ()
   | print_terms (t :: []) = print_term t
   | print_terms (t :: ts) = (print_term t; print ","; print_terms ts);
fun print_all_thm th =
   let val (ant,conseq) = dest_thm th
   in (print "["; print_terms ant; print "] |- ";
       print_term conseq; print_newline() )
   end;
fun print_theorems []        = ()
   | print_theorems (t :: ts) = (print_theorem t; print "\n";
                                 print_theorems ts);
fun print_goal (asl,gl) = (print_term gl; print_newline());

fun print_theory_size () =
   (print "The theory ";
    print (current_theory ());
    print " has ";
    print (Int.toString (length (types (current_theory ()))));
    print " types, ";
    print (Int.toString (length (axioms "-")));
    print " axioms, ";
    print (Int.toString (length (definitions "-")));
    print " definitions, and ";
    print (Int.toString (length (theorems "-")));
    print " theorems.";
    print "\n" );

fun pthm th =
    ( print_thm th;
      print_newline();
      th );

fun pairf f g (x,y) = (f x,g y);
fun test f x = ( f x; x );
fun try f x = f x handle _ => x;

(* must somehow overload the substitution operator '<|':
map new_special_symbol [`<|s`;`<|v`;`<|vs`;`<|a`;
                        `<|xs`;`<|e`;`<|es`;`<|b`;`<|c`;`<|env`;`<|g`;
                        `<|vv`;`<|vsv`;`<|av`;`:==`;`//v`;`<<`]; ();

Expect to do this by using alphabetic versions, as
    subst_s, subst_v, etc.
*)


(* We will need the tools for definitions in the following structure: *)
(*
open new_type;
*)


(* --------------------------------------------------------------------- *)
(* Need the HOL 88 compatibility library.                                *)
(* --------------------------------------------------------------------- *)
open hol88Lib;
open listLib;
open Psyntax;



val ONE_ONE_DEF = boolTheory.ONE_ONE_DEF;
val ONTO_DEF    = boolTheory.ONTO_DEF;

(* These operators transform implications to collect antecedents into
  a single conjunction, or else to reverse this and spread them into
  a sequence of individual implications.  Each has type thm->thm.
*)

val AND2IMP = REWRITE_RULE[(SYM o SPEC_ALL)AND_IMP_INTRO];
val IMP2AND = REWRITE_RULE[AND_IMP_INTRO];

fun TACTIC_ERR{function,message} =
    Feedback.mk_HOL_ERR "Tactic" function message

fun failwith function =
    raise TACTIC_ERR{function = function,message = ""};

fun fail () = failwith "fail";


(* Here are some useful tactics, that are not included in the standard HOL: *)

val PRINT_TAC :tactic = fn (asl,gl) =>
     (print_goal (asl,gl);
      ALL_TAC (asl,gl));

val POP_TAC = POP_ASSUM (fn th => ALL_TAC);

fun ETA_TAC v :tactic = fn (asl,gl) =>
      let val (t1,t2) = dest_eq gl;
          val at1 = “\^v.^t1 ^v”;
          val at2 = “\^v.^t2 ^v” in
      ([(asl,mk_eq(at1,at2))],
       fn [thm] => TRANS (SYM(ETA_CONV at1)) (TRANS thm (ETA_CONV at2)))
      end;

fun EXT_TAC v :tactic = fn (asl,gl) =>
      let val (t1,t2) = dest_eq gl;
          val at1 = mk_comb(t1,v)
          and at2 = mk_comb(t2,v) in
      ([(asl,mk_forall(v,mk_eq(at1,at2)))],
       fn [thm] => EXT thm)
      end;

val CHECK_TAC :tactic = fn (asl,gl) =>
      if exists (aconv gl) asl
      then ACCEPT_TAC (ASSUME gl) (asl,gl)
      else failwith "CHECK_TAC";

val FALSE_TAC :tactic = fn (asl,gl) =>
      if exists (fn th => Feq th) asl
      then CONTR_TAC (ASSUME “F”) (asl,gl)
      else failwith "FALSE_TAC";

fun MP_IMP_TAC imp_th :tactic = fn (asl,gl) =>
      let val (ant,cns) = dest_imp(concl imp_th) in
      ([(asl,ant)],
       fn [thm] => MP imp_th thm)
      end;

fun UNASSUME_THEN (ttac:thm_tactic) tm :tactic = fn (asl,t) =>
 if tmem tm asl
 then ttac (ASSUME tm) (op_set_diff aconv asl [tm], t)
 else failwith "UNASSUME_TAC";

val CONTRAPOS_TAC :tactic = fn (asl,gl) =>
      let val (ant,cns) = dest_imp gl in
      ([(asl,mk_imp (dest_neg cns, dest_neg ant))],
       fn [thm] => CONTRAPOS thm)
      end;

val FORALL_EQ_TAC :tactic = fn (asl,gl) =>
     (let val (allt1,allt2) = dest_eq gl;
          val (x,t1) = dest_forall allt1
          and (y,t2) = dest_forall allt2 in
      if x !~ y then fail()
      else
       ([(asl,mk_eq (t1, t2))],
        fn [thm] => FORALL_EQ x thm)
      end)
      handle _ => failwith "FORALL_EQ_TAC";

val EXISTS_EQ_TAC :tactic = fn (asl,gl) =>
     (let val (ext1,ext2) = dest_eq gl;
          val (x,t1) = dest_exists ext1
          and (y,t2) = dest_exists ext2 in
      if x !~ y then fail()
      else
       ([(asl,mk_eq (t1, t2))],
        fn [thm] => EXISTS_EQ x thm)
      end)
      handle _ => failwith "EXISTS_EQ_TAC";

fun EXISTS_VAR (x,u) th =
    let val p = subst[(x,u)] (concl th) in
    EXISTS (mk_exists(x,p),u) th
    end;

val FIND_EXISTS_TAC :tactic = fn (asl,gl) =>
    let val (vars,body) = strip_exists gl
        val v = hd vars
        val cnjs = strip_conj body
        fun find_exists_eq [] = failwith "find_exists_eq"
          | find_exists_eq (cnj::cnjs) =
            let val (lhs,rhs) = dest_eq cnj
            in
                if lhs ~~ v then rhs
                else if rhs ~~ v then lhs
                else failwith "find_exists_eq"
            end
            handle _ => find_exists_eq cnjs
    in
        EXISTS_TAC (find_exists_eq cnjs) (asl,gl)
    end
    handle _ => failwith "FIND_EXISTS_TAC";


(* introducing a beta abstration

              A |- t
     ========================
           A |- (\x.t)x
*)

(* [PVH 95.2.19] *)

fun UNBETA_TAC x :tactic = fn (asl,gl) =>
     ([(asl,mk_comb(mk_abs(x, gl), x))],
       fn [thm] => BETA_RULE thm)
      handle _ => failwith "UNBETA_TAC";

(*
g `x < y`;
e(UNBETA_TAC “x:num”);
e(UNBETA_TAC “y:num”);
*)
(*
val WELL_FOUNDED_NUM_TAC :tactic = fn (asl,gl) =>
     (let val n = (fst o dest_forall) gl in
        (GEN_TAC
         THEN UNBETA_TAC n
         THEN SPEC_TAC(n,n)
         THEN MATCH_MP_TAC NUM_WELL_FOUNDED
         THEN BETA_TAC
         THEN GEN_TAC
         THEN DISCH_TAC) end) (asl,gl)
      handle _ => failwith "WELL_FOUNDED_NUM_TAC";
*)

(*
% ! implication abstraction

          A |- t1 ==> t2
     -----------------------
      A |- (!x.t1) ==> (!x.t2)
%

% Adapted from FORALL_EQ: [PVH 94.12.05]                                             %

let FORALL_IMP =
    fn x => let all t = mk_forall(x,t) in
        fn th => let (t1,t2) = dest_imp (concl th) in     %  t1 ==> t2  %
             let at1 = all t1 in
             DISCH at1 (GEN x
               (MATCH_MP (GEN x th) (SPEC x (ASSUME at1))))
        handle _ => failwith "FORALL_IMP";

%
FORALL_IMP = - : (term -> thm -> thm)
FORALL_IMP “n:num” (SPEC_ALL SUB_ADD);
FORALL_IMP “n:num” (SPEC_ALL (ASSUME “!n:num. R n ==> Q n”));
%

let FORALL_IMP_TAC :tactic = fn (asl,gl) =>
     (let allt1,allt2 = dest_imp gl in
      let x,t1 = dest_forall allt1 in
      let y,t2 = dest_forall allt2 in
      if not (x = y) then fail()
      else
       [asl,mk_imp (t1, t2)],
       fn [thm] => FORALL_IMP x thm)
      handle _ => failwith "FORALL_IMP_TAC";
*)

val rec UNDISCH_ALL_TAC :tactic = fn (asl,gl) =>
        if null asl then ALL_TAC (asl,gl)
        else (UNDISCH_TAC (hd asl)
              THEN UNDISCH_ALL_TAC) (asl,gl);

val UNDISCH_LAST_TAC :tactic =
    POP_ASSUM MP_TAC;

fun DEFINE_NEW_VAR def :tactic =
      let val (v,tm) = dest_eq def in
      SUBGOAL_THEN (mk_exists(v,def)) STRIP_ASSUME_TAC
      THENL
        [  EXISTS_TAC tm
           THEN REWRITE_TAC[],
           ALL_TAC
        ]
      end
      handle _ => failwith "DEFINE_NEW_VAR";


val LIST_INDUCT_TAC =
 let val tm = Term `!P:'a list -> bool.
                       P [] /\ (!t. P t ==> !x. P (x::t)) ==> !l. P l`
     val eq = ALPHA (concl listTheory.list_induction) tm
     val list_induction' = EQ_MP eq listTheory.list_induction
 in INDUCT_THEN list_induction' ASSUME_TAC
 end;


val DOUBLE_LIST_INDUCT_TAC :tactic =
    LIST_INDUCT_TAC
    THENL
      [ ALL_TAC,
        GEN_TAC THEN LIST_INDUCT_TAC THEN POP_TAC
      ];

val LENGTH_LIST_INDUCT_TAC :tactic =
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LENGTH_NIL,LENGTH_CONS]
    THEN REPEAT GEN_TAC THEN STRIP_TAC
    THEN POP_ASSUM (fn th => REWRITE_TAC[th]);


val FORALL_SYM_CONV :conv = fn tm1 =>
      let val (x,body1) = dest_forall tm1;
          val (y,body)  = dest_forall body1;
          val tm2 = mk_forall(y,mk_forall(x,body)) in
      IMP_ANTISYM_RULE ((DISCH_ALL o GENL[y,x] o SPECL[x,y] o ASSUME) tm1)
                       ((DISCH_ALL o GENL[x,y] o SPECL[y,x] o ASSUME) tm2)
      end
      handle _ => failwith "FORALL_SYM_CONV";

(*
FORALL_SYM_CONV “!x y. x+y=z”;
*)


fun NOT_AP_TERM_TAC f :tactic = fn (asl,gl) =>
      let val eq_gl = dest_neg gl;
          val (a,b) = dest_eq eq_gl in
      ([(asl,mk_neg(mk_eq(mk_comb(f,a),mk_comb(f,b))))],
       fn [thm] => MP (CONTRAPOS (DISCH eq_gl (AP_TERM f (ASSUME eq_gl)))) thm)
      end
      handle _ => failwith "NOT_AP_TERM_TAC";

val APP_let_CONV :conv = fn tm1 =>
      let val (f,args) = strip_comb tm1;
          val lt::rest = args;
          val (bodyf,vl) = dest_let lt;
          val (var,body) = dest_abs bodyf;
          val tm2 = mk_let((mk_abs(var,(list_mk_comb(f,(body::rest))))),vl)
      in
          TRANS ((ONCE_DEPTH_CONV let_CONV) tm1)
                (SYM ((ONCE_DEPTH_CONV let_CONV) tm2))
      end
      handle _ => failwith "APP_LET_CONV";

val LIFT_let_TAC = (REPEAT o CONV_TAC o CHANGED_CONV o ONCE_DEPTH_CONV)
                    APP_let_CONV;

val STRIP_let_TAC :tactic = fn (asl,gl) =>
      let val (bodyf,vl) = dest_let gl;
          val (var,body) = dest_abs bodyf;
          val let_equal = mk_eq(var,vl) in
      ([(let_equal::asl,body)],
      fn [thm] => (pthm (SYM (let_CONV gl)); pthm thm;
                   map (pthm o ASSUME) (hyp thm);
               (pthm o pthm) (EQ_MP (SYM (let_CONV gl))
                      (DISCH let_equal thm))))
      end
      handle _ => failwith "STRIP_let_TAC";

fun USE_IMP_EQ_matches th =
      let val (vars,imps) = strip_forall(concl th);
          val (hyps,body) = strip_imp imps;
          val left = fst(dest_eq body) in
      fn tm => match left tm
      end
      handle _ => failwith "USE_IMP_EQ_matches";

fun USE_IMP_matches th =
      let val (vars,imps) = strip_forall(concl th);
          val (hyps,body) = strip_imp imps in
      fn tm => match body tm
      end
      handle _ => failwith "USE_IMP_matches";

fun SUB_matches (f:term->'a) tm =
    if is_comb tm then
       (let val (rator,rand) = dest_comb tm in
        (f rator handle _ => f rand)
        end)
    else
    if is_abs tm then
       (let val (bv,body) = dest_abs tm in
        f body
        end)
    else (failwith "SUB_matches");

fun ONCE_DEPTH_matches (f:term->'a) tm =
       (f tm handle _ => ((SUB_matches (ONCE_DEPTH_matches f)) tm));

fun ONCE_DEPTH_USE_IMP_EQ_matches th =
    ONCE_DEPTH_matches (USE_IMP_EQ_matches th);

fun ONCE_DEPTH_USE_IMP_matches th =
    ONCE_DEPTH_matches (USE_IMP_matches th);

fun USE_IMP_THEN ttac th :tactic = fn (asl,gl) =>
      let val matches = ONCE_DEPTH_USE_IMP_EQ_matches th gl;
          val ith = INST_TY_TERM matches (SPEC_ALL th);
          val subgoal = concl (UNDISCH_ALL ith) in
       (SUBGOAL_THEN subgoal ttac
        THEN (MATCH_MP_TAC th ORELSE ALL_TAC)) (asl,gl)
      end
      handle _ => failwith "USE_IMP_THEN";

fun USE_IMP_TAC th :tactic = USE_IMP_THEN ASSUME_TAC th;

fun USE_IMP_AND_THEN ttac th tac :tactic =
    USE_IMP_THEN ttac th
    THENL [ tac, ALL_TAC ];

fun USE_THEN ttac th :tactic = fn (asl,gl) =>
      let val matches = ONCE_DEPTH_USE_IMP_matches th gl;
          val ith = INST_TY_TERM matches (SPEC_ALL th);
          val subgoal = concl (UNDISCH_ALL ith) in
       (SUBGOAL_THEN subgoal ttac
        THEN (MATCH_MP_TAC th ORELSE ALL_TAC)) (asl,gl)
      end
      handle _ => failwith "USE_THEN";

fun USE_TAC th :tactic = USE_THEN ASSUME_TAC th;

fun USE_AND_THEN ttac th tac :tactic =
    USE_THEN ttac th
    THENL [ tac, ALL_TAC ];

fun RES2_THEN thm_tac =
    RES_THEN (fn th => IMP_RES_THEN thm_tac th ORELSE ALL_TAC);

fun IMP_RES2_THEN thm_tac =
    IMP_RES_THEN (fn th => IMP_RES_THEN thm_tac th ORELSE ALL_TAC);

fun IMP_RES_M_THEN tac th g =
    IMP_RES_THEN (REPEAT_GTCL IMP_RES_THEN tac) th g handle _ => ALL_TAC g;

fun RES_M_THEN tac g =
    RES_THEN (REPEAT_GTCL IMP_RES_THEN tac) g handle _ => ALL_TAC g;

val REWRITE_THM = fn th => REWRITE_TAC[th];
val ASM_REWRITE_THM = fn th => ASM_REWRITE_TAC[th];
val ONCE_REWRITE_THM = fn th => ONCE_REWRITE_TAC[th];
val IMP_RES_REWRITE_TAC = IMP_RES_THEN REWRITE_THM;
val RES_REWRITE_TAC = RES_THEN REWRITE_THM;

fun REWRITE_ASSUM_TAC rths :tactic =
    RULE_ASSUM_TAC (REWRITE_RULE rths);

fun REWRITE_ALL_TAC rths :tactic =
    REWRITE_TAC rths  THEN
    REWRITE_ASSUM_TAC rths;

fun ASM_REWRITE_ALL_TAC rths :tactic =
    REWRITE_ASSUM_TAC rths  THEN
    ASM_REWRITE_TAC rths;

fun ONCE_REWRITE_ASSUM_TAC rths :tactic =
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE rths);

fun ONCE_REWRITE_ALL_TAC rths :tactic =
    ONCE_REWRITE_TAC rths  THEN
    ONCE_REWRITE_ASSUM_TAC rths;

fun ONCE_ASM_REWRITE_ALL_TAC rths :tactic =
    ONCE_REWRITE_ASSUM_TAC rths  THEN
    ONCE_ASM_REWRITE_TAC rths;

val REWRITE_ALL_THM = fn th => REWRITE_ALL_TAC[th];
val ASM_REWRITE_ALL_THM = fn th => ASM_REWRITE_ALL_TAC[th];
val ONCE_REWRITE_ALL_THM = fn th => ONCE_REWRITE_ALL_TAC[th];
val ONCE_ASM_REWRITE_ALL_THM = fn th => ONCE_ASM_REWRITE_ALL_TAC[th];


val UNIFY_VARS_TAC :tactic =
    ASSUM_LIST (fn thms => MAP_EVERY (fn th => REWRITE_ALL_TAC[th])
                 (mapfilter (SYM o (test ((pairf dest_var dest_var)
                                          o dest_eq o concl))) thms));


fun EVERY1 tacl =
    case tacl
    of [] =>
         ALL_TAC
     | (t::tacl') =>
         t THEN1 EVERY1 tacl';

end; (* struct *)
