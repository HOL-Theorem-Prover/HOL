(* ========================================================================= *)
(* TEST SUITE FOR THE HOL INTERFACE TO FIRST-ORDER LOGIC.                    *)
(* Created by Joe Hurd, June 2002                                            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Be really quiet while we set everything up.                               *)
(* ------------------------------------------------------------------------- *)

val () = quietdec := true;

(* ------------------------------------------------------------------------- *)
(* Load things in and set up pretty-printing etc.                            *)
(* ------------------------------------------------------------------------- *)

val _ = loadPath :=
["/home/jeh1004/dev/hol/metis/src/mlib",
 "/home/jeh1004/dev/hol/metis/src/normalize",
 "/home/jeh1004/dev/hol/metis/src/metis"] @ !loadPath;

val _ = app load
  ["bossLib","numLib","pred_setTheory","listTheory","llistTheory",
   "mlibProblem","metisLib"];

val () = installPP mlibTerm.pp_term;
val () = installPP mlibTerm.pp_formula;
val () = installPP mlibThm.pp_thm;
val () = installPP folTools.pp_logic_map;

val () = set_trace "normalForms" 1;
val () = set_trace "Metis" 2;

open normalForms folTools metisLib;

(* ------------------------------------------------------------------------- *)
(* Output functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun profile f = Count.apply (try f);

fun SAY s =
  print
  ("\n\n-------------------------------------" ^
   "-------------------------------------\n\n" ^ s ^ "\n\n");

val METIS_TEST =
  let val next = let val r = ref 0 in fn () => (r := !r + 1; !r) end
  in fn s => SAY ("Metis Test " ^ mlibUseful.int_to_string (next ()) ^ ": " ^ s)
  end;

(* ------------------------------------------------------------------------- *)
(* Setting up parsing for first-order problems.                              *)
(* ------------------------------------------------------------------------- *)

fun gen_const var =
  let
    val (s, ty) = dest_var var
    val d = Definition.new_specification
      (s^"_DEF", [s], INST_TYPE [alpha |-> ty] (EQT_ELIM (SPEC T EXISTS_SIMP)))
    val () = Parse.add_const s
  in
    mk_const (s, ty)
  end;

val () = Globals.guessing_tyvars := true;
val () = Globals.notify_on_tyvar_guess := false;
val () = Parse.reveal "C";
val () = set_fixity "%" (Infix (LEFT, 5000));
val () = set_fixity "/" (Infix (LEFT, 600));
val () = set_fixity "=" (Infix (NONASSOC, 425));
val () = set_fixity "==" (Infix (NONASSOC, 425));
val () = set_fixity "<=>" (Infix (RIGHT, 100));
val () = overload_on ("%", gen_const ``FAKE_BINOP1 : 'a->'a->'a``);
val () = overload_on ("/", gen_const ``FAKE_BINOP2 : 'a->'a->'a``);
val () = overload_on ("<=>", gen_const ``FAKE_IFF : bool->bool->bool``);
val () = overload_on ("==", gen_const ``FAKE_EQUALITY : 'a->'a->bool``);
val interpret = subst [``FAKE_IFF`` |-> ``$= : bool->bool->bool``];

fun FOL_Term q =
  let
    val tm = interpret (Term q)
    val tys = map (type_of o bvar) (find_terms is_abs tm)
    val tyS = matchTools.vunify_type is_vartype tys
    val tyU = case tys of [] => alpha | ty :: _ => type_subst tyS ty
  in
    inst (map (fn ty => ty |-> tyU) (type_vars_in_term tm)) tm
  end;

(* ------------------------------------------------------------------------- *)
(* Setting up the test prover                                                *)
(* ------------------------------------------------------------------------- *)

val DEFAULTS = I : metisTools.parameters -> metisTools.parameters;
val INTERFACE = metisTools.update_interface;
val LIMIT = metisTools.update_limit o K;
val SOLVER = metisTools.update_solver;
val MAPPING = INTERFACE o update_mapping;
val HIGHER_ORDER = MAPPING (folMapping.update_higher_order (K true));
val FIRST_ORDER = MAPPING (folMapping.update_higher_order (K false));
val TYPES = MAPPING (folMapping.update_with_types (K true));
val NO_TYPES = MAPPING (folMapping.update_with_types (K false));
val COMBINATOR = INTERFACE (update_combinator (K true));
val BOOLEAN = INTERFACE (update_boolean (K true));
val NO_PROVERS = (SOLVER o K) [];
val RESOLUTION = (SOLVER o K) [mlibMetis.default_resolution];
val MESON = (SOLVER o K) [mlibMetis.default_meson];
val ORESOLUTION = (SOLVER o K) (#solver metisTools.defaults);

val settings = ref DEFAULTS;

fun PARM f =
  (print "\nWarning: changing settings!\n\n";
   settings := (f o !settings));

fun WITH_PARM f = mlibUseful.with_flag (settings, fn set => f o set);

fun MPROVE ths tm =
  (profile o try o mlibUseful.try) prove
  (tm, metisTools.GEN_METIS_TAC (!settings metisTools.defaults) ths);

val METIS_PROVE = (profile o try o mlibUseful.try o metisLib.METIS_PROVE);

local
  fun LIST_MK_CONJUNCTS ths =
    case rev ths of [] => raise mlibUseful.BUG "LIST_MK_CONJUNCTS" ""
    | h :: t => foldl (uncurry CONJ) h t;

  fun f ((tmV, _), ths) =
    (CONV_RULE PRETTIFY_VARS_CONV o GENL tmV o LIST_MK_CONJUNCTS) ths;
in
  fun MSOLVE n db q =
    (profile o try o mlibUseful.try)
    (map f o mlibStream.to_list o mlibStream.take n o
     metisTools.GEN_METIS_SOLVE (MESON (!settings metisTools.defaults))
     (map ASSUME db)) q;

  fun PROLOG n db =
    (profile o try o mlibUseful.try)
    (map f o mlibStream.to_list o
     (case n of SOME m => mlibStream.take m | NONE => I) o
     metisTools.PROLOG_SOLVE (map ASSUME db));
end;

local
  fun attack1 {name, comment = _, goal} =
    let
      val () = SAY name
      val tm = FOL_Term goal
      val comment =
        case total (MPROVE []) tm of NONE
          => "FAILED TO PROVE:\n" ^ term_to_string tm
        | SOME th => "SUCCESSFULLY PROVED:\n" ^ thm_to_string th
    in
      print ("\n" ^ comment ^ "\n")
    end;
in
  fun attack set =
    let val {blurb = _, name = _, probs} = set ()
    in app attack1 probs
    end;
end;

(* ------------------------------------------------------------------------- *)
(* Switch echoing back on now we've set everything up.                       *)
(* ------------------------------------------------------------------------- *)

val () = quietdec := false;

(* ------------------------------------------------------------------------- *)
val () = SAY "Syntax checking the problem sets";
(* ------------------------------------------------------------------------- *)

val check_syntax : (unit -> term mlibProblem.set) -> string -> term =
  C assoc
  o map (fn {name, goal, ...} => (print (name ^ "\n"); (name, FOL_Term goal)))
  o #probs
  o (fn p => p ());

val nonequality = try check_syntax mlibProblem.nonequality;
val equality    = try check_syntax mlibProblem.equality;
val tptp        = try check_syntax mlibProblem.tptp;

(* ------------------------------------------------------------------------- *)
val () = SAY "Creating ML bindings for the test problems";
(* ------------------------------------------------------------------------- *)

val p_or_not_p = try nonequality "PROP_6";
val xor_assoc = try nonequality "XOR_ASSOC";
val all_3_cls = try nonequality "ALL_3_CLAUSES";
val p28 = try nonequality "P28";
val los = try nonequality "LOS";
val steamroller = try nonequality "STEAM_ROLLER";
val gilmore9 = try nonequality "GILMORE_9";
val p34 = try nonequality "P34";
val p55 = try nonequality "P55";
val agatha = try equality "AGATHA";
val lcl9 = try tptp "LCL009-1";

(* ------------------------------------------------------------------------- *)
(* Debugging Central.                                                        *)
(* ------------------------------------------------------------------------- *)

(*
val DEFAULTS = (LIMIT {time = SOME 60.0, infs = NONE} o DEFAULTS);
val () = show_types := true;
val () = show_assums := true;
val () = show_tags := true;
val () = set_trace "Metis" 3;
val () = PARM (ORESOLUTION o DEFAULTS);
val () = folMapping.prettify_fol := false;
val () = folTools.recent_fol_problems := SOME [];

MPROVE [arithmeticTheory.MULT_COMM, arithmeticTheory.MULT_ASSOC]
  ``(!x y. divides x y = ?z. y = z * x) ==>
    (!x y z. divides x y ==> divides x (z * y))``;

MPROVE [arithmeticTheory.MULT_COMM, arithmeticTheory.MULT_ASSOC]
  ``a * b * c * d * e * f * g * h * i = i * h * g * f * e * d * c * b * a``;

folTools.recent_fol_problems;
stop;

val () = folMapping.prettify_fol := false;
val () = folTools.recent_fol_problems := SOME [];
MPROVE [] ``P ODD EVEN (MOD) divides
(SUBSET) {} UNIV (IN) (UNION) (INTER) COMPL CARD
PRE NULL I [] TL CONS APPEND LENGTH (=) (&) 0 SUC (+) (-)
( * ) ( ** ) (<=) (<) (>) (>=) (NUMERAL) (NUMERAL_BIT1) (NUMERAL_BIT2)
(ALT_ZERO) (,) FST SND : bool``;
folTools.recent_fol_problems;

METIS_PROVE
[ASSUME ``!x y. (f:num->bool#bool) ((g:bool#bool->num) (x,y)) = (x,y)``,
 pairTheory.ABS_PAIR_THM]
``!a. (f:num->bool#bool) ((g:bool#bool->num) a) = a``;

val prob = Term `
  (!x. x = x) /\ (!x y z v. x + y <= z + v \/ ~(x <= z) \/ ~(y <= v)) /\
  (!x. x + 0 = x) /\ (!x. x + ~x = 0) /\
  (!x y z. x + (y + z) = x + y + z) ==>
  ~d <= 0 /\ c + d <= i /\ ~(c <= i) ==> F`;
oresolution_prove prob;
meson_prove prob;

folTools.recent_fol_problems;
stop;

load "integerTheory";
open integerTheory;
METIS_PROVE [INT_LE_LADD, INT_ADD_COMM, INT_ADD_ASSOC, INT_LE_ADD2,
             INT_ADD_LID]
``0 <= c + x ==> x <= y ==> (0 <= c + y = T)``;

val int_arith_139 = Term
 `(!x y z v.
     (($int_le ($int_add x y) ($int_add x z)) \/ ~($int_le y z)) /\
     (~($int_le ($int_add x y) ($int_add x z)) \/ ($int_le y z)) /\
     $int_add x y = $int_add y x /\
     $int_add x ($int_add y z) = $int_add ($int_add x y) z /\
     (($int_le ($int_add x y) ($int_add z v)) \/ ~($int_le x z) \/
      ~($int_le y v)) /\ $int_add (int_of_num 0) x = x ==>
     ~($int_le (int_of_num 0) ($int_add c c_y)) /\
     ($int_le (int_of_num 0) ($int_add c c_x)) /\ ($int_le c_x c_y)) ==> F`;
METIS_PROVE [] int_arith_139;

folTools.recent_fol_problems;
stop;
*)

(* ------------------------------------------------------------------------- *)
val () = SAY "Testing the normalization steps";
(* ------------------------------------------------------------------------- *)

val t = WITH_PARM NO_PROVERS (MPROVE []) ``(\x. 42) 35 = 42``;

val t = WITH_PARM NO_PROVERS (MPROVE []) ``!f. (f : 'a -> 'b) = (\x. f x)``;

val t = WITH_PARM NO_PROVERS (MPROVE []) ``!x. ?!y. x = y``;

val t = WITH_PARM NO_PROVERS (MPROVE []) ``?f. !x. f x = ~x``;

val t = WITH_PARM NO_PROVERS (MPROVE []) all_3_cls;

val t =
  METIS_PROVE []
  ``!f g a. (!x. (if T then f x else a) = g x) ==> (f = g)``;

(* Bug check: this used to fail because of CHOOSE_THEN's choice of var names *)
val t = prove (``p x ==> ((?x. p x) = q) ==> q``,
                 DISCH_TAC THEN POP_ASSUM_LIST METIS_TAC);

(* Bug check: this used to fail because of GEN_TAC's choice of var names *)
val t = prove (``p x ==> (!y. q = p y) ==> !x. p x``,
                 DISCH_TAC THEN POP_ASSUM_LIST METIS_TAC);

(* Bug check: this used to fail because SKICo_CONV didn't normalize etas *)
val t = METIS_PROVE [] ``P f ==> P (\x. f x)``;

(* ------------------------------------------------------------------------- *)
val () = METIS_TEST "proving a selection of first-order HOL goals";
(* ------------------------------------------------------------------------- *)

val t = METIS_PROVE [] ``c /\ (c = d) ==> d``;

(* Bug check: this tests whether conditionals are being handled *)
val t = METIS_PROVE [] ``p (a : 'a) \/ p b ==> p (if p a then a else b)``;

(* Bug check: this tests whether relations are always boolean *)
val t = METIS_PROVE [] ``!x y z. p /\ (p ==> q) /\ ~q ==> option_case x y z``;

(* Bug check: this tests whether we normalize restricted quantifiers *)
val t = METIS_PROVE [] ``!x :: s. ?y :: s. x = y``;

(* Bug check: this tests whether we normalize unique existence *)
val t =
  METIS_PROVE [numTheory.INV_SUC, arithmeticTheory.num_CASES]
  ``!x. ~(x = 0) ==> ?!y. x = SUC y``;

(* Bug check: this tests how we handle duplicate first-order theorems *)
val t =
  METIS_PROVE []
  ``((LENGTH ([] : bool list) = 0) \/ q) /\
    ((LENGTH ([] : num list) = 0) \/ q) /\
    ((LENGTH ([] : num list list) = 0) \/ q) ==>
    (q \/ (LENGTH ([] : num list) = 0))``;

(* Bug check: this used to fail generating an equality axiom for HD/2 *)
val t =
  METIS_PROVE []
  ``(HD [I] x = x) /\ (p \/ q) /\ (~p \/ q) /\ (p \/ ~q) /\ (~p \/ ~q) ==> F``;

(* Bug check: this tests how we handle embedded booleans (from Konrad) *)
val t =
  METIS_PROVE
  [ASSUME ``!x y. (f:num->bool#bool) ((g:bool#bool->num) (x,y)) = (x,y)``,
   pairTheory.ABS_PAIR_THM]
  ``!a. (f:num->bool#bool) ((g:bool#bool->num) a) = a``;

(* Bug check: this tests the constants generated by MIN_CNF (from Michael) *)
val INJMAP_def = Definition.new_definition
  ("INJ_MAP_def",
   ``INJMAP (f : 'a -> 'b) s t =
     ((!x :: s. f x IN t) /\ !x y :: s. (f x = f y) ==> (x = y))``);
val t =
  METIS_PROVE [INJMAP_def] ``INJMAP (g : 'b -> 'a) b a ==> !y :: b. g y IN a``;

val metis_p_or_not_p = METIS_PROVE [] p_or_not_p;
val metis_xor_assoc = METIS_PROVE [] xor_assoc;
val metis_p28 = METIS_PROVE [] p28;
val metis_los = METIS_PROVE [] los;
val metis_gilmore9 = METIS_PROVE [] gilmore9;
val metis_p34 = METIS_PROVE [] p34;
val metis_p55 = METIS_PROVE [] p55;
val metis_agatha = METIS_PROVE [] agatha;
val metis_lcl9 = METIS_PROVE [] lcl9;

(* too expensive
val metis_steamroller = METIS_PROVE [] steamroller; *)

(* too long and expensive to run each time, but a great test
val () = PARM DEFAULTS;
val () = PARM (LIMIT {time = SOME 30.0, infs = NONE});
val () = PARM RESOLUTION;

val () = attack mlibProblem.nonequality;
val () = attack mlibProblem.equality;

val () = PARM TYPES;

val () = attack mlibProblem.nonequality;
val () = attack mlibProblem.equality;

val () = PARM HIGHER_ORDER;

val () = attack mlibProblem.nonequality;
val () = attack mlibProblem.equality;

val () = PARM FIRST_ORDER;

val () = attack mlibProblem.nonequality;
val () = attack mlibProblem.equality;

val () = PARM DEFAULTS;

stop;
quit();
*)

val t = METIS_PROVE [] ``~((a : 'a) = b) /\ (!x : 'a. x = c) ==> F``;
(* Running without types produces the following bogus proof:
[(|- F, Resolve ($ c, |- $ c, |- ~$ c)),
 (|- ~$ c, Resolve (falsity = c, |- falsity = c, |- ~(falsity = c) \/ ~$ c)),
 (|- ~(falsity = c) \/ ~$ c,
     Equality
     {lit = ~$ falsity, path = [0], res = c, lr = true, thm = |- ~$ falsity}),
 (|- ~$ falsity, Axiom [~$ falsity]),
 (|- falsity = c, Inst ([vg15896 |-> falsity], |- vg15896 = c)),
 (|- $ c, Resolve (truth = c, |- truth = c, |- ~(truth = c) \/ $ c)),
 (|- ~(truth = c) \/ $ c,
     Equality
     {lit = $ truth, path = [0], res = c, lr = true, thm = |- $ truth}),
 (|- $ truth, Axiom [$ truth]),
 (|- truth = c, Inst ([vg15896 |-> truth], |- vg15896 = c)),
 (|- vg15896 = c, Axiom [vg15896 = c])]
*)

(* ------------------------------------------------------------------------- *)
val () = METIS_TEST "solving a selection of first-order HOL goals";
(* ------------------------------------------------------------------------- *)

val lives = ``lives (x : 'a) : bool``;
val killed = ``killed (x : 'a) (agatha : 'a) : bool``;
val t = MSOLVE 1 [rand (rator p55)] (([``x``], []), [lives, killed]);
val t = MSOLVE 2 [rand (rator p55)] (([``x``], []), [lives, mk_neg killed]);
(* too expensive
val t = MSOLVE 1 [rand (rator agatha)] (([``x``], []), [lives, killed]); *)
val t = MSOLVE 2 [rand (rator agatha)] (([``x``], []), [lives, mk_neg killed]);

(* This next one fails if prolog runs with_types = false *)
val x = ``x : 'a -> bool``;
val t =
  PROLOG (SOME 1) [``FINITE ({} : num -> bool)``, ``FINITE ({} : 'a -> bool)``]
  (([``^x``], []), [``FINITE ^x``]);

(* A classic test: finding subsets and supersets *)
val x = ``x : num -> bool``;
val subset_rules =
  [``({} : num -> bool) SUBSET {}``,
   ``!v x y. ^x SUBSET y ==> (v INSERT x) SUBSET (v INSERT y)``,
   ``!v x y. ^x SUBSET y ==> x SUBSET (v INSERT y)``];
val t = PROLOG NONE subset_rules (([``^x``], []), [``^x SUBSET {0; 1; 2}``]);
val t = PROLOG (SOME 4) subset_rules (([``^x``], []), [``{0;1;2} SUBSET ^x``]);

(* ------------------------------------------------------------------------- *)
val () = METIS_TEST "first-order polymorphic goals";
(* ------------------------------------------------------------------------- *)

val t = METIS_PROVE [pred_setTheory.SUBSET_REFL] ``{0} SUBSET {0}``;

val t =
  METIS_PROVE
  [pred_setTheory.SUBSET_REFL, pred_setTheory.SUBSET_INSERT,
   pred_setTheory.IN_SING, numTheory.NOT_SUC] ``{0} SUBSET {SUC x; 0}``;

(* Bug check: this used to fail because type variables were ill-handled. *)
val t =
  METIS_PROVE [listTheory.LENGTH_CONS]
  ``(SUC (LENGTH (l1 :'a list)) = LENGTH (l2 :'b list)) ==>
    ?(l2h :'b) (l2t :'b list).
      ((l2 :'b list) = l2h :: l2t) /\ (LENGTH l2t = LENGTH (l1 :'a list))``;

(* ------------------------------------------------------------------------- *)
val () = METIS_TEST "first-order goals with combinators";
(* ------------------------------------------------------------------------- *)

val t = WITH_PARM COMBINATOR (MPROVE []) ``I 42 = 42``;

val t = WITH_PARM COMBINATOR (MPROVE []) ``K 42 35 = 42``;

(* ------------------------------------------------------------------------- *)
val () = METIS_TEST "higher-order goals";
(* ------------------------------------------------------------------------- *)

(* Higher-order because f is used with two different arities *)
val t =
  METIS_PROVE [pred_setTheory.IN_IMAGE]
  ``!f s a b. (!x. f x = a) /\ b IN IMAGE f s ==> (a = b)``;

(* Higher-order because of the boolean variables. *)
val t = METIS_PROVE [] ``?x. x``;
val t =
  WITH_PARM HIGHER_ORDER (MSOLVE 1 [])
  (([``x : bool``], []), [``x : bool``]);

(* Higher-order because of overlap between predicate and function symbols *)
val t = METIS_PROVE [combinTheory.I_THM] ``p ==> I p``;
val t = METIS_PROVE [combinTheory.I_THM] ``!x. p x ==> I (p x)``;
val t = METIS_PROVE [] ``(!x. f x = x) ==> f T``;

(* Bug check: this used to fail because resolution ate all the memory. *)
val t =
  METIS_PROVE [llistTheory.LAPPEND, llistTheory.LMAP]
  ``?(x : 'a llist) (y' : 'a llist).
      (LMAP (f : 'a -> 'b) (t :'a llist) = LMAP f (LAPPEND x y')) /\
      (LMAP f t = LAPPEND (LMAP f x) (LMAP f y'))``;

(* Bug check: this boolean case of extensionality wasn't covered *)
val t = METIS_PROVE [] ``(!x. p x \/ ~q x) /\ (!x. ~p x \/ q x) ==> (p = q)``;

(* Bug check: this used to be classified as a first-order problem *)
val t = METIS_PROVE [combinTheory.I_THM] ``I T``;

(* From Konrad Slind: strong induction implies weak induction *)
val t =
  METIS_PROVE [prim_recTheory.LESS_SUC_REFL, prim_recTheory.NOT_LESS_0,
               arithmeticTheory.num_CASES]
  ``(!P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n) ==>
    !P. P 0 /\ (!n. P n ==> P (SUC n)) ==> !n. P n``;

(* Examples from Jia Meng *)
val t =
  METIS_PROVE [combinTheory.K_THM]
  ``(!f. P (f a) a /\ !f. Q (f b) b) ==> ?x y. !g. P g x /\ Q g y``;

(* ------------------------------------------------------------------------- *)
val () = METIS_TEST "higher-order goals requiring combinator reductions";
(* ------------------------------------------------------------------------- *)

val t =
  WITH_PARM (COMBINATOR o TYPES o HIGHER_ORDER)
  (MPROVE []) ``?f. !x. f x = x``;
(* too expensive
val t =
  WITH_PARM (COMBINATOR o TYPES o HIGHER_ORDER)
  (MSOLVE 2 []) (([``f : 'a -> 'a``], []), [``f x = x``, ``f y = y``]); *)

(* too expensive; why is ordered resolution so rubbish at combinator goals? ***
val t =
  WITH_PARM (COMBINATOR o TYPES o HIGHER_ORDER)
  (MPROVE []) ``!x. S K x = I``; *)

(* If we run this without types, like this:

val t =
  WITH_PARM (COMBINATOR o NO_TYPES o HIGHER_ORDER)
  (MPROVE []) ``!x. S K x = I``;

then it sometimes results in a proof that can't be lifted to HOL. The
problem occurs due to extensionality, which is included in the
combinator reduction theorems.

The correct proof goes like so:

X                                                 = X
---------------------------------------------------------------------------
EXT_POINT (S K x) I                               = EXT_POINT (S K x) I
---------------------------------------------------------------------------
K (EXT_POINT (S K x) I) (x (EXT_POINT (S K x) I)) = EXT_POINT (S K x) I
---------------------------------------------------------------------------
S K x (EXT_POINT (S K x) I)                       = EXT_POINT (S K x) I
---------------------------------------------------------------------------
S K x (EXT_POINT (S K x) I)                       = I (EXT_POINT (S K x) I)
---------------------------------------------------------------------------
S K x                                             = I

The broken proofs use extensionality again on the way up

A (EXT_POINT A B)                                 = B (EXT_POINT A B)
---------------------------------------------------------------------------
A                                                 = B

This doesn't break the proof, which completes happily, but it does
over-specialize the HOL types during proof translation, so one of the
final HOL theorems becomes:

|- S K x = (I : ('x -> 'y) -> ('x -> 'y))

which breaks the proof, since it tries to resolve with

|- ~(S K x = (I : 'a -> 'a))

where the 'a is a locally constant type variable (since it appears in
the goal).

The moral is: when extensionality is kicking around, switch on types.
*)

(* too expensive
val t =
  WITH_PARM (COMBINATOR o TYPES o HIGHER_ORDER)
  (MPROVE []) ``!f c. (!x. f x = c) ==> (f = K c)``; *)

(* too expensive
val t =
  WITH_PARM (COMBINATOR o TYPES o HIGHER_ORDER)
  (MPROVE []) ``?f. !x. f x = x z``; *)
(* Can't seem to solve this one at all
val t =
  WITH_PARM (COMBINATOR o TYPES o HIGHER_ORDER) (MSOLVE 1 [])
  (([``f : ('b->'a)->'a``], []), [``f x = x z``, ``f y = y z``]); *)

val t =
  WITH_PARM (COMBINATOR o TYPES o HIGHER_ORDER)
  (MPROVE []) ``?p x. p x``;

(* Yet another example where we need types. If we run this without types,

val t =
  WITH_PARM (COMBINATOR o NO_TYPES o HIGHER_ORDER)
  (MPROVE []) ``?p x. p x``;

then the provers simply apply the unit theorem

$! (K T)

which is too type-specific. *)

(* ------------------------------------------------------------------------- *)
val () = METIS_TEST "higher-order goals requiring boolean theorems";
(* ------------------------------------------------------------------------- *)

val t =
  WITH_PARM (BOOLEAN o COMBINATOR o TYPES o HIGHER_ORDER)
  (MPROVE []) ``?x. $! x``;
(* too expensive
val t =
  WITH_PARM (BOOLEAN o COMBINATOR o TYPES o HIGHER_ORDER)
  (MSOLVE 2 []) (([``x : 'a -> bool``], []), [``$! x``]);
*)

(* With theorems about booleans, proving the following goal may result
   in a proof that cannot be lifted to HOL.

val t =
  WITH_PARM (BOOLEAN o COMBINATOR o NO_TYPES o HIGHER_ORDER)
  (MPROVE []) ``?f. !x. f x = x``;

This is a proof found at the first-order level:

    First negate         ~?f. !x. f x = x
(1) and convert to CNF   !f. ~(f (x f) = x f)         (x is a skolem constant)
(2) Now prove            ($= T) (x ($= T)) = (x ($= T))
    and finally resolve (1) and (2) to give a contradiction.

The resolution step cannot be lifted to HOL because

      the type of f    is 'a   -> 'a
  and the type of $= T is bool -> bool

which cannot be unified.
[Even though 'a is a type variable, the fact that it is present in the
goal means that it must be treated as locally constant.]
*)

(* too expensive
val t =
  WITH_PARM (BOOLEAN o COMBINATOR o TYPES o HIGHER_ORDER)
  (MPROVE []) ``P T /\ P F ==> !t. P t``; *)

(* too expensive
val t =
  WITH_PARM (BOOLEAN o COMBINATOR o TYPES o HIGHER_ORDER)
  (MPROVE []) ``!x. x \/ I (~x)``; *)

(* Can't seem to solve this one at all
val t =
  WITH_PARM (BOOLEAN o COMBINATOR o TYPES o HIGHER_ORDER)
  (MSOLVE 1 [])
  (([``f : 'a -> 'a``], []), [(rhs o concl o SKICo_CONV) ``!x. f x = x``]);
*)

(* Can't seem to prove this one at all
val t =
  WITH_PARM (BOOLEAN o TYPES o HIGHER_ORDER)
  (MPROVE []) ``(!x. f x) /\ (!x. x ==> p x) ==> p ($! f)``;
*)

(* ------------------------------------------------------------------------- *)
val () = METIS_TEST "some things that MESON can't do";
(* ------------------------------------------------------------------------- *)

(* Meson doesn't deal with boolean variables *)
val t = METIS_PROVE [] ``?x. x``;

(* Meson doesn't like lambda terms *)
val t = METIS_PROVE [] ``p (\x. x) /\ q ==> q /\ p (\y. y)``;

(* Known Meson bug with partially applied equality.                    *)
(* John Harrison: "The special treatment of equality in FOL_CONV and   *)
(* other stuff spoils MESON_TAC[] on goals involving partially applied *)
(* equality. Anyway, all this stuff is a bit hacky and weird."         *)
val t =
  METIS_PROVE []
  ``~q c /\ (!x. q x ==> ((x = c) \/ (p ((=) x)))) ==>
    !x. q x ==> (p ((=) x))``;

(* Meson uses equality axioms *)
val t =
  METIS_PROVE [arithmeticTheory.MULT_COMM, arithmeticTheory.MULT_ASSOC]
  ``a * b * c * d * e * f * g * h * i = i * h * g * f * e * d * c * b * a``;

(* Random equality example from Konrad Slind *)
val t =
  METIS_PROVE [arithmeticTheory.MOD_PLUS, arithmeticTheory.DIVMOD_ID,
               arithmeticTheory.MOD_MOD, arithmeticTheory.ADD_CLAUSES]
  ``!n x. 0 < n ==> ((x + n) MOD n = x MOD n)``;

(* ------------------------------------------------------------------------- *)
val () = METIS_TEST "some extreme examples";
(* ------------------------------------------------------------------------- *)

(* This one came from Mike Gordon: inefficiencies in basic HOL conversions *)
(* used to mean MESON took exponentially long in the number of variables.  *)
val t =
  METIS_PROVE []
  ``P (a,b,c,d,e,f,g,h,i,j,k,l,m,n,p,q,r,s,t,u,v,w,x,y,z) ==>
    ?a b c d e f g h i j k l m n p q r s t u v w x y z.
      P (a,b,c,d,e,f,g,h,i,j,k,l,m,n,p,q,r,s,t,u,v,w,x,y,z)``;

(* This one became possible when the HOL specific model was added. *)
(* Sadly, it's just too expensive for this test suite :-(
val t =
  METIS_PROVE [arithmeticTheory.MULT_COMM, arithmeticTheory.MULT_ASSOC]
  ``a*b*c*d*e*f*g*h*i*j*k*l*m*n*p*q*r*s*t*u*v*w*x*y*z=
    z*y*x*w*v*u*t*s*r*q*p*n*m*l*k*j*i*h*g*f*e*d*c*b*a``;
*)

(* ------------------------------------------------------------------------- *)
val () = SAY "Results presented in talks and papers";
(* ------------------------------------------------------------------------- *)

val t = WITH_PARM MESON (MPROVE []) los;
val t = WITH_PARM (TYPES o MESON) (MPROVE []) los;
val t = WITH_PARM (HIGHER_ORDER o MESON) (MPROVE []) los;
val t = WITH_PARM (TYPES o HIGHER_ORDER o MESON) (MPROVE []) los;

(* From Konrad Slind: strong induction implies weak induction *)
val t =
  METIS_PROVE [prim_recTheory.LESS_SUC_REFL, arithmeticTheory.num_CASES]
  ``(!P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n) ==>
    !P. P 0 /\ (!n. P n ==> P (SUC n)) ==> !n. P n``;
(* An alternative tactic proof (further reduced from Konrad's version)
   DISCH_THEN (fn t => NTAC 2 STRIP_TAC THEN MP_TAC (Q.ID_SPEC t)) THEN
   DISCH_THEN MATCH_MP_TAC THEN
   (Cases THEN1 ASM_REWRITE_TAC []) THEN
   DISCH_THEN (MP_TAC o Q.SPEC `n'`) THEN
   ASM_REWRITE_TAC [LESS_SUC_REFL] *)

(* too expensive
val t =
  WITH_PARM MESON
  (MPROVE [arithmeticTheory.MULT_ASSOC, arithmeticTheory.MULT_COMM])
   ``(!x y. divides x y = ?z. y = z * x) ==>
     (!x y z. divides x y ==> divides x (z * y))``; *)
