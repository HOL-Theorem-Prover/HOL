(* ===================================================================== *)
(* FILE          : boolScript.sml                                        *)
(* DESCRIPTION   : Definition of the logical constants and assertion of  *)
(*                 the axioms.                                           *)
(* AUTHORS       : (c) Mike Gordon, University of Cambridge              *)
(*                 Tom Melham, Richard Boulton, John Harrison,           *)
(*                 Konrad Slind, Michael Norrish, Jim Grundy, Joe Hurd   *)
(*                 and probably others that don't immediately come to    *)
(*                 mind.                                                 *)
(* ===================================================================== *)

structure boolScript =
struct

open HolKernel Parse
open Unicode TexTokenMap OpenTheoryMap

val _ = new_theory "bool";

(*---------------------------------------------------------------------------*
 *             BASIC DEFINITIONS                                             *
 *---------------------------------------------------------------------------*)

(* parsing/printing support for theory min *)
val _ = OpenTheory_tyop_name {tyop={Thy="min",Tyop="fun"},name=([],"->")}
val _ = OpenTheory_tyop_name {tyop={Thy="min",Tyop="bool"},name=([],"bool")}
val _ = OpenTheory_const_name {const={Thy="min",Name="="},name=([],"=")}
val _ = OpenTheory_const_name {const={Thy="min",Name="@"},name=([],"select")}

val ns = ["Data","Bool"]

val _ = unicode_version {u = UChar.imp, tmnm = "==>"}
val _ = TeX_notation {hol = "==>", TeX = ("\\HOLTokenImp{}", 1)}
val _ = TeX_notation {hol = UChar.imp, TeX = ("\\HOLTokenImp{}", 1)}
val _ = OpenTheory_const_name {const={Thy="min",Name="==>"},name=(ns,"==>")}

val _ = TeX_notation {hol = "\\", TeX = ("\\HOLTokenLambda{}", 1)}
val _ = TeX_notation {hol = UChar.lambda, TeX = ("\\HOLTokenLambda{}", 1)}

val _ = TeX_notation {hol = "@", TeX = ("\\HOLTokenHilbert{}", 1)}

(* records *)
val _ = TeX_notation {hol = "<|", TeX = ("\\HOLTokenLeftrec{}", 2)}
val _ = TeX_notation {hol = "|>", TeX = ("\\HOLTokenRightrec{}", 2)}

(* case expressions *)
val _ = TeX_notation {hol = "case", TeX = ("\\HOLKeyword{case}", 4)}
val _ = TeX_notation {hol = "of",   TeX = ("\\HOLKeyword{of}", 2)}
val _ = TeX_notation {hol = "=>", TeX = ("\\HOLTokenImp{}", 1)}

(* let expressions *)
val _ = TeX_notation {hol = "let", TeX = ("\\HOLKeyword{let}", 3)}
val _ = TeX_notation {hol = "and", TeX = ("\\HOLKeyword{and}", 2)}
val _ = TeX_notation {hol = "in",  TeX = ("\\HOLKeyword{in}", 2)}

(* if statements *)
val _ = TeX_notation {hol = "if",   TeX = ("\\HOLKeyword{if}", 2)}
val _ = TeX_notation {hol = "then", TeX = ("\\HOLKeyword{then}", 4)}
val _ = TeX_notation {hol = "else", TeX = ("\\HOLKeyword{else}", 4)}


val T_DEF =
 Definition.new_definition
   ("T_DEF",          Term `T = ((\x:bool. x) = \x:bool. x)`);

val _ = add_const "T";
val _ = OpenTheory_const_name {const={Thy="bool",Name="T"},name=(ns,"T")}

val FORALL_DEF =
 Definition.new_definition
   ("FORALL_DEF",     Term `! = \P:'a->bool. P = \x. T`);

val _ = (set_fixity "!" Binder; add_const "!");
val _ = unicode_version {u = UChar.forall, tmnm = "!"};
val _ = TeX_notation {hol = "!", TeX = ("\\HOLTokenForall{}",1)}
val _ = TeX_notation {hol = UChar.forall, TeX = ("\\HOLTokenForall{}",1)}
val _ = OpenTheory_const_name {const={Thy="bool",Name="!"},name=(ns,"!")}

val EXISTS_DEF =
 Definition.new_definition
   ("EXISTS_DEF",     Term `? = \P:'a->bool. P ($@ P)`);

val _ = (set_fixity "?" Binder; add_const "?");
val _ = unicode_version {u = UChar.exists, tmnm = "?"}
val _ = TeX_notation {hol = "?", TeX = ("\\HOLTokenExists{}",1)}
val _ = TeX_notation {hol = UChar.exists, TeX = ("\\HOLTokenExists{}",1)}
val _ = OpenTheory_const_name {const={Thy="bool",Name="?"},name=(ns,"?")}

val AND_DEF =
 Definition.new_definition
   ("AND_DEF",        Term `/\ = \t1 t2. !t. (t1 ==> t2 ==> t) ==> t`);

val _ = (add_infix ("/\\", 400, RIGHT); add_const "/\\");
val _ = unicode_version {u = UChar.conj, tmnm = "/\\"};
val _ = TeX_notation {hol = "/\\", TeX = ("\\HOLTokenConj{}",1)}
val _ = TeX_notation {hol = UChar.conj, TeX = ("\\HOLTokenConj{}",1)}
val _ = OpenTheory_const_name {const={Thy="bool",Name="/\\"},name=(ns,"/\\")}


val OR_DEF =
 Definition.new_definition
   ("OR_DEF",         Term `\/ = \t1 t2. !t. (t1 ==> t) ==> (t2 ==> t) ==> t`)

val _ = (add_infix ("\\/", 300, RIGHT); add_const "\\/");
val _ = unicode_version {u = UChar.disj, tmnm = "\\/"}
val _ = TeX_notation {hol = "\\/", TeX = ("\\HOLTokenDisj{}",1)}
val _ = TeX_notation {hol = UChar.disj, TeX = ("\\HOLTokenDisj{}",1)}
val _ = OpenTheory_const_name {const={Thy="bool",Name="\\/"},name=(ns,"\\/")}


val F_DEF =
 Definition.new_definition
   ("F_DEF",          Term `F = !t. t`);

val _ = Parse.add_const "F";
val _ = OpenTheory_const_name {const={Thy="bool",Name="F"},name=(ns,"F")}

val NOT_DEF =
 Definition.new_definition
   ("NOT_DEF",        Term `~ = \t. t ==> F`);

val _ = add_const "~";
val _ = OpenTheory_const_name {const={Thy="bool",Name="~"},name=(ns,"~")}

val EXISTS_UNIQUE_DEF =
Definition.new_definition
("EXISTS_UNIQUE_DEF", Term `?! = \P:'a->bool.
                                    $? P /\ !x y. P x /\ P y ==> (x=y)`);

val _ = (set_fixity "?!" Binder; add_const "?!")

val _ = unicode_version { u = UChar.exists ^ "!", tmnm = "?!"}
val _ = TeX_notation {hol = "?!", TeX = ("\\HOLTokenUnique{}",2)}
val _ = TeX_notation {hol = UChar.exists ^ "!", TeX = ("\\HOLTokenUnique{}",2)}
val _ = OpenTheory_const_name {const={Thy="bool",Name="?!"},name=(ns,"?!")}

val LET_DEF =
 Definition.new_definition
   ("LET_DEF",        Term `LET = \(f:'a->'b) x. f x`);

val _ = add_const "LET";
val _ = OpenTheory_const_name {const={Thy="bool",Name="LET"},name=(ns,"let")}

val COND_DEF =
 Definition.new_definition
   ("COND_DEF",       Term `COND = \t t1 t2.
                                      @x:'a. ((t=T) ==> (x=t1)) /\
                                             ((t=F) ==> (x=t2))`);
val _ = add_const "COND";
val _ = OpenTheory_const_name {const={Thy="bool",Name="COND"},name=(ns,"cond")}

val ONE_ONE_DEF =
 Definition.new_definition
   ("ONE_ONE_DEF",    Term `ONE_ONE = \f:'a->'b. !x1 x2.
                                         (f x1 = f x2) ==> (x1 = x2)`);

val _ = add_const "ONE_ONE";

val ONTO_DEF =
 Definition.new_definition
   ("ONTO_DEF",       Term `ONTO = \f:'a->'b. !y. ?x. y = f x`);

val _ = add_const "ONTO";

val TYPE_DEFINITION =
 Definition.new_definition
   ("TYPE_DEFINITION",
                      Term `TYPE_DEFINITION = \P:'a->bool. \rep:'b->'a.
                              (!x' x''. (rep x' = rep x'') ==> (x' = x'')) /\
                              (!x. P x = (?x'. x = rep x'))`);

val _ = add_const "TYPE_DEFINITION";
val _ = OpenTheory_const_name {const={Thy="bool",Name="TYPE_DEFINITION"},name=(["HOL4"],"TYPE_DEFINITION")}
val _ = OpenTheory_const_name {const={Thy="bool",Name="DATATYPE"},name=(["HOL4"],"DATATYPE")}


(*---------------------------------------------------------------------------*
 *   Parsing directives for some of the basic operators.                     *
 *---------------------------------------------------------------------------*)

open Portable;
val _ = add_rule {term_name   = "~",
                  fixity      = Prefix 900,
                  pp_elements = [TOK "~"],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundEachPhrase, (CONSISTENT, 0))};
val _ = unicode_version { u = UChar.neg, tmnm = "~"};
val _ = TeX_notation {hol = "~", TeX = ("\\HOLTokenNeg{}",1)}
val _ = TeX_notation {hol = UChar.neg, TeX = ("\\HOLTokenNeg{}",1)}

(* prettyprinting information here for "let" and "and" is completely ignored;
   the pretty-printer handles these specially.  These declarations are only
   for the parser's benefit. *)
val _ = add_rule {term_name   = GrammarSpecials.let_special,
                  fixity = Prefix 8,
                  pp_elements = [TOK "let", BreakSpace(1,0), TM,
                                 BreakSpace(1, 0), TOK "in",
                                 BreakSpace(1, 0)],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundEachPhrase, (INCONSISTENT, 0))};

val _ = add_rule {term_name = GrammarSpecials.and_special,
                  fixity = Infixl 9,
                  pp_elements = [TOK "and"],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundEachPhrase, (INCONSISTENT, 0))}

val _ = add_rule{term_name   = "COND",
                 fixity      = Prefix 70,
                 pp_elements = [PPBlock([TOK "if", BreakSpace(1,2), TM,
                                         BreakSpace(1,0),
                                         TOK "then"], (CONSISTENT, 0)),
                                BreakSpace(1,2), TM, BreakSpace(1,0),
                                TOK "else", BreakSpace(1,2)],
                 paren_style = OnlyIfNecessary,
                 block_style = (AroundEachPhrase, (CONSISTENT, 0))};


(*---------------------------------------------------------------------------*
 *                   AXIOMS                                                  *
 *                                                                           *
 * Bruno Barras noticed that the axiom IMP_ANTISYM_AX from the original      *
 * HOL logic was provable.                                                   *
 *---------------------------------------------------------------------------*)

val BOOL_CASES_AX =
 new_axiom
   ("BOOL_CASES_AX", Term `!t. (t=T) \/ (t=F)`);

val ETA_AX =
 new_axiom
   ("ETA_AX",        Term `!t:'a->'b. (\x. t x) = t`);

val SELECT_AX =
 new_axiom
   ("SELECT_AX",     Term `!(P:'a->bool) x. P x ==> P ($@ P)`);

val INFINITY_AX =
 new_axiom
   ("INFINITY_AX",   Term `?f:ind->ind. ONE_ONE f /\ ~ONTO f`);


(*---------------------------------------------------------------------------*
 * Miscellaneous utility definitions, of use in some packages.               *
 *---------------------------------------------------------------------------*)

val arb = new_constant("ARB",alpha);  (* Doesn't have to be defined at all. *)
val _ = OpenTheory_const_name {const={Thy="bool",Name="ARB"},name=(ns,"arb")}

val literal_case_DEF =
 Definition.new_definition
   ("literal_case_DEF",  Term `literal_case = \(f:'a->'b) x. f x`);

val _ = List.app add_const ["ARB", "literal_case"];
val _ = overload_on ("case", ``bool$literal_case``);
val _ = OpenTheory_const_name {const={Thy="bool",Name="literal_case"},name=(["HOL4"],"literal_case")}

val IN_DEF =
 Definition.new_definition
   ("IN_DEF",         Term `IN = \x (f:'a->bool). f x`);

val _ = (add_infix ("IN", 425, Parse.NONASSOC); add_const "IN");
val _ = unicode_version {u = UChar.setelementof, tmnm = "IN"};
val _ = TeX_notation {hol = "IN", TeX = ("\\HOLTokenIn{}",1)}
val _ = TeX_notation {hol = UChar.setelementof, TeX = ("\\HOLTokenIn{}",1)}
val _ = OpenTheory_const_name {const={Thy="bool",Name="IN"},name=(["Set"],"member")}

val RES_FORALL_DEF =
 Definition.new_definition
   ("RES_FORALL_DEF", Term `RES_FORALL = \p m. !x : 'a. x IN p ==> m x`);

val _ = (add_const "RES_FORALL"; associate_restriction ("!",  "RES_FORALL"));

val RES_EXISTS_DEF =
 Definition.new_definition
   ("RES_EXISTS_DEF", Term `RES_EXISTS = \p m. ?x : 'a. x IN p /\ m x`);

val _ = (add_const "RES_EXISTS"; associate_restriction ("?",  "RES_EXISTS"));

val RES_EXISTS_UNIQUE_DEF =
 Definition.new_definition
   ("RES_EXISTS_UNIQUE_DEF",
    Term `RES_EXISTS_UNIQUE =
          \p m. (?(x : 'a) :: p. m x) /\ !x y :: p. m x /\ m y ==> (x = y)`);

val _ = add_const "RES_EXISTS_UNIQUE";
val _ = associate_restriction ("?!",  "RES_EXISTS_UNIQUE");

val RES_SELECT_DEF =
 Definition.new_definition
   ("RES_SELECT_DEF", Term `RES_SELECT = \p m. @x : 'a. x IN p /\ m x`);

val _ = (add_const "RES_SELECT"; associate_restriction ("@",  "RES_SELECT"));

(* Note: RES_ABSTRACT comes later, defined by new_specification *)

(*---------------------------------------------------------------------------*)
(* Experimental rewriting directives                                         *)
(*---------------------------------------------------------------------------*)

val BOUNDED_DEF =
  Definition.new_definition
    ("BOUNDED_DEF",
     Term `BOUNDED = \(v:bool). T`);
val _ = OpenTheory_const_name {const={Thy="bool",Name="BOUNDED"},name=(["HOL4"],"bounded")}

(*---------------------------------------------------------------------------*)
(* Support for detecting datatypes in theory files                           *)
(*---------------------------------------------------------------------------*)

val DATATYPE_TAG_DEF =
  Definition.new_definition
    ("DATATYPE_TAG_DEF",
     Term`DATATYPE = \x. T`);

val _ = List.app add_const ["BOUNDED", "DATATYPE"];

(*---------------------------------------------------------------------------*
 *                   THEOREMS                                                *
 *---------------------------------------------------------------------------*)

val op --> = Type.-->
infix ## |->;

val ERR = Feedback.mk_HOL_ERR "boolScript"

val F = Term`F`
val T = Term`T`;
val implication = prim_mk_const{Name="==>", Thy="min"}
val select      = prim_mk_const{Name="@",   Thy="min"}
val conjunction = prim_mk_const{Name="/\\", Thy="bool"}
val disjunction = prim_mk_const{Name="\\/", Thy="bool"}
val negation    = prim_mk_const{Name="~",   Thy="bool"}
val universal   = prim_mk_const{Name="!",   Thy="bool"}
val existential = prim_mk_const{Name="?",   Thy="bool"}
val exists1     = prim_mk_const{Name="?!",  Thy="bool"}
val in_tm       = prim_mk_const{Name="IN",  Thy="bool"};


val dest_neg    = sdest_monop("~","bool")   (ERR"dest_neg" "");
val dest_eq     = sdest_binop("=","min")    (ERR"dest_eq" "");
val dest_disj   = sdest_binop("\\/","bool") (ERR"dest_disj" "");
val dest_conj   = sdest_binop("/\\","bool") (ERR"dest_conj" "");
val dest_forall = sdest_binder("!","bool")  (ERR"dest_forall" "");
val dest_exists = sdest_binder("?","bool")  (ERR"dest_exists" "");
fun strip_forall fm =
   if can dest_forall fm
   then let val (Bvar,Body) = dest_forall fm
            val (bvs,core) = strip_forall Body
        in ((Bvar::bvs), core)
        end
   else ([],fm);
val lhs = fst o dest_eq;
val rhs = snd o dest_eq;


local val imp = Term`$==>`  val notc = Term`$~`
in
fun dest_imp M =
 let val (Rator,conseq) = dest_comb M
 in if is_comb Rator
    then let val (Rator,ant) = dest_comb Rator
         in if Rator=imp then (ant,conseq)
            else raise Fail "dest_imp"
         end
    else if Rator=notc then (conseq,F) else raise Fail "dest_imp"
 end
end

fun mk_neg M              = Term `~^M`;
fun mk_eq(lhs,rhs)        = Term `^lhs = ^rhs`;
fun mk_imp(ant,conseq)    = Term `^ant ==> ^conseq`;
fun mk_conj(conj1,conj2)  = Term `^conj1 /\ ^conj2`;
fun mk_disj(disj1,disj2)  = Term `^disj1 \/ ^disj2`;
fun mk_forall(Bvar,Body)  = Term `!^Bvar. ^Body`
fun mk_exists(Bvar,Body)  = Term `?^Bvar. ^Body`
fun mk_exists1(Bvar,Body) = Term `?!^Bvar. ^Body`

val list_mk_forall = itlist (curry mk_forall)
val list_mk_exists = itlist (curry mk_exists)

(* also implemented in Drule *)
fun ETA_CONV t =
  let val (var, cmb) = dest_abs t
      val tysubst = [alpha |-> type_of var, beta |-> type_of cmb]
      val th = SPEC (rator cmb) (INST_TYPE tysubst ETA_AX)
  in
    TRANS (ALPHA t (lhs (concl th))) th
  end;

fun EXT th =
   let val (Bvar,_) = dest_forall(concl th)
       val th1 = SPEC Bvar th
       val (t1x, t2x) = dest_eq(concl th1)
       val x = rand t1x
       val th2 = ABS x th1
   in
   TRANS (TRANS(SYM(ETA_CONV (mk_abs(x, t1x)))) th2)
         (ETA_CONV (mk_abs(x,t2x)))
   end;

fun DISCH_ALL th = DISCH_ALL (DISCH (hd (hyp th)) th) handle _ => th;

fun PROVE_HYP ath bth = MP (DISCH (concl ath) bth) ath;

fun CONV_RULE conv th = EQ_MP (conv(concl th)) th;

fun RAND_CONV conv tm =
   let val (Rator,Rand) = dest_comb tm
   in AP_TERM Rator (conv Rand)
   end;

fun RATOR_CONV conv tm =
   let val (Rator,Rand) = dest_comb tm in AP_THM (conv Rator) Rand end;

fun ABS_CONV conv tm =
   let val (Bvar,Body) = dest_abs tm in ABS Bvar (conv Body) end;

fun QUANT_CONV conv = RAND_CONV(ABS_CONV conv);

fun RIGHT_BETA th = TRANS th (BETA_CONV(snd(dest_eq(concl th))));

fun UNDISCH th = MP th (ASSUME(fst(dest_imp(concl th))));

fun FALSITY_CONV tm = DISCH F (SPEC tm (EQ_MP F_DEF (ASSUME F)))

fun UNFOLD_OR_CONV tm =
  let val (disj1,disj2) = dest_disj tm in
  RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM OR_DEF disj1)) disj2)
  end;

(* common variables used throughout what follows *)
fun Av s = mk_var(s, alpha)
fun Bv s = mk_var(s, bool)
val tb = Bv "t"
val t1b = Bv "t1"
val t2b = Bv "t2"
val Pb = Bv "P"
val Qb = Bv "Q"
val Pab = mk_var("P", alpha --> bool)
val Qab = mk_var("Q", alpha --> bool)

val fabt = mk_var("f", alpha --> beta)
val xa = Av "x"
val ya = Av "y"

(*---------------------------------------------------------------------------
 *  |- T
 *---------------------------------------------------------------------------*)

val TRUTH = EQ_MP (SYM T_DEF) (REFL (--`\x:bool. x`--));
val _ = save_thm("TRUTH",TRUTH);

fun EQT_ELIM th = EQ_MP (SYM th) TRUTH;

(* SPEC could be built here. *)
(* GEN could be built here. *)

(* auxiliary functions to do bool case splitting *)
(* maps thm  |- P[x\t]  to  |- y=t ==> P[x\y] *)
fun CUT_EQUAL P x y t thm =
  let val e = mk_eq(y,t) in
  DISCH e (SUBST [(x|->SYM (ASSUME e))] P thm)
  end;

(* given proofs of P[x\T] and P[x\F], proves P[x\t] *)
fun BOOL_CASE P x t pt pf =
  let val th0 = SPEC t BOOL_CASES_AX
      val th1 = EQ_MP (UNFOLD_OR_CONV (concl th0)) th0
      val th2 = SPEC (subst[(x|->t)] P) th1 in
  MP (MP th2 (CUT_EQUAL P x t T pt)) (CUT_EQUAL P x t F pf)
  end;

fun EQT_INTRO th =
   let val t = concl th
       val x = genvar bool
   in
   BOOL_CASE (--`^x=T`--) x t (REFL T)
     (MP (FALSITY_CONV (--`F=T`--)) (EQ_MP (ASSUME(--`^t=F`--)) th))
   end;

(*---------------------------------------------------------------------------
 * |- !t1 t2. (t1 ==> t2) ==> (t2 ==> t1) ==> (t1 = t2)
 *---------------------------------------------------------------------------*)

infixr ==>
val op==> = mk_imp
infix ==
val op== = mk_eq
val IMP_ANTISYM_AX = save_thm(
  "IMP_ANTISYM_AX",
  let fun dsch t1 t2 th = DISCH (t2 ==> t1) (DISCH (t1 ==> t2) th)
      fun sch t1 t2 = (t1==>t2) ==> (t2==>t1) ==> (t1 == t2)
      val abs = MP (FALSITY_CONV (F == T)) (MP (ASSUME (T ==> F)) TRUTH)
      val tht = BOOL_CASE (sch T t2b) t2b t2b
                          (dsch T T (REFL T)) (dsch F T (SYM abs))
      val thf = BOOL_CASE (sch F t2b) t2b t2b
                          (dsch T F abs) (dsch F F (REFL F))
  in
    GEN t1b (GEN t2b (BOOL_CASE (sch t1b t2b) t1b t1b tht thf))
  end);

fun IMP_ANTISYM_RULE th1 th2 =
  let val (ant,conseq) = dest_imp(concl th1)
  in
     MP (MP (SPEC conseq (SPEC ant IMP_ANTISYM_AX)) th1) th2
  end;


(*---------------------------------------------------------------------------
 * |- !t. F ==> t
 *---------------------------------------------------------------------------*)

val FALSITY = save_thm("FALSITY", GEN tb (FALSITY_CONV tb))

fun CONTR tm th = MP (SPEC tm FALSITY) th

fun DISJ_IMP dth =
   let val (disj1,disj2) = dest_disj (concl dth)
       val nota = mk_neg disj1
   in
     DISCH nota
      (DISJ_CASES dth
         (CONTR disj2 (MP (ASSUME nota) (ASSUME disj1)))
         (ASSUME disj2))
   end

fun EQF_INTRO th = IMP_ANTISYM_RULE (NOT_ELIM th)
        (DISCH (Term`F`) (CONTR (dest_neg (concl th)) (ASSUME (Term`F`))));

fun SELECT_EQ x =
 let val ty = type_of x
     val choose = mk_const("@", (ty --> Type.bool) --> ty)
 in
  fn th => AP_TERM choose (ABS x th)
 end

fun GENL varl thm = itlist GEN varl thm;

fun SPECL tm_list th = rev_itlist SPEC tm_list th

fun GEN_ALL th = itlist GEN (set_diff (free_vars(concl th))
                                      (free_varsl (hyp th))) th;

local fun f v (vs,l) = let val v' = variant vs v in (v'::vs, v'::l) end
in
fun SPEC_ALL th =
   let val (hvs,con) = (free_varsl ## I) (hyp th, concl th)
       val fvs = free_vars con
       and vars = fst(strip_forall con)
   in
     SPECL (snd(itlist f vars (hvs@fvs,[]))) th
   end
end;

fun SUBST_CONV theta template tm =
  let fun retheta {redex,residue} = (redex |-> genvar(type_of redex))
      val theta0 = map retheta theta
      val theta1 = map (op |-> o (#residue ## #residue)) (zip theta0 theta)
  in
   SUBST theta1 (mk_eq(tm,subst theta0 template)) (REFL tm)
  end;

local fun combine [] [] = []
        | combine (v::rst1) (t::rst2) = (v |-> t) :: combine rst1 rst2
        | combine _ _ = raise Fail "SUBS"
in
fun SUBS ths th =
   let val ls = map (lhs o concl) ths
       val vars = map (genvar o type_of) ls
       val w = subst (combine ls vars) (concl th)
   in
     SUBST (combine vars ths) w th
   end
end;

fun IMP_TRANS th1 th2 =
   let val (ant,conseq) = dest_imp(concl th1)
   in DISCH ant (MP th2 (MP th1 (ASSUME ant))) end;

fun ADD_ASSUM t th = MP (DISCH t th) (ASSUME t);

fun SPEC_VAR th =
   let val (Bvar,_) = dest_forall (concl th)
       val bv' = variant (free_varsl (hyp th)) Bvar
   in (bv', SPEC bv' th)
   end;

fun MK_EXISTS bodyth =
   let val (x, sth) = SPEC_VAR bodyth
       val (a,b) = dest_eq (concl sth)
       val (abimp,baimp) = EQ_IMP_RULE sth
       fun HALF (p,q) pqimp =
          let val xp = mk_exists(x,p)
              and xq = mk_exists(x,q)
          in DISCH xp
              (CHOOSE (x, ASSUME xp) (EXISTS (xq,x) (MP pqimp (ASSUME p))))
          end
   in
     IMP_ANTISYM_RULE (HALF (a,b) abimp) (HALF (b,a) baimp)
   end;

fun SELECT_RULE th =
  let val (tm as (Bvar, Body)) = dest_exists(concl th)
      val v = genvar(type_of Bvar)
      val P = mk_abs tm
      val SELECT_AX' = INST_TYPE[alpha |-> type_of Bvar] SELECT_AX
      val th1 = SPEC v (SPEC P SELECT_AX')
      val (ant,conseq) = dest_imp(concl th1)
      val th2 = BETA_CONV ant
      and th3 = BETA_CONV conseq
      val th4 = EQ_MP th3 (MP th1 (EQ_MP(SYM th2) (ASSUME (rhs(concl th2)))))
  in
     CHOOSE (v,th) th4
  end;


(*---------------------------------------------------------------------------
     ETA_THM = |- !M. (\x. M x) = M
 ---------------------------------------------------------------------------*)

val ETA_THM = save_thm("ETA_THM", GEN_ALL(ETA_CONV (Term`\x:'a. (M x:'b)`)));

(*---------------------------------------------------------------------------
 *  |- !t. t \/ ~t
 *---------------------------------------------------------------------------*)

val EXCLUDED_MIDDLE = save_thm(
  "EXCLUDED_MIDDLE",
  let val th1 = RIGHT_BETA(AP_THM NOT_DEF tb)
      val th2 = DISJ1 (EQT_ELIM (ASSUME (tb == T))) (mk_neg tb)
      and th3 = DISJ2 tb (EQ_MP (SYM th1)
                                (DISCH tb (EQ_MP (ASSUME (tb == F))
                                                         (ASSUME tb))))
  in
     GEN tb (DISJ_CASES (SPEC tb BOOL_CASES_AX) th2 th3)
  end)

val _ = save_thm("EXCLUDED_MIDDLE",EXCLUDED_MIDDLE);

fun IMP_ELIM th =
  let val (ant,conseq) = dest_imp (concl th)
       val not_t1 = mk_neg ant
  in
   DISJ_CASES (SPEC ant EXCLUDED_MIDDLE)
              (DISJ2 not_t1 (MP th (ASSUME ant)))
              (DISJ1 (ASSUME not_t1) conseq)
  end;

(*---------------------------------------------------------------------------*
 *  |- !f y. (\x. f x) y = f y                                               *
 *---------------------------------------------------------------------------*)

val BETA_THM = save_thm(
  "BETA_THM",
  GENL [fabt, ya] (BETA_CONV (Term`(\x. (f:'a->'b) x) y`)))

(*---------------------------------------------------------------------------
     LET_THM = |- !f x. LET f x = f x
 ---------------------------------------------------------------------------*)

val LET_THM = save_thm(
  "LET_THM",
  GEN fabt (GEN xa
    (RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM LET_DEF fabt)) xa))))

(* |- $! f <=> !x. f x *)
val FORALL_THM = save_thm(
  "FORALL_THM",
  SYM (AP_TERM (Term `$! :('a->bool)->bool`)
               (ETA_CONV (Term `\x:'a. f x:bool`))))

(* |- $? f <=> ?x. f x *)
val EXISTS_THM = save_thm(
  "EXISTS_THM",
  SYM (AP_TERM (Term `$? :('a->bool)->bool`)
               (ETA_CONV (Term `\x:'a. f x:bool`))));

(*---------------------------------------------------------------------------*
 *  |- !t1:'a. !t2:'b. (\x. t1) t2 = t1                                      *
 *---------------------------------------------------------------------------*)

val ABS_SIMP =
   GENL [Term`t1:'a`, Term `t2:'b`]
        (BETA_CONV (Term`(\x:'b. t1:'a) t2`));

val _ = save_thm("ABS_SIMP", ABS_SIMP);

(*---------------------------------------------------------------------------
 *   |- !t. (!x.t)  =  t
 *---------------------------------------------------------------------------*)

val FORALL_SIMP = save_thm(
  "FORALL_SIMP",
  GEN tb (IMP_ANTISYM_RULE
           (DISCH ``!^xa. ^tb`` (SPEC xa (ASSUME ``!^xa.^tb``)))
           (DISCH tb (GEN xa (ASSUME tb)))));

(*---------------------------------------------------------------------------
 *   |- !t. (?x.t)  =  t
 *---------------------------------------------------------------------------*)

val EXISTS_SIMP = save_thm(
  "EXISTS_SIMP",
  let val ext = mk_exists(xa,tb)
  in
  GEN tb (IMP_ANTISYM_RULE
              (DISCH ext (CHOOSE(Av "p", ASSUME ext) (ASSUME tb)))
              (DISCH tb (EXISTS(ext, Av "r") (ASSUME tb))))
  end);

(*---------------------------------------------------------------------------
 *       |- !t1 t2. t1 ==> t2 ==> t1 /\ t2
 *---------------------------------------------------------------------------*)

val AND_INTRO_THM = save_thm(
  "AND_INTRO_THM",
   let val t12 = t1b ==> t2b ==> tb
       val th1 = GEN tb (DISCH t12 (MP (MP (ASSUME t12)
                                           (ASSUME t1b))
                                       (ASSUME t2b)))
       val th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM AND_DEF t1b)) t2b)
   in
     GEN t1b (GEN t2b (DISCH t1b (DISCH t2b (EQ_MP (SYM th2) th1))))
   end);

(*---------------------------------------------------------------------------
 * |- !t1 t2. t1 /\ t2 ==> t1
 *---------------------------------------------------------------------------*)

val AND1_THM = save_thm(
  "AND1_THM",
  let val t12 = mk_conj(t1b, t2b)
      val th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM AND_DEF t1b)) t2b)
      val th3 = SPEC t1b (EQ_MP th2 (ASSUME t12))
      val th4 = DISCH t1b (DISCH t2b (ADD_ASSUM t2b (ASSUME t1b)))
  in
    GEN t1b (GEN t2b (DISCH t12 (MP th3 th4)))
  end);

(*---------------------------------------------------------------------------
 *    |- !t1 t2. t1 /\ t2 ==> t2
 *---------------------------------------------------------------------------*)

val AND2_THM =
  let val t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      val th1 = ASSUME (--`^t1 /\ ^t2`--)
      val th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM AND_DEF t1)) t2)
      val th3 = SPEC t2 (EQ_MP th2 th1)
      val th4 = DISCH t1 (DISCH t2 (ADD_ASSUM t1 (ASSUME t2)))
  in
  GEN t1 (GEN t2 (DISCH (--`^t1 /\ ^t2`--) (MP th3 th4)))
  end;

val _ = save_thm("AND2_THM", AND2_THM);

(* CONJ, CONJUNCT1 and CONJUNCT2 should be built here.*)

fun CONJ_PAIR thm = (CONJUNCT1 thm, CONJUNCT2 thm);

fun CONJUNCTS th =
  (CONJUNCTS (CONJUNCT1 th) @ CONJUNCTS (CONJUNCT2 th)) handle _ => [th];

val LIST_CONJ = end_itlist CONJ

(*---------------------------------------------------------------------------
 *   |- !t1 t2. (t1 /\ t2) = (t2 /\ t1)
 *---------------------------------------------------------------------------*)

val CONJ_SYM =
  let val t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      val th1 = ASSUME (--`^t1 /\ ^t2`--)
      and th2 = ASSUME (--`^t2 /\ ^t1`--)
  in
  GEN t1 (GEN t2 (IMP_ANTISYM_RULE
                 (DISCH (--`^t1 /\ ^t2`--)
                        (CONJ(CONJUNCT2 th1)(CONJUNCT1 th1)))
                 (DISCH (--`^t2 /\ ^t1`--)
                        (CONJ(CONJUNCT2 th2)(CONJUNCT1 th2)))))
  end;

val _ = save_thm("CONJ_SYM", CONJ_SYM);
val _ = save_thm("CONJ_COMM", CONJ_SYM);

(*---------------------------------------------------------------------------
 * |- !t1 t2 t3. t1 /\ (t2 /\ t3) = (t1 /\ t2) /\ t3
 *---------------------------------------------------------------------------*)

val CONJ_ASSOC =
  let val t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      and t3 = --`t3:bool`--
      val th1 = ASSUME (--`^t1 /\ (^t2 /\ ^t3)`--)
      val th2 = ASSUME (--`(^t1 /\ ^t2) /\ ^t3`--)
      val th3 = DISCH (--`^t1 /\ (^t2 /\ ^t3)`--)
                   (CONJ (CONJ(CONJUNCT1 th1)
                              (CONJUNCT1(CONJUNCT2 th1)))
                         (CONJUNCT2(CONJUNCT2 th1)))
      and th4 = DISCH (--`(^t1 /\ ^t2) /\ ^t3`--)
                   (CONJ (CONJUNCT1(CONJUNCT1 th2))
                         (CONJ(CONJUNCT2(CONJUNCT1 th2))
                              (CONJUNCT2 th2)))
  in
  GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE th3 th4)))
  end;

val _ = save_thm("CONJ_ASSOC", CONJ_ASSOC);


(*---------------------------------------------------------------------------
 *  |- !t1 t2. t1 ==> t1 \/ t2
 *---------------------------------------------------------------------------*)

val OR_INTRO_THM1 =
  let val t = --`t:bool`--
      and t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      val th1 = ADD_ASSUM (--`^t2 ==> ^t`--) (MP (ASSUME (--`^t1 ==> ^t`--))
                                              (ASSUME t1))
      val th2 = GEN t (DISCH (--`^t1 ==> ^t`--) (DISCH (--`^t2 ==> ^t`--) th1))
      val th3 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM OR_DEF t1)) t2)
  in
    GEN t1 (GEN t2 (DISCH t1 (EQ_MP (SYM th3) th2)))
  end;

val _ = save_thm("OR_INTRO_THM1", OR_INTRO_THM1);

(*---------------------------------------------------------------------------
 * |- !t1 t2. t2 ==> t1 \/ t2
 *---------------------------------------------------------------------------*)

val OR_INTRO_THM2 =
  let val t  = --`t:bool`--
      and t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      val th1 = ADD_ASSUM (--`^t1 ==> ^t`--)
                     (MP (ASSUME (--`^t2 ==> ^t`--)) (ASSUME t2))
      val th2 = GEN t (DISCH (--`^t1 ==> ^t`--) (DISCH (--`^t2 ==> ^t`--) th1))
      val th3 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM OR_DEF t1)) t2)
  in
    GEN t1 (GEN t2 (DISCH t2 (EQ_MP (SYM th3) th2)))
  end;

val _ = save_thm("OR_INTRO_THM2", OR_INTRO_THM2);

(*---------------------------------------------------------------------------
 * |- !t t1 t2. (t1 \/ t2) ==> (t1 ==> t) ==> (t2 ==> t) ==> t
 *---------------------------------------------------------------------------*)

val OR_ELIM_THM =
   let val t =  --`t:bool`--
       and t1 = --`t1:bool`--
       and t2 = --`t2:bool`--
       val th1 = ASSUME (--`^t1 \/ ^t2`--)
       val th2 = UNFOLD_OR_CONV (concl th1)
       val th3 = SPEC t (EQ_MP th2 th1)
       val th4 = MP (MP th3 (ASSUME (--`^t1 ==> ^t`--)))
                    (ASSUME (--`^t2 ==> ^t`--))
       val th4 = DISCH (--`^t1 ==> ^t`--) (DISCH (--`^t2 ==> ^t`--) th4)
   in
   GEN t (GEN t1 (GEN t2 (DISCH (--`^t1 \/ ^t2`--) th4)))
   end;

val _ = save_thm("OR_ELIM_THM", OR_ELIM_THM);

(* DISJ1, DISJ2, DISJ_CASES should be built here. *)

fun DISJ_CASES_UNION dth ath bth =
    DISJ_CASES dth (DISJ1 ath (concl bth)) (DISJ2 (concl ath) bth);


(*---------------------------------------------------------------------------
 * |- !t. (t ==> F) ==> ~t
 *---------------------------------------------------------------------------*)

val IMP_F =
   let val t = --`t:bool`--
       val th1 = RIGHT_BETA (AP_THM NOT_DEF t)
   in
     GEN t (DISCH (--`^t ==> F`--)
                 (EQ_MP (SYM th1) (ASSUME (--`^t ==> F`--))))
   end;

val _ = save_thm("IMP_F", IMP_F);


(*---------------------------------------------------------------------------
 * |- !t. ~t ==> (t ==> F)
 *---------------------------------------------------------------------------*)

val F_IMP =
   let val t = --`t:bool`--
       val th1 = RIGHT_BETA(AP_THM NOT_DEF t)
   in
   GEN t (DISCH (--`~^t`--)
                (EQ_MP th1 (ASSUME (--`~^t`--))))
   end;

val _ = save_thm("F_IMP", F_IMP);


(*---------------------------------------------------------------------------
 * |- !t. ~t ==> (t=F)
 *---------------------------------------------------------------------------*)

val NOT_F =
   let val t = --`t:bool`--
       val th1 = MP (SPEC t F_IMP) (ASSUME (--`~ ^t`--))
       and th2 = SPEC t FALSITY
       val th3 = IMP_ANTISYM_RULE th1 th2
   in
   GEN t (DISCH (--`~^t`--) th3)
   end;

val _ = save_thm("NOT_F", NOT_F);

(*---------------------------------------------------------------------------
 *  |- !t. ~(t /\ ~t)
 *---------------------------------------------------------------------------*)

val NOT_AND =
   let val th = ASSUME (--`t /\ ~t`--)
   in NOT_INTRO(DISCH (--`t /\ ~t`--) (MP (CONJUNCT2 th) (CONJUNCT1 th)))
   end;

val _ = save_thm("NOT_AND", NOT_AND);


(*---------------------------------------------------------------------------
 * |- !t. (T /\ t) = t
 *---------------------------------------------------------------------------*)

val AND_CLAUSE1 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`T /\ ^t`--) (CONJUNCT2(ASSUME (--`T /\ ^t`--)))
       and th2 = DISCH t (CONJ TRUTH (ASSUME t))
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *  |- !t. (t /\ T) = t
 *---------------------------------------------------------------------------*)

val AND_CLAUSE2 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`^t /\ T`--) (CONJUNCT1(ASSUME (--`^t /\ T`--)))
       and th2 = DISCH t (CONJ (ASSUME t) TRUTH)
   in
     GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *   |- !t. (F /\ t) = F
 *---------------------------------------------------------------------------*)

val AND_CLAUSE3 =
   let val t = --`t:bool`--
       val th1 = IMP_TRANS (SPEC t (SPEC (--`F`--) AND1_THM))
                           (SPEC (--`F`--) FALSITY)
       and th2 = SPEC (--`F /\ ^t`--) FALSITY
   in
     GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *   |- !t. (t /\ F) = F
 *---------------------------------------------------------------------------*)

val AND_CLAUSE4 =
   let val t = --`t:bool`--
       val th1 = IMP_TRANS (SPEC (--`F`--) (SPEC t AND2_THM))
                           (SPEC (--`F`--) FALSITY)
       and th2 = SPEC (--`^t /\ F`--) FALSITY
   in
     GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *    |- !t. (t /\ t) = t
 *---------------------------------------------------------------------------*)

val AND_CLAUSE5 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`^t /\ ^t`--) (CONJUNCT1(ASSUME (--`^t /\ ^t`--)))
       and th2 = DISCH t (CONJ(ASSUME t)(ASSUME t))
   in
     GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *  |- !t. (T /\ t) = t /\
 *         (t /\ T) = t /\
 *         (F /\ t) = F /\
 *         (t /\ F) = F /\
 *         (t /\ t) = t
 *---------------------------------------------------------------------------*)

val AND_CLAUSES =
   let val t = --`t:bool`--
   in
   GEN t (LIST_CONJ [SPEC t AND_CLAUSE1, SPEC t AND_CLAUSE2,
                     SPEC t AND_CLAUSE3, SPEC t AND_CLAUSE4,
                     SPEC t AND_CLAUSE5])
   end;

val _ = save_thm("AND_CLAUSES", AND_CLAUSES);

(*---------------------------------------------------------------------------
 *   |- !t. (T \/ t) = T
 *---------------------------------------------------------------------------*)

val OR_CLAUSE1 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`T \/ ^t`--) TRUTH
       and th2 = DISCH (--`T`--) (DISJ1 TRUTH t)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *  |- !t. (t \/ T) = T
 *---------------------------------------------------------------------------*)

val OR_CLAUSE2 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`^t \/ T`--) TRUTH
       and th2 = DISCH (--`T`--) (DISJ2 t TRUTH)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *    |- (F \/ t) = t
 *---------------------------------------------------------------------------*)

val OR_CLAUSE3 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`F \/ ^t`--) (DISJ_CASES (ASSUME (--`F \/ ^t`--))
                                        (UNDISCH (SPEC t FALSITY))
                                        (ASSUME t))
       and th2 = SPEC t (SPEC (--`F`--) OR_INTRO_THM2)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *    |- !t. (t \/ F) = t
 *---------------------------------------------------------------------------*)

val OR_CLAUSE4 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`^t \/ F`--) (DISJ_CASES (ASSUME (--`^t \/ F`--))
                                             (ASSUME t)
                                             (UNDISCH (SPEC t FALSITY)))
       and th2 = SPEC (--`F`--) (SPEC t OR_INTRO_THM1)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *   |- !t. (t \/ t) = t
 *---------------------------------------------------------------------------*)

val OR_CLAUSE5 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`^t \/ ^t`--)
                  (DISJ_CASES(ASSUME (--`^t \/ ^t`--)) (ASSUME t) (ASSUME t))
       and th2 = DISCH t (DISJ1(ASSUME t)t)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 * |- !t. (T \/ t) = T /\
 *        (t \/ T) = T /\
 *        (F \/ t) = t /\
 *        (t \/ F) = t /\
 *        (t \/ t) = t
 *---------------------------------------------------------------------------*)

val OR_CLAUSES =
   let val t = --`t:bool`--
   in
   GEN t (LIST_CONJ [SPEC t OR_CLAUSE1, SPEC t OR_CLAUSE2,
                     SPEC t OR_CLAUSE3, SPEC t OR_CLAUSE4,
                     SPEC t OR_CLAUSE5])
   end;

val _ = save_thm("OR_CLAUSES", OR_CLAUSES);


(*---------------------------------------------------------------------------
 *  |- !t. (T ==> t) = t
 *---------------------------------------------------------------------------*)

val IMP_CLAUSE1 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`T ==> ^t`--) (MP (ASSUME (--`T ==> ^t`--)) TRUTH)
       and th2 = DISCH t (DISCH (--`T`--) (ADD_ASSUM (--`T`--) (ASSUME t)))
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *  |- !t. (F ==> t) = T
 *---------------------------------------------------------------------------*)

val IMP_CLAUSE2 =
   let val t = --`t:bool`--
   in GEN t (EQT_INTRO(SPEC t FALSITY))
   end;

(*---------------------------------------------------------------------------
 *  |- !t. (t ==> T) = T
 *---------------------------------------------------------------------------*)

val IMP_CLAUSE3 =
   let val t = --`t:bool`--
   in GEN t (EQT_INTRO(DISCH t (ADD_ASSUM t TRUTH)))
   end;

(*---------------------------------------------------------------------------
 *  |- ((T ==> F) = F) /\ ((F ==> F) = T)
 *---------------------------------------------------------------------------*)
val IMP_CLAUSE4 =
   let val th1 = DISCH (--`T ==> F`--) (MP (ASSUME (--`T ==> F`--)) TRUTH)
       and th2 = SPEC (--`T ==> F`--) FALSITY
       and th3 = EQT_INTRO(DISCH (--`F`--) (ASSUME (--`F`--)))
   in
   CONJ(IMP_ANTISYM_RULE th1 th2) th3
   end;

(*---------------------------------------------------------------------------
 *  |- !t. (t ==> F) = ~t
 *---------------------------------------------------------------------------*)

val IMP_CLAUSE5 =
    let val t = --`t:bool`--
        val th1 = SPEC t IMP_F
        and th2 = SPEC t F_IMP
    in
    GEN t (IMP_ANTISYM_RULE th1 th2)
    end;

(*---------------------------------------------------------------------------
 *  |- !t. (T ==> t) = t /\
 *         (t ==> T) = T /\
 *         (F ==> t) = T /\
 *         (t ==> t) = t /\
 *         (t ==> F) = ~t
 *---------------------------------------------------------------------------*)

val IMP_CLAUSES =
   let val t = --`t:bool`--
   in GEN t
      (LIST_CONJ [SPEC t IMP_CLAUSE1, SPEC t IMP_CLAUSE3,
                  SPEC t IMP_CLAUSE2, EQT_INTRO(DISCH t (ASSUME t)),
                  SPEC t IMP_CLAUSE5])
   end;

val _ = save_thm("IMP_CLAUSES", IMP_CLAUSES);


(*----------------------------------------------------------------------------
 *    |- (~~t = t) /\ (~T = F) /\ (~F = T)
 *---------------------------------------------------------------------------*)

val NOT_CLAUSES =
 CONJ
  (GEN (--`t:bool`--)
    (IMP_ANTISYM_RULE
      (DISJ_IMP(IMP_ELIM(DISCH (--`t:bool`--) (ASSUME (--`t:bool`--)))))
      (DISCH (--`t:bool`--)
       (NOT_INTRO(DISCH (--`~t`--) (UNDISCH (NOT_ELIM(ASSUME (--`~t`--)))))))))
  (CONJ (IMP_ANTISYM_RULE
          (DISCH (--`~T`--)
                 (MP (MP (SPEC (--`T`--) F_IMP) (ASSUME (--`~T`--))) TRUTH))
          (SPEC (--`~T`--) FALSITY))
        (IMP_ANTISYM_RULE (DISCH (--`~F`--) TRUTH)
                          (DISCH (--`T`--) (MP (SPEC (--`F`--) IMP_F)
                                               (SPEC (--`F`--) FALSITY)))));

val _ = save_thm("NOT_CLAUSES", NOT_CLAUSES);

(*---------------------------------------------------------------------------
 *   |- !x. x=x
 *---------------------------------------------------------------------------*)

val EQ_REFL = GEN (--`x : 'a`--) (REFL (--`x : 'a`--));

val _ = save_thm("EQ_REFL", EQ_REFL);

(*---------------------------------------------------------------------------
 *   |- !x. (x=x) = T
 *---------------------------------------------------------------------------*)

val REFL_CLAUSE = GEN (--`x: 'a`--) (EQT_INTRO(SPEC (--`x:'a`--) EQ_REFL));

val _ = save_thm("REFL_CLAUSE", REFL_CLAUSE );

(*---------------------------------------------------------------------------
 *   |- !x y. x=y  ==>  y=x
 *---------------------------------------------------------------------------*)

val EQ_SYM =
 let val x = --`x:'a`--
     and y = --`y:'a`--
 in
   GEN x (GEN y (DISCH (--`^x = ^y`--) (SYM(ASSUME (--`^x = ^y`--)))))
 end;

val _ = save_thm("EQ_SYM",EQ_SYM);

(*---------------------------------------------------------------------------
 *    |- !x y. (x = y) = (y = x)
 *---------------------------------------------------------------------------*)

val EQ_SYM_EQ =
   GEN (--`x:'a`--)
    (GEN (--`y:'a`--)
      (IMP_ANTISYM_RULE (SPEC (--`y:'a`--) (SPEC (--`x:'a`--) EQ_SYM))
                        (SPEC (--`x:'a`--) (SPEC (--`y:'a`--) EQ_SYM))));

val _ = save_thm("EQ_SYM_EQ",EQ_SYM_EQ);

(*---------------------------------------------------------------------------
 *    |- !f g. (!x. f x = g x)  ==>  f=g
 *---------------------------------------------------------------------------*)

val EQ_EXT =
   let val f = (--`f:'a->'b`--)
       and g = (--`g: 'a -> 'b`--)
   in
   GEN f (GEN g (DISCH (--`!x:'a. ^f (x:'a) = ^g (x:'a)`--)
                       (EXT(ASSUME (--`!x:'a. ^f (x:'a) = ^g (x:'a)`--)))))
   end;

val _ = save_thm("EQ_EXT",EQ_EXT);

(*---------------------------------------------------------------------------
      FUN_EQ_THM  |- !f g. (f = g) = !x. f x = g x
 ---------------------------------------------------------------------------*)

val FUN_EQ_THM =
  let val f = mk_var("f", Type.alpha --> Type.beta)
      val g = mk_var("g", Type.alpha --> Type.beta)
      val x = mk_var("x", Type.alpha)
      val f_eq_g = mk_eq(f,g)
      val fx_eq_gx = mk_eq(mk_comb(f,x),mk_comb(g,x))
      val uq_f_eq_g = mk_forall(x,fx_eq_gx)
      val th1 = GEN x (AP_THM (ASSUME f_eq_g) x);
      val th2 = MP (SPEC_ALL EQ_EXT) (ASSUME uq_f_eq_g);
  in
    GEN f (GEN g
        (IMP_ANTISYM_RULE (DISCH_ALL th1) (DISCH_ALL th2)))
  end;

val _ = save_thm("FUN_EQ_THM",FUN_EQ_THM);

(*---------------------------------------------------------------------------
 *    |- !x y z. x=y  /\  y=z  ==>  x=z
 *---------------------------------------------------------------------------*)

val EQ_TRANS =
   let val x = --`x:'a`--
       and y = --`y:'a`--
       and z = --`z:'a`--
       val xyyz  = (--`(^x = ^y) /\ (^y = ^z)`--)
   in
   GEN x
    (GEN y
     (GEN z
      (DISCH xyyz
       (TRANS (CONJUNCT1(ASSUME xyyz))
              (CONJUNCT2(ASSUME xyyz))))))
   end;

val _ = save_thm("EQ_TRANS",EQ_TRANS);

(*---------------------------------------------------------------------------
 *     |- ~(T=F) /\ ~(F=T)
 *---------------------------------------------------------------------------*)

val BOOL_EQ_DISTINCT =
   let val TF = --`T = F`--
       and FT = --`F = T`--
   in
   CONJ
    (NOT_INTRO(DISCH TF (EQ_MP (ASSUME TF) TRUTH)))
    (NOT_INTRO(DISCH FT (EQ_MP (SYM(ASSUME FT)) TRUTH)))
   end;

val _ = save_thm("BOOL_EQ_DISTINCT", BOOL_EQ_DISTINCT);


(*---------------------------------------------------------------------------
 *     |- !t. (T = t) = t
 *---------------------------------------------------------------------------*)

val EQ_CLAUSE1 =
   let val t = --`t:bool`--
       val Tt = --`T = ^t`--
       val th1 = DISCH Tt (EQ_MP (ASSUME Tt) TRUTH)
       and th2 = DISCH t (SYM(EQT_INTRO(ASSUME t)))
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *  |- !t. (t = T) = t
 *---------------------------------------------------------------------------*)

val EQ_CLAUSE2 =
   let val t = --`t:bool`--
       val tT = --`^t = T`--
       val th1 = DISCH tT (EQ_MP (SYM (ASSUME tT)) TRUTH)
       and th2 = DISCH t (EQT_INTRO(ASSUME t))
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *    |- !t. (F = t) = ~t
 *---------------------------------------------------------------------------*)

val EQ_CLAUSE3 =
   let val t = --`t:bool`--
       val Ft = --`F = ^t`--
       val tF = --`^t = F`--
       val th1 = DISCH Ft (MP (SPEC t IMP_F)
                              (DISCH t (EQ_MP(SYM(ASSUME Ft))
                                             (ASSUME t))))
       and th2 = IMP_TRANS (SPEC t NOT_F)
                           (DISCH tF (SYM(ASSUME tF)))
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *  |- !t. (t = F) = ~t
 *---------------------------------------------------------------------------*)

val EQ_CLAUSE4 =
   let val t = --`t:bool`--
       val tF = --`^t = F`--
       val th1 = DISCH tF (MP (SPEC t IMP_F)
                              (DISCH t (EQ_MP(ASSUME tF)
                                             (ASSUME t))))
       and th2 = SPEC t NOT_F
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *  |- !t.  (T = t)  =  t  /\
 *          (t = T)  =  t  /\
 *          (F = t)  =  ~t /\
 *          (t = F)  =  ~t
 *---------------------------------------------------------------------------*)

val EQ_CLAUSES =
   let val t = --`t:bool`--
   in
   GEN t (LIST_CONJ [SPEC t EQ_CLAUSE1, SPEC t EQ_CLAUSE2,
                     SPEC t EQ_CLAUSE3, SPEC t EQ_CLAUSE4])
   end;

val _ = save_thm("EQ_CLAUSES", EQ_CLAUSES);


(*---------------------------------------------------------------------------
 *    |- !t1 t2 :'a. COND T t1 t2 = t1
 *---------------------------------------------------------------------------*)

val COND_CLAUSE1 =
 let val (x,t1,t2,v) = (Term`x:'a`, Term`t1:'a`,
                        Term`t2:'a`, genvar Type.bool)
     val th1 = RIGHT_BETA(AP_THM
                 (RIGHT_BETA(AP_THM
                    (RIGHT_BETA(AP_THM COND_DEF (--`T`--))) t1))t2)
     val TT = EQT_INTRO(REFL (--`T`--))
     val th2 = SUBST [v |-> SYM TT]
                     (--`(^v ==> (^x=^t1)) = (^x=^t1)`--)
                     (CONJUNCT1 (SPEC (--`^x=^t1`--) IMP_CLAUSES))
     and th3 = DISCH (--`T=F`--)
                     (MP (SPEC (--`^x=^t2`--) FALSITY)
                         (UNDISCH(MP (SPEC (--`T=F`--) F_IMP)
                                     (CONJUNCT1 BOOL_EQ_DISTINCT))))
     val th4 = DISCH (--`^x=^t1`--)
                     (CONJ(EQ_MP(SYM th2)(ASSUME (--`^x=^t1`--)))th3)
     and th5 = DISCH (--`((T=T) ==> (^x=^t1))/\((T=F) ==> (^x=^t2))`--)
                     (MP (CONJUNCT1(ASSUME (--`((T=T) ==> (^x=^t1))/\
                                               ((T=F) ==> (^x=^t2))`--)))
                         (REFL (--`T`--)))
     val th6 = IMP_ANTISYM_RULE th4 th5
     val th7 = TRANS th1 (SYM(SELECT_EQ x th6))
     val th8 = EQ_MP (SYM(BETA_CONV (--`(\ ^x.^x = ^t1) ^t1`--))) (REFL t1)
     val th9 = MP (SPEC t1 (SPEC (--`\ ^x.^x = ^t1`--) SELECT_AX)) th8
 in
   GEN t1 (GEN t2 (TRANS th7 (EQ_MP (BETA_CONV(concl th9)) th9)))
 end;


(*---------------------------------------------------------------------------
 *    |- !tm1 tm2:'a. COND F tm1 tm2 = tm2
 *
 *   Note that there is a bound variable conflict if we use use t1
 *   and t2 as the variable names. That would be a good test of the
 *   substitution algorithm.
 *---------------------------------------------------------------------------*)

val COND_CLAUSE2 =
   let val (x,t1,t2,v) = (--`x:'a`--,  --`tm1:'a`--, --`tm2:'a`--,
                          genvar Type.bool)
       val th1 = RIGHT_BETA(AP_THM
                   (RIGHT_BETA(AP_THM
                     (RIGHT_BETA(AP_THM COND_DEF (--`F`--))) t1))t2)
       val FF = EQT_INTRO(REFL (--`F`--))
       val th2 = SUBST [v |-> SYM FF]
                       (--`(^v ==> (^x=^t2))=(^x=^t2)`--)
                       (CONJUNCT1(SPEC (--`^x=^t2`--) IMP_CLAUSES))
       and th3 = DISCH (--`F=T`--) (MP (SPEC (--`^x=^t1`--) FALSITY)
                                 (UNDISCH (MP (SPEC (--`F=T`--) F_IMP)
                                              (CONJUNCT2 BOOL_EQ_DISTINCT))))
       val th4 = DISCH (--`^x=^t2`--)
                       (CONJ th3 (EQ_MP(SYM th2)(ASSUME (--`^x=^t2`--))))
       and th5 = DISCH (--`((F=T) ==> (^x=^t1)) /\ ((F=F) ==> (^x=^t2))`--)
                       (MP (CONJUNCT2(ASSUME (--`((F=T) ==> (^x=^t1)) /\
                                                 ((F=F) ==> (^x=^t2))`--)))
                           (REFL (--`F`--)))
       val th6 = IMP_ANTISYM_RULE th4 th5
       val th7 = TRANS th1 (SYM(SELECT_EQ x th6))
       val th8 = EQ_MP (SYM(BETA_CONV (--`(\ ^x.^x = ^t2) ^t2`--)))
                       (REFL t2)
       val th9 = MP (SPEC t2 (SPEC (--`\ ^x.^x = ^t2`--) SELECT_AX)) th8
   in
     GEN t1 (GEN t2 (TRANS th7 (EQ_MP (BETA_CONV(concl th9)) th9)))
   end;


(*---------------------------------------------------------------------------
 *    |- !t1:'a.!t2:'a. ((T => t1 | t2) = t1) /\ ((F => t1 | t2) = t2)
 *---------------------------------------------------------------------------*)

val COND_CLAUSES =
   let val (t1,t2) = (--`t1:'a`--, --`t2:'a`--)
   in
   GEN t1 (GEN t2 (CONJ(SPEC t2(SPEC t1 COND_CLAUSE1))
                       (SPEC t2(SPEC t1 COND_CLAUSE2))))
   end;

val _ = save_thm("COND_CLAUSES", COND_CLAUSES);


(*--------------------------------------------------------------------- *)
(* |- b. !t. (b => t | t) = t						*)
(*					                   TFM 90.07.23 *)
(*--------------------------------------------------------------------- *)

val COND_ID =
   let val b = --`b:bool`--
       and t = --`t:'a`--
       val def = INST_TYPE [beta |-> alpha] COND_DEF
       val th1 = itlist (fn x => RIGHT_BETA o (C AP_THM x))
                        [t,t,b] def
       val p = genvar bool
       val asm1 = ASSUME (--`((^b=T)==>^p) /\ ((^b=F)==>^p)`--)
       val th2 = DISJ_CASES (SPEC b BOOL_CASES_AX)
                            (UNDISCH (CONJUNCT1 asm1))
                            (UNDISCH (CONJUNCT2 asm1))
       val imp1 = DISCH (concl asm1) th2
       val asm2 = ASSUME p
       val imp2 = DISCH p (CONJ (DISCH (--`^b=T`--)
                                       (ADD_ASSUM (--`^b=T`--) asm2))
	                        (DISCH (--`^b=F`--)
                                       (ADD_ASSUM (--`^b=F`--) asm2)))
       val lemma = SPEC (--`x:'a = ^t`--)
                        (GEN p (IMP_ANTISYM_RULE imp1 imp2))
       val th3 = TRANS th1 (SELECT_EQ (--`x:'a`--) lemma)
       val th4 = EQ_MP (SYM(BETA_CONV (--`(\x.x = ^t) ^t`--)))
                       (REFL t)
       val th5 = MP (SPEC t (SPEC (--`\x.x = ^t` --) SELECT_AX)) th4
       val lemma2 = EQ_MP (BETA_CONV(concl th5)) th5
   in
     GEN b (GEN t (TRANS th3 lemma2))
   end;

val _ = save_thm("COND_ID", COND_ID);

(*---------------------------------------------------------------------------
      SELECT_THM = |- !P. P (@x. P x) = ?x. P x
 ---------------------------------------------------------------------------*)

val SELECT_THM =
  GEN (Term`P:'a->bool`)
   (SYM (RIGHT_BETA(RIGHT_BETA
          (AP_THM EXISTS_DEF (Term`\x:'a. P x:bool`)))));

val _ = save_thm("SELECT_THM", SELECT_THM);

(* ---------------------------------------------------------------------*)
(* SELECT_REFL = |- !x. (@y. y = x) = x                                 *)
(* ---------------------------------------------------------------------*)

val SELECT_REFL =
  let val th1 = SPEC (--`x:'a`--)
                      (SPEC (--`\y:'a. y = x`--) SELECT_AX)
      val ths = map BETA_CONV [--`(\y:'a. y = x) x`--,
                               --`(\y:'a. y = x)(@y. y = x)`--]
      val th2 = SUBST[Term`u:bool` |-> el 1 ths, Term`v:bool` |-> el 2 ths]
                     (Term`u ==> v`) th1
  in
  GEN (--`x:'a`--) (MP th2 (REFL (--`x:'a`--)))
  end;

val _ = save_thm("SELECT_REFL", SELECT_REFL);

val SELECT_REFL_2 =
  let val x = mk_var("x",   Type.alpha)
      val y = mk_var("y",   Type.alpha)
      val th1 = REFL x
      val th2 = EXISTS (mk_exists(y,mk_eq(x,y)),x) th1
      val th3 = SPEC y (SPEC (mk_abs(y,mk_eq(x,y))) SELECT_AX)
     val th4 = UNDISCH th3
     val th5 = DISCH_ALL(SYM (EQ_MP (BETA_CONV (concl th4)) th4))
     val th6 = UNDISCH(CONV_RULE (RATOR_CONV (RAND_CONV BETA_CONV)) th5)
 in
   GEN x (CHOOSE(y,th2) th6)
 end;

val _ = save_thm("SELECT_REFL_2", SELECT_REFL_2);

(*---------------------------------------------------------------------------*)
(* SELECT_UNIQUE = |- !P x. (!y. P y = (y = x)) ==> ($@ P = x)               *)
(*---------------------------------------------------------------------------*)

val SELECT_UNIQUE =
  let fun mksym tm = DISCH tm (SYM(ASSUME tm))
      val th0 = IMP_ANTISYM_RULE (mksym (--`y:'a = x`--))
                                 (mksym (--`x:'a = y`--))
      val th1 = SPEC (--`y:'a`--) (ASSUME (--`!y:'a. P y = (y = x)`--))
      val th2 = EXT(GEN (--`y:'a`--) (TRANS th1 th0))
      val th3 = AP_TERM (--`$@ :('a->bool)->'a`--) th2
      val th4 = TRANS (BETA_CONV (--`(\y:'a. y = x) y`--)) th0
      val th5 = AP_TERM (--`$@ :('a->bool)->'a`--) (EXT(GEN (--`y:'a`--) th4))
      val th6 = TRANS (TRANS th3 (SYM th5)) (SPEC (--`x:'a`--) SELECT_REFL)
  in
  GENL [(--`P:'a->bool`--), (--`x:'a`--)]
       (DISCH (--`!y:'a. P y = (y = x)`--) th6)
  end;

val _ = save_thm("SELECT_UNIQUE", SELECT_UNIQUE);

(* ----------------------------------------------------------------------
    SELECT_ELIM_THM = |- !P Q. (?x. P x) /\ (!x. P x ==> Q x) ==> Q ($@ P)
   ---------------------------------------------------------------------- *)

val SELECT_ELIM_THM = let
  val P = mk_var("P", alpha --> bool)
  val Q = mk_var("Q", alpha --> bool)
  val x = mk_var("x", alpha)
  val Px = mk_comb(P, x)
  val Qx = mk_comb(Q, x)
  val PimpQ = mk_imp(Px, Qx)
  val allPimpQ = mk_forall(x, PimpQ)
  val exPx = mk_exists (x, Px)
  val selP = mk_comb(prim_mk_const{Thy = "min", Name = "@"}, P)
  val asm_t = mk_conj(exPx, allPimpQ)
  val asm = ASSUME asm_t
  val (ex_th, forall_th) = CONJ_PAIR asm
  val imp_th = SPEC selP forall_th
  val Px_th = ASSUME Px
  val PselP_th0 = UNDISCH (SPEC_ALL SELECT_AX)
  val PselP_th = CHOOSE(x, ex_th) PselP_th0
in
  save_thm("SELECT_ELIM_THM", GENL [P, Q] (DISCH_ALL (MP imp_th PselP_th)))
end

(* -------------------------------------------------------------------------*)
(* NOT_FORALL_THM = |- !P. ~(!x. P x) = ?x. ~P x                   	    *)
(* -------------------------------------------------------------------------*)

val NOT_FORALL_THM =
    let val f = ``P:'a->bool``
	val x = ``x:'a``
	val t = mk_comb(f,x)
	val all = mk_forall(x,t)
	and exists = mk_exists(x,mk_neg t)
	val nott = ASSUME (mk_neg t)
	val th1 = DISCH all (MP nott (SPEC x (ASSUME all)))
	val imp1 = DISCH exists (CHOOSE (x, ASSUME exists) (NOT_INTRO th1))
	val th2 =
	    CCONTR t (MP (ASSUME(mk_neg exists)) (EXISTS(exists,x)nott))
	val th3 = CCONTR exists (MP (ASSUME (mk_neg all)) (GEN x th2))
	val imp2 = DISCH (mk_neg all) th3
    in
	GEN f (IMP_ANTISYM_RULE imp2 imp1)
    end;

val _ = save_thm("NOT_FORALL_THM",NOT_FORALL_THM);


(* ------------------------------------------------------------------------- *)
(* NOT_EXISTS_THM = |- !P. ~(?x. P x) = (!x. ~P x)                   	    *)
(* ------------------------------------------------------------------------- *)

val NOT_EXISTS_THM =
    let val f = (--`P:'a->bool`--)
	val x = (--`x:'a`--)
	val t = mk_comb(f,x)
	val tm = mk_neg(mk_exists(x,t))
	val all = mk_forall(x,mk_neg t)
	val asm1 = ASSUME t
	val thm1 = MP (ASSUME tm) (EXISTS (rand tm, x) asm1)
	val imp1 = DISCH tm (GEN x (NOT_INTRO (DISCH t thm1)))
	val asm2 = ASSUME  all and asm3 = ASSUME (rand tm)
	val thm2 = DISCH (rand tm) (CHOOSE (x,asm3) (MP (SPEC x asm2) asm1))
	val imp2 = DISCH all (NOT_INTRO thm2)
    in
	GEN f (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("NOT_EXISTS_THM",NOT_EXISTS_THM);


(* ------------------------------------------------------------------------- *)
(* FORALL_AND_THM |- !P Q. (!x. P x /\ Q x) = ((!x. P x) /\ (!x. Q x))       *)
(* ------------------------------------------------------------------------- *)

val FORALL_AND_THM =
    let val f = (--`P:'a->bool`--)
	val g = (--`Q:'a->bool`--)
	val x = (--`x:'a`--)
	val th1 = ASSUME (--`!x:'a. (P x) /\ (Q x)`--)
	val imp1 =
	    (uncurry CONJ) ((GEN x ## GEN x) (CONJ_PAIR (SPEC x th1)))
	val th2 = ASSUME (--`(!x:'a. P x) /\ (!x:'a. Q x)`--)
	val imp2 =
	    GEN x (uncurry CONJ ((SPEC x ## SPEC x) (CONJ_PAIR th2)))
    in
	    GENL [f,g] (IMP_ANTISYM_RULE (DISCH_ALL imp1) (DISCH_ALL imp2))
    end;

val _ = save_thm("FORALL_AND_THM",FORALL_AND_THM);



(* ------------------------------------------------------------------------- *)
(* LEFT_AND_FORALL_THM = |- !P Q. (!x. P x) /\ Q = (!x. P x /\ Q)            *)
(* ------------------------------------------------------------------------- *)

val LEFT_AND_FORALL_THM =
    let val x = (--`x:'a`--)
	val f = (--`P:'a->bool`--)
	val Q = (--`Q:bool`--)
	val th1 = ASSUME (--`(!x:'a. P x) /\ Q`--)
	val imp1 = GEN x ((uncurry CONJ) ((SPEC x ## I) (CONJ_PAIR th1)))
	val th2 = ASSUME (--`!x:'a. P x /\ Q`--)
	val imp2 = (uncurry CONJ) ((GEN x ## I) (CONJ_PAIR (SPEC x th2)))
    in
	GENL [f,Q] (IMP_ANTISYM_RULE (DISCH_ALL imp1) (DISCH_ALL imp2))
    end;

val _ = save_thm("LEFT_AND_FORALL_THM",LEFT_AND_FORALL_THM);


(* ------------------------------------------------------------------------- *)
(* RIGHT_AND_FORALL_THM = |- !P Q. P /\ (!x. Q x) = (!x. P /\ Q x)           *)
(* ------------------------------------------------------------------------- *)

val RIGHT_AND_FORALL_THM =
    let	val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val g = (--`Q:'a->bool`--)
	val th1 = ASSUME (--`P /\ (!x:'a. Q x)`--)
	val imp1 = GEN x ((uncurry CONJ) ((I ## SPEC x) (CONJ_PAIR th1)))
	val th2 = ASSUME (--`!x:'a. P /\ Q x`--)
	val imp2 = (uncurry CONJ) ((I ## GEN x) (CONJ_PAIR (SPEC x th2)))
    in
	GENL [P,g] (IMP_ANTISYM_RULE (DISCH_ALL imp1) (DISCH_ALL imp2))
    end;

val _ = save_thm("RIGHT_AND_FORALL_THM",RIGHT_AND_FORALL_THM);


(* ------------------------------------------------------------------------- *)
(* EXISTS_OR_THM |- !P Q. (?x. P x \/ Q x) = ((?x. P x) \/ (?x. Q x))        *)
(* ------------------------------------------------------------------------- *)

val EXISTS_OR_THM =
    let val f = (--`P:'a->bool`--)
	val g = (--`Q:'a->bool`--)
	val x = (--`x:'a`--)
	val P = mk_comb(f,x)
	val Q = mk_comb(g,x)
	val tm = mk_exists (x,mk_disj(P,Q))
	val ep = mk_exists (x,P)
	and eq = mk_exists(x,Q)
	val Pth = EXISTS(ep,x)(ASSUME P)
	and Qth = EXISTS(eq,x)(ASSUME Q)
	val thm1 = DISJ_CASES_UNION (ASSUME(mk_disj(P,Q))) Pth Qth
	val imp1 = DISCH tm (CHOOSE (x,ASSUME tm) thm1)
	val t1 = DISJ1 (ASSUME P) Q and t2 = DISJ2 P (ASSUME Q)
	val th1 = EXISTS(tm,x) t1 and th2 = EXISTS(tm,x) t2
	val e1 = CHOOSE (x,ASSUME ep) th1 and e2 = CHOOSE (x,ASSUME eq) th2
	val thm2 = DISJ_CASES (ASSUME(mk_disj(ep,eq))) e1 e2
	val imp2 = DISCH (mk_disj(ep,eq)) thm2
    in
	GENL [f,g] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("EXISTS_OR_THM",EXISTS_OR_THM);


(* ------------------------------------------------------------------------- *)
(* LEFT_OR_EXISTS_THM = |- (?x. P x) \/ Q = (?x. P x \/ Q)                   *)
(* ------------------------------------------------------------------------- *)

val LEFT_OR_EXISTS_THM =
    let val x = (--`x:'a`--)
	val Q = (--`Q:bool`--)
	val f = (--`P:'a->bool`--)
	val P = mk_comb(f,x)
	val ep = mk_exists(x,P)
	val tm = mk_disj(ep,Q)
	val otm = mk_exists(x,mk_disj(P,Q))
	val t1 = DISJ1 (ASSUME P) Q
        val t2 = DISJ2 P (ASSUME Q)
	val th1 = EXISTS(otm,x) t1 and th2 = EXISTS(otm,x) t2
	val thm1 = DISJ_CASES (ASSUME tm) (CHOOSE(x,ASSUME ep)th1) th2
	val imp1 = DISCH tm thm1
	val Pth = EXISTS(ep,x)(ASSUME P) and Qth = ASSUME Q
	val thm2 = DISJ_CASES_UNION (ASSUME(mk_disj(P,Q))) Pth Qth
	val imp2 = DISCH otm (CHOOSE (x,ASSUME otm) thm2)
    in
	GENL [f,Q] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("LEFT_OR_EXISTS_THM",LEFT_OR_EXISTS_THM);


(* ------------------------------------------------------------------------- *)
(* RIGHT_OR_EXISTS_THM = |- P \/ (?x. Q x) = (?x. P \/ Q x)                  *)
(* ------------------------------------------------------------------------- *)

val RIGHT_OR_EXISTS_THM =
    let	val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val g = (--`Q:'a->bool`--)
	val Q = mk_comb(g,x)
	val eq = mk_exists(x,Q)
	val tm = mk_disj(P,eq)
	val otm = mk_exists(x,mk_disj(P,Q))
	val t1 = DISJ1 (ASSUME P) Q and t2 = DISJ2 P (ASSUME Q)
	val th1 = EXISTS(otm,x) t1 and th2 = EXISTS(otm,x) t2
	val thm1 = DISJ_CASES (ASSUME tm) th1 (CHOOSE(x,ASSUME eq)th2)
	val imp1 = DISCH tm thm1
	val Qth = EXISTS(eq,x)(ASSUME Q) and Pth = ASSUME P
	val thm2 = DISJ_CASES_UNION (ASSUME(mk_disj(P,Q))) Pth Qth
	val imp2 = DISCH otm (CHOOSE (x,ASSUME otm)  thm2)
    in
	    GENL [P,g] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("RIGHT_OR_EXISTS_THM",RIGHT_OR_EXISTS_THM);


(* ------------------------------------------------------------------------- *)
(* BOTH_EXISTS_AND_THM = |- !P Q. (?x. P /\ Q) = (?x. P) /\ (?x. Q)          *)
(* ------------------------------------------------------------------------- *)

val BOTH_EXISTS_AND_THM =
    let	val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val Q = (--`Q:bool`--)
	val t = mk_conj(P,Q)
	val exi = mk_exists(x,t)
	val (t1,t2) = CONJ_PAIR (ASSUME t)
	val t11 = EXISTS ((mk_exists(x,P)),x) t1
	val t21 = EXISTS ((mk_exists(x,Q)),x) t2
	val imp1 = DISCH_ALL (CHOOSE (x,
                    ASSUME (mk_exists(x,mk_conj(P,Q))))
		   (CONJ t11 t21))
	val th21 = EXISTS (exi,x) (CONJ (ASSUME P) (ASSUME Q))
	val th22 = CHOOSE(x,ASSUME(mk_exists(x,P))) th21
	val th23 = CHOOSE(x,ASSUME(mk_exists(x,Q))) th22
	val (u1,u2) =
	    CONJ_PAIR (ASSUME (mk_conj(mk_exists(x,P),mk_exists(x,Q))))
	val th24 = PROVE_HYP u1 (PROVE_HYP u2 th23)
	val imp2 = DISCH_ALL th24
    in
	GENL [P,Q] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("BOTH_EXISTS_AND_THM",BOTH_EXISTS_AND_THM);

(* ------------------------------------------------------------------------- *)
(* LEFT_EXISTS_AND_THM = |- !P Q. (?x. P x /\ Q) = (?x. P x) /\ Q            *)
(* ------------------------------------------------------------------------- *)

val LEFT_EXISTS_AND_THM =
    let val x = (--`x:'a`--)
	val f = (--`P:'a->bool`--)
	val P = mk_comb(f,x)
	val Q = (--`Q:bool`--)
	val t = mk_conj(P,Q)
	val exi = mk_exists(x,t)
	val (t1,t2) = CONJ_PAIR (ASSUME t)
	val t11 = EXISTS ((mk_exists(x,P)),x) t1
	val imp1 =
	    DISCH_ALL
		(CHOOSE
		 (x, ASSUME (mk_exists(x,mk_conj(P,Q))))
		    (CONJ t11 t2))
	val th21 = EXISTS (exi,x) (CONJ (ASSUME P) (ASSUME Q))
	val th22 = CHOOSE(x,ASSUME(mk_exists(x,P))) th21
	val (u1,u2) = CONJ_PAIR(ASSUME(mk_conj(mk_exists(x,P), Q)))
	val th23 = PROVE_HYP u1 (PROVE_HYP u2 th22)
	val imp2 = DISCH_ALL th23
    in
	GENL [f,Q] (IMP_ANTISYM_RULE imp1 imp2)
    end ;

val _ = save_thm("LEFT_EXISTS_AND_THM",LEFT_EXISTS_AND_THM);

(* ------------------------------------------------------------------------- *)
(* RIGHT_EXISTS_AND_THM = |- !P Q. (?x. P /\ Q x) = P /\ (?x. Q x)           *)
(* ------------------------------------------------------------------------- *)

val RIGHT_EXISTS_AND_THM =
    let	val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val g = (--`Q:'a->bool`--)
	val Q = mk_comb(g,x)
	val t = mk_conj(P,Q)
	val exi = mk_exists(x,t)
	val (t1,t2) = CONJ_PAIR (ASSUME t)
	val t21 = EXISTS ((mk_exists(x,Q)),x) t2
	val imp1 =
	    DISCH_ALL
		(CHOOSE
		 (x, ASSUME (mk_exists(x,mk_conj(P,Q)))) (CONJ t1 t21))
	val th21 = EXISTS (exi,x) (CONJ (ASSUME P) (ASSUME Q))
	val th22 = CHOOSE(x,ASSUME(mk_exists(x,Q))) th21
	val (u1,u2) = CONJ_PAIR (ASSUME (mk_conj(P, mk_exists(x,Q))))
	val th23 = PROVE_HYP u1 (PROVE_HYP u2 th22)
	val imp2 = DISCH_ALL th23
    in
	GENL [P,g] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("RIGHT_EXISTS_AND_THM",RIGHT_EXISTS_AND_THM);


(* ------------------------------------------------------------------------- *)
(* BOTH_FORALL_OR_THM = |- !P Q. (!x. P \/ Q) = (!x. P) \/ (!x. Q)           *)
(* ------------------------------------------------------------------------- *)

val BOTH_FORALL_OR_THM =
  let val x = (--`x:'a`--)
      val P = (--`P:bool`--)
      val Q = (--`Q:bool`--)
      val imp11 = DISCH_ALL (SPEC x (ASSUME (mk_forall(x,P))))
      val imp12 = DISCH_ALL (GEN x (ASSUME P))
      val fath = IMP_ANTISYM_RULE imp11 imp12
      val th1 = REFL (mk_forall(x,mk_disj(P,Q)))
      val th2 = CONV_RULE (RAND_CONV
                 (K (INST [P |-> mk_disj(P,Q)] fath))) th1
      val th3 = CONV_RULE(RAND_CONV(RATOR_CONV(RAND_CONV(K(SYM fath))))) th2
      val th4 = CONV_RULE(RAND_CONV(RAND_CONV(K(SYM(INST[P|->Q] fath))))) th3
  in
    GENL [P,Q] th4
  end;

val _ = save_thm("BOTH_FORALL_OR_THM",BOTH_FORALL_OR_THM);

(* ------------------------------------------------------------------------- *)
(* LEFT_FORALL_OR_THM = |- !P Q. (!x. P x \/ Q) = (!x. P x) \/ Q             *)
(* ------------------------------------------------------------------------- *)

val LEFT_FORALL_OR_THM =
  let val x = (--`x:'a`--)
      val f = (--`P:'a->bool`--)
      val P = mk_comb(f,x)
      val Q = (--`Q:bool`--)
      val tm = mk_forall(x,mk_disj(P,Q))
      val thm1 = SPEC x (ASSUME tm)
      val thm2 = CONTR P (MP (ASSUME (mk_neg Q)) (ASSUME Q))
      val thm3 = DISJ1 (GEN x (DISJ_CASES thm1 (ASSUME P) thm2)) Q
      val thm4 = DISJ2 (mk_forall(x,P)) (ASSUME Q)
      val imp1 = DISCH tm (DISJ_CASES (SPEC Q EXCLUDED_MIDDLE) thm4 thm3)
      val thm5 = SPEC x (ASSUME (mk_forall(x,P)))
      val thm6 = ASSUME Q
      val imp2 = DISCH_ALL (GEN x (DISJ_CASES_UNION
                  (ASSUME(mk_disj(mk_forall(x,P), Q))) thm5 thm6))
  in
      GENL [Q,f] (IMP_ANTISYM_RULE imp1 imp2)
  end;

val _ = save_thm("LEFT_FORALL_OR_THM",LEFT_FORALL_OR_THM);

(* ------------------------------------------------------------------------- *)
(* RIGHT_FORALL_OR_THM = |- !P Q. (!x. P \/ Q x) = P \/ (!x. Q x)            *)
(* ------------------------------------------------------------------------- *)

val RIGHT_FORALL_OR_THM =
    let	val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val g = (--`Q:'a->bool`--)
	val Q = mk_comb(g,x)
	val tm   = mk_forall(x,mk_disj(P,Q))
	val thm1 = SPEC x (ASSUME tm)
	val thm2 = CONTR Q (MP (ASSUME (mk_neg P)) (ASSUME P))
	val thm3 = DISJ2 P (GEN x (DISJ_CASES thm1 thm2 (ASSUME Q)))
	val thm4 = DISJ1 (ASSUME P) (mk_forall(x,Q))
	val imp1 = DISCH tm (DISJ_CASES (SPEC P EXCLUDED_MIDDLE) thm4 thm3)
	val thm5 = ASSUME P
	val thm6 = SPEC x (ASSUME (mk_forall(x,Q)))
	val imp2 = DISCH_ALL (GEN x (DISJ_CASES_UNION
                   (ASSUME (mk_disj(P, mk_forall(x,Q))))
                   thm5 thm6))
    in
	    GENL [P,g] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("RIGHT_FORALL_OR_THM",RIGHT_FORALL_OR_THM);


(* ------------------------------------------------------------------------- *)
(* BOTH_FORALL_IMP_THM = |- (!x. P ==> Q) = ((?x.P) ==> (!x.Q))              *)
(* ------------------------------------------------------------------------- *)

val BOTH_FORALL_IMP_THM =
    let val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val Q = (--`Q:bool`--)
	val tm = mk_forall(x, mk_imp(P,Q))
	val asm = mk_exists(x,P)
	val th1 = GEN x (CHOOSE(x,ASSUME asm)(UNDISCH(SPEC x (ASSUME tm))))
	val imp1 = DISCH tm (DISCH asm th1)
	val cncl = rand(concl imp1)
	val th2 = SPEC x (MP (ASSUME cncl) (EXISTS (asm,x) (ASSUME P)))
	val imp2 = DISCH cncl (GEN x (DISCH P th2))
    in
	GENL [P,Q] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("BOTH_FORALL_IMP_THM",BOTH_FORALL_IMP_THM);


(* ------------------------------------------------------------------------- *)
(* LEFT_FORALL_IMP_THM = |- (!x. P[x]==>Q) = ((?x.P[x]) ==> Q)               *)
(* ------------------------------------------------------------------------- *)

val LEFT_FORALL_IMP_THM =
    let	val x = (--`x:'a`--)
	val f = (--`P:'a->bool`--)
	val P = mk_comb(f,x)
	val Q = (--`Q:bool`--)
	val tm = mk_forall(x, mk_imp(P,Q))
	val asm = mk_exists(x,P)
	val th1 = CHOOSE(x,ASSUME asm)(UNDISCH(SPEC x (ASSUME tm)))
	val imp1 = DISCH tm (DISCH asm th1)
	val cncl = rand(concl imp1)
	val th2 = MP (ASSUME cncl) (EXISTS (asm,x) (ASSUME P))
	val imp2 = DISCH cncl (GEN x (DISCH P th2))
    in
	GENL [f,Q] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("LEFT_FORALL_IMP_THM",LEFT_FORALL_IMP_THM);

(* ------------------------------------------------------------------------- *)
(* RIGHT_FORALL_IMP_THM = |- (!x. P==>Q[x]) = (P ==> (!x.Q[x]))              *)
(* ------------------------------------------------------------------------- *)

val RIGHT_FORALL_IMP_THM =
    let val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val g = (--`Q:'a->bool`--)
	val Q = mk_comb(g,x)
	val tm = mk_forall(x, mk_imp(P,Q))
	val imp1 = DISCH P(GEN x(UNDISCH(SPEC x(ASSUME tm))))
	val cncl = concl imp1
	val imp2 = GEN x (DISCH P(SPEC x(UNDISCH (ASSUME cncl))))
    in
	GENL [P,g] (IMP_ANTISYM_RULE (DISCH tm imp1) (DISCH cncl imp2))
    end;

val _ = save_thm("RIGHT_FORALL_IMP_THM",RIGHT_FORALL_IMP_THM);


(* ------------------------------------------------------------------------- *)
(* BOTH_EXISTS_IMP_THM = |- (?x. P ==> Q) = ((!x.P) ==> (?x.Q))              *)
(* ------------------------------------------------------------------------- *)

val BOTH_EXISTS_IMP_THM =
    let val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val Q = (--`Q:bool`--)
	val tm = mk_exists(x,mk_imp(P,Q))
	val eQ = mk_exists(x,Q)
	val aP = mk_forall(x,P)
	val thm1 = EXISTS(eQ,x)(UNDISCH(ASSUME(mk_imp(P,Q))))
	val thm2 = DISCH aP (PROVE_HYP (SPEC x (ASSUME aP)) thm1)
	val imp1 = DISCH tm (CHOOSE(x,ASSUME tm) thm2)
	val thm2 = CHOOSE(x,UNDISCH (ASSUME (rand(concl imp1)))) (ASSUME Q)
	val thm3 = DISCH P (PROVE_HYP (GEN x (ASSUME P)) thm2)
	val imp2 = DISCH (rand(concl imp1)) (EXISTS(tm,x) thm3)
    in
	GENL [P,Q] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("BOTH_EXISTS_IMP_THM",BOTH_EXISTS_IMP_THM);


(* ------------------------------------------------------------------------- *)
(* LEFT_EXISTS_IMP_THM = |- (?x. P[x] ==> Q) = ((!x.P[x]) ==> Q)             *)
(* ------------------------------------------------------------------------- *)

val LEFT_EXISTS_IMP_THM =
    let	val x = (--`x:'a`--)
	val f = (--`P:'a->bool`--)
	val P = mk_comb(f,x)
	val Q = (--`Q:bool`--)
	val tm = mk_exists(x, mk_imp(P,Q))
	val allp = mk_forall(x,P)
	val th1 = SPEC x (ASSUME allp)
	val thm1 = MP (ASSUME(mk_imp(P,Q))) th1
	val imp1 = DISCH tm (CHOOSE(x,ASSUME tm)(DISCH allp thm1))
	val otm = rand(concl imp1)
	val thm2 = EXISTS(tm,x)(DISCH P (UNDISCH(ASSUME otm)))
	val nex =  mk_exists(x,mk_neg P)
	val asm1 = EXISTS (nex, x) (ASSUME (mk_neg P))
	val th2 = CCONTR P (MP (ASSUME (mk_neg nex)) asm1)
	val th3 = CCONTR nex (MP (ASSUME (mk_neg allp)) (GEN x th2))
	val thm4 = DISCH P (CONTR Q (UNDISCH (ASSUME (mk_neg P))))
	val thm5 = CHOOSE(x,th3)(EXISTS(tm,x)thm4)
	val thm6 = DISJ_CASES (SPEC allp EXCLUDED_MIDDLE) thm2 thm5
	val imp2 = DISCH otm thm6
    in
	GENL [f, Q] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("LEFT_EXISTS_IMP_THM",LEFT_EXISTS_IMP_THM);


(* ------------------------------------------------------------------------- *)
(* RIGHT_EXISTS_IMP_THM = |- (?x. P ==> Q[x]) = (P ==> (?x.Q[x]))            *)
(* ------------------------------------------------------------------------- *)

val RIGHT_EXISTS_IMP_THM =
    let	val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val g = (--`Q:'a->bool`--)
	val Q = mk_comb(g,x)
	val tm = mk_exists(x,mk_imp(P,Q))
	val thm1 = EXISTS (mk_exists(x,Q),x)
	                   (UNDISCH(ASSUME(mk_imp(P,Q))))
	val imp1 = DISCH tm (CHOOSE(x,ASSUME tm) (DISCH P thm1))
	val thm2 = UNDISCH (ASSUME (rand(concl imp1)))
	val thm3 = CHOOSE (x,thm2) (EXISTS (tm,x) (DISCH P (ASSUME Q)))
	val thm4 = EXISTS(tm,x)(DISCH P(CONTR Q(UNDISCH(ASSUME(mk_neg P)))))
	val thm5 = DISJ_CASES (SPEC P EXCLUDED_MIDDLE) thm3 thm4
	val imp2 = DISCH(rand(concl imp1)) thm5
    in
	GENL [P,g] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("RIGHT_EXISTS_IMP_THM",RIGHT_EXISTS_IMP_THM);

(* --------------------------------------------------------------------- *)
(* OR_IMP_THM = |- !A B. (A = B \/ A) = (B ==> A)                        *)
(* [TFM 90.06.28]                                                        *)
(* --------------------------------------------------------------------- *)

val OR_IMP_THM =
 let val t1 = (--`A:bool`--) and t2 = (--`B:bool`--)
     val asm1 = ASSUME (--`^t1 = (^t2 \/ ^t1)`--)
     and asm2 = EQT_INTRO(ASSUME t2)
     val th1 = SUBST [t2 |-> asm2] (concl asm1) asm1
     val th2 = TRANS th1 (CONJUNCT1 (SPEC t1 OR_CLAUSES))
     val imp1 = DISCH (concl asm1) (DISCH t2 (EQT_ELIM th2))
     val asm3 = ASSUME (--`^t2 ==> ^t1`--)
     and asm4 = ASSUME (--`^t2 \/ ^t1`--)
     val th3 = DISJ_CASES asm4 (MP asm3 (ASSUME t2)) (ASSUME t1)
     val th4 = DISCH (concl asm4) th3
     and th5 = DISCH t1 (DISJ2 t2 (ASSUME t1))
     val imp2 = DISCH (--`^t2 ==> ^t1`--) (IMP_ANTISYM_RULE th5 th4)
  in
   GEN t1 (GEN t2 (IMP_ANTISYM_RULE imp1 imp2))
  end;

val _ = save_thm("OR_IMP_THM",OR_IMP_THM);

(* --------------------------------------------------------------------- *)
(* NOT_IMP = |- !A B. ~(A ==> B) = A /\ ~B                               *)
(* [TFM 90.07.09]                                                        *)
(* --------------------------------------------------------------------- *)

val NOT_IMP =
let val t1 = (--`A:bool`--) and t2 = (--`B:bool`--)
    val asm1 = ASSUME (--`~(^t1 ==> ^t2)`--)
    val thm1 = SUBST [t1 |-> EQF_INTRO (ASSUME (mk_neg t1))] (concl asm1) asm1
    val thm2 = CCONTR t1 (MP thm1 (DISCH(--`F`--)(CONTR t2 (ASSUME(--`F`--)))))
    val thm3 = SUBST [t2 |-> EQT_INTRO (ASSUME t2)] (concl asm1) asm1
    val thm4 = NOT_INTRO(DISCH t2 (MP thm3 (DISCH t1 (ADD_ASSUM t1 TRUTH))))
    val imp1 = DISCH (concl asm1) (CONJ thm2 thm4)
    val conj =  ASSUME (--`^t1 /\ ~^t2`--)
    val (asm2,asm3) = (CONJUNCT1 conj, CONJUNCT2 conj)
    val asm4 = ASSUME (--`^t1 ==> ^t2`--)
    val thm5 = MP (SUBST [t2 |-> EQF_INTRO asm3] (concl asm4) asm4) asm2
    val imp2 = DISCH (--`^t1 /\ ~ ^t2`--)
                     (NOT_INTRO(DISCH (--`^t1 ==> ^t2`--) thm5))
 in
    GEN t1 (GEN t2 (IMP_ANTISYM_RULE imp1 imp2))
 end;

val _ = save_thm("NOT_IMP", NOT_IMP);

(* --------------------------------------------------------------------- *)
(* DISJ_ASSOC: |- !A B C. A \/ B \/ C = (A \/ B) \/ C                    *)
(* --------------------------------------------------------------------- *)

val DISJ_ASSOC =
let val t1 = (--`A:bool`--) and t2 = (--`B:bool`--) and t3 = (--`C:bool`--)
    val at1 = DISJ1 (DISJ1 (ASSUME t1) t2) t3 and
        at2 = DISJ1 (DISJ2 t1 (ASSUME t2)) t3 and
        at3 = DISJ2 (mk_disj(t1,t2)) (ASSUME t3)
    val thm = DISJ_CASES (ASSUME (mk_disj(t2,t3))) at2 at3
    val thm1 = DISJ_CASES (ASSUME (mk_disj(t1,mk_disj(t2,t3)))) at1 thm
    val at1 = DISJ1 (ASSUME t1) (mk_disj(t2,t3)) and
        at2 = DISJ2 t1 (DISJ1 (ASSUME t2) t3) and
        at3 = DISJ2 t1 (DISJ2 t2 (ASSUME t3))
    val thm = DISJ_CASES (ASSUME (mk_disj(t1,t2))) at1 at2
    val thm2 = DISJ_CASES (ASSUME (mk_disj(mk_disj(t1,t2),t3))) thm at3
    val imp1 = DISCH (mk_disj(t1,mk_disj(t2,t3))) thm1 and
        imp2 = DISCH (mk_disj(mk_disj(t1,t2),t3)) thm2
 in
   GENL [t1,t2,t3] (IMP_ANTISYM_RULE imp1 imp2)
 end;

val _ = save_thm("DISJ_ASSOC", DISJ_ASSOC);

(* --------------------------------------------------------------------- *)
(* DISJ_SYM: |- !A B. A \/ B = B \/ A                   		 *)
(* --------------------------------------------------------------------- *)

val DISJ_SYM =
let val t1   = (--`A:bool`--) and t2 = (--`B:bool`--)
    val th1  = DISJ1 (ASSUME t1) t2 and th2 = DISJ2 t1 (ASSUME t2)
    val thm1 = DISJ_CASES (ASSUME(mk_disj(t2,t1))) th2 th1
    val th1  = DISJ1 (ASSUME t2) t1 and th2 = DISJ2 t2 (ASSUME t1)
    val thm2 = DISJ_CASES (ASSUME(mk_disj(t1,t2))) th2 th1
    val imp1 = DISCH (mk_disj(t2,t1)) thm1 and
        imp2 = DISCH (mk_disj(t1,t2)) thm2
 in
   GENL [t1,t2] (IMP_ANTISYM_RULE imp2 imp1)
 end;

val _ = save_thm("DISJ_SYM", DISJ_SYM);
val _ = save_thm("DISJ_COMM", DISJ_SYM);

(* --------------------------------------------------------------------- *)
(* DE_MORGAN_THM: 							 *)
(*  |- !A B. (~(t1 /\ t2) = ~t1 \/ ~t2) /\ (~(t1 \/ t2) = ~t1 /\ ~t2)    *)
(* --------------------------------------------------------------------- *)

val DE_MORGAN_THM =
let val t1 = (--`A:bool`--) and t2 = (--`B:bool`--)
    val thm1 =
      let val asm1 = ASSUME (--`~(^t1 /\ ^t2)`--)
          val cnj = MP asm1 (CONJ (ASSUME t1) (ASSUME t2))
          val imp1 =
            let val case1 = DISJ2 (--`~^t1`--) (NOT_INTRO(DISCH t2 cnj))
                val case2 = DISJ1 (ASSUME (--`~ ^t1`--)) (--`~ ^t2`--)
            in DISJ_CASES (SPEC t1 EXCLUDED_MIDDLE) case1 case2
            end
          val th1 = MP (ASSUME (--`~^t1`--))
                       (CONJUNCT1 (ASSUME (--`^t1 /\ ^t2`--)))
          val th2 = MP (ASSUME (--`~^t2`--))
                   (CONJUNCT2 (ASSUME (--`^t1 /\ ^t2`--)))
          val imp2 =
            let val fth = DISJ_CASES (ASSUME (--`~^t1 \/ ~^t2`--)) th1 th2
            in DISCH (--`~^t1 \/ ~^t2`--)
                     (NOT_INTRO(DISCH (--`^t1 /\ ^t2`--) fth))
            end
      in
        IMP_ANTISYM_RULE (DISCH (--`~(^t1 /\ ^t2)`--) imp1) imp2
      end
    val thm2 =
      let val asm1 = ASSUME (--`~(^t1 \/ ^t2)`--)
          val imp1 =
            let val th1 = NOT_INTRO (DISCH t1(MP asm1 (DISJ1 (ASSUME t1) t2)))
                val th2 = NOT_INTRO (DISCH t2 (MP asm1 (DISJ2 t1 (ASSUME t2))))
            in DISCH (--`~(^t1 \/ ^t2)`--) (CONJ th1 th2)
            end
          val imp2 =
            let val asm = ASSUME (--`^t1 \/ ^t2`--)
                val a1 = CONJUNCT1(ASSUME (--`~^t1 /\ ~^t2`--)) and
                    a2 = CONJUNCT2(ASSUME (--`~^t1 /\ ~^t2`--))
               val fth = DISJ_CASES asm (UNDISCH a1) (UNDISCH a2)
            in DISCH (--`~^t1 /\ ~^t2`--)
                    (NOT_INTRO(DISCH (--`^t1 \/ ^t2`--) fth))
            end
      in IMP_ANTISYM_RULE imp1 imp2
      end
 in GEN t1 (GEN t2 (CONJ thm1 thm2))
 end;

val _ = save_thm("DE_MORGAN_THM", DE_MORGAN_THM);

(* -------------------------------------------------------------------------*)
(* Distributive laws:							    *)
(*									    *)
(* LEFT_AND_OVER_OR   |- !A B C. A /\ (B \/ C) = A /\ B \/ A /\ C           *)
(*									    *)
(* RIGHT_AND_OVER_OR  |- !A B C. (B \/ C) /\ A = B /\ A \/ C /\ A           *)
(*									    *)
(* LEFT_OR_OVER_AND   |- !A B C. A \/ B /\ C = (A \/ B) /\ (A \/ C)         *)
(*									    *)
(* RIGHT_OR_OVER_AND  |- !A B C. B /\ C \/ A = (B \/ A) /\ (C \/ A)         *)
(* -------------------------------------------------------------------------*)

val LEFT_AND_OVER_OR =
    let val t1 = --`A:bool`--
        and t2 = --`B:bool`--
        and t3 = --`C:bool`--
        val (th1,th2) = CONJ_PAIR(ASSUME (mk_conj(t1,mk_disj(t2,t3))))
        val th3 = CONJ th1 (ASSUME t2) and th4 = CONJ th1 (ASSUME t3)
        val th5 = DISJ_CASES_UNION th2 th3 th4
        val imp1 = DISCH (mk_conj(t1,mk_disj(t2,t3))) th5
        val (th1,th2) = (I ## C DISJ1 t3) (CONJ_PAIR (ASSUME (mk_conj(t1,t2))))
        val (th3,th4) = (I ## DISJ2 t2) (CONJ_PAIR (ASSUME (mk_conj(t1,t3))))
        val th5 = CONJ th1 th2 and th6 = CONJ th3 th4
        val th6 = DISJ_CASES (ASSUME (rand(concl imp1))) th5 th6
        val imp2 = DISCH (rand(concl imp1)) th6
    in
      GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)))
    end;

val _ = save_thm("LEFT_AND_OVER_OR", LEFT_AND_OVER_OR);

val RIGHT_AND_OVER_OR =
   let val t1 = --`A:bool`--
       and t2 = --`B:bool`--
       and t3 = --`C:bool`--
       val (th1,th2) = CONJ_PAIR(ASSUME (mk_conj(mk_disj(t2,t3),t1)))
       val th3 = CONJ (ASSUME t2) th2 and th4 = CONJ (ASSUME t3) th2
       val th5 = DISJ_CASES_UNION th1 th3 th4
       val imp1 = DISCH (mk_conj(mk_disj(t2,t3),t1)) th5
       val (th1,th2) = (C DISJ1 t3 ## I) (CONJ_PAIR (ASSUME (mk_conj(t2,t1))))
       val (th3,th4) = (DISJ2 t2 ## I) (CONJ_PAIR (ASSUME (mk_conj(t3,t1))))
       val th5 = CONJ th1 th2 and th6 = CONJ th3 th4
       val th6 = DISJ_CASES (ASSUME (rand(concl imp1))) th5 th6
       val imp2 = DISCH (rand(concl imp1)) th6
   in
     GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)))
   end;

val _ = save_thm("RIGHT_AND_OVER_OR", RIGHT_AND_OVER_OR);

val LEFT_OR_OVER_AND =
   let val t1 = --`A:bool`--
       and t2 = --`B:bool`--
       and t3 = --`C:bool`--
       val th1 = ASSUME (mk_disj(t1,mk_conj(t2,t3)))
       val th2 = CONJ (DISJ1 (ASSUME t1) t2) (DISJ1 (ASSUME t1) t3)
       val (th3,th4) = CONJ_PAIR (ASSUME(mk_conj(t2,t3)))
       val th5 = CONJ (DISJ2 t1 th3) (DISJ2 t1 th4)
       val imp1 = DISCH (concl th1) (DISJ_CASES th1 th2 th5)
       val (th1,th2) = CONJ_PAIR (ASSUME (rand(concl imp1)))
       val th3 = DISJ1 (ASSUME t1) (mk_conj(t2,t3))
       val (th4,th5) = CONJ_PAIR (ASSUME (mk_conj(t2,t3)))
       val th4 = DISJ2 t1 (CONJ (ASSUME t2) (ASSUME t3))
       val th5 = DISJ_CASES th2 th3 (DISJ_CASES th1 th3 th4)
       val imp2 = DISCH (rand(concl imp1)) th5
   in
     GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)))
   end;

val _ = save_thm("LEFT_OR_OVER_AND", LEFT_OR_OVER_AND);

val RIGHT_OR_OVER_AND =
   let val t1 = --`A:bool`--
       and t2 = --`B:bool`--
       and t3 = --`C:bool`--
       val th1 = ASSUME (mk_disj(mk_conj(t2,t3),t1))
       val th2 = CONJ (DISJ2 t2 (ASSUME t1)) (DISJ2 t3 (ASSUME t1))
       val (th3,th4) = CONJ_PAIR (ASSUME(mk_conj(t2,t3)))
       val th5 = CONJ (DISJ1 th3 t1) (DISJ1 th4 t1)
       val imp1 = DISCH (concl th1) (DISJ_CASES th1 th5 th2)
       val (th1,th2) = CONJ_PAIR (ASSUME (rand(concl imp1)))
       val th3 = DISJ2 (mk_conj(t2,t3)) (ASSUME t1)
       val (th4,th5) = CONJ_PAIR (ASSUME (mk_conj(t2,t3)))
       val th4 = DISJ1 (CONJ (ASSUME t2) (ASSUME t3)) t1
       val th5 = DISJ_CASES th2 (DISJ_CASES th1 th4 th3) th3
       val imp2 = DISCH (rand(concl imp1)) th5
   in
     GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)))
   end;

val _ = save_thm("RIGHT_OR_OVER_AND", RIGHT_OR_OVER_AND);


(*---------------------------------------------------------------------------*
 * IMP_DISJ_THM = |- !A B. A ==> B = ~A \/ B                                 *
 *---------------------------------------------------------------------------*)

val IMP_DISJ_THM =
let val A = --`A:bool`--
    val B = --`B:bool`--
    val th1 = ASSUME (Term`A ==> B`)
    val th2 = ASSUME A
    val th3 = MP th1 th2
    val th4 = DISJ2 (Term`~A`) th3
    val th5 = ASSUME (Term`~A`);
    val th6 = ADD_ASSUM (Term`A ==> B`) th5
    val th7 = DISJ1 th6 B
    val th8 = SPEC A EXCLUDED_MIDDLE
    val th9 = DISJ_CASES th8 th4 th7

    val th10 = EQT_INTRO th2
    val th11 = ASSUME (Term`~A \/ B`)
    val th12 = SUBST [A |-> th10] (concl th11) th11
    val th13 = CONJUNCT1 (CONJUNCT2 NOT_CLAUSES)
    val th14 = SUBST [A |-> th13] (subst [Term`~T` |-> A] (concl th12)) th12
    val th15 = CONJUNCT1 (CONJUNCT2(CONJUNCT2 (SPEC B OR_CLAUSES)))
    val th16 = SUBST [A |-> th15] A th14
    val th17 = DISCH A th16
    val th18 = DISCH (concl th11) th17
 in
   GENL [A,B] (IMP_ANTISYM_RULE (DISCH (hd(hyp th9)) th9) th18)
 end;

val _ = save_thm ("IMP_DISJ_THM", IMP_DISJ_THM);

(*----------------------------------------------------------------------*)
(* DISJ_IMP_THM = |- !P Q R. P \/ Q ==> R = (P ==> R) /\ (Q ==> R)      *)
(*                                                         MN 99.05.06  *)
(*----------------------------------------------------------------------*)

val DISJ_IMP_THM = let
  val P = --`P:bool`--
  val Q = --`Q:bool`--
  val R = --`R:bool`--
  val lhs = --`P \/ Q ==> R`--
  val rhs = --`(P ==> R) /\ (Q ==> R)`--
  val ass_lhs = ASSUME lhs
  val ass_P = ASSUME P
  val ass_Q = ASSUME Q
  val p_imp_r = DISCH P (MP ass_lhs (DISJ1 ass_P Q))
  val q_imp_r = DISCH Q (MP ass_lhs (DISJ2 P ass_Q))
  val lr_imp = DISCH lhs (CONJ p_imp_r q_imp_r)
  (* half way there! *)
  val ass_rhs = ASSUME rhs
  val porq = (--`P \/ Q`--)
  val ass_porq = ASSUME porq
  val my_and1 = SPECL [(--`P ==> R`--), (--`Q ==> R`--)] AND1_THM
  val p_imp_r = MP my_and1 ass_rhs
  val r_from_p = MP p_imp_r ass_P
  val my_and2 = SPECL [(--`P ==> R`--), (--`Q ==> R`--)] AND2_THM
  val q_imp_r = MP my_and2 ass_rhs
  val r_from_q = MP q_imp_r ass_Q
  val rl_imp = DISCH rhs (DISCH porq (DISJ_CASES ass_porq r_from_p r_from_q))
in
  save_thm("DISJ_IMP_THM", GENL [P,Q,R] (IMP_ANTISYM_RULE lr_imp rl_imp))
end

(* ----------------------------------------------------------------------
    IMP_CONJ_THM = |- !P Q R. P ==> Q /\ R = (P ==> Q) /\ (P ==> R)
                                                          MN 2002.10.06
   ---------------------------------------------------------------------- *)

val IMP_CONJ_THM = let
  val P = mk_var("P", bool)
  val Q = mk_var("Q", bool)
  val R = mk_var("R", bool)
  val QandR = mk_conj(Q,R)
  val PimpQandR = mk_imp(P, QandR)
  val PiQaR_th = ASSUME PimpQandR
  val P_th = ASSUME P
  val QaR_th = MP PiQaR_th P_th
  val (Q_th, R_th) = CONJ_PAIR QaR_th
  val PQ_th = DISCH P Q_th
  val PR_th = DISCH P R_th
  val L2R = DISCH PimpQandR (CONJ PQ_th PR_th)
  val PiQ = mk_imp(P, Q)
  val PiR = mk_imp(P, R)
  val PiQaPiR = mk_conj(PiQ, PiR)
  val PiQaPiR_th = ASSUME PiQaPiR
  val (PiQ_th, PiR_th) = CONJ_PAIR PiQaPiR_th
  val Q_th = MP PiQ_th P_th
  val R_th = MP PiR_th P_th
  val QaR_th = CONJ Q_th R_th
  val R2L = DISCH PiQaPiR (DISCH P QaR_th)
in
  save_thm("IMP_CONJ_THM", GENL [P,Q,R] (IMP_ANTISYM_RULE L2R R2L))
end

(* ---------------------------------------------------------------------*)
(* IMP_F_EQ_F                                                           *)
(*                                                                      *)
(* |- !t. t ==> F = (t = F)					        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)
local fun nthCONJUNCT n cth =
        let val th = funpow (n-1) CONJUNCT2 cth
        in if (can dest_conj (concl th))
           then CONJUNCT1 th else th
        end
in
val IMP_F_EQ_F =
   GEN (--`t:bool`--)
     (TRANS (nthCONJUNCT 5 (SPEC_ALL IMP_CLAUSES))
            (SYM (nthCONJUNCT 4 (SPEC_ALL EQ_CLAUSES))))
end;

val _ = save_thm("IMP_F_EQ_F", IMP_F_EQ_F);

(* ---------------------------------------------------------------------*)
(* AND_IMP_INTRO							*)
(*								        *)
(* |- !t1 t2 t3. t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3		        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

val AND_IMP_INTRO =
let val t1 = --`t1:bool`--
    and t2 = --`t2:bool`--
    and t3 = --`t3:bool`--
    and imp = --`$==>`--
    val [IMP1,IMP2,IMP3,_,IMP4] = map GEN_ALL(CONJUNCTS (SPEC_ALL IMP_CLAUSES))
    and [AND1,AND2,AND3,AND4,_] = map GEN_ALL(CONJUNCTS (SPEC_ALL AND_CLAUSES))
    val thTl = SPEC (--`t2 ==> t3`--) IMP1
    and thFl = SPEC (--`t2 ==> t3`--) IMP3
    val thTr = AP_THM (AP_TERM imp (SPEC t2 AND1)) t3
    and thFr = TRANS (AP_THM (AP_TERM imp (SPEC t2 AND3)) t3)(SPEC t3 IMP3)
    val thT1 = TRANS thTl (SYM thTr)
    and thF1 = TRANS thFl (SYM thFr)
    val tm   = Term`t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3`
    val thT2 = SUBST_CONV [t1 |-> ASSUME (--`t1 = T`--)] tm tm
    and thF2 = SUBST_CONV [t1 |-> ASSUME (--`t1 = F`--)] tm tm
    val thT3 = EQ_MP (SYM thT2) thT1
    and thF3 = EQ_MP (SYM thF2) thF1
 in
   GENL [t1,t2,t3] (DISJ_CASES (SPEC t1 BOOL_CASES_AX) thT3 thF3)
 end;

val _ = save_thm("AND_IMP_INTRO", AND_IMP_INTRO);

(* ---------------------------------------------------------------------*)
(* EQ_IMP_THM							        *)
(*								        *)
(* |- !t1 t2. (t1 = t2) = (t1 ==> t2) /\ (t2 ==> t1)		        *)
(*								        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

val EQ_IMP_THM =
let val t1 = --`t1:bool`--
    and t2 = --`t2:bool`--
    val conj = --`$/\`--
    val [IMP1,IMP2,IMP3,_,IMP4] = map GEN_ALL(CONJUNCTS (SPEC_ALL IMP_CLAUSES))
    and [AND1,AND2,AND3,AND4,_] = map GEN_ALL(CONJUNCTS (SPEC_ALL AND_CLAUSES))
    and [EQ1,EQ2,EQ3,EQ4] = map GEN_ALL (CONJUNCTS (SPEC_ALL EQ_CLAUSES))
    val thTl = SPEC t2 EQ1
    and thFl = SPEC t2 EQ3
    val thTr = TRANS (MK_COMB (AP_TERM conj (SPEC t2 IMP1), SPEC t2 IMP2))
                     (SPEC t2 AND2)
    and thFr = TRANS (MK_COMB (AP_TERM conj (SPEC t2 IMP3), SPEC t2 IMP4))
                     (SPEC (mk_neg t2) AND1)
    val thT1 = TRANS thTl (SYM thTr)
    and thF1 = TRANS thFl (SYM thFr)
    val tm = (--`(t1 = t2) = (t1 ==> t2) /\ (t2 ==> t1)`--)
    val thT2 = SUBST_CONV [t1 |-> ASSUME (--`t1 = T`--)] tm tm
    and thF2 = SUBST_CONV [t1 |-> ASSUME (--`t1 = F`--)] tm tm
    val thT3 = EQ_MP (SYM thT2) thT1
    and thF3 = EQ_MP (SYM thF2) thF1
 in
   GENL [t1,t2] (DISJ_CASES (SPEC t1 BOOL_CASES_AX) thT3 thF3)
 end;

val _ = save_thm("EQ_IMP_THM", EQ_IMP_THM);

(* ---------------------------------------------------------------------*)
(* EQ_EXPAND = |- !t1 t2. (t1 = t2) = ((t1 /\ t2) \/ (~t1 /\ ~t2))      *)
(*                                                         RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

val EQ_EXPAND =
let val t1 = --`t1:bool`-- and t2 = --`t2:bool`--
    val conj = --`$/\`--   and disj = --`$\/`--
    val [NOT1,NOT2] = tl (CONJUNCTS NOT_CLAUSES)
    and [EQ1,EQ2,EQ3,EQ4] = map GEN_ALL (CONJUNCTS (SPEC_ALL EQ_CLAUSES))
    and [OR1,OR2,OR3,OR4,_] = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
    and [AND1,AND2,AND3,AND4,_] = map GEN_ALL (CONJUNCTS(SPEC_ALL AND_CLAUSES))
    val thTl = SPEC t2 EQ1
    and thFl = SPEC t2 EQ3
    val thTr = TRANS (MK_COMB (AP_TERM disj (SPEC t2 AND1),
                               TRANS (AP_THM (AP_TERM conj NOT1) (mk_neg t2))
                                     (SPEC (mk_neg t2) AND3)))
                     (SPEC t2 OR4)
    and thFr = TRANS (MK_COMB (AP_TERM disj (SPEC t2 AND3),
                               TRANS (AP_THM (AP_TERM conj NOT2) (mk_neg t2))
                                     (SPEC (mk_neg t2) AND1)))
                     (SPEC (mk_neg t2) OR3)
    val thT1 = TRANS thTl (SYM thTr)
    and thF1 = TRANS thFl (SYM thFr)
    val tm = (--`(t1 = t2) = ((t1 /\ t2) \/ (~t1 /\ ~t2))`--)
    val thT2 = SUBST_CONV [t1 |-> ASSUME (--`t1 = T`--)] tm tm
    and thF2 = SUBST_CONV [t1 |-> ASSUME (--`t1 = F`--)] tm tm
    val thT3 = EQ_MP (SYM thT2) thT1
    and thF3 = EQ_MP (SYM thF2) thF1
 in
   GENL [t1,t2] (DISJ_CASES (SPEC t1 BOOL_CASES_AX) thT3 thF3)
 end;

val _ = save_thm("EQ_EXPAND", EQ_EXPAND);

(* ---------------------------------------------------------------------*)
(* COND_RATOR |- !b (f:'a->'b) g x. (b => f | g) x = (b => f x | g x)   *)
(*								        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

val COND_RATOR =
let val f = --`f: 'a -> 'b`--
    val g = --`g: 'a -> 'b`--
    val x = --`x:'a`--
    and b = --`b:bool`--
    val fx = --`^f ^x`-- and gx = --`^g ^x`--
    val t1 = --`t1:'a`--
    val t2 = --`t2:'a`--
    val theta1 = [Type`:'a` |-> Type`:'a -> 'b`]
    val theta2 = [Type`:'a` |-> Type`:'b`]
    val (COND_T,COND_F) = (GENL[t1,t2]##GENL[t1,t2])
                          (CONJ_PAIR(SPEC_ALL COND_CLAUSES))
    val thTl = AP_THM (SPECL [f,g] (INST_TYPE theta1 COND_T)) x
    and thFl = AP_THM (SPECL [f,g] (INST_TYPE theta1 COND_F)) x
    val thTr = SPECL [fx,gx] (INST_TYPE theta2 COND_T)
    and thFr = SPECL [fx,gx] (INST_TYPE theta2 COND_F)
    val thT1 = TRANS thTl (SYM thTr)
    and thF1 = TRANS thFl (SYM thFr)
    val tm = (--`(if b then (f:'a->'b ) else g) x = (if b then f x else g x)`--)
    val thT2 = SUBST_CONV [b |-> ASSUME (--`b = T`--)] tm tm
    and thF2 = SUBST_CONV [b |-> ASSUME (--`b = F`--)] tm tm
    val thT3 = EQ_MP (SYM thT2) thT1
    and thF3 = EQ_MP (SYM thF2) thF1
 in
    GENL [b,f,g,x] (DISJ_CASES (SPEC b BOOL_CASES_AX) thT3 thF3)
 end;

val _ = save_thm("COND_RATOR", COND_RATOR);

(* ---------------------------------------------------------------------*)
(* COND_RAND							        *)
(*								        *)
(* |- !(f:'a->'b) b x y. f (b => x | y) = (b => f x | f y)	        *)
(*								        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

val COND_RAND =
let val f = --`f: 'a -> 'b`--
    val x = --`x:'a`--
    val y = --`y:'a`--
    and b = --`b:bool`--
    val fx = --`^f ^x`-- and fy = --`^f ^y`--
    val t1 = --`t1:'a`--
    val t2 = --`t2:'a`--
    val theta = [Type.alpha |-> Type.beta]
    val (COND_T,COND_F) = (GENL[t1,t2]##GENL[t1,t2])
                          (CONJ_PAIR (SPEC_ALL COND_CLAUSES))
    val thTl = AP_TERM f (SPECL [x,y] COND_T)
    and thFl = AP_TERM f (SPECL [x,y] COND_F)
    val thTr = SPECL [fx,fy] (INST_TYPE theta COND_T)
    and thFr = SPECL [fx,fy] (INST_TYPE theta COND_F)
    val thT1 = TRANS thTl (SYM thTr)
    and thF1 = TRANS thFl (SYM thFr)
    val tm = (--`(f:'a->'b ) (if b then x else y) = (if b then f x else f y)`--)
    val thT2 = SUBST_CONV [b |-> ASSUME (--`b = T`--)] tm tm
    and thF2 = SUBST_CONV [b |-> ASSUME (--`b = F`--)] tm tm
    val thT3 = EQ_MP (SYM thT2) thT1
    and thF3 = EQ_MP (SYM thF2) thF1
 in
   GENL [f,b,x,y] (DISJ_CASES (SPEC b BOOL_CASES_AX) thT3 thF3)
 end;

val _ = save_thm("COND_RAND", COND_RAND);

(* ---------------------------------------------------------------------*)
(* COND_ABS							        *)
(*								        *)
(* |- !b (f:'a->'b) g. (\x. (b => f(x) | g(x))) = (b => f | g)	        *)
(*								        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

val COND_ABS =
let val b = --`b:bool`--
    val f = --`f:'a->'b`--
    val g = --`g:'a->'b`--
    val x = --`x:'a`--
 in
   GENL [b,f,g]
      (TRANS (ABS x (SYM (SPECL [b,f,g,x] COND_RATOR)))
             (ETA_CONV (--`\ ^x. (if ^b then ^f else ^g) ^x`--)))
 end;

val _ = save_thm("COND_ABS", COND_ABS);

(* ---------------------------------------------------------------------*)
(* COND_EXPAND							        *)
(*								        *)
(* |- !b t1 t2. (b => t1 | t2) = ((~b \/ t1) /\ (b \/ t2))	        *)
(*								        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

val COND_EXPAND =
let val b    = --`b:bool`--
    val t1   = --`t1:bool`--
    val t2   = --`t2:bool`--
    val conj = --`$/\`--
    val disj = --`$\/`--
    val theta = [Type`:'a` |-> Type.bool]
    val (COND_T,COND_F) =
      let val t1 = --`t1:'a`--  and  t2 = --`t2:'a`--
      in (GENL[t1,t2]##GENL[t1,t2]) (CONJ_PAIR(SPEC_ALL COND_CLAUSES))
      end
    and [NOT1,NOT2] = tl (CONJUNCTS NOT_CLAUSES)
    and [OR1,OR2,OR3,OR4,_] = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
    and [AND1,AND2,AND3,AND4,_] = map GEN_ALL (CONJUNCTS(SPEC_ALL AND_CLAUSES))
    val thTl = SPECL [t1,t2] (INST_TYPE theta COND_T)
    and thFl = SPECL [t1,t2] (INST_TYPE theta COND_F)
    val thTr =
      let val th1 = TRANS (AP_THM (AP_TERM disj NOT1) t1) (SPEC t1 OR3)
          and th2 = SPEC t2 OR1
      in
         TRANS (MK_COMB (AP_TERM conj th1,th2)) (SPEC t1 AND2)
      end
    and thFr =
      let val th1 = TRANS (AP_THM (AP_TERM disj NOT2) t1) (SPEC t1 OR1)
          and th2 = SPEC t2 OR3
      in
        TRANS (MK_COMB (AP_TERM conj th1,th2)) (SPEC t2 AND1)
      end
    val thT1 = TRANS thTl (SYM thTr)
    and thF1 = TRANS thFl (SYM thFr)
    val tm = (--`(if b then t1 else t2) = ((~b \/ t1) /\ (b \/ t2))`--)
    val thT2 = SUBST_CONV [b |-> ASSUME (--`b = T`--)] tm tm
    and thF2 = SUBST_CONV [b |-> ASSUME (--`b = F`--)] tm tm
    val thT3 = EQ_MP (SYM thT2) thT1
    and thF3 = EQ_MP (SYM thF2) thF1
 in
   GENL [b, t1, t2] (DISJ_CASES (SPEC b BOOL_CASES_AX) thT3 thF3)
 end;

val _ = save_thm("COND_EXPAND", COND_EXPAND);

(* ---------------------------------------------------------------------*)
(* COND_EXPAND_IMP						        *)
(*								        *)
(* |- !b t1 t2. (b => t1 | t2) = ((b ==> t1) /\ (~b ==> t2))	        *)
(*								        *)
(*				       	                    TT 09.03.18 *)
(* ---------------------------------------------------------------------*)

val COND_EXPAND_IMP =
let val b    = --`b:bool`--
    val t1   = --`t1:bool`--
    val t2   = --`t2:bool`--
    val nb   = mk_neg b;
    val nnb  = mk_neg nb;


    val imp_th1  = SPECL [b, t1] IMP_DISJ_THM;
    val imp_th2a = SPECL [nb, t2] IMP_DISJ_THM
    val imp_th2b = SUBST_CONV [nnb |-> (SPEC b (CONJUNCT1 NOT_CLAUSES))]
		   (mk_disj (nnb, t2)) (mk_disj (nnb, t2))
    val imp_th2  = TRANS imp_th2a imp_th2b


    val new_rhs = ``(b ==> t1) /\ (~b ==> t2)``;
    val subst = [mk_imp(b,t1) |-> imp_th1,
                 mk_imp(nb,t2) |-> imp_th2]

    val th1 = SUBST_CONV subst new_rhs new_rhs
    val th2 = TRANS (SPECL [b,t1,t2] COND_EXPAND) (SYM th1)
in
    GENL [b,t1,t2] th2
end;

val _ = save_thm("COND_EXPAND_IMP", COND_EXPAND_IMP);



(* ---------------------------------------------------------------------*)
(* COND_EXPAND_OR 						        *)
(*								        *)
(* |- !b t1 t2. (b => t1 | t2) = ((b /\ t1) \/ (~b /\ t2))	        *)
(*								        *)
(*				       	                    TT 09.03.18 *)
(* ---------------------------------------------------------------------*)


val COND_EXPAND_OR =
let val b    = --`b:bool`--
    val t1   = --`t1:bool`--
    val t2   = --`t2:bool`--
    val conj = --`$/\`--
    val disj = --`$\/`--
    val theta = [Type`:'a` |-> Type.bool]
    val (COND_T,COND_F) =
      let val t1 = --`t1:'a`--  and  t2 = --`t2:'a`--
      in (GENL[t1,t2]##GENL[t1,t2]) (CONJ_PAIR(SPEC_ALL COND_CLAUSES))
      end
    and [NOT1,NOT2] = tl (CONJUNCTS NOT_CLAUSES)
    and [OR1,OR2,OR3,OR4,_] = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
    and [AND1,AND2,AND3,AND4,_] = map GEN_ALL (CONJUNCTS(SPEC_ALL AND_CLAUSES))
    val thTl = SPECL [t1,t2] (INST_TYPE theta COND_T)
    and thFl = SPECL [t1,t2] (INST_TYPE theta COND_F)
    val thTr =
      let val th2 = TRANS (AP_THM (AP_TERM conj NOT1) t2) (SPEC t2 AND3)
          and th1 = SPEC t1 AND1
      in
         TRANS (MK_COMB (AP_TERM disj th1,th2)) (SPEC t1 OR4)
      end
    and thFr =
      let val th2 = TRANS (AP_THM (AP_TERM conj NOT2) t2) (SPEC t2 AND1)
          and th1 = SPEC t1 AND3
      in
        TRANS (MK_COMB (AP_TERM disj th1,th2)) (SPEC t2 OR3)
      end
    val thT1 = TRANS thTl (SYM thTr)
    and thF1 = TRANS thFl (SYM thFr)
    val tm = (--`(if b then t1 else t2) = ((b /\ t1) \/ (~b /\ t2))`--)
    val thT2 = SUBST_CONV [b |-> ASSUME (--`b = T`--)] tm tm
    and thF2 = SUBST_CONV [b |-> ASSUME (--`b = F`--)] tm tm
    val thT3 = EQ_MP (SYM thT2) thT1
    and thF3 = EQ_MP (SYM thF2) thF1
 in
   GENL [b, t1, t2] (DISJ_CASES (SPEC b BOOL_CASES_AX) thT3 thF3)
 end;

val _ = save_thm("COND_EXPAND_OR", COND_EXPAND_OR);





val TYPE_DEFINITION_THM =
  let val P   = Term `P:'a-> bool`
      val rep = Term `rep :'b -> 'a`
  in
    GEN P (GEN rep
      (RIGHT_BETA(AP_THM
          (RIGHT_BETA (AP_THM TYPE_DEFINITION P)) rep)))
  end;

val _ = save_thm("TYPE_DEFINITION_THM", TYPE_DEFINITION_THM);

val ONTO_THM = save_thm(
  "ONTO_THM",
  let val f = mk_var("f", Type.alpha --> Type.beta)
  in
      GEN f (RIGHT_BETA (AP_THM ONTO_DEF f))
  end);

val ONE_ONE_THM = save_thm(
  "ONE_ONE_THM",
  let val f = mk_var("f", Type.alpha --> Type.beta)
  in
      GEN f (RIGHT_BETA (AP_THM ONE_ONE_DEF f))
  end);


(*---------------------------------------------------------------------------*
 * ABS_REP_THM                                                               *
 *  |- !P. (?rep. TYPE_DEFINITION P rep) ==>                                 *
 *         ?rep abs. (!a. abs (rep a) = a) /\ !r. P r = (rep (abs r) = r)    *
 *---------------------------------------------------------------------------*)

val ABS_REP_THM =
   let val th1 = ASSUME (--`?rep:'b->'a. TYPE_DEFINITION P rep`--)
       val th2 = MK_EXISTS (SPEC (--`P:'a->bool`--) TYPE_DEFINITION_THM)
       val def = EQ_MP th2 th1
       val asm = ASSUME (snd(dest_exists(concl def)))
       val (asm1,asm2)  = CONJ_PAIR asm
       val rep_eq =
         let val th1 = DISCH (--`a:'b=a'`--)
                         (AP_TERM (--`rep:'b->'a`--) (ASSUME (--`a:'b=a'`--)))
         in IMP_ANTISYM_RULE (SPECL [(--`a:'b`--),(--`a':'b`--)] asm1) th1
         end
       val ABS = (--`\r:'a. @a:'b. r = rep a`--)
       val absd =  RIGHT_BETA (AP_THM (REFL ABS) (--`rep (a:'b):'a`--))
       val lem = SYM(SELECT_RULE(EXISTS ((--`?a':'b.a=a'`--),(--`a:'b`--))
                                        (REFL (--`a:'b`--))))
       val TH1 = GEN (--`a:'b`--)
                     (TRANS(TRANS absd (SELECT_EQ (--`a':'b`--) rep_eq)) lem)
       val t1 = SELECT_RULE(EQ_MP (SPEC (--`r:'a`--) asm2)
                                  (ASSUME (--`(P:'a->bool) r`--)))
       val absd2 =  RIGHT_BETA (AP_THM (REFL ABS) (--`r:'a`--))
       val v = mk_var("v",type_of(rhs (concl absd2)))
       val (t1l,t1r) = dest_eq (concl t1)
       (* val rep = fst(strip_comb t1r) *)
       val rep = rator t1r
       val template = mk_eq(t1l, mk_comb(rep,v))
       val imp1 = DISCH (--`(P:'a->bool) r`--)
                    (SYM (SUBST [v |-> SYM absd2] template t1))
       val t2 = EXISTS ((--`?a:'b. r:'a = rep a`--), (--`^ABS r`--))
	               (SYM(ASSUME (--`rep(^ABS (r:'a):'b) = r`--)))
       val imp2 = DISCH (--`rep(^ABS (r:'a):'b) = r`--)
     		        (EQ_MP (SYM (SPEC (--`r:'a`--) asm2)) t2)
       val TH2 = GEN (--`r:'a`--) (IMP_ANTISYM_RULE imp1 imp2)
       val CTH = CONJ TH1 TH2
       val ath = subst [ABS |-> Term`abs:'a->'b`] (concl CTH)
       val eth1 = EXISTS ((--`?abs:'a->'b. ^ath`--), ABS) CTH
       val eth2 = EXISTS ((--`?rep:'b->'a. ^(concl eth1)`--),
                          (--`rep:'b->'a`--)) eth1
       val result = DISCH (concl th1) (CHOOSE ((--`rep:'b->'a`--),def) eth2)
   in
   GEN (--`P:'a->bool`--) result
   end;

val _ = save_thm("ABS_REP_THM", ABS_REP_THM);


(*---------------------------------------------------------------------------
    LET_RAND =  P (let x = M in N x) = (let x = M in P (N x))
 ---------------------------------------------------------------------------*)

val LET_RAND = save_thm("LET_RAND",
 let val tm1 = Term`\x:'a. P (N x:'b):bool`
     val tm2 = Term`M:'a`
     val tm3 = Term`\x:'a. N x:'b`
     val P   = Term`P:'b -> bool`
     val LET_THM1 = RIGHT_BETA (SPEC tm2 (SPEC tm1
                    (Thm.INST_TYPE [beta |-> bool] LET_THM)))
     val LET_THM2 = AP_TERM P (RIGHT_BETA (SPEC tm2 (SPEC tm3 LET_THM)))
 in TRANS LET_THM2 (SYM LET_THM1)
 end);


(*---------------------------------------------------------------------------
    LET_RATOR =  (let x = M in N x) b = (let x = M in N x b)
 ---------------------------------------------------------------------------*)

val LET_RATOR = save_thm("LET_RATOR",
 let val M = Term`M:'a`
     val b = Term`b:'b`
     val tm1 = Term`\x:'a. N x:'b->'c`
     val tm2 = Term`\x:'a. N x ^b:'c`
     val LET_THM1 = AP_THM (RIGHT_BETA (SPEC M (SPEC tm1
                   (Thm.INST_TYPE [beta |-> (beta --> gamma)] LET_THM)))) b
     val LET_THM2 = RIGHT_BETA (SPEC M (SPEC tm2
                      (Thm.INST_TYPE [beta |-> gamma] LET_THM)))
 in TRANS LET_THM1 (SYM LET_THM2)
 end);


(*---------------------------------------------------------------------------
           !P. (!x y. P x y) = (!y x. P x y)
 ---------------------------------------------------------------------------*)

val SWAP_FORALL_THM =
  let val P = mk_var("P", Type `:'a->'b->bool`)
      val x = mk_var("x", Type.alpha)
      val y = mk_var("y", Type.beta)
      val Pxy = list_mk_comb (P,[x,y])
      val th1 = ASSUME (list_mk_forall [x,y] Pxy)
      val th2 = DISCH_ALL (GEN y (GEN x (SPEC y (SPEC x th1))))
      val th3 = ASSUME (list_mk_forall [y,x] Pxy)
      val th4 = DISCH_ALL (GEN x (GEN y (SPEC x (SPEC y th3))))
  in
     GEN P (IMP_ANTISYM_RULE th2 th4)
  end;

val _ = save_thm("SWAP_FORALL_THM", SWAP_FORALL_THM);

(*---------------------------------------------------------------------------
           !P. (?x y. P x y) = (?y x. P x y)
 ---------------------------------------------------------------------------*)

val SWAP_EXISTS_THM =
  let val P = mk_var("P", Type `:'a->'b->bool`)
      val x = mk_var("x", Type.alpha)
      val y = mk_var("y", Type.beta)
      val Pxy = list_mk_comb (P,[x,y])
      val tm1 = list_mk_exists[x] Pxy
      val tm2 = list_mk_exists[y] tm1
      val tm3 = list_mk_exists[y] Pxy
      val tm4 = list_mk_exists[x] tm3
      val th1 = ASSUME Pxy
      val th2 = EXISTS(tm2,y) (EXISTS (tm1,x) th1)
      val th3 = ASSUME (list_mk_exists [y] Pxy)
      val th4 = CHOOSE(y,th3) th2
      val th5 = CHOOSE(x,ASSUME (list_mk_exists [x,y] Pxy)) th4
      val th6 = EXISTS(tm4,x) (EXISTS (tm3,y) th1)
      val th7 = ASSUME (list_mk_exists[x] Pxy)
      val th8 = CHOOSE(x,th7) th6
      val th9 = CHOOSE(y,ASSUME (list_mk_exists [y,x] Pxy)) th8
  in
     GEN P (IMP_ANTISYM_RULE (DISCH_ALL th5) (DISCH_ALL th9))
  end;

val _ = save_thm("SWAP_EXISTS_THM", SWAP_EXISTS_THM);


(*---------------------------------------------------------------------------
   EXISTS_UNIQUE_THM

     !P. (?!x. P x) = (?x. P x) /\ (!x y. P x /\ P y ==> (x = y))
 ---------------------------------------------------------------------------*)

val EXISTS_UNIQUE_THM =
 let val th1 = RIGHT_BETA (AP_THM EXISTS_UNIQUE_DEF (Term`\x:'a. P x:bool`))
     val th2 = CONV_RULE (RAND_CONV (RAND_CONV
                (QUANT_CONV (QUANT_CONV (RATOR_CONV
                    (RAND_CONV (RAND_CONV BETA_CONV))))))) th1
 in
   CONV_RULE (RAND_CONV (RAND_CONV (QUANT_CONV (QUANT_CONV (RATOR_CONV
               (RAND_CONV (RATOR_CONV (RAND_CONV BETA_CONV)))))))) th2
 end;

val _ = save_thm("EXISTS_UNIQUE_THM", EXISTS_UNIQUE_THM);


(*---------------------------------------------------------------------------
  LET_CONG =
    |- !f g M N.  (M = N) /\ (!x. (x = N) ==> (f x = g x))
                            ==>
                   (LET f M = LET g N)
 ---------------------------------------------------------------------------*)

val LET_CONG =
  let val f = mk_var("f",alpha-->beta)
      val g = mk_var("g",alpha-->beta)
      val M = mk_var("M",alpha)
      val N = mk_var("N",alpha)
      val x = mk_var ("x",alpha)
      val MeqN = mk_eq(M,N)
      val x_eq_N = mk_eq(x,N)
      val fx_eq_gx = mk_eq(mk_comb(f,x),mk_comb(g,x))
      val ctm = mk_forall(x, mk_imp(x_eq_N,fx_eq_gx))
      val th  = RIGHT_BETA(AP_THM(RIGHT_BETA(AP_THM LET_DEF f)) M)
      val th1 = ASSUME MeqN
      val th2 = MP (SPEC N (ASSUME ctm)) (REFL N)
      val th3 = SUBS [SYM th1] th2
      val th4 = TRANS (TRANS th th3) (MK_COMB (REFL g,th1))
      val th5 = RIGHT_BETA(AP_THM(RIGHT_BETA(AP_THM LET_DEF g)) N)
      val th6 = TRANS th4 (SYM th5)
      val th7 = SUBS [SPECL [MeqN, ctm, concl th6] AND_IMP_INTRO]
                     (DISCH MeqN (DISCH ctm th6))
  in
    GENL [f,g,M,N] th7
  end;

val _ = save_thm("LET_CONG", LET_CONG);


(*---------------------------------------------------------------------------
  IMP_CONG =
    |- !x x' y y'. (x = x') /\ (x' ==> (y = y'))
                            ==>
                   (x ==> y = x' ==> y')
 ---------------------------------------------------------------------------*)

val IMP_CONG =
 let val x = mk_var("x",Type.bool)
     val x' = mk_var("x'",Type.bool)
     val y = mk_var("y",Type.bool)
     val y' = mk_var("y'",Type.bool)
     val x_eq_x' = mk_eq(x,x')
     val ctm = mk_imp(x', mk_eq(y,y'))
     val x_imp_y = mk_imp(x,y)
     val x'_imp_y' = mk_imp(x',y')
     val th = ASSUME x_eq_x'
     val th1 = UNDISCH(ASSUME ctm)
     val th2 = ASSUME x_imp_y
     val th3 = DISCH x_imp_y (DISCH x' (UNDISCH(SUBS [th,th1] th2)))
     val th4 = ASSUME x'_imp_y'
     val th5 = UNDISCH (SUBS [SYM th] (DISCH x' th1))
     val th6 = DISCH x'_imp_y' (DISCH x (UNDISCH(SUBS [SYM th,SYM th5] th4)))
     val th7 = IMP_ANTISYM_RULE th3 th6
     val th8 = DISCH x_eq_x' (DISCH ctm th7)
     val th9 = SUBS [SPECL [x_eq_x', ctm, concl th7] AND_IMP_INTRO] th8
 in
   GENL [x,x',y,y'] th9
 end;

val _ = save_thm("IMP_CONG", IMP_CONG);


(*---------------------------------------------------------------------------
  AND_CONG = |- !P P' Q Q'.
                  (Q ==> (P = P')) /\ (P' ==> (Q = Q'))
                                   ==>
                            (P /\ Q = P' /\ Q')
 ---------------------------------------------------------------------------*)

val AND_CONG =
 let val P = mk_var("P",Type.bool)
     val P' = mk_var("P'",Type.bool)
     val Q = mk_var("Q",Type.bool)
     val Q' = mk_var("Q'",Type.bool)
     val PandQ = mk_conj(P,Q)
     val P'andQ' = mk_conj(P',Q')
     val ctm1 = mk_imp(Q,  mk_eq(P,P'))
     val ctm2 = mk_imp(P', mk_eq(Q,Q'))
     val th1 = ASSUME PandQ
     val th2 = MP (ASSUME ctm1) (CONJUNCT2 th1)
     val th3 = MP (ASSUME ctm2) (SUBS [th2] (CONJUNCT1 th1))
     val th4 = DISCH PandQ (SUBS[th2,th3] th1)
     val th5 = ASSUME P'andQ'
     val th6 = MP (ASSUME ctm2) (CONJUNCT1 th5)
     val th7 = MP (ASSUME ctm1) (SUBS [SYM th6] (CONJUNCT2 th5))
     val th8 = DISCH P'andQ' (SUBS[SYM th6,SYM th7] th5)
     val th9 = IMP_ANTISYM_RULE th4 th8
     val th10 = SUBS [SPECL [ctm1,ctm2,concl th9] AND_IMP_INTRO]
                     (DISCH ctm1 (DISCH ctm2 th9))
 in
   GENL [P,P',Q,Q'] th10
 end;

val _ = save_thm("AND_CONG", AND_CONG);

(*---------------------------------------------------------------------------
  LEFT_AND_CONG =
       |- !P P' Q Q'.
          (P = P') /\ (P' ==> (Q = Q'))
                  ==>
          (P /\ Q = P' /\ Q')
 ---------------------------------------------------------------------------*)

val LEFT_AND_CONG =
 let val P = mk_var("P",Type.bool)
     val P' = mk_var("P'",Type.bool)
     val Q = mk_var("Q",Type.bool)
     val Q' = mk_var("Q'",Type.bool)
     val PandQ = mk_conj(P,Q)
     val P'andQ' = mk_conj(P',Q')
     val ctm1 = mk_eq(P,P')
     val ctm2 = mk_imp(P', mk_eq(Q,Q'))
     val th1 = ASSUME PandQ
     val th2 = ASSUME ctm1
     val th3 = SUBS [th2] (CONJUNCT1 th1)
     val th3a = MP (ASSUME ctm2) th3
     val th4 = DISCH PandQ (SUBS[th2,th3a] th1)
     val th5 = ASSUME P'andQ'
     val th6 = SUBS [SYM th2] (CONJUNCT1 th5)
     val th7 = SYM(MP (ASSUME ctm2) (CONJUNCT1 th5))
     val th8 = DISCH P'andQ' (SUBS[SYM th2,th7] th5)
     val th9 = IMP_ANTISYM_RULE th4 th8
     val th10 = SUBS [SPECL [ctm1,ctm2,concl th9] AND_IMP_INTRO]
                     (DISCH ctm1 (DISCH ctm2 th9))
 in
   GENL [P,P',Q,Q'] th10
 end;

val _ = save_thm("LEFT_AND_CONG", LEFT_AND_CONG);


(*---------------------------------------------------------------------------
   val OR_CONG =
       |- !P P' Q Q'.
         (~Q ==> (P = P')) /\ (~P' ==> (Q = Q'))
                           ==>
                   (P \/ Q = P' \/ Q')
 ---------------------------------------------------------------------------*)

val OR_CONG =
 let val P = mk_var("P",Type.bool)
     val P' = mk_var("P'",Type.bool)
     val Q = mk_var("Q",Type.bool)
     val Q' = mk_var("Q'",Type.bool)
     val notQ = mk_neg Q
     val notP' = mk_neg P'
     val PorQ = mk_disj(P,Q)
     val P'orQ' = mk_disj(P',Q')
     val PeqP'= mk_eq(P,P')
     val QeqQ'= mk_eq(Q,Q')
     val ctm1 = mk_imp(notQ,PeqP')
     val ctm2 = mk_imp(notP',QeqQ')
     val th1 = ASSUME PorQ
     val th2 = ASSUME P
     val th3 = ASSUME Q
     val th4 = ASSUME ctm1
     val th5 = ASSUME ctm2
     val th6 = SUBS [SPEC Q (CONJUNCT1 NOT_CLAUSES)]
                    (SUBS [SPECL[notQ, PeqP'] IMP_DISJ_THM] th4)
     val th7 = SUBS [SPEC P' (CONJUNCT1 NOT_CLAUSES)]
                    (SUBS [SPECL[notP', QeqQ'] IMP_DISJ_THM] th5)
     val th8 = ASSUME P'
     val th9 = DISJ1 th8 Q'
     val th10 = ASSUME QeqQ'
     val th11 = SUBS [th10] th3
     val th12 = DISJ2 P' th11
     val th13 = ASSUME PeqP'
     val th14 = MK_COMB(REFL(mk_const("\\/",bool-->bool-->bool)),th13)
     val th15 = EQ_MP (MK_COMB (th14,th10)) th1
     val th16 = DISJ_CASES th6 th12 th15
     val th17 = DISCH PorQ (DISJ_CASES th7 th9 th16)

     val th18 = ASSUME P'orQ'
     val th19 = DISJ2 P th3
     val th20 = DISJ1 (SUBS [SYM th13] th8) Q
     val th21 = EQ_MP (SYM (MK_COMB(th14,th10))) th18
     val th22 = DISJ_CASES th7 th20 th21
     val th23 = DISCH P'orQ' (DISJ_CASES th6 th19 th22)
     val th24 = IMP_ANTISYM_RULE th17 th23
     val th25 = SUBS [SPECL [ctm1,ctm2,concl th24] AND_IMP_INTRO]
                     (DISCH ctm1 (DISCH ctm2 th24))
 in
   GENL [P,P',Q,Q'] th25
 end;

val _ = save_thm("OR_CONG", OR_CONG);


(*---------------------------------------------------------------------------
   val LEFT_OR_CONG =
       |- !P P' Q Q'.
         (P = P') /\ (~P' ==> (Q = Q'))
                  ==>
          (P \/ Q = P' \/ Q')
 ---------------------------------------------------------------------------*)

val LEFT_OR_CONG =
 let fun mk_boolvar s = mk_var(s,Type.bool)
     val [P,P',Q,Q'] = map mk_boolvar ["P","P'","Q","Q'"]
     val notP = mk_neg P
     val notP' = mk_neg P'
     val PorQ = mk_disj(P,Q)
     val P'orQ' = mk_disj(P',Q')
     val PeqP' = mk_eq(P,P')
     val ctm = mk_imp(notP',mk_eq(Q,Q'))
     val th1 = ASSUME ctm
     val th2 = ASSUME PeqP'
     val th3 = DISJ1 (SUBS [th2] (ASSUME P)) Q'
     val th4 = MP th1 (SUBS [th2] (ASSUME notP))
     val th5 = DISJ2 P' (SUBS [th4] (ASSUME Q))
     val th6 = DISJ_CASES (SPEC P EXCLUDED_MIDDLE) th3 th5
     val th7 = DISCH PorQ (DISJ_CASES (ASSUME PorQ) th3 th6)
     val th8 = DISJ1 (SUBS [SYM th2] (ASSUME P')) Q
     val th9 = MP th1 (ASSUME notP')
     val th10 = DISJ2 P (SUBS [SYM th9] (ASSUME Q'))
     val th11 = DISJ_CASES (SPEC P' EXCLUDED_MIDDLE) th8 th10
     val th12 = DISCH P'orQ' (DISJ_CASES (ASSUME P'orQ') th8 th11)
     val th13 = DISCH PeqP' (DISCH ctm (IMP_ANTISYM_RULE th7 th12))
     val th14 = SUBS[SPECL [PeqP',ctm,mk_eq(PorQ,P'orQ')] AND_IMP_INTRO] th13
 in
   GENL [P,P',Q,Q'] th14
 end;

val _ = save_thm("LEFT_OR_CONG", LEFT_OR_CONG);


(*---------------------------------------------------------------------------
   val COND_CONG =
    |- !P Q x x' y y'.
         (P = Q) /\ (Q ==> (x = x')) /\ (~Q ==> (y = y'))
                 ==>
         ((if P then x else y) = (if Q then x' else y'))
 ---------------------------------------------------------------------------*)

fun mk_cond {cond,larm,rarm} = Term `if ^cond then ^larm else ^rarm`;

val COND_CONG =
 let val P = mk_var("P",Type.bool)
     val Q = mk_var("Q",Type.bool)
     val x = mk_var("x",alpha)
     val x' = mk_var("x'",alpha)
     val y  = mk_var("y",alpha)
     val y' = mk_var("y'",alpha)
     val PeqQ = mk_eq(P,Q)
     val ctm1 = mk_imp(Q, mk_eq(x,x'))
     val ctm2 = mk_imp(mk_neg Q, mk_eq(y,y'))
     val target = mk_eq(mk_cond{cond=P,larm=x,rarm=y},
                        mk_cond{cond=Q,larm=x',rarm=y'})
     val OR_ELIM = MP (SPECL[target,P,mk_neg P] OR_ELIM_THM)
                      (SPEC P EXCLUDED_MIDDLE)
     val th1 = ASSUME P
     val th2 = EQT_INTRO th1
     val th3 = CONJUNCT1 (SPECL [x,y] COND_CLAUSES)
     val th3a = CONJUNCT1 (SPECL [x',y'] COND_CLAUSES)
     val th4 = SUBS [SYM th2] th3
     val th4a = SUBS [SYM th2] th3a
     val th5 = ASSUME PeqQ
     val th6 = ASSUME ctm1
     val th7 = ASSUME ctm2
     val th8 = UNDISCH (SUBS [SYM th5] th6)
     val th9 = TRANS th4 th8
     val th10 = TRANS th9 (SYM (SUBS [th5] th4a))

     val th11 = EQF_INTRO (ASSUME (mk_neg P))
     val th12 = CONJUNCT2 (SPECL [x,y] COND_CLAUSES)
     val th13 = CONJUNCT2 (SPECL [x',y'] COND_CLAUSES)
     val th14 = SUBS [SYM th11] th12
     val th15 = SUBS [SYM th11] th13
     val th16 = UNDISCH (SUBS [SYM th5] th7)
     val th17 = TRANS th14 th16
     val th18 = TRANS th17 (SYM (SUBS [th5] th15))
     val th19 = MP (MP OR_ELIM (DISCH P th10)) (DISCH (mk_neg P) th18)
     val th20 = DISCH PeqQ (DISCH ctm1 (DISCH ctm2 th19))
     val th21 = SUBS [SPECL [ctm1, ctm2,concl th19] AND_IMP_INTRO] th20
     val cnj  = mk_conj(ctm1,ctm2)
     val th22 = SUBS [SPECL [PeqQ,cnj,concl th19] AND_IMP_INTRO] th21
 in
   GENL [P,Q,x,x',y,y'] th22
 end;

val _ = save_thm("COND_CONG", COND_CONG);

(* ----------------------------------------------------------------------

    RES_FORALL_CONG
       |- (P = Q) ==> (!x. x IN Q ==> (f x = g x)) ==>
          (RES_FORALL P f = RES_FORALL Q g)

    RES_EXISTS_CONG
       |- (P = Q) ==> (!x. x IN Q ==> (f x = g x)) ==>
          (RES_EXISTS P f = RES_EXISTS P g)
   ---------------------------------------------------------------------- *)

val (RES_FORALL_CONG, RES_EXISTS_CONG) = let
  (* stuff in common to both *)
  val aset_ty = alpha --> bool
  val [P,Q,f,g] = map (fn s => mk_var(s, aset_ty)) ["P", "Q", "f", "g"]
  val PeqQ_t = mk_eq(P, Q)
  val PeqQ_th = ASSUME PeqQ_t
  val x = mk_var("x", alpha)
  val fx_t = mk_comb(f, x)
  val gx_t = mk_comb(g, x)
  val IN_t = prim_mk_const {Thy = "bool", Name = "IN"}
  val xINP_t = list_mk_comb(IN_t, [x, P])
  val xINP_th = ASSUME xINP_t
  val xINQ_t = list_mk_comb(IN_t, [x, Q])
  val xINQ_th = ASSUME xINQ_t
  val xINP_eq_xINQ_th = AP_TERM (mk_comb(IN_t, x)) PeqQ_th
  val (xINP_imp_xINQ, xINQ_imp_xINP) = EQ_IMP_RULE xINP_eq_xINQ_th
  val feqg_t = mk_forall(x, mk_imp(xINQ_t, mk_eq(mk_comb(f,x), mk_comb(g, x))))
  val feqg_th = SPEC x (ASSUME feqg_t)
  val feqg_th = MP feqg_th xINQ_th
  val (f_imp_g_th, g_imp_f_th) = EQ_IMP_RULE feqg_th

  fun mk_res th args =
      List.foldl (RIGHT_BETA o uncurry (C AP_THM)) th args

  (* forall thm *)
  val resfa_t = prim_mk_const {Thy = "bool", Name = "RES_FORALL"}
  val res_pf_t = list_mk_comb(resfa_t, [P, f])
  val res_qg_t = list_mk_comb(resfa_t, [Q, g])
  val resfa_pf_eqn = mk_res RES_FORALL_DEF [P, f]
  val resfa_qg_eqn = mk_res RES_FORALL_DEF [Q, g]

  val resfa_pf_eq_th = SPEC x (EQ_MP resfa_pf_eqn (ASSUME res_pf_t))
  val g_th = MP f_imp_g_th (MP resfa_pf_eq_th xINP_th)
  val xinq_imp_g_th =
      GEN x (DISCH xINQ_t (PROVE_HYP (UNDISCH xINQ_imp_xINP) g_th))
  val rfa_pf_imp_rfa_qg =
      DISCH res_pf_t (EQ_MP (SYM resfa_qg_eqn) xinq_imp_g_th)

  val resfa_qg_eq_th = SPEC x (EQ_MP resfa_qg_eqn (ASSUME res_qg_t))
  val f_th = MP g_imp_f_th (MP resfa_qg_eq_th xINQ_th)
  val xinp_imp_f_th =
      GEN x (DISCH xINP_t (PROVE_HYP (UNDISCH xINP_imp_xINQ) f_th))
  val rfa_qg_imp_rfa_pf =
      DISCH res_qg_t (EQ_MP (SYM resfa_pf_eqn) xinp_imp_f_th)
  val fa_eqn = IMP_ANTISYM_RULE rfa_pf_imp_rfa_qg rfa_qg_imp_rfa_pf

  (* exists thm *)
  val resex_t = prim_mk_const {Thy = "bool", Name = "RES_EXISTS"}
  val res_pf_t = list_mk_comb(resex_t, [P, f])
  val res_qg_t = list_mk_comb(resex_t, [Q, g])
  val resex_pf_eqn = mk_res RES_EXISTS_DEF [P, f]
  val resex_qg_eqn = mk_res RES_EXISTS_DEF [Q, g]

  val pf_exbody_th = EQ_MP resex_pf_eqn (ASSUME res_pf_t)
  val pf_body_th = ASSUME(mk_conj(xINP_t, fx_t))
  val (new_xINP_th, fx_th) = CONJ_PAIR pf_body_th
  val new_xINQ_th = MP xINP_imp_xINQ new_xINP_th
  val new_gx_th = PROVE_HYP new_xINQ_th (MP f_imp_g_th fx_th)
  val qg_exists =
      EXISTS(rhs (concl resex_qg_eqn), x) (CONJ new_xINQ_th new_gx_th)
  val pf_chosen = CHOOSE(x,EQ_MP resex_pf_eqn (ASSUME res_pf_t)) qg_exists
  val ex_pf_imp_qg = DISCH res_pf_t (EQ_MP (SYM resex_qg_eqn) pf_chosen)

  val qg_exbody_th = EQ_MP resex_qg_eqn (ASSUME res_qg_t)
  val qg_body_th = ASSUME(mk_conj(xINQ_t, gx_t))
  val (new_xINQ_th, gx_th) = CONJ_PAIR qg_body_th
  val new_xINP_th = MP xINQ_imp_xINP new_xINQ_th
  val new_fx_th = PROVE_HYP new_xINQ_th (MP g_imp_f_th gx_th)
  val pf_exists =
      EXISTS (rhs (concl resex_pf_eqn), x) (CONJ new_xINP_th new_fx_th)
  val qg_chosen = CHOOSE(x, EQ_MP resex_qg_eqn (ASSUME res_qg_t)) pf_exists
  val ex_qg_imp_pf = DISCH res_qg_t (EQ_MP (SYM resex_pf_eqn) qg_chosen)

  val ex_eqn = IMP_ANTISYM_RULE ex_pf_imp_qg ex_qg_imp_pf

in
  (save_thm("RES_FORALL_CONG", DISCH PeqQ_t (DISCH feqg_t fa_eqn)),
   save_thm("RES_EXISTS_CONG", DISCH PeqQ_t (DISCH feqg_t ex_eqn)))
end

(* ------------------------------------------------------------------------- *)
(* Monotonicity.                                                             *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* MONO_AND |- (x ==> y) /\ (z ==> w) ==> (x /\ z ==> y /\ w)                *)
(* ------------------------------------------------------------------------- *)

val MONO_AND = save_thm("MONO_AND",
 let val tm1 = Term `x ==> y`
     val tm2 = Term `z ==> w`
     val tm3 = Term `x /\ z`
     val tm4 = Term `y /\ w`
     val th1 = ASSUME tm1
     val th2 = ASSUME tm2
     val th3 = ASSUME tm3
     val th4 = CONJUNCT1 th3
     val th5 = CONJUNCT2 th3
     val th6 = MP th1 th4
     val th7 = MP th2 th5
     val th8 = CONJ th6 th7
     val th9 = itlist DISCH [tm1,tm2,tm3] th8
     val th10 = SPEC (Term`^tm3 ==> ^tm4`) (SPEC tm2 (SPEC tm1 AND_IMP_INTRO))
 in
    EQ_MP th10 th9
 end);


(* ------------------------------------------------------------------------- *)
(* MONO_OR |- (x ==> y) /\ (z ==> w) ==> (x \/ z ==> y \/ w)                 *)
(* ------------------------------------------------------------------------- *)

val MONO_OR = save_thm("MONO_OR",
 let val tm1 = Term `x ==> y`
     val tm2 = Term `z ==> w`
     val tm3 = Term `x \/ z`
     val tm4 = Term `y \/ w`
     val th1 = ASSUME tm1
     val th2 = ASSUME tm2
     val th3 = ASSUME tm3
     val th4 = DISJ1 (MP th1 (ASSUME (Term `x:bool`))) (Term`w:bool`)
     val th5 = DISJ2 (Term`y:bool`) (MP th2 (ASSUME (Term `z:bool`)))
     val th6 = DISJ_CASES th3 th4 th5
     val th7 = DISCH tm1 (DISCH tm2 (DISCH tm3 th6))
     val th8 = SPEC (Term`^tm3 ==> ^tm4`) (SPEC tm2 (SPEC tm1 AND_IMP_INTRO))
 in
    EQ_MP th8 th7
 end);


(* ------------------------------------------------------------------------- *)
(* MONO_IMP |- (y ==> x) /\ (z ==> w) ==> ((x ==> z) ==> (y ==> w))          *)
(* ------------------------------------------------------------------------- *)

val MONO_IMP = save_thm("MONO_IMP",
 let val tm1 = Term `y ==> x`
     val tm2 = Term `z ==> w`
     val tm3 = Term `x ==> z`
     val tm4 = Term `y ==> w`
     val tm5 = Term `y:bool`
     val th1 = ASSUME tm1
     val th2 = ASSUME tm2
     val th3 = ASSUME tm3
     val th4 = MP th1 (ASSUME tm5)
     val th5 = MP th3 th4
     val th6 = MP th2 th5
     val th7 = DISCH tm1 (DISCH tm2 (DISCH tm3 (DISCH tm5 th6)))
     val th8 = SPEC (Term`^tm3 ==> ^tm4`) (SPEC tm2 (SPEC tm1 AND_IMP_INTRO))
 in
    EQ_MP th8 th7
 end);


(* ------------------------------------------------------------------------- *)
(* MONO_NOT |- (y ==> x) ==> (~x ==> ~y)                                     *)
(* ------------------------------------------------------------------------- *)

val MONO_NOT = save_thm("MONO_NOT",
 let val tm1 = Term `y ==> x`
     val tm2 = Term `~x`
     val tm3 = Term `y:bool`
     val th1 = ASSUME tm1
     val th2 = ASSUME tm2
     val th3 = ASSUME tm3
     val th4 = MP th1 th3
     val th5 = DISCH tm3 (MP th2 th4)
     val th6 = EQ_MP (SYM (RIGHT_BETA (AP_THM NOT_DEF tm3))) th5
 in
    DISCH tm1 (DISCH tm2 th6)
 end);


(* ------------------------------------------------------------------------- *)
(* MONO_NOT_EQ |- (y ==> x) = (~x ==> ~y)                                     *)
(* ------------------------------------------------------------------------- *)


val MONO_NOT_EQ = save_thm("MONO_NOT_EQ",
 let val tm1 = Term `x:bool`
     val tm2 = Term `y:bool`
     val th1 = INST [tm1 |-> mk_neg tm2, tm2 |-> mk_neg tm1] MONO_NOT

     val th2 = SUBST [Term `x1:bool` |-> SPEC tm1 (CONJUNCT1 NOT_CLAUSES),
                      Term `x2:bool` |-> SPEC tm2 (CONJUNCT1 NOT_CLAUSES)]
                     (Term `(~x ==> ~y) ==> (x2 ==> x1)`) th1

     val th3 = IMP_ANTISYM_RULE MONO_NOT th2
 in
     th3
 end);


(* ------------------------------------------------------------------------- *)
(* MONO_ALL |- (!x. P x ==> Q x) ==> (!x. P x) ==> !x. Q x                   *)
(* ------------------------------------------------------------------------- *)

val MONO_ALL = save_thm("MONO_ALL",
 let val tm1 = Term `!x:'a. P x ==> Q x`
     val tm2 = Term `!x:'a. P x`
     val tm3 = Term `x:'a`
     val th1 = ASSUME tm1
     val th2 = ASSUME tm2
     val th3 = SPEC tm3 th1
     val th4 = SPEC tm3 th2
     val th5 = GEN tm3 (MP th3 th4)
 in
    DISCH tm1 (DISCH tm2 th5)
 end);


(* ------------------------------------------------------------------------- *)
(* MONO_EXISTS =  [] |- (!x. P x ==> Q x) ==> (?x. P x) ==> ?x. Q x          *)
(* ------------------------------------------------------------------------- *)

val MONO_EXISTS = save_thm("MONO_EXISTS",
 let val tm1 = Term `!x:'a. P x ==> Q x`
     val tm2 = Term `?x:'a. P x`
     val tm3 = Term `@x:'a. P x`
     val tm4 = Term `\x:'a. P x:bool`
     val th1 = ASSUME tm1
     val th2 = ASSUME tm2
     val th3 = SPEC tm3 th1
     val th4 = RIGHT_BETA(RIGHT_BETA (AP_THM EXISTS_DEF tm4))
     val th5 = EQ_MP th4 th2
     val th6 = MP th3 th5
 in
    DISCH tm1 (DISCH tm2 (EXISTS (Term`?x:'a. Q x`, tm3) th6))
 end);


(* ------------------------------------------------------------------------- *)
(* MONO_COND |- (x ==> y) ==> (z ==> w)                                      *)
(*              ==> (if b then x else z) ==> (if b then y else w)            *)
(* ------------------------------------------------------------------------- *)

val MONO_COND = save_thm("MONO_COND",
 let val tm1 = Term `x ==> y`
     val tm2 = Term `z ==> w`
     val tm3 = Term `if b then x else z:bool`
     val tm4 = Term `b:bool`
     val tm5 = Term `x:bool`
     val tm6 = Term `z:bool`
     val tm7 = Term `y:bool`
     val tm8 = Term `w:bool`
     val th1 = ASSUME tm1
     val th2 = ASSUME tm2
     val th3 = ASSUME tm3
     val th4 = SPEC tm6 (SPEC tm5 (INST_TYPE [alpha |-> bool] COND_CLAUSES))
     val th5 = CONJUNCT1 th4
     val th6 = CONJUNCT2 th4
     val th7 = SPEC tm4 BOOL_CASES_AX
     val th8 = ASSUME (Term`b = T`)
     val th9 = ASSUME (Term`b = F`)
     val th10 = SUBST [tm4 |-> th8] (concl th3) th3
     val th11 = SUBST [tm4 |-> th9] (concl th3) th3
     val th12 = EQ_MP th5 th10
     val th13 = EQ_MP th6 th11
     val th14 = MP th1 th12
     val th15 = MP th2 th13

     val th16 = INST [tm5 |-> tm7, tm6 |-> tm8] th4
     val th17 = SYM (CONJUNCT1 th16)
     val th18 = SYM (CONJUNCT2 th16)
     val th19 = EQ_MP th17 th14
     val th20 = EQ_MP th18 th15
     val th21 = DISCH tm3 th19
     val th22 = DISCH tm3 th20
     val th23 = SUBST [tm4 |-> th8] (concl th21) th21
     val th24 = SUBST [tm4 |-> th9] (concl th22) th22
     val v = Term`v:bool`
     val T = mk_const("T",bool)
     val template = subst [T |-> v] (concl th23)
     val th25 = SUBST [v |-> SYM th8] template th23
     val th26 = SUBST [v |-> SYM th9] template th24
 in
    DISCH tm1 (DISCH tm2 (DISJ_CASES th7 th25 th26))
 end);


(* ------------------------------------------------------------------------- *)
(* EXISTS_REFL |- !a. ?x. x = a                                              *)
(* ------------------------------------------------------------------------- *)

val EXISTS_REFL = save_thm("EXISTS_REFL",
 let val a = Term `a:'a`
     val th1 = REFL a
     val th2 = EXISTS (Term`?x:'a. x = a`, a) th1
 in GEN a th2
 end);

(* ------------------------------------------------------------------------- *)
(* EXISTS_UNIQUE_REFL |- !a. ?!x. x = a                                      *)
(* ------------------------------------------------------------------------- *)

val EXISTS_UNIQUE_REFL = save_thm("EXISTS_UNIQUE_REFL",
 let val a = Term `a:'a`
     val P = Term `\x:'a. x = a`
     val tmx = Term `^P x`
     val tmy= Term `^P y`
     val ex = Term `?x. ^P x`
     val th1 = SPEC a EXISTS_REFL
     val th2 = ABS (Term`x:'a`) (BETA_CONV tmx)
     val th3 = AP_TERM (Term`$? :('a->bool)->bool`) th2
     val th4 = EQ_MP (SYM th3) th1
     val th5 = ASSUME (mk_conj(tmx,tmy))
     val th6 = CONJUNCT1 th5
     val th7 = CONJUNCT2 th5
     val th8 = EQ_MP (BETA_CONV (concl th6)) th6
     val th9 = EQ_MP (BETA_CONV (concl th7)) th7
     val th10 = TRANS th8 (SYM th9)
     val th11 = DISCH (hd(hyp th10)) th10
     val th12 = GEN (Term`x:'a`) (GEN (Term`y:'a`) th11)
     val th13 = INST [Term`P:'a->bool` |-> P] EXISTS_UNIQUE_THM
     val th14 = EQ_MP (SYM th13) (CONJ th4 th12)
     val th15 = AP_TERM (Term`$?! :('a->bool)->bool`) th2
 in
     GEN a (EQ_MP th15 th14)
 end);


(* ------------------------------------------------------------------------- *)
(* Unwinding.                                                                *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* UNWIND1_THM |- !P a. (?x. (a = x) /\ P x) = P a                           *)
(* ------------------------------------------------------------------------- *)

val UNWIND_THM1 = save_thm("UNWIND_THM1",
 let val P = Term`P:'a->bool`
     val a = Term `a:'a`
     val Pa = Term`^P ^a`
     val v = Term `v:'a`
     val tm1 = Term`?x:'a. (a = x) /\ P x`
     val th1 = ASSUME tm1
     val th2 = ASSUME (Term`(a:'a = v) /\ P v`)
     val th3 = CONJUNCT1 th2
     val th4 = CONJUNCT2 th2
     val th5 = SUBST [v |-> SYM th3] (concl th4) th4
     val th6 = DISCH tm1 (CHOOSE (v,th1) th5)
     val th7 = ASSUME Pa
     val th8 = CONJ (REFL a) th7
     val th9 = EXISTS (tm1,a) th8
     val th10 = DISCH Pa th9
     val th11 = SPEC Pa (SPEC tm1 IMP_ANTISYM_AX)
 in
    GEN P (GEN a (MP (MP th11 th6) th10))
 end);


(* ------------------------------------------------------------------------- *)
(* UNWIND_THM2  |- !P a. (?x. (x = a) /\ P x) = P a                          *)
(* ------------------------------------------------------------------------- *)

val UNWIND_THM2 = save_thm("UNWIND_THM2",
 let val P = Term`P:'a->bool`
     val a = Term `a:'a`
     val Px = Term`^P x`
     val Pa = Term`^P ^a`
     val u = Term `u:'a`
     val v = Term `v:'a`
     val a_eq_x = Term `a:'a = x`
     val x_eq_a = Term `x:'a = a`
     val th1 = SPEC a (SPEC P UNWIND_THM1)
     val th2 = REFL Pa
     val th3 = DISCH a_eq_x (SYM (ASSUME a_eq_x))
     val th4 = DISCH x_eq_a (SYM (ASSUME x_eq_a))
     val th5 = SPEC a_eq_x (SPEC x_eq_a IMP_ANTISYM_AX)
     val th6 = MP (MP th5 th4) th3
     val th7 = MK_COMB (MK_COMB (REFL (Term`$/\`), th6), REFL Px)
     val th8 = MK_COMB (REFL(Term`$? :('a->bool)->bool`),
                        ABS (Term`x:'a`) th7)
     val th9 = MK_COMB(MK_COMB (REFL(Term`$= :bool->bool->bool`), th8),th2)
     val th10 = EQ_MP (SYM th9) th1
 in
    GEN P (GEN a th10)
 end);


(* ------------------------------------------------------------------------- *)
(* UNWIND_FORALL_THM1   |- !f v. (!x. (v = x) ==> f x) = f v                 *)
(* ------------------------------------------------------------------------- *)

val UNWIND_FORALL_THM1 = save_thm("UNWIND_FORALL_THM1",
 let val f = Term `f : 'a -> bool`
     val v = Term `v:'a`
     val fv = Term `^f ^v`
     val tm1 = Term `!x:'a. (v = x) ==> f x`
     val tm2 = Term `v:'a = x`
     val th1 = ASSUME tm1
     val th2 = ASSUME fv
     val th3 = DISCH tm1 (MP (SPEC v th1) (REFL v))
     val th4 = ASSUME tm2
     val th5 = SUBST [v |-> th4] (concl th2) th2
     val th6 = DISCH fv (GEN (Term`x:'a`) (DISCH tm2 th5))
     val th7 = MP (MP (SPEC tm1 (SPEC fv IMP_ANTISYM_AX)) th6) th3
 in
   GEN f (GEN v (SYM th7))
 end);


(* ------------------------------------------------------------------------- *)
(* UNWIND_FORALL_THM2   |- !f v. (!x. (x = v) ==> f x) = f v                 *)
(* ------------------------------------------------------------------------- *)

val UNWIND_FORALL_THM2 = save_thm("UNWIND_FORALL_THM2",
 let val f   = Term `f:'a->bool`
     val v   = Term `v:'a`
     val fv  = Term `^f ^v`
     val tm1 = Term `!x:'a. (x = v) ==> f x`
     val tm2 = Term `x:'a = v`
     val th1 = ASSUME tm1
     val th2 = ASSUME fv
     val th3 = DISCH tm1 (MP (SPEC v th1) (REFL v))
     val th4 = ASSUME tm2
     val th5 = SUBST [v |-> SYM th4] (concl th2) th2
     val th6 = DISCH fv (GEN (Term`x:'a`) (DISCH tm2 th5))
     val th7 = MP (MP (SPEC tm1 (SPEC fv IMP_ANTISYM_AX)) th6) th3
 in
   GEN f (GEN v (SYM th7))
 end);


(* ------------------------------------------------------------------------- *)
(* Skolemization:    |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x)            *)
(* ------------------------------------------------------------------------- *)

val SKOLEM_THM = save_thm("SKOLEM_THM",
 let val P = Term`P:'a -> 'b -> bool`
     val x = Term`x:'a`
     val y = Term`y:'b`
     val f = Term`f:'a->'b`
     val tm1 = Term`!x. ?y. ^P x y`
     val tm2 = Term `?f. !x. ^P x (f x)`
     val tm4 = Term`\x. @y. ^P x y`
     val tm5 = Term`(\x. @y. ^P x y) x`
     val th1 = ASSUME tm1
     val th2 = ASSUME tm2
     val th3 = SPEC x th1
     val th4 = INST_TYPE [alpha |-> beta] SELECT_AX
     val th5 = SPEC y (SPEC (Term`\y. ^P x y`) th4)
     val th6 = BETA_CONV (fst(dest_imp(concl th5)))
     val th7 = BETA_CONV (snd(dest_imp(concl th5)))
     val th8 = MK_COMB (MK_COMB (REFL (Term`$==>`),th6),th7)
     val th9 = EQ_MP th8 th5
     val th10 = MP th9 (ASSUME(fst(dest_imp(concl th9))))
     val th11 = CHOOSE (y,th3) th10
     val th12 = SYM (BETA_CONV tm5)
     val th13 = SUBST [Term`v:'b` |-> th12] (Term`^P x v`) th11
     val th14 = DISCH tm1 (EXISTS (tm2,tm4) (GEN x th13))
     val th15 = ASSUME (Term`!x. ^P x (f x)`)
     val th16 = SPEC x th15
     val th17 = GEN x (EXISTS(Term`?y. ^P x y`,Term`f (x:'a):'b`) th16)
     val th18 = DISCH tm2 (CHOOSE (f,th2) th17)
     val th19 = MP (MP (SPEC tm1 (SPEC tm2 IMP_ANTISYM_AX)) th18) th14
 in
     GEN P (SYM th19)
 end);


(*---------------------------------------------------------------------------
    Support for pattern matching on booleans.

    bool_case_thm =
        |- (!e0 e1. bool_case e0 e1 T = e0) /\
            !e0 e1. bool_case e0 e1 F = e1
 ---------------------------------------------------------------------------*)

val bool_case_thm = let
  val (vs,_) = strip_forall (concl COND_CLAUSES)
in
  save_thm("bool_case_thm",
           COND_CLAUSES |> SPECL vs |> CONJUNCTS |> map (GENL vs) |> LIST_CONJ)
end

(* ------------------------------------------------------------------------- *)
(*    bool_case_ID = |- !x b. bool_case x x b = x                            *)
(* ------------------------------------------------------------------------- *)

val bool_case_ID = save_thm("bool_case_ID", COND_ID)


(* ------------------------------------------------------------------------- *)
(* boolAxiom  |- !e0 e1. ?fn. (fn T = e0) /\ (fn F = e1)                     *)
(* ------------------------------------------------------------------------- *)

val boolAxiom = save_thm("boolAxiom",
 let
   val ([e0,e1], _) = strip_forall (concl COND_CLAUSES)
   val (th2, th3) = CONJ_PAIR (SPECL [e0, e1] COND_CLAUSES)
   val f_t = Term`\b. if b then ^e0 else ^e1`
   val f_T = TRANS (BETA_CONV (mk_comb(f_t, T))) th2
   val f_F = TRANS (BETA_CONV (mk_comb(f_t, F))) th3
   val th4 = CONJ f_T f_F
   val th5 = EXISTS (Term`?fn. (fn T = ^e0) /\ (fn F = ^e1)`, f_t) th4
 in
    GEN e0 (GEN e1 th5)
 end);

(* ------------------------------------------------------------------------- *)
(* bool_INDUCT |- !P. P T /\ P F ==> !b. P b                                 *)
(* ------------------------------------------------------------------------- *)

val bool_INDUCT = save_thm("bool_INDUCT",
 let val P = Term`P:bool -> bool`
     val b = Term `b:bool`
     val v = Term `v:bool`
     val tm1 = Term`^P T /\ ^P F`
     val th1 = SPEC b BOOL_CASES_AX
     val th2 = ASSUME tm1
     val th3 = CONJUNCT1 th2
     val th4 = CONJUNCT2 th2
     val th5 = ASSUME (Term `b = T`)
     val th6 = ASSUME (Term `b = F`)
     val th7 = SUBST [v |-> SYM th5] (Term`^P ^v`) th3
     val th8 = SUBST [v |-> SYM th6] (Term`^P ^v`) th4
     val th9 = GEN b (DISJ_CASES th1 th7 th8)
 in
     GEN P (DISCH tm1 th9)
 end);

(* ---------------------------------------------------------------------------
   |- !P Q x x' y y'.
         (P = Q) /\ (Q ==> (x = x')) /\ (~Q ==> (y = y')) ==>
         ((case P of T -> x || F -> y) = (case Q of T -> x' || F -> y'))
  --------------------------------------------------------------------------- *)

val bool_case_CONG = save_thm("bool_case_CONG", COND_CONG)

val FORALL_BOOL = save_thm
("FORALL_BOOL",
 let val tm1 = Term `!b:bool. P b`
     val tm2 = Term `P T /\ P F`
     val th1 = ASSUME tm1
     val th2 = CONJ (SPEC T th1) (SPEC F th1)
     val th3 = DISCH tm1 th2
     val th4 = ASSUME tm2
     val th5 = MP (SPEC (Term `P:bool->bool`) bool_INDUCT) th4
     val th6 = DISCH tm2 th5
 in
   IMP_ANTISYM_RULE th3 th6
 end);


(*---------------------------------------------------------------------------
          Results about Unique existence.
 ---------------------------------------------------------------------------*)

local
  val LAND_CONV = RATOR_CONV o RAND_CONV
  val P = mk_var("P",   Type.alpha --> Type.bool)
  val p = mk_var("p",   Type.bool)
  val q = mk_var("q",   Type.bool)
  val Q = mk_var("Q",   Type.alpha --> Type.bool)
  val x = mk_var("x",   Type.alpha)
  val y = mk_var("y",   Type.alpha)
  val Px = mk_comb(P, x)
  val Py = mk_comb(P, y)
  val Qx = mk_comb(Q, x)
  val Qy = mk_comb(Q, y)
  val uex_t = mk_const("?!", (alpha --> bool) --> bool)
  val exP = mk_exists(x, Px)
  val exQ = mk_exists(x, Qx)
  val uexP = mk_exists1(x, Px)
  val uexQ = mk_exists1(x, Qx)
  val pseudo_mp = let
    val lhs_t = mk_conj(p, mk_imp(p, q))
    val rhs_t = mk_conj(p, q)
    val lhs_thm = ASSUME lhs_t
    val (p_thm, pimpq) = CONJ_PAIR lhs_thm
    val dir1 = DISCH_ALL (CONJ p_thm (MP pimpq p_thm))
    val rhs_thm = ASSUME rhs_t
    val (p_thm, q_thm) = CONJ_PAIR rhs_thm
    val dir2 = DISCH_ALL (CONJ p_thm (DISCH p q_thm))
  in
    IMP_ANTISYM_RULE dir1 dir2
  end
in
  val UEXISTS_OR_THM = let
    val subdisj_t = mk_abs(x, mk_disj(Px, Qx))
    val lhs_t = mk_comb(uex_t, subdisj_t)
    val lhs_thm = ASSUME lhs_t
    val lhs_eq = AP_THM EXISTS_UNIQUE_DEF subdisj_t
    val lhs_expanded = CONV_RULE BETA_CONV (EQ_MP lhs_eq lhs_thm)
    val (expq0, univ) =  CONJ_PAIR lhs_expanded
    val expq = EQ_MP (SPEC_ALL EXISTS_OR_THM) expq0
    val univ1 = SPEC_ALL univ
    val univ2 = CONV_RULE (LAND_CONV (LAND_CONV BETA_CONV)) univ1
    val univ3 = CONV_RULE (LAND_CONV (RAND_CONV BETA_CONV)) univ2
    val P_half = let
      val asm = ASSUME (mk_conj(Px,Py))
      val (Px_thm, Py_thm) = CONJ_PAIR asm
      val PxQx_thm = DISJ1 Px_thm Qx
      val PyQy_thm = DISJ1 Py_thm Qy
      val resolvent = CONJ PxQx_thm PyQy_thm
      val rhs =
        GENL [x,y]
        (DISCH (mk_conj(Px,Py)) (PROVE_HYP resolvent (UNDISCH univ3)))
    in
      DISJ1 (EQ_MP (SYM EXISTS_UNIQUE_THM) (CONJ (ASSUME exP) rhs)) uexQ
    end
    val Q_half = let
      val asm = ASSUME (mk_conj(Qx,Qy))
      val (Qx_thm, Qy_thm) = CONJ_PAIR asm
      val PxQx_thm = DISJ2 Px Qx_thm
      val PyQy_thm = DISJ2 Py Qy_thm
      val resolvent = CONJ PxQx_thm PyQy_thm
      val rhs =
        GENL [x,y]
        (DISCH (mk_conj(Qx,Qy)) (PROVE_HYP resolvent (UNDISCH univ3)))
      val uex_expanded = SYM (INST [P |-> Q] EXISTS_UNIQUE_THM)
    in
      DISJ2 uexP (EQ_MP uex_expanded (CONJ (ASSUME exQ) rhs))
    end
  in
    save_thm("UEXISTS_OR_THM",
             GENL [P, Q] (DISCH_ALL (DISJ_CASES expq P_half Q_half)))
  end;

  val UEXISTS_SIMP = let
    fun mCONV_RULE c thm = TRANS thm (c  (rhs (concl thm)))
    val xeqy = mk_eq(x,y)
    val t = mk_var("t",   bool)
    val abst = mk_abs(x, t)
    val uext_t = mk_exists1(x,t)
    val exp0 = AP_THM EXISTS_UNIQUE_DEF abst
    val exp1 = mCONV_RULE BETA_CONV exp0
    val exp2 = mCONV_RULE (LAND_CONV (K (SPEC t EXISTS_SIMP))) exp1
    val exp3 =
      mCONV_RULE (RAND_CONV
                  (QUANT_CONV
                   (QUANT_CONV (LAND_CONV (LAND_CONV BETA_CONV))))) exp2
    val exp4 =
      mCONV_RULE (RAND_CONV
                  (QUANT_CONV
                   (QUANT_CONV (LAND_CONV (RAND_CONV BETA_CONV))))) exp3
    val exp5 =
      mCONV_RULE (RAND_CONV
                  (QUANT_CONV
                   (QUANT_CONV (LAND_CONV (K (SPEC t AND_CLAUSE5)))))) exp4
    val pushy0 =
      SPECL [t, mk_abs(y,xeqy)]
      RIGHT_FORALL_IMP_THM
    val pushy1 =
      CONV_RULE (LAND_CONV (QUANT_CONV (RAND_CONV BETA_CONV))) pushy0
    val pushy2 =
      CONV_RULE (RAND_CONV (RAND_CONV (QUANT_CONV BETA_CONV))) pushy1
    val exp6 =
      mCONV_RULE (RAND_CONV (QUANT_CONV (K pushy2))) exp5
    val pushx0 = SPECL [t, mk_abs(x, mk_forall(y,xeqy))]
                       RIGHT_FORALL_IMP_THM
    val pushx1 =
      CONV_RULE (LAND_CONV (QUANT_CONV (RAND_CONV BETA_CONV))) pushx0
    val pushx2 =
      CONV_RULE (RAND_CONV (RAND_CONV (QUANT_CONV BETA_CONV))) pushx1
    val exp7 =
      mCONV_RULE (RAND_CONV (K pushx2)) exp6
    val mp' = Thm.INST [p |-> t, q |-> list_mk_forall [x,y] xeqy] pseudo_mp
  in
    save_thm("UEXISTS_SIMP", mCONV_RULE (K mp') exp7)
  end
end


(*---------------------------------------------------------------------------
     The definition of restricted abstraction.
 ---------------------------------------------------------------------------*)

val RES_ABSTRACT_EXISTS =
  let
    fun B_CONV n = funpow n RATOR_CONV BETA_CONV
    fun RHS th = rhs (concl th)
    val p = Term `p : 'a -> bool`
    val m = Term `m : 'a -> 'b`
    val m1 = Term `m1 : 'a -> 'b`
    val m2 = Term `m2 : 'a -> 'b`
    val x = Term `x : 'a`
    val witness = Term `\p m x. if x IN p then ^m x else ARB x`
    val A1 = B_CONV 2 (Term `^witness ^p ^m ^x`)
    val A2 = TRANS A1 (B_CONV 1 (RHS A1))
    val A3 = TRANS A2 (BETA_CONV (RHS A2))
    val A4 = EQT_INTRO (ASSUME (Term `^x IN ^p`))
    val A5 = RATOR_CONV (RATOR_CONV (RAND_CONV (K A4))) (RHS A3)
    val A6 = INST_TYPE [alpha |-> beta] COND_CLAUSE1
    val A7 = SPECL [Term `^m ^x`, Term `ARB ^x : 'b`] A6
    val A8 = DISCH (Term `^x IN ^p`) (TRANS (TRANS A3 A5) A7)
    val A9 = GENL [Term `^p`, Term `^m`, Term `^x`] A8
    (* Completed the first clause of the definition *)
    val B1 = SPEC (Term `^x IN ^p`) EXCLUDED_MIDDLE
    val B2 = UNDISCH A8
    val B3 = INST [m |-> m1] B2
    val B4 = INST [m |-> m2] B2
    val B5 = SPEC_ALL (ASSUME (Term `!x. x IN ^p ==> (^m1 x = ^m2 x)`))
    val B6 = TRANS B3 (TRANS (UNDISCH B5) (SYM B4))
    val B7 = INST [m |-> m1] A3
    val B8 = INST [m |-> m2] A3
    val B9 = SYM (SPEC (Term `^x IN ^p`) EQ_CLAUSE4)
    val B10 = EQ_MP B9 (ASSUME (Term `~(^x IN ^p)`))
    val B11 = INST_TYPE [alpha |-> beta] COND_CLAUSE2
    val B12 = RATOR_CONV (RATOR_CONV (RAND_CONV (K B10))) (RHS B7)
    val B13 = TRANS B12 (SPECL [Term `^m1 ^x`, Term `ARB ^x : 'b`] B11)
    val B14 = RATOR_CONV (RATOR_CONV (RAND_CONV (K B10))) (RHS B8)
    val B15 = TRANS B14 (SPECL [Term `^m2 ^x`, Term `ARB ^x : 'b`] B11)
    val B16 = TRANS (TRANS B7 B13) (SYM (TRANS B8 B15))
    val B17 = DISJ_CASES B1 B6 B16
    val B18 = ABS x B17
    val B19 = CONV_RULE (RATOR_CONV (RAND_CONV ETA_CONV)) B18
    val B20 = CONV_RULE (RAND_CONV ETA_CONV) B19
    val B21 = DISCH (Term `!x. x IN ^p ==> (^m1 x = ^m2 x)`) B20
    val B22 = GENL [p, m1, m2] B21
    (* Cleaning up *)
    val C1 = CONJ A9 B22
    val C2 = EXISTS
      (Term `?f.
               (!p (m : 'a -> 'b) x. x IN p ==> (f p m x = m x)) /\
               (!p m1 m2.
                  (!x. x IN p ==> (m1 x = m2 x)) ==> (f p m1 = f p m2))`,
       Term `\p (m : 'a -> 'b) x. (if x IN p then m x else ARB x)`) C1
  in
    C2
  end;

val RES_ABSTRACT_DEF =
  Definition.new_specification
  ("RES_ABSTRACT_DEF", ["RES_ABSTRACT"], RES_ABSTRACT_EXISTS);

val _ = add_const "RES_ABSTRACT";
val _ = associate_restriction ("\\", "RES_ABSTRACT");


val (RES_FORALL_THM, RES_EXISTS_THM, RES_EXISTS_UNIQUE_THM, RES_SELECT_THM) =
    let
      val Pf = map (fn s => mk_var(s, alpha --> bool)) ["P", "f"]
      fun mk_eq th =
          GENL Pf (List.foldl (RIGHT_BETA o uncurry (C AP_THM)) th Pf)
    in
      (save_thm("RES_FORALL_THM", mk_eq RES_FORALL_DEF),
       save_thm("RES_EXISTS_THM", mk_eq RES_EXISTS_DEF),
       save_thm("RES_EXISTS_UNIQUE_THM", mk_eq RES_EXISTS_UNIQUE_DEF),
       save_thm("RES_SELECT_THM", mk_eq RES_SELECT_DEF))
    end


(* (!x::P. T) = T *)
val RES_FORALL_TRUE = let
  val x = mk_var("x", alpha)
  val T = concl TRUTH
  val KT = mk_abs(x, T)
  val P = mk_var("P", alpha --> bool)
  val th0 = SPECL[P,KT] RES_FORALL_THM
  val th1 = CONV_RULE (RAND_CONV (QUANT_CONV (RAND_CONV BETA_CONV))) th0
  val xINP_t = (rand o rator o #2 o dest_forall o rhs o concl) th1
  val timpT_th = List.nth(CONJUNCTS (SPEC xINP_t IMP_CLAUSES), 1)
  val th2 = CONV_RULE (RAND_CONV (QUANT_CONV (K timpT_th))) th1
in
  save_thm("RES_FORALL_TRUE", TRANS th2 (SPEC T FORALL_SIMP))
end

(* (?x::P. F) = F *)
val RES_EXISTS_FALSE = let
  val x = mk_var("x", alpha)
  val F = prim_mk_const{Thy = "bool", Name = "F"}
  val KF = mk_abs(x, F)
  val P = mk_var("P", alpha --> bool)
  val th0 = SPECL [P, KF] RES_EXISTS_THM
  val th1 = CONV_RULE (RAND_CONV (QUANT_CONV (RAND_CONV BETA_CONV))) th0
  val xINP_t = (rand o rator o #2 o dest_exists o rhs o concl) th1
  val tandF_th = List.nth(CONJUNCTS (SPEC xINP_t AND_CLAUSES), 3)
  val th2 = CONV_RULE (RAND_CONV (QUANT_CONV (K tandF_th))) th1
in
  save_thm("RES_EXISTS_FALSE", TRANS th2 (SPEC F EXISTS_SIMP))
end

(*---------------------------------------------------------------------------
     From Joe Hurd : case analysis on the (4) functions in the
     type :bool -> bool.

     val BOOL_FUN_CASES_THM =
     |- !f. (f = \b. T) \/ (f = \b. F) \/ (f = \b. b) \/ (f = \b. ~b)
 ---------------------------------------------------------------------------*)

val BOOL_FUN_CASES_THM =
 let val x       = mk_var("x",bool)
     val f       = mk_var("f",bool-->bool)
     val KF      = Term `\b:bool.F`
     val KT      = Term `\b:bool.T`
     val Ibool   = Term `\b:bool.b`
     val dual    = Term `\b. ~b`
     val fT      = mk_comb(f,T)
     val fF      = mk_comb(f,F)
     val fT_eq_T = mk_eq(fT,T)
     val fF_eq_T = mk_eq(fF,T)
     val fT_eq_F = mk_eq(fT,F)
     val fF_eq_F = mk_eq(fF,F)
     val final   = Term `(f = ^KT) \/ (f = ^KF) \/ (f = ^Ibool) \/ (f = ^dual)`
     val a0 = TRANS (ASSUME fT_eq_T) (SYM (BETA_CONV (mk_comb(KT,T))))
     val a1 = TRANS (ASSUME fF_eq_T) (SYM (BETA_CONV (mk_comb(KT,F))))
     val a2 = BOOL_CASE (Term`f x = ^KT x`) x x a0 a1
     val a3 = EXT (GEN x a2)
     val a  = DISJ1 a3 (Term`(f = \b. F) \/ (f = \b. b) \/ (f = \b. ~b)`)
     val b0 = TRANS (ASSUME fT_eq_F) (SYM (BETA_CONV (mk_comb(KF,T))))
     val b1 = TRANS (ASSUME fF_eq_F) (SYM (BETA_CONV (mk_comb(KF,F))))
     val b2 = BOOL_CASE (Term`f x = ^KF x`) x x b0 b1
     val b3 = EXT (GEN x b2)
     val b4 = DISJ1 b3 (Term`(f = ^Ibool) \/ (f = \b. ~b)`)
     val b  = DISJ2 (Term`f = ^KT`) b4
     val c0 = TRANS (ASSUME fT_eq_T) (SYM (BETA_CONV (mk_comb(Ibool,T))))
     val c1 = TRANS (ASSUME fF_eq_F) (SYM (BETA_CONV (mk_comb(Ibool,F))))
     val c2 = BOOL_CASE (Term`f x = ^Ibool x`) x x c0 c1
     val c3 = EXT (GEN x c2)
     val c4 = DISJ1 c3 (Term`f = ^dual`)
     val c5 = DISJ2 (Term `f = ^KF`) c4
     val c  = DISJ2 (Term `f = ^KT`) c5
     val d0 = TRANS (ASSUME fT_eq_F)
                (TRANS (SYM (CONJUNCT1 (CONJUNCT2 NOT_CLAUSES)))
                       (SYM (BETA_CONV (mk_comb(dual,T)))))
     val d1 = TRANS (ASSUME fF_eq_T)
               (TRANS (SYM (CONJUNCT2 (CONJUNCT2 NOT_CLAUSES)))
                      (SYM (BETA_CONV (mk_comb(dual,F)))))
     val d2 = BOOL_CASE (Term`f x = ^dual x`) x x d0 d1
     val d3 = EXT (GEN x d2)
     val d4 = DISJ2 (Term `f = ^Ibool`) d3
     val d5 = DISJ2 (Term `f = ^KF`) d4
     val d  = DISJ2 (Term`f = ^KT`) d5
     val ad0 = DISCH fT_eq_T a
     val ad1 = DISCH fT_eq_F d
     val ad2 = BOOL_CASE (Term `(f T = x) ==> ^final`) x x ad0 ad1
     val ad3 = SPEC fT (GEN x ad2)
     val ad  = MP ad3 (REFL fT)
     val bc0 = DISCH fT_eq_T c
     val bc1 = DISCH fT_eq_F b
     val bc2 = BOOL_CASE (Term `(f T = x) ==> ^final`) x x bc0 bc1
     val bc3 = SPEC fT (GEN x bc2)
     val bc  = MP bc3 (REFL fT)
     val abcd0 = DISCH fF_eq_T ad
     val abcd1 = DISCH fF_eq_F bc
     val abcd2 = BOOL_CASE (Term`(f F = x) ==> ^final`) x x abcd0 abcd1
     val abcd3 = SPEC fF (GEN x abcd2)
     val abcd  = MP abcd3 (REFL fF)
in
   GEN f abcd
end;

val _ = save_thm("BOOL_FUN_CASES_THM",BOOL_FUN_CASES_THM);


(*---------------------------------------------------------------------------
     Another from Joe Hurd : consequence of BOOL_FUN_CASES_THM

     BOOL_FUN_INDUCT =
     |- !P. P (\b. T) /\ P (\b. F) /\ P (\b. b) /\ P (\b. ~b) ==> !f. P f
 ---------------------------------------------------------------------------*)

  fun or_imp th0 =
    let val (disj1, disj2) = dest_disj (concl th0)
        val th1 = SYM (SPEC disj1 (CONJUNCT1 NOT_CLAUSES))
        val th2 = MK_COMB (REFL disjunction, th1)
        val th3 = MK_COMB (th2, REFL disj2)
        val th4 = EQ_MP th3 th0
        val th5 = SYM (SPECL [mk_neg disj1, disj2] IMP_DISJ_THM)
    in
      EQ_MP th5 th4
    end

  fun imp_and th0 =
    let val (ant, conseq) = dest_imp (concl th0)
      val (ant', conseq') = dest_imp conseq
      val th1 = SPECL [ant, ant', conseq'] AND_IMP_INTRO
    in
      EQ_MP th1 th0
    end


val BOOL_FUN_INDUCT =
 let val f = mk_var("f",bool-->bool)
     val g = mk_var("g",bool-->bool)
     val f_eq_g = mk_eq(f,g)
     val P = mk_var("P",(bool-->bool) --> bool)
     val KF    = Term `\b:bool.F`
     val KT    = Term `\b:bool.T`
     val Ibool = Term `\b:bool.b`
     val dual  = Term `\b. ~b`
     val f0 = ASSUME (mk_neg(mk_comb(P,f)))
     val f1 = ASSUME (mk_neg(mk_neg(f_eq_g)))
     val f2 = EQ_MP (SPEC f_eq_g (CONJUNCT1 NOT_CLAUSES)) f1
     val f3 = MK_COMB (REFL P, f2)
     val f4 = MK_COMB (REFL negation, f3)
     val f5 = UNDISCH (NOT_ELIM (EQ_MP f4 f0))
     val f6 = CCONTR (mk_neg(f_eq_g)) f5
     val f7  = GEN g (DISCH (mk_comb(P,g)) f6)
     val a0 = SPEC f BOOL_FUN_CASES_THM
     val a1 = MP (or_imp a0) (UNDISCH (SPEC KT f7))
     val a2 = MP (or_imp a1) (UNDISCH (SPEC KF f7))
     val a3 = MP (or_imp a2) (UNDISCH (SPEC Ibool f7))
     val a  = MP (NOT_ELIM (UNDISCH (SPEC dual f7))) a3
     val b0 = CCONTR (mk_comb(P,f)) a
     val b1 = GEN f b0
     val b2 = DISCH (mk_comb(P,dual)) b1
     val b3 = imp_and (DISCH (mk_comb(P,Ibool)) b2)
     val b4 = imp_and (DISCH (mk_comb(P,KF)) b3)
     val b  = imp_and (DISCH (mk_comb(P,KT)) b4)
in
   GEN P b
end;

val BOOL_FUN_INDUCT = save_thm("BOOL_FUN_INDUCT",BOOL_FUN_INDUCT);


(*---------------------------------------------------------------------------
     literal_case_THM = |- !f x. literal_case f x = f x
 ---------------------------------------------------------------------------*)

val literal_case_THM =
 let val f = ``f:'a->'b``
     val x = ``x:'a``
 in
  GEN f (GEN x
    (RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM literal_case_DEF f)) x)))
 end;

val _ = save_thm("literal_case_THM", literal_case_THM);


(*---------------------------------------------------------------------------*)
(*    literal_case_RAND =                                                    *)
(*        |- P (literal_case (\x. N x) M) = (literal_case (\x. P (N x)) M)   *)
(*---------------------------------------------------------------------------*)

val literal_case_RAND = save_thm("literal_case_RAND",
 let val tm1 = Term`\x:'a. P (N x:'b):bool`
     val tm2 = Term`M:'a`
     val tm3 = Term`\x:'a. N x:'b`
     val P   = Term`P:'b -> bool`
     val literal_case_THM1 = RIGHT_BETA (SPEC tm2 (SPEC tm1
                    (Thm.INST_TYPE [beta |-> bool] literal_case_THM)))
     val literal_case_THM2 = AP_TERM P (RIGHT_BETA (SPEC tm2 (SPEC tm3 literal_case_THM)))
 in TRANS literal_case_THM2 (SYM literal_case_THM1)
 end);


(*---------------------------------------------------------------------------*)
(*    literal_case_RATOR =                                                   *)
(*         |- (literal_case (\x. N x) M) b = (literal_case (\x. N x b) M)    *)
(*---------------------------------------------------------------------------*)

val literal_case_RATOR = save_thm("literal_case_RATOR",
 let val M = Term`M:'a`
     val b = Term`b:'b`
     val tm1 = Term`\x:'a. N x:'b->'c`
     val tm2 = Term`\x:'a. N x ^b:'c`
     val literal_case_THM1 = AP_THM (RIGHT_BETA (SPEC M (SPEC tm1
                   (Thm.INST_TYPE [beta |-> (beta --> gamma)] literal_case_THM)))) b
     val literal_case_THM2 = RIGHT_BETA (SPEC M (SPEC tm2
                      (Thm.INST_TYPE [beta |-> gamma] literal_case_THM)))
 in TRANS literal_case_THM1 (SYM literal_case_THM2)
 end);


(*---------------------------------------------------------------------------
  literal_case_CONG =
    |- !f g M N.  (M = N) /\ (!x. (x = N) ==> (f x = g x))
                            ==>
                   (literal_case f M = literal_case g N)
 ---------------------------------------------------------------------------*)

val literal_case_CONG =
  let val f = mk_var("f",alpha-->beta)
      val g = mk_var("g",alpha-->beta)
      val M = mk_var("M",alpha)
      val N = mk_var("N",alpha)
      val x = mk_var ("x",alpha)
      val MeqN = mk_eq(M,N)
      val x_eq_N = mk_eq(x,N)
      val fx_eq_gx = mk_eq(mk_comb(f,x),mk_comb(g,x))
      val ctm = mk_forall(x, mk_imp(x_eq_N,fx_eq_gx))
      val th  = RIGHT_BETA(AP_THM(RIGHT_BETA(AP_THM literal_case_DEF f)) M)
      val th1 = ASSUME MeqN
      val th2 = MP (SPEC N (ASSUME ctm)) (REFL N)
      val th3 = SUBS [SYM th1] th2
      val th4 = TRANS (TRANS th th3) (MK_COMB (REFL g,th1))
      val th5 = RIGHT_BETA(AP_THM(RIGHT_BETA(AP_THM literal_case_DEF g)) N)
      val th6 = TRANS th4 (SYM th5)
      val th7 = SUBS [SPECL [MeqN, ctm, concl th6] AND_IMP_INTRO]
                     (DISCH MeqN (DISCH ctm th6))
  in
    GENL [f,g,M,N] th7
  end;

val _ = save_thm("literal_case_CONG", literal_case_CONG);

(*---------------------------------------------------------------------------*)
(* Sometime useful rewrite, but you will want a higher-order version.        *)
(*  |- literal_case (\x. bool_case t u (x=a)) a = t                          *)
(*---------------------------------------------------------------------------*)

val literal_case_id = save_thm
("literal_case_id",
 let val a = mk_var("a", alpha)
    val x = mk_var("x", alpha)
    val t = mk_var("t",beta)
    val u = mk_var("u",beta)
    val eq = mk_eq(x,a)
    val bcase = inst [alpha |-> beta]
                     (prim_mk_const{Name = "COND",Thy="bool"})
    val g = mk_abs(x,list_mk_comb(bcase,[eq, t, u]))
    val lit_thm = RIGHT_BETA(SPEC a (SPEC g literal_case_THM))
    val Teq = SYM (EQT_INTRO(REFL a))
    val ifT = CONJUNCT1(SPECL[t,u] (INST_TYPE[alpha |-> beta] COND_CLAUSES))
    val ifeq = SUBS [Teq] ifT
 in
    TRANS lit_thm ifeq
 end);

(*---------------------------------------------------------------------------
         Support for parsing "case" expressions
 ---------------------------------------------------------------------------*)

val _ = new_constant(GrammarSpecials.case_special,
                     Type`:'a -> ('a -> 'b) -> 'b`);
val _ = new_constant(GrammarSpecials.case_split_special,
                     Type`:('a -> 'b) -> ('a -> 'b) -> 'a -> 'b`);
val _ = new_constant(GrammarSpecials.case_arrow_special,
                     Type`:'a -> 'b -> 'a -> 'b`);

val _ = let open GrammarSpecials
        in app add_const [case_special, case_split_special,
                          case_arrow_special]
        end

val _ = add_rule{pp_elements = [HardSpace 1, TOK "=>", BreakSpace(1,2)],
                 fixity = Infixr 10,
                 block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                 paren_style = OnlyIfNecessary,
                 term_name = GrammarSpecials.case_arrow_special}

val _ = add_rule{pp_elements = [PPBlock([TOK "case", BreakSpace(1,2),
                                         TM, BreakSpace(1,2), TOK "of"],
                                        (PP.CONSISTENT, 0)),
                                BreakSpace(1,2)],
                 fixity = Prefix 1,
                 block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                 paren_style = Always,
                 term_name = GrammarSpecials.case_special};

val _ = add_rule{pp_elements = [PPBlock([TOK "case", BreakSpace(1,2),
                                         TM, BreakSpace(1,2), TOK "of"],
                                        (PP.CONSISTENT, 0)),
                                BreakSpace(1,2), TM, BreakSpace(1,0),
                                TOK "|", HardSpace 1],
                 fixity = Prefix 1,
                 block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                 paren_style = Always,
                 term_name = GrammarSpecials.case_special};

val _ = add_rule{pp_elements = [PPBlock([TOK "case", BreakSpace(1,2),
                                         TM, BreakSpace(1,2), TOK "of"],
                                        (PP.CONSISTENT, 0)),
                                TOK "|", HardSpace 1],
                 fixity = Prefix 1,
                 block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                 paren_style = Always,
                 term_name = GrammarSpecials.case_special};


val _ = add_rule{pp_elements = [PPBlock([TOK "case", BreakSpace(1,2),
                                         TM, BreakSpace(1,2), TOK "of"],
                                        (PP.CONSISTENT, 0)),
                                BreakSpace(1,2), TM, BreakSpace(1,0),
                                TOK "|", HardSpace 1, TM, BreakSpace(1,0),
                                TOK "|", HardSpace 1],
                 fixity = Prefix 1,
                 block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                 paren_style = Always,
                 term_name = GrammarSpecials.case_special};




val BOUNDED_THM =
    let val v = Term `v:bool`
    in
      GEN v (RIGHT_BETA(AP_THM BOUNDED_DEF v))
    end;

val _ = save_thm("BOUNDED_THM", BOUNDED_THM);

(*---------------------------------------------------------------------------*)
(* LCOMM_THM : derive "left-commutativity" from associativity and            *)
(* commutativity. Used in permutative rewriting, e.g., simpLib entrypoints   *)
(*                                                                           *)
(*  LCOMM_THM  |- !f. (!x y. f x y = f y x) ==>                              *)
(*                    (!x y z. f x (f y z) = f (f x y) z) ==>                *)
(*                    (!x y z. f x (f y z) = f y (f x z))                    *)
(*---------------------------------------------------------------------------*)

val LCOMM_THM = save_thm("LCOMM_THM",
 let val x = mk_var("x",alpha)
     val y = mk_var("y",alpha)
     val z = mk_var("z",alpha)
     val f = mk_var("f",alpha --> alpha --> alpha)
     val comm = Term`!x y. ^f x y = f y x`
     val assoc = Term`!x y z. ^f x (f y z) = f (f x y) z`
     val comm_thm = ASSUME comm
     val assoc_thm = ASSUME assoc
     val th0 = SPEC (list_mk_comb(f,[y,z])) (SPEC x comm_thm)
     val th1 = SYM (SPECL [y,z,x] assoc_thm)
     val th2 = TRANS th0 th1
     val th3 = AP_TERM (mk_comb(f,y)) (SPECL[z,x] comm_thm)
 in
   GEN f (DISCH assoc (DISCH comm (GENL [x,y,z] (TRANS th2 th3))))
 end);


val DATATYPE_TAG_THM = save_thm("DATATYPE_TAG_THM",
    let val x = mk_var("x",alpha)
    in GEN x (RIGHT_BETA (AP_THM DATATYPE_TAG_DEF x))
    end);


val DATATYPE_BOOL = save_thm("DATATYPE_BOOL",
 let val thm1 = INST_TYPE [alpha |-> bool] DATATYPE_TAG_THM
     val bvar = mk_var("bool",bool--> bool-->bool)
 in
    SPEC (list_mk_comb(bvar,[T,F])) thm1
 end);

(* ----------------------------------------------------------------------
    Set up the "itself" type constructor and its one value
   ---------------------------------------------------------------------- *)

val ITSELF_TYPE_DEF = let
  val itself_exists = SPEC (Term`ARB:'a`) EXISTS_REFL
  val eq_sym_eq' =
      AP_TERM (Term`$? :('a -> bool) -> bool`)
              (ABS (Term`x:'a`) (SPECL [Term`x:'a`, Term`ARB:'a`] EQ_SYM_EQ))
in
  new_type_definition("itself", EQ_MP eq_sym_eq' itself_exists)
end
val _ = add_type "itself"

val _ = new_constant("the_value", Type`:'a itself`)
val _ = add_const "the_value"

(* prove uniqueness of the itself value:
     |- !i:'a itself. i = (:'a)
*)
val ITSELF_UNIQUE = let
  val typedef_asm = ASSUME (#2 (dest_exists (concl ITSELF_TYPE_DEF)))
  val typedef_eq0 =
      AP_THM (INST_TYPE [beta |-> ``:'a itself``] TYPE_DEFINITION)
             ``$= (ARB:'a)``
  val typedef_eq0 = RIGHT_BETA typedef_eq0
  val typedef_eq = AP_THM typedef_eq0 ``rep:'a itself -> 'a``
  val typedef_eq = RIGHT_BETA typedef_eq
  val (typedef_11, typedef_onto) = CONJ_PAIR (EQ_MP typedef_eq typedef_asm)
  val onto' = INST [``x:'a`` |-> ``(rep:'a itself -> 'a) i``]
                   (#2 (EQ_IMP_RULE (SPEC_ALL typedef_onto)))
  val allreps_arb = let
    val ex' = EXISTS (``?x':'a itself. rep i = rep x':'a``, ``i:'a itself``)
                     (REFL ``(rep:'a itself -> 'a) i``)
  in
    SYM (MP onto' ex')
  end
  val allreps_repthevalue =
      TRANS allreps_arb
            (SYM (INST [``i:'a itself`` |-> ``bool$the_value``] allreps_arb))
  val all_eq_thevalue =
      GEN_ALL (MP (SPECL [``i:'a itself``, ``bool$the_value``] typedef_11)
                  allreps_repthevalue)
in
  save_thm("ITSELF_UNIQUE",
           CHOOSE (``rep:'a itself -> 'a``, ITSELF_TYPE_DEF) all_eq_thevalue)
end

(* prove a datatype axiom for the type, allowing definitions of the form
    f (:'a) = ...
*)
val itself_Axiom = let
  val witness = ``(\x:'b itself. e : 'a)``
  val fn_behaves = BETA_CONV  (mk_comb(witness, ``(:'b)``))
  val fn_exists = EXISTS (``?f:'b itself -> 'a. f (:'b) = e``, witness)
                  fn_behaves
in
  save_thm("itself_Axiom", GEN_ALL fn_exists)
end

(* prove induction *)
val itself_induction = let
  val pval = ASSUME ``P (:'a) : bool``
  val pi =
      EQ_MP (SYM (AP_TERM ``P:'a itself -> bool`` (SPEC_ALL ITSELF_UNIQUE)))
            pval
in
  save_thm("itself_induction", GEN_ALL (DISCH_ALL (GEN_ALL pi)))
end

(* define case operator *)
val itself_case_thm = let
  val witness = ``\(i:'a itself) (b:'b). b``
  val witness_applied1 = BETA_CONV (mk_comb(witness, ``(:'a)``))
  val witness_applied2 = RIGHT_BETA (AP_THM witness_applied1 ``b:'b``)
in
  new_specification("itself_case_thm",
                    ["itself_case"],
                    EXISTS (``?f:'a itself -> 'b -> 'b. !b. f (:'a) b = b``,
                            witness)
                           (GEN_ALL witness_applied2))
end


(*---------------------------------------------------------------------------*)
(* Pulling FORALL and EXISTS up through /\ and ==>                           *)
(*---------------------------------------------------------------------------*)

local
  val flip = INST [Pb |-> Qb, Qab |-> Pab]
  val PULL_EXISTS1 = LEFT_FORALL_IMP_THM |> SPEC_ALL |> SYM
  val PULL_EXISTS2 = LEFT_EXISTS_AND_THM |> SPEC_ALL |> SYM
  val PULL_EXISTS3 = RIGHT_EXISTS_AND_THM |> SPEC_ALL |> SYM |> flip
  val PULL_FORALL1 = RIGHT_FORALL_IMP_THM |> SPEC_ALL |> SYM |> flip
  val PULL_FORALL2 = LEFT_AND_FORALL_THM |> SPEC_ALL
  val PULL_FORALL3 = RIGHT_AND_FORALL_THM |> SPEC_ALL |> flip
in
  val PULL_EXISTS = save_thm("PULL_EXISTS",
    LIST_CONJ [PULL_EXISTS1, PULL_EXISTS2, PULL_EXISTS3] |> GENL [Pab, Qb])
  val PULL_FORALL = save_thm("PULL_FORALL",
    LIST_CONJ [PULL_FORALL1, PULL_FORALL2, PULL_FORALL3] |> GENL [Pab, Qb])
end

(*---------------------------------------------------------------------------*)
(* PEIRCE  =  |- ((P ==> Q) ==> P) ==> P                                     *)
(*---------------------------------------------------------------------------*)

val PEIRCE = save_thm
("PEIRCE",
 let val th1 = ASSUME ``(P ==> Q) ==> P``
     val th2 = ASSUME ``P:bool``
     val th3 = ASSUME ``~P``
     val th4 = MP th3 th2
     val th5 = MP (SPEC ``Q:bool`` FALSITY) th4
     val th6 = DISCH ``P:bool`` th5
     val th7 = MP th1 th6
     val th8 = MP th3 th7
     val th9 = DISCH ``~P`` th8
     val th10 = MP (SPEC ``~P`` IMP_F) th9
     val th11 = SUBS [SPEC ``P:bool`` (CONJUNCT1 NOT_CLAUSES)] th10
 in
   DISCH ``(P ==> Q) ==> P`` th11
 end);

(* ----------------------------------------------------------------------
    JRH_INDUCT_UTIL : !P t. (!x. (x = t) ==> P x) ==> $? P

    Used multiple times in places relevant to inductive definitions and/or
    algebraic types.
   ---------------------------------------------------------------------- *)

val JRH_INDUCT_UTIL = let
  val asm_t = ``!x:'a. (x = t) ==> P x``
  val asm = ASSUME asm_t
  val t = ``t:'a``
  val P = ``P : 'a -> bool``
  val Pt = MP (SPEC t asm) (REFL t)
  val ExPx = EXISTS (``?x:'a. P x``, t) Pt
  val P_eta = SPEC P (INST_TYPE [beta |-> bool] ETA_AX)
  val ExP_eta = AP_TERM ``(?) : ('a -> bool) -> bool`` P_eta
in
  save_thm("JRH_INDUCT_UTIL", GENL [P, t] (DISCH asm_t (EQ_MP ExP_eta ExPx)))
end

(* Parsing additions *)
(* iff *)
val _ = overload_on ("<=>", ``(=) : bool -> bool -> bool``)
val _ = set_fixity "<=>" (Infix(NONASSOC, 100))
val _ = unicode_version {u = UChar.iff, tmnm = "<=>"}
val _ = TeX_notation {hol = "<=>", TeX = ("\\HOLTokenEquiv{}",2)}
val _ = TeX_notation {hol = UChar.iff, TeX = ("\\HOLTokenEquiv{}",2)}

(* not equal *)
val _ = overload_on ("<>", ``\x:'a y:'a. ~(x = y)``)
val _ = set_fixity "<>" (Infix(NONASSOC, 450))
val _ = TeX_notation {hol="<>", TeX = ("\\HOLTokenNotEqual{}",1)}

val _ = uset_fixity UChar.neq (Infix(NONASSOC, 450))
val _ = uoverload_on (UChar.neq, ``\x:'a y:'a. ~(x = y)``)
val _ = TeX_notation {hol=UChar.neq, TeX = ("\\HOLTokenNotEqual{}",1)}

(* not an element of *)
val _ = overload_on ("NOTIN", ``\x:'a y:('a -> bool). ~(x IN y)``)
val _ = set_fixity "NOTIN" (Infix(NONASSOC, 425))
val _ = unicode_version {u = UChar.not_elementof, tmnm = "NOTIN"}
val _ = TeX_notation {hol="NOTIN", TeX = ("\\HOLTokenNotIn{}",1)}
val _ = TeX_notation {hol=UChar.not_elementof,
                      TeX = ("\\HOLTokenNotIn{}",1)}

(* not iff *)
val _ = overload_on ("<=/=>", ``$<> : bool -> bool -> bool``)
val _ = set_fixity "<=/=>" (Infix(NONASSOC, 100))
val _ = unicode_version {u = UChar.not_iff, tmnm = "<=/=>"}
val _ = TeX_notation {hol="<=/=>", TeX = ("\\HOLTokenNotEquiv{}",2)}
val _ = TeX_notation {hol=UChar.not_iff,
                      TeX = ("\\HOLTokenNotEquiv{}",2)}

val _ = export_theory();

end (* boolScript *)
