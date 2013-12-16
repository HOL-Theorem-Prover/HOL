(* File: totoTacs.sml. Author: F. Lockwood Morris. Begun 25 Oct. 2012.    *)
(* Revised 23 Sept 2013 to include treatment of type int. *)
(* Revised 12 Dec. 2013 to suit HOL-Kananaskis 9. *)

(* Conversions for evaluating expressions of type cpn, that is three-way
   comparisons, typically of the form f x y, where f:t->t->cpn satisfies
   TotOrd, more particularly of the form apto g x y, with g:t toto for
   some type t. *)

structure totoTacs :> totoTacs =
struct
(*
app load ["totoTheory", "pred_setLib", "bossLib",
          "reduceLib", "relationTheory", "stringLib"];
*)
open Parse HolKernel boolLib bossLib;

val _ = set_trace "Unicode" 0;
open totoTheory reduceLib relationTheory
     listTheory pairTheory optionTheory pred_setLib stringLib;

val AR = ASM_REWRITE_TAC [];
fun ulist x = [x];

val ERR = mk_HOL_ERR "totoTacs";

(* At least for composing conversions, Hol's MATCH_MP is prone to yield
  generality that we don't want, by introducing variants of variables
  when it is sound to do so. Relying again on PART_MATCH, we devise a
  plain version to suit our needs. *)

fun PURE_MATCH_MP f x = MP (PART_MATCH (rand o rator) f (concl x)) x;

(* As I understand it, results from PART_MATCH never have quantifiers,
   and we need only preserve the same for all products of conversions. *)

(* seem to need a tripartite equivalent of illegitimate REWR cpn_case_def
   (to avoid searching the whole term with REWRITE_CONV) *)

val [LESS_REWR, EQUAL_REWR, GREATER_REWR] = CONJUNCTS cpn_case_def;

(* LESS_REWR = |- !v0 v1 v2.
         (case LESS of LESS -> v0 || EQUAL -> v1 || GREATER -> v2) = v0
   EQUAL_REWR = |- !v0 v1 v2.
         (case EQUAL of LESS -> v0 || EQUAL -> v1 || GREATER -> v2) = v1
   GREATER_REWR = |- !v0 v1 v2.
         (case GREATER of LESS -> v0 || EQUAL -> v1 || GREATER -> v2) = v2 *)

val cpn_REWR_CONV = REWR_CONV LESS_REWR ORELSEC REWR_CONV EQUAL_REWR ORELSEC
                    REWR_CONV GREATER_REWR ORELSEC
(fn _ => Raise (mk_HOL_ERR "rbtTacs" "cpn_REWR_CONV" "not a case cpn of ..."));

(* *********************************************************************** *)
(* ****             Getting to toto-deciding conversions.             **** *)
(* *********************************************************************** *)

(* Given 
    lin_ord_thm: |- LinearOrder phi;
    toto_of_thm: |- cmp = toto_of_LinearOrder phi;
    eq_conv: reduces equations of ground terms (of phi's arg. type) to T/F;
    lo_conv: reduces terms c phi c' to T/F;

   we expect
               toto_CONV lin_ord_thm toto_of_thm eq_conv lo_conv

   to be a conversion that will reduce terms  apto cmp c c'
   to LESS/EQUAL/GREATER. *)

val var1 = mk_var ("_z", Type`:bool`); (* supposedly not an identifier *)

fun toto_CONV lin_ord_thm toto_of_thm eq_conv lo_conv =
let val phi = snd (dest_comb (concl lin_ord_thm));
    (* val cmp = fst (dest_eq (concl toto_of_thm)); *)
    val cj = CONJ lin_ord_thm toto_of_thm;
    val eq_thm  = PURE_MATCH_MP toto_equal_imp cj
    and uneq_thm = PURE_MATCH_MP toto_unequal_imp cj
in fn (t:term) => (* supposed to have the form apto cmp t1 t2 *)
     let val (t1, t2) = (rand (rator t), rand t);
         val eq_verdict = eq_conv (mk_eq (t1, t2))
     in PURE_MATCH_MP eq_thm eq_verdict
        handle _ => 
        let val cond = PURE_MATCH_MP uneq_thm eq_verdict;
        (* cond = `if phi x y then ... = LESS else ... = GREATER` *)
            val (phi12, arm1, arm2) = dest_cond (concl cond);
            val subst_res = SUBST [var1 |-> lo_conv phi12]
                                   (mk_cond (var1, arm1, arm2))
                                   cond
        in CONV_RULE COND_CONV subst_res end end end;

(* ** However, we don't obtain numto, or any specific order, by toto_CONV: ** *)

(* ***************************************************************** *)
(*                              numto_CONV                           *)
(* ***************************************************************** *)

(* imitate equality checks for nums, chars, strings from stringLib *)

val refl_clause_num = MATCH_MP TO_refl TO_numOrd;

(* refl_clause_num = |- !x. numOrd x x = EQUAL *)

val TLA_ZERO = GSYM arithmeticTheory.ALT_ZERO;

val num_pre_CONV =  REWR_CONV arithmeticTheory.NUMERAL_DEF ORELSEC
                    REWR_CONV TLA_ZERO ORELSEC
                    ALL_CONV;

val numeral_lt_CONV = BINOP_CONV num_pre_CONV THENC
                      REWRITE_CONV [numeralTheory.numeral_lt];

val numeralOrd_CONV = BINOP_CONV num_pre_CONV THENC
                      PURE_REWRITE_CONV [numeralOrd, cpn_case_def];

fun numOrd_CONV t =
 let val (Na, Nb) = dest_binop (Term`numOrd`)
                    (ERR "numOrd_CONV" "not a numOrd N N' comparison") t
 in if Na = Nb then SPEC Na refl_clause_num else
  let val eqn = numeralOrd_CONV t;
      val ans = rand (concl eqn)
  in if is_const ans andalso type_of ans = Type`:cpn` then eqn else
            Raise (ERR "numOrd_CONV" "not a numOrd test")
 end end;

val numto_CONV = 
RATOR_CONV (RATOR_CONV (REWR_CONV apnumto_thm)) THENC
                 numOrd_CONV;

fun charOrd_CONV t =
 let val (Ca, Cb) = dest_binop (Term`charOrd`)
                    (ERR "charOrd_CONV" "not a charOrd C C' comparison") t;
     val (a, b) = (rand Ca, rand Cb);
     val dictum = numOrd_CONV (mk_comb (mk_comb (Term`numOrd`, a), b));
     val outcome = rand (concl dictum)
 in if outcome = Term`EQUAL` then PURE_MATCH_MP charOrd_eq_lem dictum
    else if outcome = Term`LESS` then
    let val bless = numeral_lt_CONV (mk_comb (mk_comb (Term`($<):num reln`, b),
                                              Term`256`))
    in PURE_MATCH_MP (PURE_MATCH_MP charOrd_lt_lem dictum) bless end
    else if outcome = Term`GREATER` then
    let val aless = numeral_lt_CONV (mk_comb (mk_comb (Term`($<):num reln`, a),
                                              Term`256`))
    in PURE_MATCH_MP (PURE_MATCH_MP charOrd_gt_lem dictum) aless end
    else Raise (ERR "charOrd_CONV" "not a good character comparison")
 end;

val charto_CONV = RATOR_CONV (RATOR_CONV (REWR_CONV apcharto_thm)) THENC
                 charOrd_CONV;

(* ********* qk_numto_CONV similar to numto_CONV: *********** *)

val refl_clause_qk_num = MATCH_MP TO_refl TO_qk_numOrd;

val qk_numeralOrd_CONV = BINOP_CONV num_pre_CONV THENC
                         PURE_REWRITE_CONV [qk_numeralOrd, cpn_case_def];

fun qk_numOrd_CONV t =
 let val (Na, Nb) = dest_binop (Term`qk_numOrd`)
                    (ERR "qk_numOrd_CONV" "not a qk_numOrd N N' comparison") t
 in if Na = Nb then SPEC Na refl_clause_qk_num else
  let val eqn = qk_numeralOrd_CONV t;
      val ans = rand (concl eqn)
  in if is_const ans andalso type_of ans = Type`:cpn` then eqn else
            Raise (ERR "qk_numOrd_CONV" "not a qk_numOrd test")
 end end;

val qk_numto_CONV = 
RATOR_CONV (RATOR_CONV (REWR_CONV ap_qk_numto_thm)) THENC
                 qk_numOrd_CONV;

(* ******************************************************************** *)
(* **********                lextoto_CONV                     ********* *)
(* ******************************************************************** *)

(* lextoto_CONV expects two conversions, say Ato_CONV, Bto_CONV for computing
   orders Ato, Bto, and a term (apto (lextoto Ato Bto) (a1, b1) (a2, b2)).
   Tests follow declaration of stringto_CONV below. *)

fun lextoto_CONV Aconv Bconv =
REWR_CONV aplextoto THENC
RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV Aconv))) THENC
     ((REWR_CONV EQUAL_REWR THENC Bconv) ORELSEC
      REWR_CONV LESS_REWR ORELSEC REWR_CONV GREATER_REWR);

(* ***** listoto_CONV should also be easily developed from aplistoto; ***** *)
(* ***** it expects one conversion (for elements) as first argument,  ***** *)
(* *** and a term argument of the form (apto (listtoto elem_CONV) l1 l2) ** *)

val [lsnn, lsnc, lscn, lscc] = map GEN_ALL (CONJUNCTS (SPEC_ALL aplistoto));

(* lsnn = |- !c. apto (listoto c) [] [] = EQUAL
   lsnc = |- !c b y. apto (listoto c) [] (b::y) = LESS
   lscn = |- !c a x. apto (listoto c) (a::x) [] = GREATER
   lscc = |- !c a x b y. apto (listoto c) (a::x) (b::y) =
         case apto c a b of
            LESS -> LESS
         || EQUAL -> apto (listoto c) x y
         || GREATER -> GREATER *)

fun listoto_CONV elem_conv =
 let fun lis_c t =
 ((REWR_CONV lscc THENC 
   RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV elem_conv))) THENC 
   ((REWR_CONV EQUAL_REWR THENC lis_c) ORELSEC
    REWR_CONV LESS_REWR ORELSEC REWR_CONV GREATER_REWR)) ORELSEC
  REWR_CONV lsnn ORELSEC REWR_CONV lsnc ORELSEC REWR_CONV lscn) t
 in lis_c ORELSEC (fn _ => Raise (ERR "listoto_CONV" "unsuitable args")) end;

(* ******* Type string treated as synonymous with char list ******* *)

val refl_clause_string = MATCH_MP TO_refl
                         (ISPEC (Term`stringto`) TotOrd_apto);

fun stringto_CONV t = 
if rand (rator t) = rand t then SPEC (rand t) refl_clause_string else
 (RATOR_CONV (RATOR_CONV (RAND_CONV (REWR_CONV stringto))) THENC
  listoto_CONV charto_CONV) t;

(* ************ test cases, just to put everyone throught the motions:

numOrd_CONV (Term`numOrd 57 54`);

numto_CONV (Term`apto numto 6 6`);
numto_CONV (Term`apto numto 6 7`);
numto_CONV (Term`apto numto 8 7`);

charOrd_CONV (Term`charOrd (#"A") (#"B")`);
charOrd_CONV (Term`charOrd (#"A") (#"A")`);
charOrd_CONV (Term`charOrd (#"Z") (#"B")`);
charOrd_CONV (Term`charOrd (CHR 0) (CHR 0)`);

charto_CONV (Term`apto charto #"8" #"7"`);

val testn = Count.apply (numto_CONV o Term);

testn`apto numto 5 7`;
testn`apto numto 0 0`; 

val testc = Count.apply (charOrd_CONV o Term);

testc`charOrd #"A" #"B"`;
testc`charOrd #"<" #"<"`;
testc`charOrd #"a" #">"`;

qk_numOrd_CONV (Term`qk_numOrd 57 54`);  (* LESS *)

qk_numto_CONV (Term`apto qk_numto 6 6`); (* EQUAL *)
qk_numto_CONV (Term`apto qk_numto 6 7`); (* GREATER *)
qk_numto_CONV (Term`apto qk_numto 8 7`); (* GREATER *)

val lnC = listoto_CONV numto_CONV;
lnC (Term`apto (listoto numto) [5; 3; 7] [5; 3]`);
lnC (Term`apto (listoto numto) [5; 3; 7] [5; 3; 7]`);
lnC (Term`apto (listoto numto) [5; 3] [5; 3; 7]`);

stringto_CONV (Term`apto stringto "abcdefghijklmnopq" "abcdefghijklmnopr"`);
   stringto_CONV (Term`apto stringto "abc" "ab"`);
Count.apply string_EQ_CONV
  (Term`"abcdefghijklmnopqrstuvwxyz" = "abcdefghijklmnopqrstuvwxyzA"`);
(* last used 270 inference steps *)
Count.apply stringto_CONV (Term
 `apto stringto "abcdefghijklmnopqrstuvwxyz" "abcdefghijklmnopqrstuvwxyzA"`);
(* 1067 inference steps, not quite as good as the 772 steps from specially
   written stringOrd/stringto (under HOL-Kananaskis-8), but close enough. *)

val p1 = Term`(6, "ab")`;
val p2 = Term`(7, "ab")`;
val p3 = Term`(6, "ac")`;

val lexns = lextoto_CONV numto_CONV stringto_CONV;

lexns (Term`apto (numto lextoto stringto) ^p1 ^p2`);
lexns (Term`apto (numto lextoto stringto) ^p2 ^p1`);
lexns (Term`apto (numto lextoto stringto) ^p1 ^p3`);
lexns (Term`apto (numto lextoto stringto) ^p3 ^p1`);
lexns (Term`apto (numto lextoto stringto) ^p2 ^p3`);
lexns (Term`apto (numto lextoto stringto) ^p3 ^p2`);
lexns (Term`apto (numto lextoto stringto) ^p3 ^p3`);
*************** *)
end;
