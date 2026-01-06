(*****************************************************************************)
(* File: translateScript.sml                                                 *)
(* Author: James Reynolds                                                    *)
(*                                                                           *)
(* Provides theories and definitions for conversion between s-expressions    *)
(* and native HOL                                                            *)
(*****************************************************************************)

(*****************************************************************************)
(* Load files for interactive sessions                                       *)
(*****************************************************************************)

(*
val _ = app                                   (* load infrastructure         *)
 load
 ["sexp",
  "sexpTheory",
  "hol_defaxiomsTheory",
  "intLib","listLib","translateLib"];

quietdec := true;
use "translateScript.sml" handle _ => quietdec := false;
quietdec := false;
*)

(*****************************************************************************)
(* Load base theories                                                        *)
(*****************************************************************************)
Theory translate
Ancestors
  sexp arithmetic frac rat integer complex_rational intExtension
  combin hol_defaxioms rich_list list
Libs
  sexp intLib translateLib


(*****************************************************************************)
(* Start new theory "translate"                                              *)
(*****************************************************************************)

(*****************************************************************************)
(* General theorems for translation schemes (see add_translation_scheme) :   *)
(*     SEXP_REDUCE - A theorem of the following form, specialised to sexp:   *)
(*             |- !x. P x ==> M (L x) < M x /\ M (R x) < M x                 *)
(*     SEXP_TERMINAL - A theorem of the following form:                      *)
(*             |- P t = F                                                    *)
(*****************************************************************************)

val sexp_size_def =
    snd (TypeBase.size_of ``:sexp``) handle e =>
    sexpTheory.sexp_size_def;

Theorem SEXP_REDUCE:
      !x. (|= consp x) ==>
          sexp_size (car x) < sexp_size x /\
          sexp_size (cdr x) < sexp_size x
Proof
    Cases THEN RW_TAC arith_ss [sexp_size_def,car_def,
                                cdr_def,consp_def,ACL2_TRUE,t_def,nil_def]
QED

val SEXP_TERMINAL = save_thm("SEXP_TERMINAL",
    REWRITE_CONV [ACL2_TRUE,REWRITE_CONV [nil_def] ``consp nil``,consp_def]
    ``|= consp nil``);

(*****************************************************************************)
(* Induction over s-expressions, as performed by lists.                      *)
(*****************************************************************************)

Theorem sexp_list_ind:
      !P0 P1.
          (!x. P1 x ==> P0 x) /\
          (!x. (|= consp x) /\ P0 (cdr x) ==> P1 x) /\
          (!x. ~(|= consp x) ==> P1 x) ==>
               (!x. P0 x) /\ (!x. P1 x)
Proof
        REPEAT STRIP_TAC THEN Induct_on `x` THEN
        TRY (METIS_TAC [sexpTheory.ACL2_TRUE,sexpTheory.consp_def]) THEN
        PAT_ASSUM ``!x. ~p ==> q`` (K ALL_TAC) THEN
        REPEAT (FIRST_ASSUM MATCH_MP_TAC) THEN
        ASM_REWRITE_TAC [consp_def,cdr_def,EVAL ``|= t``] THEN
        METIS_TAC []
QED

(*****************************************************************************)
(* Extra encoding functions:                                                 *)
(*****************************************************************************)

Definition rat_def:   rat a = num (com a rat_0)
End

Definition bool_def:   (bool T = t) /\ (bool F = nil)
End

(*****************************************************************************)
(* Extra fix funtions:                                                       *)
(*                                                                           *)
(*****************************************************************************)

Definition fix_bool_def:   fix_bool x = if |= booleanp x then x else bool T
End

Definition fix_rat_def:   fix_rat x = if |= rationalp x then x else rat 0
End

Definition fix_char_def:
     fix_char x = if |= characterp x then x else chr #"a"
End

Definition fix_string_def:   fix_string x = if |= stringp x then x else str ""
End

(*****************************************************************************)
(* Decoding functions:                                                       *)
(*                                                                           *)
(* Inverse to ``num : complex_rational -> sexp``                             *)
(* Inverse to ``int : int -> sexp``                                          *)
(* Inverse to ``nat : num -> sexp``                                          *)
(* Inverse to ``rat : rat -> sexp``                                          *)
(* Inverse to ``bool : bool -> sexp``                                        *)
(* Inverse to ``chr : char -> sexp``                                         *)
(* Inverse to ``str : string -> sexp``                                       *)
(*****************************************************************************)

Definition sexp_to_com_def:
   (sexp_to_com (num a) = a) /\ (sexp_to_com _ = com_0)
End

Definition sexp_to_int_def:
   (sexp_to_int (num (com a b)) =
     if |= integerp (num (com a b))
        then (rat_nmr a) / (rat_dnm a) else 0) /\
   (sexp_to_int _ = 0)
End

Definition sexp_to_nat_def:
   sexp_to_nat a = if |= natp a then Num (sexp_to_int a) else 0
End

Definition sexp_to_rat_def:
   (sexp_to_rat (num (com a b)) =
     if |= rationalp (num (com a b)) then a else 0) /\
   (sexp_to_rat _ = 0)
End

Definition sexp_to_bool_def:   sexp_to_bool x = |= x
End

Definition sexp_to_char_def:
  (sexp_to_char (chr x) = x) /\
         (sexp_to_char _ = #"a")
End

Definition sexp_to_string_def:
  (sexp_to_string (str x) = x) /\
         (sexp_to_string _ = "")
End

(*****************************************************************************)
(* Encoding and decoding pairs                                               *)
(*                                                                           *)
(* pair         : ('a -> sexp) -> ('b -> sexp) -> ('a # 'b) -> sexp          *)
(* sexp_to_pair : (sexp -> 'a) -> (sexp -> 'a) -> sexp -> ('a # 'b)          *)
(* pairp        : (sexp -> bool) -> (sexp -> bool) -> sexp -> bool           *)
(* all_pair     : ('a -> bool) -> ('b -> bool) -> 'a # 'b -> bool            *)
(* fix_pair     : (sexp -> sexp) -> (sexp -> sexp) -> sexp -> sexp           *)
(*                                                                           *)
(* Eg:      pair nat int (1,2) = cons (nat 1) (int 2)                        *)
(*      and pairp (sexp_to_bool o natp) integerp (cons (nat 1) (int 2) = T   *)
(*****************************************************************************)

Definition pair_def:   pair f g p = cons (f (FST p)) (g (SND p))
End

val pair_thm = save_thm("pair_thm",
    GEN_ALL (REWRITE_RULE [pairTheory.FST,pairTheory.SND]
                (Q.SPECL [`f`,`g`,`(a,b)`] pair_def)));

Definition pairp_def:
  !f g. pairp f g x =
    if (|= consp x) then f (car x) /\ g (cdr x) else F
End

Definition sexp_to_pair_def:
  !f g x. sexp_to_pair f g x =
    if (|= consp x) then (f (car x),g (cdr x)) else (f nil,g nil)
End

Definition all_pair_def:   all_pair P1 P2 (a,b) = P1 a /\ P2 b
End

Definition fix_pair_def:   fix_pair f g x =
    if |= consp x then (cons (f (car x)) (g (cdr x))) else pair f g (nil,nil)
End

(*****************************************************************************)
(* Encoding and decoding lists                                               *)
(*                                                                           *)
(* list         : ('a -> sexp) -> 'a list -> sexp                            *)
(* sexp_to_list : (sexp -> 'a) -> sexp -> 'a list                            *)
(* listp        : (sexp -> bool) -> sexp -> bool                             *)
(*                                                                           *)
(* Eg:     list nat [1;2;3] = cons (nat 1) (cons (nat 2) (cons (nat 3) nil)) *)
(*     and listp (sexp_to_bool o natp)                                       *)
(*                    (cons (nat 1) (cons (nat 2) (cons (nat 3) nil))) = T   *)
(*****************************************************************************)

Definition list_def:
     (list f (x::xs) = cons (f x) (list f xs)) /\ (list f [] = nil)
End

val sexp_to_list_def =
    tDefine "sexp_to_list"
    `(sexp_to_list f (cons x xs) =
          (f x)::(sexp_to_list f xs)) /\
     (sexp_to_list f _ = [])`
    (WF_REL_TAC `measure (sexp_size o SND)` THEN
     RW_TAC arith_ss [sexp_size_def]);

Theorem sexp_to_list_thm:
    !f x. sexp_to_list f x =
          if (|= consp x)
             then let (a,b) = sexp_to_pair f (sexp_to_list f) x in (a::b)
             else []
Proof
        GEN_TAC THEN Induct THEN
        RW_TAC (std_ss ++ boolSimps.LET_ss)
                [sexp_to_list_def,consp_def,ACL2_TRUE,t_def,nil_def,
                 car_def,cdr_def,sexp_to_pair_def]
QED

Theorem list_thm:
    (!f x xs. list f (x::xs) = pair f (list f) (x,xs)) /\
    (!f. list f [] = nil)
Proof
        REWRITE_TAC [list_def,pair_def,pairTheory.FST,pairTheory.SND]
QED

val listp_def = tDefine "listp"
 `(listp f (cons a b) = f a /\ listp f b) /\
  (listp f x = (x = nil))`
 (WF_REL_TAC `measure (sexp_size o SND)` THEN
  RW_TAC arith_ss [sexp_size_def]);

Theorem listp_thm:
      !f g x. listp f x = if (|= consp x) then
                                pairp f (listp f) x else (x = list I [])
Proof
        NTAC 2 GEN_TAC THEN Induct THEN
        REWRITE_TAC [list_def,pairp_def,listp_def,consp_def,ACL2_TRUE,
                car_def,cdr_def,t_def,nil_def,sexp_distinct,sexp_11,
                EVAL ``"T" = "NIL"``]
QED

val fix_list_def =
    tDefine "fix_list"
    `(fix_list f (cons a b) = cons (f a) (fix_list f b)) /\
     (fix_list f x = list I [])`
    (WF_REL_TAC `measure (sexp_size o SND)` THEN
     RW_TAC arith_ss [sexp_size_def]);

Theorem fix_list_thm:
      !f x. fix_list f x =
         if pairp (K T) (K T) x then fix_pair f (fix_list f) x else list I []
Proof
    GEN_TAC THEN Induct THEN
    REWRITE_TAC [fix_list_def,fix_pair_def,consp_def,ACL2_TRUE,EVAL ``t = nil``,
                 car_def,cdr_def,pairp_def,K_THM]
QED

(*****************************************************************************)
(* Source theorem all_id: all (K T) ... (K T) = K T                          *)
(*     Should really be moved into the respective theories...                *)
(*****************************************************************************)

Theorem ALLID_PAIR:
      all_pair (K T) (K T) = K T
Proof
    REWRITE_TAC [FUN_EQ_THM] THEN Cases THEN
    REWRITE_TAC [K_THM,all_pair_def]
QED

Theorem ALLID_LIST:
      EVERY (K T) = K T
Proof
    REWRITE_TAC [FUN_EQ_THM] THEN Induct THEN
    ASM_REWRITE_TAC [EVERY_DEF,K_THM]
QED

val proves = ref ([]:(int * term) list);
val stores = ref ([]:(int * string) list);

fun prove (term,tactic) =
let     val start = Time.now();
        val proof = Tactical.prove(term,tactic);
        val end_t = Time.now();
        val diff = Time.toMilliseconds (Time.-(end_t,start))
in
        (proves := (diff,term) :: (!proves) ; proof)
end;

fun store_thm (string,term,tactic) =
let     val start = Time.now();
        val proof = Tactical.store_thm(string,term,tactic);
        val end_t = Time.now();
        val diff = Time.toMilliseconds (Time.-(end_t,start))
in
        (stores := (diff,string) :: (!stores) ; proof)
end;

(*****************************************************************************)
(* IS_INT_EXISTS :                                                           *)
(*                                                                           *)
(* |- !a b.                                                                  *)
(*      IS_INT (com a b) = (b = rat_0) /\ ?c. a = abs_rat (abs_frac (c,1))   *)
(*****************************************************************************)

val int_pos = prove(``0 < a ==> 0 < Num a``,
    METIS_TAC [INT_OF_NUM,INT_LT,INT_LT_IMP_LE]);

val int_mod_eq_thm = prove(
    ``0 < b ==> ((Num (ABS a) MOD Num b = 0) = (a % b = 0))``,
        ONCE_REWRITE_TAC [GSYM INT_EQ_CALCULATE] THEN
        RW_TAC std_ss [GSYM INT_MOD,int_pos,DECIDE ``0 < a ==> ~(a = 0n)``,
                       snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_LT_IMP_LE,
                       INT_ABS_POS] THEN
        RW_TAC int_ss [INT_ABS,INT_MOD_EQ0,INT_LT_IMP_NE] THEN
        EQ_TAC THEN STRIP_TAC THEN
        Q.EXISTS_TAC `~k` THEN
        intLib.ARITH_TAC);

val IS_INT_select = prove(
    ``!a b. IS_INT (com a b) ==> (b = rat_0) /\
         ?c. a = abs_rat (abs_frac(c,1))``,
    RW_TAC std_ss [IS_INT_def,DIVIDES_def,rat_nmr_def,rat_dnm_def,FRAC_DNMPOS,
                   INT_ABS_CALCULATE_POS,int_mod_eq_thm,INT_MOD_EQ0,
                   INT_LT_IMP_NE] THEN
    Q.EXISTS_TAC `rat_nmr a / rat_dnm a` THEN
    SUBGOAL_THEN ``?a'. a  = abs_rat a'`` (CHOOSE_THEN SUBST_ALL_TAC) THEN1
      (Q.EXISTS_TAC `rep_rat a` THEN MATCH_ACCEPT_TAC (GSYM ratTheory.RAT)) THEN
    RW_TAC int_ss [rat_nmr_def,rat_dnm_def,RAT_EQ,DNM,NMR,INT_LT_01,
                   INT_DIV_RMUL,FRAC_DNMPOS,INT_LT_IMP_NE] THEN
    SUBGOAL_THEN ``?c d. (a' = abs_frac (c,d)) /\ 0 < d`` STRIP_ASSUME_TAC THEN1
      (Q.EXISTS_TAC `frac_nmr a'` THEN Q.EXISTS_TAC `frac_dnm a'` THEN
    REWRITE_TAC [FRAC,FRAC_DNMPOS]) THEN
    RW_TAC std_ss [NMR,DNM] THEN
    RAT_CONG_TAC THEN
    PAT_ASSUM ``0i < d`` (fn th => (RULE_ASSUM_TAC
                    (SIMP_RULE std_ss [th,NMR,DNM]))) THEN
    PAT_ASSUM ``frac_nmr a = b * c:int`` SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [
            CONV_RULE bool_EQ_CONV (AC_CONV(INT_MUL_ASSOC,INT_MUL_COMM)
                      ``a * b * c = (a * c) * b:int``)]) THEN
    IMP_RES_TAC (fst (EQ_IMP_RULE (SPEC_ALL INT_EQ_RMUL))) THEN
    MP_TAC (SPEC ``x:frac`` FRAC_DNMPOS) THEN ASM_REWRITE_TAC [INT_LT_REFL]);

val IS_INT_eq = prove(``!a. IS_INT (com (abs_rat (abs_frac(a,1))) rat_0)``,
    RW_TAC std_ss [IS_INT_def,DIVIDES_def,rat_nmr_def,rat_dnm_def,FRAC_DNMPOS,
                   INT_ABS_CALCULATE_POS,int_mod_eq_thm,INT_LT_IMP_NE] THEN
    RAT_CONG_TAC THEN
    FULL_SIMP_TAC int_ss [NMR,DNM,INT_LT_01,INT_MOD_COMMON_FACTOR,INT_LT_IMP_NE,
                          FRAC_DNMPOS]);

Theorem IS_INT_EXISTS:
       !a b. IS_INT (com a b) = (b = rat_0) /\
                                ?c. a = abs_rat (abs_frac(c,1))
Proof
     METIS_TAC [IS_INT_select,IS_INT_eq]
QED

(*****************************************************************************)
(* Congruence theorems to make proofs easier...                              *)
(*****************************************************************************)

Theorem NAT_CONG:
      !a b. (nat a = nat b) = (a = b)
Proof
    RW_TAC intLib.int_ss [nat_def,int_def,cpx_def,sexpTheory.rat_def,
                          ratTheory.RAT_EQ,fracTheory.NMR,fracTheory.DNM]
QED

Theorem INT_CONG:
      !a b. (int a = int b) = (a = b)
Proof
    RW_TAC intLib.int_ss [nat_def,int_def,cpx_def,sexpTheory.rat_def,
                          ratTheory.RAT_EQ,fracTheory.NMR,fracTheory.DNM]
QED

Theorem BOOL_CONG:
      !a b. (bool a = bool b) = (a = b)
Proof
    REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN TRY AP_TERM_TAC THEN
    Cases_on `a` THEN Cases_on `b` THEN POP_ASSUM MP_TAC THEN
    RW_TAC std_ss [bool_def,nil_def,t_def]
QED

(*****************************************************************************)
(* Make sure all 'p' functions operate on |= instead of nil or t             *)
(*****************************************************************************)

val nil_t = CONV_RULE bool_EQ_CONV (EVAL ``~(nil = t)``);
val true_t = CONV_RULE bool_EQ_CONV (EVAL ``|= t``);
val false_f = CONV_RULE bool_EQ_CONV (EVAL ``~(|= nil)``);
val nil_nil = prove(``(x = nil) = ~|= x``,
    EQ_TAC THEN RW_TAC std_ss [false_f] THEN
    REPEAT (POP_ASSUM MP_TAC THEN
            RW_TAC std_ss [ACL2_TRUE_def,ite_def,equal_def,nil_t]));

val TRUTH_REWRITES = save_thm("TRUTH_REWRITES",LIST_CONJ
        (map (fn x =>
         prove(x,TRY (Cases_on `a`) THEN
                 RW_TAC std_ss [ite_def,nil_t,true_t,false_f,bool_def,
                                consp_def,AP_TERM ``consp`` nil_def,nil_nil]))
      [``~(nil = t)``,``(|= (if a then b else c)) = a /\ (|= b) \/ ~a /\ |= c``,
       ``(consp nil = nil)``,``ite nil a b = b``,``ite t a b = a``,
       ``(x = nil) = ~(|= x)``,``~(x = nil) = (|= x)``,``|= t``,``~(|= nil)``,
       ``(|= bool a) = a``]));

val ANDL_JUDGEMENT = prove(
    ``(|= andl []) /\ !a b. (|= a) /\ (|= andl b) ==> (|= andl (a::b))``,
    STRIP_TAC THENL [ALL_TAC,GEN_TAC THEN Induct] THEN
    RW_TAC std_ss [andl_def,TRUTH_REWRITES,ite_def]);

Theorem ANDL_REWRITE:
      !a b. (|= andl []) /\ ((|= andl (a::b)) = (|= a) /\ (|= andl b))
Proof
    GEN_TAC THEN Cases THEN RW_TAC std_ss [andl_def,TRUTH_REWRITES,ite_def]
QED

Theorem NOT_REWRITE:
      (|= not a) = ~|= a
ProofRW_TAC std_ss [not_def,TRUTH_REWRITES,ite_def]
QED

(*****************************************************************************)
(* Encode, detect, all theorems (ENCDETALL).                                 *)
(*****************************************************************************)

Theorem ENCDETALL_BOOL:
      (sexp_to_bool o  booleanp) o bool = K T
Proof
    REWRITE_TAC [FUN_EQ_THM] THEN
    Cases THEN RW_TAC std_ss [K_THM,ite_def,bool_def,booleanp_def,
          TRUTH_REWRITES,equal_def,sexp_to_bool_def]
QED

Theorem ENCDETALL_INT:
      (sexp_to_bool o integerp) o int = K T
Proof
    REWRITE_TAC [FUN_EQ_THM] THEN
    RW_TAC std_ss [integerp_def,int_def,cpx_def,IS_INT_EXISTS,TRUTH_REWRITES,
                   K_THM,sexpTheory.rat_def,rat_0_def,frac_0_def,
                   sexp_to_bool_def] THEN
    PROVE_TAC []
QED

 val natp_int_lem = prove(``(|= (natp (int x))) = 0 <= x``,
    RW_TAC arith_ss [natp_def,nat_def,
           REWRITE_RULE [o_THM,FUN_EQ_THM,sexp_to_bool_def] ENCDETALL_INT,
           TRUTH_REWRITES,andl_def,not_def,ite_def] THEN
    RW_TAC int_ss [int_def,less_def,cpx_def,TRUTH_REWRITES] THEN
    RW_TAC int_ss [sexpTheory.rat_def,RAT_LES_CALCULATE,NMR,DNM,INT_NOT_LT]);

Theorem ENCDETALL_NAT:
      (sexp_to_bool o natp) o nat = K T
Proof
    RW_TAC int_ss [nat_def,o_THM,FUN_EQ_THM,natp_int_lem,sexp_to_bool_def]
QED

Theorem ENCDETALL_RAT:
      (sexp_to_bool o  rationalp) o rat = K T
Proof
    RW_TAC std_ss [FUN_EQ_THM,o_THM,rationalp_def,rat_def,TRUTH_REWRITES,
                   sexp_to_bool_def]
QED

Theorem ENCDETALL_COM:
      (sexp_to_bool o acl2_numberp) o num = K T
Proof
    RW_TAC std_ss [acl2_numberp_def,TRUTH_REWRITES,K_THM,o_THM,
                   sexp_to_bool_def,FUN_EQ_THM]
QED

Theorem ENCDETALL_PAIR:
      (pairp p0 p1 o pair f0 f1) = all_pair (p0 o f0) (p1 o f1)
Proof
    REWRITE_TAC [FUN_EQ_THM,pair_def,pairp_def,o_THM] THEN Cases THEN
    REWRITE_TAC [o_THM,all_pair_def,consp_def,car_def,cdr_def,TRUTH_REWRITES]
QED

Theorem ENCDETALL_LIST:
      (listp p o list f) = EVERY (p o f)
Proof
    REWRITE_TAC [FUN_EQ_THM] THEN Induct THEN
    ASM_REWRITE_TAC [list_def,o_THM,EVERY_DEF,listp_def,nil_def] THEN
    PROVE_TAC [o_THM]
QED

Theorem ENCDETALL_CHAR:
      (sexp_to_bool o characterp) o chr = K T
Proof
    RW_TAC std_ss [sexp_to_bool_def,FUN_EQ_THM,o_THM,K_THM,characterp_def,
                   TRUTH_REWRITES]
QED

Theorem ENCDETALL_STRING:
      (sexp_to_bool o  stringp) o str = K T
Proof
    RW_TAC std_ss [sexp_to_bool_def,FUN_EQ_THM,o_THM,K_THM,
                   stringp_def,TRUTH_REWRITES]
QED

(*****************************************************************************)
(* Encode, decode, map (ENCDECMAP) proofs                                    *)
(*****************************************************************************)


local

(* Ugly patch by MJCG: was failing with the RAT_CONG_TAC in translateLib     *)
val RAT_CONG_TAC =
        REPEAT (POP_ASSUM MP_TAC) THEN
        REPEAT (Q.PAT_ABBREV_TAC
               `x''''' = rep_rat (abs_rat (abs_frac (a''''',b''''')))`) THEN
        REPEAT (DISCH_TAC) THEN
        EVERY_ASSUM (fn th =>
                    (ASSUME_TAC o Rewrite.REWRITE_RULE [ratTheory.RAT] o
                                  AP_TERM ``abs_rat``)
                    (Rewrite.REWRITE_RULE [markerTheory.Abbrev_def] th)
                    handle e => ALL_TAC) THEN
        RULE_ASSUM_TAC (Rewrite.REWRITE_RULE [ratTheory.RAT_EQ])

in

Theorem ENCDECMAP_INT:
      (sexp_to_int o int) = I
Proof
    REWRITE_TAC [FUN_EQ_THM,o_THM,I_THM] THEN
    RW_TAC int_ss [sexp_to_int_def,int_def,cpx_def,
                   sexpTheory.rat_def] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [GSYM int_def,GSYM cpx_def,
         GSYM sexpTheory.rat_def,REWRITE_RULE [FUN_EQ_THM,o_THM,
         sexp_to_bool_def] ENCDETALL_INT,K_THM]) THEN
    REWRITE_TAC [rat_nmr_def,rat_dnm_def] THEN
    RAT_CONG_TAC THEN
    POP_ASSUM MP_TAC THEN RW_TAC int_ss [NMR,DNM] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC INT_DIV_RMUL THEN
    PROVE_TAC [INT_POS_NZ,FRAC_DNMPOS]
QED

end;

Theorem ENCDECMAP_NAT:
      (sexp_to_nat o nat) = I
Proof
    RW_TAC int_ss [o_THM,sexp_to_nat_def,nat_def,natp_int_lem,FUN_EQ_THM,I_THM,
                   REWRITE_RULE [FUN_EQ_THM,I_THM,o_THM] ENCDECMAP_INT]
QED

Theorem ENCDECMAP_RAT:
      (sexp_to_rat o rat) = I
Proof
    RW_TAC int_ss [sexp_to_rat_def,rat_def,I_THM,o_THM,FUN_EQ_THM,
                   rationalp_def,TRUTH_REWRITES]
QED

Theorem ENCDECMAP_COM:
      (sexp_to_com o num) = I
Proof
    RW_TAC std_ss [FUN_EQ_THM,o_THM,I_THM,sexp_to_com_def]
QED

Theorem ENCDECMAP_PAIR:
      (sexp_to_pair f0 f1 o pair g0 g1) = ((f0 o g0) ## (f1 o g1))
Proof
    REWRITE_TAC [FUN_EQ_THM] THEN Cases THEN
    REWRITE_TAC [pairTheory.PAIR_MAP,pair_def,sexp_to_pair_def,o_THM,consp_def,
                 car_def,cdr_def,TRUTH_REWRITES]
QED

Theorem ENCDECMAP_LIST:
      (sexp_to_list f o list g) = MAP (f o g)
Proof
    REWRITE_TAC [FUN_EQ_THM] THEN Induct THEN
    ASM_REWRITE_TAC [MAP,o_THM,list_def,sexp_to_list_def,nil_def] THEN
    PROVE_TAC [o_THM]
QED

Theorem ENCDECMAP_BOOL:
      (sexp_to_bool o bool) = I
Proof
    REWRITE_TAC [FUN_EQ_THM,o_THM,I_THM] THEN
    Cases THEN RW_TAC std_ss [bool_def,sexp_to_bool_def,TRUTH_REWRITES]
QED

Theorem ENCDECMAP_CHAR:
      (sexp_to_char o chr) = I
Proof
    RW_TAC std_ss [sexp_to_char_def,FUN_EQ_THM,o_THM,I_THM]
QED

Theorem ENCDECMAP_STRING:
      (sexp_to_string o str) = I
Proof
    RW_TAC std_ss [sexp_to_string_def,FUN_EQ_THM,o_THM,I_THM]
QED

(*****************************************************************************)
(* Decode, Encode, Fix (DECENCFIX) theorems                                  *)
(*****************************************************************************)

Theorem DECENCFIX_BOOL:
      (bool o sexp_to_bool) = fix_bool
Proof
    RW_TAC int_ss [bool_def,sexp_to_bool_def,fix_bool_def,o_THM,FUN_EQ_THM,
                   ACL2_TRUE,booleanp_def,ite_def,equal_def] THEN
    Cases_on `x = nil` THEN RW_TAC arith_ss [bool_def] THEN
    PROVE_TAC []
QED

Theorem DECENCFIX_INT:
      (int o sexp_to_int) = ifix
Proof
    REWRITE_TAC [FUN_EQ_THM] THEN Cases THEN TRY (Cases_on `c`) THEN
    RW_TAC int_ss [ifix_def,sexp_to_int_def,o_THM,ite_def,nat_def,integerp_def,
                   ACL2_TRUE] THEN POP_ASSUM MP_TAC THEN
    RW_TAC int_ss [TRUTH_REWRITES] THEN IMP_RES_TAC IS_INT_EXISTS THEN
    RW_TAC int_ss [int_def,cpx_def,sexpTheory.rat_def,rat_0_def,frac_0_def,
                   rat_nmr_def,rat_dnm_def] THEN
    RAT_CONG_TAC THEN
    FULL_SIMP_TAC int_ss [DNM,NMR] THEN RW_TAC int_ss [] THEN
    REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
    MATCH_MP_TAC INT_DIV_RMUL THEN
    PROVE_TAC [INT_POS_NZ,FRAC_DNMPOS]
QED

Theorem DECENCFIX_NAT:
      (nat o sexp_to_nat) = nfix
Proof
    RW_TAC int_ss [nat_def,sexp_to_nat_def,FUN_EQ_THM,o_THM,nfix_def,natp_def,
                   ite_def,ISPEC ``int`` COND_RAND,
                   ISPEC ``$& : num -> int`` COND_RAND,ACL2_TRUE] THEN
    RW_TAC int_ss [ACL2_TRUE] THEN RES_TAC THEN
    POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
    RW_TAC int_ss [andl_def,ite_def,GSYM ACL2_TRUE,TRUTH_REWRITES] THEN
    `?c. x = int c` by Q.EXISTS_TAC `sexp_to_int x` THEN
    ASM_REWRITE_TAC [REWRITE_RULE [o_THM,FUN_EQ_THM] DECENCFIX_INT,ifix_def,
                     ite_def,TRUTH_REWRITES] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC int_ss [REWRITE_RULE [o_THM,FUN_EQ_THM] ENCDECMAP_INT] THEN
    POP_ASSUM MP_TAC THEN
    RW_TAC int_ss [int_def,less_def,cpx_def,sexpTheory.rat_def,not_def,
                   TRUTH_REWRITES,RAT_LES_CALCULATE,NMR,DNM] THEN
    PROVE_TAC [INT_OF_NUM,INT_NOT_LT]
QED

Theorem DECENCFIX_RAT:
      (rat o sexp_to_rat) = fix_rat
Proof
    REWRITE_TAC [FUN_EQ_THM] THEN Cases THEN TRY (Cases_on `c`) THEN
    REWRITE_TAC [fix_rat_def,rat_def,sexp_to_rat_def,o_THM,rationalp_def,
                 TRUTH_REWRITES,sexp_to_rat_def] THEN
    PROVE_TAC []
QED

Theorem DECENCFIX_COM:
      (num o sexp_to_com) = fix
Proof
    REWRITE_TAC [FUN_EQ_THM] THEN Cases THEN
    RW_TAC int_ss [fix_def,sexp_to_com_def,acl2_numberp_def,ite_def,
                   TRUTH_REWRITES,com_0_def,cpx_def,sexpTheory.rat_def,
                   rat_0_def,frac_0_def]
QED

Theorem DECENCFIX_CHAR:
      (chr o sexp_to_char) = fix_char
Proof
    REWRITE_TAC [FUN_EQ_THM] THEN Cases THEN
    REWRITE_TAC [sexp_to_char_def,o_THM,fix_char_def,characterp_def,
                 TRUTH_REWRITES]
QED

Theorem DECENCFIX_STRING:
      (str o sexp_to_string) = fix_string
Proof
    REWRITE_TAC [FUN_EQ_THM] THEN Cases THEN
    REWRITE_TAC [sexp_to_string_def,o_THM,fix_string_def,stringp_def,
                 TRUTH_REWRITES]
QED

Theorem DECENCFIX_PAIR:
      (pair f0 f1 o sexp_to_pair g0 g1) = fix_pair (f0 o g0) (f1 o g1)
Proof
    REWRITE_TAC [FUN_EQ_THM] THEN Cases THEN
    RW_TAC int_ss [fix_pair_def,o_THM,sexp_to_pair_def,pair_def]
QED

Theorem DECENCFIX_LIST:
      (list f o sexp_to_list g) = fix_list (f o g)
Proof
    REWRITE_TAC [FUN_EQ_THM] THEN Induct THEN
    RW_TAC int_ss [fix_list_def,sexp_to_list_def,list_def] THEN
    PROVE_TAC [o_THM]
QED

(*****************************************************************************)
(* Encode map encode (ENCMAPENC) fusion theorems.                            *)
(*****************************************************************************)

Theorem ENCMAPENC_LIST:
      list f o MAP g = list (f o g)
Proof
    REWRITE_TAC [FUN_EQ_THM] THEN Induct THEN
    REWRITE_TAC [o_THM,MAP,list_def] THEN METIS_TAC [o_THM]
QED

Theorem ENCMAPENC_PAIR:
      pair f1 f2 o (g1 ## g2) = pair (f1 o g1) (f2 o g2)
Proof
    REWRITE_TAC [FUN_EQ_THM,o_THM,pairTheory.PAIR_MAP,pair_def]
QED

(*****************************************************************************)
(* Fix identity (FIXID) theorems.                                            *)
(*****************************************************************************)

Theorem FIXID_BOOL:
      !x. (sexp_to_bool o booleanp) x ==> (fix_bool x = x)
Proof
    RW_TAC int_ss [fix_bool_def,booleanp_def,sexp_to_bool_def]
QED

Theorem FIXID_INT:
      !x. (sexp_to_bool o integerp) x ==> (ifix x = x)
Proof
    RW_TAC int_ss [sexp_to_bool_def,integerp_def,ifix_def,ite_def,
                   TRUTH_REWRITES]
QED

Theorem FIXID_NAT:
      !x. (sexp_to_bool o natp) x ==> (nfix x = x)
Proof
    RW_TAC int_ss [sexp_to_bool_def,natp_def,nfix_def,ite_def,
                   TRUTH_REWRITES]
QED

Theorem FIXID_RAT:
      !x. (sexp_to_bool o rationalp) x ==> (fix_rat x = x)
Proof
    RW_TAC int_ss [sexp_to_bool_def,rationalp_def,fix_rat_def,ite_def,
                   TRUTH_REWRITES]
QED

Theorem FIXID_COM:
      !x. (sexp_to_bool o acl2_numberp) x ==> (fix x = x)
Proof
    RW_TAC int_ss [sexp_to_bool_def,acl2_numberp_def,fix_def,ite_def,
                   TRUTH_REWRITES]
QED

Theorem FIXID_CHAR:
      !x. (sexp_to_bool o characterp) x ==> (fix_char x = x)
Proof
    RW_TAC int_ss [sexp_to_bool_def,characterp_def,fix_char_def,ite_def,
                   TRUTH_REWRITES]
QED

Theorem FIXID_STRING:
      !x. (sexp_to_bool o stringp) x ==> (fix_string x = x)
Proof
    RW_TAC int_ss [sexp_to_bool_def,stringp_def,fix_string_def,ite_def,
                   TRUTH_REWRITES]
QED

Theorem FIXID_PAIR:
      (!x. p0 x ==> (f0 x = x)) /\
      (!x. p1 x ==> (f1 x = x)) ==>
            (!x. pairp p0 p1 x ==> (fix_pair f0 f1 x = x))
Proof
    STRIP_TAC THEN Cases THEN RW_TAC int_ss [fix_pair_def,pairp_def,consp_def,
                                             TRUTH_REWRITES,car_def,cdr_def]
QED

Theorem FIXID_LIST:
      (!x. p x ==> (f x = x)) ==>
           (!x. listp p x ==> (fix_list f x = x))
Proof
    STRIP_TAC THEN Induct THEN RW_TAC int_ss [fix_list_def,listp_def,list_def]
QED

(*****************************************************************************)
(* Simple encode then decode theorems.                                       *)
(*****************************************************************************)

fun make_encdec x = REWRITE_RULE [I_THM,o_THM,FUN_EQ_THM] x;

val SEXP_TO_INT_OF_INT = save_thm("SEXP_TO_INT_OF_INT",
                                make_encdec ENCDECMAP_INT);
val SEXP_TO_NAT_OF_NAT = save_thm("SEXP_TO_NAT_OF_NAT",
                                make_encdec ENCDECMAP_NAT);

(*****************************************************************************)
(* Simple decode then encode theorems.                                       *)
(*****************************************************************************)

val list = ref ([]:thm list);
fun make_decenc x y =
let val r =
    GEN_ALL (DISCH_ALL (TRANS (SPEC_ALL (REWRITE_RULE [FUN_EQ_THM,o_THM] x))
          (UNDISCH (SPEC_ALL y))));
in  (list := r :: !list ; r)
end;

val DECENC_BOOL = save_thm("DECENC_BOOL",make_decenc DECENCFIX_BOOL FIXID_BOOL);
val DECENC_INT = save_thm("DECENC_INT",make_decenc DECENCFIX_INT FIXID_INT);
val DECENC_NAT = save_thm("DECENC_NAT",make_decenc DECENCFIX_NAT FIXID_NAT);
val DECENC_RAT = save_thm("DECENC_RAT",make_decenc DECENCFIX_RAT FIXID_RAT);
val DECENC_COM = save_thm("DECENC_COM",make_decenc DECENCFIX_COM FIXID_COM);
val DECENC_CHAR = save_thm("DECENC_CHAR",make_decenc DECENCFIX_CHAR FIXID_CHAR);
val DECENC_STRING = save_thm("DECENC_STRING",
                        make_decenc DECENCFIX_STRING FIXID_STRING);

val INT_OF_SEXP_TO_INT = save_thm("INT_OF_SEXP_TO_INT",
    REWRITE_RULE [combinTheory.o_THM,sexp_to_bool_def] DECENC_INT);

val NAT_OF_SEXP_TO_NAT = save_thm("NAT_OF_SEXP_TO_NAT",
    REWRITE_RULE [combinTheory.o_THM,sexp_to_bool_def] DECENC_NAT);

val RAT_OF_SEXP_TO_RAT = save_thm("RAT_OF_SEXP_TO_RAT",
    REWRITE_RULE [combinTheory.o_THM,sexp_to_bool_def] DECENC_RAT);

val _ = list := [INT_OF_SEXP_TO_INT,NAT_OF_SEXP_TO_NAT] @ (!list);

val CHOOSEP_TAC = translateLib.CHOOSEP_TAC (!list);

(*****************************************************************************)
(* Simple encode then detect theorems.                                       *)
(*****************************************************************************)

fun make_encdet x =
    CONV_RULE (STRIP_QUANT_CONV (REWR_CONV o_THM))
              (REWRITE_RULE [FUN_EQ_THM,K_THM] x);

val ENCDET_BOOL = save_thm("ENCDET_BOOL",make_encdet ENCDETALL_BOOL);
val ENCDET_INT = save_thm("ENCDET_INT",make_encdet ENCDETALL_INT);
val ENCDET_NAT = save_thm("ENCDET_NAT",make_encdet ENCDETALL_NAT);
val ENCDET_RAT = save_thm("ENCDET_RAT",make_encdet ENCDETALL_RAT);
val ENCDET_COM = save_thm("ENCDET_COM",make_encdet ENCDETALL_COM);
val ENCDET_CHAR = save_thm("ENCDET_CHAR",make_encdet ENCDETALL_CHAR);
val ENCDET_STRING = save_thm("ENCDET_STRING",
                        make_encdet ENCDETALL_STRING);

fun make_ii x = REWRITE_RULE [o_THM,sexp_to_bool_def] x;

val INTEGERP_INT = save_thm("INTEGERP_INT",make_ii ENCDET_INT);
val NATP_NAT = save_thm("NATP_NAT",make_ii ENCDET_NAT);
val BOOLEANP_BOOL = save_thm("BOOLEANP_BOOL",make_ii ENCDET_BOOL);
val ACL2_NUMBERP_NUM = save_thm("ACL2_NUMBERP_NUM",make_ii ENCDET_COM);
val RATIONALP_RAT = save_thm("RATIONALP_RAT",make_ii ENCDET_RAT);

(*****************************************************************************)
(* detect dead theorems:                                                     *)
(*     Theorems stating that the bottom value, nil, is not recursive.        *)
(*     This is required for the future encoding of compound types.           *)
(*                                                                           *)
(*****************************************************************************)

Theorem DETDEAD_PAIR:
      ~pairp f g nil
Proof
    REWRITE_TAC [pairp_def,consp_def,TRUTH_REWRITES]
QED

Theorem DETDEAD_LIST:
      listp p nil
Proof
    REWRITE_TAC [listp_def,pairp_def,nil_def]
QED

Theorem DETDEAD_NAT:
      ~sexp_to_bool (natp nil)
Proof
    REWRITE_TAC [ACL2_TRUE,natp_def,nil_def,integerp_def,sexp_to_bool_def,
                 andl_def,ite_def]
QED

Theorem DETDEAD_INT:
      ~sexp_to_bool (integerp nil)
Proof
    REWRITE_TAC [ACL2_TRUE,natp_def,nil_def,integerp_def,sexp_to_bool_def]
QED

Theorem DETDEAD_RAT:
      ~sexp_to_bool (rationalp nil)
Proof
    REWRITE_TAC [ACL2_TRUE,rationalp_def,sexp_to_bool_def,nil_def]
QED

Theorem DETDEAD_COM:
      ~sexp_to_bool (acl2_numberp nil)
Proof
    REWRITE_TAC [ACL2_TRUE,acl2_numberp_def,sexp_to_bool_def,nil_def]
QED

Theorem DETDEAD_CHAR:
      ~sexp_to_bool (characterp nil)
Proof
    REWRITE_TAC [ACL2_TRUE,characterp_def,sexp_to_bool_def,nil_def]
QED

Theorem DETDEAD_STRING:
      ~sexp_to_bool (stringp nil)
Proof
    REWRITE_TAC [ACL2_TRUE,stringp_def,sexp_to_bool_def,nil_def]
QED

Theorem DETDEAD_BOOL:
      sexp_to_bool (booleanp nil)
Proof
    REWRITE_TAC [sexp_to_bool_def,booleanp_def,ite_def,
                 TRUTH_REWRITES,equal_def]
QED

(*****************************************************************************)
(* General detect theorems: !x. detect p x ==> detect (K T) x                *)
(*****************************************************************************)

Theorem GENERAL_DETECT_PAIR:
      !f g x. pairp f g x ==> pairp (K T) (K T) x
Proof
    REWRITE_TAC [pairp_def,K_THM] THEN METIS_TAC []
QED

Theorem GENERAL_DETECT_LIST:
      !f x. listp f x ==> listp (K T) x
Proof
    GEN_TAC THEN Induct THEN REWRITE_TAC [listp_def] THEN METIS_TAC [K_THM]
QED

(*****************************************************************************)
(* Boolean theorems and definitions                                          *)
(*****************************************************************************)

Theorem FLATTEN_BOOL:
      !a. bool ((sexp_to_bool o booleanp) a) = booleanp (I a)
Proof
    RW_TAC std_ss [booleanp_def,ite_def,equal_def,TRUTH_REWRITES,
           sexp_to_bool_def,bool_def]
QED

Theorem COND_REWRITE:
      T ==>
    (bool p = P) /\ (p ==> (f a = A)) /\ (~p ==> (f b = B)) ==>
                 (f (if p then a else b) = ite P A B)
Proof
        Cases_on `p` THEN
        RW_TAC arith_ss [ite_def,bool_def,TRUTH_REWRITES] THEN
        METIS_TAC [TRUTH_REWRITES]
QED

Theorem COND_T:
      p ==> (f (if p then a else b) = f a)
Proof
    METIS_TAC []
QED

Theorem COND_F:
      ~p ==> (f (if p then a else b) = f b)
Proof
    METIS_TAC []
QED

val BOOLEANP_EQUAL = prove(``!a b. |= booleanp (equal a b)``,RW_TAC std_ss [equal_def,booleanp_def,ite_def,TRUTH_REWRITES]);

val BOOLEANP_LESS = prove(``!a b. |= booleanp (less a b)``,
        REWRITE_TAC [booleanp_def,ite_def,equal_def,TRUTH_REWRITES] THEN
        Cases THEN Cases THEN TRY (Cases_on `c`) THEN TRY (Cases_on `c'`) THEN RW_TAC std_ss [less_def,TRUTH_REWRITES]);


val BOOLEANP_NOT = prove(``!a. |= booleanp (not a)``,
        RW_TAC std_ss [booleanp_def,equal_def,ite_def,TRUTH_REWRITES,not_def]);

val BOOLEANP_IF = prove(``!a b. (|= booleanp a) /\ (|= booleanp b) ==> |= booleanp (ite p a b)``,
        REPEAT GEN_TAC THEN Cases_on `a = nil` THEN Cases_on `b = nil` THEN RW_TAC std_ss [booleanp_def,equal_def,ite_def,TRUTH_REWRITES]);

val BOOLEANP_CONSP = prove(``!a. |= booleanp (consp a)``,Cases THEN RW_TAC std_ss [booleanp_def,consp_def,ite_def,TRUTH_REWRITES,equal_def]);

val BOOLEANP_ZP = prove(``!a. |= booleanp (zp a)``,
        RW_TAC std_ss [booleanp_def,ite_def,equal_def,zp_def,TRUTH_REWRITES,GSYM (SPEC ``0i`` int_def)] THEN
        REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC std_ss [TRUTH_REWRITES,not_def,ite_def]);

val BOOLEANP_NATP = prove(``!a. |= booleanp (natp a)``,
        Cases_on `a` THEN RW_TAC std_ss [booleanp_def,natp_def,ite_def,TRUTH_REWRITES,integerp_def,equal_def,andl_def,not_def]);

val BOOLEANP_IMPLIES = prove(``!a b. (|= booleanp a) /\ (|= booleanp b) ==> (|= booleanp (implies a b))``,
        RW_TAC std_ss [implies_def,booleanp_def,andl_def,ite_def,equal_def,TRUTH_REWRITES,ANDL_REWRITE,not_def]);

val BOOLEANP_ANDL = prove(``!a b. (|= booleanp a) /\ (|= booleanp (andl b)) ==> (|= booleanp (andl (a::b)))``,
        GEN_TAC THEN Induct THEN RW_TAC std_ss [implies_def,booleanp_def,andl_def,ite_def,equal_def,TRUTH_REWRITES]);

val BOOLEANP_ANDL_NULL = prove(``|= booleanp (andl [])``,
        RW_TAC std_ss [andl_def,booleanp_def,ite_def,equal_def,TRUTH_REWRITES]);

Theorem BOOL_LEFT_AND:
      !a b. T ==> (bool a = A) /\ (a ==> (bool b = B)) ==>
              (bool (a /\ b) = andl [A; B])
Proof
    REPEAT Cases THEN
    RW_TAC arith_ss [TRUTH_REWRITES,ite_def,bool_def,andl_def]
QED

Theorem BOOL_RIGHT_AND:
      !a b. T ==> (bool b = B) /\ (b ==> (bool a = A)) ==>
              (bool (a /\ b) = andl [B; A])
Proof
    REPEAT Cases THEN
    RW_TAC arith_ss [TRUTH_REWRITES,ite_def,bool_def,andl_def]
QED

Theorem BOOL_LEFT_OR:
      !a b. T ==> (bool ~a = A) /\ (~a ==> (bool ~b = B)) ==>
            (bool (a \/ b) = not (andl [A ; B]))
Proof
    REPEAT Cases THEN
    RW_TAC arith_ss [TRUTH_REWRITES,ite_def,bool_def,andl_def,not_def] THEN
    PROVE_TAC []
QED

Theorem BOOL_RIGHT_OR:
      !a b. T ==> (bool ~b = B) /\ (~b ==> (bool ~a = A)) ==>
            (bool (a \/ b) = not (andl [B ; A]))
Proof
    REPEAT Cases THEN
    RW_TAC arith_ss [TRUTH_REWRITES,ite_def,bool_def,andl_def,not_def] THEN
    PROVE_TAC []
QED

Theorem BOOL_IMPLIES:
      !a b. T ==> (bool a = A) /\ (a ==> (bool b = B)) ==>
            (bool (a ==> b) = implies A B)
Proof
   REPEAT Cases THEN
   RW_TAC arith_ss [implies_def,bool_def,andl_def,TRUTH_REWRITES,ite_def] THEN
   METIS_TAC [TRUTH_REWRITES,ACL2_TRUE]
QED

Theorem BOOL_EQUALITY:
      (!x. g (f x) = x) ==> (bool (a = b) = equal (f a) (f b))
Proof
    Cases_on `a = b` THEN
    RW_TAC arith_ss [equal_def,bool_def,TRUTH_REWRITES] THEN PROVE_TAC []
QED

Theorem BOOL_NOT:
      !a. bool (~a) = not (bool a)
Proof
    Cases THEN RW_TAC std_ss [not_def,TRUTH_REWRITES,bool_def]
QED

val BOOL_T = save_thm("BOOL_T",CONJUNCT1 bool_def);

val BOOL_F = save_thm("BOOL_F",CONJUNCT2 bool_def);

Theorem BOOL_PAIR:
      !x. bool (|= consp x) = consp x
Proof
    Cases THEN REWRITE_TAC [consp_def,bool_def,ACL2_TRUE,EVAL ``t = nil``]
QED

val BOOL_PAIRP = save_thm("BOOL_PAIRP",
    (REWRITE_CONV [pairp_def] ``bool (pairp x y z)``));

val BOOL_KT = save_thm("BOOL_KT",
    (REWRITE_CONV [combinTheory.K_THM] ``bool (K T x)``));

Theorem I_ENCODE:
      T ==> (encode a = A) ==> (I (encode a) = A)
Proof
    RW_TAC std_ss [combinTheory.I_THM]
QED

(*****************************************************************************)
(* Integer theorems:                                                         *)
(*****************************************************************************)

Theorem FLATTEN_INT:
      !a. bool ((sexp_to_bool o integerp) a) = integerp (I a)
Proof
    Cases THEN RW_TAC std_ss [integerp_def,sexp_to_bool_def,
             TRUTH_REWRITES,bool_def]
QED

Theorem INTEGERP_ADD:  !a b. (|= integerp a) /\ (|= integerp b) ==> |= integerp (add a b)
Proof
        Cases THEN Cases THEN
        RW_TAC std_ss [sexpTheory.rat_def,int_def,integerp_def,cpx_def,rat_0_def,frac_0_def,add_def,TRUTH_REWRITES] THEN
        Cases_on `c` THEN Cases_on `c'` THEN
        FULL_SIMP_TAC std_ss [IS_INT_EXISTS,COMPLEX_ADD_def,RAT_ADD_RID,rat_0_def,GSYM rat_0] THEN
        Q.EXISTS_TAC `c + c'` THEN
        RW_TAC std_ss [rat_add_def,frac_add_def] THEN
        RAT_CONG_TAC THEN
        FULL_SIMP_TAC int_ss [INT_LT_01,DNM,NMR] THEN
        RW_TAC int_ss [RAT_EQ,FRAC_DNMPOS,INT_MUL_POS_SIGN,NMR,DNM,INT_LT_01,INT_RDISTRIB,INT_MUL_ASSOC] THEN
        ARITH_TAC
QED

Theorem INTEGERP_MULT:  !a b. (|= integerp a) /\ (|= integerp b) ==> |= integerp (mult a b)
Proof
        Cases THEN Cases THEN
        RW_TAC std_ss [sexpTheory.rat_def,int_def,integerp_def,cpx_def,rat_0_def,frac_0_def,mult_def,TRUTH_REWRITES] THEN
        Cases_on `c` THEN Cases_on `c'` THEN
        FULL_SIMP_TAC std_ss [IS_INT_EXISTS,COMPLEX_MULT_def,RAT_ADD_RID,rat_0_def,GSYM rat_0,RAT_MUL_LZERO,RAT_MUL_RZERO,RAT_ADD_RID,RAT_SUB_RID] THEN
        Q.EXISTS_TAC `c * c'` THEN
        RW_TAC std_ss [rat_mul_def,frac_mul_def] THEN
        RAT_CONG_TAC THEN
        FULL_SIMP_TAC int_ss [INT_LT_01,DNM,NMR] THEN
        RW_TAC int_ss [RAT_EQ,FRAC_DNMPOS,INT_MUL_POS_SIGN,NMR,DNM,INT_LT_01,INT_RDISTRIB,INT_MUL_ASSOC] THEN
        ARITH_TAC
QED

Theorem INTEGERP_UNARY_MINUS:  !a. (|= integerp a) ==> |= integerp (unary_minus a)
Proof
        Cases THEN
        RW_TAC std_ss [sexpTheory.rat_def,int_def,integerp_def,cpx_def,rat_0_def,frac_0_def,unary_minus_def,TRUTH_REWRITES] THEN
        Cases_on `c` THEN
        FULL_SIMP_TAC std_ss [IS_INT_EXISTS,COMPLEX_SUB_def,RAT_ADD_RID,rat_0_def,GSYM rat_0,com_0_def] THEN
        POP_ASSUM MP_TAC THEN RW_TAC std_ss [RAT_SUB_RID,RAT_SUB_LID,RAT_AINV_0] THEN
        Q.EXISTS_TAC `~c` THEN
        RW_TAC std_ss [RAT_AINV_CALCULATE,frac_ainv_def,NMR,INT_LT_01,DNM]
QED

Theorem INT_ADD:  !a b. int (a + b) = add (int a) (int b)
Proof
        RW_TAC int_ss [add_def,int_def,cpx_def,sexpTheory.rat_def,COMPLEX_ADD_def,rat_add_def,frac_add_def,RAT_EQ,NMR,DNM,INT_LT_01] THEN
        RAT_CONG_TAC THEN
        FULL_SIMP_TAC int_ss [NMR,DNM,INT_LT_01,RAT_EQ,FRAC_DNMPOS,INT_MUL_POS_SIGN,GSYM INT_ADD] THEN ARITH_TAC
QED

Theorem INT_MULT:  !a b. int (a * b) = mult (int a) (int b)
Proof
        RW_TAC std_ss [mult_def,int_def,cpx_def,sexpTheory.rat_def,GSYM rat_0,GSYM frac_0_def,COMPLEX_MULT_def,
                RAT_MUL_RZERO,RAT_SUB_RID,RAT_MUL_LZERO,RAT_ADD_RID] THEN
        RW_TAC int_ss [RAT_EQ,rat_mul_def,frac_mul_def,DNM,NMR,INT_LT_01] THEN
        RAT_CONG_TAC THEN
        FULL_SIMP_TAC int_ss [DNM,NMR,INT_LT_01,FRAC_DNMPOS,INT_MUL_POS_SIGN] THEN ARITH_TAC
QED

Theorem INT_UNARY_MINUS:  !a. int (~a) = unary_minus (int a)
Proof
        RW_TAC int_ss [unary_minus_def,int_def,cpx_def,sexpTheory.rat_def,GSYM rat_0,GSYM frac_0_def,COMPLEX_SUB_def,com_0_def,
                rat_0_def,GSYM rat_0,RAT_SUB_LID,RAT_AINV_CALCULATE,RAT_AINV_0,FRAC_AINV_CALCULATE]
QED

Theorem INT_EQUAL:
      !a b. bool (a = b) = equal (int a) (int b)
Proof
    RW_TAC std_ss [INT_CONG,equal_def,bool_def,TRUTH_REWRITES]
QED

Theorem INT_LT:  !a b. bool (a < b) = less (int a) (int b)
Proof
        RW_TAC intLib.int_ss [nat_def,int_def,cpx_def,sexpTheory.rat_def,ratTheory.RAT_EQ,fracTheory.NMR,fracTheory.DNM,less_def,RAT_LES_CALCULATE,bool_def]
QED

(*****************************************************************************)
(* Nat theorems:                                                             *)
(*****************************************************************************)

Theorem FLATTEN_NAT:
      bool ((sexp_to_bool o natp) a) = natp (I a)
Proof
    REPEAT (RW_TAC arith_ss [natp_def,bool_def,less_def,andl_def,not_def,
                             ite_def,TRUTH_REWRITES,sexp_to_bool_def])
QED

Theorem NAT_EQUAL:  !a b. bool (a = b) = equal (nat a) (nat b)
Proof
        RW_TAC int_ss [NAT_CONG,equal_def,bool_def]
QED

Theorem NAT_EQUAL_0:  !a. bool (a = 0n) = zp (nat a)
Proof
    Cases THEN RW_TAC int_ss [bool_def,zp_def,nat_def,INTEGERP_INT,
          TRUTH_REWRITES,ite_def,GSYM int_def,GSYM INT_LT,not_def]
QED

Theorem NAT_0_LT:
      !a. bool (0n < a) = not (zp (nat a))
Proof
    Cases THEN RW_TAC int_ss [bool_def,zp_def,nat_def,INTEGERP_INT,
          TRUTH_REWRITES,ite_def,GSYM int_def,GSYM INT_LT,not_def]
QED

Theorem NAT_ADD:
      !a b. nat (a + b) = add (nat a) (nat b)
Proof
    RW_TAC std_ss [nat_def,add_def,int_def,cpx_def,sexpTheory.rat_def,
           COMPLEX_ADD_def,rat_0_def,GSYM rat_0,GSYM frac_0_def,RAT_ADD_RID,
           rat_add_def,frac_add_def] THEN
    RAT_CONG_TAC THEN
    FULL_SIMP_TAC int_ss [NMR,DNM,INT_LT_01,RAT_EQ,FRAC_DNMPOS,
                  INT_MUL_POS_SIGN,INT_LT_IMP_NE] THEN ARITH_TAC
QED

Theorem NAT_SUC:  !a. nat (SUC a) = add (nat a) (nat 1)
Proof
    RW_TAC std_ss [NAT_ADD,ADD1]
QED

Theorem NAT_PRE:  !a. (?d. a = SUC d) ==>
              (nat (PRE a) = add (nat a) (unary_minus (nat 1)))
Proof
        Cases THEN
        RW_TAC arith_ss [nat_def,GSYM INT_UNARY_MINUS,GSYM INT_ADD] THEN
        AP_TERM_TAC THEN RW_TAC int_ss [ADD1,GSYM integerTheory.INT_ADD] THEN
        ARITH_TAC
QED

Theorem NAT_SUC_PRE:
      !a. (?d. a = SUC d) ==> (nat (SUC (PRE a)) = nat a)
Proof
    Cases THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN RW_TAC arith_ss [ADD1]
QED

Theorem NAT_MULT:
      !a b. nat (a * b) = mult (nat a) (nat b)
Proof
    RW_TAC std_ss [nat_def,mult_def,int_def,cpx_def,sexpTheory.rat_def,
           COMPLEX_MULT_def,rat_0_def,GSYM rat_0,GSYM frac_0_def,
           RAT_MUL_RZERO,RAT_SUB_RID,rat_mul_def,frac_mul_def,RAT_ADD_RID] THEN
    RAT_CONG_TAC THEN
    FULL_SIMP_TAC int_ss [NMR,DNM,INT_LT_01,RAT_EQ,FRAC_DNMPOS,
        INT_MUL_POS_SIGN,INT_LT_IMP_NE,rat_0,frac_0_def,RAT_NMREQ0_CONG] THEN
    ARITH_TAC
QED

Theorem NAT_NUM:
      !a b. 0 <= a ==> (nat (Num a) = int a)
Proof
    RW_TAC int_ss [nat_def,INT_OF_NUM,INT_CONG]
QED

(*****************************************************************************)
(* Rational theorems:                                                        *)
(*****************************************************************************)

Theorem FLATTEN_RAT:
      !a. bool ((sexp_to_bool o rationalp) a) = rationalp (I a)
Proof
    Cases THEN MAP_EVERY (TRY o Cases_on) [`c`,`c'`] THEN
    RW_TAC std_ss [rationalp_def,sexp_to_bool_def,
             TRUTH_REWRITES,bool_def]
QED

Theorem RATIONALP_ADD:  !a b. (|= rationalp a) /\ (|= rationalp b) ==> |= rationalp (add a b)
Proof
        Cases THEN Cases THEN RW_TAC std_ss [rationalp_def,add_def,TRUTH_REWRITES] THEN
        Cases_on `c` THEN Cases_on `c'` THEN FULL_SIMP_TAC std_ss [rationalp_def,COMPLEX_ADD_def,TRUTH_REWRITES,rat_0_def,GSYM rat_0,RAT_ADD_RID]
QED

Theorem RATIONALP_MULT:  !a b. (|= rationalp a) /\ (|= rationalp b) ==> |= rationalp (mult a b)
Proof
        Cases THEN Cases THEN RW_TAC std_ss [rationalp_def,mult_def,TRUTH_REWRITES] THEN
        Cases_on `c` THEN Cases_on `c'` THEN FULL_SIMP_TAC std_ss [rationalp_def,COMPLEX_MULT_def,TRUTH_REWRITES,rat_0_def,GSYM rat_0,RAT_ADD_RID,RAT_MUL_RZERO,RAT_MUL_LZERO]
QED

Theorem RATIONALP_UNARY_MINUS:  !a. (|= rationalp a) ==> |= rationalp (unary_minus a)
Proof
        Cases THEN RW_TAC std_ss [rationalp_def,unary_minus_def,TRUTH_REWRITES] THEN
        Cases_on `c` THEN FULL_SIMP_TAC std_ss [rationalp_def,TRUTH_REWRITES,rat_0_def,GSYM rat_0,com_0_def,COMPLEX_SUB_def,RAT_SUB_RID]
QED

Theorem RATIONALP_RECIPROCAL:  !a. (|= rationalp a) ==> |= rationalp (reciprocal a)
Proof
        Cases THEN RW_TAC std_ss [rationalp_def,reciprocal_def,TRUTH_REWRITES,int_def,com_0_def,cpx_def,sexpTheory.rat_def,rat_0_def, GSYM rat_0,GSYM frac_0_def] THEN
        Cases_on `c` THEN FULL_SIMP_TAC std_ss [COMPLEX_RECIPROCAL_def,complex_rational_11,rationalp_def,TRUTH_REWRITES,rat_0_def,
                GSYM rat_0,RAT_MUL_RZERO,RAT_ADD_RID,RAT_AINV_0,RAT_LDIV_EQ,RAT_NO_ZERODIV_NEG]
QED


Theorem RAT_ADD:  !a b. rat (a + b) = add (rat a) (rat b)
Proof
        RW_TAC std_ss [add_def,COMPLEX_ADD_def,rat_0_def,GSYM rat_0,RAT_ADD_RID,rat_def]
QED

Theorem RAT_MULT:  !a b. rat (a * b) = mult (rat a) (rat b)
Proof
        RW_TAC std_ss [mult_def,COMPLEX_MULT_def,rat_0_def,GSYM rat_0,rat_def,RAT_SUB_RID,RAT_MUL_LZERO,RAT_MUL_RZERO,RAT_ADD_RID]
QED

Theorem RAT_UNARY_MINUS:  !a. rat (~a) = unary_minus (rat a)
Proof
        RW_TAC std_ss [rat_def,unary_minus_def,com_0_def,COMPLEX_SUB_def,rat_0_def,GSYM rat_0,RAT_SUB_LID,RAT_AINV_0]
QED

val rat_divshiftthm = prove(``a * (b / c) = a * b / c:rat``,
    RW_TAC std_ss [RAT_DIV_MULMINV,RAT_MUL_ASSOC]);

Theorem RAT_DIV:
      !a b. ~(b = 0) ==> (rat (a / b) = mult (rat a) (reciprocal (rat b)))
Proof
    RW_TAC std_ss [rat_def,mult_def,reciprocal_def,COMPLEX_RECIPROCAL_def,
           rat_0_def,GSYM rat_0,COMPLEX_MULT_def,RAT_MUL_RZERO,
           RAT_ADD_RID,RAT_MUL_LZERO,RAT_ADD_LID,RAT_AINV_0,int_def,
           RAT_SUB_RID,com_0_def,complex_rational_11,cpx_def,sexpTheory.rat_def,
           GSYM frac_0_def,RAT_LDIV_EQ,rat_divshiftthm,RAT_NO_ZERODIV_NEG,
           RAT_RDIV_EQ,RAT_MUL_ASSOC] THEN
    CONV_TAC (AC_CONV (RAT_MUL_ASSOC,RAT_MUL_COMM))
QED

Theorem RAT_SUB:  !a b. rat (a - b) = add (rat a) (unary_minus (rat b))
Proof
        RW_TAC std_ss [rat_def,add_def,unary_minus_def,com_0_def,rat_0_def,GSYM rat_0,COMPLEX_SUB_def,COMPLEX_ADD_def,RAT_SUB_LID,RAT_ADD_RID,RAT_AINV_0,RAT_SUB_ADDAINV]
QED

Theorem RAT_EQUAL:  !a b. bool (a = b) = equal (rat a) (rat b)
ProofRW_TAC std_ss [bool_def,equal_def,rat_def,RAT_LES_REF]
QED

(*****************************************************************************)
(* Complex (general number) theorems:                                        *)
(*****************************************************************************)

Theorem ACL2_NUMBERP_COM:  !a. |= acl2_numberp (num a)
ProofRW_TAC std_ss [acl2_numberp_def,TRUTH_REWRITES]
QED

Theorem ACL2_NUMBERP_ADD:  !a b. |= acl2_numberp (add a b)
Proof
        Cases THEN Cases THEN RW_TAC std_ss [acl2_numberp_def,add_def,TRUTH_REWRITES,int_def,cpx_def]
QED

Theorem ACL2_NUMBERP_MULT:  !a b. |= acl2_numberp (mult a b)
Proof
        Cases THEN Cases THEN RW_TAC std_ss [acl2_numberp_def,mult_def,TRUTH_REWRITES,int_def,cpx_def]
QED

Theorem ACL2_NUMBERP_UNARY_MINUS:  !a. |= acl2_numberp (unary_minus a)
Proof
        Cases_on `a` THEN RW_TAC std_ss [acl2_numberp_def,unary_minus_def,TRUTH_REWRITES,int_def,cpx_def]
QED

Theorem ACL2_NUMBERP_RECIPROCAL:  !a. |= acl2_numberp (reciprocal a)
Proof
        Cases_on `a` THEN RW_TAC std_ss [acl2_numberp_def,reciprocal_def,TRUTH_REWRITES,int_def,cpx_def]
QED

Theorem COM_ADD:  !a b. num (a + b) = add (num a) (num b)
ProofRW_TAC std_ss [add_def]
QED

Theorem COM_MULT:  !a b. num (a * b) = mult (num a) (num b)
ProofRW_TAC std_ss [mult_def]
QED

Theorem COM_UNARY_MINUS:  !a. num (~a) = unary_minus (num a)
ProofRW_TAC std_ss [unary_minus_def,COMPLEX_NEG_def]
QED

Theorem COM_SUB:  num (a - b) = add (num a) (unary_minus (num b))
Proof
        RW_TAC std_ss [unary_minus_def,add_def,com_0_def] THEN
        Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [COMPLEX_ADD_def,COMPLEX_SUB_def,rat_0_def,GSYM rat_0,RAT_SUB_LID,RAT_LSUB_EQ] THEN
        METIS_TAC [RAT_ADD_COMM,RAT_ADD_ASSOC,RAT_ADD_RINV,RAT_ADD_RID]
QED

Theorem COM_DIV:  !a b. ~(b = com_0) ==> (num (a / b) = mult (num a) (reciprocal (num b)))
Proof
        RW_TAC std_ss [mult_def,reciprocal_def,COMPLEX_DIV_def]
QED

Theorem COM_EQUAL:  bool (a = b) = equal (num a) (num b)
Proof
        Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [bool_def,equal_def,TRUTH_REWRITES,complex_rational_11]
QED

Theorem FIX_NUM:  (!a. fix (num a) = num a) /\ (!a. fix (rat a) = rat a) /\ (!a. fix (int a) = int a) /\ (!a. fix (nat a) = nat a)
Proof
        RW_TAC std_ss [fix_def,ACL2_NUMBERP_NUM,ite_def,TRUTH_REWRITES,rat_def,int_def,nat_def,cpx_def]
QED

Theorem NAT_NFIX:  nfix (nat a) = nat a
Proof
        RW_TAC std_ss [nfix_def,ite_def,TRUTH_REWRITES,nat_def,ANDL_REWRITE,INTEGERP_INT,GSYM INT_LT,GSYM BOOL_NOT] THEN
        METIS_TAC [INT_POS,INT_NOT_LT]
QED

Theorem INT_IFIX:  ifix (int a) = int a
ProofRW_TAC std_ss [ifix_def,ite_def,TRUTH_REWRITES,INTEGERP_INT]
QED

(*****************************************************************************)
(* Pair theorems:                                                            *)
(*****************************************************************************)

Theorem PAIR_FST:
      f (FST x) = car (pair f g x)
Proof
    RW_TAC std_ss [pairTheory.FST,pair_def,car_def]
QED

Theorem PAIR_SND:
      g (SND x) = cdr (pair f g x)
Proof
    RW_TAC std_ss [pairTheory.SND,pair_def,cdr_def]
QED

Theorem PAIR_CASE:
      f (pair_case g x) = f ((\(a,b). g a b) x)
Proof
    Cases_on `x` THEN REWRITE_TAC [TypeBase.case_def_of ``:'a # 'b``] THEN
    pairLib.GEN_BETA_TAC THEN REWRITE_TAC []
QED

(*****************************************************************************)
(* List theorems:                                                            *)
(*****************************************************************************)

Theorem LIST_HD:
      (?a b. l = a::b) ==> (encode (HD l) = car (list encode l))
Proof
    Induct_on `l` THEN RW_TAC std_ss [list_def,HD,car_def]
QED

Theorem LIST_TL:
      (?a b. l = a :: b) ==> (list encode (TL l) = cdr (list encode l))
Proof
    Induct_on `l` THEN RW_TAC std_ss [list_def,TL,cdr_def]
QED

Theorem LIST_NULL:
      !l. bool (NULL l) = atom (list f l)
Proof
    Cases THEN
    RW_TAC arith_ss [bool_def,hol_defaxiomsTheory.atom_def,list_def,NULL,
           TRUTH_REWRITES,hol_defaxiomsTheory.not_def,consp_def]
QED

Theorem LIST_LENGTH:
      nat (LENGTH l) = len (list f l)
Proof
    Induct_on `l` THEN ONCE_REWRITE_TAC [len_def] THEN
    RW_TAC std_ss [LENGTH,list_def,consp_def,ite_def,
                   TRUTH_REWRITES,NAT_SUC,cdr_def] THEN
    POP_ASSUM (SUBST_ALL_TAC o GSYM) THEN
    RW_TAC arith_ss [GSYM NAT_ADD]
QED

(*****************************************************************************)
(* String theorems:                                                          *)
(*****************************************************************************)

val list_rewrite = prove(``list_to_sexp = list``,REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN Induct THEN METIS_TAC [list_def,list_to_sexp_def]);

Theorem STRING_EXPLODE:  list chr (EXPLODE s) = coerce (str s) (sym "COMMON-LISP" "LIST")
Proof
        RW_TAC std_ss [coerce_def,coerce_string_to_list_def,list_rewrite]
QED

Theorem STRING_IMPLODE:  str (IMPLODE l) = coerce (list chr l) (sym "COMMON-LISP" "STRING")
Proof
        Induct_on `l` THEN RW_TAC std_ss [coerce_def,coerce_list_to_string_def,list_rewrite,list_def,
                nil_def,stringTheory.IMPLODE_EQNS,make_character_list_def] THEN
        Cases_on `list chr l` THEN POP_ASSUM MP_TAC THEN Cases_on `l` THEN
        REPEAT (RW_TAC std_ss [coerce_def,list_def,nil_def,stringTheory.IMPLODE_EQNS,
                make_character_list_def,coerce_list_to_string_def] THEN REPEAT (POP_ASSUM MP_TAC))
QED

val coerce_rewrite = CONJ (GSYM STRING_EXPLODE) (GSYM STRING_IMPLODE);

Theorem STRING_LENGTH:  nat (STRLEN s) = length (str s)
Proof
        RW_TAC std_ss [stringp_def,ite_def,TRUTH_REWRITES,length_def,coerce_def,coerce_string_to_list_def,
                        stringTheory.STRLEN_THM,GSYM LIST_LENGTH,list_rewrite,csym_def,COMMON_LISP_def,
                        GSYM stringTheory.STRLEN_EXPLODE_THM]
QED


(*****************************************************************************)
(* Case theorems                                                             *)
(*****************************************************************************)

Theorem NUM_CONSTRUCT:
      !a. bool (?d. a = SUC d) = bool (0 < a)
Proof
    Cases THEN RW_TAC arith_ss []
QED

Theorem NUM_CASE:
      !X a b. f (num_case a b X) =
                               f (if X = 0 then a else b (PRE X))
Proof
    Cases THEN REWRITE_TAC [TypeBase.case_def_of ``:num``] THEN
    RW_TAC arith_ss []
QED

Theorem LIST_CASE:
      !l. f (list_case n c l) =
                         f (if (l = []) then n else c (HD l) (TL l))
Proof
    Cases THEN RW_TAC arith_ss [NULL,HD,TL]
QED

Theorem LIST_CONSTRUCT1:
      !l. bool (l = []) = bool (NULL l)
Proof
    Cases THEN REWRITE_TAC [NULL,GSYM (TypeBase.distinct_of ``:'a list``)]
QED

Theorem LIST_CONSTRUCT2:
      !l. bool (?a b. l = a::b) = bool (~NULL l)
Proof
    Cases THEN REWRITE_TAC [NULL] THEN
    AP_TERM_TAC THEN EQ_TAC THEN METIS_TAC [TypeBase.distinct_of ``:'a list``]
QED

(*****************************************************************************)
(* Comparison theorems:                                                      *)
(*****************************************************************************)

(* LT, LE, GT, GE *)

Theorem NAT_LT:  !a b. bool (a < b) = less (nat a) (nat b)
Proof
        RW_TAC int_ss [nat_def,GSYM INT_LT,bool_def]
QED

Theorem RAT_LT:  !a b. bool (a < b) = less (rat a) (rat b)
ProofRW_TAC std_ss [bool_def,less_def,rat_def,RAT_LES_REF]
QED

Theorem COM_LT:  bool (a < b) = less (num a) (num b)
Proof
        Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [bool_def,less_def,TRUTH_REWRITES,COMPLEX_LT_def]
QED


Theorem COM_NOT_LT:  !a b. ~(a < b) = b <= a:complex_rational
Proof
        Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [COMPLEX_LT_def,COMPLEX_LE_def,RAT_LEQ_LES,rat_leq_def] THEN METIS_TAC [RAT_LES_IMP_NEQ]
QED

Theorem NAT_LE:  bool (a <= b) = not (less (nat b) (nat a))
ProofRW_TAC std_ss [bool_def,TRUTH_REWRITES,not_def,ite_def,GSYM NAT_LT,NOT_LESS]
QED

Theorem INT_LE:  bool (a <= b) = not (less (int b) (int a))
ProofRW_TAC int_ss [bool_def,TRUTH_REWRITES,not_def,ite_def,GSYM INT_LT,INT_NOT_LT]
QED

Theorem RAT_LE:  bool (a <= b) = not (less (rat b) (rat a))
ProofRW_TAC std_ss [bool_def,TRUTH_REWRITES,not_def,ite_def,GSYM RAT_LT,RAT_LEQ_LES]
QED

Theorem COM_LE:  bool (a <= b) = not (less (num b) (num a))
ProofRW_TAC std_ss [bool_def,TRUTH_REWRITES,not_def,ite_def,GSYM COM_LT,COM_NOT_LT]
QED


Theorem NAT_GE:  bool (a >= b) = bool (b <= a:num)
ProofAP_TERM_TAC THEN DECIDE_TAC
QED
Theorem INT_GE:  bool (a >= b) = bool (b <= a:int)
ProofAP_TERM_TAC THEN ARITH_TAC
QED
Theorem RAT_GE:  bool (a >= b) = bool (b <= a:rat)
ProofREWRITE_TAC [rat_geq_def]
QED
Theorem COM_GE:  bool (a >= b) = bool (b <= a:complex_rational)
Proof
        AP_TERM_TAC THEN Cases_on `a` THEN Cases_on `b` THEN
        REWRITE_TAC [COMPLEX_LE_def,COMPLEX_GE_def,rat_gre_def,rat_geq_def] THEN
        EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []
QED

Theorem NAT_GT:  bool (a > b) = bool (b < a:num)
ProofAP_TERM_TAC THEN DECIDE_TAC
QED
Theorem INT_GT:  bool (a > b) = bool (b < a:int)
ProofAP_TERM_TAC THEN ARITH_TAC
QED
Theorem RAT_GT:  bool (a > b) = bool (b < a:rat)
ProofREWRITE_TAC [rat_gre_def]
QED
Theorem COM_GT:  bool (a > b) = bool (b < a:complex_rational)
Proof
        AP_TERM_TAC THEN Cases_on `a` THEN Cases_on `b` THEN
        REWRITE_TAC [COMPLEX_LT_def,COMPLEX_GT_def,rat_gre_def,rat_geq_def] THEN
        EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []
QED

(*****************************************************************************)
(* Subtraction theorems:                                                     *)
(*****************************************************************************)

Theorem INT_SUB:  !a b. int (a - b) = add (int a) (unary_minus (int b))
Proof
        RW_TAC int_ss [GSYM INT_ADD,GSYM INT_UNARY_MINUS,int_sub]
QED

Theorem NAT_SUB:
      !a b. nat (a - b) = nfix (add (nat a) (unary_minus (nat b)))
Proof
    RW_TAC int_ss [nat_def,GSYM INT_SUB,nfix_def,ite_def,TRUTH_REWRITES,
           natp_def,INTEGERP_INT,GSYM INT_EQUAL,
           GSYM INT_LT,INT_CONG,GSYM BOOL_NOT,ANDL_REWRITE] THEN
    FULL_SIMP_TAC int_ss [INT_NOT_LT,INT_LE_SUB_RADD,INT_LT_SUB_LADD,
                  integerTheory.INT_SUB,INT_LE_SUB_LADD,INT_LT_SUB_RADD]
QED

Theorem RAT_SUB:  rat (a - b) = add (rat a) (unary_minus (rat b))
Proof
        RW_TAC std_ss [rat_sub_def,frac_sub_def,GSYM RAT_ADD,GSYM RAT_UNARY_MINUS,rat_ainv_def,rat_add_def,frac_ainv_def,RAT_ADD_CONG]
QED
Theorem COM_SUB:  num (a - b) = add (num a) (unary_minus (num b))
Proof
        Cases_on `a` THEN Cases_on `b` THEN RW_TAC std_ss [COMPLEX_SUB_def,GSYM COM_UNARY_MINUS,GSYM COM_ADD,
                COMPLEX_NEG_def,COMPLEX_ADD_def,com_0_def,RAT_SUB_LID,rat_0_def,GSYM rat_0,RAT_SUB_ADDAINV]
QED

Theorem NAT_SUB_COND:  !a b. b <= a ==> (nat (a - b) = add (nat a) (unary_minus (nat b)))
Proof
        RW_TAC int_ss [nat_def,GSYM INT_SUB,nfix_def,ite_def,TRUTH_REWRITES,natp_def,INTEGERP_INT,GSYM INT_EQUAL,GSYM INT_LT,INT_CONG] THEN
        FULL_SIMP_TAC int_ss [INT_NOT_LT,INT_LE_SUB_RADD,INT_LT_SUB_LADD,integerTheory.INT_SUB] THEN FULL_SIMP_TAC int_ss [INT_EQ_SUB_LADD]
QED

val MK_THMS = LIST_CONJ o (map GEN_ALL);

(*****************************************************************************)
(* Natural number judgement theorems:                                        *)
(*****************************************************************************)

Theorem NATP_ADD:
      !a b. (|= natp a) /\ (|= natp b) ==> |= natp (add a b)
Proof
    REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN
    RW_TAC std_ss [GSYM NAT_ADD,NATP_NAT]
QED

Theorem NATP_MULT:
      !a b. (|= natp a) /\ (|= natp b) ==> |= natp (mult a b)
Proof
    REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN
    RW_TAC std_ss [GSYM NAT_MULT,NATP_NAT]
QED

Theorem NATP_PRE:
      !a. (|= natp a) ==> ~(a = nat 0) ==>
          |= natp (add a (unary_minus (nat 1)))
Proof
    REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN
    FULL_SIMP_TAC int_ss [nat_def,GSYM INT_ADD,GSYM INT_UNARY_MINUS,
        INT_ADD_CALCULATE,natp_def,ANDL_REWRITE,INTEGERP_INT,GSYM INT_LT,
        not_def,TRUTH_REWRITES,ite_def,INT_CONG]
QED

Theorem NATP_SUB:
      !a b. (|= natp a) /\ (|= natp b) /\ (|= not (less a b)) ==>
         |= natp (add a (unary_minus b))
Proof
    REPEAT STRIP_TAC THEN CHOOSEP_TAC THEN
    FULL_SIMP_TAC int_ss [nat_def,GSYM INT_ADD,GSYM INT_UNARY_MINUS,
        INT_ADD_CALCULATE,natp_def,ANDL_REWRITE,INTEGERP_INT,GSYM INT_LT,
        not_def,TRUTH_REWRITES,ite_def,INT_CONG]
QED

Theorem NATP_NFIX:
       !a. |= natp (nfix a)
Proof
     RW_TAC std_ss [natp_def,nfix_def,ite_def,TRUTH_REWRITES,
            ANDL_REWRITE,nat_def] THEN
    FULL_SIMP_TAC std_ss [INTEGERP_INT,GSYM INT_LT,GSYM INT_EQUAL,
                  TRUTH_REWRITES] THEN
    CHOOSEP_TAC THEN
    FULL_SIMP_TAC std_ss [GSYM BOOL_NOT,INTEGERP_INT,GSYM INT_LT,
                  GSYM INT_EQUAL,TRUTH_REWRITES] THEN
    ARITH_TAC
QED

(*****************************************************************************)
(* Grouped theorems for export.                                              *)
(*****************************************************************************)

val NAT_THMS = save_thm("NAT_THMS",
    MK_THMS [NAT_EQUAL_0,NAT_EQUAL,NAT_0_LT,NAT_LT,NAT_LE,NAT_GE,NAT_GT,
             NAT_ADD,NAT_SUC_PRE,NAT_PRE,NAT_SUC,NAT_MULT,NAT_SUB]);

val INT_THMS = save_thm("INT_THMS",
    MK_THMS [INT_EQUAL,INT_LT,INT_LE,INT_GE,INT_GT,
             INT_ADD,INT_MULT,INT_UNARY_MINUS,INT_SUB]);

val RAT_THMS = save_thm("RAT_THMS",
    MK_THMS [RAT_EQUAL,RAT_LT,RAT_LE,RAT_GE,RAT_GT,
             RAT_ADD,RAT_MULT,RAT_UNARY_MINUS,RAT_DIV,RAT_SUB]);

val COM_THMS = save_thm("COM_THMS",
    MK_THMS [COM_EQUAL,COM_LT,COM_LE,COM_GE,COM_GT,
             COM_ADD,COM_MULT,COM_UNARY_MINUS,COM_DIV,COM_SUB]);

val BOOL_THMS = save_thm("BOOL_THMS",
    MK_THMS [BOOL_EQUALITY,BOOL_NOT,BOOL_T,BOOL_F]);

val LIST_THMS = save_thm("LIST_THMS",
    MK_THMS [LIST_HD,LIST_TL,LIST_LENGTH]);

val PAIR_THMS = save_thm("PAIR_THMS",
    MK_THMS [PAIR_FST,PAIR_SND]);

val STRING_THMS = save_thm("STRING_THMS",
    MK_THMS [STRING_EXPLODE,STRING_IMPLODE,STRING_LENGTH]);

val JUDGEMENT_THMS = save_thm("JUDGEMENT_THMS",
    MK_THMS [CONJUNCT1 ANDL_JUDGEMENT,CONJUNCT2 ANDL_JUDGEMENT,
             NATP_NAT,INTEGERP_INT,RATIONALP_RAT,ACL2_NUMBERP_NUM,BOOLEANP_BOOL,
             NATP_ADD,NATP_PRE,NATP_SUB,NATP_NFIX,NATP_MULT,
             BOOLEANP_IMPLIES,BOOLEANP_ANDL,BOOLEANP_ANDL_NULL,
             BOOLEANP_EQUAL,BOOLEANP_LESS,BOOLEANP_NOT,BOOLEANP_CONSP,
             BOOLEANP_IF,
             INTEGERP_ADD,INTEGERP_MULT,INTEGERP_UNARY_MINUS,
             RATIONALP_ADD,RATIONALP_MULT,RATIONALP_RECIPROCAL,
             RATIONALP_UNARY_MINUS,
             ACL2_NUMBERP_ADD,ACL2_NUMBERP_MULT,ACL2_NUMBERP_RECIPROCAL,
             ACL2_NUMBERP_UNARY_MINUS]);


