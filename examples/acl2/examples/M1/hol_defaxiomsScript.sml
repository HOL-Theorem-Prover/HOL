
(*****************************************************************************)
(* HOL definition of those ACL2 functions defined in defaxioms.lisp.trans    *)
(* that are used in the axioms proved in hol_defaxioms_proofsTheory.         *)
(* Unused functions are specified in comments, but not actually defined.     *)
(* Some functions are axiomatically defined using acl2AxiomDefine            *)
(*****************************************************************************)

(*****************************************************************************)
(* Ignore everything up to "END BOILERPLATE"                                 *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE NEEDED FOR COMPILATION                                  *)
(*****************************************************************************)

(******************************************************************************
* Load theories
******************************************************************************)
(* The commented out stuff below should be loaded in interactive sessions
quietdec := true;
map
 load
 ["stringLib","complex_rationalTheory","gcdTheory",
  "sexp","sexpTheory"];
open stringLib complex_rationalTheory gcdTheory
     sexp sexpTheory;
Globals.checking_const_names := false;
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation: open HOL4 systems modules.
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories (including ratTheory from Jens Brandt).
******************************************************************************)
open stringLib complex_rationalTheory gcdTheory sexp sexpTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

val _ = new_theory "hol_defaxioms";

(*
     [oracles: DEFUN ACL2::IFF, DISK_THM] [axioms: ] []
     |- iff p q = itel [(p,andl [q; t]); (q,nil)] t,
*)

val iff_def =
 acl2Define "ACL2::IFF"
  `iff p q = itel [(p,andl [q; t]); (q,nil)] t`;

val iff =
 store_thm
  ("iff_thm",
   ``iff p q = ite p (ite q t nil) (ite q nil t)``,
   RW_TAC std_ss [iff_def,ite_def,itel_def,andl_def]);

(*
     [oracles: DEFUN ACL2::BOOLEANP, DISK_THM] [axioms: ] []
     |- booleanp x = ite (equal x t) t (equal x nil),
*)

val booleanp_def =
 acl2Define "ACL2::BOOLEANP"
  `booleanp x = ite (equal x t) t (equal x nil)`;

(*
     [oracles: DEFUN ACL2::IMPLIES, DISK_THM] [axioms: ] []
     |- implies p q = ite p (andl [q; t]) t,
*)

(* Moved to sexpScript.sml
val implies_def =
 acl2Define "ACL2::IMPLIES"
  `implies p q = ite p (andl [q; t]) t`;

val implies_ite =
 store_thm
  ("implies_ite",
   ``implies p q = ite p (ite q t nil) t``,
   RW_TAC std_ss [implies_def,ite_def,itel_def,andl_def]);

val implies =
 store_thm
  ("implies",
   ``(|= implies p q) = (|= p) ==> (|= q)``,
   ACL2_SIMP_TAC[]);
*)

(*
     [oracles: DEFUN COMMON-LISP::NOT, DISK_THM] [axioms: ] []
     |- not p = ite p nil t,
*)

(* Moved to sexpScript.sml
val not_def =
 acl2Define "COMMON-LISP::NOT"
  `not p = ite p nil t`;
*)

(*
     [oracles: DEFUN ACL2::HIDE] [axioms: ] [] |- hide x = x,
*)

val hide_def =
 acl2Define "ACL2::HIDE"
  `hide x = x`;

(*
     [oracles: DEFUN COMMON-LISP::EQ] [axioms: ] [] |- eq x y = equal x y,
*)

val eq_def =
 acl2Define "COMMON-LISP::EQ"
  `eq x y = equal x y`;

(*
     [oracles: DEFUN ACL2::TRUE-LISTP, DISK_THM] [axioms: ] []
     |- true_listp x = ite (consp x) (true_listp (cdr x)) (eq x nil),
*)

val (true_listp_def,true_listp_ind) =
 acl2_defn "ACL2::TRUE-LISTP"
  (`true_listp x = ite (consp x) (true_listp (cdr x)) (eq x nil)`,
   WF_REL_TAC `measure sexp_size`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN ACL2::LIST-MACRO, DISK_THM] [axioms: ] []
     |- list_macro lst =
        andl [consp lst; List [csym "CONS"; car lst; list_macro (cdr lst)]],
*)

val (list_macro_def,list_macro_ind) =
 acl2_defn "ACL2::LIST-MACRO"
  (`list_macro lst =
    andl [consp lst; List [csym "CONS"; car lst; list_macro (cdr lst)]]`,
   WF_REL_TAC `measure sexp_size`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN ACL2::AND-MACRO, DISK_THM] [axioms: ] []
     |- and_macro lst =
        ite (consp lst)
          (ite (consp (cdr lst))
             (List [csym "IF"; car lst; and_macro (cdr lst); nil]) (car lst))
          t,
*)

val (and_macro_def,and_macro_ind) =
 acl2_defn "ACL2::AND-MACRO"
  (`and_macro lst =
     ite (consp lst)
         (ite (consp (cdr lst))
              (List [csym "IF"; car lst; and_macro (cdr lst); nil])
              (car lst))
         t`,
   WF_REL_TAC `measure sexp_size`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN ACL2::OR-MACRO, DISK_THM] [axioms: ] []
     |- or_macro lst =
        andl
          [consp lst;
           ite (consp (cdr lst))
             (List [csym "IF"; car lst; car lst; or_macro (cdr lst)])
             (car lst)],
*)

val (or_macro_def,or_macro_ind) =
 acl2_defn "ACL2::OR-MACRO"
  (`or_macro lst =
     andl
      [consp lst;
       ite (consp (cdr lst))
           (List [csym "IF"; car lst; car lst; or_macro (cdr lst)])
           (car lst)]`,
   WF_REL_TAC `measure sexp_size`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN ACL2::INTEGER-ABS, DISK_THM] [axioms: ] []
     |- integer_abs x =
        ite (integerp x) (ite (less x (nat 0)) (unary_minus x) x) (nat 0),
*)

val integer_abs_def =
 acl2Define "ACL2::INTEGER-ABS"
  `integer_abs x =
    ite (integerp x) (ite (less x (nat 0)) (unary_minus x) x) (nat 0)`;

(*
     [oracles: DEFUN ACL2::XXXJOIN, DISK_THM] [axioms: ] []
     |- xxxjoin fn args =
        ite (cddr args) (List [fn; car args; xxxjoin fn (cdr args)])
          (cons fn args),
*)

val (xxxjoin_def,xxxjoin_ind) =
 acl2_defn "ACL2::XXXJOIN"
  (`xxxjoin fn args =
     ite (cddr args)
         (List [fn; car args; xxxjoin fn (cdr args)])
         (cons fn args)`,
   WF_REL_TAC `measure (sexp_size o SND)`
    THEN Cases_on `args`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN ACL2::LEN, DISK_THM] [axioms: ] []
     |- len x = ite (consp x) (add (nat 1) (len (cdr x))) (nat 0),
*)

val (len_def,len_ind) =
 acl2_defn "ACL2::LEN"
  (`len x = ite (consp x) (add (nat 1) (len (cdr x))) (nat 0)`,
   WF_REL_TAC `measure sexp_size`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN COMMON-LISP::LENGTH, DISK_THM] [axioms: ] []
     |- length x = ite (stringp x) (len (coerce x (csym "LIST"))) (len x),
*)

val length_def =
 acl2Define "COMMON-LISP::LENGTH"
  `length x = ite (stringp x) (len (coerce x (csym "LIST"))) (len x)`;

(*
     [oracles: DEFUN ACL2::ACL2-COUNT, DISK_THM] [axioms: ] []
     |- acl2_count x =
        itel
          [(consp x,
            add (nat 1) (add (acl2_count (car x)) (acl2_count (cdr x))));
           (rationalp x,
            ite (integerp x) (integer_abs x)
              (add (integer_abs (numerator x)) (denominator x)));
           (complex_rationalp x,
            add (nat 1)
              (add (acl2_count (realpart x)) (acl2_count (imagpart x))));
           (stringp x,length x)] (nat 0),
*)

(*
     [oracles: DEFUN ACL2::COND-CLAUSESP, DISK_THM] [axioms: ] []
     |- cond_clausesp clauses =
        ite (consp clauses)
          (andl
             [consp (car clauses); true_listp (car clauses);
              less (len (car clauses)) (nat 3);
              ite (eq (caar clauses) t) (eq (cdr clauses) nil)
                (cond_clausesp (cdr clauses))]) (eq clauses nil),
*)

val (cond_clausesp_def,cond_clausesp_ind) =
 acl2_defn
 "ACL2::COND-CLAUSESP"
  (`cond_clausesp clauses =
     ite (consp clauses)
         (andl
           [consp (car clauses); true_listp (car clauses);
            less (len (car clauses)) (nat 3);
            ite (eq (caar clauses) t)
                (eq (cdr clauses) nil)
                (cond_clausesp (cdr clauses))])
         (eq clauses nil)`,
   WF_REL_TAC `measure sexp_size`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN ACL2::COND-MACRO, DISK_THM] [axioms: ] []
     |- cond_macro clauses =
        andl
          [consp clauses;
           ite (eq (caar clauses) t)
             (ite (cdar clauses) (cadar clauses) (caar clauses))
             (List
                [csym "IF"; caar clauses;
                 ite (cdar clauses) (cadar clauses) (caar clauses);
                 cond_macro (cdr clauses)])],
*)

(*
     [oracles: DEFUN ACL2::EQLABLEP, DISK_THM] [axioms: ] []
     |- eqlablep x =
        itel [(acl2_numberp x,acl2_numberp x); (symbolp x,symbolp x)]
          (characterp x),
*)

val eqlablep_def =
 acl2Define "ACL2::EQLABLEP"
  `eqlablep x =
    itel [(acl2_numberp x,acl2_numberp x); (symbolp x,symbolp x)]
         (characterp x)`;

(*
     [oracles: DEFUN ACL2::EQLABLE-LISTP, DISK_THM] [axioms: ] []
     |- eqlable_listp l =
        ite (consp l) (andl [eqlablep (car l); eqlable_listp (cdr l)])
          (equal l nil),
*)

val (eqlable_listp_def,eqlable_listp_ind) =
 acl2_defn
 "ACL2::EQLABLE-LISTP"
  (`eqlable_listp l =
     ite (consp l)
         (andl [eqlablep (car l); eqlable_listp (cdr l)])
         (equal l nil)`,
   WF_REL_TAC `measure sexp_size`
    THEN ACL2_SIMP_TAC []);

val eqlable_listp =
 store_thm
  ("eqlable_listp",
   ``(eqlable_listp (cons s s0) =
       if itel
           [(acl2_numberp s,acl2_numberp s);
            (symbolp s,symbolp s)] (characterp s) = nil
        then nil
        else eqlable_listp s0)
     /\
     (eqlable_listp (num n) = nil)
     /\
     (eqlable_listp (chr c) = nil)
     /\
     (eqlable_listp (str st) = nil)
     /\
     (eqlable_listp (sym st st0) = if sym st st0 = nil then t else nil)``,
   REPEAT CONJ_TAC
    THEN CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[eqlable_listp_def]))
    THEN ACL2_SIMP_TAC[]);

val _ = add_acl2_simps[eqlable_listp];

(*
     [oracles: DEFUN COMMON-LISP::ATOM] [axioms: ] []
     |- atom x = not (consp x),
*)

val atom_def =
 acl2Define "COMMON-LISP::ATOM"
  `atom x = not (consp x)`;

(*
     [oracles: DEFUN ACL2::MAKE-CHARACTER-LIST, DISK_THM] [axioms: ] []
     |- acl2_make_character_list x =
        itel
          [(atom x,nil);
           (characterp (car x),
            cons (car x) (acl2_make_character_list (cdr x)))]
          (cons (code_char (nat 0)) (acl2_make_character_list (cdr x))),
*)

val (acl2_make_character_list_def,acl2_make_character_list_ind) =
 acl2_defn
 "ACL2::MAKE-CHARACTER-LIST"
  (`acl2_make_character_list x =
     itel
      [(atom x,nil);
       (characterp (car x),
        cons (car x) (acl2_make_character_list (cdr x)))]
      (cons (code_char (nat 0)) (acl2_make_character_list (cdr x)))`,
   WF_REL_TAC `measure sexp_size`
    THEN ACL2_SIMP_TAC []);

val acl2_make_character_list =
 store_thm
  ("acl2_make_character_list",
   ``(acl2_make_character_list (cons s s0) =
       if characterp s = nil
        then cons (code_char (nat 0)) (acl2_make_character_list s0)
        else cons s (acl2_make_character_list s0))
     /\
     (acl2_make_character_list (num n) = nil)
     /\
     (acl2_make_character_list (chr c) = nil)
     /\
     (acl2_make_character_list (str st) = nil)
     /\
     (acl2_make_character_list (sym st st0) = nil)``,
   REPEAT CONJ_TAC
    THEN CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[acl2_make_character_list_def]))
    THEN ACL2_SIMP_TAC[itel_def]);

val _ = add_acl2_simps[acl2_make_character_list];

(*
     [oracles: DEFUN ACL2::EQLABLE-ALISTP, DISK_THM] [axioms: ] []
     |- eqlable_alistp x =
        ite (atom x) (equal x nil)
          (andl [consp (car x); eqlablep (caar x); eqlable_alistp (cdr x)]),
*)

val (eqlable_alistp_def,eqlable_alistp_ind) =
 acl2_defn
 "ACL2::EQLABLE-ALISTP"
  (`eqlable_alistp x =
     ite (atom x)
         (equal x nil)
         (andl [consp (car x); eqlablep (caar x); eqlable_alistp (cdr x)])`,
   WF_REL_TAC `measure sexp_size`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN ACL2::ALISTP, DISK_THM] [axioms: ] []
     |- alistp l =
        ite (atom l) (eq l nil) (andl [consp (car l); alistp (cdr l)]),
*)

val (alistp_def,alistp_ind) =
 acl2_defn
 "ACL2::ALISTP"
  (`alistp l =
     ite (atom l) (eq l nil) (andl [consp (car l); alistp (cdr l)])`,
   WF_REL_TAC `measure sexp_size`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN COMMON-LISP::ACONS] [axioms: ] []
     |- acons key datum alist = cons (cons key datum) alist,
*)

val acons_def =
 acl2Define "COMMON-LISP::ACONS"
  `acons key datum alist = cons (cons key datum) alist`;

(*
     [oracles: DEFUN COMMON-LISP::ENDP] [axioms: ] [] |- endp x = atom x,
*)

val endp_def =
 acl2Define "COMMON-LISP::ENDP"
  `endp x = atom x`;

(*
     [oracles: DEFUN ACL2::MUST-BE-EQUAL] [axioms: ] []
     |- must_be_equal logic exec = logic,
*)

(*
     [oracles: DEFUN ACL2::MEMBER-EQUAL, DISK_THM] [axioms: ] []
     |- member_equal x lst =
        itel [(endp lst,nil); (equal x (car lst),lst)]
          (member_equal x (cdr lst)),
*)

val (member_equal_def,member_equal_ind) =
 acl2_defn "ACL2::MEMBER-EQUAL"
  (`member_equal x lst =
     itel [(endp lst,nil); (equal x (car lst),lst)]
          (member_equal x (cdr lst))`,
   WF_REL_TAC `measure (sexp_size o SND)`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN ACL2::UNION-EQUAL, DISK_THM] [axioms: ] []
     |- union_equal x y =
        itel [(endp x,y); (member_equal (car x) y,union_equal (cdr x) y)]
          (cons (car x) (union_equal (cdr x) y)),
*)

(*
     [oracles: DEFUN ACL2::SUBSETP-EQUAL, DISK_THM] [axioms: ] []
     |- subsetp_equal x y =
        ite (endp x) t
          (andl [member_equal (car x) y; subsetp_equal (cdr x) y]),
*)

(*
     [oracles: DEFUN ACL2::SYMBOL-LISTP, DISK_THM] [axioms: ] []
     |- symbol_listp lst =
        ite (atom lst) (eq lst nil)
          (andl [symbolp (car lst); symbol_listp (cdr lst)]),
*)

(*
     [oracles: DEFUN COMMON-LISP::NULL] [axioms: ] [] |- null x = eq x nil,
*)

val null_def =
 acl2Define "COMMON-LISP::NULL"
  `null x = eq x nil`;

(*
     [oracles: DEFUN ACL2::MEMBER-EQ, DISK_THM] [axioms: ] []
     |- member_eq x lst =
        itel [(endp lst,nil); (eq x (car lst),lst)] (member_eq x (cdr lst)),
*)

(*
     [oracles: DEFUN ACL2::SUBSETP-EQ, DISK_THM] [axioms: ] []
     |- subsetp_eq x y =
        ite (endp x) t (andl [member_eq (car x) y; subsetp_eq (cdr x) y]),
*)

(*
     [oracles: DEFUN ACL2::SYMBOL-ALISTP, DISK_THM] [axioms: ] []
     |- symbol_alistp x =
        ite (atom x) (eq x nil)
          (andl [consp (car x); symbolp (caar x); symbol_alistp (cdr x)]),
*)

(*
     [oracles: DEFUN ACL2::ASSOC-EQ, DISK_THM] [axioms: ] []
     |- assoc_eq x alist =
        itel [(endp alist,nil); (eq x (caar alist),car alist)]
          (assoc_eq x (cdr alist)),
*)

(*
     [oracles: DEFUN ACL2::ASSOC-EQUAL, DISK_THM] [axioms: ] []
     |- assoc_equal x alist =
        itel [(endp alist,nil); (equal x (caar alist),car alist)]
          (assoc_equal x (cdr alist)),
*)

(*
     [oracles: DEFUN ACL2::ASSOC-EQ-EQUAL-ALISTP, DISK_THM] [axioms: ] []
     |- assoc_eq_equal_alistp x =
        ite (atom x) (eq x nil)
          (andl
             [consp (car x); symbolp (caar x); consp (cdar x);
              assoc_eq_equal_alistp (cdr x)]),
*)

(*
     [oracles: DEFUN ACL2::ASSOC-EQ-EQUAL, DISK_THM] [axioms: ] []
     |- assoc_eq_equal x y alist =
        itel
          [(endp alist,nil);
           (andl [eq (caar alist) x; equal (cadar alist) y],car alist)]
          (assoc_eq_equal x y (cdr alist)),
*)

(*
     [oracles: DEFUN ACL2::NO-DUPLICATESP-EQUAL, DISK_THM] [axioms: ] []
     |- no_duplicatesp_equal l =
        itel [(endp l,t); (member_equal (car l) (cdr l),nil)]
          (no_duplicatesp_equal (cdr l)),
*)

(*
     [oracles: DEFUN ACL2::STRIP-CARS, DISK_THM] [axioms: ] []
     |- strip_cars x = ite (endp x) nil (cons (caar x) (strip_cars (cdr x))),
*)

(*
     [oracles: DEFUN COMMON-LISP::EQL] [axioms: ] [] |- eql x y = equal x y,
*)

val eql_def =
 acl2Define "COMMON-LISP::EQL"
  `eql x y = equal x y`;

(*
     [oracles: DEFUN COMMON-LISP::=] [axioms: ] []
     |- common_lisp_equal x y = equal x y,
*)

val common_lisp_equal_def =
 acl2Define "COMMON-LISP::="
  `common_lisp_equal x y = equal x y`;

(*
     [oracles: DEFUN COMMON-LISP::/=] [axioms: ] []
     |- slash_equal x y = not (equal x y),
*)

(*
     [oracles: DEFUN ACL2::ZP, DISK_THM] [axioms: ] []
     |- zp x = ite (integerp x) (not (less (nat 0) x)) t,
*)

val zp_def =
 acl2Define "ACL2::ZP"
  `zp x = ite (integerp x) (not (less (cpx 0 1 0 1) x)) t`;

val zp =
 store_thm
  ("zp",
   ``zp x = ite (integerp x) (not (less (nat 0) x)) t``,
   RW_TAC std_ss [zp_def,nat_def,int_def]);

(*
     [oracles: DEFUN ACL2::ZIP, DISK_THM] [axioms: ] []
     |- zip x = ite (integerp x) (common_lisp_equal x (nat 0)) t,
*)

val zip_def =
 acl2Define "ACL2::ZIP"
  `zip x = ite (integerp x) (equal x (cpx 0 1 0 1)) t`;

val zip =
 store_thm
  ("zip",
   ``zip x = ite (integerp x) (common_lisp_equal x (nat 0)) t``,
   RW_TAC std_ss [common_lisp_equal_def,zip_def,nat_def,int_def]);

(*
     [oracles: DEFUN COMMON-LISP::NTH, DISK_THM] [axioms: ] []
     |- nth n l =
        itel [(endp l,nil); (zp n,car l)] (nth (add (int ~1) n) (cdr l)),
*)

(*
     [oracles: DEFUN COMMON-LISP::CHAR, DISK_THM] [axioms: ] []
     |- char s n = nth n (coerce s (csym "LIST")),
*)

(*
     [oracles: DEFUN ACL2::PROPER-CONSP, DISK_THM] [axioms: ] []
     |- proper_consp x = andl [consp x; true_listp x],
*)

(*
     [oracles: DEFUN ACL2::IMPROPER-CONSP, DISK_THM] [axioms: ] []
     |- improper_consp x = andl [consp x; not (true_listp x)],
*)

(*
     [oracles: DEFUN COMMON-LISP::CONJUGATE, DISK_THM] [axioms: ] []
     |- conjugate x =
        ite (complex_rationalp x)
          (complex (realpart x) (unary_minus (imagpart x))) x,
*)

(*
     [oracles: DEFUN ACL2::PROG2$] [axioms: ] [] |- prog2_dollar x y = y,
*)

(*
     [oracles: DEFUN ACL2::TIME$] [axioms: ] [] |- time_dollar x = x,
*)

(*
     [oracles: DEFUN ACL2::FIX, DISK_THM] [axioms: ] []
     |- fix x = ite (acl2_numberp x) x (nat 0),
*)

val fix_def =
 acl2Define "ACL2::FIX"
  `fix x = ite (acl2_numberp x) x (cpx 0 1 0 1)`;

val fix =
 store_thm
  ("fix",
   ``fix x = ite (acl2_numberp x) x (nat 0)``,
   RW_TAC std_ss [fix_def,nat_def,int_def]);

(*
     [oracles: DEFUN ACL2::FORCE] [axioms: ] [] |- force x = x,
*)

val force_def =
 Define `force(s:sexp) = s`;

(*
     [oracles: DEFUN ACL2::IMMEDIATE-FORCE-MODEP] [axioms: ] []
     |- immediate_force_modep = str "See :DOC immediate-force-modep.",
*)

(*
     [oracles: DEFUN ACL2::CASE-SPLIT] [axioms: ] [] |- case_split x = x,
*)

(*
     [oracles: DEFUN ACL2::SYNP] [axioms: ] [] |- synp vars form term = t,
*)

(*
     [oracles: DEFUN COMMON-LISP::MEMBER, DISK_THM] [axioms: ] []
     |- member x l =
        itel [(endp l,nil); (eql x (car l),l)] (member x (cdr l)),
*)

val (member_def,member_ind) =
 acl2_defn "COMMON-LISP::MEMBER"
  (`member x l =
     itel [(endp l,nil); (eql x (car l),l)] (member x (cdr l))`,
   WF_REL_TAC `measure (sexp_size o SND)`
    THEN ACL2_SIMP_TAC[]);

(*
     [oracles: DEFUN ACL2::NO-DUPLICATESP, DISK_THM] [axioms: ] []
     |- no_duplicatesp l =
        itel [(endp l,t); (member (car l) (cdr l),nil)]
          (no_duplicatesp (cdr l)),
*)

(*
     [oracles: DEFUN COMMON-LISP::ASSOC, DISK_THM] [axioms: ] []
     |- assoc x alist =
        itel [(endp alist,nil); (eql x (caar alist),car alist)]
          (assoc x (cdr alist)),
*)

val (assoc_def,assoc_ind) =
 acl2_defn "COMMON-LISP::ASSOC"
  (`assoc x alist =
      itel [(endp alist,nil); (eql x (caar alist),car alist)]
           (assoc x (cdr alist))`,
   WF_REL_TAC `measure (sexp_size o SND)`
    THEN ACL2_SIMP_TAC[]);

(*
     [oracles: DEFUN ACL2::R-EQLABLE-ALISTP, DISK_THM] [axioms: ] []
     |- r_eqlable_alistp x =
        ite (atom x) (equal x nil)
          (andl [consp (car x); eqlablep (cdar x); r_eqlable_alistp (cdr x)]),
*)

(*
     [oracles: DEFUN COMMON-LISP::RASSOC, DISK_THM] [axioms: ] []
     |- rassoc x alist =
        itel [(endp alist,nil); (eql x (cdar alist),car alist)]
          (rassoc x (cdr alist)),
*)

(*
     [oracles: DEFUN ACL2::RASSOC-EQUAL, DISK_THM] [axioms: ] []
     |- rassoc_equal x alist =
        itel [(endp alist,nil); (equal x (cdar alist),car alist)]
          (rassoc_equal x (cdr alist)),
*)

(*
     [oracles: DEFUN ACL2::R-SYMBOL-ALISTP, DISK_THM] [axioms: ] []
     |- r_symbol_alistp x =
        ite (atom x) (equal x nil)
          (andl [consp (car x); symbolp (cdar x); r_symbol_alistp (cdr x)]),
*)

(*
     [oracles: DEFUN ACL2::RASSOC-EQ, DISK_THM] [axioms: ] []
     |- rassoc_eq x alist =
        itel [(endp alist,nil); (eq x (cdar alist),car alist)]
          (rassoc_eq x (cdr alist)),
*)

(*
     [oracles: DEFUN COMMON-LISP::STANDARD-CHAR-P, DISK_THM] [axioms: ] []
     |- standard_char_p x =
         andl
          [member x
             (List
                [chr #"\n"; chr #" "; chr #"!"; chr #"\""; chr #"#";
                 chr #"$"; chr #"%"; chr #"&"; chr #"'"; chr #"("; chr #")";
                 chr #"*"; chr #"+"; chr #","; chr #"-"; chr #"."; chr #"/";
                 chr #"0"; chr #"1"; chr #"2"; chr #"3"; chr #"4"; chr #"5";
                 chr #"6"; chr #"7"; chr #"8"; chr #"9"; chr #":"; chr #";";
                 chr #"<"; chr #"="; chr #">"; chr #"?"; chr #"@"; chr #"A";
                 chr #"B"; chr #"C"; chr #"D"; chr #"E"; chr #"F"; chr #"G";
                 chr #"H"; chr #"I"; chr #"J"; chr #"K"; chr #"L"; chr #"M";
                 chr #"N"; chr #"O"; chr #"P"; chr #"Q"; chr #"R"; chr #"S";
                 chr #"T"; chr #"U"; chr #"V"; chr #"W"; chr #"X"; chr #"Y";
                 chr #"Z"; chr #"["; chr #"\\"; chr #"]"; chr #"^"; chr #"_";
                 chr #"`"; chr #"a"; chr #"b"; chr #"c"; chr #"d"; chr #"e";
                 chr #"f"; chr #"g"; chr #"h"; chr #"i"; chr #"j"; chr #"k";
                 chr #"l"; chr #"m"; chr #"n"; chr #"o"; chr #"p"; chr #"q";
                 chr #"r"; chr #"s"; chr #"t"; chr #"u"; chr #"v"; chr #"w";
                 chr #"x"; chr #"y"; chr #"z"; chr #"{"; chr #"|"; chr #"}";
                 chr #"~"]); t],
*)

val standard_char_p_def =
 acl2Define "COMMON-LISP::STANDARD-CHAR-P"
  `standard_char_p x =
    andl
     [member x
        (List (MAP chr
          [ #"\n"; #" "; #"!"; #"\""; #"#";
            #"$"; #"%"; #"&"; #"'"; #"("; #")";
            #"*"; #"+"; #";"; #"-"; #"."; #"/";
            #"0"; #"1"; #"2"; #"3"; #"4"; #"5";
            #"6"; #"7"; #"8"; #"9"; #":"; #";";
            #"<"; #"="; #">"; #"?"; #"@"; #"A";
            #"B"; #"C"; #"D"; #"E"; #"F"; #"G";
            #"H"; #"I"; #"J"; #"K"; #"L"; #"M";
            #"N"; #"O"; #"P"; #"Q"; #"R"; #"S";
            #"T"; #"U"; #"V"; #"W"; #"X"; #"Y";
            #"Z"; #"["; #"\\"; #"]"; #"^^"; #"_";
            #"^`"; #"a"; #"b"; #"c"; #"d"; #"e";
            #"f"; #"g"; #"h"; #"i"; #"j"; #"k";
            #"l"; #"m"; #"n"; #"o"; #"p"; #"q";
            #"r"; #"s"; #"t"; #"u"; #"v"; #"w";
            #"x"; #"y"; #"z"; #"{"; #"|"; #"}";
            #"~"])); t]`;



(*
- REWRITE_RULE [listTheory.MAP]standard_char_p_def;
> val it =
    |- !x.
         standard_char_p x =
         andl
           [member x
              (List
                 [chr #"\n"; chr #" "; chr #"!"; chr #"\""; chr #"#";
                  chr #"$"; chr #"%"; chr #"&"; chr #"'"; chr #"(";
                  chr #")"; chr #"*"; chr #"+"; chr #","; chr #"-";
                  chr #"."; chr #"/"; chr #"0"; chr #"1"; chr #"2";
                  chr #"3"; chr #"4"; chr #"5"; chr #"6"; chr #"7";
                  chr #"8"; chr #"9"; chr #":"; chr #";"; chr #"<";
                  chr #"="; chr #">"; chr #"?"; chr #"@"; chr #"A";
                  chr #"B"; chr #"C"; chr #"D"; chr #"E"; chr #"F";
                  chr #"G"; chr #"H"; chr #"I"; chr #"J"; chr #"K";
                  chr #"L"; chr #"M"; chr #"N"; chr #"O"; chr #"P";
                  chr #"Q"; chr #"R"; chr #"S"; chr #"T"; chr #"U";
                  chr #"V"; chr #"W"; chr #"X"; chr #"Y"; chr #"Z";
                  chr #"["; chr #"\\"; chr #"]"; chr #"^"; chr #"_";
                  chr #"`"; chr #"a"; chr #"b"; chr #"c"; chr #"d";
                  chr #"e"; chr #"f"; chr #"g"; chr #"h"; chr #"i";
                  chr #"j"; chr #"k"; chr #"l"; chr #"m"; chr #"n";
                  chr #"o"; chr #"p"; chr #"q"; chr #"r"; chr #"s";
                  chr #"t"; chr #"u"; chr #"v"; chr #"w"; chr #"x";
                  chr #"y"; chr #"z"; chr #"{"; chr #"|"; chr #"}";
                  chr #"~"]); t] : thm
*)

val standard_char_p =
 save_thm
  ("standard_char_p",
   REWRITE_RULE [listTheory.MAP]standard_char_p_def);

(*
     [oracles: DEFUN ACL2::STANDARD-CHAR-LISTP, DISK_THM] [axioms: ] []
     |- standard_char_listp l =
        ite (consp l)
          (andl
             [characterp (car l); standard_char_p (car l);
              standard_char_listp (cdr l)]) (equal l nil),
*)

val (standard_char_listp_def,standard_char_listp_ind) =
 acl2_defn "ACL2::STANDARD-CHAR-LISTP"
  (`standard_char_listp l =
     ite (consp l)
         (andl
           [characterp (car l); standard_char_p (car l);
            standard_char_listp (cdr l)])
         (equal l nil)`,
   WF_REL_TAC `measure sexp_size`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN ACL2::CHARACTER-LISTP, DISK_THM] [axioms: ] []
     |- character_listp l =
        ite (atom l) (equal l nil)
          (andl [characterp (car l); character_listp (cdr l)]),
*)

val (character_listp_def,character_listp_ind) =
 acl2_defn "ACL2::CHARACTER-LISTP"
  (`character_listp l =
     ite (atom l) (equal l nil)
         (andl [characterp (car l); character_listp (cdr l)])`,
   ACL2_SIMP_TAC[]
    THEN WF_REL_TAC `measure sexp_size`
    THEN Cases
    THEN ACL2_FULL_SIMP_TAC[]);

val character_listp =
 store_thm
  ("character_listp",
   ``(character_listp (cons s s0) =
       if characterp s = nil then nil else character_listp s0)
     /\
     (character_listp (num n) = nil)
     /\
     (character_listp (chr c) = nil)
     /\
     (character_listp (str st) = nil)
     /\
     (character_listp (sym st st0) = if sym st st0 = nil then t else nil)``,
   REPEAT CONJ_TAC
    THEN CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[character_listp_def]))
    THEN ACL2_SIMP_TAC[]);

val _ = add_acl2_simps[character_listp];

(*
     [oracles: DEFUN COMMON-LISP::STRING, DISK_THM] [axioms: ] []
     |- string x =
        itel [(stringp x,x); (symbolp x,symbol_name x)]
          (coerce (List [x]) (csym "STRING")),
*)

val string_def =
 acl2Define "COMMON-LISP::STRING"
  `string x =
    itel [(stringp x,x); (symbolp x,symbol_name x)]
         (coerce (List [x]) (csym "STRING"))`;

(*
     [oracles: DEFUN COMMON-LISP::ALPHA-CHAR-P, DISK_THM] [axioms: ] []
     |- alpha_char_p x =
        andl
          [member x
             (List
                [chr #"a"; chr #"b"; chr #"c"; chr #"d"; chr #"e"; chr #"f";
                 chr #"g"; chr #"h"; chr #"i"; chr #"j"; chr #"k"; chr #"l";
                 chr #"m"; chr #"n"; chr #"o"; chr #"p"; chr #"q"; chr #"r";
                 chr #"s"; chr #"t"; chr #"u"; chr #"v"; chr #"w"; chr #"x";
                 chr #"y"; chr #"z"; chr #"A"; chr #"B"; chr #"C"; chr #"D";
                 chr #"E"; chr #"F"; chr #"G"; chr #"H"; chr #"I"; chr #"J";
                 chr #"K"; chr #"L"; chr #"M"; chr #"N"; chr #"O"; chr #"P";
                 chr #"Q"; chr #"R"; chr #"S"; chr #"T"; chr #"U"; chr #"V";
                 chr #"W"; chr #"X"; chr #"Y"; chr #"Z"]); t],
*)

val alpha_char_p_def =
 acl2Define "COMMON-LISP::ALPHA-CHAR-P"
  `alpha_char_p x =
    andl
      [member x
         (List
            [chr #"a"; chr #"b"; chr #"c"; chr #"d"; chr #"e"; chr #"f";
             chr #"g"; chr #"h"; chr #"i"; chr #"j"; chr #"k"; chr #"l";
             chr #"m"; chr #"n"; chr #"o"; chr #"p"; chr #"q"; chr #"r";
             chr #"s"; chr #"t"; chr #"u"; chr #"v"; chr #"w"; chr #"x";
             chr #"y"; chr #"z"; chr #"A"; chr #"B"; chr #"C"; chr #"D";
             chr #"E"; chr #"F"; chr #"G"; chr #"H"; chr #"I"; chr #"J";
             chr #"K"; chr #"L"; chr #"M"; chr #"N"; chr #"O"; chr #"P";
             chr #"Q"; chr #"R"; chr #"S"; chr #"T"; chr #"U"; chr #"V";
             chr #"W"; chr #"X"; chr #"Y"; chr #"Z"]); t]`;

(*
     [oracles: DEFUN COMMON-LISP::UPPER-CASE-P, DISK_THM] [axioms: ] []
     |- upper_case_p x =
        andl
          [member x
             (List
                [chr #"A"; chr #"B"; chr #"C"; chr #"D"; chr #"E"; chr #"F";
                 chr #"G"; chr #"H"; chr #"I"; chr #"J"; chr #"K"; chr #"L";
                 chr #"M"; chr #"N"; chr #"O"; chr #"P"; chr #"Q"; chr #"R";
                 chr #"S"; chr #"T"; chr #"U"; chr #"V"; chr #"W"; chr #"X";
                 chr #"Y"; chr #"Z"]); t],
*)

val upper_case_p_def =
 acl2Define "COMMON-LISP::UPPER-CASE-P"
  `upper_case_p x =
    andl
      [member x
         (List
            [chr #"A"; chr #"B"; chr #"C"; chr #"D"; chr #"E"; chr #"F";
             chr #"G"; chr #"H"; chr #"I"; chr #"J"; chr #"K"; chr #"L";
             chr #"M"; chr #"N"; chr #"O"; chr #"P"; chr #"Q"; chr #"R";
             chr #"S"; chr #"T"; chr #"U"; chr #"V"; chr #"W"; chr #"X";
             chr #"Y"; chr #"Z"]); t]`;

(*
     [oracles: DEFUN COMMON-LISP::LOWER-CASE-P, DISK_THM] [axioms: ] []
     |- lower_case_p x =
        andl
          [member x
             (List
                [chr #"a"; chr #"b"; chr #"c"; chr #"d"; chr #"e"; chr #"f";
                 chr #"g"; chr #"h"; chr #"i"; chr #"j"; chr #"k"; chr #"l";
                 chr #"m"; chr #"n"; chr #"o"; chr #"p"; chr #"q"; chr #"r";
                 chr #"s"; chr #"t"; chr #"u"; chr #"v"; chr #"w"; chr #"x";
                 chr #"y"; chr #"z"]); t],
*)

val lower_case_p_def =
 acl2Define "COMMON-LISP::LOWER-CASE-P"
  `lower_case_p x =
    andl
      [member x
         (List
            [chr #"a"; chr #"b"; chr #"c"; chr #"d"; chr #"e"; chr #"f";
             chr #"g"; chr #"h"; chr #"i"; chr #"j"; chr #"k"; chr #"l";
             chr #"m"; chr #"n"; chr #"o"; chr #"p"; chr #"q"; chr #"r";
             chr #"s"; chr #"t"; chr #"u"; chr #"v"; chr #"w"; chr #"x";
             chr #"y"; chr #"z"]); t]`;

(*
     [oracles: DEFUN COMMON-LISP::CHAR-UPCASE, DISK_THM] [axioms: ] []
     |- char_upcase x =
        (let pair =
               assoc x
                 (List
                    [cons (chr #"a") (chr #"A"); cons (chr #"b") (chr #"B");
                     cons (chr #"c") (chr #"C"); cons (chr #"d") (chr #"D");
                     cons (chr #"e") (chr #"E"); cons (chr #"f") (chr #"F");
                     cons (chr #"g") (chr #"G"); cons (chr #"h") (chr #"H");
                     cons (chr #"i") (chr #"I"); cons (chr #"j") (chr #"J");
                     cons (chr #"k") (chr #"K"); cons (chr #"l") (chr #"L");
                     cons (chr #"m") (chr #"M"); cons (chr #"n") (chr #"N");
                     cons (chr #"o") (chr #"O"); cons (chr #"p") (chr #"P");
                     cons (chr #"q") (chr #"Q"); cons (chr #"r") (chr #"R");
                     cons (chr #"s") (chr #"S"); cons (chr #"t") (chr #"T");
                     cons (chr #"u") (chr #"U"); cons (chr #"v") (chr #"V");
                     cons (chr #"w") (chr #"W"); cons (chr #"x") (chr #"X");
                     cons (chr #"y") (chr #"Y"); cons (chr #"z") (chr #"Z")])
         in
           itel [(pair,cdr pair); (characterp x,x)] (code_char (nat 0))),
*)

val char_upcase_def =
 acl2Define "COMMON-LISP::CHAR-UPCASE"
  `char_upcase x =
    (let pair =
           assoc x
             (List
                [cons (chr #"a") (chr #"A"); cons (chr #"b") (chr #"B");
                 cons (chr #"c") (chr #"C"); cons (chr #"d") (chr #"D");
                 cons (chr #"e") (chr #"E"); cons (chr #"f") (chr #"F");
                 cons (chr #"g") (chr #"G"); cons (chr #"h") (chr #"H");
                 cons (chr #"i") (chr #"I"); cons (chr #"j") (chr #"J");
                 cons (chr #"k") (chr #"K"); cons (chr #"l") (chr #"L");
                 cons (chr #"m") (chr #"M"); cons (chr #"n") (chr #"N");
                 cons (chr #"o") (chr #"O"); cons (chr #"p") (chr #"P");
                 cons (chr #"q") (chr #"Q"); cons (chr #"r") (chr #"R");
                 cons (chr #"s") (chr #"S"); cons (chr #"t") (chr #"T");
                 cons (chr #"u") (chr #"U"); cons (chr #"v") (chr #"V");
                 cons (chr #"w") (chr #"W"); cons (chr #"x") (chr #"X");
                 cons (chr #"y") (chr #"Y"); cons (chr #"z") (chr #"Z")])
     in
       itel [(pair,cdr pair); (characterp x,x)] (code_char (nat 0)))`;

(*
     [oracles: DEFUN COMMON-LISP::CHAR-DOWNCASE, DISK_THM] [axioms: ] []
     |- char_downcase x =
        (let pair =
               assoc x
                 (List
                    [cons (chr #"A") (chr #"a"); cons (chr #"B") (chr #"b");
                     cons (chr #"C") (chr #"c"); cons (chr #"D") (chr #"d");
                     cons (chr #"E") (chr #"e"); cons (chr #"F") (chr #"f");
                     cons (chr #"G") (chr #"g"); cons (chr #"H") (chr #"h");
                     cons (chr #"I") (chr #"i"); cons (chr #"J") (chr #"j");
                     cons (chr #"K") (chr #"k"); cons (chr #"L") (chr #"l");
                     cons (chr #"M") (chr #"m"); cons (chr #"N") (chr #"n");
                     cons (chr #"O") (chr #"o"); cons (chr #"P") (chr #"p");
                     cons (chr #"Q") (chr #"q"); cons (chr #"R") (chr #"r");
                     cons (chr #"S") (chr #"s"); cons (chr #"T") (chr #"t");
                     cons (chr #"U") (chr #"u"); cons (chr #"V") (chr #"v");
                     cons (chr #"W") (chr #"w"); cons (chr #"X") (chr #"x");
                     cons (chr #"Y") (chr #"y"); cons (chr #"Z") (chr #"z")])
         in
           itel [(pair,cdr pair); (characterp x,x)] (code_char (nat 0))),
*)

val char_downcase_def =
 acl2Define "COMMON-LISP::CHAR-DOWNCASE"
  `char_downcase x =
        (let pair =
               assoc x
                 (List
                    [cons (chr #"A") (chr #"a"); cons (chr #"B") (chr #"b");
                     cons (chr #"C") (chr #"c"); cons (chr #"D") (chr #"d");
                     cons (chr #"E") (chr #"e"); cons (chr #"F") (chr #"f");
                     cons (chr #"G") (chr #"g"); cons (chr #"H") (chr #"h");
                     cons (chr #"I") (chr #"i"); cons (chr #"J") (chr #"j");
                     cons (chr #"K") (chr #"k"); cons (chr #"L") (chr #"l");
                     cons (chr #"M") (chr #"m"); cons (chr #"N") (chr #"n");
                     cons (chr #"O") (chr #"o"); cons (chr #"P") (chr #"p");
                     cons (chr #"Q") (chr #"q"); cons (chr #"R") (chr #"r");
                     cons (chr #"S") (chr #"s"); cons (chr #"T") (chr #"t");
                     cons (chr #"U") (chr #"u"); cons (chr #"V") (chr #"v");
                     cons (chr #"W") (chr #"w"); cons (chr #"X") (chr #"x");
                     cons (chr #"Y") (chr #"y"); cons (chr #"Z") (chr #"z")])
         in
           itel [(pair,cdr pair); (characterp x,x)] (code_char (nat 0)))`;

(*
     [oracles: DEFUN ACL2::STRING-DOWNCASE1, DISK_THM] [axioms: ] []
     |- string_downcase1 l =
        ite (atom l) nil
          (cons (char_downcase (car l)) (string_downcase1 (cdr l))),
*)

val (string_downcase1_def,string_downcase1_ind) =
 acl2_defn "ACL2::STRING-DOWNCASE1"
  (`string_downcase1 l =
     ite (atom l) nil
         (cons (char_downcase (car l)) (string_downcase1 (cdr l)))`,
   WF_REL_TAC `measure sexp_size`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN COMMON-LISP::STRING-DOWNCASE, DISK_THM] [axioms: ] []
     |- string_downcase x =
        coerce (string_downcase1 (coerce x (csym "LIST"))) (csym "STRING"),
*)

val string_downcase_def =
 acl2Define "COMMON-LISP::STRING-DOWNCASE"
  `string_downcase x =
    coerce (string_downcase1 (coerce x (csym "LIST"))) (csym "STRING")`;

(*
     [oracles: DEFUN ACL2::STRING-UPCASE1, DISK_THM] [axioms: ] []
     |- string_upcase1 l =
        ite (atom l) nil
          (cons (char_upcase (car l)) (string_upcase1 (cdr l))),
*)

val (string_upcase1_def,string_upcase1_ind) =
 acl2_defn "ACL2::STRING-UPCASE1"
  (`string_upcase1 l =
     ite (atom l) nil
         (cons (char_upcase (car l)) (string_upcase1 (cdr l)))`,
   WF_REL_TAC `measure sexp_size`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN COMMON-LISP::STRING-UPCASE, DISK_THM] [axioms: ] []
     |- string_upcase x =
        coerce (string_upcase1 (coerce x (csym "LIST"))) (csym "STRING"),
*)

val string_upcase_def =
 acl2Define "COMMON-LISP::STRING-UPCASE"
  `string_upcase x =
    coerce (string_upcase1 (coerce x (csym "LIST"))) (csym "STRING")`;

(*
     [oracles: DEFUN ACL2::OUR-DIGIT-CHAR-P, DISK_THM] [axioms: ] []
     |- our_digit_char_p ch radix =
        (let l =
               assoc ch
                 (List
                    [cons (chr #"0") (nat 0); cons (chr #"1") (nat 1);
                     cons (chr #"2") (nat 2); cons (chr #"3") (nat 3);
                     cons (chr #"4") (nat 4); cons (chr #"5") (nat 5);
                     cons (chr #"6") (nat 6); cons (chr #"7") (nat 7);
                     cons (chr #"8") (nat 8); cons (chr #"9") (nat 9);
                     cons (chr #"a") (nat 10); cons (chr #"b") (nat 11);
                     cons (chr #"c") (nat 12); cons (chr #"d") (nat 13);
                     cons (chr #"e") (nat 14); cons (chr #"f") (nat 15);
                     cons (chr #"g") (nat 16); cons (chr #"h") (nat 17);
                     cons (chr #"i") (nat 18); cons (chr #"j") (nat 19);
                     cons (chr #"k") (nat 20); cons (chr #"l") (nat 21);
                     cons (chr #"m") (nat 22); cons (chr #"n") (nat 23);
                     cons (chr #"o") (nat 24); cons (chr #"p") (nat 25);
                     cons (chr #"q") (nat 26); cons (chr #"r") (nat 27);
                     cons (chr #"s") (nat 28); cons (chr #"t") (nat 29);
                     cons (chr #"u") (nat 30); cons (chr #"v") (nat 31);
                     cons (chr #"w") (nat 32); cons (chr #"x") (nat 33);
                     cons (chr #"y") (nat 34); cons (chr #"z") (nat 35);
                     cons (chr #"A") (nat 10); cons (chr #"B") (nat 11);
                     cons (chr #"C") (nat 12); cons (chr #"D") (nat 13);
                     cons (chr #"E") (nat 14); cons (chr #"F") (nat 15);
                     cons (chr #"G") (nat 16); cons (chr #"H") (nat 17);
                     cons (chr #"I") (nat 18); cons (chr #"J") (nat 19);
                     cons (chr #"K") (nat 20); cons (chr #"L") (nat 21);
                     cons (chr #"M") (nat 22); cons (chr #"N") (nat 23);
                     cons (chr #"O") (nat 24); cons (chr #"P") (nat 25);
                     cons (chr #"Q") (nat 26); cons (chr #"R") (nat 27);
                     cons (chr #"S") (nat 28); cons (chr #"T") (nat 29);
                     cons (chr #"U") (nat 30); cons (chr #"V") (nat 31);
                     cons (chr #"W") (nat 32); cons (chr #"X") (nat 33);
                     cons (chr #"Y") (nat 34); cons (chr #"Z") (nat 35)])
         in
           andl [l; less (cdr l) radix; cdr l]),
*)

val our_digit_char_p_def =
 acl2Define "ACL2::OUR-DIGIT-CHAR-P"
  `our_digit_char_p ch radix =
    (let l = assoc ch
              (List
                [cons (chr #"0") (nat 0); cons (chr #"1") (nat 1);
                 cons (chr #"2") (nat 2); cons (chr #"3") (nat 3);
                 cons (chr #"4") (nat 4); cons (chr #"5") (nat 5);
                 cons (chr #"6") (nat 6); cons (chr #"7") (nat 7);
                 cons (chr #"8") (nat 8); cons (chr #"9") (nat 9);
                 cons (chr #"a") (nat 10); cons (chr #"b") (nat 11);
                 cons (chr #"c") (nat 12); cons (chr #"d") (nat 13);
                 cons (chr #"e") (nat 14); cons (chr #"f") (nat 15);
                 cons (chr #"g") (nat 16); cons (chr #"h") (nat 17);
                 cons (chr #"i") (nat 18); cons (chr #"j") (nat 19);
                 cons (chr #"k") (nat 20); cons (chr #"l") (nat 21);
                 cons (chr #"m") (nat 22); cons (chr #"n") (nat 23);
                 cons (chr #"o") (nat 24); cons (chr #"p") (nat 25);
                 cons (chr #"q") (nat 26); cons (chr #"r") (nat 27);
                 cons (chr #"s") (nat 28); cons (chr #"t") (nat 29);
                 cons (chr #"u") (nat 30); cons (chr #"v") (nat 31);
                 cons (chr #"w") (nat 32); cons (chr #"x") (nat 33);
                 cons (chr #"y") (nat 34); cons (chr #"z") (nat 35);
                 cons (chr #"A") (nat 10); cons (chr #"B") (nat 11);
                 cons (chr #"C") (nat 12); cons (chr #"D") (nat 13);
                 cons (chr #"E") (nat 14); cons (chr #"F") (nat 15);
                 cons (chr #"G") (nat 16); cons (chr #"H") (nat 17);
                 cons (chr #"I") (nat 18); cons (chr #"J") (nat 19);
                 cons (chr #"K") (nat 20); cons (chr #"L") (nat 21);
                 cons (chr #"M") (nat 22); cons (chr #"N") (nat 23);
                 cons (chr #"O") (nat 24); cons (chr #"P") (nat 25);
                 cons (chr #"Q") (nat 26); cons (chr #"R") (nat 27);
                 cons (chr #"S") (nat 28); cons (chr #"T") (nat 29);
                 cons (chr #"U") (nat 30); cons (chr #"V") (nat 31);
                 cons (chr #"W") (nat 32); cons (chr #"X") (nat 33);
                 cons (chr #"Y") (nat 34); cons (chr #"Z") (nat 35)])
     in
       andl [l; less (cdr l) radix; cdr l])`;

(*
     [oracles: DEFUN COMMON-LISP::CHAR-EQUAL] [axioms: ] []
     |- char_equal x y = eql (char_downcase x) (char_downcase y),
*)

val char_equal_def =
 acl2Define "COMMON-LISP::CHAR-EQUAL"
   `char_equal x y = eql (char_downcase x) (char_downcase y)`;

(*
     [oracles: DEFUN ACL2::ATOM-LISTP, DISK_THM] [axioms: ] []
     |- atom_listp lst =
        ite (atom lst) (eq lst nil)
          (andl [atom (car lst); atom_listp (cdr lst)]),
*)

val (atom_listp_def,atom_listp_ind) =
 acl2_defn "ACL2::ATOM-LISTP"
  (`atom_listp lst =
     ite (atom lst) (eq lst nil)
         (andl [atom (car lst); atom_listp (cdr lst)])`,
   WF_REL_TAC `measure sexp_size`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN ACL2::IFIX, DISK_THM] [axioms: ] []
     |- ifix x = ite (integerp x) x (nat 0),
*)

val ifix_def =
 acl2Define "ACL2::IFIX"
  `ifix x = ite (integerp x) x (nat 0)`;

(*
     [oracles: DEFUN ACL2::RFIX, DISK_THM] [axioms: ] []
     |- rfix x = ite (rationalp x) x (nat 0),
*)

val rfix_def =
 acl2Define "ACL2::RFIX"
  `rfix x = ite (rationalp x) x (nat 0)`;

(*
     [oracles: DEFUN ACL2::REALFIX, DISK_THM] [axioms: ] []
     |- realfix x = ite (rationalp x) x (nat 0),
*)

val realfix_def =
 acl2Define "ACL2::REALFIX"
  `realfix x = ite (rationalp x) x (nat 0)`;

(*
     [oracles: DEFUN ACL2::NFIX, DISK_THM] [axioms: ] []
     |- nfix x = ite (andl [integerp x; not (less x (nat 0))]) x (nat 0),
*)

val nfix_def =
 acl2Define "ACL2::NFIX"
  `nfix x = ite (andl [integerp x; not (less x (nat 0))]) x (nat 0)`;

(*
     [oracles: DEFUN ACL2::STRING-EQUAL1, DISK_THM] [axioms: ] []
     |- string_equal1 str1 str2 i maximum =
        (let i = nfix i in
           ite (not (less i (ifix maximum))) t
             (andl
                [char_equal (char str1 i) (char str2 i);
                 string_equal1 str1 str2 (add (nat 1) i) maximum])),
*)

(*

val sexp_to_num_def =
 Define
  `sexp_to_num s = @n. s = nat n`;

Hol_defn "FOO"
 `string_equal1 str1 str2 i maximum =
        (let i = nfix i in
           ite (not (less i (ifix maximum))) t
             (andl
                [char_equal (char str1 i) (char str2 i);
                 string_equal1 str1 str2 (add (nat 1) i) maximum]))`;

Defn.tgoal it;

e(WF_REL_TAC
   `measure(\(str1,str2,i,maximum). (sexp_to_num maximum - sexp_to_num i))`);

e(RW_TAC std_ss
   [DECIDE ``0 < ((m:num) - n) = n < m``]);

DECIDE ``p <= m ==> ((m:num) < n + (m - p) = p < n)``;

val less_nat_ref =
 store_thm
  ("less_nat_ref",
   ``!n. less (nat n) (nat n) = nil``,
   ACL2_SIMP_TAC
    [nat_def,int_def,cpx_def,
     ratTheory.RAT_LES_REF]);

val less_int_ref =
 store_thm
  ("less_int_ref",
   ``!n. less (int n) (int n) = nil``,
   ACL2_SIMP_TAC
    [nat_def,int_def,cpx_def,
     ratTheory.RAT_LES_REF]);

val sexp_to_num_less =
 store_thm
  ("sexp_to_num_less",
   ``!m n.
      (not (less (nfix m) (ifix n)) = nil)
      ==>
      sexp_to_num m < sexp_to_num n``
   Cases THEN Cases
    THEN ACL2_SIMP_TAC[nat_def,REWRITE_RULE[nil_def]less_int_ref]

*)

(*
     [oracles: DEFUN COMMON-LISP::STRING-EQUAL, DISK_THM] [axioms: ] []
     |- string_equal str1 str2 =
        (let len1 = length str1 in
           andl
             [common_lisp_equal len1 (length str2);
              string_equal1 str1 str2 (nat 0) len1]),
*)

(*
     [oracles: DEFUN ACL2::STANDARD-STRING-ALISTP, DISK_THM] [axioms: ] []
     |- standard_string_alistp x =
        ite (atom x) (eq x nil)
          (andl
             [consp (car x); stringp (caar x);
              standard_char_listp (coerce (caar x) (csym "LIST"));
              standard_string_alistp (cdr x)]),
*)

(*
     [oracles: DEFUN ACL2::ASSOC-STRING-EQUAL, DISK_THM] [axioms: ] []
     |- assoc_string_equal acl2_str alist =
        itel
          [(endp alist,nil); (string_equal acl2_str (caar alist),car alist)]
          (assoc_string_equal acl2_str (cdr alist)),
*)

(*
     [oracles: DEFUN ACL2::NATP, DISK_THM] [axioms: ] []
     |- natp x = andl [integerp x; not (less x (nat 0))],
*)

val natp_def =
 acl2Define "ACL2::NATP"
  `natp x = andl [integerp x; not (less x (nat 0))]`;

(*
     [oracles: DEFUN ACL2::POSP, DISK_THM] [axioms: ] []
     |- posp x = andl [integerp x; less (nat 0) x],
*)

val posp_def =
 acl2Define "ACL2::POSP"
  `posp x = andl [integerp x; less (nat 0) x]`;

(*
     [oracles: DEFUN ACL2::O-FINP] [axioms: ] [] |- o_finp x = atom x,
*)

val o_finp_def =
 acl2Define "ACL2::O-FINP"
  `o_finp x = atom x`;

(*
     [oracles: DEFUN ACL2::O-FIRST-EXPT, DISK_THM] [axioms: ] []
     |- o_first_expt x = ite (o_finp x) (nat 0) (caar x),
*)

val o_first_expt_def =
 acl2Define "ACL2::O-FIRST-EXPT"
  `o_first_expt x = ite (o_finp x) (nat 0) (caar x)`;


(*****************************************************************************)
(* Tell system that o_first_expt decreases size                              *)
(*****************************************************************************)
val sexp_size_o_first_expt =
 store_thm
  ("sexp_size_o_first_expt",
   ``!x. ~(consp x = nil) /\ ~(consp(car x) = nil)
         ==>
         (sexp_size (o_first_expt x) < sexp_size x)``,
   Cases
    THEN ACL2_SIMP_TAC[sexp_size_def]
    THEN FULL_SIMP_TAC arith_ss [GSYM nil_def]
    THEN METIS_TAC[sexp_size_car,DECIDE``m:num < n ==> !p. m < n+p``]);

val _ = add_acl2_simps [sexp_size_o_first_expt];

(*
     [oracles: DEFUN ACL2::O-FIRST-COEFF, DISK_THM] [axioms: ] []
     |- o_first_coeff x = ite (o_finp x) x (cdar x),
*)

val o_first_coeff_def =
 acl2Define "ACL2::O-FIRST-COEFF"
  `o_first_coeff x = ite (o_finp x) x (cdar x)`;

(*****************************************************************************)
(* Tell system that o_first_coeff decreases size                             *)
(*****************************************************************************)
val sexp_size_o_first_coeff =
 store_thm
  ("sexp_size_o_first_coeff",
   ``!x. ~(consp x = nil) /\ ~(consp(car x) = nil)
         ==>
         (sexp_size (o_first_coeff x) < sexp_size x)``,
   Cases
    THEN ACL2_SIMP_TAC[sexp_size_def]
    THEN FULL_SIMP_TAC arith_ss [GSYM nil_def]
    THEN METIS_TAC[sexp_size_cdr,DECIDE``m:num < n ==> !p. m < n+p``]);

val _ = add_acl2_simps [sexp_size_o_first_coeff];

(*
     [oracles: DEFUN ACL2::O-RST] [axioms: ] [] |- o_rst x = cdr x,
*)

val o_rst_def =
 acl2Define "ACL2::O-RST"
  `o_rst x = cdr x`;

(*****************************************************************************)
(* Tell system that o_rest decreases size                                    *)
(*****************************************************************************)
val sexp_size_o_rst =
 store_thm
  ("sexp_size_o_rst",
   ``!x. ~(consp x = nil) ==> (sexp_size (o_rst x) < sexp_size x)``,
   ACL2_SIMP_TAC[]);

val _ = add_acl2_simps [sexp_size_o_rst];

(*
     [oracles: DEFUN ACL2::O<G, DISK_THM] [axioms: ] []
     |- o_less_g x =
        ite (atom x) (rationalp x)
          (andl
             [consp (car x); rationalp (o_first_coeff x);
              o_less_g (o_first_expt x); o_less_g (o_rst x)]),
*)

(*
     [oracles: DEFUN ACL2::O<, DISK_THM] [axioms: ] []
     |- o_less x y =
        itel
          [(o_finp x,ite (not (o_finp y)) (not (o_finp y)) (less x y));
           (o_finp y,nil);
           (not (equal (o_first_expt x) (o_first_expt y)),
            o_less (o_first_expt x) (o_first_expt y));
           (not (common_lisp_equal (o_first_coeff x) (o_first_coeff y)),
            less (o_first_coeff x) (o_first_coeff y))]
          (o_less (o_rst x) (o_rst y)),
*)

(*
     [oracles: DEFUN ACL2::O-P, DISK_THM] [axioms: ] []
     |- o_p x =
        ite (o_finp x) (natp x)
          (andl
             [consp (car x); o_p (o_first_expt x);
              not (eql (nat 0) (o_first_expt x)); posp (o_first_coeff x);
              o_p (o_rst x);
              o_less (o_first_expt (o_rst x)) (o_first_expt x)]),
*)

(*
Need help from a TFL expert for this. I suspect need to add
something with more oomph than andl_CONG for Defn Base to exploit
sexp_size_o_first_expt and sexp_size_o_rst

acl2_tgoal  "ACL2::O-P"
   `o_p x =
     ite (o_finp x) (natp x)
         (andl
            [consp (car x); o_p (o_first_expt x);
             not (eql (nat 0) (o_first_expt x)); posp (o_first_coeff x);
             o_p (o_rst x);
             o_less (o_first_expt (o_rst x)) (o_first_expt x)])`;

> val it =
    Initial goal:

    ?R.
      WF R /\ (!x. (o_finp x = nil) ==> R (o_first_expt x) x) /\
      !x. (o_finp x = nil) ==> R (o_rst x) x

     : goalstack

- e(WF_REL_TAC `measure sexp_size`);
OK..
1 subgoal:
> val it =
    (!x. (o_finp x = nil) ==> sexp_size (o_first_expt x) < sexp_size x) /\
    !x. (o_finp x = nil) ==> sexp_size (o_rst x) < sexp_size x

     : goalstack

- sexp_size_o_first_expt;
> val it =
    |- !x.
         ~(consp x = nil) /\ ~(consp (car x) = nil) ==>
         sexp_size (o_first_expt x) < sexp_size x : thm

- sexp_size_o_rst;
> val it = |- !x. ~(consp x = nil) ==> sexp_size (o_rst x) < sexp_size x : thm

e(WF_REL_TAC `measure sexp_size`);

val (o_p_def,o_p_ind) =
 acl2_defn "ACL2::O-P"
  (`o_p x =
     ite (o_finp x) (natp x)
         (andl
            [consp (car x); o_p (o_first_expt x);
             not (eql (nat 0) (o_first_expt x)); posp (o_first_coeff x);
             o_p (o_rst x);
             o_less (o_first_expt (o_rst x)) (o_first_expt x)])`,
   WF_REL_TAC `measure sexp_size`
    THEN ACL2_SIMP_TAC [o_finp_def]
    THEN FULL_SIMP_TAC std_ss [GSYM nil_def]
*)

(*
     [oracles: DEFUN ACL2::MAKE-ORD] [axioms: ] []
     |- make_ord fe fco rst = cons (cons fe fco) rst,
*)

(*

     [oracles: DEFUN ACL2::LIST*-MACRO] [axioms: ] []
     |- list_star_macro lst =
        ite (endp (cdr lst)) (car lst)
          (cons (sym COMMON_LISP ACL2_STRING_ABBREV_714)
             (cons (car lst) (cons (list_star_macro (cdr lst)) nil)))
*)

(*
     [oracles: DEFUN ACL2::HARD-ERROR] [axioms: ] []
     |- hard_error ctx acl2_str alist = nil,
*)

(*
     [oracles: DEFUN ACL2::ILLEGAL] [axioms: ] []
     |- illegal ctx acl2_str alist = hard_error ctx acl2_str alist,
*)

(*
     [oracles: DEFUN COMMON-LISP::KEYWORDP, DISK_THM] [axioms: ] []
     |- keywordp x =
        andl [symbolp x; equal (symbol_package_name x) (str KEYWORD)],
*)

(*
     [oracles: DEFUN ACL2::MEMBER-SYMBOL-NAME, DISK_THM] [axioms: ] []
     |- member_symbol_name acl2_str l =
        itel [(endp l,nil); (equal acl2_str (symbol_name (car l)),l)]
          (member_symbol_name acl2_str (cdr l)),
*)

val (member_symbol_name_def,member_symbol_name_ind) =
 acl2_defn "ACL2::MEMBER-SYMBOL-NAME"
  (`member_symbol_name acl2_str l =
     itel [(endp l,nil); (equal acl2_str (symbol_name (car l)),l)]
          (member_symbol_name acl2_str (cdr l))`,
   WF_REL_TAC `measure (sexp_size o SND)`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN ACL2::BINARY-APPEND, DISK_THM] [axioms: ] []
     |- binary_append x y =
        ite (endp x) y (cons (car x) (binary_append (cdr x) y)),
*)

val (binary_append_def,binary_append_ind) =
 acl2_defn "ACL2::BINARY-APPEND"
  (`binary_append x y =
     ite (endp x) y (cons (car x) (binary_append (cdr x) y))`,
   WF_REL_TAC `measure (sexp_size o FST)`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN ACL2::STRING-APPEND, DISK_THM] [axioms: ] []
     |- string_append str1 str2 =
        coerce
          (binary_append (coerce str1 (csym "LIST"))
             (coerce str2 (csym "LIST"))) (csym "STRING"),
*)

(*
     [oracles: DEFUN ACL2::STRING-LISTP, DISK_THM] [axioms: ] []
     |- string_listp x =
        ite (atom x) (eq x nil)
          (andl [stringp (car x); string_listp (cdr x)]),
*)

(*
     [oracles: DEFUN ACL2::STRING-APPEND-LST, DISK_THM] [axioms: ] []
     |- string_append_lst x =
        ite (endp x) (str "")
          (string_append (car x) (string_append_lst (cdr x))),
*)

(*
     [oracles: DEFUN COMMON-LISP::REMOVE, DISK_THM] [axioms: ] []
     |- remove x l =
        itel [(endp l,nil); (eql x (car l),remove x (cdr l))]
          (cons (car l) (remove x (cdr l))),
*)

(*
     [oracles: DEFUN ACL2::PAIRLIS$, DISK_THM] [axioms: ] []
     |- pairlis_dollar x y =
        ite (endp x) nil
          (cons (cons (car x) (car y)) (pairlis_dollar (cdr x) (cdr y))),
*)

(*
     [oracles: DEFUN ACL2::REMOVE-DUPLICATES-EQL, DISK_THM] [axioms: ] []
     |- remove_duplicates_eql l =
        itel
          [(endp l,nil);
           (member (car l) (cdr l),remove_duplicates_eql (cdr l))]
          (cons (car l) (remove_duplicates_eql (cdr l))),
*)

(*
     [oracles: DEFUN COMMON-LISP::REMOVE-DUPLICATES, DISK_THM] [axioms: ] []
     |- remove_duplicates l =
        ite (stringp l)
          (coerce (remove_duplicates_eql (coerce l (csym "LIST")))
             (csym "STRING")) (remove_duplicates_eql l),
*)

(*
     [oracles: DEFUN ACL2::REMOVE-DUPLICATES-EQUAL, DISK_THM] [axioms: ] []
     |- remove_duplicates_equal l =
        itel
          [(endp l,nil);
           (member_equal (car l) (cdr l),remove_duplicates_equal (cdr l))]
          (cons (car l) (remove_duplicates_equal (cdr l))),
*)

(*
     [oracles: DEFUN COMMON-LISP::IDENTITY] [axioms: ] [] |- identity x = x,
*)

(*
     [oracles: DEFUN COMMON-LISP::REVAPPEND, DISK_THM] [axioms: ] []
     |- revappend x y = ite (endp x) y (revappend (cdr x) (cons (car x) y)),
*)

(*
     [oracles: DEFUN COMMON-LISP::REVERSE, DISK_THM] [axioms: ] []
     |- reverse x =
        ite (stringp x)
          (coerce (revappend (coerce x (csym "LIST")) nil) (csym "STRING"))
          (revappend x nil),
*)

(*
     [oracles: DEFUN ACL2::SET-DIFFERENCE-EQ, DISK_THM] [axioms: ] []
     |- set_difference_eq l1 l2 =
        itel
          [(endp l1,nil);
           (member_eq (car l1) l2,set_difference_eq (cdr l1) l2)]
          (cons (car l1) (set_difference_eq (cdr l1) l2)),
*)

(*
     [oracles: DEFUN ACL2::STRIP-CDRS, DISK_THM] [axioms: ] []
     |- strip_cdrs x = ite (endp x) nil (cons (cdar x) (strip_cdrs (cdr x))),
*)

(*
     [oracles: DEFUN ACL2::MUTUAL-RECURSION-GUARDP, DISK_THM] [axioms: ] []
     |- mutual_recursion_guardp rst =
        ite (atom rst) (equal rst nil)
          (andl
             [consp (car rst); true_listp (car rst);
              member_eq (caar rst) (List [csym "DEFUN"; asym "DEFUND"]);
              mutual_recursion_guardp (cdr rst)]),
*)

(*
     [oracles: DEFUN ACL2::COLLECT-CADRS-WHEN-CAR-EQ, DISK_THM] [axioms: ] []
     |- collect_cadrs_when_car_eq x alist =
        itel
          [(endp alist,nil);
           (eq x (caar alist),
            cons (cadar alist) (collect_cadrs_when_car_eq x (cdr alist)))]
          (collect_cadrs_when_car_eq x (cdr alist)),
*)

(*
     [oracles: DEFUN ACL2::XD-NAME, DISK_THM] [axioms: ] []
     |- xd_name event_type name =
        itel
          [(eq event_type (asym "DEFUND"),List [ksym "DEFUND"; name]);
           (eq event_type (asym "DEFTHMD"),List [ksym "DEFTHMD"; name])]
          (illegal (asym "XD-NAME")
             (str "Unexpected event-type for xd-name, %x0")
             (List [cons (chr #"0") event_type])),
*)

(*
     [oracles: DEFUN ACL2::DEFUND-NAME-LIST, DISK_THM] [axioms: ] []
     |- defund_name_list defuns acc =
        ite (endp defuns) (reverse acc)
          (defund_name_list (cdr defuns)
             (cons
                (ite (eq (caar defuns) (asym "DEFUND"))
                   (xd_name (asym "DEFUND") (cadar defuns)) (cadar defuns))
                acc)),
*)

(*
     [oracles: DEFUN ACL2::PSEUDO-TERM-LISTP, DISK_THM] [axioms: ] []
     |- pseudo_term_listp lst =
        ite (atom lst) (equal lst nil)
          (andl [pseudo_termp (car lst); pseudo_term_listp (cdr lst)]),
*)

(*
     [oracles: DEFUN ACL2::PSEUDO-TERMP, DISK_THM] [axioms: ] []
     |- pseudo_termp x =
        itel
          [(atom x,symbolp x);
           (eq (car x) (csym "QUOTE"),andl [consp (cdr x); null (cddr x)]);
           (not (true_listp x),nil); (not (pseudo_term_listp (cdr x)),nil);
           (symbolp (car x),symbolp (car x))]
          (andl
             [true_listp (car x); equal (length (car x)) (nat 3);
              eq (caar x) (csym "LAMBDA"); symbol_listp (cadar x);
              pseudo_termp (caddar x);
              equal (length (cadar x)) (length (cdr x))]),
*)

(*
     [oracles: DEFUN ACL2::PSEUDO-TERM-LIST-LISTP, DISK_THM] [axioms: ] []
     |- pseudo_term_list_listp l =
        ite (atom l) (equal l nil)
          (andl [pseudo_term_listp (car l); pseudo_term_list_listp (cdr l)]),
*)

(*
     [oracles: DEFUN ACL2::ADD-TO-SET-EQ, DISK_THM] [axioms: ] []
     |- add_to_set_eq x lst = ite (member_eq x lst) lst (cons x lst),
*)

(*
     [oracles: DEFUN ACL2::ADD-TO-SET-EQL, DISK_THM] [axioms: ] []
     |- add_to_set_eql x lst = ite (member x lst) lst (cons x lst),
*)

(*
     [oracles: DEFUN ACL2::QUOTEP, DISK_THM] [axioms: ] []
     |- quotep x = andl [consp x; eq (car x) (csym "QUOTE")],
*)

(*
     [oracles: DEFUN ACL2::KWOTE, DISK_THM] [axioms: ] []
     |- kwote x = List [csym "QUOTE"; x],
*)

(*
     [oracles: DEFUN ACL2::FN-SYMB, DISK_THM] [axioms: ] []
     |- fn_symb x = andl [consp x; not (eq (csym "QUOTE") (car x)); car x],
*)

(*
     [oracles: DEFUN ACL2::ALL-VARS1-LST, DISK_THM] [axioms: ] []
     |- all_vars1_lst lst ans =
        ite (endp lst) ans
          (all_vars1_lst (cdr lst) (all_vars1 (car lst) ans)),
*)

(*
     [oracles: DEFUN ACL2::ALL-VARS1, DISK_THM] [axioms: ] []
     |- all_vars1 term ans =
        itel
          [(atom term,add_to_set_eq term ans);
           (eq (csym "QUOTE") (car term),ans)] (all_vars1_lst (cdr term) ans),
*)

(*
     [oracles: DEFUN ACL2::ALL-VARS] [axioms: ] []
     |- all_vars term = all_vars1 term nil,
*)

(*
     [oracles: DEFUN ACL2::INTERSECTP-EQ, DISK_THM] [axioms: ] []
     |- intersectp_eq x y =
        itel [(endp x,nil); (member_eq (car x) y,t)]
          (intersectp_eq (cdr x) y),
*)

(*
     [oracles: DEFUN ACL2::INTERSECTP-EQUAL, DISK_THM] [axioms: ] []
     |- intersectp_equal x y =
        itel [(endp x,nil); (member_equal (car x) y,t)]
          (intersectp_equal (cdr x) y),
*)

(*
     [oracles: DEFUN ACL2::MAKE-FMT-BINDINGS, DISK_THM] [axioms: ] []
     |- make_fmt_bindings chars forms =
        ite (endp forms) nil
          (List
             [csym "CONS"; List [csym "CONS"; car chars; car forms];
              make_fmt_bindings (cdr chars) (cdr forms)]),
*)

(*
     [oracles: DEFUN ACL2::ER-PROGN-FN, DISK_THM] [axioms: ] []
     |- er_progn_fn lst =
        itel [(endp lst,nil); (endp (cdr lst),car lst)]
          (List
             [asym "MV-LET";
              List
                [asym "ER-PROGN-NOT-TO-BE-USED-ELSEWHERE-ERP";
                 asym "ER-PROGN-NOT-TO-BE-USED-ELSEWHERE-VAL"; asym "STATE"];
              car lst;
              List
                [csym "IF"; asym "ER-PROGN-NOT-TO-BE-USED-ELSEWHERE-ERP";
                 List
                   [asym "MV"; asym "ER-PROGN-NOT-TO-BE-USED-ELSEWHERE-ERP";
                    asym "ER-PROGN-NOT-TO-BE-USED-ELSEWHERE-VAL";
                    asym "STATE"];
                 List
                   [asym "CHECK-VARS-NOT-FREE";
                    List
                      [asym "ER-PROGN-NOT-TO-BE-USED-ELSEWHERE-ERP";
                       asym "ER-PROGN-NOT-TO-BE-USED-ELSEWHERE-VAL"];
                    er_progn_fn (cdr lst)]]]),
*)

(*
     [oracles: DEFUN ACL2::LEGAL-CASE-CLAUSESP, DISK_THM] [axioms: ] []
     |- legal_case_clausesp tl =
        ite (atom tl) (eq tl nil)
          (andl
             [consp (car tl);
              ite (eqlablep (caar tl)) (eqlablep (caar tl))
                (eqlable_listp (caar tl)); consp (cdar tl); null (cddar tl);
              ite
                (ite (eq t (caar tl)) (eq t (caar tl))
                   (eq (csym "OTHERWISE") (caar tl))) (null (cdr tl)) t;
              legal_case_clausesp (cdr tl)]),
*)

(*
     [oracles: DEFUN ACL2::CASE-TEST, DISK_THM] [axioms: ] []
     |- case_test x pat =
        ite (atom pat) (List [csym "EQL"; x; List [csym "QUOTE"; pat]])
          (List [csym "MEMBER"; x; List [csym "QUOTE"; pat]]),
*)

(*
     [oracles: DEFUN ACL2::CASE-LIST, DISK_THM] [axioms: ] []
     |- case_list x l =
        itel
          [(endp l,nil);
           (ite (eq t (caar l)) (eq t (caar l))
              (eq (csym "OTHERWISE") (caar l)),List [List [t; cadar l]]);
           (null (caar l),case_list x (cdr l))]
          (cons (List [case_test x (caar l); cadar l]) (case_list x (cdr l))),
*)

(*
     [oracles: DEFUN ACL2::CASE-LIST-CHECK, DISK_THM] [axioms: ] []
     |- case_list_check l =
        itel
          [(endp l,nil);
           (ite (eq t (caar l)) (eq t (caar l))
              (eq (csym "OTHERWISE") (caar l)),
            List
              [List
                 [t;
                  List
                    [asym "CHECK-VARS-NOT-FREE";
                     List [asym "CASE-DO-NOT-USE-ELSEWHERE"]; cadar l]]]);
           (null (caar l),case_list_check (cdr l))]
          (cons
             (List
                [case_test (asym "CASE-DO-NOT-USE-ELSEWHERE") (caar l);
                 List
                   [asym "CHECK-VARS-NOT-FREE";
                    List [asym "CASE-DO-NOT-USE-ELSEWHERE"]; cadar l]])
             (case_list_check (cdr l))),
*)

(*
     [oracles: DEFUN ACL2::POSITION-EQUAL-AC, DISK_THM] [axioms: ] []
     |- position_equal_ac item lst acc =
        itel [(endp lst,nil); (equal item (car lst),acc)]
          (position_equal_ac item (cdr lst) (add (nat 1) acc)),
*)

(*
     [oracles: DEFUN ACL2::POSITION-AC, DISK_THM] [axioms: ] []
     |- position_ac item lst acc =
        itel [(endp lst,nil); (eql item (car lst),acc)]
          (position_ac item (cdr lst) (add (nat 1) acc)),
*)

(*
     [oracles: DEFUN ACL2::POSITION-EQUAL, DISK_THM] [axioms: ] []
     |- position_equal item lst =
        ite (stringp lst)
          (position_ac item (coerce lst (csym "LIST")) (nat 0))
          (position_equal_ac item lst (nat 0)),
*)

(*
     [oracles: DEFUN ACL2::POSITION-EQ-AC, DISK_THM] [axioms: ] []
     |- position_eq_ac item lst acc =
        itel [(endp lst,nil); (eq item (car lst),acc)]
          (position_eq_ac item (cdr lst) (add (nat 1) acc)),
*)

(*
     [oracles: DEFUN ACL2::POSITION-EQ, DISK_THM] [axioms: ] []
     |- position_eq item lst = position_eq_ac item lst (nat 0),
*)

(*
     [oracles: DEFUN COMMON-LISP::POSITION, DISK_THM] [axioms: ] []
     |- position item lst =
        ite (stringp lst)
          (position_ac item (coerce lst (csym "LIST")) (nat 0))
          (position_ac item lst (nat 0)),
*)

(*
     [oracles: DEFUN ACL2::NONNEGATIVE-INTEGER-QUOTIENT, DISK_THM] [axioms: ]
     []
     |- nonnegative_integer_quotient i j =
        ite
          (ite (common_lisp_equal (nfix j) (nat 0))
             (common_lisp_equal (nfix j) (nat 0)) (less (ifix i) j)) (nat 0)
          (add (nat 1)
             (nonnegative_integer_quotient (add i (unary_minus j)) j)),
*)

val nonnegative_integer_quotient_def =
 acl2AxiomDefine "ACL2::NONNEGATIVE-INTEGER-QUOTIENT"
  `nonnegative_integer_quotient i j =
    ite
      (ite (common_lisp_equal (nfix j) (nat 0))
         (common_lisp_equal (nfix j) (nat 0)) (less (ifix i) j)) (nat 0)
      (add (nat 1)
         (nonnegative_integer_quotient (add i (unary_minus j)) j))`;


(*
     [oracles: DEFUN ACL2::LEGAL-LET*-P] [axioms: ] []
     |- legal_let_star_p bindings ignore_vars ignored_seen top_form =
        ite (endp bindings)
          (ite (eq ignore_vars nil) (eq ignore_vars nil)
             (hard_error (sym COMMON_LISP ACL2_STRING_ABBREV_453)
                (str
                   "All variables declared IGNOREd in a LET* form must ~\n                          be bound, but ~&0 ~#0~[is~/are~] not bound in the ~\n                          form ~x1.")
                (cons (cons (chr #"0") ignore_vars)
                   (cons (cons (chr #"1") top_form) nil))))
          (ite (member_eq (car (car bindings)) ignored_seen)
             (hard_error (sym COMMON_LISP ACL2_STRING_ABBREV_453)
                (str
                   "A variable bound twice in a LET* form may not be ~\n                      declared ignored.  However, the variable ~x0 is bound in ~\n                      the form ~x1 and yet is declared ignored.")
                (cons (cons (chr #"0") (car (car bindings)))
                   (cons (cons (chr #"1") top_form) nil)))
             (ite (member_eq (car (car bindings)) ignore_vars)
                (legal_let_star_p (cdr bindings)
                   (remove (car (car bindings)) ignore_vars)
                   (cons (car (car bindings)) ignored_seen) top_form)
                (legal_let_star_p (cdr bindings) ignore_vars ignored_seen
                   top_form)))
*)

(*
     [oracles: DEFUN ACL2::LET*-MACRO, DISK_THM] [axioms: ] []
     |- let_star_macro bindings ignore_vars body =
        ite (ite (endp bindings) (endp bindings) (endp (cdr bindings)))
          (cons (sym COMMON_LISP ACL2_STRING_ABBREV_455)
             (cons bindings
                (ite ignore_vars
                   (cons
                      (cons (sym COMMON_LISP ACL2_STRING_ABBREV_755)
                         (cons
                            (cons (sym COMMON_LISP ACL2_STRING_ABBREV_555)
                               ignore_vars) nil)) (cons body nil))
                   (cons body nil))))
          (cons (sym COMMON_LISP ACL2_STRING_ABBREV_455)
             (cons (cons (car bindings) nil)
                (let (rest,ignore_vars,bindings) =
                       (let_star_macro (cdr bindings)
                          (remove (car (car bindings)) ignore_vars) body,
                        ignore_vars,bindings)
                 in
                   ite (member_eq (car (car bindings)) ignore_vars)
                     (cons
                        (cons (sym COMMON_LISP ACL2_STRING_ABBREV_755)
                           (cons
                              (cons (sym COMMON_LISP ACL2_STRING_ABBREV_555)
                                 (cons (car (car bindings)) nil)) nil))
                        (cons rest nil)) (cons rest nil))))
*)

(*
     [oracles: DEFUN COMMON-LISP::FLOOR, DISK_THM] [axioms: ] []
     |- floor i j =
        (let q = mult i (reciprocal j) in
         let n = numerator q in
         let d = denominator q in
           itel
             [(common_lisp_equal d (nat 1),n);
              (not (less n (nat 0)),nonnegative_integer_quotient n d)]
             (add
                (unary_minus
                   (nonnegative_integer_quotient (unary_minus n) d))
                (int ~1))),
*)

val floor_def =
 acl2Define "COMMON-LISP::FLOOR"
  `floor i j =
    (let q = mult i (reciprocal j) in
     let n = numerator q in
     let d = denominator q in
       itel
         [(common_lisp_equal d (nat 1),n);
          (not (less n (nat 0)),nonnegative_integer_quotient n d)]
         (add
            (unary_minus
               (nonnegative_integer_quotient (unary_minus n) d))
            (int ~1)))`;


(*
     [oracles: DEFUN COMMON-LISP::CEILING, DISK_THM] [axioms: ] []
     |- ceiling i j =
        (let q = mult i (reciprocal j) in
         let n = numerator q in
         let d = denominator q in
           itel
             [(common_lisp_equal d (nat 1),n);
              (not (less n (nat 0)),
               add (nonnegative_integer_quotient n d) (nat 1))]
             (unary_minus (nonnegative_integer_quotient (unary_minus n) d))),
*)

(*
     [oracles: DEFUN COMMON-LISP::TRUNCATE, DISK_THM] [axioms: ] []
     |- truncate i j =
        (let q = mult i (reciprocal j) in
         let n = numerator q in
         let d = denominator q in
           itel
             [(common_lisp_equal d (nat 1),n);
              (not (less n (nat 0)),nonnegative_integer_quotient n d)]
             (unary_minus (nonnegative_integer_quotient (unary_minus n) d))),
*)

(*
     [oracles: DEFUN COMMON-LISP::ROUND, DISK_THM] [axioms: ] []
     |- round i j =
        (let q = mult i (reciprocal j) in
           itel
             [(integerp q,q);
              (not (less q (nat 0)),
               (let fl = floor q (nat 1) in
                let remainder = add q (unary_minus fl) in
                  itel
                    [(less (cpx 1 2 0 1) remainder,add fl (nat 1));
                     (less remainder (cpx 1 2 0 1),fl);
                     (integerp (mult fl (reciprocal (nat 2))),fl)]
                    (add fl (nat 1))))]
             (let cl = ceiling q (nat 1) in
              let remainder = add q (unary_minus cl) in
                itel
                  [(less (cpx (~1) 2 0 1) remainder,cl);
                   (less remainder (cpx (~1) 2 0 1),add cl (int ~1));
                   (integerp (mult cl (reciprocal (nat 2))),cl)]
                  (add cl (int ~1)))),
*)

(*
     [oracles: DEFUN COMMON-LISP::MOD] [axioms: ] []
     |- mod x y = add x (unary_minus (mult (floor x y) y)),

Needs FLOOR

val mod_def =
 acl2Define "COMMON-LISP::MOD"
  `mod x y = add x (unary_minus (mult (floor x y) y))`;
*)

val mod_def =
 acl2Define "COMMON-LISP::MOD"
  `mod x y = add x (unary_minus (mult (floor x y) y))`;

(*
     [oracles: DEFUN COMMON-LISP::REM] [axioms: ] []
     |- x rem y = add x (unary_minus (mult (truncate x y) y)),
*)

(*
     [oracles: DEFUN COMMON-LISP::EVENP, DISK_THM] [axioms: ] []
     |- evenp x = integerp (mult x (reciprocal (nat 2))),
*)

(*
     [oracles: DEFUN COMMON-LISP::ODDP] [axioms: ] []
     |- oddp x = not (evenp x),
*)

(*
     [oracles: DEFUN COMMON-LISP::ZEROP, DISK_THM] [axioms: ] []
     |- zerop x = eql x (nat 0),
*)

(*
     [oracles: DEFUN COMMON-LISP::PLUSP, DISK_THM] [axioms: ] []
     |- plusp x = less (nat 0) x,
*)

(*
     [oracles: DEFUN COMMON-LISP::MINUSP, DISK_THM] [axioms: ] []
     |- minusp x = less x (nat 0),
*)

(*
     [oracles: DEFUN COMMON-LISP::MIN, DISK_THM] [axioms: ] []
     |- min x y = ite (less x y) x y,
*)

(*
     [oracles: DEFUN COMMON-LISP::MAX, DISK_THM] [axioms: ] []
     |- max x y = ite (less y x) x y,
*)

(*
     [oracles: DEFUN COMMON-LISP::ABS, DISK_THM] [axioms: ] []
     |- abs x = ite (minusp x) (unary_minus x) x,
*)

(*
     [oracles: DEFUN COMMON-LISP::SIGNUM, DISK_THM] [axioms: ] []
     |- signum x = itel [(zerop x,nat 0); (minusp x,int ~1)] (nat 1),
*)

(*
     [oracles: DEFUN COMMON-LISP::LOGNOT, DISK_THM] [axioms: ] []
     |- lognot i = add (unary_minus (ifix i)) (int ~1),
*)

(*
     [oracles: DEFUN COMMON-LISP::EXPT, DISK_THM] [axioms: ] []
     |- expt r i =
        itel
          [(zip i,nat 1); (common_lisp_equal (fix r) (nat 0),nat 0);
           (less (nat 0) i,mult r (expt r (add i (int ~1))))]
          (mult (reciprocal r) (expt r (add i (nat 1)))),

> Matt says: The measure for (expt r i) is (abs (ifix i)).  Intuitively, we count
> down for positive exponents and count up for negative exponents

val (expt_def,expt_ind) =
 acl2_defn "COMMON-LISP::EXPT"
  (`expt r i =
     itel
       [(zip i,nat 1); (common_lisp_equal (fix r) (nat 0),nat 0);
        (less (nat 0) i,mult r (expt r (add i (int ~1))))]
       (mult (reciprocal r) (expt r (add i (nat 1))))`,
   WF_REL_TAC `measure (sexp_size o FST)`
    THEN ACL2_SIMP_TAC []);
*)

val expt_def =
 acl2AxiomDefine "COMMON-LISP::EXPT"
  `expt r i =
    itel
      [(zip i,nat 1); (common_lisp_equal (fix r) (nat 0),nat 0);
       (less (nat 0) i,mult r (expt r (add i (int ~1))))]
      (mult (reciprocal r) (expt r (add i (nat 1))))`;

(*
     [oracles: DEFUN COMMON-LISP::LOGCOUNT, DISK_THM] [axioms: ] []
     |- logcount x =
        itel
          [(zip x,nat 0); (less x (nat 0),logcount (lognot x));
           (evenp x,logcount (nonnegative_integer_quotient x (nat 2)))]
          (add (nat 1) (logcount (nonnegative_integer_quotient x (nat 2)))),
*)

(*
     [oracles: DEFUN COMMON-LISP::LISTP, DISK_THM] [axioms: ] []
     |- listp x = ite (consp x) (consp x) (equal x nil),
*)

(*
     [oracles: DEFUN COMMON-LISP::NTHCDR, DISK_THM] [axioms: ] []
     |- nthcdr n l = ite (zp n) l (nthcdr (add n (int ~1)) (cdr l)),
*)

(*
     [oracles: DEFUN COMMON-LISP::LAST, DISK_THM] [axioms: ] []
     |- last l = ite (atom (cdr l)) l (last (cdr l)),
*)

(*
     [oracles: DEFUN COMMON-LISP::LOGBITP, DISK_THM] [axioms: ] []
     |- logbitp i j = oddp (floor (ifix j) (expt (nat 2) (nfix i))),
*)

(*
     [oracles: DEFUN COMMON-LISP::ASH, DISK_THM] [axioms: ] []
     |- ash i c = floor (mult (ifix i) (expt (nat 2) c)) (nat 1),
*)

(*
     [oracles: DEFUN ACL2::THE-ERROR] [axioms: ] []
     |- the_error x y = cdr (cons x y),
*)

(*
     [oracles: DEFUN COMMON-LISP::CHAR<] [axioms: ] []
     |- char_less x y = less (char_code x) (char_code y),
*)

val char_less_def =
 acl2Define "COMMON-LISP::CHAR<"
  `char_less x y = less (char_code x) (char_code y)`;

(*
     [oracles: DEFUN COMMON-LISP::CHAR>] [axioms: ] []
     |- char_greater x y = less (char_code y) (char_code x),
*)

(*
     [oracles: DEFUN COMMON-LISP::CHAR<=] [axioms: ] []
     |- char_less_equal x y = not (less (char_code y) (char_code x)),
*)

(*
     [oracles: DEFUN COMMON-LISP::CHAR>=] [axioms: ] []
     |- char_greater_equal x y = not (less (char_code x) (char_code y)),
*)

(*
     [oracles: DEFUN ACL2::STRING<-L] [axioms: ] []
     |- string_less_l l1 l2 i =
        ite (endp l1) (ite (endp l2) nil i)
          (ite (endp l2) nil
             (ite (eql (car l1) (car l2))
                (string_less_l (cdr l1) (cdr l2) (add i (cpx 1 1 0 1)))
                (ite (char_less (car l1) (car l2)) i nil)))
*)

val (string_less_l_def,string_less_l_ind) =
 acl2_defn "ACL2::STRING<-L"
  (`string_less_l l1 l2 i =
     ite (endp l1)
         (ite (endp l2) nil i)
         (ite (endp l2)
              nil
              (ite (eql (car l1) (car l2))
                   (string_less_l (cdr l1) (cdr l2) (add i (cpx 1 1 0 1)))
                   (ite (char_less (car l1) (car l2)) i nil)))`,
    WF_REL_TAC `measure (sexp_size o FST o SND)`
    THEN ACL2_SIMP_TAC []);


(*
     DEFUN COMMON-LISP::STRING<
     [oracles: DEFUN COMMON-LISP::STRING<] [axioms: ] []
     |- string_less str1 str2 =
        string_less_l (coerce str1 (sym COMMON_LISP ACL2_STRING_ABBREV_521))
          (coerce str2 (sym COMMON_LISP ACL2_STRING_ABBREV_521))
          (cpx 0 1 0 1)
|- ACL2_STRING_ABBREV_521 = "LIST"
*)

val string_less_def =
 acl2Define "COMMON-LISP::STRING<"
  `string_less str1 str2 =
    string_less_l (coerce str1 (sym COMMON_LISP "LIST"))
                  (coerce str2 (sym COMMON_LISP "LIST"))
                  (cpx 0 1 0 1)`;


(*
     [oracles: DEFUN COMMON-LISP::STRING>] [axioms: ] []
     |- string_greater str1 str2 = string_less str2 str1,
*)

(*
     [oracles: DEFUN COMMON-LISP::STRING<=, DISK_THM] [axioms: ] []
     |- string_less_equal str1 str2 =
        ite (equal str1 str2) (length str1) (string_less str1 str2),
*)

val string_less_equal_def =
 acl2Define "COMMON-LISP::STRING<="
  `string_less_equal str1 str2 =
    ite (equal str1 str2) (length str1) (string_less str1 str2)`;

(*
     [oracles: DEFUN COMMON-LISP::STRING>=, DISK_THM] [axioms: ] []
     |- string_greater_equal str1 str2 =
        ite (equal str1 str2) (length str1) (string_greater str1 str2),
*)

(*
     [oracles: DEFUN ACL2::SYMBOL-<, DISK_THM] [axioms: ] []
     |- symbol_less x y =
        (let (x1,y1,y,x) = (symbol_name x,symbol_name y,y,x) in
           ite (string_less x1 y1) (string_less x1 y1)
             (ite (equal x1 y1)
                (string_less (symbol_package_name x) (symbol_package_name y))
                nil))
*)

val symbol_less_def =
 acl2Define "ACL2::SYMBOL::-<"
  `symbol_less x y =
    (let (x1,y1,y,x) = (symbol_name x,symbol_name y,y,x) in
      ite (string_less x1 y1) (string_less x1 y1)
          (ite (equal x1 y1)
               (string_less (symbol_package_name x) (symbol_package_name y))
               nil))`;


(*
     [oracles: DEFUN ACL2::SUBSTITUTE-AC, DISK_THM] [axioms: ] []
     |- substitute_ac new old seq acc =
        itel
          [(endp seq,reverse acc);
           (eql old (car seq),
            substitute_ac new old (cdr seq) (cons new acc))]
          (substitute_ac new old (cdr seq) (cons (car seq) acc)),
*)

(*
     [oracles: DEFUN COMMON-LISP::SUBSTITUTE, DISK_THM] [axioms: ] []
     |- substitute new old seq =
        ite (stringp seq)
          (coerce (substitute_ac new old (coerce seq (csym "LIST")) nil)
             (csym "STRING")) (substitute_ac new old seq nil),
*)

(*
     [oracles: DEFUN COMMON-LISP::SUBSETP, DISK_THM] [axioms: ] []
     |- subsetp x y =
        ite (endp x) t (andl [member (car x) y; subsetp (cdr x) y]),
*)

(*
     [oracles: DEFUN COMMON-LISP::SUBLIS, DISK_THM] [axioms: ] []
     |- sublis alist tree =
        ite (atom tree)
          (let pair = assoc tree alist in ite pair (cdr pair) tree)
          (cons (sublis alist (car tree)) (sublis alist (cdr tree))),
*)

(*
     [oracles: DEFUN COMMON-LISP::SUBST, DISK_THM] [axioms: ] []
     |- subst new old tree =
        itel [(eql old tree,new); (atom tree,tree)]
          (cons (subst new old (car tree)) (subst new old (cdr tree))),
*)

(*
     [oracles: DEFUN ACL2::WORLDP, DISK_THM] [axioms: ] []
     |- worldp alist =
        ite (atom alist) (eq alist nil)
          (andl
             [consp (car alist); symbolp (caar alist); consp (cdar alist);
              symbolp (cadar alist); worldp (cdr alist)]),
*)

(*
     [oracles: DEFUN ACL2::PUTPROP] [axioms: ] []
     |- putprop symb key value world_alist =
        cons (cons symb (cons key value)) world_alist,
*)

(*
     [oracles: DEFUN ACL2::GETPROP-DEFAULT] [axioms: ] []
     |- getprop_default symb key default = default,
*)

(*
     [oracles: DEFUN ACL2::FGETPROP, DISK_THM] [axioms: ] []
     |- fgetprop symb key default world_alist =
        itel
          [(endp world_alist,default);
           (andl [eq symb (caar world_alist); eq key (cadar world_alist)],
            (let ans = cddar world_alist in
               ite (eq ans (ksym "ACL2-PROPERTY-UNBOUND")) default ans))]
          (fgetprop symb key default (cdr world_alist)),
*)

(*
     [oracles: DEFUN ACL2::SGETPROP, DISK_THM] [axioms: ] []
     |- sgetprop symb key default world_name world_alist =
        itel
          [(endp world_alist,default);
           (andl [eq symb (caar world_alist); eq key (cadar world_alist)],
            (let ans = cddar world_alist in
               ite (eq ans (ksym "ACL2-PROPERTY-UNBOUND")) default ans))]
          (sgetprop symb key default world_name (cdr world_alist)),
*)

(*
     [oracles: DEFUN ACL2::ORDERED-SYMBOL-ALISTP] [axioms: ] []
     |- ordered_symbol_alistp x =
        ite (atom x) (null x)
          (ite (atom (car x)) nil
             (ite (symbolp (car (car x)))
                (ite
                   (ite (atom (cdr x)) (atom (cdr x))
                      (ite (consp (car (cdr x)))
                         (ite (symbolp (car (car (cdr x))))
                            (symbol_less (car (car x)) (car (car (cdr x))))
                            nil) nil)) (ordered_symbol_alistp (cdr x)) nil)
                nil))
*)

(*
     [oracles: DEFUN ACL2::ADD-PAIR] [axioms: ] []
     |- add_pair key value l =
        ite (endp l) (cons (cons key value) nil)
          (ite (eq key (car (car l))) (cons (cons key value) (cdr l))
             (ite (symbol_less key (car (car l))) (cons (cons key value) l)
                (cons (car l) (add_pair key value (cdr l)))))
*)

(*
     [oracles: DEFUN ACL2::REMOVE-FIRST-PAIR, DISK_THM] [axioms: ] []
     |- remove_first_pair key l =
        itel [(endp l,nil); (eq key (caar l),cdr l)]
          (cons (car l) (remove_first_pair key (cdr l))),
*)

(*
     [oracles: DEFUN ACL2::TRUE-LIST-LISTP, DISK_THM] [axioms: ] []
     |- true_list_listp x =
        ite (atom x) (eq x nil)
          (andl [true_listp (car x); true_list_listp (cdr x)]),
*)

(*
     [oracles: DEFUN ACL2::GETPROPS1, DISK_THM] [axioms: ] []
     |- getprops1 alist =
        itel
          [(endp alist,nil);
           (ite (null (cdar alist)) (null (cdar alist))
              (eq (cadar alist) (ksym "ACL2-PROPERTY-UNBOUND")),
            getprops1 (cdr alist))]
          (cons (cons (caar alist) (cadar alist)) (getprops1 (cdr alist))),
*)

(*
     [oracles: DEFUN ACL2::GETPROPS, DISK_THM] [axioms: ] []
     |- getprops symb world_name world_alist =
        itel
          [(endp world_alist,nil);
           (eq symb (caar world_alist),
            (let alist = getprops symb world_name (cdr world_alist) in
               ite (eq (cddar world_alist) (ksym "ACL2-PROPERTY-UNBOUND"))
                 (ite (assoc_eq (cadar world_alist) alist)
                    (remove_first_pair (cadar world_alist) alist) alist)
                 (add_pair (cadar world_alist) (cddar world_alist) alist)))]
          (getprops symb world_name (cdr world_alist)),
*)

(*
     [oracles: DEFUN ACL2::HAS-PROPSP1, DISK_THM] [axioms: ] []
     |- has_propsp1 alist exceptions known_unbound =
        itel
          [(endp alist,nil);
           (itel
              [(null (cdar alist),null (cdar alist));
               (eq (cadar alist) (ksym "ACL2-PROPERTY-UNBOUND"),
                eq (cadar alist) (ksym "ACL2-PROPERTY-UNBOUND"));
               (member_eq (caar alist) exceptions,
                member_eq (caar alist) exceptions)]
              (member_eq (caar alist) known_unbound),
            has_propsp1 (cdr alist) exceptions known_unbound)] t,
*)

(*
     [oracles: DEFUN ACL2::HAS-PROPSP, DISK_THM] [axioms: ] []
     |- has_propsp symb exceptions world_name world_alist known_unbound =
        itel
          [(endp world_alist,nil);
           (itel
              [(not (eq symb (caar world_alist)),
                not (eq symb (caar world_alist)));
               (member_eq (cadar world_alist) exceptions,
                member_eq (cadar world_alist) exceptions)]
              (member_eq (cadar world_alist) known_unbound),
            has_propsp symb exceptions world_name (cdr world_alist)
              known_unbound);
           (eq (cddar world_alist) (ksym "ACL2-PROPERTY-UNBOUND"),
            has_propsp symb exceptions world_name (cdr world_alist)
              (cons (cadar world_alist) known_unbound))] t,
*)

(*
     [oracles: DEFUN ACL2::EXTEND-WORLD] [axioms: ] []
     |- extend_world name wrld = wrld,
*)

(*
     [oracles: DEFUN ACL2::RETRACT-WORLD] [axioms: ] []
     |- retract_world name wrld = wrld,
*)

(*
     [oracles: DEFUN ACL2::GLOBAL-VAL, DISK_THM] [axioms: ] []
     |- global_val var wrld =
        fgetprop var (asym "GLOBAL-VALUE")
          (List
             [ksym "ERROR";
              str
                "GLOBAL-VAL didn't find a value.  Initialize this ~\n                     symbol in PRIMORDIAL-WORLD-GLOBALS."])
          wrld,
*)

(*
     [oracles: DEFUN ACL2::FUNCTION-SYMBOLP, DISK_THM] [axioms: ] []
     |- function_symbolp acl2_sym wrld =
        not (eq (fgetprop acl2_sym (asym "FORMALS") t wrld) t),
*)

(*
     [oracles: DEFUN ACL2::SET-DIFFERENCE-EQUAL, DISK_THM] [axioms: ] []
     |- set_difference_equal l1 l2 =
        itel
          [(endp l1,nil);
           (member_equal (car l1) l2,set_difference_equal (cdr l1) l2)]
          (cons (car l1) (set_difference_equal (cdr l1) l2)),
*)

(*
     [oracles: DEFUN ACL2::BOUNDED-INTEGER-ALISTP, DISK_THM] [axioms: ] []
     |- bounded_integer_alistp l n =
        ite (atom l) (null l)
          (andl
             [consp (car l);
              (let key = caar l in
                 andl
                   [ite (eq key (ksym "HEADER")) (eq key (ksym "HEADER"))
                      (andl
                         [integerp key; integerp n; not (less key (nat 0));
                          less key n]); bounded_integer_alistp (cdr l) n])]),
*)

(*
     [oracles: DEFUN ACL2::KEYWORD-VALUE-LISTP, DISK_THM] [axioms: ] []
     |- keyword_value_listp l =
        ite (atom l) (null l)
          (andl
             [keywordp (car l); consp (cdr l); keyword_value_listp (cddr l)]),
*)

(*
     [oracles: DEFUN ACL2::ASSOC-KEYWORD, DISK_THM] [axioms: ] []
     |- assoc_keyword key l =
        itel [(endp l,nil); (eq key (car l),l)] (assoc_keyword key (cddr l)),
*)

(*
     [oracles: DEFUN ACL2::ARRAY1P, DISK_THM] [axioms: ] []
     |- array1p name l =
        andl
          [symbolp name; alistp l;
           (let header_keyword_list = cdr (assoc_eq (ksym "HEADER") l) in
              andl
                [keyword_value_listp header_keyword_list;
                 (let dimensions =
                        cadr
                          (assoc_keyword (ksym "DIMENSIONS")
                             header_keyword_list)
                  in
                    andl
                      [true_listp dimensions;
                       equal (length dimensions) (nat 1);
                       integerp (car dimensions);
                       integerp
                         (cadr
                            (assoc_keyword (ksym "MAXIMUM-LENGTH")
                               header_keyword_list));
                       less (nat 0) (car dimensions);
                       less (car dimensions)
                         (cadr
                            (assoc_keyword (ksym "MAXIMUM-LENGTH")
                               header_keyword_list));
                       not
                         (less (nat 2147483647)
                            (cadr
                               (assoc_keyword (ksym "MAXIMUM-LENGTH")
                                  header_keyword_list)));
                       bounded_integer_alistp l (car dimensions)])])],
*)

(*
     [oracles: DEFUN ACL2::BOUNDED-INTEGER-ALISTP2, DISK_THM] [axioms: ] []
     |- bounded_integer_alistp2 l i j =
        ite (atom l) (null l)
          (andl
             [consp (car l);
              (let key = caar l in
                 ite (eq key (ksym "HEADER")) (eq key (ksym "HEADER"))
                   (andl
                      [consp key;
                       (let i1 = car key in
                          andl
                            [integerp i1; integerp (cdr key); integerp i;
                             integerp j; not (less i1 (nat 0)); less i1 i;
                             not (less (cdr key) (nat 0));
                             less (cdr key) j])]));
              bounded_integer_alistp2 (cdr l) i j]),
*)

(*
     [oracles: DEFUN ACL2::ASSOC2, DISK_THM] [axioms: ] []
     |- assoc2 i j l =
        itel
          [(atom l,nil);
           (andl
              [consp (car l); consp (caar l); eql i (caaar l);
               eql j (cdaar l)],car l)] (assoc2 i j (cdr l)),
*)

(*
     [oracles: DEFUN ACL2::ARRAY2P, DISK_THM] [axioms: ] []
     |- array2p name l =
        andl
          [symbolp name; alistp l;
           (let header_keyword_list = cdr (assoc_eq (ksym "HEADER") l) in
              andl
                [keyword_value_listp header_keyword_list;
                 (let dimensions =
                        cadr
                          (assoc_keyword (ksym "DIMENSIONS")
                             header_keyword_list)
                  in
                    andl
                      [true_listp dimensions;
                       equal (length dimensions) (nat 2);
                       (let d1 = car dimensions in
                          andl
                            [integerp d1; integerp (cadr dimensions);
                             integerp
                               (cadr
                                  (assoc_keyword (ksym "MAXIMUM-LENGTH")
                                     header_keyword_list)); less (nat 0) d1;
                             less (nat 0) (cadr dimensions);
                             less (mult d1 (cadr dimensions))
                               (cadr
                                  (assoc_keyword (ksym "MAXIMUM-LENGTH")
                                     header_keyword_list));
                             not
                               (less (nat 2147483647)
                                  (cadr
                                     (assoc_keyword (ksym "MAXIMUM-LENGTH")
                                        header_keyword_list)));
                             bounded_integer_alistp2 l d1
                               (cadr dimensions)])])])],
*)

(*
     [oracles: DEFUN ACL2::HEADER, DISK_THM] [axioms: ] []
     |- header name l = prog2_dollar name (assoc_eq (ksym "HEADER") l),
*)

(*
     [oracles: DEFUN ACL2::DIMENSIONS, DISK_THM] [axioms: ] []
     |- dimensions name l =
        cadr (assoc_keyword (ksym "DIMENSIONS") (cdr (header name l))),
*)

(*
     [oracles: DEFUN ACL2::MAXIMUM-LENGTH, DISK_THM] [axioms: ] []
     |- maximum_length name l =
        cadr (assoc_keyword (ksym "MAXIMUM-LENGTH") (cdr (header name l))),
*)

(*
     [oracles: DEFUN ACL2::DEFAULT, DISK_THM] [axioms: ] []
     |- default name l =
        cadr (assoc_keyword (ksym "DEFAULT") (cdr (header name l))),
*)

(*
     [oracles: DEFUN ACL2::AREF1, DISK_THM] [axioms: ] []
     |- aref1 name l n =
        (let x = andl [not (eq n (ksym "HEADER")); assoc n l] in
           ite (null x) (default name l) (cdr x)),
*)

(*
     [oracles: DEFUN ACL2::COMPRESS11, DISK_THM] [axioms: ] []
     |- compress11 name l i n default =
        ite (zp (add n (unary_minus i))) nil
          (let (pair,n,i,l,name,default) = (assoc i l,n,i,l,name,default) in
             ite (ite (null pair) (null pair) (equal (cdr pair) default))
               (compress11 name l (add i (nat 1)) n default)
               (cons pair (compress11 name l (add i (nat 1)) n default))),
*)

(*
     [oracles: DEFUN ACL2::COMPRESS1, DISK_THM] [axioms: ] []
     |- compress1 name l =
        cons (header name l)
          (compress11 name l (nat 0) (car (dimensions name l))
             (default name l)),
*)

(*
     [oracles: DEFUN ACL2::ASET1, DISK_THM] [axioms: ] []
     |- aset1 name l n val =
        (let l = cons (cons n val) l in
           ite (less (maximum_length name l) (length l)) (compress1 name l)
             l),
*)

(*
     [oracles: DEFUN ACL2::AREF2, DISK_THM] [axioms: ] []
     |- aref2 name l i j =
        (let x = assoc2 i j l in ite (null x) (default name l) (cdr x)),
*)

(*
     [oracles: DEFUN ACL2::COMPRESS211, DISK_THM] [axioms: ] []
     |- compress211 name l i x j default =
        ite (zp (add j (unary_minus x))) nil
          (let (pair,j,x,i,l,name,default) =
                 (assoc2 i x l,j,x,i,l,name,default)
           in
             ite (ite (null pair) (null pair) (equal (cdr pair) default))
               (compress211 name l i (add (nat 1) x) j default)
               (cons pair (compress211 name l i (add (nat 1) x) j default))),
*)

(*
     [oracles: DEFUN ACL2::COMPRESS21, DISK_THM] [axioms: ] []
     |- compress21 name l n i j default =
        ite (zp (add i (unary_minus n))) nil
          (binary_append (compress211 name l n (nat 0) j default)
             (compress21 name l (add n (nat 1)) i j default)),
*)

(*
     [oracles: DEFUN ACL2::COMPRESS2, DISK_THM] [axioms: ] []
     |- compress2 name l =
        cons (header name l)
          (compress21 name l (nat 0) (car (dimensions name l))
             (cadr (dimensions name l)) (default name l)),
*)

(*
     [oracles: DEFUN ACL2::ASET2, DISK_THM] [axioms: ] []
     |- aset2 name l i j val =
        (let l = cons (cons (cons i j) val) l in
           ite (less (maximum_length name l) (length l)) (compress2 name l)
             l),
*)

(*
     [oracles: DEFUN ACL2::FLUSH-COMPRESS] [axioms: ] []
     |- flush_compress name = nil,
*)

(*
     [oracles: DEFUN ACL2::CDRN, DISK_THM] [axioms: ] []
     |- cdrn x i =
        ite (zp i) x (cdrn (List [csym "CDR"; x]) (add (int ~1) i)),
*)

(*
     [oracles: DEFUN ACL2::MV-NTH, DISK_THM] [axioms: ] []
     |- mv_nth n l =
        itel [(endp l,nil); (zp n,car l)] (mv_nth (add (int ~1) n) (cdr l)),
*)

val (mv_nth_def,mv_nth_ind) =
 acl2_defn "ACL2::MV-NTH"
  (`mv_nth n l =
     itel [(endp l,nil); (zp n,car l)] (mv_nth (add (int ~1) n) (cdr l))`,
   WF_REL_TAC `measure (sexp_size o SND)`
    THEN ACL2_SIMP_TAC []);

(*
     [oracles: DEFUN ACL2::MAKE-MV-NTHS, DISK_THM] [axioms: ] []
     |- make_mv_nths args call i =
        ite (endp args) nil
          (cons (List [car args; List [asym "MV-NTH"; i; call]])
             (make_mv_nths (cdr args) call (add i (nat 1)))),
*)

(*
     [oracles: DEFUN ACL2::UPDATE-NTH, DISK_THM] [axioms: ] []
     |- update_nth key val l =
        ite (zp key) (cons val (cdr l))
          (cons (car l) (update_nth (add (int ~1) key) val (cdr l))),
*)

(*
     [oracles: DEFUN ACL2::UPDATE-NTH-ARRAY] [axioms: ] []
     |- update_nth_array j key val l =
        update_nth j (update_nth key val (nth j l)) l,
*)

(*
     [oracles: DEFUN ACL2::32-BIT-INTEGERP, DISK_THM] [axioms: ] []
     |- acl2_32_bit_integerp x =
        andl
          [integerp x; not (less (nat 2147483647) x);
           not (less x (add (unary_minus (nat 2147483647)) (int ~1)))],
*)

(*
     [oracles: DEFUN ACL2::RATIONAL-LISTP, DISK_THM] [axioms: ] []
     |- rational_listp l =
        ite (atom l) (eq l nil)
          (andl [rationalp (car l); rational_listp (cdr l)]),
*)

(*
     [oracles: DEFUN ACL2::INTEGER-LISTP, DISK_THM] [axioms: ] []
     |- integer_listp l =
        ite (atom l) (equal l nil)
          (andl [integerp (car l); integer_listp (cdr l)]),
*)

(*
     [oracles: DEFUN ACL2::32-BIT-INTEGER-LISTP, DISK_THM] [axioms: ] []
     |- acl2_32_bit_integer_listp l =
        ite (atom l) (equal l nil)
          (andl
             [acl2_32_bit_integerp (car l);
              acl2_32_bit_integer_listp (cdr l)]),
*)

(*
     [oracles: DEFUN ACL2::OPEN-INPUT-CHANNELS, DISK_THM] [axioms: ] []
     |- open_input_channels st = nth (nat 0) st,
*)

(*
     [oracles: DEFUN ACL2::UPDATE-OPEN-INPUT-CHANNELS, DISK_THM] [axioms: ]
     [] |- update_open_input_channels x st = update_nth (nat 0) x st,
*)

(*
     [oracles: DEFUN ACL2::OPEN-OUTPUT-CHANNELS, DISK_THM] [axioms: ] []
     |- open_output_channels st = nth (nat 1) st,
*)

(*
     [oracles: DEFUN ACL2::UPDATE-OPEN-OUTPUT-CHANNELS, DISK_THM] [axioms: ]
     [] |- update_open_output_channels x st = update_nth (nat 1) x st,
*)

(*
     [oracles: DEFUN ACL2::GLOBAL-TABLE, DISK_THM] [axioms: ] []
     |- global_table st = nth (nat 2) st,
*)

(*
     [oracles: DEFUN ACL2::UPDATE-GLOBAL-TABLE, DISK_THM] [axioms: ] []
     |- update_global_table x st = update_nth (nat 2) x st,
*)

(*
     [oracles: DEFUN ACL2::T-STACK, DISK_THM] [axioms: ] []
     |- t_stack st = nth (nat 3) st,
*)

(*
     [oracles: DEFUN ACL2::UPDATE-T-STACK, DISK_THM] [axioms: ] []
     |- update_t_stack x st = update_nth (nat 3) x st,
*)

(*
     [oracles: DEFUN ACL2::32-BIT-INTEGER-STACK, DISK_THM] [axioms: ] []
     |- acl2_32_bit_integer_stack st = nth (nat 4) st,
*)

(*
     [oracles: DEFUN ACL2::UPDATE-32-BIT-INTEGER-STACK, DISK_THM] [axioms: ]
     [] |- update_32_bit_integer_stack x st = update_nth (nat 4) x st,
*)

(*
     [oracles: DEFUN ACL2::BIG-CLOCK-ENTRY, DISK_THM] [axioms: ] []
     |- big_clock_entry st = nth (nat 5) st,
*)

(*
     [oracles: DEFUN ACL2::UPDATE-BIG-CLOCK-ENTRY, DISK_THM] [axioms: ] []
     |- update_big_clock_entry x st = update_nth (nat 5) x st,
*)

(*
     [oracles: DEFUN ACL2::IDATES, DISK_THM] [axioms: ] []
     |- idates st = nth (nat 6) st,
*)

(*
     [oracles: DEFUN ACL2::UPDATE-IDATES, DISK_THM] [axioms: ] []
     |- update_idates x st = update_nth (nat 6) x st,
*)

(*
     [oracles: DEFUN ACL2::RUN-TIMES, DISK_THM] [axioms: ] []
     |- run_times st = nth (nat 7) st,
*)

(*
     [oracles: DEFUN ACL2::UPDATE-RUN-TIMES, DISK_THM] [axioms: ] []
     |- update_run_times x st = update_nth (nat 7) x st,
*)

(*
     [oracles: DEFUN ACL2::FILE-CLOCK, DISK_THM] [axioms: ] []
     |- file_clock st = nth (nat 8) st,
*)

(*
     [oracles: DEFUN ACL2::UPDATE-FILE-CLOCK, DISK_THM] [axioms: ] []
     |- update_file_clock x st = update_nth (nat 8) x st,
*)

(*
     [oracles: DEFUN ACL2::READABLE-FILES, DISK_THM] [axioms: ] []
     |- readable_files st = nth (nat 9) st,
*)

(*
     [oracles: DEFUN ACL2::WRITTEN-FILES, DISK_THM] [axioms: ] []
     |- written_files st = nth (nat 10) st,
*)

(*
     [oracles: DEFUN ACL2::UPDATE-WRITTEN-FILES, DISK_THM] [axioms: ] []
     |- update_written_files x st = update_nth (nat 10) x st,
*)

(*
     [oracles: DEFUN ACL2::READ-FILES, DISK_THM] [axioms: ] []
     |- read_files st = nth (nat 11) st,
*)

(*
     [oracles: DEFUN ACL2::UPDATE-READ-FILES, DISK_THM] [axioms: ] []
     |- update_read_files x st = update_nth (nat 11) x st,
*)

(*
     [oracles: DEFUN ACL2::WRITEABLE-FILES, DISK_THM] [axioms: ] []
     |- writeable_files st = nth (nat 12) st,
*)

(*
     [oracles: DEFUN ACL2::LIST-ALL-PACKAGE-NAMES-LST, DISK_THM] [axioms: ]
     [] |- list_all_package_names_lst st = nth (nat 13) st,
*)

(*
     [oracles: DEFUN ACL2::UPDATE-LIST-ALL-PACKAGE-NAMES-LST, DISK_THM]
     [axioms: ] []
     |- update_list_all_package_names_lst x st = update_nth (nat 13) x st,
*)

(*
     [oracles: DEFUN ACL2::USER-STOBJ-ALIST1, DISK_THM] [axioms: ] []
     |- user_stobj_alist1 st = nth (nat 14) st,
*)

(*
     [oracles: DEFUN ACL2::UPDATE-USER-STOBJ-ALIST1, DISK_THM] [axioms: ] []
     |- update_user_stobj_alist1 x st = update_nth (nat 14) x st,
*)

(*
     [oracles: DEFUN ACL2::ALL-BOUNDP, DISK_THM] [axioms: ] []
     |- all_boundp alist1 alist2 =
        ite (endp alist1) t
          (andl [assoc (caar alist1) alist2; all_boundp (cdr alist1) alist2]),
*)

(*
     [oracles: DEFUN ACL2::KNOWN-PACKAGE-ALISTP, DISK_THM] [axioms: ] []
     |- known_package_alistp x =
        ite (atom x) (null x)
          (andl
             [true_listp (car x); stringp (caar x); symbol_listp (cadar x);
              known_package_alistp (cdr x)]),
*)

(*
     [oracles: DEFUN ACL2::TIMER-ALISTP, DISK_THM] [axioms: ] []
     |- timer_alistp x =
        ite (atom x) (equal x nil)
          (andl
             [consp (car x); symbolp (caar x); rational_listp (cdar x);
              timer_alistp (cdr x)]),
*)

(*
     [oracles: DEFUN ACL2::TYPED-IO-LISTP, DISK_THM] [axioms: ] []
     |- typed_io_listp l typ =
        ite (atom l) (equal l nil)
          (andl
             [itel
                [(eql typ (ksym "CHARACTER"),characterp (car l));
                 (eql typ (ksym "BYTE"),
                  andl
                    [integerp (car l); not (less (car l) (nat 0));
                     less (car l) (nat 256)])]
                (andl [eql typ (ksym "OBJECT"); t]);
              typed_io_listp (cdr l) typ]),
*)

(*
     [oracles: DEFUN ACL2::OPEN-CHANNEL1, DISK_THM] [axioms: ] []
     |- open_channel1 l =
        andl
          [true_listp l; consp l;
           (let header = car l in
              andl
                [true_listp header; equal (length header) (nat 4);
                 eq (car header) (ksym "HEADER");
                 member_eq (cadr header)
                   (List [ksym "CHARACTER"; ksym "BYTE"; ksym "OBJECT"]);
                 stringp (caddr header); integerp (cadddr header);
                 typed_io_listp (cdr l) (cadr header)])],
*)

(*
     [oracles: DEFUN ACL2::OPEN-CHANNEL-LISTP, DISK_THM] [axioms: ] []
     |- open_channel_listp l =
        ite (endp l) t
          (andl [open_channel1 (cdar l); open_channel_listp (cdr l)]),
*)

(*
     [oracles: DEFUN ACL2::OPEN-CHANNELS-P, DISK_THM] [axioms: ] []
     |- open_channels_p x =
        andl [ordered_symbol_alistp x; open_channel_listp x],
*)

(*
     [oracles: DEFUN ACL2::FILE-CLOCK-P] [axioms: ] []
     |- file_clock_p x = natp x,
*)

(*
     [oracles: DEFUN ACL2::READABLE-FILE, DISK_THM] [axioms: ] []
     |- readable_file x =
        andl
          [true_listp x; consp x;
           (let key = car x in
              andl
                [true_listp key; equal (length key) (nat 3);
                 stringp (car key);
                 member (cadr key)
                   (List [ksym "CHARACTER"; ksym "BYTE"; ksym "OBJECT"]);
                 integerp (caddr key); typed_io_listp (cdr x) (cadr key)])],
*)

(*
     [oracles: DEFUN ACL2::READABLE-FILES-LISTP, DISK_THM] [axioms: ] []
     |- readable_files_listp x =
        ite (atom x) (equal x nil)
          (andl [readable_file (car x); readable_files_listp (cdr x)]),
*)

(*
     [oracles: DEFUN ACL2::READABLE-FILES-P] [axioms: ] []
     |- readable_files_p x = readable_files_listp x,
*)

(*
     [oracles: DEFUN ACL2::WRITTEN-FILE, DISK_THM] [axioms: ] []
     |- written_file x =
        andl
          [true_listp x; consp x;
           (let key = car x in
              andl
                [true_listp key; equal (length key) (nat 4);
                 stringp (car key); integerp (caddr key);
                 integerp (cadddr key);
                 member (cadr key)
                   (List [ksym "CHARACTER"; ksym "BYTE"; ksym "OBJECT"]);
                 typed_io_listp (cdr x) (cadr key)])],
*)

(*
     [oracles: DEFUN ACL2::WRITTEN-FILE-LISTP, DISK_THM] [axioms: ] []
     |- written_file_listp x =
        ite (atom x) (equal x nil)
          (andl [written_file (car x); written_file_listp (cdr x)]),
*)

(*
     [oracles: DEFUN ACL2::WRITTEN-FILES-P] [axioms: ] []
     |- written_files_p x = written_file_listp x,
*)

(*
     [oracles: DEFUN ACL2::READ-FILE-LISTP1, DISK_THM] [axioms: ] []
     |- read_file_listp1 x =
        andl
          [true_listp x; equal (length x) (nat 4); stringp (car x);
           member (cadr x)
             (List [ksym "CHARACTER"; ksym "BYTE"; ksym "OBJECT"]);
           integerp (caddr x); integerp (cadddr x)],
*)

(*
     [oracles: DEFUN ACL2::READ-FILE-LISTP, DISK_THM] [axioms: ] []
     |- read_file_listp x =
        ite (atom x) (equal x nil)
          (andl [read_file_listp1 (car x); read_file_listp (cdr x)]),
*)

(*
     [oracles: DEFUN ACL2::READ-FILES-P] [axioms: ] []
     |- read_files_p x = read_file_listp x,
*)

(*
     [oracles: DEFUN ACL2::WRITABLE-FILE-LISTP1, DISK_THM] [axioms: ] []
     |- writable_file_listp1 x =
        andl
          [true_listp x; equal (length x) (nat 3); stringp (car x);
           member (cadr x)
             (List [ksym "CHARACTER"; ksym "BYTE"; ksym "OBJECT"]);
           integerp (caddr x)],
*)

(*
     [oracles: DEFUN ACL2::WRITABLE-FILE-LISTP, DISK_THM] [axioms: ] []
     |- writable_file_listp x =
        ite (atom x) (equal x nil)
          (andl [writable_file_listp1 (car x); writable_file_listp (cdr x)]),
*)

(*
     [oracles: DEFUN ACL2::WRITEABLE-FILES-P] [axioms: ] []
     |- writeable_files_p x = writable_file_listp x,
*)

(*
     [oracles: DEFUN ACL2::STATE-P1, DISK_THM] [axioms: ] []
     |- state_p1 x =
        andl
          [true_listp x; equal (length x) (nat 15);
           open_channels_p (open_input_channels x);
           open_channels_p (open_output_channels x);
           ordered_symbol_alistp (global_table x);
           all_boundp
             (List
                [List [asym "ACCUMULATED-TTREE"];
                 List [asym "ACCUMULATED-WARNINGS"];
                 cons (asym "ACL2-VERSION") (str "ACL2 Version 2.9.3");
                 List [asym "AXIOMSP"]; List [asym "BDDNOTES"];
                 List [asym "CERTIFY-BOOK-FILE"];
                 List [asym "CONNECTED-BOOK-DIRECTORY"];
                 List [asym "CURRENT-ACL2-WORLD"];
                 cons (asym "CURRENT-PACKAGE") (str ACL2);
                 cons (asym "DEFAXIOMS-OKP-CERT") t;
                 List [asym "ERROR-TRACE-STACK"];
                 List [asym "EVISCERATE-HIDE-TERMS"];
                 cons (asym "FMT-HARD-RIGHT-MARGIN") (nat 77);
                 cons (asym "FMT-SOFT-RIGHT-MARGIN") (nat 65);
                 List [asym "GSTACKP"]; cons (asym "GUARD-CHECKING-ON") t;
                 List [asym "IN-CERTIFY-BOOK-FLG"];
                 List [asym "IN-LOCAL-FLG"]; List [asym "IN-PROVE-FLG"];
                 List [asym "INCLUDE-BOOK-ALIST-STATE"];
                 List [asym "INFIXP"];
                 List [asym "INHIBIT-OUTPUT-LST"; asym "SUMMARY"];
                 cons (asym "LD-LEVEL") (nat 0);
                 List [asym "LD-REDEFINITION-ACTION"];
                 List [asym "LD-SKIP-PROOFSP"];
                 List [asym "MATCH-FREE-ERROR"];
                 cons (asym "MORE-DOC-MAX-LINES") (nat 45);
                 cons (asym "MORE-DOC-MIN-LINES") (nat 35);
                 List [asym "MORE-DOC-STATE"];
                 List [asym "PACKAGES-CREATED-BY-DEFPKG"];
                 cons (asym "PRINT-BASE") (nat 10);
                 cons (asym "PRINT-CASE") (ksym "UPCASE");
                 List [asym "PRINT-CLAUSE-IDS"];
                 cons (asym "PRINT-DOC-START-COLUMN") (nat 15);
                 cons (asym "PROMPT-FUNCTION") (asym "DEFAULT-PRINT-PROMPT");
                 List [asym "PROOF-TREE-CTX"];
                 cons (asym "PROOFS-CO")
                   (osym "STANDARD-CHARACTER-OUTPUT-0");
                 List
                   [asym "RAW-ARITY-ALIST";
                    cons (asym "ER-PROGN") (csym "LAST");
                    cons (csym "EVAL-WHEN") (ksym "LAST");
                    cons (csym "LET") (ksym "LAST");
                    cons (csym "LET*") (ksym "LAST");
                    cons (asym "MV-LET") (ksym "LAST");
                    cons (asym "PROG2$") (ksym "LAST");
                    cons (csym "PROGN") (ksym "LAST");
                    cons (csym "THE") (ksym "LAST");
                    cons (csym "TIME") (ksym "LAST");
                    cons (csym "TRACE") (nat 1);
                    cons (csym "UNTRACE") (nat 1)]; List [asym "SAFE-MODE"];
                 List [asym "SAVED-OUTPUT-REVERSED"];
                 List [asym "SAVED-OUTPUT-TOKEN-LST"];
                 List [asym "SAVED-OUTPUT-P"];
                 cons (asym "SKIP-PROOFS-OKP-CERT") t;
                 List [asym "SKIPPED-PROOFSP"];
                 cons (asym "STANDARD-CO")
                   (osym "STANDARD-CHARACTER-OUTPUT-0");
                 cons (asym "STANDARD-OI") (osym "STANDARD-OBJECT-INPUT-0");
                 List [asym "TAINTED-OKP"]; List [asym "TIMER-ALIST"];
                 cons (asym "TRACE-CO") (osym "STANDARD-CHARACTER-OUTPUT-0");
                 cons (asym "TRANSLATE-ERROR-DEPTH") (int ~1);
                 cons (asym "TRIPLE-PRINT-PREFIX") (str " ");
                 List [asym "UNDONE-WORLDS-KILL-RING"; nil; nil; nil];
                 List [asym "WINDOW-INTERFACEP"];
                 List [asym "WORMHOLE-NAME"]; List [asym "WORMHOLE-OUTPUT"]])
             (global_table x);
           worldp (cdr (assoc (asym "CURRENT-ACL2-WORLD") (global_table x)));
           symbol_alistp
             (fgetprop (asym "ACL2-DEFAULTS-TABLE") (asym "TABLE-ALIST") nil
                (cdr (assoc (asym "CURRENT-ACL2-WORLD") (global_table x))));
           timer_alistp (cdr (assoc (asym "TIMER-ALIST") (global_table x)));
           known_package_alistp
             (fgetprop (asym "KNOWN-PACKAGE-ALIST") (asym "GLOBAL-VALUE") nil
                (cdr (assoc (asym "CURRENT-ACL2-WORLD") (global_table x))));
           true_listp (t_stack x);
           acl2_32_bit_integer_listp (acl2_32_bit_integer_stack x);
           integerp (big_clock_entry x); integer_listp (idates x);
           rational_listp (run_times x); file_clock_p (file_clock x);
           readable_files_p (readable_files x);
           written_files_p (written_files x); read_files_p (read_files x);
           writeable_files_p (writeable_files x);
           true_list_listp (list_all_package_names_lst x);
           symbol_alistp (user_stobj_alist1 x)],
*)

(*
     [oracles: DEFUN ACL2::STATE-P] [axioms: ] []
     |- state_p state_state = state_p1 state_state,
*)

(*
     [oracles: DEFUN ACL2::BUILD-STATE1, DISK_THM] [axioms: ] []
     |- build_state1 open_input_channels open_output_channels global_table
          t_stack acl2_32_bit_integer_stack big_clock idates run_times
          file_clock readable_files written_files read_files writeable_files
          list_all_package_names_lst user_stobj_alist =
        (let s =
               List
                 [open_input_channels; open_output_channels; global_table;
                  t_stack; acl2_32_bit_integer_stack; big_clock; idates;
                  run_times; file_clock; readable_files; written_files;
                  read_files; writeable_files; list_all_package_names_lst;
                  user_stobj_alist]
         in
           ite (state_p1 s) s
             (List
                [nil; nil;
                 List
                   [List [asym "ACCUMULATED-TTREE"];
                    List [asym "ACCUMULATED-WARNINGS"];
                    cons (asym "ACL2-VERSION") (str "ACL2 Version 2.9.3");
                    List [asym "AXIOMSP"]; List [asym "BDDNOTES"];
                    List [asym "CERTIFY-BOOK-FILE"];
                    List [asym "CONNECTED-BOOK-DIRECTORY"];
                    List [asym "CURRENT-ACL2-WORLD"];
                    cons (asym "CURRENT-PACKAGE") (str ACL2);
                    cons (asym "DEFAXIOMS-OKP-CERT") t;
                    List [asym "ERROR-TRACE-STACK"];
                    List [asym "EVISCERATE-HIDE-TERMS"];
                    cons (asym "FMT-HARD-RIGHT-MARGIN") (nat 77);
                    cons (asym "FMT-SOFT-RIGHT-MARGIN") (nat 65);
                    List [asym "GSTACKP"]; cons (asym "GUARD-CHECKING-ON") t;
                    List [asym "IN-CERTIFY-BOOK-FLG"];
                    List [asym "IN-LOCAL-FLG"]; List [asym "IN-PROVE-FLG"];
                    List [asym "INCLUDE-BOOK-ALIST-STATE"];
                    List [asym "INFIXP"];
                    List [asym "INHIBIT-OUTPUT-LST"; asym "SUMMARY"];
                    cons (asym "LD-LEVEL") (nat 0);
                    List [asym "LD-REDEFINITION-ACTION"];
                    List [asym "LD-SKIP-PROOFSP"];
                    List [asym "MATCH-FREE-ERROR"];
                    cons (asym "MORE-DOC-MAX-LINES") (nat 45);
                    cons (asym "MORE-DOC-MIN-LINES") (nat 35);
                    List [asym "MORE-DOC-STATE"];
                    List [asym "PACKAGES-CREATED-BY-DEFPKG"];
                    cons (asym "PRINT-BASE") (nat 10);
                    cons (asym "PRINT-CASE") (ksym "UPCASE");
                    List [asym "PRINT-CLAUSE-IDS"];
                    cons (asym "PRINT-DOC-START-COLUMN") (nat 15);
                    cons (asym "PROMPT-FUNCTION")
                      (asym "DEFAULT-PRINT-PROMPT");
                    List [asym "PROOF-TREE-CTX"];
                    cons (asym "PROOFS-CO")
                      (osym "STANDARD-CHARACTER-OUTPUT-0");
                    List
                      [asym "RAW-ARITY-ALIST";
                       cons (asym "ER-PROGN") (csym "LAST");
                       cons (csym "EVAL-WHEN") (ksym "LAST");
                       cons (csym "LET") (ksym "LAST");
                       cons (csym "LET*") (ksym "LAST");
                       cons (asym "MV-LET") (ksym "LAST");
                       cons (asym "PROG2$") (ksym "LAST");
                       cons (csym "PROGN") (ksym "LAST");
                       cons (csym "THE") (ksym "LAST");
                       cons (csym "TIME") (ksym "LAST");
                       cons (csym "TRACE") (nat 1);
                       cons (csym "UNTRACE") (nat 1)];
                    List [asym "SAFE-MODE"];
                    List [asym "SAVED-OUTPUT-REVERSED"];
                    List [asym "SAVED-OUTPUT-TOKEN-LST"];
                    List [asym "SAVED-OUTPUT-P"];
                    cons (asym "SKIP-PROOFS-OKP-CERT") t;
                    List [asym "SKIPPED-PROOFSP"];
                    cons (asym "STANDARD-CO")
                      (osym "STANDARD-CHARACTER-OUTPUT-0");
                    cons (asym "STANDARD-OI")
                      (osym "STANDARD-OBJECT-INPUT-0");
                    List [asym "TAINTED-OKP"]; List [asym "TIMER-ALIST"];
                    cons (asym "TRACE-CO")
                      (osym "STANDARD-CHARACTER-OUTPUT-0");
                    cons (asym "TRANSLATE-ERROR-DEPTH") (int ~1);
                    cons (asym "TRIPLE-PRINT-PREFIX") (str " ");
                    List [asym "UNDONE-WORLDS-KILL-RING"; nil; nil; nil];
                    List [asym "WINDOW-INTERFACEP"];
                    List [asym "WORMHOLE-NAME"];
                    List [asym "WORMHOLE-OUTPUT"]]; nil; nil; nat 4000000;
                 nil; nil; nat 1; nil; nil; nil; nil; nil; nil])),
*)

(*
     [oracles: DEFUN ACL2::COERCE-STATE-TO-OBJECT] [axioms: ] []
     |- coerce_state_to_object x = x,
*)

(*
     [oracles: DEFUN ACL2::COERCE-OBJECT-TO-STATE] [axioms: ] []
     |- coerce_object_to_state x = x,
*)

(*
     [oracles: DEFUN ACL2::GLOBAL-TABLE-CARS1] [axioms: ] []
     |- global_table_cars1 state_state =
        strip_cars (global_table state_state),
*)

(*
     [oracles: DEFUN ACL2::GLOBAL-TABLE-CARS] [axioms: ] []
     |- global_table_cars state_state = global_table_cars1 state_state,
*)

(*
     [oracles: DEFUN ACL2::BOUNDP-GLOBAL1, DISK_THM] [axioms: ] []
     |- boundp_global1 x state_state =
        andl [assoc x (global_table state_state); t],
*)

(*
     [oracles: DEFUN ACL2::BOUNDP-GLOBAL] [axioms: ] []
     |- boundp_global x state_state = boundp_global1 x state_state,
*)

(*
     [oracles: DEFUN ACL2::DELETE-PAIR, DISK_THM] [axioms: ] []
     |- delete_pair x l =
        itel [(endp l,nil); (eq x (caar l),cdr l)]
          (cons (car l) (delete_pair x (cdr l))),
*)

(*
     [oracles: DEFUN ACL2::MAKUNBOUND-GLOBAL] [axioms: ] []
     |- makunbound_global x state_state =
        update_global_table (delete_pair x (global_table state_state))
          state_state,
*)

(*
     [oracles: DEFUN ACL2::GET-GLOBAL] [axioms: ] []
     |- get_global x state_state = cdr (assoc x (global_table state_state)),
*)

(*
     [oracles: DEFUN ACL2::PUT-GLOBAL] [axioms: ] []
     |- put_global key value state_state =
        update_global_table (add_pair key value (global_table state_state))
          state_state,
*)

(*
     [oracles: DEFUN ACL2::SET-SKIPPED-PROOFSP, DISK_THM] [axioms: ] []
     |- set_skipped_proofsp state =
        put_global (asym "SKIPPED-PROOFSP") t state,
*)

(*
     [oracles: DEFUN ACL2::SYMBOL-DOUBLET-LISTP, DISK_THM] [axioms: ] []
     |- symbol_doublet_listp lst =
        ite (atom lst) (eq lst nil)
          (andl
             [consp (car lst); symbolp (caar lst); consp (cdar lst);
              null (cddar lst); symbol_doublet_listp (cdr lst)]),
*)

(*
     [oracles: DEFUN ACL2::STATE-GLOBAL-LET*-GET-GLOBALS, DISK_THM]
     [axioms: ] []
     |- state_global_let_star_get_globals bindings =
        ite (endp bindings) nil
          (cons
             (List
                [csym "IF";
                 List
                   [asym "BOUNDP-GLOBAL"; List [csym "QUOTE"; caar bindings];
                    asym "STATE"];
                 List
                   [csym "LIST";
                    List
                      [asym "F-GET-GLOBAL";
                       List [csym "QUOTE"; caar bindings]; asym "STATE"]];
                 nil]) (state_global_let_star_get_globals (cdr bindings))),
*)

(*
     [oracles: DEFUN ACL2::STATE-GLOBAL-LET*-PUT-GLOBALS, DISK_THM]
     [axioms: ] []
     |- state_global_let_star_put_globals bindings =
        ite (endp bindings) nil
          (cons
             (List
                [asym "F-PUT-GLOBAL"; List [csym "QUOTE"; caar bindings];
                 List
                   [asym "CHECK-VARS-NOT-FREE";
                    List [asym "STATE-GLOBAL-LET*-CLEANUP-LST"];
                    cadar bindings]; asym "STATE"])
             (state_global_let_star_put_globals (cdr bindings))),
*)

(*
     [oracles: DEFUN ACL2::STATE-GLOBAL-LET*-CLEANUP, DISK_THM] [axioms: ] []
     |- state_global_let_star_cleanup bindings cdr_expr =
        ite (endp bindings) nil
          (cons
             (List
                [csym "IF"; List [csym "CAR"; cdr_expr];
                 List
                   [asym "F-PUT-GLOBAL"; List [csym "QUOTE"; caar bindings];
                    List [csym "CAR"; List [csym "CAR"; cdr_expr]];
                    asym "STATE"];
                 List
                   [asym "MAKUNBOUND-GLOBAL";
                    List [csym "QUOTE"; caar bindings]; asym "STATE"]])
             (state_global_let_star_cleanup (cdr bindings)
                (List [csym "CDR"; cdr_expr]))),
*)

(*
     [oracles: DEFUN ACL2::INTEGER-RANGE-P, DISK_THM] [axioms: ] []
     |- integer_range_p lower upper x =
        andl [integerp x; not (less x lower); less x upper],
*)

(*
     [oracles: DEFUN ACL2::SIGNED-BYTE-P, DISK_THM] [axioms: ] []
     |- signed_byte_p bits x =
        andl
          [integerp bits; less (nat 0) bits;
           integer_range_p (unary_minus (expt (nat 2) (add (int ~1) bits)))
             (expt (nat 2) (add (int ~1) bits)) x],
*)

(*
     [oracles: DEFUN ACL2::UNSIGNED-BYTE-P, DISK_THM] [axioms: ] []
     |- unsigned_byte_p bits x =
        andl
          [integerp bits; not (less bits (nat 0));
           integer_range_p (nat 0) (expt (nat 2) bits) x],
*)

(*
     [oracles: DEFUN ACL2::ZPF, DISK_THM] [axioms: ] []
     |- zpf x = ite (integerp x) (not (less (nat 0) x)) t,
*)

(*
     [oracles: DEFUN COMMON-LISP::INTEGER-LENGTH, DISK_THM] [axioms: ] []
     |- integer_length i =
        itel [(zip i,nat 0); (common_lisp_equal i (int ~1),nat 0)]
          (add (nat 1) (integer_length (floor i (nat 2)))),
*)

(*
     [oracles: DEFUN ACL2::BINARY-LOGAND, DISK_THM] [axioms: ] []
     |- binary_logand i j =
        itel
          [(zip i,nat 0); (zip j,nat 0); (eql i (int ~1),j);
           (eql j (int ~1),i)]
          (let x =
                 mult (nat 2)
                   (binary_logand (floor i (nat 2)) (floor j (nat 2)))
           in
             add x (itel [(evenp i,nat 0); (evenp j,nat 0)] (nat 1))),
*)

(*
     [oracles: DEFUN COMMON-LISP::LOGNAND] [axioms: ] []
     |- lognand i j = lognot (binary_logand i j),
*)

(*
     [oracles: DEFUN ACL2::BINARY-LOGIOR] [axioms: ] []
     |- binary_logior i j = lognot (binary_logand (lognot i) (lognot j)),
*)

(*
     [oracles: DEFUN COMMON-LISP::LOGORC1] [axioms: ] []
     |- logorc1 i j = binary_logior (lognot i) j,
*)

(*
     [oracles: DEFUN COMMON-LISP::LOGORC2] [axioms: ] []
     |- logorc2 i j = binary_logior i (lognot j),
*)

(*
     [oracles: DEFUN COMMON-LISP::LOGANDC1] [axioms: ] []
     |- logandc1 i j = binary_logand (lognot i) j,
*)

(*
     [oracles: DEFUN COMMON-LISP::LOGANDC2] [axioms: ] []
     |- logandc2 i j = binary_logand i (lognot j),
*)

(*
     [oracles: DEFUN ACL2::BINARY-LOGEQV] [axioms: ] []
     |- binary_logeqv i j = binary_logand (logorc1 i j) (logorc1 j i),
*)

(*
     [oracles: DEFUN ACL2::BINARY-LOGXOR] [axioms: ] []
     |- binary_logxor i j = lognot (binary_logeqv i j),
*)

(*
     [oracles: DEFUN COMMON-LISP::LOGNOR] [axioms: ] []
     |- lognor i j = lognot (binary_logior i j),
*)

(*
     [oracles: DEFUN COMMON-LISP::LOGTEST] [axioms: ] []
     |- logtest x y = not (zerop (binary_logand x y)),
*)

(*
     [oracles: DEFUN ACL2::DIGIT-TO-CHAR, DISK_THM] [axioms: ] []
     |- digit_to_char n =
        itel
          [(eql n (nat 1),chr #"1"); (eql n (nat 2),chr #"2");
           (eql n (nat 3),chr #"3"); (eql n (nat 4),chr #"4");
           (eql n (nat 5),chr #"5"); (eql n (nat 6),chr #"6");
           (eql n (nat 7),chr #"7"); (eql n (nat 8),chr #"8");
           (eql n (nat 9),chr #"9"); (eql n (nat 10),chr #"A");
           (eql n (nat 11),chr #"B"); (eql n (nat 12),chr #"C");
           (eql n (nat 13),chr #"D"); (eql n (nat 14),chr #"E");
           (eql n (nat 15),chr #"F")] (chr #"0"),
*)

(*
     [oracles: DEFUN ACL2::PRINT-BASE-P, DISK_THM] [axioms: ] []
     |- print_base_p print_base =
        member print_base (List [nat 2; nat 8; nat 10; nat 16]),
*)

(*
     [oracles: DEFUN ACL2::EXPLODE-NONNEGATIVE-INTEGER, DISK_THM] [axioms: ]
     []
     |- explode_nonnegative_integer n print_base ans =
        ite (ite (zp n) (zp n) (not (print_base_p print_base)))
          (ite (null ans) (List [chr #"0"]) ans)
          (explode_nonnegative_integer (floor n print_base) print_base
             (cons (digit_to_char (mod n print_base)) ans)),
*)

(*
     [oracles: DEFUN ACL2::EXPLODE-ATOM, DISK_THM] [axioms: ] []
     |- explode_atom x print_base =
        itel
          [(rationalp x,
            ite (integerp x)
              (let digits =
                     ite (less x (nat 0))
                       (cons (chr #"-")
                          (explode_nonnegative_integer (unary_minus x)
                             print_base nil))
                       (explode_nonnegative_integer x print_base nil)
               in
                 ite
                   (eql (nat 10)
                      (let var = print_base in
                         ite (integerp var) var
                           (the_error (csym "INTEGER") var))) digits
                   (cons (chr #"#")
                      (cons
                         (itel
                            [(eql print_base (nat 2),chr #"b");
                             (eql print_base (nat 8),chr #"o");
                             (eql print_base (nat 16),chr #"x")]
                            (illegal (asym "EXPLODE-ATOM")
                               (str "Unexpected base, ~x0") print_base))
                         digits)))
              (binary_append (explode_atom (numerator x) print_base)
                 (cons (chr #"/")
                    (explode_nonnegative_integer (denominator x) print_base
                       nil))));
           (complex_rationalp x,
            cons (chr #"#")
              (cons (chr #"C")
                 (cons (chr #"(")
                    (binary_append (explode_atom (realpart x) print_base)
                       (cons (chr #" ")
                          (binary_append
                             (explode_atom (imagpart x) print_base)
                             (List [chr #")"])))))));
           (characterp x,List [x]); (stringp x,coerce x (csym "LIST"))]
          (coerce (symbol_name x) (csym "LIST")),
*)

(*
     [oracles: DEFUN ACL2::OPEN-INPUT-CHANNEL-P1, DISK_THM] [axioms: ] []
     |- open_input_channel_p1 channel typ state_state =
        (let pair = assoc_eq channel (open_input_channels state_state) in
           andl [pair; eq (cadadr pair) typ]),
*)

(*
     [oracles: DEFUN ACL2::OPEN-OUTPUT-CHANNEL-P1, DISK_THM] [axioms: ] []
     |- open_output_channel_p1 channel typ state_state =
        (let pair = assoc_eq channel (open_output_channels state_state) in
           andl [pair; eq (cadadr pair) typ]),
*)

(*
     [oracles: DEFUN ACL2::OPEN-INPUT-CHANNEL-P] [axioms: ] []
     |- open_input_channel_p channel typ state_state =
        open_input_channel_p1 channel typ state_state,
*)

(*
     [oracles: DEFUN ACL2::OPEN-OUTPUT-CHANNEL-P] [axioms: ] []
     |- open_output_channel_p channel typ state_state =
        open_output_channel_p1 channel typ state_state,
*)

(*
     [oracles: DEFUN ACL2::OPEN-OUTPUT-CHANNEL-ANY-P1, DISK_THM] [axioms: ]
     []
     |- open_output_channel_any_p1 channel state_state =
        itel
          [(open_output_channel_p1 channel (ksym "CHARACTER") state_state,
            open_output_channel_p1 channel (ksym "CHARACTER") state_state);
           (open_output_channel_p1 channel (ksym "BYTE") state_state,
            open_output_channel_p1 channel (ksym "BYTE") state_state)]
          (open_output_channel_p1 channel (ksym "OBJECT") state_state),
*)

(*
     [oracles: DEFUN ACL2::OPEN-OUTPUT-CHANNEL-ANY-P] [axioms: ] []
     |- open_output_channel_any_p channel state_state =
        open_output_channel_any_p1 channel state_state,
*)

(*
     [oracles: DEFUN ACL2::OPEN-INPUT-CHANNEL-ANY-P1, DISK_THM] [axioms: ] []
     |- open_input_channel_any_p1 channel state_state =
        itel
          [(open_input_channel_p1 channel (ksym "CHARACTER") state_state,
            open_input_channel_p1 channel (ksym "CHARACTER") state_state);
           (open_input_channel_p1 channel (ksym "BYTE") state_state,
            open_input_channel_p1 channel (ksym "BYTE") state_state)]
          (open_input_channel_p1 channel (ksym "OBJECT") state_state),
*)

(*
     [oracles: DEFUN ACL2::OPEN-INPUT-CHANNEL-ANY-P] [axioms: ] []
     |- open_input_channel_any_p channel state_state =
        open_input_channel_any_p1 channel state_state,
*)

(*
     [oracles: DEFUN ACL2::CHECK-HEX-UPPERCASE] [axioms: ] []
     |- check_hex_uppercase print_base = nil,
*)

(*
     [oracles: DEFUN ACL2::WRITE-BYTE$, DISK_THM] [axioms: ] []
     |- write_byte_dollar x channel state_state =
        (let entry =
               cdr (assoc_eq channel (open_output_channels state_state))
         in
           update_open_output_channels
             (add_pair channel (cons (car entry) (cons x (cdr entry)))
                (open_output_channels state_state)) state_state),
*)

(*
     [oracles: DEFUN ACL2::PRINT-OBJECT$, DISK_THM] [axioms: ] []
     |- print_object_dollar x channel state_state =
        (let entry =
               cdr (assoc_eq channel (open_output_channels state_state))
         in
           update_open_output_channels
             (add_pair channel (cons (car entry) (cons x (cdr entry)))
                (open_output_channels state_state)) state_state),
*)

(*
     [oracles: DEFUN ACL2::CLOSE-INPUT-CHANNEL, DISK_THM] [axioms: ] []
     |- close_input_channel channel state_state =
        (let state_state =
               update_file_clock (add (nat 1) (file_clock state_state))
                 state_state
         in
         let header_entries =
               cdadr (assoc_eq channel (open_input_channels state_state))
         in
         let state_state =
               update_read_files
                 (cons
                    (List
                       [cadr header_entries; car header_entries;
                        caddr header_entries; file_clock state_state])
                    (read_files state_state)) state_state
         in
         let state_state =
               update_open_input_channels
                 (delete_pair channel (open_input_channels state_state))
                 state_state
         in
           state_state),
*)

(*
     [oracles: DEFUN ACL2::CLOSE-OUTPUT-CHANNEL, DISK_THM] [axioms: ] []
     |- close_output_channel channel state_state =
        (let state_state =
               update_file_clock (add (nat 1) (file_clock state_state))
                 state_state
         in
         let pair = assoc_eq channel (open_output_channels state_state) in
         let header_entries = cdadr pair in
         let state_state =
               update_written_files
                 (cons
                    (cons
                       (List
                          [cadr header_entries; car header_entries;
                           caddr header_entries; file_clock state_state])
                       (cddr pair)) (written_files state_state)) state_state
         in
         let state_state =
               update_open_output_channels
                 (delete_pair channel (open_output_channels state_state))
                 state_state
         in
           state_state),
*)

(*
     [oracles: DEFUN ACL2::READ-CHAR$, DISK_THM] [axioms: ] []
     |- read_char_dollar channel state_state =
        (let entry = cdr (assoc_eq channel (open_input_channels state_state))
         in
           List
             [cadr entry;
              update_open_input_channels
                (add_pair channel (cons (car entry) (cddr entry))
                   (open_input_channels state_state)) state_state]),
*)

(*
     [oracles: DEFUN ACL2::PEEK-CHAR$, DISK_THM] [axioms: ] []
     |- peek_char_dollar channel state_state =
        (let entry = cdr (assoc_eq channel (open_input_channels state_state))
         in
           cadr entry),
*)

(*
     [oracles: DEFUN ACL2::READ-BYTE$, DISK_THM] [axioms: ] []
     |- read_byte_dollar channel state_state =
        (let entry = cdr (assoc_eq channel (open_input_channels state_state))
         in
           List
             [cadr entry;
              update_open_input_channels
                (add_pair channel (cons (car entry) (cddr entry))
                   (open_input_channels state_state)) state_state]),
*)

(*
     [oracles: DEFUN ACL2::READ-OBJECT, DISK_THM] [axioms: ] []
     |- read_object channel state_state =
        (let entry = cdr (assoc_eq channel (open_input_channels state_state))
         in
           ite (cdr entry)
             (List
                [nil; cadr entry;
                 update_open_input_channels
                   (add_pair channel (cons (car entry) (cddr entry))
                      (open_input_channels state_state)) state_state])
             (List [t; nil; state_state])),
*)

(*
     [oracles: DEFUN ACL2::SOME-SLASHABLE, DISK_THM] [axioms: ] []
     |- some_slashable l =
        itel
          [(endp l,nil);
           (member (car l)
              (List
                 [chr #"\n"; chr #"\f"; chr #" "; chr #"\""; chr #"#";
                  chr #"'"; chr #"("; chr #")"; chr #","; chr #"."; chr #":";
                  chr #";"; chr #"\\"; chr #"`"; chr #"a"; chr #"b";
                  chr #"c"; chr #"d"; chr #"e"; chr #"f"; chr #"g"; chr #"h";
                  chr #"i"; chr #"j"; chr #"k"; chr #"l"; chr #"m"; chr #"n";
                  chr #"o"; chr #"p"; chr #"q"; chr #"r"; chr #"s"; chr #"t";
                  chr #"u"; chr #"v"; chr #"w"; chr #"x"; chr #"y"; chr #"z";
                  chr #"|"]),t)] (some_slashable (cdr l)),
*)

(*
     [oracles: DEFUN ACL2::MAY-NEED-SLASHES, DISK_THM] [axioms: ] []
     |- may_need_slashes x =
        (let l = coerce x (csym "LIST") in
           itel
             [(null l,null l);
              (andl
                 [member (car l)
                    (List
                       [chr #"0"; chr #"1"; chr #"2"; chr #"3"; chr #"4";
                        chr #"5"; chr #"6"; chr #"7"; chr #"8"; chr #"9";
                        chr #"+"; chr #"-"; chr #"."; chr #"^"; chr #"_"]);
                  not (member (car (last l)) (List [chr #"+"; chr #"-"]))],
               andl
                 [member (car l)
                    (List
                       [chr #"0"; chr #"1"; chr #"2"; chr #"3"; chr #"4";
                        chr #"5"; chr #"6"; chr #"7"; chr #"8"; chr #"9";
                        chr #"+"; chr #"-"; chr #"."; chr #"^"; chr #"_"]);
                  not (member (car (last l)) (List [chr #"+"; chr #"-"]))])]
             (some_slashable l)),
*)

(*
     [oracles: DEFUN ACL2::T-STACK-LENGTH1] [axioms: ] []
     |- t_stack_length1 state_state = length (t_stack state_state),
*)

(*
     [oracles: DEFUN ACL2::T-STACK-LENGTH] [axioms: ] []
     |- t_stack_length state_state = t_stack_length1 state_state,
*)

(*
     [oracles: DEFUN ACL2::MAKE-LIST-AC, DISK_THM] [axioms: ] []
     |- make_list_ac n val ac =
        ite (zp n) ac (make_list_ac (add (int ~1) n) val (cons val ac)),
*)

(*
     [oracles: DEFUN ACL2::EXTEND-T-STACK] [axioms: ] []
     |- extend_t_stack n val state_state =
        update_t_stack
          (binary_append (t_stack state_state) (make_list_ac n val nil))
          state_state,
*)

(*
     [oracles: DEFUN ACL2::FIRST-N-AC, DISK_THM] [axioms: ] []
     |- first_n_ac i l ac =
        ite (zp i) (reverse ac)
          (first_n_ac (add (int ~1) i) (cdr l) (cons (car l) ac)),
*)

(*
     [oracles: DEFUN ACL2::TAKE] [axioms: ] []
     |- take n l = first_n_ac n l nil,
*)

(*
     [oracles: DEFUN ACL2::SUBSEQ-LIST] [axioms: ] []
     |- subseq_list lst start end =
        take (add end (unary_minus start)) (nthcdr start lst),
*)

(*
     [oracles: DEFUN COMMON-LISP::SUBSEQ, DISK_THM] [axioms: ] []
     |- subseq seq start end =
        ite (stringp seq)
          (coerce
             (subseq_list (coerce seq (csym "LIST")) start
                (ite end end (length seq))) (csym "STRING"))
          (subseq_list seq start (ite end end (length seq))),
*)

(*
     [oracles: DEFUN COMMON-LISP::BUTLAST, DISK_THM] [axioms: ] []
     |- butlast lst n =
        (let lng = len lst in
           ite (not (less n lng)) nil (take (add lng (unary_minus n)) lst)),
*)

(*
     [oracles: DEFUN ACL2::SHRINK-T-STACK, DISK_THM] [axioms: ] []
     |- shrink_t_stack n state_state =
        update_t_stack
          (first_n_ac
             (max (nat 0)
                (add (length (t_stack state_state)) (unary_minus n)))
             (t_stack state_state) nil) state_state,
*)

(*
     [oracles: DEFUN ACL2::AREF-T-STACK] [axioms: ] []
     |- aref_t_stack i state_state = nth i (t_stack state_state),
*)

(*
     [oracles: DEFUN ACL2::ASET-T-STACK] [axioms: ] []
     |- aset_t_stack i val state_state =
        update_t_stack (update_nth i val (t_stack state_state)) state_state,
*)

(*
     [oracles: DEFUN ACL2::32-BIT-INTEGER-STACK-LENGTH1] [axioms: ] []
     |- acl2_32_bit_integer_stack_length1 state_state =
        length (acl2_32_bit_integer_stack state_state),
*)

(*
     [oracles: DEFUN ACL2::32-BIT-INTEGER-STACK-LENGTH] [axioms: ] []
     |- acl2_32_bit_integer_stack_length state_state =
        acl2_32_bit_integer_stack_length1 state_state,
*)

(*
     [oracles: DEFUN ACL2::EXTEND-32-BIT-INTEGER-STACK] [axioms: ] []
     |- extend_32_bit_integer_stack n val state_state =
        update_32_bit_integer_stack
          (binary_append (acl2_32_bit_integer_stack state_state)
             (make_list_ac n val nil)) state_state,
*)

(*
     [oracles: DEFUN ACL2::SHRINK-32-BIT-INTEGER-STACK, DISK_THM] [axioms: ]
     []
     |- shrink_32_bit_integer_stack n state_state =
        update_32_bit_integer_stack
          (first_n_ac
             (max (nat 0)
                (add (length (acl2_32_bit_integer_stack state_state))
                   (unary_minus n))) (acl2_32_bit_integer_stack state_state)
             nil) state_state,
*)

(*
     [oracles: DEFUN ACL2::AREF-32-BIT-INTEGER-STACK] [axioms: ] []
     |- aref_32_bit_integer_stack i state_state =
        nth i (acl2_32_bit_integer_stack state_state),
*)

(*
     [oracles: DEFUN ACL2::ASET-32-BIT-INTEGER-STACK] [axioms: ] []
     |- aset_32_bit_integer_stack i val state_state =
        update_32_bit_integer_stack
          (update_nth i val (acl2_32_bit_integer_stack state_state))
          state_state,
*)

(*
     [oracles: DEFUN ACL2::BIG-CLOCK-NEGATIVE-P, DISK_THM] [axioms: ] []
     |- big_clock_negative_p state_state =
        less (big_clock_entry state_state) (nat 0),
*)

(*
     [oracles: DEFUN ACL2::DECREMENT-BIG-CLOCK, DISK_THM] [axioms: ] []
     |- decrement_big_clock state_state =
        update_big_clock_entry (add (int ~1) (big_clock_entry state_state))
          state_state,
*)

(*
     [oracles: DEFUN ACL2::LIST-ALL-PACKAGE-NAMES, DISK_THM] [axioms: ] []
     |- list_all_package_names state_state =
        List
          [car (list_all_package_names_lst state_state);
           update_list_all_package_names_lst
             (cdr (list_all_package_names_lst state_state)) state_state],
*)

(*
     [oracles: DEFUN ACL2::USER-STOBJ-ALIST] [axioms: ] []
     |- user_stobj_alist state_state = user_stobj_alist1 state_state,
*)

(*
     [oracles: DEFUN ACL2::UPDATE-USER-STOBJ-ALIST] [axioms: ] []
     |- update_user_stobj_alist x state_state =
        update_user_stobj_alist1 x state_state,
*)

(*
     [oracles: DEFUN ACL2::POWER-EVAL, DISK_THM] [axioms: ] []
     |- power_eval l b =
        ite (endp l) (nat 0) (add (car l) (mult b (power_eval (cdr l) b))),
*)

(*
     [oracles: DEFUN ACL2::READ-IDATE, DISK_THM] [axioms: ] []
     |- read_idate state_state =
        List
          [ite (null (idates state_state)) (nat 0)
             (car (idates state_state));
           update_idates (cdr (idates state_state)) state_state],
*)

(*
     [oracles: DEFUN ACL2::READ-RUN-TIME, DISK_THM] [axioms: ] []
     |- read_run_time state_state =
        List
          [ite (null (run_times state_state)) (nat 0)
             (car (run_times state_state));
           update_run_times (cdr (run_times state_state)) state_state],
*)

(*
     [oracles: DEFUN ACL2::MAIN-TIMER, DISK_THM] [axioms: ] []
     |- main_timer state =
        (let current_time = mv_nth (nat 0) (read_run_time state) in
         let old_value =
               ite
                 (andl
                    [boundp_global (asym "MAIN-TIMER")
                       (mv_nth (nat 1) (read_run_time state));
                     rationalp
                       (get_global (asym "MAIN-TIMER")
                          (mv_nth (nat 1) (read_run_time state)))])
                 (get_global (asym "MAIN-TIMER")
                    (mv_nth (nat 1) (read_run_time state))) (nat 0)
         in
         let state =
               put_global (asym "MAIN-TIMER") current_time
                 (mv_nth (nat 1) (read_run_time state))
         in
           List [add current_time (unary_minus old_value); state]),
*)

(*
     [oracles: DEFUN ACL2::PUT-ASSOC-EQ, DISK_THM] [axioms: ] []
     |- put_assoc_eq name val alist =
        itel
          [(endp alist,List [cons name val]);
           (eq name (caar alist),cons (cons name val) (cdr alist))]
          (cons (car alist) (put_assoc_eq name val (cdr alist))),
*)

(*
     [oracles: DEFUN ACL2::PUT-ASSOC-EQL, DISK_THM] [axioms: ] []
     |- put_assoc_eql name val alist =
        itel
          [(endp alist,List [cons name val]);
           (eql name (caar alist),cons (cons name val) (cdr alist))]
          (cons (car alist) (put_assoc_eql name val (cdr alist))),
*)

(*
     [oracles: DEFUN ACL2::PUT-ASSOC-EQUAL, DISK_THM] [axioms: ] []
     |- put_assoc_equal name val alist =
        itel
          [(endp alist,List [cons name val]);
           (equal name (caar alist),cons (cons name val) (cdr alist))]
          (cons (car alist) (put_assoc_equal name val (cdr alist))),
*)

(*
     [oracles: DEFUN ACL2::SET-TIMER, DISK_THM] [axioms: ] []
     |- set_timer name val state =
        put_global (asym "TIMER-ALIST")
          (put_assoc_eq name val (get_global (asym "TIMER-ALIST") state))
          state,
*)

(*
     [oracles: DEFUN ACL2::GET-TIMER, DISK_THM] [axioms: ] []
     |- get_timer name state =
        cdr (assoc_eq name (get_global (asym "TIMER-ALIST") state)),
*)

(*
     [oracles: DEFUN ACL2::PUSH-TIMER] [axioms: ] []
     |- push_timer name val state =
        set_timer name (cons val (get_timer name state)) state,
*)

(*
     [oracles: DEFUN ACL2::POP-TIMER, DISK_THM] [axioms: ] []
     |- pop_timer name flg state =
        (let timer = get_timer name state in
           set_timer name
             (ite flg (cons (add (car timer) (cadr timer)) (cddr timer))
                (cdr timer)) state),
*)

(*
     [oracles: DEFUN ACL2::ADD-TIMERS, DISK_THM] [axioms: ] []
     |- add_timers name1 name2 state =
        (let timer1 = get_timer name1 state in
           set_timer name1
             (cons (add (car timer1) (car (get_timer name2 state)))
                (cdr timer1)) state),
*)

(*
     [oracles: DEFUN ACL2::INCREMENT-TIMER, DISK_THM] [axioms: ] []
     |- increment_timer name state =
        (let timer = get_timer name state in
         let epsilon = mv_nth (nat 0) (main_timer state) in
           set_timer name (cons (add (car timer) epsilon) (cdr timer))
             (mv_nth (nat 1) (main_timer state))),
*)

(*
     [oracles: DEFUN ACL2::W, DISK_THM] [axioms: ] []
     |- w state = get_global (asym "CURRENT-ACL2-WORLD") state,
*)

(*
     [oracles: DEFUN ACL2::CURRENT-PACKAGE, DISK_THM] [axioms: ] []
     |- current_package state = get_global (asym "CURRENT-PACKAGE") state,
*)

(*
     [oracles: DEFUN ACL2::KNOWN-PACKAGE-ALIST, DISK_THM] [axioms: ] []
     |- known_package_alist state =
        fgetprop (asym "KNOWN-PACKAGE-ALIST") (asym "GLOBAL-VALUE") nil
          (w state),
*)

(*
     [oracles: DEFUN ACL2::SET-W, DISK_THM] [axioms: ] []
     |- set_w flg wrld state =
        (let state =
               put_global (asym "CURRENT-ACL2-WORLD") (prog2_dollar flg wrld)
                 state
         in
           ite
             (let entry =
                    assoc_equal (current_package state)
                      (known_package_alist state)
              in
                andl [not (caddr entry); entry]) state
             (put_global (asym "CURRENT-PACKAGE") (str ACL2) state)),
*)

(*
     [oracles: DEFUN ACL2::UNION-EQ, DISK_THM] [axioms: ] []
     |- union_eq lst1 lst2 =
        itel
          [(endp lst1,lst2);
           (member_eq (car lst1) lst2,union_eq (cdr lst1) lst2)]
          (cons (car lst1) (union_eq (cdr lst1) lst2)),
*)

(*
     [oracles: DEFUN ACL2::LD-SKIP-PROOFSP, DISK_THM] [axioms: ] []
     |- ld_skip_proofsp state = get_global (asym "LD-SKIP-PROOFSP") state,
*)

(*
     [oracles: DEFUN ACL2::MAKE-VAR-LST1, DISK_THM] [axioms: ] []
     |- make_var_lst1 root acl2_sym n acc =
        ite (zp n) acc
          (make_var_lst1 root acl2_sym (add (int ~1) n)
             (cons
                (intern_in_package_of_symbol
                   (coerce
                      (binary_append root
                         (explode_nonnegative_integer (add (int ~1) n)
                            (nat 10) nil)) (csym "STRING")) acl2_sym) acc)),
*)

(*
     [oracles: DEFUN ACL2::MAKE-VAR-LST, DISK_THM] [axioms: ] []
     |- make_var_lst acl2_sym n =
        make_var_lst1 (coerce (symbol_name acl2_sym) (csym "LIST")) acl2_sym
          n nil,
*)

(*
     [oracles: DEFUN ACL2::NON-FREE-VAR-RUNES, DISK_THM] [axioms: ] []
     |- non_free_var_runes runes free_var_runes_once free_var_runes_all acc =
        ite (endp runes) acc
          (non_free_var_runes (cdr runes) free_var_runes_once
             free_var_runes_all
             (ite
                (ite (member_equal (car runes) free_var_runes_once)
                   (member_equal (car runes) free_var_runes_once)
                   (member_equal (car runes) free_var_runes_all)) acc
                (cons (car runes) acc))),
*)

(*
     [oracles: DEFUN ACL2::FREE-VAR-RUNES, DISK_THM] [axioms: ] []
     |- free_var_runes flg wrld =
        ite (eq flg (ksym "ONCE"))
          (global_val (asym "FREE-VAR-RUNES-ONCE") wrld)
          (global_val (asym "FREE-VAR-RUNES-ALL") wrld),
*)

(*
     [oracles: DEFUN ACL2::ABSOLUTE-PATHNAME-STRING-P, DISK_THM] [axioms: ]
     []
     |- absolute_pathname_string_p acl2_str directoryp os =
        (let len = length acl2_str in
           andl
             [less (nat 0) (length acl2_str);
              ite (eq os (ksym "MSWINDOWS"))
                (let pos_colon = position (chr #":") acl2_str in
                   andl
                     [pos_colon; position (chr #"/") acl2_str;
                      less pos_colon (position (chr #"/") acl2_str)])
                (eql (char acl2_str (nat 0)) (chr #"/"));
              ite directoryp
                (eql (char acl2_str (add (int ~1) len)) (chr #"/")) t]),
*)

(*
     [oracles: DEFUN ACL2::OS, DISK_THM] [axioms: ] []
     |- os wrld = global_val (asym "OPERATING-SYSTEM") wrld,
*)

(*
     [oracles: DEFUN ACL2::INCLUDE-BOOK-DIR-ALISTP, DISK_THM] [axioms: ] []
     |- include_book_dir_alistp x os =
        ite (atom x) (null x)
          (andl
             [consp (car x); keywordp (caar x); stringp (cdar x);
              absolute_pathname_string_p (cdar x) t os;
              include_book_dir_alistp (cdr x) os]),
*)

(*
     [oracles: DEFUN ACL2::TABLE-ALIST, DISK_THM] [axioms: ] []
     |- table_alist name wrld = fgetprop name (asym "TABLE-ALIST") nil wrld,
*)

(*
     [oracles: DEFUN ACL2::DEFAULT-VERIFY-GUARDS-EAGERNESS, DISK_THM]
     [axioms: ] []
     |- default_verify_guards_eagerness wrld =
        ite
          (cdr
             (assoc_eq (ksym "VERIFY-GUARDS-EAGERNESS")
                (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld)))
          (cdr
             (assoc_eq (ksym "VERIFY-GUARDS-EAGERNESS")
                (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld))) (nat 1),
*)

(*
     [oracles: DEFUN ACL2::DEFAULT-COMPILE-FNS, DISK_THM] [axioms: ] []
     |- default_compile_fns wrld =
        cdr
          (assoc_eq (ksym "COMPILE-FNS")
             (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld)),
*)

(*
     [oracles: DEFUN ACL2::DEFAULT-MEASURE-FUNCTION, DISK_THM] [axioms: ] []
     |- default_measure_function wrld =
        ite
          (cdr
             (assoc_eq (ksym "MEASURE-FUNCTION")
                (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld)))
          (cdr
             (assoc_eq (ksym "MEASURE-FUNCTION")
                (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld)))
          (asym "ACL2-COUNT"),
*)

(*
     [oracles: DEFUN ACL2::DEFAULT-WELL-FOUNDED-RELATION, DISK_THM]
     [axioms: ] []
     |- default_well_founded_relation wrld =
        ite
          (cdr
             (assoc_eq (ksym "WELL-FOUNDED-RELATION")
                (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld)))
          (cdr
             (assoc_eq (ksym "WELL-FOUNDED-RELATION")
                (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld))) (asym "O<"),
*)

(*
     [oracles: DEFUN ACL2::GOOD-DEFUN-MODE-P, DISK_THM] [axioms: ] []
     |- good_defun_mode_p p =
        member_eq p (List [ksym "LOGIC"; ksym "PROGRAM"]),
*)

(*
     [oracles: DEFUN ACL2::DEFAULT-DEFUN-MODE, DISK_THM] [axioms: ] []
     |- default_defun_mode wrld =
        (let val =
               cdr
                 (assoc_eq (ksym "DEFUN-MODE")
                    (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld))
         in
           ite (good_defun_mode_p val) val (ksym "PROGRAM")),
*)

(*
     [oracles: DEFUN ACL2::DEFAULT-DEFUN-MODE-FROM-STATE] [axioms: ] []
     |- default_defun_mode_from_state state = default_defun_mode (w state),
*)

(*
     [oracles: DEFUN ACL2::INVISIBLE-FNS-TABLE, DISK_THM] [axioms: ] []
     |- invisible_fns_table wrld =
        table_alist (asym "INVISIBLE-FNS-TABLE") wrld,
*)

(*
     [oracles: DEFUN ACL2::UNARY-FUNCTION-SYMBOL-LISTP, DISK_THM] [axioms: ]
     []
     |- unary_function_symbol_listp lst wrld =
        ite (atom lst) (null lst)
          (andl
             [symbolp (car lst);
              (let formals = fgetprop (car lst) (asym "FORMALS") nil wrld in
                 andl [consp formals; null (cdr formals)]);
              unary_function_symbol_listp (cdr lst) wrld]),
*)

(*
     [oracles: DEFUN ACL2::INVISIBLE-FNS-ENTRYP, DISK_THM] [axioms: ] []
     |- invisible_fns_entryp key val wrld =
        andl
          [symbolp key; function_symbolp key wrld;
           unary_function_symbol_listp val wrld],
*)

(*
     [oracles: DEFUN ACL2::DELETE-ASSOC-EQ, DISK_THM] [axioms: ] []
     |- delete_assoc_eq key alist =
        itel [(endp alist,nil); (eq key (caar alist),cdr alist)]
          (cons (car alist) (delete_assoc_eq key (cdr alist))),
*)

(*
     [oracles: DEFUN ACL2::DELETE-ASSOC-EQUAL, DISK_THM] [axioms: ] []
     |- delete_assoc_equal key alist =
        itel [(endp alist,nil); (equal key (caar alist),cdr alist)]
          (cons (car alist) (delete_assoc_equal key (cdr alist))),
*)

(*
     [oracles: DEFUN ACL2::BACKCHAIN-LIMIT, DISK_THM] [axioms: ] []
     |- backchain_limit wrld =
        andl
          [cdr
             (assoc_eq (ksym "BACKCHAIN-LIMIT")
                (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld));
           cdr
             (assoc_eq (ksym "BACKCHAIN-LIMIT")
                (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld))],
*)

(*
     [oracles: DEFUN ACL2::DEFAULT-BACKCHAIN-LIMIT, DISK_THM] [axioms: ] []
     |- default_backchain_limit wrld =
        andl
          [cdr
             (assoc_eq (ksym "DEFAULT-BACKCHAIN-LIMIT")
                (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld));
           cdr
             (assoc_eq (ksym "DEFAULT-BACKCHAIN-LIMIT")
                (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld))],
*)

(*
     [oracles: DEFUN ACL2::REWRITE-STACK-LIMIT, DISK_THM] [axioms: ] []
     |- rewrite_stack_limit wrld =
        ite
          (cdr
             (assoc_eq (ksym "REWRITE-STACK-LIMIT")
                (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld)))
          (cdr
             (assoc_eq (ksym "REWRITE-STACK-LIMIT")
                (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld))) (nat 1000),
*)

(*
     [oracles: DEFUN ACL2::CASE-SPLIT-LIMITATIONS, DISK_THM] [axioms: ] []
     |- case_split_limitations wrld =
        cdr
          (assoc_eq (ksym "CASE-SPLIT-LIMITATIONS")
             (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld)),
*)

(*
     [oracles: DEFUN ACL2::BINOP-TABLE, DISK_THM] [axioms: ] []
     |- binop_table wrld = table_alist (asym "BINOP-TABLE") wrld,
*)

(*
     [oracles: DEFUN ACL2::MATCH-FREE-DEFAULT, DISK_THM] [axioms: ] []
     |- match_free_default wrld =
        cdr
          (assoc_eq (ksym "MATCH-FREE-DEFAULT")
             (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld)),
*)

(*
     [oracles: DEFUN ACL2::MATCH-FREE-OVERRIDE, DISK_THM] [axioms: ] []
     |- match_free_override wrld =
        (let pair =
               assoc_eq (ksym "MATCH-FREE-OVERRIDE")
                 (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld)
         in
           ite (ite (null pair) (null pair) (eq (cdr pair) (ksym "CLEAR")))
             (ksym "CLEAR")
             (cons
                (cdr
                   (assoc_eq (ksym "MATCH-FREE-OVERRIDE-NUME")
                      (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld)))
                (cdr pair))),
*)

(*
     [oracles: DEFUN ACL2::NON-LINEARP, DISK_THM] [axioms: ] []
     |- non_linearp wrld =
        (let temp =
               assoc_eq (ksym "NON-LINEARP")
                 (table_alist (asym "ACL2-DEFAULTS-TABLE") wrld)
         in
           andl [temp; cdr temp]),
*)

(*
     [oracles: DEFUN ACL2::MACRO-ALIASES, DISK_THM] [axioms: ] []
     |- macro_aliases wrld = table_alist (asym "MACRO-ALIASES-TABLE") wrld,
*)

(*
     [oracles: DEFUN ACL2::NTH-ALIASES, DISK_THM] [axioms: ] []
     |- nth_aliases wrld = table_alist (asym "NTH-ALIASES-TABLE") wrld,
*)

(*
     [oracles: DEFUN ACL2::DEFAULT-HINTS, DISK_THM] [axioms: ] []
     |- default_hints wrld =
        cdr (assoc_eq t (table_alist (asym "DEFAULT-HINTS-TABLE") wrld)),
*)

(*
     [oracles: DEFUN ACL2::FIX-TRUE-LIST, DISK_THM] [axioms: ] []
     |- fix_true_list x =
        andl [consp x; cons (car x) (fix_true_list (cdr x))],
*)

(*
     [oracles: DEFUN ACL2::BOOLEAN-LISTP, DISK_THM] [axioms: ] []
     |- boolean_listp lst =
        ite (atom lst) (eq lst nil)
          (andl
             [ite (eq (car lst) t) (eq (car lst) t) (eq (car lst) nil);
              boolean_listp (cdr lst)]),
*)

(*
     [oracles: DEFUN ACL2::WORMHOLE1] [axioms: ] []
     |- wormhole1 name input form ld_specials = nil,
*)

(*
     [oracles: DEFUN ACL2::ABORT!] [axioms: ] [] |- abort_exclaim = nil,
*)

(*
     [oracles: DEFUN ACL2::FMT-TO-COMMENT-WINDOW] [axioms: ] []
     |- fmt_to_comment_window acl2_str alist col evisc_tuple = nil,
*)

(*
     [oracles: DEFUN ACL2::PAIRLIS2, DISK_THM] [axioms: ] []
     |- pairlis2 x y =
        ite (endp y) nil
          (cons (cons (car x) (car y)) (pairlis2 (cdr x) (cdr y))),
*)

(*
     [oracles: DEFUN ACL2::DUPLICATES, DISK_THM] [axioms: ] []
     |- duplicates lst =
        itel
          [(endp lst,nil);
           (member_eq (car lst) (cdr lst),
            add_to_set_eq (car lst) (duplicates (cdr lst)))]
          (duplicates (cdr lst)),
*)

(*
     [oracles: DEFUN ACL2::ADD-TO-SET-EQUAL, DISK_THM] [axioms: ] []
     |- add_to_set_equal x l = ite (member_equal x l) l (cons x l),
*)

(*
     [oracles: DEFUN ACL2::INTERSECTION-EQ, DISK_THM] [axioms: ] []
     |- intersection_eq l1 l2 =
        itel
          [(endp l1,nil);
           (member_eq (car l1) l2,
            cons (car l1) (intersection_eq (cdr l1) l2))]
          (intersection_eq (cdr l1) l2),
*)

(*
     [oracles: DEFUN ACL2::EVENS, DISK_THM] [axioms: ] []
     |- evens l = ite (endp l) nil (cons (car l) (evens (cddr l))),
*)

(*
     [oracles: DEFUN ACL2::ODDS] [axioms: ] [] |- odds l = evens (cdr l),
*)

(*
     [oracles: DEFUN ACL2::SET-EQUALP-EQUAL, DISK_THM] [axioms: ] []
     |- set_equalp_equal lst1 lst2 =
        andl [subsetp_equal lst1 lst2; subsetp_equal lst2 lst1],
*)

(*
     [oracles: DEFUN ACL2::MFC-CLAUSE, DISK_THM] [axioms: ] []
     |- mfc_clause mfc =
        andl
          [consp mfc; consp (cdr mfc); consp (cddr mfc); consp (cdddr mfc);
           consp (cddddr mfc); consp (cddddr (cdr mfc));
           consp (cddddr (cddr mfc)); consp (cddddr (cdddr mfc));
           consp (cddddr (cddddr mfc)); consp (car (cddddr (cddddr mfc)));
           consp (cdar (cddddr (cddddr mfc)));
           consp (cddar (cddddr (cddddr mfc)));
           consp (cdddar (cddddr (cddddr mfc)));
           consp (cddddr (car (cddddr (cddddr mfc))));
           consp (car (cddddr (car (cddddr (cddddr mfc)))));
           pseudo_term_listp (cdar (cddddr (car (cddddr (cddddr mfc)))));
           cdar (cddddr (car (cddddr (cddddr mfc))))],
*)

(*
     [oracles: DEFUN ACL2::TYPE-ALIST-ENTRYP, DISK_THM] [axioms: ] []
     |- type_alist_entryp x =
        andl
          [consp x; pseudo_termp (car x); consp (cdr x); integerp (cadr x);
           not (less (cadr x) (int ~8192)); not (less (nat 8191) (cadr x))],
*)

(*
     [oracles: DEFUN ACL2::TYPE-ALISTP, DISK_THM] [axioms: ] []
     |- type_alistp x =
        ite (consp x) (andl [type_alist_entryp (car x); type_alistp (cdr x)])
          (eq x nil),
*)

(*
     [oracles: DEFUN ACL2::MFC-TYPE-ALIST, DISK_THM] [axioms: ] []
     |- mfc_type_alist mfc = andl [consp mfc; type_alistp (car mfc); car mfc],
*)

(*
     [oracles: DEFUN ACL2::MFC-ANCESTORS, DISK_THM] [axioms: ] []
     |- mfc_ancestors mfc =
        andl
          [consp mfc; consp (cdr mfc); consp (cddr mfc); consp (cdddr mfc);
           consp (cddddr mfc); consp (cddddr (cdr mfc));
           true_listp (car (cddddr (cdr mfc))); car (cddddr (cdr mfc))],
*)

(*
     [oracles: DEFUN ACL2::BAD-ATOM, DISK_THM] [axioms: ] []
     |- bad_atom x =
        not
          (itel
             [(consp x,consp x); (acl2_numberp x,acl2_numberp x);
              (symbolp x,symbolp x); (characterp x,characterp x)]
             (stringp x)),
*)

val bad_atom_def =
 acl2Define "ACL2::BAD-ATOM"
  `bad_atom x =
    not
     (itel
       [(consp x,consp x);
        (acl2_numberp x,acl2_numberp x);
        (symbolp x,symbolp x);
        (characterp x,characterp x)]
       (stringp x))`;

(*
     [oracles: DEFUN ACL2::ALPHORDER, DISK_THM] [axioms: ] []
     |- alphorder x y =
        itel
          [(rationalp x,ite (rationalp y) (not (less y x)) t);
           (rationalp y,nil);
           (complex_rationalp x,
            ite (complex_rationalp y)
              (ite (less (realpart x) (realpart y))
                 (less (realpart x) (realpart y))
                 (andl
                    [common_lisp_equal (realpart x) (realpart y);
                     not (less (imagpart y) (imagpart x))])) t);
           (complex_rationalp y,nil);
           (characterp x,
            ite (characterp y) (not (less (char_code y) (char_code x))) t);
           (characterp y,nil);
           (stringp x,ite (stringp y) (andl [string_less_equal x y; t]) t);
           (stringp y,nil);
           (symbolp x,ite (symbolp y) (not (symbol_less y x)) t);
           (symbolp y,nil)] (bad_atom_less_equal x y),
*)

val alphorder_def =
 acl2Define "ACL2::ALPHORDER"
  `alphorder x y =
    itel
      [(rationalp x,ite (rationalp y) (not (less y x)) t);
       (rationalp y,nil);
       (complex_rationalp x,
        ite (complex_rationalp y)
          (ite (less (realpart x) (realpart y))
             (less (realpart x) (realpart y))
             (andl
                [common_lisp_equal (realpart x) (realpart y);
                 not (less (imagpart y) (imagpart x))])) t);
       (complex_rationalp y,nil);
       (characterp x,
        ite (characterp y) (not (less (char_code y) (char_code x))) t);
       (characterp y,nil);
       (stringp x,ite (stringp y) (andl [string_less_equal x y; t]) t);
       (stringp y,nil);
       (symbolp x,ite (symbolp y) (not (symbol_less y x)) t);
       (symbolp y,nil)] (bad_atom_less_equal x y)`;

(*
     [oracles: DEFUN ACL2::LEXORDER, DISK_THM] [axioms: ] []
     |- lexorder x y =
        itel
          [(atom x,ite (atom y) (alphorder x y) t); (atom y,nil);
           (equal (car x) (car y),lexorder (cdr x) (cdr y))]
          (lexorder (car x) (car y)),
*)

val (lexorder_def,lexorder_ind) =
 acl2_defn "ACL2::LEXORDER"
  (`lexorder x y =
     itel
      [(atom x,ite (atom y) (alphorder x y) t); (atom y,nil);
       (equal (car x) (car y),lexorder (cdr x) (cdr y))]
      (lexorder (car x) (car y))`,
   WF_REL_TAC `measure (sexp_size o SND)`
    THEN ACL2_SIMP_TAC []);


(*
     [oracles: DEFUN ACL2::IF*, DISK_THM] [axioms: ] []
     |- if_star x y z = ite x y z,
*)

(*
     [oracles: DEFUN ACL2::RESIZE-LIST, DISK_THM] [axioms: ] []
     |- resize_list lst n default_value =
        andl
          [integerp n; less (nat 0) n;
           cons (ite (atom lst) default_value (car lst))
             (resize_list (ite (atom lst) lst (cdr lst)) (add (int ~1) n)
                default_value)],
*)

(*
     [oracles: DEFUN ACL2::E/D-FN, DISK_THM] [axioms: ] []
     |- e_slash_d_fn theory e_slash_d_list enable_p =
        itel
          [(atom e_slash_d_list,theory);
           (enable_p,
            e_slash_d_fn
              (List
                 [asym "UNION-THEORIES"; theory;
                  List [csym "QUOTE"; car e_slash_d_list]])
              (cdr e_slash_d_list) nil)]
          (e_slash_d_fn
             (List
                [asym "SET-DIFFERENCE-THEORIES"; theory;
                 List [csym "QUOTE"; car e_slash_d_list]])
             (cdr e_slash_d_list) t),
*)

val _ = export_acl2_theory();
