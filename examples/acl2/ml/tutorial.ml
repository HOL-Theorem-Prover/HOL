(*****************************************************************************)
(* The project starts off by loading the encoding library: acl2encodeLib     *)
(*****************************************************************************)

load "acl2encodeLib";
open acl2encodeLib;

(*****************************************************************************)
(* We also load the example types and the example functions.                 *)
(*****************************************************************************)

load "testTypesTheory";
load "testFunctionsTheory";

(*---------------------------------------------------------------------------*)
(* Simple functions:                                                         *)
(*---------------------------------------------------------------------------*)

(*****************************************************************************)
(* We start by encoding simple functions, that is, functions that may be     *)
(* translated across their entire range (they are fully specified) and rely  *)
(* only on functions that may be encoded across their entire range.          *)
(*     Functions may be given in clausal or equational (a single clause)     *)
(* form, where mutually recursive functions are given as conjunctions.       *)
(*                                                                           *)
(* Such functions are translated using the function:                         *)
(*     translate_simple_function : (term * string) list -> thm -> thm        *)
(*                                                                           *)
(* The first argument relates function constants to the names of translated  *)
(* functions and the second is the argument itself.                          *)
(*                                                                           *)
(* The function EXP:                                                         *)
(*     |- (!m. m ** 0 = 1) /\ (!m n. m ** SUC n = m * m ** n)                *)
(* is translated as follows:                                                 *)
(*****************************************************************************)

val translated_exp = 
    translate_simple_function 
            [(``($**):num -> num -> num``,"exp")]
	    arithmeticTheory.EXP;

(*****************************************************************************)
(* val translated_exp =                                                      *)
(* |- exp m arg =                                                            *)
(* ite (andl [natp m; natp arg])                                             *)
(*   (ite (zp arg) (nat 1)                                                   *)
(*     (mult m (acl2_expt m (add arg (unary_minus (nat 1)))))) (nat 0) : thm *)
(*                                                                           *)
(* This also produces the following theorem:                                 *)
(*****************************************************************************)

val propagation_exp = fetch "-" "prop_exp";

(*****************************************************************************)
(* val propagation_exp = |- nat (m ** arg) = exp (nat m) (nat arg) : thm     *)
(*                                                                           *)
(* This theorem is automatically added to the set of rewrites,               *)
(* functionEncodeLib.rewrites, using the function                            *)
(* functionEncodeLib.add_standard_rewrite 0 "prop_exp" ...                   *)
(*                                                                           *)
(* The function LENGTH (instantiated to operate on concrete lists of natural *)
(* numbers) can also be converted using this form:                           *)
(*****************************************************************************)

val translated_length = 
    translate_simple_function
             [(``LENGTH``,"length")]
	     (INST_TYPE [alpha |-> ``:num``] listTheory.LENGTH);

val propagation_length = fetch "-" "prop_length";

(*****************************************************************************)
(* val translated_length =                                                   *)
(*   |- length arg =                                                         *)
(*   ite (listnum arg)                                                       *)
(*     (ite (atom arg) (nat 0) (add (len (cdr arg)) (nat 1))) (nat 0) : thm  *)
(*                                                                           *)
(* val propagation_length =                                                  *)
(*   |- nat (LENGTH arg) = length (list nat arg) : thm                       *)
(*****************************************************************************)

(*---------------------------------------------------------------------------*)
(* Flattening recognizers:                                                   *)
(*---------------------------------------------------------------------------*)

(*****************************************************************************)
(* It should also be noted that the constant 'listnum' is automatically      *)
(* constructed to assist this definition. This is characterised by the       *)
(* following definitions:                                                    *)
(*****************************************************************************)

val translated_listnum = fetch "-" "translated_listnum";

val propagation_listnum = fetch "-" "prop_listnum";

(*****************************************************************************)
(* val translated_listnum =                                                  *)
(*   |- listnum x =                                                          *)
(*   ite (consp x)                                                           *)
(*     (ite (consp x) (andl [natp (car x); listnum (cdr x)]) nil)            *)
(*     (equal x nil) : thm                                                   *)
(*                                                                           *)
(* val propagation_listnum =                                                 *)
(*   |- bool (listp (sexp_to_bool o natp) x) = listnum (I x) : thm           *)
(*                                                                           *)
(* 'listnum' is created using the function:                                  *)
(*      flatten_recognizers : (hol_type -> string) -> hol_type -> thm list   *)
(* function creates recognition functions, suitable for export to ACL2, for  *)
(* the type supplied, and any types in mutual recursion with it.             *)
(*                                                                           *)
(* We can create a different translation using this function directly:       *)
(*****************************************************************************)

val [translated_natp_list] = flatten_recognizers (K "natp_list") ``:num list``;

val propagation_natp_list = fetch "-" "natp_list";

(*****************************************************************************)
(* val translated_natp_list =                                                *)
(*   |- natp_list x =                                                        *)
(*       ite (consp x)                                                       *)
(*         (ite (consp x) (andl [natp (car x); natp_list (cdr x)]) nil)      *)
(*         (equal x nil) : thm                                               *)
(*                                                                           *)
(* val propagation_natp_list =                                               *)
(*   |- !x. natp_list x = bool (listp (sexp_to_bool o natp) x) : thm         *)
(*                                                                           *)
(* To use this new definition, the previous definition should be removed:    *)
(*****************************************************************************)

val _ = functionEncodeLib.remove_rewrite "listnum";

(*****************************************************************************)
(* The rewrite names are displayed in the trace as, in this case, R(listnum) *)
(*                                                                           *)
(* As rewrites for translated functions are automatically added to the       *)
(* rewrite set, functions relying on previous translations may also be       *)
(* easily translated. For example:                                           *)
(*****************************************************************************)

val translated_append =
    translate_simple_function
             [(``$++``,"append")]
	     (INST_TYPE [alpha |-> ``:num``] listTheory.APPEND);

val translated_reverse =
    translate_simple_function
             [(``REVERSE``,"reverse")]
	     (INST_TYPE [alpha |-> ``:num``] listTheory.REVERSE_DEF);

(*****************************************************************************)
(* val translated_append =                                                   *)
(*   |- append arg l2 =                                                      *)
(*   ite (andl [natp_list arg; natp_list l2])                                *)
(*     (ite (atom arg) l2 (cons (car arg) (append (cdr arg) l2))) nil        *)
(*                                                                           *)
(* val translated_reverse =                                                  *)
(*   |- reverse arg =                                                        *)
(*   ite (natp_list arg)                                                     *)
(*     (ite (atom arg) nil                                                   *)
(*        (append (reverse (cdr arg)) (cons (car arg) nil))) nil             *)
(*****************************************************************************)

(*---------------------------------------------------------------------------*)
(* Conditional functions:                                                    *)
(*---------------------------------------------------------------------------*)

(*****************************************************************************)
(* Some functions, such as DIV,MOD or %/int_div, can only be translated over *)
(* a subset of their range. Therefore, functions defined using these can     *)
(* only be translated over a subset of their range OR guard calls to the     *)
(* restricted functions using conditional statements.                        *)
(*                                                                           *)
(* The latter form of definitions are translated using:                      *)
(*    translate_conditional_function :                                       *)
(*           (term * string) list -> thm list -> thm -> thm                  *)
(* This is very similar to translate_simple_function except it takes a list  *)
(* of theorems to *assist* the translation.                                  *)
(*                                                                           *)
(* The function 'i2n' is defined as follows:                                 *)
(* |- !i l. i2n i l =                                                        *)
(*     Num (if 0 <= i then i % 2 ** l                                        *)
(*                    else (i + 1) rem 2 ** l - 1 + 2 ** l) : thm            *)
(*                                                                           *)
(* The functions 'rem' and '%' can only be translated if their second        *)
(* argument is non-zero. The propagation theorems are as follows:            *)
(*****************************************************************************)

val INT_REM = extendTranslateTheory.INT_REM;

val INT_MOD = extendTranslateTheory.INT_MOD;

(*****************************************************************************)
(* |- ~(b = 0) ==> (int (a rem b) = acl2_rem (int a) (int b)) : thm          *)
(* |- ~(b = 0) ==> (int (a % b) = acl2_mod (int a) (int b)) : thm            *)
(*                                                                           *)
(* To translate i2n we must prove that 0 <= i implies that the second        *)
(* arguments are non-zero:                                                   *)
(*****************************************************************************)

local
open intLib integerTheory
val i2n_lemma = prove(``0 <= (i + 1) rem 2 ** l - 1 + 2 ** l``,
    REWRITE_TAC [ARITH_PROVE ``0i <= a - 1 + b = ~a < b``] THEN
    MATCH_MP_TAC (ARITH_PROVE ``!a b c. a <= b /\ b < c ==> a < c:int``) THEN
    Q.EXISTS_TAC `ABS ((i + 1) rem 2 ** l)` THEN
    METIS_TAC [INT_REMQUOT,INT_ABS_NUM,INT_EXP,INT_EXP_EQ0,
        ARITH_PROVE ``~(2 = 0i)``,INT_ABS,INT_NOT_LT,INT_NEGNEG,INT_LE_REFL,
	INT_LE_NEGL]);
in
val thms = [INT_EXP_EQ0,ARITH_PROVE ``~(2 = 0i)``,
            REWRITE_CONV [integerTheory.INT_POS,integerTheory.INT_EXP] 
                 ``0 <= 2 ** a``,
            prove(``~(b = 0) /\ 0i <= b ==> 0 <= a % b``,
		     METIS_TAC [INT_MOD_BOUNDS,INT_NOT_LT]),i2n_lemma]
end;

(*****************************************************************************)
(* val thms =                                                                *)
(*   [|- !p n. (p ** n = 0) = (p = 0) /\ ~(n = 0), |- ~(2 = 0),              *)
(*    |- 0 <= 2 ** a = T, |- ~(b = 0) /\ 0 <= b ==> 0 <= a % b,              *)
(*    |- 0 <= (i + 1) rem 2 ** l - 1 + 2 ** l]                               *)
(*                                                                           *)
(* The translation code employs a simple forward-chaining rewriter, that     *)
(* when translating the expression 'encode (if P then A else B)' with the    *)
(* extra theorem '|- P ==> Q' the expression 'A' will be encoded under the   *)
(* assumptions 'P' and 'Q'.                                                  *)
(*                                                                           *)
(* A simple back-chaining rewriter is also employed that attempts to prove   *)
(* a term by repeatedly rewriting using the theorems given.                  *)
(*                                                                           *)
(* By setting the trace level to 3 we can see that the back-chaining         *)
(* rewriter is employed a number of times. The syntax:                       *)
(*    backtracking...                                                        *)
(*    #0#1#2#3#4F#4#5#6F#3#4T#3T#2#3T                                        *)
(* indicates the depth of search at each node, and whether the term given    *)
(* was proven true or false.                                                 *)
(*****************************************************************************)

val translated_i2n =
    translate_conditional_function
              [(``i2n``,"I2N")] thms
	      signedintTheory.i2n_def;

(*****************************************************************************)
(* val translated_i2n =                                                      *)
(*   |- I2N i l =                                                            *)
(*   ite (andl [integerp i; natp l])                                         *)
(*     (ite (not (less i (int 0))) (acl2_mod i (acl2_expt (int 2) l))        *)
(*        (add                                                               *)
(*           (add (acl2_rem (add i (int 1)) (acl2_expt (int 2) l))           *)
(*              (unary_minus (int 1))) (acl2_expt (int 2) l))) (nat 0) : thm *)
(*****************************************************************************)

(*---------------------------------------------------------------------------*)
(* Limit functions:                                                          *)
(*---------------------------------------------------------------------------*)

(*****************************************************************************)
(* As mentioned earlier, certain functions may not be translated across      *)
(* their entire range. In the case of SEG this is because the function       *)
(* clauses 'SEG (SUC n) _ []' are left undefined. In the case of the         *)
(* function LOG this is given explicitly:                                    *)
(* |- !a x. 1 < a /\ 1 <= x ==>                                              *)
(*          (LOG a x = if x < a then 0 else 1 + LOG a (x DIV a)) : thm       *)
(*                                                                           *)
(* When translating such functions two types of theorem are required:        *)
(*      a) In the case of clausal functions, a proof that the limit avoids   *)
(*         the specific constructors and                                     *)
(*      b) A proof that the limit is conserved across recursive calls.       *)
(*         (In the case of clausal functions these calls use destructors)    *)
(*                                                                           *)
(* When non-clausal functions are given (a) is not required. If the function *)
(* is non-recursive then (b) is not required.                                *)
(*****************************************************************************)

(*---------------------------------------------------------------------------*)
(* A word on constructors....                                                *)
(*                                                                           *)
(* All constructors are given in POSITIVE form. Hence, in the example of SEG *)
(* we write ``?n. a = SUC n`` and not ``~(a = 0)``. This is because theorems *)
(* are automatically derived to convert limits to this form during           *)
(* translation.                                                              *)
(* Note: Existentials should be given in left-right fashion...               *)
(*     When a recursive call is made in a clausal function the function is   *)
(* translated to a form using DESTRUCTORS. These can be viewed, for the type *)
(* t, using the function call:                                               *)
(*        get_coding_theorem_precise ``:sexp`` t "destructors"               *)
(*                                                                           *)
(* Destructors can be modified using the call:                               *)
(*    set_destructors : thm list -> unit                                     *)
(* Set the destructors for a given type to the theorems given.               *)
(* These theorems should be of the form: |- D (C a b c...) = b ...           *)
(* Warning: In order to translate clausal functions using these destructors  *)
(* the destructors must be translated beforehand.                            *)
(*---------------------------------------------------------------------------*)

val destructors = 
    polytypicLib.get_coding_theorem_precise
                 ``:sexp`` ``:'a list`` "destructors";

(*****************************************************************************)
(* val destructors = |- (!h t. HD (h::t) = h) /\ !h t. TL (h::t) = t : thm   *)
(*                                                                           *)
(* The function SEG can be converted by provided theorems to state that:     *)
(*     a) The limit is correct (limit_correct),                              *)
(*     b) Recursing with the list intact preserves the limit                 *)
(*        (limit_recusive1)                                                  *)
(*     c) Recursing while the list is reducing preserves the limit           *)
(*        (limit_recursive2)                                                 *)
(*                                                                           *)
(* SEG is translated using the function:                                     *)
(*     translate_limit_function :                                            *)
(*         (term * string) list ->                                           *)
(*         (term * term list) list -> thm list -> thm -> thm                 *)
(* This acts like translate_conditional_function, except for each function   *)
(* constant it takes a list of terms of the form:                            *)
(*       ``\a b c d... . P a b c d...``.                                     *)
(* These are presented as limits to the resulting function. If the theorem   *)
(* |- !a b c d ... . P a b c d ... is given in the list then the limit is    *)
(* left in the definition, but is not required in either the propagation     *)
(* theorem or translation process.                                           *)
(*****************************************************************************)

val limit_correct = 
    prove(``a + b <= LENGTH c ==> ~((?n. a = SUC n) /\ (c = []))``,
    	  Cases_on `c` THEN RW_TAC arith_ss [listTheory.LENGTH]);

val limit_recursive1 = 
    prove(``(?d. a = SUC d) /\ (b = 0) /\ 
    	    (?x y. c = x :: y) /\ a + b <= LENGTH c ==> 
    	       PRE a + 0 <= LENGTH (TL c)``,
          Cases_on `c` THEN
	  RW_TAC arith_ss [listTheory.LENGTH,listTheory.TL,listTheory.NULL]);

val limit_recursive2 = 
    prove(``(?d. a = SUC d) /\ (?d. b = SUC d) /\ 
    	    (?x y. c = x :: y) /\ a + b <= LENGTH c ==> 
    		SUC (PRE a) + PRE b <= LENGTH (TL c)``,
	  Cases_on `c` THEN
	  RW_TAC arith_ss [listTheory.LENGTH,listTheory.TL,listTheory.NULL]);

val translated_seg = 
            translate_limit_function
                 [(``SEG``,"seg")]
	         [(``SEG``,[``\a b c. a + b <= LENGTH c``])]
	         [limit_correct,limit_recursive1,limit_recursive2]
	    (INST_TYPE [alpha |-> ``:num``] rich_listTheory.SEG);

(*****************************************************************************)
(* val translated_seg =                                                      *)
(*   |- seg arg'' arg' arg =                                                 *)
(*   ite                                                                     *)
(*     (andl                                                                 *)
(*        [natp arg'';                                                       *)
(*         andl                                                              *)
(*           [natp arg';                                                     *)
(*            andl                                                           *)
(*              [natp_list arg; not (less (len arg) (add arg'' arg'))]]])    *)
(*     (ite (zp arg'') nil                                                   *)
(*        (ite (zp arg')                                                     *)
(*           (cons (car arg)                                                 *)
(*              (seg (add arg'' (unary_minus (nat 1))) (nat 0) (cdr arg)))   *)
(*           (seg arg'' (add arg' (unary_minus (nat 1))) (cdr arg)))) nil    *)
(*                                                                           *)
(* The LOG function is translated in a similar manner to SEG. However, as it *)
(* is not clausal we do not need to demonstrate that the limit is correct.   *)
(* The theorem 'log_rec' is used to remove the second limit from the         *)
(* translation process whereas the theorem 'log_rec_ok' proves that the      *)
(* first limit is preserved across recursive calls.                          *)
(*****************************************************************************)

val log_compute = prove(``1 < a /\ 1 <= x ==> 
	     (LOG a x = if x < a then 0 else 1 + LOG a (x DIV a))``,
    RW_TAC std_ss [] THEN 
    FULL_SIMP_TAC std_ss [arithmeticTheory.NOT_LESS,logrootTheory.LOG_DIV] THEN
    MATCH_MP_TAC logrootTheory.LOG_UNIQUE THEN 
    RW_TAC arith_ss [arithmeticTheory.EXP]);

val log_rec = prove(``1 < a /\ 1 <= x ==> x DIV a < x``,
    REPEAT (Induct_on `a` THEN 
    RW_TAC arith_ss [arithmeticTheory.DIV_LT_X,arithmeticTheory.ADD1,
           arithmeticTheory.LEFT_ADD_DISTRIB]));

val log_rec_ok = prove(``~(a = 0) /\ ~(x < a) ==> (1 <= x DIV a)``,
       RW_TAC arith_ss [arithmeticTheory.NOT_LESS,arithmeticTheory.X_LE_DIV]);

val translated_log = 
    translate_limit_function 
	     [(``LOG``,"log")]
	     [(``LOG``,[``\a b. 1n < a /\ 1n <= b ``,
	      ``\a b. 1 < a /\ 1 <= b ==> b DIV a < b``])]
             [GEN_ALL log_rec,DECIDE ``1 < a ==> ~(a = 0n)``,log_rec_ok]
             log_compute;

(*****************************************************************************)
(* val translated_log =                                                      *)
(*   |- log a x =                                                            *)
(*   ite                                                                     *)
(*     (andl                                                                 *)
(*        [natp a;                                                           *)
(*         andl                                                              *)
(*           [natp x;                                                        *)
(*            andl                                                           *)
(*              [less (nat 1) a;                                             *)
(*               andl                                                        *)
(*                 [not (less x (nat 1));                                    *)
(*                  implies (andl [less (nat 1) a; not (less x (nat 1))])    *)
(*                    (less (acl2_floor x a) x)]]]])                         *)
(*     (ite (less x a) (nat 0) (add (nat 1) (log a (acl2_floor x a))))       *)
(*     (nat 0) : thm                                                         *)
(*****************************************************************************)

(*---------------------------------------------------------------------------*)
(* Instantiated higher order functions:                                      *)
(*---------------------------------------------------------------------------*)

(*****************************************************************************)
(* Instantiated Higher Order functions are translated in the same manner as  *)
(* normal functions. The translation procedure treats any closed term in     *)
(* the function definition as an instantiation, so the same technique works  *)
(* for higher-order and first-order functions.                               *)
(*                                                                           *)
(* The following example demonstrates this technique in translating the      *)
(* function determining whether all elements are non-zero:                   *)
(*****************************************************************************)

val translated_everyless = 
    translate_simple_function
              [(``EVERY``,"everyless")]
              (CONJ (ISPEC ``\a. 0n < a`` (CONJUNCT1 listTheory.EVERY_DEF))
		    (ISPEC ``\a. 0n < a`` (CONJUNCT2 listTheory.EVERY_DEF)));

(*****************************************************************************)
(* val translated_everyless =                                                *)
(*   |- everyless arg =                                                      *)
(*   ite (natp_list arg)                                                     *)
(*     (ite (atom arg) t                                                     *)
(*       (andl [(\a'. not (zp a')) (car arg); everyless (cdr arg)])) t : thm *)
(*****************************************************************************)


(*---------------------------------------------------------------------------*)
(* Polymorphic functions:                                                    *)
(*---------------------------------------------------------------------------*)

(*****************************************************************************)
(* Polymorphic functions are translated in exactly the same way as           *)
(* monomorphic functions, except that one extra theorem must be supplied.    *)
(* Hence for simple functions we use:                                        *)
(*     translate_simple_polymorphic_function :                               *)
(*               (term * string) list -> (term * thm) list -> thm -> thm     *)
(* The extra theorem supplied demonstrates that the function preserves map   *)
(* functions. For example, in the case of LENGTH this theorem is:            *)
(*****************************************************************************)

val LENGTH_MAP = prove(``!x f. LENGTH (MAP f x) = LENGTH x``,
    Induct THEN 
    FULL_SIMP_TAC std_ss
        [listTheory.LENGTH,listTheory.MAP,combinTheory.o_THM]);

(*****************************************************************************)
(* val LENGTH_MAP = |- !x f. LENGTH (MAP f x) = LENGTH x : thm               *)
(*                                                                           *)
(* The corresponding theorems for APPEND and REVERSE are:                    *)
(*****************************************************************************)

val APPEND_MAP = prove(``!x y f. MAP f x ++ MAP f y = MAP f (x ++ y)``,
    Induct THEN 
    RW_TAC std_ss [listTheory.MAP,listTheory.APPEND]);

local
open listTheory
val REVERSE_APP_MAP = prove(
    ``!x y f. REVERSE (MAP f x) ++ MAP f y = MAP f (REVERSE x ++ y)``,
    Induct THEN RW_TAC std_ss [MAP,REVERSE_DEF,APPEND,GSYM APPEND_ASSOC] THEN 
    RW_TAC std_ss [GSYM MAP]);
in
val REVERSE_MAP = REWRITE_RULE [APPEND_NIL,MAP] 
    (Q.SPECL [`x`,`[]`] REVERSE_APP_MAP);
end

(*****************************************************************************)
(* val APPEND_MAP = |- !x y f. MAP f x ++ MAP f y = MAP f (x ++ y) : thm     *)
(* val REVERSE_MAP = |- !f. REVERSE (MAP f x) = MAP f (REVERSE x) : thm      *)
(*                                                                           *)
(* All of these functions are translated in exactly the same manner as their *)
(* monomorphic brethren, except the map theorem is provided.                 *)
(*****************************************************************************)

val translated_length = 
    translate_simple_polymorphic_function
              [(``LENGTH``,"length_poly")]
              [(``LENGTH``,LENGTH_MAP)]
	      listTheory.LENGTH;

val translated_append = 
    translate_simple_polymorphic_function 
              [(``$++``,"append")]
              [(``$++``,APPEND_MAP)]
	      listTheory.APPEND;

val translated_reverse = 
    translate_simple_polymorphic_function
              [(``REVERSE``,"reverse")]
	      [(``REVERSE``,REVERSE_MAP)]
	      listTheory.REVERSE_DEF;

(*****************************************************************************)
(* val translated_length =                                                   *)
(*    |- length_poly arg =                                                   *)
(*    ite (listANY arg)                                                      *)
(*      (ite (atom arg) (nat 0) (add (len (cdr arg)) (nat 1))) (nat 0) : thm *)
(*                                                                           *)
(* val translated_append =                                                   *)
(*    |- append arg l2 =                                                     *)
(*    ite (andl [listANY arg; listANY l2])                                   *)
(*      (ite (atom arg) l2 (cons (car arg) (append (cdr arg) l2))) nil : thm *)
(*                                                                           *)
(* val translated_reverse =                                                  *)
(*    |- reverse arg =                                                       *)
(*    ite (listANY arg)                                                      *)
(*      (ite (atom arg) nil                                                  *)
(*         (append (reverse (cdr arg)) (cons (car arg) nil))) nil : thm      *)
(*                                                                           *)
(* The propagation theorems have the same form as the monomorphic propgation *)
(* theorems. However, they take a general function to recognise the type     *)
(* variable:                                                                 *)
(*****************************************************************************)

val prop_reverse = fetch "-" "prop_reverse";

(*****************************************************************************)
(* val prop_reverse =                                                        *)
(*        |- list encodea (REVERSE arg) = reverse (list encodea arg) : thm   *)
(*                                                                           *)
(* Things get a little bit more complicated when limits are involved, as we  *)
(* must also provide a theorem that demonstrates that the limit, as well as  *)
(* the function, preserves the map. In the case of SEG, this requires the    *)
(* theorem:                                                                  *)
(*****************************************************************************)

val LIMIT_MAP = prove(
    ``!c a b f. a + b <= LENGTH c ==> a + b <= LENGTH (MAP f c)``,
     REWRITE_TAC [LENGTH_MAP]);

(*****************************************************************************)
(* val LIMIT_MAP =                                                           *)
(*      |- !c a b f. a + b <= LENGTH c ==> a + b <= LENGTH (MAP f c) : thm   *)
(*                                                                           *)
(* We still need the theorem for SEG of course:                              *)
(*****************************************************************************)

val SEG_MAP = prove(
    ``!c a b. a + b <= LENGTH c ==> (SEG a b (MAP f c) = MAP f (SEG a b c))``,
    Induct THEN1 
    RW_TAC std_ss [listTheory.LENGTH,listTheory.MAP,rich_listTheory.SEG] THEN
    Induct_on `a` THEN Induct_on `b` THEN 
    RW_TAC std_ss [listTheory.LENGTH,listTheory.MAP,rich_listTheory.SEG] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN DECIDE_TAC);

(*****************************************************************************)
(* val SEG_MAP =                                                             *)
(*   |- !c a b. a + b <= LENGTH c ==>                                        *)
(*                       (SEG a b (MAP f c) = MAP f (SEG a b c)) : thm       *)
(*                                                                           *)
(* SEG is then converted as follows:                                         *)
(*****************************************************************************)

val translated_seg = 
    translate_limit_polymorphic_function
             [(``SEG``,"seg")]
             [(``SEG``,SEG_MAP)]
	     [(``SEG``,[``\a b c. a + b <= LENGTH c``])]
	     [LIMIT_MAP,limit_correct,limit_recursive1,limit_recursive2]
	     rich_listTheory.SEG;

(*****************************************************************************)
(* val translated_seg =                                                      *)
(*   |- seg arg'' arg' arg =                                                 *)
(*    ite                                                                    *)
(*      (andl                                                                *)
(*         [natp arg'';                                                      *)
(*          andl                                                             *)
(*            [natp arg';                                                    *)
(*             andl [listANY arg; not (less (len arg) (add arg'' arg'))]]])  *)
(*      (ite (zp arg'') nil                                                  *)
(*         (ite (zp arg')                                                    *)
(*            (cons (car arg)                                                *)
(*               (seg (add arg'' (unary_minus (nat 1))) (nat 0) (cdr arg)))  *)
(*            (seg arg'' (add arg' (unary_minus (nat 1))) (cdr arg)))) nil   *)
(*****************************************************************************)

(*---------------------------------------------------------------------------*)
(* User defined datatypes                                                    *)
(*---------------------------------------------------------------------------*)

(*****************************************************************************)
(* The polymorphic type 'a Tree is defined as follows:                       *)
(*          `Tree = TLeaf of 'a | TBranch of Tree => Tree`;                  *)
(* Before functions can be translated, support functions for the type must   *)
(* be created. To do this, the following function is used:                   *)
(*     initialise_type : hol_type -> unit                                    *)
(*****************************************************************************)

val _ = initialise_type ``:'a Tree``;

(*****************************************************************************)
(* This produces the following functions:                                    *)
(*     map, all, encode, decode, detect and fix                              *)
(* The following theorems:                                                   *)
(*     encode_detect_all : |- detect f o encode g = all (f o g)              *)
(*     encode_map_encode : |- map f o encode g = encode (f o g)              *)
(*     encode_decode_map : |- decode f o encode g = map (f o g)              *)
(*     decode_encode_fix : |- encode f o decode g = fix (f o g)              *)
(*                                                                           *)
(*     map_id : |- map I = I                                                 *)
(*     all_id : |- all (K T) = K T                                           *)
(*     fix_id : |- (!x. p x ==> f x = x) ==> !x. detect p x ==> fix f x = x  *)
(*                                                                           *)
(*     general_detect : |- !x. detect p x ==> detect (K T) x                 *)
(*                                                                           *)
(* And the following rewrites:                                               *)
(*     Constructor encoding : encode encodea (TLeaf a) = ...                 *)
(*     Decode then encode   : encode encodea (decode decodea x) = x          *)
(*     Destructor theorems  : All destructors are given as follows...        *)
(*          (FST o ... o SND o decode_pair o encode_type) (C a b c ...)      *)
(*                                                                           *)
(* Destructors can be specified exactly using 'set_destructors' and a        *)
(* COMPLETE list of destructor functions for a type's constructors. However, *)
(* ALL destructors should be translated before functions using them are      *)
(* translated.                                                               *)
(*                                                                           *)
(* We define the function 'FLATTEN_TREE' to convert trees to a lists, in a   *)
(* depth-first order, as follows:                                            *)
(*     |- (FLATTEN_TREE (TLeaf a) = [a]) /\                                  *)
(*        (FLATTEN_TREE (TBranch t1 t2) =                                    *)
(*                      FLATTEN_TREE t1 ++ FLATTEN_TREE t2) : thm            *)
(*                                                                           *)
(* As this function is polymorphic, we must prove a map theorem. However,    *)
(* the map function was created automatically, so we must find it from the   *)
(* database. This is done using the database functions from polytypicLib:    *)
(*     polytypicLib.get_source_function_def ``:'a Tree`` "map"               *)
(*****************************************************************************)

val tree_map_def = polytypicLib.get_source_function_def ``:'a Tree`` "map";

(*****************************************************************************)
(* val tree_map_def =                                                        *)
(*     |- (!mapa a. map mapa (TLeaf a) = TLeaf (mapa a)) /\                  *)
(*        (!mapa a b. map mapa (TBranch a b) =                               *)
(*                           TBranch (map mapa a) (map mapa b)) : thm        *)
(*                                                                           *)
(* We use this theorem to derive the map theorem:                            *)
(*****************************************************************************)

val FLATTEN_TREE_MAP = prove(
    ``!x. FLATTEN_TREE (map f x) = MAP f (FLATTEN_TREE x)``,
    Induct THEN 
    RW_TAC std_ss [testFunctionsTheory.FLATTEN_TREE_def,tree_map_def,
                   listTheory.MAP,listTheory.MAP_APPEND]);

(*****************************************************************************)
(* val FLATTEN_TREE_MAP =                                                    *)
(*     |- !x. FLATTEN_TREE (map f x) = MAP f (FLATTEN_TREE x) : thm          *)
(*                                                                           *)
(* We can then translate the function as follows:                            *)
(*****************************************************************************)

val translated_flatten = 
    translate_simple_polymorphic_function 
             [(``FLATTEN_TREE``,"flatten_tree")]
	     [(``FLATTEN_TREE``,FLATTEN_TREE_MAP)]
	     testFunctionsTheory.FLATTEN_TREE_def;

(*****************************************************************************)
(* val translated_flatten =                                                  *)
(*    |- flatten_tree arg =                                                  *)
(*    ite (TreeANY arg)                                                      *)
(*      (ite (zp (car arg)) (cons (cdr arg) nil)                             *)
(*         (append (flatten_tree (car (cdr arg)))                            *)
(*            (flatten_tree (cdr (cdr arg))))) nil : thm                     *)
(*                                                                           *)
(* Conditional and limit functions are translated in exactly the same manner.*)
(*****************************************************************************)

(*---------------------------------------------------------------------------*)
(* Finite Cartesian products:                                                *)
(*---------------------------------------------------------------------------*)

(*****************************************************************************)
(* Functions using finite cartesian products are translated in a different   *)
(* manner to standard functions. First, a term is derived which *should* be  *)
(* the translation of the function. Then, this term is proven termination    *)
(* and proven to be a valid translation. This order is necessary as the      *)
(* cardinality of the type variables used must be replaced with natural      *)
(* number arguments.                                                         *)
(*                                                                           *)
(* An example of this procedure is the translation of the function word_div: *)
(*     |- !v w. v // w = n2w (w2n v DIV w2n w) : thm                         *)
(* This function is only valid for ~(w = 0w), so we translate as a limit     *)
(* function. The FCP functions do not operate on mutually recursive          *)
(* definitions, as such the functions used are as follows:                   *)
(*     val translate_simple_fcp_function                                     *)
(*        : string -> thm -> thm                                             *)
(*     val translate_conditional_fcp_function                                *)
(*     	  : string -> thm list -> thm -> thm                                 *)
(*     val translate_limit_fcp_function                                      *)
(*     	  : string -> term list -> thm list -> thm -> thm                    *)
(* The above functions only work on non-recursive functions, recursive       *)
(* functions are covered later.                                              *)
(*****************************************************************************)

val translated_worddiv = 
    translate_limit_fcp_function
	     "WORDDIV"
	     [``\a b. ~(b = 0w)``]
             [wordsTheory.w2n_eq_0]
	     wordsTheory.word_div_def;

(*****************************************************************************)
(* val translated_worddiv =                                                  *)
(*   |- !v w ABSa.                                                           *)
(*     WORDDIV v w ABSa =                                                    *)
(*     ite ( ....                                                            *)
(*              not (equal w (translated_extend (int 0) ABSa))]])            *)
(*       (translated_extend                                                  *)
(*          (acl2_floor (translated_i2n v ABSa) (translated_i2n w ABSa))     *)
(*          ABSa) (translated_extend (int 0) ABSa) : thm                     *)
(*                                                                           *)
(* In the trace, the steps of the translation are described as follows:      *)
(*     Unabstracted conversion :                                             *)
(*        An attempt to translate the definition, aborting upon reaching the *)
(*        the term ``nat (dimindex (:'a))``                                  *)
(*     Recusion points :                                                     *)
(*        Terms that cannot be encoded, as they are recursive calls to the   *)
(*        function itself.                                                   *)
(*     Terminals :                                                           *)
(*        Terms that involve the cardinality of a type variable, and must be *)
(*        replaced with a natural number argument.                           *)
(*     Abstracted definition :                                               *)
(*        The resulting definition. This must be proved terminating then     *)
(*        proved to match the HOL function.                                  *)
(*                                                                           *)
(*****************************************************************************)

(*---------------------------------------------------------------------------*)
(* Recognizers for finite cartesian products:                                *)
(*---------------------------------------------------------------------------*)

(*****************************************************************************)
(* In the translation of word_div the recognition function, word_detect, is  *)
(* expanded out and translated. Instead, a more concise definition can be    *)
(* created by flattening the definition. As with normal types, the function  *)
(*    flatten_fcp_recognizers :                                              *)
(*    (hol_type -> string) -> hol_type -> thm list                           *)
(* is used.                                                                  *)
(*****************************************************************************)

val wordp_def = flatten_fcp_recognizers (K "wordp") ``:'a word``;

(*****************************************************************************)
(* val wordp_def =                                                           *)
(*   [|- !x ABSa.                                                            *)
(*     wordp x ABSa =                                                        *)
(*     andl                                                                  *)
(*       [integerp x;                                                        *)
(*        andl                                                               *)
(*          [less x                                                          *)
(*             (acl2_expt (int 2)                                            *)
(*                (nfix (add ABSa (unary_minus (nat 1)))));                  *)
(*           not                                                             *)
(*             (less x                                                       *)
(*                (unary_minus                                               *)
(*                   (acl2_expt (int 2)                                      *)
(*                      (nfix (add ABSa (unary_minus (nat 1)))))))]]] : thm  *)
(*                                                                           *)
(* This functions in the same way as the flattening of normal types, except  *)
(* an extra argument to represent the cardinality of the type is added. This *)
(* gives the following propagation theorem:                                  *)
(*****************************************************************************)

val propagate_wordp = fetch "-" "prop_wordp";

(*****************************************************************************)
(* val propagate_wordp =                                                     *)
(*     |- bool (word_detect (:'a) x) = wordp x (nat (dimindex (:'a))) : thm  *)
(*****************************************************************************)

(*---------------------------------------------------------------------------*)
(* Recursive functions over finite cartesian products:                       *)
(*---------------------------------------------------------------------------*)

(*****************************************************************************)
(* When converting a recursive FCP function two tactics must also be         *)
(* supplied: one to prove that the new definition terminates, and another to *)
(* link the definition to the HOL definition. Additionally, a list of        *)
(* rewrite theorems is supplied that are used to rewrite the definition      *)
(* prior to the use of tDefine.                                              *)
(*                                                                           *)
(* Here, we are trying to translate the function 'addn' that adds the ith    *)
(* element of a list of arrays:                                              *)
(*****************************************************************************)

val addn_def = 
    Define `(addn i [] = 0n) /\ (addn i (y::ys) = y %% i + addn i ys)`;

(*****************************************************************************)
(* Before this definition is translated we must translate the types involved.*)
(* That is: ``:num ** 'b`` and ``:(num ** 'b) list``:                        *)
(*****************************************************************************)

val numarrayp_def =
    flatten_fcp_recognizers (K "numarrayp") ``:num ** 'b``;
val numarraylistp_def = 
    flatten_fcp_recognizers (K "numarraylistp") ``:(num ** 'b) list``;

(*****************************************************************************)
(* The first goal we are given to solve are as follows:                      *)
(* ?R. WF R /\                                                               *)
(*     !ABSa arg x.                                                          *)
(*     ~(andl [natp x; andl [numarraylistp arg ABSa; less x ABSa]] = nil) /\ *)
(*     (atom arg = nil) ==>                                                  *)
(*            R (x,cdr arg,ABSa) (x,arg,ABSa)                                *)
(* This is solved using 'ENCODE_WF_REL_TAC'. This acts like 'WF_REL_TAC'     *)
(* except the relation is encoded to s-expressions.                          *)
(*****************************************************************************) 

local
open translateTheory sexpTheory hol_defaxiomsTheory;
in
val tactic1 = 
    ENCODE_WF_REL_TAC `measure (LENGTH o FST o SND)` THEN
    FULL_SIMP_TAC std_ss [ANDL_REWRITE,TRUTH_REWRITES] THEN
    Cases_on `arg` THEN 
    FULL_SIMP_TAC std_ss [atom_def,car_def,cdr_def,consp_def,not_def,
             TRUTH_REWRITES,ite_def,sexp_to_list_def,listTheory.LENGTH]
end

(*****************************************************************************)
(* The second goal is harder to prove:                                       *)
(* |- !x arg.                                                                *)
(*          x < dimindex (:'a) ==>                                           *)
(*          (nat (addn x arg) =                                              *)
(*           ADDN (nat x)                                                    *)
(*           (list (fcp_encode nat (:'a)) arg) (nat (dimindex (:'a)))) : thm *)
(* Here, the tactic is supplied with the definition and the propagation      *)
(* theorem for the unabstracted definition. We then define the second tactic *)
(* as follows:                                                               *)
(*****************************************************************************)

local
open translateTheory sexpTheory hol_defaxiomsTheory
open extendTranslateTheory 
in
fun tactic2 definition prop_thm = 
    Induct_on `arg` THEN 
    ONCE_REWRITE_TAC [definition] THEN 
    RW_TAC std_ss [NATP_NAT,ANDL_REWRITE,TRUTH_REWRITES,ite_def,addn_def,
          list_def,atom_def,not_def,GSYM (fetch "-" "prop_numarraylistp"),
          listp_def,REWRITE_RULE [combinTheory.o_THM,FUN_EQ_THM] ENCDETALL_FCP,
          ENCDETALL_NAT,ALLID_FCP,combinTheory.K_o_THM,
          REWRITE_RULE [combinTheory.o_THM,FUN_EQ_THM] ENCDETALL_LIST,
          ENCDETALL_FCP,ALLID_LIST,GSYM NAT_THMS] THEN
    FULL_SIMP_TAC std_ss [arithmeticTheory.GREATER_DEF,NAT_THMS,cdr_def,car_def,
          GSYM LIST_THMS,consp_def,TRUTH_REWRITES] THEN
    METIS_TAC [FCP_INDEX]
end;

(*****************************************************************************)
(* For general types, the functions:                                         *)
(*     FULL_ENCODE_DECODE_THM, FULL_ENCODE_DECODE_MAP_THM etc...             *)
(* from encodeLib may be very useful in proving such theorems.               *)
(*                                                                           *)
(* Once we have the two tactics we can translate the final definition. In    *)
(* the following function call we translate 'addn' under the limit ensuring  *)
(* i is within the cardinality of :'a. No extra theorems (third argument) or *)
(* rewrites (fifth argument) are required.                                   *)
(*****************************************************************************)

val translated_addn = 
    translate_recursive_fcp_function 
              "ADDN"
              [``\i y. i < dimindex (:'a)``]
              [] addn_def []
              tactic1 tactic2;

(*****************************************************************************)
(* val translated_addn =                                                     *)
(*   |- !i arg ABSa.                                                         *)
(*     ADDN i arg ABSa =                                                     *)
(*     ite (andl [natp i; andl [numarraylistp arg ABSa; less i ABSa]])       *)
(*       (ite (atom arg) (nat 0)                                             *) 
(*          (add (car (acl2_nthcdr i (car arg))) (ADDN i (cdr arg) ABSa)))   *)
(*       (nat 0) : thm                                                       *)
(*****************************************************************************)
