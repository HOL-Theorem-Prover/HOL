(****************************************************************************)
(* FILE          : clausal_form.sml                                         *)
(* DESCRIPTION   : Functions for putting a formula into clausal form.       *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 13th May 1991                                            *)
(*                                                                          *)
(* TRANSLATED BY : R.J.Boulton                                              *)
(* DATE          : 3rd October 1995                                         *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 3rd October 1995                                         *)
(****************************************************************************)

structure BoyerMooreClausalForm =
struct

local

open HolKernel Parse basicHol90Lib Psyntax BoyerMooreSupport;
infix THEN THENC ORELSEC;

fun failwith function =
   raise HOL_ERR {origin_structure = "BoyerMooreClausalForm",
                  origin_function = function,
                  message = ""};

in

(*==========================================================================*)
(* Theorems for normalizing Boolean terms                                   *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* EQ_EXPAND = |- (x = y) = ((~x \/ y) /\ (~y \/ x))                        *)
(*--------------------------------------------------------------------------*)

val EQ_EXPAND =
   prove
      ((--`(x = y) = ((~x \/ y) /\ (~y \/ x))`--),
       BOOL_CASES_TAC (--`x:bool`--) THEN
       BOOL_CASES_TAC (--`y:bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* IMP_EXPAND = |- (x ==> y) = (~x \/ y)                                    *)
(*--------------------------------------------------------------------------*)

val IMP_EXPAND = SPECL [(--`x:bool`--),(--`y:bool`--)] IMP_DISJ_THM;

(*--------------------------------------------------------------------------*)
(* COND_EXPAND = |- (x => y | z) = ((~x \/ y) /\ (x \/ z))                  *)
(*--------------------------------------------------------------------------*)

val COND_EXPAND =
   prove
      ((--`(x => y | z) = ((~x \/ y) /\ (x \/ z))`--),
       BOOL_CASES_TAC (--`x:bool`--) THEN
       BOOL_CASES_TAC (--`y:bool`--) THEN
       BOOL_CASES_TAC (--`z:bool`--) THEN
       REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* NOT_NOT_NORM = |- ~~x = x                                                *)
(*--------------------------------------------------------------------------*)

val NOT_NOT_NORM = SPEC (--`x:bool`--) (CONJUNCT1 NOT_CLAUSES);

(*--------------------------------------------------------------------------*)
(* NOT_CONJ_NORM = |- ~(x /\ y) = (~x \/ ~y)                                *)
(*--------------------------------------------------------------------------*)

val NOT_CONJ_NORM =
   CONJUNCT1 (SPECL [(--`x:bool`--),(--`y:bool`--)] DE_MORGAN_THM);

(*--------------------------------------------------------------------------*)
(* NOT_DISJ_NORM = |- ~(x \/ y) = (~x /\ ~y)                                *)
(*--------------------------------------------------------------------------*)

val NOT_DISJ_NORM =
   CONJUNCT2 (SPECL [(--`x:bool`--),(--`y:bool`--)] DE_MORGAN_THM);

(*--------------------------------------------------------------------------*)
(* LEFT_DIST_NORM = |- x \/ (y /\ z) = (x \/ y) /\ (x \/ z)                 *)
(*--------------------------------------------------------------------------*)

val LEFT_DIST_NORM =
   SPECL [(--`x:bool`--),(--`y:bool`--),(--`z:bool`--)] LEFT_OR_OVER_AND;

(*--------------------------------------------------------------------------*)
(* RIGHT_DIST_NORM = |- (x /\ y) \/ z = (x \/ z) /\ (y \/ z)                *)
(*--------------------------------------------------------------------------*)

val RIGHT_DIST_NORM =
   SPECL [(--`z:bool`--),(--`x:bool`--),(--`y:bool`--)] RIGHT_OR_OVER_AND;

(*--------------------------------------------------------------------------*)
(* CONJ_ASSOC_NORM = |- (x /\ y) /\ z = x /\ (y /\ z)                       *)
(*--------------------------------------------------------------------------*)

val CONJ_ASSOC_NORM =
   SYM (SPECL [(--`x:bool`--),(--`y:bool`--),(--`z:bool`--)] CONJ_ASSOC);

(*--------------------------------------------------------------------------*)
(* DISJ_ASSOC_NORM = |- (x \/ y) \/ z = x \/ (y \/ z)                       *)
(*--------------------------------------------------------------------------*)

val DISJ_ASSOC_NORM =
   SYM (SPECL [(--`x:bool`--),(--`y:bool`--),(--`z:bool`--)] DISJ_ASSOC);

(*==========================================================================*)
(* Conversions for rewriting Boolean terms                                  *)
(*==========================================================================*)

val COND_EXPAND_CONV = REWR_CONV COND_EXPAND;
val CONJ_ASSOC_NORM_CONV = REWR_CONV CONJ_ASSOC_NORM;
val DISJ_ASSOC_NORM_CONV = REWR_CONV DISJ_ASSOC_NORM;
val EQ_EXPAND_CONV = REWR_CONV EQ_EXPAND;
val IMP_EXPAND_CONV = REWR_CONV IMP_EXPAND;
val LEFT_DIST_NORM_CONV = REWR_CONV LEFT_DIST_NORM;
val NOT_CONJ_NORM_CONV = REWR_CONV NOT_CONJ_NORM;
val NOT_DISJ_NORM_CONV = REWR_CONV NOT_DISJ_NORM;
val NOT_NOT_NORM_CONV = REWR_CONV NOT_NOT_NORM;
val RIGHT_DIST_NORM_CONV = REWR_CONV RIGHT_DIST_NORM;

(*--------------------------------------------------------------------------*)
(* NOT_CONV : conv                                                          *)
(*                                                                          *)
(*    |- !t. ~~t = t                                                        *)
(*    |- ~T = F                                                             *)
(*    |- ~F = T                                                             *)
(*--------------------------------------------------------------------------*)

val NOT_CONV =
   let val (th1,th2,th3) =
          case (CONJUNCTS NOT_CLAUSES)
          of [th1,th2,th3] => (th1,th2,th3)
           | _ => raise Bind
   in  fn tm =>
          let val arg = dest_neg tm
          in  if (is_T arg) then th2
              else if (is_F arg) then th3
              else SPEC (dest_neg arg) th1
          end
          handle HOL_ERR _ => failwith "NOT_CONV"
   end;

(*--------------------------------------------------------------------------*)
(* AND_CONV : conv                                                          *)
(*                                                                          *)
(*    |- T /\ t = t                                                         *)
(*    |- t /\ T = t                                                         *)
(*    |- F /\ t = F                                                         *)
(*    |- t /\ F = F                                                         *)
(*    |- t /\ t = t                                                         *)
(*--------------------------------------------------------------------------*)

val AND_CONV =
   let val (th1,th2,th3,th4,th5) =
          case (map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES)))
          of [th1,th2,th3,th4,th5] => (th1,th2,th3,th4,th5)
           | _ => raise Bind
   in  fn tm =>
          let val (arg1,arg2) = dest_conj tm
          in  if (is_T arg1) then SPEC arg2 th1
              else if (is_T arg2) then SPEC arg1 th2
              else if (is_F arg1) then SPEC arg2 th3
              else if (is_F arg2) then SPEC arg1 th4
              else if (arg1 = arg2) then SPEC arg1 th5
              else failwith ""
          end
          handle HOL_ERR _ => failwith "AND_CONV"
   end;

(*--------------------------------------------------------------------------*)
(* OR_CONV : conv                                                           *)
(*                                                                          *)
(*    |- T \/ t = T                                                         *)
(*    |- t \/ T = T                                                         *)
(*    |- F \/ t = t                                                         *)
(*    |- t \/ F = t                                                         *)
(*    |- t \/ t = t                                                         *)
(*--------------------------------------------------------------------------*)

val OR_CONV =
   let val (th1,th2,th3,th4,th5) =
          case (map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES)))
          of [th1,th2,th3,th4,th5] => (th1,th2,th3,th4,th5)
           | _ => raise Bind
   in  fn tm =>
          let val (arg1,arg2) = dest_disj tm
          in  if (is_T arg1) then SPEC arg2 th1
              else if (is_T arg2) then SPEC arg1 th2
              else if (is_F arg1) then SPEC arg2 th3
              else if (is_F arg2) then SPEC arg1 th4
              else if (arg1 = arg2) then SPEC arg1 th5
              else failwith ""
          end
          handle HOL_ERR _ => failwith "OR_CONV"
   end;

(*==========================================================================*)
(* Conversions for obtaining `clausal' form                                 *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* EQ_IMP_COND_ELIM_CONV : (term -> bool) -> conv                           *)
(*                                                                          *)
(* Eliminates Boolean equalities, Boolean conditionals, and implications    *)
(* from terms consisting of =,==>,COND,/\,\/,~ and atoms. The atoms are     *)
(* specified by the predicate that the conversion takes as its first        *)
(* argument.                                                                *)
(*--------------------------------------------------------------------------*)

fun EQ_IMP_COND_ELIM_CONV is_atom tm =
   (if (is_atom tm) then ALL_CONV tm
    else if (is_neg tm) then (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom)) tm
    else if (is_eq tm) then
       ((RATOR_CONV (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom))) THENC
        (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom)) THENC
        EQ_EXPAND_CONV) tm
    else if (is_imp tm) then
       ((RATOR_CONV (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom))) THENC
        (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom)) THENC
        IMP_EXPAND_CONV) tm
    else if (is_cond tm) then
       ((RATOR_CONV
            (RATOR_CONV (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom)))) THENC
        (RATOR_CONV (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom))) THENC
        (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom)) THENC
        COND_EXPAND_CONV) tm
    else ((RATOR_CONV (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom))) THENC
          (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom))) tm)
   handle HOL_ERR _ => failwith "EQ_IMP_COND_ELIM_CONV";

(*--------------------------------------------------------------------------*)
(* MOVE_NOT_DOWN_CONV : (term -> bool) -> conv -> conv                      *)
(*                                                                          *)
(* Moves negations down through a term consisting of /\,\/,~ and atoms. The *)
(* atoms are specified by a predicate (first argument). When a negation has *)
(* reached an atom, the conversion `conv' (second argument) is applied to   *)
(* the negation of the atom. `conv' is also applied to any non-negated      *)
(* atoms encountered. T and F are eliminated.                               *)
(*--------------------------------------------------------------------------*)

fun MOVE_NOT_DOWN_CONV is_atom conv tm =
   (if (is_atom tm) then (conv tm)
    else if (is_neg tm) then
       let val tm' = rand tm
       in  if (is_atom tm') then ((conv THENC (TRY_CONV NOT_CONV)) tm)
           else if (is_neg tm') then (NOT_NOT_NORM_CONV THENC
                                      (MOVE_NOT_DOWN_CONV is_atom conv)) tm
           else if (is_conj tm') then
              (NOT_CONJ_NORM_CONV THENC
               (RATOR_CONV (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv))) THENC
               (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv)) THENC
               (TRY_CONV AND_CONV)) tm
           else if (is_disj tm') then
              (NOT_DISJ_NORM_CONV THENC
               (RATOR_CONV (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv))) THENC
               (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv)) THENC
               (TRY_CONV OR_CONV)) tm
           else failwith ""
       end
    else if (is_conj tm) then
       ((RATOR_CONV (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv))) THENC
        (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv)) THENC
        (TRY_CONV AND_CONV)) tm
    else if (is_disj tm) then
       ((RATOR_CONV (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv))) THENC
        (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv)) THENC
        (TRY_CONV OR_CONV)) tm
    else failwith "")
   handle HOL_ERR _ => failwith "MOVE_NOT_DOWN_CONV";

(*--------------------------------------------------------------------------*)
(* CONJ_LINEAR_CONV : conv                                                  *)
(*                                                                          *)
(* Linearizes conjuncts using the following conversion applied recursively: *)
(*                                                                          *)
(*    (--`(x /\ y) /\ z`--)                                                 *)
(*    ================================                                      *)
(*    |- (x /\ y) /\ z = x /\ (y /\ z)                                      *)
(*--------------------------------------------------------------------------*)

fun CONJ_LINEAR_CONV tm =
   (if ((is_conj tm) andalso (is_conj (rand (rator tm))))
    then (CONJ_ASSOC_NORM_CONV THENC
          (RAND_CONV (TRY_CONV CONJ_LINEAR_CONV)) THENC
          (TRY_CONV CONJ_LINEAR_CONV)) tm
    else failwith "")
   handle HOL_ERR _ => failwith "CONJ_LINEAR_CONV";

(*--------------------------------------------------------------------------*)
(* CONJ_NORM_FORM_CONV : conv                                               *)
(*                                                                          *)
(* Puts a term involving /\ and \/ into conjunctive normal form. Anything   *)
(* other than /\ and \/ is taken to be an atom and is not processed.        *)
(*                                                                          *)
(* The conjunction returned is linear, i.e. the conjunctions are associated *)
(* to the right. Each conjunct is a linear disjunction.                     *)
(*--------------------------------------------------------------------------*)

fun CONJ_NORM_FORM_CONV tm =
   (if (is_disj tm) then
       (if (is_conj (rand (rator tm))) then
           ((RATOR_CONV
                (RAND_CONV ((RATOR_CONV (RAND_CONV CONJ_NORM_FORM_CONV)) THENC
                            (RAND_CONV CONJ_NORM_FORM_CONV)))) THENC
            (RAND_CONV CONJ_NORM_FORM_CONV) THENC
            RIGHT_DIST_NORM_CONV THENC
            (RATOR_CONV (RAND_CONV CONJ_NORM_FORM_CONV)) THENC
            (RAND_CONV CONJ_NORM_FORM_CONV) THENC
            (TRY_CONV CONJ_LINEAR_CONV)) tm
        else if (is_conj (rand tm)) then
           ((RATOR_CONV (RAND_CONV CONJ_NORM_FORM_CONV)) THENC
            (RAND_CONV ((RATOR_CONV (RAND_CONV CONJ_NORM_FORM_CONV)) THENC
                        (RAND_CONV CONJ_NORM_FORM_CONV))) THENC
            LEFT_DIST_NORM_CONV THENC
            (RATOR_CONV (RAND_CONV CONJ_NORM_FORM_CONV)) THENC
            (RAND_CONV CONJ_NORM_FORM_CONV) THENC
            (TRY_CONV CONJ_LINEAR_CONV)) tm
        else if (is_disj (rand (rator tm))) then
           (DISJ_ASSOC_NORM_CONV THENC CONJ_NORM_FORM_CONV) tm
        else let val th = RAND_CONV CONJ_NORM_FORM_CONV tm
                 val tm' = rhs (concl th)
             in  if (is_conj (rand tm'))
                 then TRANS th (CONJ_NORM_FORM_CONV tm')
                 else th
             end)
    else if (is_conj tm) then
       ((RATOR_CONV (RAND_CONV CONJ_NORM_FORM_CONV)) THENC
        (RAND_CONV CONJ_NORM_FORM_CONV) THENC
        (TRY_CONV CONJ_LINEAR_CONV)) tm
    else ALL_CONV tm)
   handle HOL_ERR _ => failwith "CONJ_NORM_FORM_CONV";

(*--------------------------------------------------------------------------*)
(* has_boolean_args_and_result : term -> bool                               *)
(*                                                                          *)
(* Yields true if and only if the term is of type (==`:bool`==), and if it  *)
(* is a function application, all the arguments are of type (==`:bool`==).  *)
(*--------------------------------------------------------------------------*)

fun has_boolean_args_and_result tm =
   let val args = #2 (strip_comb tm)
       val types = (type_of tm)::(map type_of args)
   in  null (subtract (mk_set types) [(==`:bool`==)])
   end
   handle HOL_ERR _ => (type_of tm = (==`:bool`==));

(*--------------------------------------------------------------------------*)
(* CLAUSAL_FORM_CONV : conv                                                 *)
(*                                                                          *)
(* Puts into clausal form terms consisting of =,==>,COND,/\,\/,~ and atoms. *)
(*--------------------------------------------------------------------------*)

fun CLAUSAL_FORM_CONV tm =
   let fun is_atom tm = not (has_boolean_args_and_result tm) orelse
                        (is_var tm) orelse (is_const tm)
   in  ((EQ_IMP_COND_ELIM_CONV is_atom) THENC
        (MOVE_NOT_DOWN_CONV is_atom ALL_CONV) THENC
        CONJ_NORM_FORM_CONV) tm
   end
   handle HOL_ERR _ => failwith "CLAUSAL_FORM_CONV";

end;

end; (* BoyerMooreClausalForm *)
