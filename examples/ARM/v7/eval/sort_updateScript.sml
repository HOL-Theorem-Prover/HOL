(* ------------------------------------------------------------------------ *)
(*  Theorems for sorting function updates (=+)                              *)
(* ------------------------------------------------------------------------ *)

open HolKernel boolLib bossLib Parse;

val _ = new_theory "sort_update";

(* ------------------------------------------------------------------------ *)

val _ = computeLib.auto_import_definitions := false;

val _ = set_fixity "=+>" (Infix(NONASSOC, 320));
val _ = set_fixity "=+<" (Infix(NONASSOC, 320));

val Ua_def = xDefine "Ua" `$=+> = $=+`;
val Ub_def = xDefine "Ub" `$=+< = $=+`;

val UPDATE_SORT_RULE1 = Q.store_thm("UPDATE_SORT_RULE1",
  `!R m a b d e. (!x y. R x y ==> ~(x = y)) ==>
     ((a =+> e) ((b =+> d) m) =
         if R a b then
           (b =+< d) ((a =+> e) m)
         else
           (a =+< e) ((b =+> d) m))`,
  METIS_TAC [Ua_def,Ub_def,combinTheory.UPDATE_COMMUTES]);

val UPDATE_SORT_RULE2 = Q.store_thm("UPDATE_SORT_RULE2",
  `!R m a b d e. (!x y. R x y ==> ~(x = y)) ==>
     ((a =+> e) ((b =+< d) m) =
         if R a b then
           (b =+< d) ((a =+> e) m)
         else
           (a =+< e) ((b =+< d) m))`,
  METIS_TAC [Ua_def,Ub_def,combinTheory.UPDATE_COMMUTES]);

val UPDATE_EQ_RULE = Q.store_thm("UPDATE_EQ_RULE",
  `((a =+< e) ((a =+> d) m) = (a =+> e) m) /\
   ((a =+< e) ((a =+< d) m) = (a =+< e) m) /\
   ((a =+> e) ((a =+> d) m) = (a =+> e) m)`,
  REWRITE_TAC [Ua_def,Ub_def,combinTheory.UPDATE_EQ]);

val SORT_WORD_THM = save_thm("SORT_WORD_THM",
let
  val WORD_GT_NEQ = wordsLib.WORD_DECIDE ``!x y:'a word. x > y ==> ~(x = y)``
  val spec = BETA_RULE o Drule.ISPECL
              [wordsSyntax.word_gt_tm,``m:'a word -> 'b``,
               ``n2w a:'a word``,``n2w b:'a word``]
  val thm1 = MATCH_MP (spec UPDATE_SORT_RULE1) WORD_GT_NEQ
  val thm2 = MATCH_MP (spec UPDATE_SORT_RULE2) WORD_GT_NEQ
in
  CONJ thm1 thm2
end);

(* ------------------------------------------------------------------------ *)

val _ = export_theory ();
