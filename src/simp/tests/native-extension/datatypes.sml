(* Splitter cases over the option, pair and list datatypes, which are built
   after simp.  The Holmakefile builds this unit only once listTheory exists:
   tools/sequences/base-hol reruns this directory after list/src. *)
structure datatypes =
struct

open NativePrelude
open HolKernel Parse boolLib simpLib splitLib testutils boolSimps
local open optionTheory pairTheory listTheory in end

val _ = let
  val option_split = TypeBase.case_pred_imp_of ``:'a option``
  val option_asm_split =
    mk_asm_split (TypeBase.case_pred_disj_of ``:'a option``)
  val _ = convtest
    ("splitter: option case",
     SPLIT_CONV [option_split],
     ``P (option_CASE x (n:'b) (f:'a -> 'b)) : bool``,
     ``(x = NONE ==> P (n:'b)) /\
       !a:'a. x = SOME a ==> P (f a)``)

  val option_asm_goal =
    ([``P (option_CASE x (n:'b) (f:'a -> 'b)) : bool``],
     ``G:bool``)
  val _ = tprint "splitter: option case in an assumption"
  val _ =
    case valid (SPLIT_ASM_TAC [option_split, option_asm_split])
               option_asm_goal of
        [none_case, some_case] =>
          if not (goal_has_double_neg none_case) andalso
             not (goal_has_double_neg some_case)
          then OK()
          else die "option assumption split retained double negations"
      | _ => die "option assumption split produced the wrong cases"

  val pair_split = TypeBase.case_pred_imp_of ``:'a # 'b``
  val _ = convtest
    ("splitter: Generic.thy Cartesian-product example",
     SPLIT_CONV [pair_split],
     ``P (pair_CASE p (f:'a -> 'b -> 'c)) : bool``,
     ``!a:'a b:'b. p = (a,b) ==> P (f a b)``)

  val list_split = TypeBase.case_pred_imp_of ``:'a list``
  val _ = convtest
    ("splitter: list case",
     SPLIT_CONV [list_split],
     ``P (list_CASE xs (n:'b)
                    (f:'a -> 'a list -> 'b)) : bool``,
     ``(xs = [] ==> P (n:'b)) /\
       !h:'a t. xs = h::t ==> P (f h t)``)
  val _ = tprint "split_ss splits a list case using TypeBase"
  val list_goal =
    ``P (list_CASE xs (n:'b) (f:'a -> 'a list -> 'b)) : bool``
  val _ =
    case valid (SIMP_TAC (bool_ss ++ split_ss) []) ([], list_goal) of
        [([], result)] =>
          if not (aconv result list_goal) andalso
             not (can (find_term TypeBase.is_case) result)
          then OK()
          else die "split_ss did not eliminate the list case"
      | _ => die "split_ss produced the wrong list subgoals"
in
  ()
end

(* The splitter's datatype splits, and ExclX's case names, are those of the
   context the tactic runs in, whatever the live context has. *)
val _ = new_theory "split_datatypes"
val _ = let
  val earlier = Context.snapshot ()
  val _ = Feedback.quiet_messages Datatype.Datatype
            [QUOTE "nx_split_ctxt = NXA | NXB"]
  val declared = Context.snapshot ()
  val ty = mk_thy_type {Thy = current_theory (), Tyop = "nx_split_ctxt",
                        Args = []}
  val case_term =
    list_mk_icomb (TypeBase.case_const_of ty,
                   [mk_var ("x", ty), mk_var ("a", bool), mk_var ("b", bool)])
  val goal = ([], mk_comb (mk_var ("P", bool --> bool), case_term))
  fun splits ctxt tac =
    case Tactical.VALID tac goal ctxt of
        ([([], result)], _) =>
          not (can (find_term (aconv (#1 (strip_comb case_term)))) result)
      | _ => false
  val plain = SIMP_TAC (bool_ss ++ split_ss) []
  val excluded = SIMP_TAC (bool_ss ++ split_ss) [ExclX "case:nx_split_ctxt"]
  fun check label ok = (tprint label; if ok then OK () else die label)
  fun unmatched ctxt =
    case Exn.capture (Tactical.VALID excluded goal) ctxt of
        Exn.Exn (HOL_ERR e) =>
          Feedback.message_of e = "ExclX did not match case:nx_split_ctxt"
      | _ => false
in
  Context.restore earlier;
  check "split_ss splits a datatype of the tactic's context"
    (splits declared plain);
  check "ExclX names a datatype case of the tactic's context"
    (not (splits declared excluded));
  Context.restore declared;
  check "split_ss ignores a datatype only the live context has"
    (not (splits earlier plain));
  check "ExclX does not name a datatype case only the live context has"
    (unmatched earlier)
end

end (* struct *)
