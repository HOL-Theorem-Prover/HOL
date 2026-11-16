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

end (* struct *)
