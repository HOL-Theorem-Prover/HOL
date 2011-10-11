open Opentheory Logging

fun termArticle out t = let
  val _ = raw_start_logging out
  val _ = export_thm (mk_thm([],t))
  val _ = stop_logging()
in () end

fun articleThm inp = let
  val thms = raw_read_article inp {
    define_const = fn _ => raise Fail "define_const",
    define_tyop = fn _ => raise Fail "define_tyop",
    axiom = axiom_in_db,
    const_name = const_name_in_map,
    tyop_name = tyop_name_in_map}
in hd (Net.listItems thms) end

(*
termArticle (TextIO.openOut("/tmp/tm.art")) ``!x. ?y. (x \/ y) /\ ~y``
termArticle (TextIO.openOut("/tmp/tm.art")) ``!x. ?y. x \/ y``

    ``(p \/ ~q) /\ r``,
    ``?p. (p \/ ~q) /\ r``,
    ``?q. (p \/ ~q) /\ r``,
    ``?r. (p \/ ~q) /\ r``,
    ``!p. ?q. (p \/ ~q) /\ r``,
    ``!p q. ?r. (p \/ ~q) /\ r``,
    ``!p. ?q r. (p \/ ~q) /\ r``,
    ``?p. !q. ?r. (p \/ ~q) /\ r``
    ``?x. x /\ ~x``,
    ``!x. ?y. x /\ y``,
    ``!x. ?y. (x \/ y) /\ ~y``
    ``?x. x``,
    ``!x. ?y. x \/ y``,
    ``!x. ?y. (x \/ y) /\ (~x \/ y)``
*)
