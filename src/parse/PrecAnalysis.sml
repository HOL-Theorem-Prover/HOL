structure PrecAnalysis :> PrecAnalysis =
struct

open HOLgrammars term_grammar_dtype

type lspec = listspec

fun listfld_tok ppels =
  case ppels of
      [] => raise Fail "No TOK in list field pp-element list"
    | RE (TOK s) :: _ => s
    | RE TM :: _ => raise Fail "TM in list field pp-element list"
    | ListForm _ :: _ => raise Fail "ListForm in list field pp-element list"
    | _ :: rest => listfld_tok rest

fun listform_left ({leftdelim,...} : lspec) = listfld_tok leftdelim
fun listform_right ({rightdelim,...} : lspec) = listfld_tok rightdelim

fun rel_equalities rels =
  let
    fun recurse rels (A as (lastopt, acc)) =
      case (lastopt, rels) of
          (_, []) => acc
        | (SOME(_, true), TM :: _) => raise Fail "Two TM elements in a row"
        | (SOME(tk1,false), TM :: rest) => recurse rest (SOME(tk1,true), acc)
        | (SOME(tk1, tmp), TOK tk2::rest) =>
            recurse rest (SOME(tk2,false), (tk1,tmp,tk2)::acc)
        | (SOME(tk1, true), ListTM _ :: rest) =>
            raise Fail "rel_equalities: TM before ListTM"
        | (SOME(tk1, false), ListTM{sep,...} :: TOK tk2 :: rest) =>
            recurse rest (SOME (tk2,false),
                          (tk1,true,sep) :: (sep,true,sep) ::
                          (sep,false,tk2) :: (sep,true,tk2) ::
                          (tk1,true,tk2) :: (tk1,false,tk2) :: acc)
        | (_, ListTM _ :: ListTM _ :: _) =>
            raise Fail "rel_equalities: two ListTMs in a row"
        | (_, ListTM _ :: TM :: _) =>
            raise Fail "rel_equalities: ListTM followed by TM"
        | (_, [ListTM _]) => raise Fail "rel_equalities: last ListTM"
        | (NONE, TM :: _) => raise Fail "rel_equalities: initial TM"
        | (NONE, TOK tk :: rest) => recurse rest (SOME(tk,false), acc)
        | (NONE, ListTM _ :: _) => raise Fail "rel_equalities: initial ListTM"
  in
    recurse rels (NONE, [])
  end

fun ppel_equalities ppels = rel_equalities (term_grammar.rule_elements ppels)
fun rule_equalities (rr : rule_record) = ppel_equalities (#elements rr)

type rell_transform = rule_element list -> rule_element list

fun mkrels_infix rels = TM :: (rels @ [TM])
fun mkrels_suffix rels = TM :: rels
fun mkrels_prefix rels = rels @ [TM]
fun mkrels_closefix rels = rels


end
