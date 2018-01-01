structure PrecAnalysis :> PrecAnalysis =
struct

open HOLgrammars term_grammar_dtype

type lspec = listspec
type rel = HOLgrammars.rule_element
type mlsp = HOLgrammars.mini_lspec

infix |>
fun (x |> f) = f x

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

fun check_for_listreductions check rels =
  let
    val rev = List.rev
    fun recurse A left_opt sep_opt p rels =
      (* left_opt is candidate left-delimiter, sep_opt candidate separator
         Invariant:
           left_opt = SOME l ==> TOK l was seen earlier as candidate leftdelim
           sep_opt = SOME s ==>
             ?l. left_opt = SOME l /\ TOK s followed a TM after the l was
                 seen and there have been no other TOKs seen since, and
                 check(l,s) = NONE
           (p <=> last thing seen was TM)
       *)
      case rels of
          [] => rev A
        | [TM] => rev A
        | [TOK tk1] => (* tk1 may end a list *)
          let
          in
            case sep_opt of
                SOME s =>
                   (case check(s, tk1) of
                        NONE =>
                        (case check(valOf left_opt, tk1) of
                             NONE => rev A
                           | SOME lp =>
                               rev ((valOf left_opt, tk1, lp) :: A))
                      | SOME lp => rev ((s,tk1,lp)::A))
              | NONE =>
                   (case left_opt of
                        NONE => rev A
                      | SOME l => (case check(l,tk1) of
                                       NONE => rev A
                                     | SOME lp => rev ((l,tk1,lp) :: A)))
          end
        | TOK tk1 :: TM :: rest =>
          let
          in
            case sep_opt of
                SOME s =>
                   (if s = tk1 andalso p then
                      recurse A left_opt sep_opt true rest
                    else
                      case check (valOf left_opt, tk1) of
                          NONE =>
                          (case check (s, tk1) of
                               NONE =>
                                 if p then
                                   recurse A (SOME s) (SOME tk1) true rest
                                 else
                                   recurse A (SOME tk1) NONE true rest
                             | SOME lp =>
                                 recurse ((s,tk1,lp)::A) (SOME tk1) NONE
                                         true rest)
                        | SOME lp => recurse ((valOf left_opt, tk1, lp)::A)
                                             (SOME tk1) NONE true rest)
              | NONE =>
                  (case left_opt of
                       NONE => recurse A (SOME tk1) NONE true rest
                     | SOME l =>
                         (case check (l, tk1) of
                              NONE => if p then
                                        recurse A left_opt (SOME tk1) true rest
                                      else
                                        recurse A (SOME tk1) NONE true rest
                            | SOME lp =>
                                recurse ((l,tk1,lp)::A) (SOME tk1) NONE
                                        true rest))
          end
        | TOK tk1 :: TOK tk2 :: rest =>
            (case sep_opt of
                 SOME s =>
                   if s = tk1 andalso p then
                     case check (valOf left_opt, tk2) of
                         NONE =>
                         (case check(tk1,tk2) of
                              NONE => recurse A (SOME tk2) NONE false rest
                            | SOME lp =>
                                recurse ((tk1,tk2,lp)::A) (SOME tk2) NONE
                                        false rest)
                       | SOME lp =>
                          recurse ((valOf left_opt, tk2, lp)::A)
                                  (SOME tk2) NONE false rest
                   else
                     (case check(s,tk1) of
                         NONE =>
                         if p then
                           case check(s,tk2) of
                               NONE =>
                               (case check (tk1,tk2) of
                                    NONE => recurse A (SOME tk2) NONE false rest
                                  | SOME lp =>
                                    recurse ((tk1,tk2,lp)::A) (SOME tk2)
                                            NONE false rest)
                             | SOME lp =>
                               (* s is the left, tk1 is the sep, tk2 right *)
                               recurse ((s,tk2,lp)::A) (SOME tk2) NONE false
                                       rest
                         else
                           (case check (tk1,tk2) of
                                    NONE => recurse A (SOME tk2) NONE false rest
                                  | SOME lp =>
                                    recurse ((tk1,tk2,lp)::A) (SOME tk2)
                                            NONE false rest)
                       | SOME lp =>
                            recurse ((s,tk1,lp)::A) (SOME tk1) NONE
                                    false (TOK tk2 :: rest))
               | NONE => (* no sep *)
                 let
                   val f = case check(tk1,tk2) of
                                NONE => (fn A => A)
                              | SOME lp => (fn A => (tk1,tk2,lp) :: A)
                 in
                   case left_opt of
                      NONE => recurse (f A) (SOME tk2) NONE false rest
                    | SOME l =>
                      (case check(l,tk1) of
                           NONE =>
                           if p then (* tk1 might be sep and tk2 rdelim *)
                             case check(l,tk2) of
                                 NONE =>
                                   recurse (f A) (SOME tk2) NONE false rest
                               | SOME lp =>
                                   recurse ((l,tk2,lp)::A) (SOME tk2) NONE false
                                           rest
                           else
                             recurse (f A) (SOME tk2) NONE false rest
                         | SOME lp =>
                             recurse (f ((l,tk1,lp)::A)) (SOME tk2) NONE false
                                     rest)
                 end)
        | TM :: rest => (* p must be false as two TMs in a row is impossible *)
            recurse A left_opt sep_opt true rest
        | _ => raise Fail "check_for_listreductions: impossible rhs"
  in
    recurse [] NONE NONE false rels
  end

fun rev2 (l1, l2, c) = (List.rev l1, List.rev l2, c)
fun c1 x (l1, l2, c) = (x::l1, l2, c)
fun c2 x (l1, l2, c) = (l1, x::l2, c)
fun inc (l1, l2, c) = (l1, l2, c + 1)
fun ap1 f (x,y,z) = (f x, y, z)

fun remove_listrels lsps rels =
  let
    fun recurse (A as (outrels, listbits, tmc)) lsps rels =
      case lsps of
          [] => ap1 (fn l => l @ rels) (rev2 A)
        | (ld,rd,lsp:mini_lspec)::more_lsps =>
          (case rels of
               [] => rev2 A
             | TM :: rrest => recurse (A |> inc |> c1 TM) lsps rrest
             | (rel as TOK tk) :: more_rels =>
                 if tk <> ld then recurse (c1 rel A) lsps more_rels
                 else (* tk = ld *)
                   let
                     val {sep,...} = lsp
                   in
                     case more_rels of
                         TOK tk' :: later_rels =>
                           if tk' = rd then
                             recurse
                               (A |> c1 rel |> c1 TM |> c2 (lsp,[]))
                               more_lsps
                               more_rels
                           else
                             (* probably an error; can't be sep as no TM first*)
                             recurse (c1 rel A) more_lsps more_rels
                       | TM :: (inter_rels as (TOK sep' :: later_rels)) =>
                           if sep = sep' then
                             consume_list
                               (A |> c1 rel |> c1 TM |> inc) (lsp, [#3 A]) rd
                               more_lsps later_rels
                           else if sep' = rd then
                             recurse
                               (A |> c1 rel |> c1 TM |> inc |> c2 (lsp, [#3 A]))
                               more_lsps inter_rels
                           else (* probably an error *)
                             recurse (A |> c1 rel |> c1 TM |> inc)
                                     lsps
                                     inter_rels
                       | _ => raise Fail "remove_listrels: malformed RHS"
                   end
             | _ => raise Fail "remove_listrels: malformed RHS(2)")
    and consume_list A (curr as (lsp, idxs)) rdelim lsps rels =
        case rels of
            [] => (* probably an error *) rev2 (A |> c2 (lsp, List.rev idxs))
          | TM :: rest => consume_list (A |> inc) (lsp, #3 A :: idxs)
                                       rdelim lsps rest
          | TOK t :: rest =>
            if t = rdelim then
              recurse (A |> c2 (lsp, List.rev idxs)) lsps rels
            else (* it's assumed to be the sep *)
              consume_list A curr rdelim lsps rest
          | _ => raise Fail "consume_list: malformed RHS"
    val (x, y, _) = recurse ([], [], 0) lsps rels
  in
    (x,y)
  end

end
