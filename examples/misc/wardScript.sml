open HolKernel Parse boolLib bossLib

open dividesTheory

val _ = new_theory "ward"

val list_exp_def = Define`
  (list_exp l 0 = []) ∧
  (list_exp l (SUC n) = l ++ list_exp l n)
`;



val _ = Hol_datatype `alphabet = a | b | I`

val (thm_rules, thm_ind, thm_cases) = Hol_reln`
  thm [I] ∧
  (∀x y. thm (x ++ y) ⇒ thm (x ++ [I] ++ y)) ∧
  (∀x y. x ++ y ≠ [] ∧ thm (x ++ [I] ++ y) ⇒ thm (x ++ y)) ∧
  (∀x y. thm (x ++ [I] ++ y) ⇒ thm (x ++ [a;a;a] ++ y)) ∧
  (∀x y. thm (x ++ [a;a;a] ++ y) ⇒ thm (x ++ [I] ++ y)) ∧
  (∀x y. thm (x ++ [I] ++ y) ⇒ thm (x ++ [b;b;b] ++ y)) ∧
  (∀x y. thm (x ++ [b;b;b] ++ y) ⇒ thm (x ++ [I] ++ y)) ∧
  (∀x y. thm (x ++ [a;b;a;b] ++ y) ⇒ thm (x ++ [b;b;a;a] ++ y)) ∧
  (∀x y. thm (x ++ [b;b;a;a] ++ y) ⇒ thm (x ++ [a;b;a;b] ++ y))
`
open lcsymtacs
val div3_lemma = prove(
  ``divides 3 (x + 3 + y) ⇔ divides 3 (x + y)``,
  `x + 3 + y = x + y + 3` by DECIDE_TAC THEN
  SRW_TAC [][] THEN
  EQ_TAC THENL [
    METIS_TAC [arithmeticTheory.ADD_COMM, DIVIDES_REFL,
               DIVIDES_ADD_2],
    METIS_TAC [DIVIDES_REFL, DIVIDES_ADD_1]
  ])

val ab_DIV3 = store_thm(
  "ab_DIV3",
  ``∀l. thm l ⇒ divides 3 (LENGTH (FILTER ((=) a) l)) ∧
                divides 3 (LENGTH (FILTER ((=) b) l))``,
  Induct_on `thm` THEN SRW_TAC [][listTheory.FILTER_APPEND_DISTRIB,
                                  div3_lemma]);

val (thmrwt_rules, thmrwt_ind, thmrwt_cases) = Hol_reln`
  (∀x y. (x ++ y ≠ []) ⇒ thmrwt (x ++ [I] ++ y) (x ++ y)) ∧
  (∀x y. thmrwt (x ++ [a;a;a] ++ y) (x ++ [I] ++ y)) ∧
  (∀x y. thmrwt (x ++ [b;b;b] ++ y) (x ++ [I] ++ y)) ∧
  (∀x y. thmrwt (x ++ [a;b;a;b] ++ y) (x ++ [b;b;a;a] ++ y)) ∧
  (∀x y. thmrwt (x ++ [b;b;a;a;b;b] ++ y) (x ++ [a;b;a] ++ y)) ∧
  (∀x y. thmrwt (x ++ [a;a;b;b;a;a] ++ y) (x ++ [b;a;b] ++ y)) ∧
  (∀x y. thmrwt (x ++ [a;a;b;b] ++ y) (x ++ [b;a;b;a] ++ y))
`;

fun thm i = List.nth(CONJUNCTS thmrwt_rules, i)

val alphanil_t = ``[] : alphabet list``

fun lmkapp l = listSyntax.list_mk_append l handle HOL_ERR _ => alphanil_t

datatype accitem = TM of term | CONSLR of term list

fun strcons acc changedp t =
    if listSyntax.is_cons t then let
        val (h, hs_t) = listSyntax.dest_cons t
      in
        strcons (h::acc) true hs_t
      end
    else (acc, changedp, if listSyntax.is_nil t then NONE else SOME t)

fun stripapp worklist acc =
    case worklist of
      [] => let
        fun foldthis (TM t, acc) = t::acc
          | foldthis (CONSLR ts, acc) =
              listSyntax.mk_list (List.rev ts, type_of (hd ts)) :: acc
      in
        List.foldl foldthis [] acc
      end
    | t::ts => let
        open listSyntax
      in
        if is_append t then let
            val (l1, l2) = dest_append t
          in
            stripapp (l1 :: l2 :: ts) acc
          end
        else let
            val (consbase, accrest) = case acc of
                                        CONSLR l::rest => (l, rest)
                                      | _ => ([], acc)
          in
            case strcons consbase false t of
              ([], _, NONE) => stripapp ts acc
            | (els, _, NONE) => stripapp ts (CONSLR els :: accrest)
            | (_, false, SOME t') => stripapp ts (TM t'::acc)
            | (els, true, SOME t') => stripapp (t'::ts) (CONSLR els :: accrest)
          end
      end

datatype ('key, 'a) cons_trie =
         Node of 'a option * ('key,('key,'a) cons_trie) Binarymap.dict

fun find_trie_matches key trie = let
  fun recurse pfxr acc key (Node (valopt, d)) = let
    val newacc =
        case valopt of
          NONE => acc
        | SOME r => (List.rev pfxr, r) :: acc
  in
    case key of
      [] => newacc
    | e::es => let
      in
        case Binarymap.peek (d, e) of
          NONE => newacc
        | SOME trie' => recurse (e::pfxr) newacc es trie'
      end
  end
in
  recurse [] [] key trie
end

fun empty cmp = Node(NONE, Binarymap.mkDict cmp)

fun insert cmp (k,v) (Node(valopt,d)) =
    case k of
      [] => Node(SOME v, d)
    | e::es => let
      in
        case Binarymap.peek (d, e) of
          NONE => let
            val temp' = insert cmp (es,v) (empty cmp)
          in
            Node(valopt, Binarymap.insert(d,e,temp'))
          end
        | SOME t' => Node(valopt, Binarymap.insert(d,e,insert cmp(es,v) t'))
      end

val db = let
  fun foldthis ((t,v), acc) = let
    val (els, _) = listSyntax.dest_list t
  in
    insert Term.compare (els,v) acc
  end
in
  List.foldl foldthis (empty Term.compare)
             [(``[I:alphabet]``, (alphanil_t, thm 0)),
              (``[a;a;a]``,  (``[I:alphabet]``, thm 1)),
              (``[b;b;b]``, (``[I:alphabet]``, thm 2)),
              (``[a;b;a;b]``, (``[b;b;a;a]``, thm 3)),
              (``[b;b;a;a;b;b]``, (``[a;b;a]``, thm 4)),
              (``[a;a;b;b;a;a]``, (``[b;a;b]``, thm 5)),
              (``[a;a;b;b]``, (``[b;a;b;a]``, thm 6))]
end

fun find_cons_matches db els =
    case els of
      [] => let
        val res = find_trie_matches els db
      in
        map (fn v => ([],v,[])) res
      end
    | t::ts => let
        val hdres = find_trie_matches els db
        fun mapthis (v as (k,r)) = ([], v, List.drop(els,length k))
        val hdres' = map mapthis hdres
        val tlres = find_cons_matches db ts
      in
        (hdres' @ map (fn (p,v,s) => (t::p,v,s)) tlres)
      end
val alpha_ty = ``:alphabet``
fun find_app_matches db app_list = let
  fun recurse pfxr acc apps =
    case apps of
      [] => acc
    | t::ts => let
        val els = #1 (listSyntax.dest_list t) handle HOL_ERR _ => []
        val t_results0 = find_cons_matches db els
        fun mapthis (p,r,s) = let
          val p_l = if null p then [] else [listSyntax.mk_list(p, alpha_ty)]
          val s_l = if null s then [] else [listSyntax.mk_list(s, alpha_ty)]
        in
          (List.rev(p_l @ pfxr), r, s_l @ ts)
        end
        val results = map mapthis t_results0
      in
        recurse (t::pfxr) (acc @ results) ts
      end
in
  recurse [] [] app_list
end

open listTheory

fun solver (asl, t) = let
  val nonnil_asms = map ASSUME (filter is_neg asl)
  fun munge extras p s th =
      th |> SPECL [lmkapp p, lmkapp s]
         |> REWRITE_RULE (GSYM APPEND_ASSOC :: APPEND_eq_NIL :: APPEND ::
                          APPEND_NIL :: NOT_NIL_CONS :: NOT_CONS_NIL ::
                          extras @ nonnil_asms)
         |> MATCH_MP relationTheory.RTC_SUBSET
  val (_,body) = dest_exists t
in
  if is_conj body then let
      val (c1, c2) = dest_conj body
      val (_, [_, x1, _]) = strip_comb c1
      val (_, [_, x2, _]) = strip_comb c2
      val app_args1 = stripapp [x1] []
      val app_args2 = stripapp [x2] []
      val possibilities1 = find_app_matches db app_args1
      val possibilities2 = find_app_matches db app_args2
      fun nilf t = if listSyntax.is_nil t then [] else [t]
      fun check (p1, (_, (res1, _)), s1) (p2, (_, (res2, _)), s2) =
          p1 @ nilf res1 @ s1 = p2 @ nilf res2 @ s2
      fun checkl t = List.mapPartial (fn t' => if check t t' then SOME (t,t')
                                               else NONE)
      fun checkll [] p2 = []
        | checkll (h::t) p2 = checkl h p2 @ checkll t p2
      val possibilities = checkll possibilities1 possibilities2
      val ((pfx1, (_, (res1, th1)), sfx1), (pfx2, (_, (res2, th2)), sfx2)) =
          hd possibilities
      fun conclude extras = let
        val th1' = munge extras pfx1 sfx1 th1
        val th2' = munge extras pfx2 sfx2 th2
      in
        EXISTS_TAC (rand (concl th1')) THEN
        REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] THEN
        ACCEPT_TAC (CONJ th1' th2')
      end
    in
      if null nonnil_asms andalso listSyntax.is_nil res1 andalso
         listSyntax.is_nil res2 andalso List.all is_var pfx1 andalso
         List.all is_var sfx1
      then let
          val eqn = mk_eq(last (pfx1 @ sfx1), alphanil_t)
        in
          ASM_CASES_TAC eqn THENL [
            BasicProvers.VAR_EQ_TAC THEN REWRITE_TAC [APPEND_NIL] THEN
            solver,
            conclude [ASSUME (mk_neg eqn)]
          ]
        end
      else conclude []
    end
  else let
      val (_, [_, x, _]) = strip_comb body
    in
      EXISTS_TAC x THEN MATCH_ACCEPT_TAC relationTheory.RTC_REFL
    end
end (asl,t) handle Empty => raise mk_HOL_ERR "wardScript" "solver" "Empty list"
(*
val thmrwt_weak_confluent = store_thm(
  "thmrwt_weak_confluent",
  ``∀x y. thmrwt x y ⇒ ∀z. thmrwt x z ⇒ ∃u. thmrwt^* y u ∧ thmrwt^* z u``,
  Induct_on `thmrwt` >> rpt conj_tac >-
    (rpt gen_tac >> strip_tac >> gen_tac >>
     srw_tac [][SimpL ``(==>)``, Once thmrwt_cases] >>
     fsrw_tac [][listTheory.APPEND_EQ_APPEND_MID,
                 listTheory.APPEND_EQ_SING,
                 listTheory.APPEND_eq_NIL,
                 listTheory.APPEND_EQ_CONS] >>
     srw_tac [][] >>
     fsrw_tac [][listTheory.APPEND_EQ_SING,
                 listTheory.APPEND_eq_NIL] >>
     solver)
   >- (rpt gen_tac >> srw_tac [][SimpL ``(==>)``, Once thmrwt_cases] >>
       fsrw_tac [][APPEND_EQ_APPEND_MID, APPEND_EQ_SING, APPEND_EQ_CONS] THEN
       srw_tac [][] >> fsrw_tac [][] >> TRY  solver >>
       fsrw_tac [][APPEND_EQ_APPEND, APPEND_EQ_CONS] >> srw_tac [][] >>
       fsrw_tac [][APPEND_EQ_CONS] >> TRY solver

     TRY (metis_tac [relationTheory.RTC_SUBSET, relationTheory.RTC_REFL,
                     listTheory.APPEND_ASSOC, thmrwt_rules,
                     listTheory.APPEND_eq_NIL]) >>
     solver
     >| [
       qexists_tac `x' ++ [b;b;a;a] ++ z ++ y` >>
       conj_tac >| [
         metis_tac [relationTheory.RTC_SUBSET, listTheory.APPEND_ASSOC,
                    thmrwt_rules],
         srw_tac [][relationTheory.RTC_SUBSET, thmrwt_rules]
       ],
       qexists_tac `x ++ z' ++ [b;b;a;a] ++ y'` >>
       conj_tac >- srw_tac [][thmrwt_rules, relationTheory.RTC_SUBSET] >>
       match_mp_tac relationTheory.RTC_SUBSET >>
       `x ++ [I] ++ z' ++ [b;b;a;a] ++ y' = x ++ [I] ++ (z' ++ [b;b;a;a] ++ y')`
          by srw_tac [][] >>
       pop_assum SUBST1_TAC >>
       `x ++ z' ++ [b;b;a;a] ++ y' = x ++ (z' ++ [b;b;a;a] ++ y')`
          by srw_tac [][] >>
       pop_assum SUBST1_TAC >>
       match_mp_tac (hd (CONJUNCTS thmrwt_rules)) >> srw_tac [][],
       pop_assum (MP_TAC o AP_TERM ``MEM I``) >> srw_tac [][],
*)
val _ = export_theory()
