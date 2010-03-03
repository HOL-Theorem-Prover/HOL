open HolKernel boolLib bossLib Parse
open EmitML option_emitTheory num_emitTheory llistTheory list_emitTheory

val _ = new_theory "llist_emit"

val llcases_exists0 = prove(
  ``!l. ?v. (l = [||]) /\ (v = n) \/
            ?h t. (l = h:::t) /\ (v = c (h, t))``,
  GEN_TAC THEN Q.SPEC_THEN `l` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][EXISTS_OR_THM])
val llcases_exists =
    llcases_exists0 |> GEN_ALL |> SIMP_RULE bool_ss [SKOLEM_THM]
val llcases_def = new_specification("llcases_def", ["llcases"],
                                    llcases_exists)

val llcases_LNIL = llcases_def |> SPEC_ALL |> Q.INST [`l` |-> `LNIL`]
                               |> SIMP_RULE (srw_ss()) []
val llcases_LCONS = llcases_def |> SPEC_ALL |> Q.INST [`l` |-> `h:::t`]
                               |> SIMP_RULE (srw_ss()) []

val LLCONS_def = Define`
  LLCONS h t = LCONS h (t ())`;

val LAPPEND_llcases = prove(
  ``LAPPEND l1 l2 = llcases l2 (\(h,t). LLCONS h (\(). LAPPEND t l2)) l1``,
  Q.SPEC_THEN `l1` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][LLCONS_def, llcases_LCONS, llcases_LNIL]);

val LMAP_llcases = prove(
  ``LMAP f l = llcases LNIL (\(h,t). LLCONS (f h) (\(). LMAP f t)) l``,
  Q.ISPEC_THEN `l` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][LLCONS_def, llcases_LCONS, llcases_LNIL]);

val LFILTER_llcases = prove(
  ``LFILTER P l = llcases LNIL (\(h,t). if P h then LLCONS h (\(). LFILTER P t)
                                        else LFILTER P t) l``,
  Q.ISPEC_THEN `l` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][LLCONS_def, llcases_LCONS, llcases_LNIL]);

val LHD_llcases = prove(
  ``LHD ll = llcases NONE (\(h,t). SOME h) ll``,
  Q.ISPEC_THEN `ll` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][llcases_LCONS, llcases_LNIL]);

val LTL_llcases = prove(
  ``LTL ll = llcases NONE (\(h,t). SOME t) ll``,
  Q.ISPEC_THEN `ll` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][llcases_LCONS, llcases_LNIL]);

val LTAKE_thm = prove(
  ``!ll. LTAKE n ll =
                if n = 0 then SOME []
                else case LHD ll of
                       NONE -> NONE
                    || SOME h -> OPTION_MAP (\t. h::t)
                                            (LTAKE (n - 1) (THE (LTL ll)))``,
  Induct_on `n` THEN SRW_TAC [boolSimps.ETA_ss][LTAKE] THEN
  Q.ISPEC_THEN `ll` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][] THEN Cases_on `LHD t` THEN SRW_TAC [][] THEN
  Cases_on `OPTION_MAP (CONS x) (LTAKE (n - 1) (THE (LTL t)))` THEN
  SRW_TAC [][]);

val toList_llcases = prove(
  ``toList ll = llcases (SOME []) (\(h,t). OPTION_MAP (\t. h::t) (toList t)) ll``,
  Q.ISPEC_THEN `ll` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [boolSimps.ETA_ss][llcases_LCONS, llcases_LNIL, toList_THM])

fun insert_const c = let val t = Parse.Term [QUOTE c] in
  ConstMapML.prim_insert(t, (false, "", c, type_of t))
end
val _ = insert_const "llcases"
val _ = insert_const "LLCONS"
val _ = insert_const "LCONS"
val _ = insert_const "LNIL"
val _ = insert_const "LUNFOLD"
val _ = adjoin_to_theory
{sig_ps = NONE, struct_ps = SOME (fn ppstrm =>
  let val S = PP.add_string ppstrm
      fun NL() = PP.add_newline ppstrm
  in S "fun insert_const c = let val t = Parse.Term [QUOTE c] in"; NL();
     S "  ConstMapML.prim_insert(t, (false, \"\", c, type_of t))"; NL();
     S "end"; NL();
     S "val _ = insert_const \"llcases\""; NL();
     S "val _ = insert_const \"LLCONS\""; NL();
     S "val _ = insert_const \"LCONS\""; NL();
     S "val _ = insert_const \"LNIL\""; NL();
     S "val _ = insert_const \"LUNFOLD\""
  end)}

val _ = eSML "llist"
        (MLSIG "type 'a llist" ::
         MLSIG "val LNIL : 'a llist" ::
         MLSIG "val LLCONS : 'a -> (unit -> 'a llist) -> 'a llist" ::
         MLSIG "val LCONS : 'a -> 'a llist -> 'a llist" ::
         MLSIG "val ::: : 'a * 'a llist -> 'a llist" ::
         MLSIG "val llcases : 'b -> ('a * 'a llist -> 'b) -> 'a llist -> 'b" ::
         MLSIG "val LUNFOLD : ('a -> ('a * 'b) option) -> 'a -> 'b llist" ::
         MLSIG "type num = numML.num" ::
         OPEN ["num", "list"] ::
         MLSTRUCT "type 'a llist = 'a seq.seq" ::
         MLSTRUCT "fun llcases n c seq = seq.fcases seq (n,c)" ::
         MLSTRUCT "fun LLCONS h t = seq.cons h (seq.delay t)"::
         MLSTRUCT "fun LCONS h t = seq.cons h t"::
         MLSTRUCT "val LNIL = seq.empty"::
         MLSTRUCT "fun :::(h,t) = LCONS h t"::
         MLSTRUCT "fun LUNFOLD f x = seq.delay (fn () => case f x of NONE => LNIL | SOME (y,e) => LCONS e (LUNFOLD f y))" ::
         map DEFN [
           LAPPEND_llcases, LMAP_llcases, LFILTER_llcases,
           LHD_llcases, LTL_llcases, LTAKE_thm,
           toList_llcases])

val _ = export_theory()
