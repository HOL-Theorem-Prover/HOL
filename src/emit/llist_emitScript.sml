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

val LAPPEND_llcases = prove(
  ``LAPPEND l1 l2 = llcases l2 (\(h,t). h:::LAPPEND t l2) l1``,
  Q.SPEC_THEN `l1` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][llcases_LCONS, llcases_LNIL]);

val LMAP_llcases = prove(
  ``LMAP f l = llcases LNIL (\(h,t). f h ::: LMAP f t) l``,
  Q.ISPEC_THEN `l` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][llcases_LCONS, llcases_LNIL]);

val LFILTER_llcases = prove(
  ``LFILTER P l = llcases LNIL (\(h,t). if P h then h ::: LFILTER P t
                                        else LFILTER P t) l``,
  Q.ISPEC_THEN `l` STRUCT_CASES_TAC llist_CASES THEN
  SRW_TAC [][llcases_LCONS, llcases_LNIL]);

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

val _ = ConstMapML.prim_insert (
                                ``llcases``, (false, "", "llcases",
                                              type_of ``llcases``))
val _ = ConstMapML.prim_insert(``LCONS``, (false, "", "LCONS",
                                           type_of ``LCONS``))
val _ = ConstMapML.prim_insert(``LNIL``, (false, "", "LNIL",
                                           type_of ``LNIL``))
val _ = ConstMapML.prim_insert(``LUNFOLD``, (false, "", "LUNFOLD",
                                           type_of ``LUNFOLD``))

val _ = eSML "llist"
        (MLSIG "type 'a llist" ::
         MLSIG "val LNIL : 'a llist" ::
         MLSIG "val LCONS : 'a -> 'a llist -> 'a llist" ::
         MLSIG "val ::: : 'a * 'a llist -> 'a llist" ::
         MLSIG "val llcases : 'b -> ('a * 'a llist -> 'b) -> 'a llist -> 'b" ::
         MLSIG "val LUNFOLD : ('a -> ('a * 'b) option) -> 'a -> 'b llist" ::
         OPEN ["num", "list"] ::
         MLSTRUCT "type 'a llist = 'a seq.seq" ::
         MLSTRUCT "fun llcases n c seq = seq.fcases seq (n,c)" ::
         MLSTRUCT "fun LCONS h t = seq.cons h t"::
         MLSTRUCT "val LNIL = seq.empty"::
         MLSTRUCT "fun :::(h,t) = LCONS h t"::
         MLSTRUCT "fun LUNFOLD f x = seq.delay (fn () => case f x of NONE => LNIL | SOME (y,e) => LCONS e (LUNFOLD f y))" ::
         [DEFN LAPPEND_llcases, DEFN LMAP_llcases, DEFN LFILTER_llcases,
          DEFN LHD_llcases, DEFN LTL_llcases, DEFN LTAKE_thm])

val _ = export_theory()

