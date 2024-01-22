structure translationsLib :> translationsLib =
struct

open HolKernel Parse boolLib bossLib;

open full_ltlTheory arithmeticTheory automaton_formulaTheory xprop_logicTheory prop_logicTheory
     infinite_pathTheory tuerk_tacticsLib symbolic_semi_automatonTheory listTheory pred_setTheory
     temporal_deep_mixedTheory pred_setTheory rich_listTheory set_lemmataTheory
     pairTheory pred_setSyntax ltl_to_automaton_formulaTheory numLib listLib translationsLibTheory
     rltl_to_ltlTheory rltlTheory computeLib congLib temporal_deep_simplificationsLib
     Trace symbolic_kripke_structureTheory psl_lemmataTheory ProjectionTheory psl_to_rltlTheory;

exception NoLTLTerm;

val list_ss = list_ss -* ["LT1_EQ0"]
val std_ss = std_ss -* ["LT1_EQ0"]

(* This function is recursive thus cannot be defined as a value *)
fun SETIFY_CONV tm =
   (SUB_CONV (SETIFY_CONV) THENC TRY_CONV (pred_setLib.INSERT_CONV NO_CONV)) tm;

(* The translation of LTL to GEN_BUECHI using just rewrite rules *)
fun ltl2omega_rewrite t l = let
    val (typeString, ltl_type) = (dest_type (type_of l));
    val _ = if (typeString = "ltl") then T else raise NoLTLTerm;
    val ltl_type = hd (ltl_type);
    val thm = if t then LTL_TO_GEN_BUECHI___TRANSLATION_THM___MAX
              else LTL_TO_GEN_BUECHI___TRANSLATION_THM___MIN;
    val thm = INST_TYPE [alpha |-> ltl_type] thm;
    val thm = SPECL [``F:bool``, l] thm;
    val thm = SIMP_RULE list_ss [LTL_TO_GEN_BUECHI_def,
                  LTL_ALWAYS_def, LTL_EVENTUAL_def,
                  LTL_TO_GEN_BUECHI_DS___A_NDET_def,
                  LTL_TO_GEN_BUECHI_DS___A_UNIV_def,
                  LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
                  LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
                  LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def,
                  XP_BIGAND_def,
                  LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def,
                  LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS_def,
                  A_BIGAND_def,
                  symbolic_semi_automaton_REWRITES,
                  LTL_TO_GEN_BUECHI___EXTEND_def,
                  P_USED_VARS_def,
                  XP_CURRENT_def,
                  XP_NEXT_def,
                  P_BIGAND_def,
                  UNION_INSERT,
                  LET_THM, EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
                  EXTEND_LTL_TO_GEN_BUECHI_DS_def, ltl_to_gen_buechi_ds_REWRITES,
                  UNION_EMPTY, EMPTY_LTL_TO_GEN_BUECHI_DS_def] thm;
  in
    thm
  end;

(******************************************************************************)
(* A more sophistacted translations, that is able to exploit term-sharing     *)
(******************************************************************************)

(* some general helpers *)
fun boolToHOL b = if b then T else F;
fun HOLToBool b = (b ~~ T);

fun dsExtractFromThm dsThm =
  hd (snd (strip_comb(concl (dsThm))));

fun dsBindingsExtractFromThm dsThm =
  let
    val set = el 6 (snd (strip_comb(dsExtractFromThm dsThm)));
    val result = strip_set set;
  in
    result
  end;

fun getBindingFor b1 b2 l [] = (false, false, ``dummy:num``)
  | getBindingFor b1 b2 l (h::l1) =
      let
        val hList = strip_pair h;
        val (l', a1, a2, pf) = (el 1 hList, HOLToBool(el 2 hList), HOLToBool(el 3 hList), el 4 hList);
      in
        if ((l' ~~ l) andalso ((not b1) orelse a1) andalso ((not b2) orelse a2)) then
          (a1, a2, pf)
        else
          getBindingFor b1 b2 l l1
      end;

exception T_IMP_Error;
val t_imp_elim_rwt = prove (``!x. (T ==> x) = x``, REWRITE_TAC[]);

fun T_IMP_ELIM_RULE thm =
  (CONV_RULE (REWR_CONV t_imp_elim_rwt) thm) handle _ => (
    let
      val _ = print "Theorem not of the form T ==> x\n\n";
      val _ = print_thm thm;
    in
      raise T_IMP_Error
    end
  );

local
  val bindings_compset = new_compset [IN_SING, IN_INSERT, OR_CLAUSES, AND_CLAUSES]
in
  fun SIMP_DS___BINDINGS thm =
    let
        val conv = (DEPTH_CONV (pred_setLib.IN_CONV NO_CONV)) THENC CBV_CONV bindings_compset
        val thm = CONV_RULE (RATOR_CONV (RAND_CONV conv)) thm;
        val thm = T_IMP_ELIM_RULE thm;
    in
      thm
    end;
end;

(* ltl_to_omega_internal and ltl_to_omega *)
local
  exception UnsupportedLTLTerm;
  exception UnsupportedTerm;
  exception NotYetImplemented;
  exception ImplementionError;

  val SIMP_DS___BASIC =
    let
      val compset = new_compset [ltl_to_gen_buechi_ds_REWRITES,
        NOT_CLAUSES, AND_CLAUSES]
    in
      CONV_RULE (CBV_CONV compset)
    end;

  val SIMP_DS___USED_VARS =
    let
      val compset = new_compset [UNION_EMPTY, P_USED_VARS_EVAL, UNION_SING,
        INSERT_UNION_EQ, INSERT_INSERT]
      val conv = CBV_CONV compset
    in
      CONV_RULE (RAND_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV (conv))))))
    end;

  val SIMP_DS___USED_VARS___DUPLICATES =
      CONV_RULE (RAND_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV (SETIFY_CONV))))))

  val SIMP_DS___USED_STATE_VARS =
    let
      val conv = REDUCE_CONV
    in
      CONV_RULE (RAND_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV (conv))))))))
    end;

  val SIMP_DS___FAIRNESS_CONSTRAINT =
    let
      val compset = new_compset [COND_CLAUSES, APPEND_NIL, APPEND]
      val conv = CBV_CONV compset
    in
      CONV_RULE (RAND_CONV (RATOR_CONV (RAND_CONV (conv))))
    end;

  fun BUILD_LIST_FIRST_CONV term conv =
    if (is_comb term) then
      BUILD_LIST_FIRST_CONV (rator term) (RATOR_CONV conv)
    else
      (term, conv);

  val compset = new_compset [XP_CURRENT_def, XP_NEXT_def]
  fun SIMP_DS___FIRST_TRANSITION thm =
    let
      val conv = CBV_CONV compset;
      val term = rator(rand (rator (rator (rand (concl thm)))))
      val (_, conv) = BUILD_LIST_FIRST_CONV term (RAND_CONV conv);
      val conv = (RAND_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV (conv)))))
    in
      CONV_RULE conv thm
    end;

  fun SIMP_DS___BODY thm =
    let
      val thm = SIMP_DS___USED_VARS thm
      val thm = SIMP_DS___USED_STATE_VARS thm
      val thm = SIMP_DS___FAIRNESS_CONSTRAINT thm
    in
      thm
    end;

  fun ltl2omega_internal2 b1 b2 l dsThm TSPECL =
      let
        fun extractFuncAndArgs l =
          let
            val (f, args) = strip_comb l;
            val (fs, _) = dest_const f;
          in
            (f, args, fs)
          end;
        val (f, args, fs) = extractFuncAndArgs l handle _ => (l, [], "ERROR");

        fun addBindingFor b1 b2 l dsThm =
          let
            val dsB = dsBindingsExtractFromThm dsThm;
            val (b1', b2', pf) = getBindingFor b1 b2 l dsB;
        in
            if (b1' orelse b2') then (b1', b2', pf, dsThm) else (
              let
                val dsThm = ltl2omega_internal2 b1 b2 l dsThm TSPECL;
                val dsB = dsBindingsExtractFromThm dsThm;
                val (b1', b2', pf) = (getBindingFor b1 b2 l dsB);
                val _ = if (b1' orelse b2') then T else
                  (let
                    val _ = print "After inserting a binding for (";
                    val _ = print_term l;
                    val _ = print ", ";
                    val _ = print_term (boolToHOL b1);
                    val _ = print ", ";
                    val _ = print_term (boolToHOL b2);
                    val _ = print "), it still is not present in:\n\n";
                    val _ = print_thm dsThm;
                    val _ = print "\n\nThere has to be an Implementation Error!\n\n";
                  in
                    raise ImplementionError
                  end);
              in
                (b1', b2', pf, dsThm)
              end
            )
          end;

      in
        if fs = "LTL_PROP" then (
          let
            val ds = dsExtractFromThm dsThm;
            val thm = TSPECL [ds, hd args]
              (CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PROP___eval);
            val thm = MP thm dsThm;
            val thm = SIMP_DS___BASIC thm;
            val thm = SIMP_DS___USED_VARS thm
          in
            thm
          end
        ) else if fs = "LTL_NOT" then (
          let
            val (b2', b1', pf, dsThm) = addBindingFor b2 b1 (hd args) dsThm;
            val ds = dsExtractFromThm dsThm;
            val thm = TSPECL [boolToHOL b2', boolToHOL b1']
              (CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT___eval);
            val thm = REWRITE_RULE [NOT_CLAUSES] thm
            val thm = SPECL [ds, hd args, pf] thm
            val thm = MP thm dsThm;
            val thm = SIMP_DS___BASIC thm;
            val thm = SIMP_DS___BINDINGS thm;
          in
            thm
          end
        ) else if fs = "LTL_NEXT" then (
          let
            val (b1', b2', pf, dsThm) = addBindingFor b1 b2 (hd args) dsThm;
            val ds = dsExtractFromThm dsThm;
            val thm = TSPECL [(boolToHOL b1'), (boolToHOL b2'), ds, hd args, pf]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NEXT___eval;
            val thm = MP thm dsThm;
            val thm = SIMP_DS___BASIC thm;
            val thm = SIMP_DS___BINDINGS thm;
            val thm = SIMP_DS___USED_STATE_VARS thm
            val thm = SIMP_DS___FIRST_TRANSITION thm;
          in
            thm
          end
        ) else if fs = "LTL_PSNEXT" then (
          let
            val (b1', b2', pf, dsThm) = addBindingFor b1 b2 (hd args) dsThm;
            val ds = dsExtractFromThm dsThm;
            val thm = TSPECL [(boolToHOL b1'), (boolToHOL b2'), ds, hd args, pf]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSNEXT___eval;
            val thm = MP thm dsThm;
            val thm = SIMP_DS___BASIC thm;
            val thm = SIMP_DS___BINDINGS thm;
            val thm = SIMP_DS___USED_STATE_VARS thm
            val thm = SIMP_DS___FIRST_TRANSITION thm;
          in
            thm
          end
        ) else if fs = "LTL_PNEXT" then (
          let
            val (b1', b2', pf, dsThm) = addBindingFor b1 b2 (hd args) dsThm;
            val ds = dsExtractFromThm dsThm;
            val thm = TSPECL [(boolToHOL b1'), (boolToHOL b2'), ds, hd args, pf]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PNEXT___eval;
            val thm = MP thm dsThm;
            val thm = SIMP_DS___BASIC thm;
            val thm = SIMP_DS___BINDINGS thm;
            val thm = SIMP_DS___USED_STATE_VARS thm
            val thm = SIMP_DS___FIRST_TRANSITION thm;
          in
            thm
          end
        ) else if fs = "LTL_AND" then (
          let
            val args = strip_pair (hd args);
            val (l1, l2) = (el 1 args, el 2 args);
            val (b11, b12, pf1, dsThm) = addBindingFor b1 b2 l1 dsThm;
            val (b21, b22, pf2, dsThm) = addBindingFor b1 b2 l2 dsThm;
            val ds = dsExtractFromThm dsThm;
            val thm = TSPECL [ds, (boolToHOL b11), (boolToHOL b12), (boolToHOL b21), (boolToHOL b22), l1, l2, pf1, pf2]
              (CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_AND___eval);
            val thm = MP thm dsThm;
            val thm = SIMP_DS___BASIC thm;
            val thm = SIMP_DS___BINDINGS thm;
          in
            thm
          end
        ) else if fs = "LTL_OR" then (
          let
            val args = strip_pair (hd args);
            val (l1, l2) = (el 1 args, el 2 args);
            val (b11, b12, pf1, dsThm) = addBindingFor b1 b2 l1 dsThm;
            val (b21, b22, pf2, dsThm) = addBindingFor b1 b2 l2 dsThm;
            val ds = dsExtractFromThm dsThm;
            val thm = TSPECL [ds, (boolToHOL b11), (boolToHOL b12), (boolToHOL b21), (boolToHOL b22), l1, l2, pf1, pf2]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_OR___eval;
            val thm = MP thm dsThm;
            val thm = SIMP_DS___BASIC thm;
            val thm = SIMP_DS___BINDINGS thm;
          in
            thm
          end
        ) else if fs = "LTL_EQUIV" then (
          let
            val args = strip_pair (hd args);
            val (l1, l2) = (el 1 args, el 2 args);
            val (b11, b12, pf1, dsThm) = addBindingFor true true l1 dsThm;
            val (b21, b22, pf2, dsThm) = addBindingFor true true l2 dsThm;
            val ds = dsExtractFromThm dsThm;
            val thm = TSPECL [ds, l1, l2, pf1, pf2]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_EQUIV___eval;
            val thm = MP thm dsThm;
            val thm = SIMP_DS___BASIC thm;
            val thm = SIMP_DS___BINDINGS thm;
          in
            thm
          end
        ) else if fs = "LTL_SUNTIL" then (
          let
            val args = strip_pair (hd args);
            val (l1, l2) = (el 1 args, el 2 args);
            val (b11, b12, pf1, dsThm) = addBindingFor b1 b2 l1 dsThm;
            val (b21, b22, pf2, dsThm) = addBindingFor b1 b2 l2 dsThm;
            val ds = dsExtractFromThm dsThm;
            val thm = TSPECL [(boolToHOL b11), (boolToHOL b12), (boolToHOL b21),
              (boolToHOL b22), (boolToHOL b1)] CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_SUNTIL___eval;
            val thm = REWRITE_RULE [APPEND] thm;
            val thm = SPECL [ds, l1, l2, pf1, pf2] thm;
            val thm = MP thm dsThm;
            val thm = SIMP_DS___BASIC thm;
            val thm = SIMP_DS___BINDINGS thm;
            val thm = SIMP_DS___USED_STATE_VARS thm
            val thm = SIMP_DS___FIRST_TRANSITION thm;
          in
            thm
          end
        ) else if fs = "LTL_BEFORE" then (
          let
            val args = strip_pair (hd args);
            val (l1, l2) = (el 1 args, el 2 args);
            val (b11, b12, pf1, dsThm) = addBindingFor b1 b2 l1 dsThm;
            val (b21, b22, pf2, dsThm) = addBindingFor b2 b1 l2 dsThm;
            val ds = dsExtractFromThm dsThm;
            val thm = TSPECL [(boolToHOL b11), (boolToHOL b12), (boolToHOL b21),
              (boolToHOL b22), (boolToHOL b2)]               CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_BEFORE___eval;
            val thm = REWRITE_RULE [APPEND] thm;
            val thm = SPECL [ds, l1, l2, pf1, pf2] thm;
            val thm = MP thm dsThm;
            val thm = SIMP_DS___BASIC thm;
            val thm = SIMP_DS___BINDINGS thm;
            val thm = SIMP_DS___USED_STATE_VARS thm
            val thm = SIMP_DS___FIRST_TRANSITION thm;
          in
            thm
          end
        ) else if fs = "LTL_PBEFORE" then (
          let
            val args = strip_pair (hd args);
            val (l1, l2) = (el 1 args, el 2 args);
            val (b11, b12, pf1, dsThm) = addBindingFor b1 b2 l1 dsThm;
            val (b21, b22, pf2, dsThm) = addBindingFor b2 b1 l2 dsThm;
            val ds = dsExtractFromThm dsThm;
            val thm = TSPECL [(boolToHOL b11), (boolToHOL b12), (boolToHOL b21),
              (boolToHOL b22)]                             CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PBEFORE___eval;
            val thm = REWRITE_RULE [APPEND] thm;
            val thm = SPECL [ds, l1, l2, pf1, pf2] thm;
            val thm = MP thm dsThm;
            val thm = SIMP_DS___BASIC thm;
            val thm = SIMP_DS___BINDINGS thm;
            val thm = SIMP_DS___USED_STATE_VARS thm
            val thm = SIMP_DS___FIRST_TRANSITION thm;
          in
            thm
          end
        ) else if fs = "LTL_PSUNTIL" then (
          let
            val args = strip_pair (hd args);
            val (l1, l2) = (el 1 args, el 2 args);
            val (b11, b12, pf1, dsThm) = addBindingFor b1 b2 l1 dsThm;
            val (b21, b22, pf2, dsThm) = addBindingFor b1 b2 l2 dsThm;
            val ds = dsExtractFromThm dsThm;
            val thm = TSPECL [(boolToHOL b11), (boolToHOL b12), (boolToHOL b21),
              (boolToHOL b22), ds, l1, l2, pf1, pf2]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSUNTIL___eval;
            val thm = MP thm dsThm;
            val thm = SIMP_DS___BASIC thm;
            val thm = SIMP_DS___BINDINGS thm;
            val thm = SIMP_DS___USED_STATE_VARS thm
            val thm = SIMP_DS___FIRST_TRANSITION thm;
          in
            thm
          end
        ) else (
          let
            val _ = print "\n\n\n";
            val _ = print_term f;
            val _ = print "\n";
            val _ = print_term l;
            val _ = print "\n\n\n";
          in
            raise UnsupportedLTLTerm
          end
        )
      end;

  fun dsSingBindingExtractFromThm dsThm =
    let
      val ds = dsExtractFromThm dsThm;
      val set = el 6 (snd (strip_comb ds));
      val binding = hd (strip_set set);
      val hList = strip_pair binding;
      val (l, b1, b2, pf) = (el 1 hList, HOLToBool(el 2 hList), HOLToBool(el 3 hList), el 4 hList);
    in
      (ds, l, b1, b2, pf)
    end;

  local
    val compset = new_compset [MAP, APPEND_NIL,
      COND_CLAUSES, APPEND, ltl_to_gen_buechi_ds_REWRITES,
          NOT_CLAUSES, t_imp_elim_rwt, ADD_CLAUSES];
  in
    fun SIMP_DS___BODY___FORGET thm =
      let
        val thm = CONV_RULE (CBV_CONV compset) thm
        val thm = SIMP_DS___USED_VARS thm
        val thm = SIMP_DS___USED_STATE_VARS thm
      in
        thm
      end;
  end

  fun ltl2omega_internal3_forget b1 b2 l TSPECL =
      let
        fun extractFuncAndArgs l =
          let
            val (f, args) = strip_comb l;
            val (fs, _) = dest_const f;
          in
            (f, args, fs)
          end;
        val (f, args, fs) = extractFuncAndArgs l handle _ => (l, [], "ERROR");

        fun oneAncestor b1 b2 b11 b12 A thm =
          (let
            val dsThm = ltl2omega_internal3_forget b11 b12 A TSPECL;
            val (ds, l, _, _, pf) = dsSingBindingExtractFromThm dsThm;
            val thm = TSPECL [boolToHOL b1, boolToHOL b2, ds, l, pf]  thm;
            val thm = MP thm dsThm;
            val thm = SIMP_DS___BODY___FORGET thm;
          in
            thm
          end);

        fun twoAncestors b1 b2 b11 b12 b21 b22 aPair thm = (
          let
            val args = strip_pair (aPair);
            val (l1, l2) = (el 1 args, el 2 args);

            val ds1Thm = ltl2omega_internal3_forget b11 b12 l1 TSPECL;
            val ds2Thm = ltl2omega_internal3_forget b21 b22 l2 TSPECL;
            val (ds1, l1, _, _, pf1) = dsSingBindingExtractFromThm ds1Thm;
            val (ds2, l2, _, _, pf2) = dsSingBindingExtractFromThm ds2Thm;

            val thm = TSPECL [(boolToHOL b1), (boolToHOL b2), ds1, ds2, l1, l2, pf1, pf2] thm;
            val thm = MP thm ds1Thm;
            val thm = MP thm ds2Thm;
            val thm = SIMP_DS___BODY___FORGET thm;
          in
            thm
          end);
      in
        if fs = "LTL_PROP" then (
          let
            val thm = TSPECL [(boolToHOL b1), (boolToHOL b2), hd args]
              (CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PROP___forget_eval);
            val thm = SIMP_DS___USED_VARS thm
          in
            thm
          end
        ) else if fs = "LTL_NOT" then (
          oneAncestor b1 b2 b2 b1 (hd args) CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT___forget_eval
        ) else if fs = "LTL_NEXT" then (
          oneAncestor b1 b2 b1 b2 (hd args) CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NEXT___forget_eval
        ) else if fs = "LTL_PSNEXT" then (
          oneAncestor b1 b2 b1 b2 (hd args) CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSNEXT___forget_eval
        ) else if fs = "LTL_PNEXT" then (
          oneAncestor b1 b2 b1 b2 (hd args) CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PNEXT___forget_eval
        ) else if fs = "LTL_AND" then (
          twoAncestors b1 b2 b1 b2 b1 b2 (hd args) CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_AND___forget_eval
        ) else if fs = "LTL_EQUIV" then (
          twoAncestors b1 b2 true true true true (hd args) CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_EQUIV___forget_eval
        ) else if fs = "LTL_OR" then (
          twoAncestors b1 b2 b1 b2 b1 b2 (hd args) CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_OR___forget_eval
        ) else if fs = "LTL_SUNTIL" then (
          twoAncestors b1 b2 b1 b2 b1 b2 (hd args) CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_SUNTIL___forget_eval
        ) else if fs = "LTL_BEFORE" then (
          twoAncestors b1 b2 b1 b2 b2 b1 (hd args) CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_BEFORE___forget_eval
        ) else if fs = "LTL_PBEFORE" then (
          twoAncestors b1 b2 b1 b2 b2 b1 (hd args) CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PBEFORE___forget_eval
        ) else if fs = "LTL_PSUNTIL" then (
          twoAncestors b1 b2 b1 b2 b1 b2 (hd args) CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSUNTIL___forget_eval
        ) else (
          let
            val _ = print "\n\n\n";
            val _ = print_term f;
            val _ = print "\n";
            val _ = print_term l;
            val _ = print "\n\n\n";
          in
            raise UnsupportedLTLTerm
          end
        )
      end;


  fun ltl2omega_internal2_forget b1 b2 l TSPECL =
      let
        val thm = ltl2omega_internal3_forget b1 b2 l TSPECL;
        val thm = SIMP_RULE list_ss [INSERT_UNION_EQ,
          UNION_EMPTY] thm
      in
        thm
      end;

  val ltl_ss = std_ss ++ rewrites [LTL_ALWAYS_PALWAYS_ALTERNATIVE_DEFS,
        LTL_IMPL_def,
        LTL_COND_def,
        LTL_EVENTUAL_def,
        LTL_UNTIL_def,
        LTL_SBEFORE_def,
        LTL_WHILE_def,
        LTL_SWHILE_def,
        LTL_PEVENTUAL_def,
        LTL_PUNTIL_def,
        LTL_PSBEFORE_def,
        LTL_PWHILE_def,
        LTL_PSWHILE_def,
        LTL_INIT_def];

  val emptyDSThm = SIMP_RULE std_ss [EMPTY_LTL_TO_GEN_BUECHI_DS_def]
                             EMPTY_LTL_TO_GEN_BUECHI_DS___SEM;

  val basic_compset = new_compset [ltl_to_gen_buechi_ds_REWRITES,
                                   LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def]

  val final_compset = new_compset [LTL_TO_GEN_BUECHI_DS___A_NDET_def,
                                   LTL_TO_GEN_BUECHI_DS___A_UNIV_def,
                                   ltl_to_gen_buechi_ds_REWRITES,
                                   LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
                                   LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
                                   LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def,
                                   LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS_def,
                                   MAP]

in

  fun ltl2omega_internal fast b1 b2 t =
    let
      val ltl_type = hd (snd (dest_type (type_of t)));
      fun TSPECL t thm =
        SPECL t (INST_TYPE [alpha |-> ltl_type] thm);
      val dsThm = (INST_TYPE [alpha |-> ltl_type] emptyDSThm);
      val equiv_const = inst [alpha |-> ltl_type] ``LTL_EQUIVALENT:'a ltl -> 'a ltl -> bool``

      val equivTHM = CONGRUENCE_SIMP_CONV equiv_const ltl_nnf_cs ltl_ss [] t;

      val equivTHM = CONV_RULE (RAND_CONV (REWRITE_CONV [LTL_FALSE_def, LTL_TRUE_def])) equivTHM;
      val l = rand (concl (equivTHM));

      val thm = if fast then
                  ltl2omega_internal2_forget b1 b2 l TSPECL
                else
                  ltl2omega_internal2 b1 b2 l dsThm TSPECL;
      val thm = SIMP_DS___USED_VARS___DUPLICATES thm

      val ds = dsExtractFromThm thm;
      val dsB = dsBindingsExtractFromThm thm;
      val (b1', b2', pf) = (getBindingFor b1 b2 l dsB);
    in
      (l, equivTHM, thm, ds, pf, b1', b2')
    end;

    fun ltl2omega fast neg l =
      let
        val (typeString, ltl_type) = (dest_type (type_of l));
        val _ = if (typeString = "ltl") then T else raise NoLTLTerm;
        val ltl_type = hd (ltl_type);
        val (b1, b2) = if neg then (true, false) else (false, true);
        val (equivL, equivTHM, dsThm, ds, pf, b1', b2') = ltl2omega_internal fast b1 b2 l;

        val thm = if neg then LTL_TO_GEN_BUECHI_DS___SEM___MAX___eval else
                    LTL_TO_GEN_BUECHI_DS___SEM___MIN___eval;
        val a = if neg then b2' else b1';
        val thm = INST_TYPE [alpha |-> ltl_type] thm;
        val thm = SPECL [ds, l, equivL, pf, boolToHOL a] thm;
        val thm = MP thm dsThm
        val thm = MP thm equivTHM
        val thm = CONV_RULE (CBV_CONV basic_compset) thm
        val thm = SIMP_DS___BINDINGS thm
        val thm = CONV_RULE (CBV_CONV final_compset) thm
        val thm = SIMP_RULE std_ss [] thm
      in
        thm
      end;
end;

(* ltl_to_ks functions *)
local
  val final_compset_ks = new_compset [LTL_TO_GEN_BUECHI_DS___A_NDET_def,
                    LTL_TO_GEN_BUECHI_DS___A_UNIV_def,
                    ltl_to_gen_buechi_ds_REWRITES,
                    LTL_TO_GEN_BUECHI_DS___SEMI_AUTOMATON_def,
                    LTL_TO_GEN_BUECHI_DS___USED_STATE_VARS_def,
                    LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def,
                    LTL_TO_GEN_BUECHI_DS___FAIRNESS_CONSTRAINTS_def,
                    MAP, XP_NEXT_THM, XP_CURRENT_THM, P_BIGAND_def, XP_BIGAND_def];

  val final_compset_ks___product = new_compset [SYMBOLIC_KRIPKE_STRUCTURE_PRODUCT_def,
    symbolic_kripke_structure_REWRITES, SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def,
    UNION_EMPTY, P_USED_VARS_EVAL, XP_USED_VARS_EVAL, UNION_SING,
    INSERT_UNION_EQ, INSERT_INSERT];

  val special_CS = CSFRAG {rewrs  = [],
      relations = [],
      dprocs = [],
      congs  = [IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE_cong]};

  val basic_compset = new_compset [ltl_to_gen_buechi_ds_REWRITES,
                                   LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR_def];

  val final_cs = mk_congset [prop_logic_CS, xprop_logic_CS, special_CS];

in
  fun ltl_contradiction2ks_fair_emptyness fast l =
    let
      val (typeString, ltl_type) = (dest_type (type_of l));
      val _ = if (typeString = "ltl") then T else raise NoLTLTerm;
      val ltl_type = hd (ltl_type);
      val (equivL, equivTHM, dsThm, ds, pf, b1', b2') = ltl2omega_internal fast true false l;

      val thm = LTL_TO_GEN_BUECHI_DS___SEM___CONTRADICTION___KRIPKE_STRUCTURE___eval
      val thm = INST_TYPE [alpha |-> ltl_type] thm;
      val thm = SPECL [ds, l, equivL, pf, boolToHOL b2'] thm;
      val thm = MP thm dsThm
      val thm = MP thm equivTHM
      val thm = CONV_RULE (CBV_CONV basic_compset) thm
      val thm = SIMP_DS___BINDINGS thm
      val thm = CONV_RULE (CBV_CONV final_compset_ks) thm
      val thm = CONGRUENCE_SIMP_RULE final_cs std_ss [] thm
    in
      thm
    end;

  fun ltl_equivalent2ks_fair_emptyness fast l1 l2 =
    let
      val contr_thm = ISPECL [l1, l2] LTL_EQUIVALENT___TO___CONTRADICTION;
      val l = rand (rhs (concl contr_thm))
      val thm = ltl_contradiction2ks_fair_emptyness fast l
      val thm = REWRITE_RULE [GSYM contr_thm] thm
    in
      thm
    end;

  fun ltl_equivalent_initial2ks_fair_emptyness fast l1 l2 =
    let
      val contr_thm = ISPECL [l1, l2] LTL_EQUIVALENT_INITIAL___TO___CONTRADICTION;
      val l = rand (rhs (concl contr_thm))
      val thm = ltl_contradiction2ks_fair_emptyness fast l
      val thm = REWRITE_RULE [GSYM contr_thm] thm
    in
      thm
    end;

  fun ltl_ks_sem2ks_fair_emptyness___no_ks fast l =
    let
      val (typeString, ltl_type) = (dest_type (type_of l));
      val _ = if (typeString = "ltl") then T else raise NoLTLTerm;
      val ltl_type = hd (ltl_type);
      val (equivL, equivTHM, dsThm, ds, pf, b1', b2') = ltl2omega_internal fast false true l;

      val thm = LTL_TO_GEN_BUECHI_DS___KS_SEM___KRIPKE_STRUCTURE___eval
      val thm = INST_TYPE [alpha |-> ltl_type] thm;
      val thm = SPECL [ds, l, equivL, pf, boolToHOL b1'] thm;
      val thm = MP thm dsThm
      val thm = MP thm equivTHM
      val thm = CONV_RULE (CBV_CONV basic_compset) thm
      val thm = SIMP_DS___BINDINGS thm
      val thm = CONV_RULE (CBV_CONV final_compset_ks) thm
      val thm = SIMP_RULE std_ss [] thm
    in
      thm
    end;

  fun ltl_ks_sem2ks_fair_emptyness fast l M =
    let
      val thm = ltl_ks_sem2ks_fair_emptyness___no_ks fast l;
      val thm = SPEC M thm;
      val thm = CONV_RULE (CBV_CONV final_compset_ks___product) thm
      val thm = CONGRUENCE_SIMP_RULE final_cs std_ss [] thm
    in
      thm
    end;
end;

(* ltl_to_ks num functions *)
local
  val used_vars_compset =
    new_compset [LTL_USED_VARS_EVAL,
                 P_USED_VARS_EVAL,
                 XP_USED_VARS_EVAL,
                 SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def,
                 symbolic_kripke_structure_REWRITES,
                 UNION_EMPTY,
                 UNION_SING, INSERT_UNION_EQ]

  val renaming_to_num_compset =
    new_compset [LTL_VAR_RENAMING_EVAL, P_VAR_RENAMING_EVAL]

  val renaming_to_num_compset_ks =
    new_compset [LTL_VAR_RENAMING_EVAL, P_VAR_RENAMING_EVAL,
                 SYMBOLIC_KRIPKE_STRUCTURE_VAR_RENAMING_def,
                 P_VAR_RENAMING_EVAL, XP_VAR_RENAMING_EVAL,
                 symbolic_kripke_structure_REWRITES]

  val pred_set_forall_compset =
    new_compset [
                res_quanTheory.RES_FORALL_EMPTY,
                RES_FORALL_INSERT,
                prove (``!x:num n:num. x + n >= n``, DECIDE_TAC),
                AND_CLAUSES]

  val inj_thm_compset =
    new_compset [MEM, OR_CLAUSES, IN_INSERT, NOT_IN_EMPTY, IMP_CLAUSES]

  val all_distinct_compset =
    new_compset [ALL_DISTINCT, AND_CLAUSES, MEM, OR_CLAUSES,DE_MORGAN_THM, NOT_CLAUSES]

  fun enum_list n [] = []
    | enum_list n (h::l) = ((n, h)::(enum_list (n+1) l))

  val ks_var_renaming_compset =
    new_compset [MAP, SYMBOLIC_KRIPKE_STRUCTURE_VAR_RENAMING_def,
                 symbolic_kripke_structure_REWRITES,
                 P_VAR_RENAMING_EVAL, XP_VAR_RENAMING_EVAL]


  fun ks_fair_emptyness___num___initial thm num_thm ltl_type =
    let
      val used_vars_term = rand (rator (rand (rator (body (rand (concl thm))))));
      val num_thm = GSYM (UNDISCH (SPEC_ALL num_thm));

      val thm = ISPEC ``\n:num. n`` thm
      val thm = REWRITE_RULE [num_thm, IS_ELEMENT_ITERATOR___ID] thm
      val thm = DISCH_ALL thm;
      val thm = CONV_RULE (RATOR_CONV (CBV_CONV used_vars_compset)) thm

      val f_term = rand (rator (rator (rand (rator ((concl thm))))))
      val thm = GEN f_term thm
      val new_f_term = ``\x. ((f:'a->num) x) + n``;
      val new_f_term = inst [alpha |-> ltl_type] new_f_term;
      val new_f_term = subst [(``n:num`` |-> used_vars_term),
                              ((mk_var ("f", ltl_type --> num)) |-> f_term)] new_f_term;
      val thm = SPEC new_f_term thm
      val thm = CONV_RULE (RAND_CONV (RATOR_CONV (CBV_CONV pred_set_forall_compset))) thm
      val thm = REWRITE_RULE [INJ___ADD_FUNC] thm
      val thm = BETA_RULE thm
      val thm = CONV_RULE (RATOR_CONV (SETIFY_CONV)) thm;
      val thm = GEN f_term thm

    in
      (thm, ltl_type, int_of_term used_vars_term)
    end;


fun ks_fair_emptyness___num___eq thm ltl_type used_vars_num =
  let
    val var_set_term = rand (rator (rand (rator (body (rand (concl thm))))));
    val var_list = strip_set var_set_term;
    val var_list_term = listSyntax.mk_list (var_list, ltl_type);

    val pos_start_term = ``\x:'a. PRE (POS_START (0:num) (l:'a list) x)``;
    val pos_start_term = inst [alpha |-> ltl_type] pos_start_term
    val pos_start_term = subst [mk_var("l", type_of var_list_term) |-> var_list_term] pos_start_term;

    val thm = SPEC pos_start_term thm

    val inj_thm = INJ_POS_START___MP_HELPER;
    val inj_thm = ISPECL [var_list_term, var_set_term, ``0:num``] inj_thm
    val inj_thm = CONV_RULE (RATOR_CONV (RAND_CONV (CBV_CONV inj_thm_compset))) inj_thm
    val inj_thm = UNDISCH (REWRITE_RULE [] inj_thm)


    val pos_start_term_concr = ``PRE (POS_START (0:num) (l:'a list) (x:'a))``;
    val pos_start_term_concr = inst [alpha |-> ltl_type] pos_start_term_concr;
    val pos_start_term_concr = subst [mk_var("l", type_of var_list_term) |-> var_list_term] pos_start_term_concr
    val pos_start_thm_concr = REWRITE_CONV [PRE_POS_START___REWRITES] pos_start_term_concr;
    val pos_start_thm_concr = REDUCE_RULE pos_start_thm_concr;
    val pos_start_thm_concr = GEN (mk_var ("x", ltl_type)) pos_start_thm_concr;

    val inj_pos_start_thm_list = map (fn x => (SPEC x pos_start_thm_concr)) var_list;
    val inj_pos_start_thm = LIST_CONJ inj_pos_start_thm_list;

    val all_distinct_term = hd (hyp inj_thm);
    val all_distinct_eval_thm = CBV_CONV all_distinct_compset all_distinct_term;

    val inj_pos_start_thm = ADD_ASSUM (rhs (concl all_distinct_eval_thm)) inj_pos_start_thm
    val inj_pos_start_thm = ASM_REWRITE_RULE [] inj_pos_start_thm
    val inj_pos_start_thm = DISCH_ALL inj_pos_start_thm
    val inj_pos_start_thm = REWRITE_RULE [GSYM all_distinct_eval_thm] inj_pos_start_thm
    val inj_pos_start_thm = UNDISCH_ALL inj_pos_start_thm

    val thm = BETA_RULE thm
    val thm = REWRITE_RULE [inj_thm, inj_pos_start_thm] thm
    val thm = REDUCE_RULE thm
    val thm = DISCH_ALL thm
  in
    (thm, enum_list used_vars_num var_list)
  end

fun ks_fair_emptyness___num___impl thm ltl_type used_vars_num =
  let
    val var_set_term = rand (rator (rand (rator (body (rand (concl thm))))));
    val var_list = strip_set var_set_term;
    val var_list_term = listSyntax.mk_list (var_list, ltl_type);


    val f_term = bvar(rand (concl thm))
    val rewrite = map (fn p => (mk_comb(f_term, snd p) |-> term_of_int (fst p))) (enum_list 0 var_list)
    val is_empty_ks_term = rhs (rand (body (rand (concl thm))));
    val is_empty_ks_term = subst rewrite is_empty_ks_term

    val renaming_cond = ``\x:num. (if (x = n:num) then (((f:'a->num) e) + y:num) else (m:num->num) x)``;
    val renaming_cond = inst [alpha |-> ltl_type] renaming_cond;

    val renaming_list = (enum_list used_vars_num var_list)
    fun renaming_fun ((n, t), et) =
      (subst [(mk_var("f", ltl_type --> num) |-> f_term),
              (mk_var("y", num) |-> term_of_int used_vars_num),
              (mk_var("n", num) |-> term_of_int n),
              (mk_var("e", ltl_type) |-> t),
              (mk_var("m", num --> num) |-> et)] renaming_cond)
    val renaming_term = foldr renaming_fun ``\x:num. x`` renaming_list

    val (term, fc) = dest_comb is_empty_ks_term;
    val ks = rand term;

    val imp_thm = IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE___IDENTIFY_VARIABLES;
    val imp_thm = ISPECL [renaming_term, ks, fc] imp_thm
    val imp_thm = BETA_RULE imp_thm
    val imp_thm = CONV_RULE (CBV_CONV ks_var_renaming_compset) imp_thm
    (*if there are no variables, do not apply REDUCE_RULE, because then
      the theorem is of the form X ==> X and will be simplified to T*)
    val lhs = rand (rator (concl imp_thm))
    val rhs = rand (concl imp_thm)
    val imp_thm = if (lhs ~~ rhs) then imp_thm else REDUCE_RULE imp_thm

    val thm = SPEC_ALL thm
    val thm = UNDISCH thm
    val thm = REDUCE_RULE thm (*because x + 0 may have been reduced to x in imp_thm*)
    val thm = CONV_RULE (RAND_CONV (REWRITE_CONV [GSYM thm])) imp_thm
    val thm = DISCH_ALL thm
    val thm = GEN f_term thm
    val thm = SIMP_RULE std_ss [LEFT_FORALL_IMP_THM] thm

    val inj_exists_term = rand (rator (concl thm));
    val inj_exists_thm = prove (inj_exists_term,
                                MATCH_MP_TAC NUM_FINITE_INJ_EXISTS THEN
                                REWRITE_TAC[FINITE_INSERT, FINITE_EMPTY])
    val thm = REWRITE_RULE [inj_exists_thm] thm
  in
    (thm, enum_list used_vars_num var_list)
  end

  fun ks_fair_emptyness___num mode thm num_thm ltl_type =
    let
      val (thm, ltl_type, used_vars_num) = ks_fair_emptyness___num___initial thm num_thm ltl_type
    in
      if (mode = 1) then
        ks_fair_emptyness___num___eq thm ltl_type used_vars_num
      else if mode = 2 then
        ks_fair_emptyness___num___impl thm ltl_type used_vars_num
      else
        let
          val (impl_thm, vl) = ks_fair_emptyness___num___impl thm ltl_type used_vars_num
          val (eq_thm, _) = ks_fair_emptyness___num___eq thm ltl_type used_vars_num
        in
          (CONJ eq_thm impl_thm, vl)
        end
    end

in

  fun ltl_contradiction2ks_fair_emptyness___num mode fast l =
    let
      val (typeString, ltl_type) = (dest_type (type_of l));
      val _ = if (typeString = "ltl") then T else raise NoLTLTerm;
      val ltl_type = hd (ltl_type);

      val num_thm = INST_TYPE [beta |-> num] LTL_CONTRADICTION___VAR_RENAMING;
      val num_thm = ISPEC l num_thm;
      val num_thm = CONV_RULE (CBV_CONV renaming_to_num_compset) num_thm;
      val num_l = rand (rhs (rand (body (rand (concl num_thm)))));
      val thm = ltl_contradiction2ks_fair_emptyness fast num_l

    in
      ks_fair_emptyness___num mode thm num_thm ltl_type
    end


  fun ltl_equivalent2ks_fair_emptyness___num mode fast l1 l2 =
    let
      val contr_thm = ISPECL [l1, l2] LTL_EQUIVALENT___TO___CONTRADICTION;
      val l = rand (rhs (concl contr_thm))
      val (thm, l) = ltl_contradiction2ks_fair_emptyness___num mode fast l
      val thm = REWRITE_RULE [GSYM contr_thm] thm
    in
      (thm, l)
    end;

  fun ltl_equivalent_initial2ks_fair_emptyness___num mode fast l1 l2 =
    let
      val contr_thm = ISPECL [l1, l2] LTL_EQUIVALENT_INITIAL___TO___CONTRADICTION;
      val l = rand (rhs (concl contr_thm))
      val (thm, l) = ltl_contradiction2ks_fair_emptyness___num mode fast l
      val thm = REWRITE_RULE [GSYM contr_thm] thm
    in
      (thm, l)
    end;

  fun ltl_ks_sem2ks_fair_emptyness___num mode fast l M =
    let
      val (typeString, ltl_type) = (dest_type (type_of l));
      val _ = if (typeString = "ltl") then T else raise NoLTLTerm;
      val ltl_type = hd (ltl_type);

      val num_thm = INST_TYPE [beta |-> num] LTL_KS_SEM___VAR_RENAMING;
      val num_thm = ISPECL [l, M] num_thm;
      val num_thm = CONV_RULE (CBV_CONV renaming_to_num_compset_ks) num_thm;
      val num_l = rand (rhs (rand (body (rand (concl num_thm)))))
      val num_M = rand (rator (rhs (rand (body (rand (concl num_thm))))))

      val thm = ltl_ks_sem2ks_fair_emptyness fast num_l num_M
    in
      ks_fair_emptyness___num mode thm num_thm ltl_type
    end
end;


(*********************************************************************************
 * PSL stuff
 ********************************************************************************)

(*Given a PSL Term t, this function replaces all functions in t by its definition.
  Thenit tries to prove that t is CLOCK_SERE_FREE and finally calculates the a
  translation of t to ltl*)

local

  exception NOT_CLOCK_SERE_FREE;

in

  fun prepare_psl_term t =
    let
      val eval_thm = EVAL_CONV t
      val cs_free_term = liteLib.mk_icomb (``F_CLOCK_SERE_FREE:'a fl->bool``, t);
      val cs_free_thm = ((REWRITE_CONV [eval_thm]) THENC (REWRITE_CONV [ F_CLOCK_SERE_FREE_def, F_CLOCK_FREE_def, F_SERE_FREE_def])) cs_free_term;
      val _ = if ((rhs (concl cs_free_thm)) ~~ T) then true else (
        let
          val _ = print "! ERROR: Could not prove that\n! ";
          val _ = print_term t;
          val _ = print "\n! contains no clocks or seres. Intermediate theorem:\n\n";
          val _ = print_thm cs_free_thm;
          val _ = print "\n\n";
        in
          raise NOT_CLOCK_SERE_FREE
        end);
      val cs_free_thm = ONCE_REWRITE_RULE [] cs_free_thm;

      val ltl_term = liteLib.mk_icomb (``PSL_TO_LTL:'a fl->'a ltl``, t);
      val ltl_thm = (REWRITE_CONV [eval_thm] THENC REWRITE_CONV[PSL_TO_LTL_def,
        RLTL_TO_LTL_def, PSL_TO_RLTL_def, BEXP_TO_PROP_LOGIC_def]) ltl_term;

      val ltl = rhs (concl ltl_thm);
    in
      (eval_thm, cs_free_thm, ltl_thm, ltl)
    end;

end;

fun psl_contradiction2ks_fair_emptyness fast f =
    let
      val (eval_thm, cs_free_thm, ltl_thm, l) = prepare_psl_term f;
      val to_ltl_thm = ISPEC f PSL_TO_LTL___UF_CONTRADICTION;
      val to_ltl_thm = MP to_ltl_thm cs_free_thm

      val thm = ltl_contradiction2ks_fair_emptyness fast l
      val thm = REWRITE_RULE [GSYM ltl_thm, GSYM to_ltl_thm] thm
    in
      thm
    end

fun psl_contradiction2ks_fair_emptyness___num mode fast f =
    let
      val (eval_thm, cs_free_thm, ltl_thm, l) = prepare_psl_term f;
      val to_ltl_thm = ISPEC f PSL_TO_LTL___UF_CONTRADICTION;
      val to_ltl_thm = MP to_ltl_thm cs_free_thm

      val (thm, uv) = ltl_contradiction2ks_fair_emptyness___num mode fast l
      val thm = REWRITE_RULE [GSYM ltl_thm, GSYM to_ltl_thm] thm
    in
      (thm, uv)
    end

fun psl_ks_sem2ks_fair_emptyness___no_ks fast f =
    let
      val (eval_thm, cs_free_thm, ltl_thm, l) = prepare_psl_term f;
      val to_ltl_thm = ISPEC ``M:'b symbolic_kripke_structure`` PSL_TO_LTL___UF_KS_SEM;
      val to_ltl_thm = ISPEC f to_ltl_thm;
      val to_ltl_thm = MP to_ltl_thm cs_free_thm

      val thm = ltl_ks_sem2ks_fair_emptyness___no_ks fast l
      val thm = REWRITE_RULE [GSYM ltl_thm, GSYM to_ltl_thm] thm
    in
      thm
    end

fun psl_ks_sem2ks_fair_emptyness fast f M =
    let
      val (eval_thm, cs_free_thm, ltl_thm, l) = prepare_psl_term f;
      val to_ltl_thm = ISPECL [M, f] PSL_TO_LTL___UF_KS_SEM;
      val to_ltl_thm = MP to_ltl_thm cs_free_thm

      val thm = ltl_ks_sem2ks_fair_emptyness fast l M
      val thm = REWRITE_RULE [GSYM ltl_thm, GSYM to_ltl_thm] thm
    in
      thm
    end

fun psl_ks_sem2ks_fair_emptyness___num mode fast f M =
    let
      val (eval_thm, cs_free_thm, ltl_thm, l) = prepare_psl_term f;
      val to_ltl_thm = ISPECL [M, f] PSL_TO_LTL___UF_KS_SEM;
      val to_ltl_thm = MP to_ltl_thm cs_free_thm

      val (thm, uv) = ltl_ks_sem2ks_fair_emptyness___num mode fast l M
      val thm = REWRITE_RULE [GSYM ltl_thm, GSYM to_ltl_thm] thm
    in
      (thm, uv)
    end

fun psl_equivalent2ks_fair_emptyness fast f1 f2 =
  let
    val (eval_thm1, cs_free_thm1, ltl_thm1, _) = prepare_psl_term f1;
    val (eval_thm2, cs_free_thm2, ltl_thm2, _) = prepare_psl_term f2;

    val to_ltl_thm = ISPECL [f1, f2] PSL_TO_LTL___UF_EQUIVALENT;
    val to_ltl_thm = MP to_ltl_thm cs_free_thm1
    val to_ltl_thm = MP to_ltl_thm cs_free_thm2
    val to_ltl_thm = ONCE_REWRITE_RULE [ltl_thm1, ltl_thm2] to_ltl_thm
    val l = rand (rhs (concl to_ltl_thm))

    val thm = ltl_contradiction2ks_fair_emptyness fast l
    val thm = REWRITE_RULE [GSYM to_ltl_thm] thm

  in
    thm
  end;

fun psl_equivalent2ks_fair_emptyness___num mode fast f1 f2 =
  let
    val (eval_thm1, cs_free_thm1, ltl_thm1, _) = prepare_psl_term f1;
    val (eval_thm2, cs_free_thm2, ltl_thm2, _) = prepare_psl_term f2;

    val to_ltl_thm = ISPECL [f1, f2] PSL_TO_LTL___UF_EQUIVALENT;
    val to_ltl_thm = MP to_ltl_thm cs_free_thm1
    val to_ltl_thm = MP to_ltl_thm cs_free_thm2
    val to_ltl_thm = ONCE_REWRITE_RULE [ltl_thm1, ltl_thm2] to_ltl_thm
    val l = rand (rhs (concl to_ltl_thm))

    val (thm, uv) = ltl_contradiction2ks_fair_emptyness___num mode fast l
    val thm = REWRITE_RULE [GSYM to_ltl_thm] thm

  in
    (thm, uv)
  end;

end
