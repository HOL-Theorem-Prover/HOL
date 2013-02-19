structure stateLib :> stateLib =
struct

open HolKernel boolLib bossLib
open lcsymtacs updateLib utilsLib
open stateTheory
open progSyntax

infix \\
val op \\ = op THEN;

val ERR = Feedback.mk_HOL_ERR "stateLib"

(* Some syntax functions *)

fun mk_state_pred x =
   pred_setSyntax.mk_set [pred_setSyntax.mk_set [pairSyntax.mk_pair x]]

(* ------------------------------------------------------------------------
   update_frame_state_thm: Generate theorems of the form

   !a w s x.
      f a IN x ==> (FRAME_STATE m x (u s a w) = FRAME_STATE m x (r s))

   where "u" is a state update function.
   ------------------------------------------------------------------------ *)

local
   fun tac t = Cases THEN SRW_TAC [] [t, combinTheory.APPLY_UPDATE_THM]
   fun frame_state_thm def (f, u, r) =
      let
         val n = utilsLib.get_function def
         val thm =
            UPDATE_FRAME_STATE
            |> Drule.ISPEC n
            |> Q.ISPECL [f, u, r]
            |> SIMP_RULE (srw_ss()) []
         val p = fst (boolSyntax.dest_imp (Thm.concl thm))
         val p_thm = Tactical.prove (p, tac def)
      in
         Drule.GEN_ALL (MATCH_MP thm p_thm)
      end
in
   fun update_frame_state_thm proj_def =
      Drule.LIST_CONJ o
      List.map (Feedback.trace ("notify type variable guesses", 0)
                  (frame_state_thm proj_def))
end

(* ------------------------------------------------------------------------
   star_select_state_thm: Generate theorems of the form

   !cd m p s x.
      ({cd} * p) (SELECT_STATE m x s) =
      (!c d. (c, d) IN cd ==> (m s c = d)) /\ IMAGE FST cd SUBSET x /\
      p (SELECT_STATE m (x DIFF IMAGE FST cd) s)

   pool_select_state_thm: Generate theorems of the form

   !cd m p s x.
      {cd} (SELECT_STATE m x s) =
      (!c d. (c, d) IN cd ==> (m s c = d)) /\ IMAGE FST cd SUBSET x /\
      (x DIFF IMAGE FST cd = {})

   ------------------------------------------------------------------------ *)

local
   val EXPAND_lem = Q.prove(
      `!x y m s c.
          (!c d. (c, d) IN set (x :: y) ==> (m s c = d)) =
          (!c d. ((c, d) = x) ==> (m s c = d)) /\
          (!c d. ((c, d) IN set y) ==> (m s c = d))`,
      SRW_TAC [] [] \\ utilsLib.qm_tac [])
   val EXPAND_lem2 = Q.prove(
      `!x y m s c.
          (!c d. (c, d) IN x INSERT y ==> (m s c = d)) =
          (!c d. ((c, d) = x) ==> (m s c = d)) /\
          (!c d. ((c, d) IN y) ==> (m s c = d))`,
      SRW_TAC [] [] \\ utilsLib.qm_tac [])
   val emp_thm =
      set_sepTheory.SEP_CLAUSES
      |> Drule.SPEC_ALL
      |> Drule.CONJUNCTS
      |> List.last
in
   fun star_select_state_thm proj_def thms (l, thm) =
      let
         val proj_tm = utilsLib.get_function proj_def
         val tm = thm |> Thm.concl |> boolSyntax.strip_forall |> snd
                      |> boolSyntax.rhs |> pred_setSyntax.strip_set |> List.hd
         val tm_thm = (REWRITE_CONV thms THENC Conv.CHANGED_CONV EVAL) tm
                      handle HOL_ERR {origin_function = "CHANGED_CONV", ...} =>
                         combinTheory.I_THM
      in
         STAR_SELECT_STATE
         |> Drule.ISPECL ([tm, proj_tm] @ l)
         |> Conv.CONV_RULE (Conv.STRIP_QUANT_CONV
               (Conv.FORK_CONV
                   (REWRITE_CONV [GSYM thm, emp_thm],
                    REWRITE_CONV [tm_thm, EXPAND_lem, EXPAND_lem2]
                    THENC SIMP_CONV (srw_ss()) [proj_def, emp_SELECT_STATE])))
         |> Drule.GEN_ALL
      end
   fun pool_select_state_thm proj_def thms instr_def =
      let
         val tm = utilsLib.get_function proj_def
         val ty = utilsLib.rng (Term.type_of tm)
         val ty =
            (pairSyntax.mk_prod (Type.dom_rng ty) --> Type.bool) --> Type.bool
         val emp = Term.mk_const ("emp", ty)
      in
         star_select_state_thm proj_def thms ([emp], instr_def)
      end
end

(* ------------------------------------------------------------------------
   sep_definitions sthy expnd thm

   Generate a state component map for a given next state function, where

   sthy: name of model (used as a prefix tag), e.g. "x86"
   expnd: specifies which record components should be expanded
          (be given separate component names). For example, [["CPSR"]]
   thm: the next state function
   ------------------------------------------------------------------------ *)

local
   fun def_suffix s = s ^ "_def"

   val comp_names =
      List.map (def_suffix o fst o Term.dest_const o utilsLib.get_function)

   fun mk_state_var ty = Term.mk_var ("s", ty)

   fun make_component_name sthy =
      String.concat o Lib.cons (sthy ^ "_c_") o Lib.separate "_" o List.rev

   fun make_assert_name sthy tm =
      sthy ^ String.extract (fst (Term.dest_const tm),
                             String.size sthy + 2, NONE)

   fun component (n, ty) =
      case Lib.total Type.dom_rng ty of
         SOME (d, r) => ((n, [ParseDatatype.dAQ d]), r)
       | NONE => ((n, []), ty)

   fun build_names (sthy, expnd, sty) =
      let
         val s = mk_state_var sty
         fun loop (x as ((path, ty), tm), es) =
            case Lib.total TypeBase.fields_of ty of
               NONE => [x]
             | SOME [] => [x]
             | SOME l =>
               let
                  val l = ListPair.zip (l, utilsLib.accessor_fns ty)
                  val (nd, dn) =
                     List.foldl
                        (fn ((x as ((n, t), f)), (nd, dn)) =>
                           let
                              val es' =
                                 es
                                 |> List.filter
                                      (Lib.equal (SOME n) o
                                       Lib.total List.hd)
                                 |> List.map List.tl
                              val y = ((n :: path, t), Term.mk_comb (f, tm))
                           in
                              if List.null es'
                                 then (nd, y :: dn)
                              else ((y, es') :: nd, dn)
                           end) ([], []) l
               in
                  dn @ List.concat (List.map loop nd)
               end
         val (l1, tms) = ListPair.unzip (loop ((([], sty), s), expnd))
         val (components, data) =
            ListPair.unzip
              (List.map (component o (make_component_name sthy ## Lib.I)) l1)
      in
         (components, Lib.mk_set data, tms)
      end

   fun data_constructor ty =
      case Type.dest_thy_type ty of
         {Thy = "fcp", Args = [_, n], Tyop = "cart"} =>
            "word" ^ Arbnum.toString (fcpSyntax.dest_numeric_type n)
       | {Thy = "min", Args = [a, b], Tyop = "fun"} =>
            data_constructor a ^ "_to_" ^ data_constructor b
       | {Thy = "pair", Args = [a, b], Tyop = "prod"} =>
            data_constructor a ^ "_X_" ^ data_constructor b
       | {Thy = "option", Args = [a], Tyop = "option"} =>
            data_constructor a ^ "_option"
       | {Thy = "list", Args = [a], Tyop = "list"} =>
            data_constructor a ^ "_list"
       | {Args = [], Tyop = s, ...} => s
       | _ => raise ERR "data_constructor" "incompatible type"

   fun define_assert0 sthy pred_ty (tm1, tm2) =
      let
         val dty = utilsLib.dom (Term.type_of tm2)
         val d = Term.mk_var ("d", dty)
         val tm_d = Term.mk_comb (tm2, d)
         val s = make_assert_name sthy tm1
         val l = Term.mk_comb (Term.mk_var (s, dty --> pred_ty), d)
         val r = mk_state_pred (tm1, tm_d)
      in
         Definition.new_definition (def_suffix s, boolSyntax.mk_eq (l, r))
      end

   fun define_assert1 sthy pred_ty (tm1, tm2) =
      let
         val (tm1, v, vty) =
            case Term.free_vars tm1 of
               [v] => let
                         val vty = Term.type_of v
                         val fv = Term.mk_var ("c", vty)
                      in
                         (Term.subst [v |-> fv] tm1, fv, vty)
                      end
             | _ => raise ERR "define_assert1" "expecting single free var"
         val dty = utilsLib.dom (Term.type_of tm2)
         val d = Term.mk_var ("d", dty)
         val tm_d = Term.mk_comb (tm2, d)
         val s = make_assert_name sthy (fst (boolSyntax.strip_comb tm1))
         val l =
            Term.list_mk_comb (Term.mk_var (s, vty --> dty --> pred_ty), [v, d])
         val r = mk_state_pred (tm1, tm_d)
      in
         Definition.new_definition (def_suffix s, boolSyntax.mk_eq (l, r))
      end
in
   fun sep_definitions sthy expnd thm =
      let
         val next_tm = utilsLib.get_function thm
         val state_ty = utilsLib.dom (Term.type_of next_tm)
         val (components, data, tms) = build_names (sthy, expnd, state_ty)
         fun dc ty = sthy ^ "_d_" ^ data_constructor ty
         val data_cons = List.map (fn d => (dc d, [ParseDatatype.dAQ d])) data
         val s_c = sthy ^ "_component"
         val s_d = sthy ^ "_data"
         val () = Datatype.astHol_datatype
                    [(s_c, ParseDatatype.Constructors components)]
         val () = Datatype.astHol_datatype
                    [(s_d, ParseDatatype.Constructors data_cons)]
         val cty = Type.mk_type (s_c, [])
         val dty = Type.mk_type (s_d, [])
         val pred_ty =
            pred_setSyntax.mk_set_type
               (pred_setSyntax.mk_set_type (pairSyntax.mk_prod (cty, dty)))
         fun mk_dc ty = Term.mk_const (dc ty, ty --> dty)
         val n = ref 0
         val a0 = define_assert0 sthy pred_ty
         val a1 = define_assert1 sthy pred_ty
         val define_component =
            fn ((s, []), tm) =>
                let
                   val tm1 = Term.mk_const (s, cty)
                   val tm2 = mk_dc (type_of tm)
                in
                   ((tm1, Term.mk_comb (tm2, tm)), a0 (tm1, tm2))
                end
             | ((s, [a]), tm) =>
                let
                   val aty = ParseDatatype.pretypeToType a
                   val v = Term.mk_var ("v" ^ Int.toString (!n), aty)
                   val tm_v = Term.mk_comb (tm, v)
                   val bty = utilsLib.rng (Term.type_of tm)
                   val () = Portable.inc n
                   val tm1 = Term.mk_comb (Term.mk_const (s, aty --> cty), v)
                   val tm2 = mk_dc (Term.type_of tm_v)
                in
                   ((tm1, Term.mk_comb (tm2, tm_v)), a1 (tm1, tm2))
                end
             | _ => raise ERR "define_component" "too many arguments"
         val l = List.map define_component (ListPair.zip (components, tms))
         val (cs, defs) = ListPair.unzip l
         val proj_r = TypeBase.mk_pattern_fn cs
         val proj_s = sthy ^ "_proj"
         val proj_f = Term.mk_var (proj_s, state_ty --> cty --> dty)
         val proj_l = Term.mk_comb (proj_f, mk_state_var state_ty)
         val proj_def =
            Definition.new_definition
               (sthy ^ "_proj_def", boolSyntax.mk_eq (proj_l, proj_r))
         val () =
            Theory.adjoin_to_theory
               {sig_ps =
                  SOME (fn ppstrm =>
                           PP.add_string ppstrm "val component_defs: thm list"),
                struct_ps =
                  SOME (fn ppstrm =>
                          (PP.add_string ppstrm "val component_defs = ["
                           ; PP.begin_block ppstrm PP.INCONSISTENT 0
                           ; Portable.pr_list
                                 (PP.add_string ppstrm)
                                 (fn () => PP.add_string ppstrm ",")
                                 (fn () => PP.add_break ppstrm (1, 0))
                                 (comp_names defs)
                           ; PP.add_string ppstrm "]"
                           ; PP.end_block ppstrm
                           ; PP.add_newline ppstrm))}
      in
         proj_def :: defs
      end
end

(* ------------------------------------------------------------------------
   mk_code_pool: make term ``CODE_POOL f {(v, opc)}``
   ------------------------------------------------------------------------ *)

local
   val code_pool_tm = Term.prim_mk_const {Thy = "prog", Name = "CODE_POOL"}
in
   fun mk_code_pool (f, v, opc) =
      let
         val x = pred_setSyntax.mk_set [pairSyntax.mk_pair (v, opc)]
      in
         boolSyntax.list_mk_icomb (code_pool_tm, [f, x])
      end
      handle HOL_ERR {message, ...} => raise ERR "mk_code_pool" message
end

(* ------------------------------------------------------------------------
   list_mk_code_pool: make term ``CODE_POOL f {(v, [opc0, ...])}``
   ------------------------------------------------------------------------ *)

fun list_mk_code_pool (f, v, l) =
   mk_code_pool (f, v, listSyntax.mk_list (l, Term.type_of (hd l)))

(* ------------------------------------------------------------------------
   is_code_access:
   test if term is of the form ``s.mem v`` or ``s.mems (v + x)``
   ------------------------------------------------------------------------ *)

fun is_code_access (s, v) tm =
   case boolSyntax.dest_strip_comb tm of
      (c, [_, a]) =>
         c = s andalso
         (a = v orelse
            (case Lib.total wordsSyntax.dest_word_add a of
                SOME (x, y) => x = v andalso wordsSyntax.is_word_literal y
              | NONE => false))
    | _ => false

(* ------------------------------------------------------------------------
   dest_code_access:
   ``s.mem a = r``       -> (0, ``r``)
   ``s.mem (a + i) = r`` -> (i, ``r``)
   ------------------------------------------------------------------------ *)

fun dest_code_access tm =
   let
      val (l, r) = boolSyntax.dest_eq tm
      val a = boolSyntax.rand l
      val a = case Lib.total (snd o wordsSyntax.dest_word_add) a of
                 SOME x => wordsSyntax.uint_of_word x
               | NONE => 0
   in
      (a, case Lib.total optionSyntax.dest_some r of SOME v => v | NONE => r)
   end

(* ------------------------------------------------------------------------
   read_footprint proj_def comp_defs cpool extras

   Generate a map from step-theorem to

      (component pre-conditions,
       code-pool,
       Boolean pre-condition,
       processed next-state term)

   ------------------------------------------------------------------------ *)

local
   val vnum =
      ref (Redblackmap.mkDict String.compare : (string, int) Redblackmap.dict)
in
   fun gvar s ty =
      let
         val i = case Redblackmap.peek (!vnum, s) of
                    SOME i => (vnum := Redblackmap.insert (!vnum, s, i + 1)
                               ; Int.toString i)
                  | NONE => (vnum := Redblackmap.insert (!vnum, s, 0); "")
      in
         Term.mk_var (s ^ i, ty)
      end
   val vvar = gvar "%v"
   fun varReset () = vnum := Redblackmap.mkDict String.compare
   fun is_vvar tm =
      case Lib.total Term.dest_var tm of
         SOME (s, _) => String.sub (s, 0) = #"%"
       | NONE => false
   fun build_assert (f: term * term -> term) g =
      fn ((d, (c, pat)), (a, tm)) =>
         let
            val v = vvar (utilsLib.dom (Term.type_of d))
         in
            (f (c, Term.mk_comb (d, v)) :: a, Term.subst [pat |-> g v] tm)
         end
end

type footprint_extra = (term * term) * (term -> term) * (term -> term)

local
   fun entry (c, d) = let val (d, pat) = Term.dest_comb d in (d, (c, pat)) end

   fun component_assoc_list proj_def =
      proj_def |> Thm.concl
               |> boolSyntax.strip_forall |> snd
               |> boolSyntax.rhs
               |> Term.dest_abs |> snd
               |> TypeBase.strip_case |> snd
               |> List.map entry
               |> List.partition (fn (_, (t, _)) => Term.is_comb t)

   fun prim_pat_match (c, pat) tm =
      HolKernel.bvk_find_term (K true)
        (fn t =>
            let val m = fst (Term.match_term pat t) in (Term.subst m c, t) end)
        tm

   fun pat_match s_tm (c, pat) tm =
      HolKernel.bvk_find_term (Term.is_comb o snd)
        (fn t =>
            let
               val m = fst (Term.match_term pat t)
               val _ = List.length (HolKernel.find_terms (Lib.equal s_tm) t) < 2
                       orelse raise ERR "" ""
            in
               (Term.subst m c, t)
            end) tm

   fun read_extra x =
      fn [] => x
       | l as ((cpat, f, g) :: r) =>
           (case prim_pat_match cpat (snd x) of
               SOME (d, pat) =>
                  read_extra
                     (build_assert (f o snd) g ((d, (boolSyntax.T, pat)), x)) l
             | NONE => read_extra x r)

   fun map_rws rws = List.map (utilsLib.rhsc o Conv.QCONV (REWRITE_CONV rws))

   val tidyup = map_rws [optionTheory.SOME_11]

   fun is_ok_rhs tm =
      Term.is_var tm orelse
      (case Lib.total optionSyntax.dest_some tm of
          SOME v => Term.is_var v
        | NONE => List.null (Term.free_vars tm))

   fun mk_rewrite1 (l, r) =
      Lib.assert
         (fn {redex, residue} =>
             Term.is_var redex andalso is_ok_rhs residue andalso
             Term.type_of redex = Term.type_of residue) (l |-> r)

   fun mk_rewrite tm =
      case Lib.total boolSyntax.dest_eq tm of
         SOME x => mk_rewrite1 x
       | NONE => (case Lib.total boolSyntax.dest_neg tm of
                     SOME v => mk_rewrite1 (v, boolSyntax.F)
                   | NONE => mk_rewrite1 (tm, boolSyntax.T))

   val is_rewrite = Lib.can mk_rewrite

   fun make_subst tms =
      tms |> List.map mk_rewrite
          |> List.partition (Term.is_var o #residue)
          |> (fn (l1, l2) => Term.subst (l2 @ l1))

   fun not_some_none tm =
      case Lib.total optionSyntax.dest_is_some tm of
         SOME t => not (optionSyntax.is_some t)
       | NONE => true

in
   fun read_footprint proj_def comp_defs cpool (extras: footprint_extra list) =
      let
         val (l1, l2) = component_assoc_list proj_def
         val sty = utilsLib.dom (Term.type_of (utilsLib.get_function proj_def))
         val b_assert =
            build_assert
              (utilsLib.rhsc o REWRITE_CONV (List.map GSYM comp_defs) o
               mk_state_pred) Lib.I
         val mtch = pat_match (Term.mk_var ("s", sty))
      in
         fn thm: thm =>
            let
               val () = varReset ()
               val (b, c: term, tm) = cpool thm
               val x =
                  List.foldl
                     (fn e as ((_, cpat), x) =>
                         if Option.isSome (prim_pat_match cpat (snd x))
                            then b_assert e
                         else x) ([], tm) l2
               fun loop modified x =
                  fn [] => if modified then loop false x l1 else x
                   | l as ((d, cpat) :: r) =>
                       (case mtch cpat (snd x) of
                           NONE => loop modified x r
                         | SOME m => loop true (b_assert ((d, m), x)) l)
               val (a, tm) = read_extra (loop false x l1) extras
               val a = b :: a
               val (p, tm) = boolSyntax.strip_imp tm
               val (eqs, rest) = List.partition is_rewrite (tidyup p)
               val rest = List.filter not_some_none rest
               val sbst = make_subst eqs
               val a = List.map sbst a
               val p = if List.null rest
                          then boolSyntax.T
                       else sbst (boolSyntax.list_mk_conj rest)
            in
               (a, c, p, sbst (optionSyntax.dest_some (boolSyntax.rhs tm)))
            end
      end
end

(* ------------------------------------------------------------------------
   mk_pre_post

   Generate pre-codition, code-pool and post-condition for step-theorem
   ------------------------------------------------------------------------ *)

local
   val next_rel_tm = Term.prim_mk_const {Thy = "state", Name = "NEXT_REL"}
   val state_tm = Term.prim_mk_const {Thy = "state", Name = "STATE"}
   fun mk_next_rel l = boolSyntax.list_mk_icomb (next_rel_tm, l)
   fun mk_state p = boolSyntax.mk_icomb (state_tm, p)
   fun mk_part_spec m = boolSyntax.mk_icomb (progSyntax.spec_tm, m)
in
   fun mk_pre_post next_def instr_def proj_def comp_defs cpool extras write =
      let
         val read = read_footprint proj_def comp_defs cpool extras
         val state_tm = mk_state (utilsLib.get_function proj_def)
         val sty = utilsLib.dom (Term.type_of state_tm)
         val eq_tm = Term.inst [Type.alpha |-> sty] boolSyntax.equality
         val rel_tm = mk_next_rel [eq_tm, utilsLib.get_function next_def]
         val instr_tm = utilsLib.get_function instr_def
         val model_tm =
            pairSyntax.list_mk_pair [state_tm, rel_tm, instr_tm, eq_tm]
         val mk_spec = HolKernel.list_mk_icomb (mk_part_spec model_tm)
      in
         fn thm: thm =>
            let
               val (p, pool, c, tm) = read thm
               val (p, q) = write (p, []: term list, tm)
               val p = if c = boolSyntax.T
                          then p
                       else progSyntax.mk_star (progSyntax.mk_cond c, p)
            in
               mk_spec [p, pool, q]
            end
      end
end

(* ------------------------------------------------------------------------
   spec

   Generate a tool for mapping strings to Hoare tripes, using an instruction
   evaluator.
   ------------------------------------------------------------------------ *)

(*
open lcsymtacs
val () = set_trace "goalstack print goal at top" 0
val () = set_trace "goalstack print goal at top" 1
*)

local
   val WEAK_STRIP_TAC = DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)
   val AND_IMP_INTRO_RULE =
      Conv.CONV_RULE (Conv.DEPTH_CONV Conv.AND_IMP_INTRO_CONV)
   fun is_ineq tys =
      fn thm =>
         (thm |> Thm.concl
              |> boolSyntax.dest_neg
              |> boolSyntax.dest_eq |> fst
              |> Term.type_of
              |> Lib.C Lib.mem tys)
         handle HOL_ERR _ => false
   val ADDRESS_EQ_CONV =
      PURE_REWRITE_CONV [wordsTheory.WORD_EQ_ADD_LCANCEL,
                         wordsTheory.WORD_ADD_INV_0_EQ]
      THENC (Conv.TRY_CONV wordsLib.word_EQ_CONV)
   fun UPDATE_TAC tys =
      fn thms =>
         CONV_TAC
            (Conv.DEPTH_CONV
                (updateLib.UPDATE_APPLY_CONV
                    (PURE_REWRITE_CONV (List.filter (is_ineq tys) thms)
                     THENC ADDRESS_EQ_CONV)))
   val cond_STAR1 = CONJUNCT1 (Drule.SPEC_ALL set_sepTheory.cond_STAR)
   val STAR_ASSOC_CONV =
      Conv.REDEPTH_CONV (Conv.REWR_CONV (GSYM set_sepTheory.STAR_ASSOC))
in
   fun spec imp_spec read_thms write_thms select_state_thms frame_thms
            component_11 map_tys EXTRA_TAC STATE_TAC =
      let
         open lcsymtacs
         val MP_SPEC_TAC = MATCH_MP_TAC imp_spec
         val sthms = cond_STAR1 :: select_state_thms
         val pthms = [boolTheory.DE_MORGAN_THM, pred_setTheory.NOT_IN_EMPTY,
                      pred_setTheory.IN_DIFF, pred_setTheory.IN_INSERT]
         val UPD_TAC = UPDATE_TAC map_tys
         val PRE_TAC =
            MP_SPEC_TAC
            \\ GEN_TAC
            \\ GEN_TAC
            \\ CONV_TAC
                  (Conv.LAND_CONV
                     (Conv.RATOR_CONV STAR_ASSOC_CONV
                      THENC REWRITE_CONV (component_11 @ sthms @ pthms)))
            \\ WEAK_STRIP_TAC
         val POST_TAC =
            PURE_ASM_REWRITE_TAC write_thms
            \\ Tactical.REVERSE CONJ_TAC
            >- (
                ASM_SIMP_TAC pure_ss frame_thms
                \\ (
                    REFL_TAC
                    ORELSE RW_TAC pure_ss frame_thms
                           \\ REFL_TAC
                   )
               )
            \\ CONV_TAC (Conv.RATOR_CONV STAR_ASSOC_CONV)
            (* For testing:
                   val tac = ref ALL_TAC
                   ASSUM_LIST (fn thms => (tac := UPD_TAC thms; ALL_TAC))
                   val update_TAC = !tac
            *)
            \\ ASSUM_LIST
                   (fn thms =>
                      let
                         val update_TAC = UPD_TAC thms
                      in
                         REPEAT
                           (
                            ONCE_REWRITE_TAC sthms
                            \\ CONJ_TAC
                            >- (
                                STATE_TAC
                                \\ update_TAC
                                \\ ASM_REWRITE_TAC [boolTheory.COND_ID]
                               )
                            \\ CONJ_TAC
                            >- ASM_REWRITE_TAC (component_11 @ pthms)
                           )
                      end
                   )
            \\ POP_ASSUM SUBST1_TAC
            \\ REFL_TAC
         fun tac (v, dthm) =
            PRE_TAC
            \\ Tactic.EXISTS_TAC v
            \\ CONJ_TAC
            >- (
                MATCH_MP_TAC dthm
                \\ ASM_REWRITE_TAC read_thms
                \\ EXTRA_TAC
               )
            \\ POST_TAC
      in
         fn (thm, t) =>
            let
               val v = optionSyntax.dest_some (utilsLib.rhsc thm)
               val dthm = AND_IMP_INTRO_RULE (Drule.DISCH_ALL thm)
            in
               (*
                  set_goal ([], t)
               *)
               prove (t, tac (v, dthm))
            end
      end
end

(* ------------------------------------------------------------------------ *)

end
