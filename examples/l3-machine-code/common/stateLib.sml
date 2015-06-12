structure stateLib :> stateLib =
struct

open HolKernel boolLib bossLib
open lcsymtacs updateLib utilsLib
open stateTheory temporal_stateTheory
open helperLib progSyntax temporalSyntax temporal_stateSyntax

structure Parse = struct
  open Parse
  val (Type, Term) =
     parse_from_grammars temporal_stateTheory.temporal_state_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "stateLib"

(* ------------------------------------------------------------------------ *)

(* Versions of operations in helperLib that are generalise to cover
   TEMPORAL_NEXT as well as SPEC *)

fun SPECC_FRAME_RULE frame th =
   Thm.SPEC frame
      (Drule.MATCH_MP progTheory.SPEC_FRAME th
       handle HOL_ERR _ =>
          Drule.MATCH_MP temporal_stateTheory.TEMPORAL_NEXT_FRAME th)

fun SPECL_FRAME_RULE l th =
   let
      val p = temporal_stateSyntax.dest_pre' (Thm.concl th)
      val xs = progSyntax.strip_star p
      val lx =
         List.filter
            (fn t => not (Lib.exists (Lib.can (Term.match_term t)) xs)) l
   in
      List.foldl (Lib.uncurry SPECC_FRAME_RULE) th lx
   end

val MOVE_COND_CONV =
   Conv.REWR_CONV (GSYM progTheory.SPEC_MOVE_COND)
   ORELSEC Conv.REWR_CONV (GSYM temporal_stateTheory.TEMPORAL_NEXT_MOVE_COND)

local
   val cond_T = Q.prove (
      `!p. (set_sep$cond T * p = p) /\ (p * set_sep$cond T = p)`,
      REWRITE_TAC [set_sepTheory.SEP_CLAUSES])
   val rule1 =
      helperLib.PRE_POST_RULE (REWRITE_CONV [cond_T]) o
      Conv.CONV_RULE MOVE_COND_CONV
   fun COND_RW_CONV atm =
      let
         val cnv = Conv.RAND_CONV (PURE_REWRITE_CONV [ASSUME atm])
      in
         fn tm => if progSyntax.is_cond tm then cnv tm else NO_CONV tm
      end
in
   fun MOVE_COND_RULE tm thm =
      let
         val thm1 = Conv.CONV_RULE (Conv.DEPTH_CONV (COND_RW_CONV tm)) thm
      in
         case Thm.hyp thm1 of
            [t] => if t = tm then rule1 (Thm.DISCH t thm1) else thm
          | _ => thm
      end
end

fun PRE_COND_CONV cnv =
   helperLib.PRE_CONV
      (Conv.ONCE_DEPTH_CONV
         (fn tm => if progSyntax.is_cond tm
                      then Conv.RAND_CONV cnv tm
                   else raise ERR "PRE_COND_CONV" "")
       THENC PURE_ONCE_REWRITE_CONV [stateTheory.cond_true_elim])

(* Some syntax functions *)

fun mk_state_pred x =
   pred_setSyntax.mk_set [pred_setSyntax.mk_set [pairSyntax.mk_pair x]]

(* ------------------------------------------------------------------------
   update_frame_state_thm: Generate theorem with conjuncts of the form

   !a w s x.
      f a IN x ==> (FRAME_STATE m x (u s a w) = FRAME_STATE m x (r s))

   where "m" is a projection map and "u" is a state update function.
   ------------------------------------------------------------------------ *)

local
   val concat_ = String.concat o Lib.separate "_"
   val dom_of = utilsLib.dom o Term.type_of
   val rng_of = utilsLib.rng o Term.type_of
   val ty_name = #Tyop o Type.dest_thy_type o Term.type_of
in
   fun update_frame_state_thm proj_def =
      let
         val tac =
            Cases THEN SRW_TAC [] [proj_def, combinTheory.APPLY_UPDATE_THM]
         val proj = utilsLib.get_function proj_def
         val th = Drule.ISPEC proj stateTheory.UPDATE_FRAME_STATE
         val {Thy = p_thy, Name = n, Ty = ty, ...} = Term.dest_thy_const proj
         val isa = if String.isSuffix "_proj" n
                      then String.extract (n, 0, SOME (String.size n - 5))
                   else raise ERR "update_frame_state_thm"
                                  "unexpected proj name"
         val state_ty = fst (Type.dom_rng ty)
         val {Thy = thy, ...} = Type.dest_thy_type state_ty
         val s = Term.mk_var ("s", state_ty)
         fun frame_state_thm component =
            let
               val l = String.tokens (Lib.equal #".") component
               val c_name = concat_ (isa :: "c" :: l)
               val c = Term.prim_mk_const {Name = c_name, Thy = p_thy}
               val (f, aty, not_map) =
                  case Lib.total dom_of c of
                     SOME ty => (c, ty, false)
                   | NONE =>
                       (combinSyntax.mk_K_1 (c, Type.alpha), Type.alpha, true)
               val a = Term.mk_var ("a", aty)
               val w = ref boolSyntax.T
               fun iter rest tm =
                  fn [] => if rest
                              then tm
                           else if not_map
                              then (w := Term.mk_var ("w", Term.type_of tm); !w)
                           else ( w := Term.mk_var ("w", rng_of tm)
                                ; Term.mk_comb
                                     (combinSyntax.mk_update (a, !w), tm)
                                )
                   | h :: t =>
                       let
                          val fupd_name = concat_ [ty_name tm, h, "fupd"]
                          val fupd =
                             Term.prim_mk_const {Name = fupd_name, Thy = thy}
                          val d = utilsLib.dom (dom_of fupd)
                          val v = Term.mk_var (utilsLib.lowercase h, d)
                       in
                          Term.list_mk_comb
                            (fupd, [combinSyntax.mk_K_1 (iter rest v t, d), tm])
                       end
               val u = iter false s l
               val u = Term.list_mk_abs ([s, a, !w], u)
               val l = if not_map then Lib.butlast l else l
               val r = Term.mk_abs (s, iter true s l)
               val thm = th |> Drule.ISPECL [f, u, r] |> SIMP_RULE (srw_ss()) []
               val p = fst (boolSyntax.dest_imp (Thm.concl thm))
               val p_thm = Tactical.prove (p, tac)
            in
               Drule.GEN_ALL (MATCH_MP thm p_thm)
            end
      in
         Drule.LIST_CONJ o List.map frame_state_thm
      end
end

(* ------------------------------------------------------------------------
   update_hidden_frame_state_thm: Generate theorem with conjuncts of the form

   !x y s. (FRAME_STATE m x (s with ? := x) = FRAME_STATE m x s)

   where "m" is a projection map.
   ------------------------------------------------------------------------ *)

local
   val tac =
      NTAC 2 STRIP_TAC
      THEN REWRITE_TAC [stateTheory.FRAME_STATE_def, stateTheory.STATE_def,
                        stateTheory.SELECT_STATE_def, set_sepTheory.fun2set_def]
      THEN SRW_TAC [] [pred_setTheory.EXTENSION, pred_setTheory.GSPECIFICATION]
      THEN EQ_TAC
      THEN STRIP_TAC
      THEN Q.EXISTS_TAC `a`
      THEN Cases_on `a`
   fun prove_hidden thm u =
      let
         val p = utilsLib.get_function thm
         val t = tac THEN FULL_SIMP_TAC (srw_ss()) [thm]
      in
         Drule.GEN_ALL
           (Q.prove (`!y s. FRAME_STATE ^p y ^u = FRAME_STATE ^p y s`, t))
      end
in
   fun update_hidden_frame_state_thm proj_def =
      utilsLib.map_conv (prove_hidden proj_def)
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

   fun build_names (sthy, expnd, hide, state_ty) =
      let
         val s = mk_state_var state_ty
         fun loop (x as ((path, ty), tm), es, hs) =
            case Lib.total TypeBase.fields_of ty of
               NONE => [x]
             | SOME [] => [x]
             | SOME l =>
               let
                  val l = ListPair.zip (l, utilsLib.accessor_fns ty)
                  fun process n =
                     List.map List.tl o
                     List.filter (Lib.equal (SOME n) o Lib.total List.hd)
                  val (nd, dn) =
                     List.foldl
                        (fn ((x as ((n, t), f)), (nd, dn)) =>
                           let
                              val hs' = process n hs
                              val es' = process n es
                              val ahide = Lib.mem [] hs'
                              val y = ((n :: path, t), Term.mk_comb (f, tm))
                           in
                              if List.null es'
                                 then (nd, if ahide then dn else y :: dn)
                              else ((y, es', hs') :: nd, dn)
                           end) ([], []) l
               in
                  dn @ List.concat (List.map loop nd)
               end
         val (l1, tms) =
            ListPair.unzip (loop ((([], state_ty), s), expnd, hide))
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
   fun sep_definitions sthy expnd hide thm =
      let
         val next_tm = utilsLib.get_function thm
         val state_ty = utilsLib.dom (Term.type_of next_tm)
         val (components, data, tms) = build_names (sthy, expnd, hide, state_ty)
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

(*

open arm_stepTheory

val sthy = "arm"
val expnd = [["CPSR"], ["FP", "FPSCR"]]
val hide = [["undefined"], ["CurrentCondition"]]
val thm = arm_stepTheory.NextStateARM_def

val (x as ((path, ty), tm), es) = ((([], state_ty), s), expnd)
val SOME l = Lib.total TypeBase.fields_of ty
val (x as ((n, t), f)) = hd l

val hs = [["Architecture"]]

*)

(* ------------------------------------------------------------------------
   define_map_component (name, f, def)

   Given a definition of the form

    |- !c d. model_X c d = {{(model_c_X, model_d_Y)}}

   this function generates a map version, as defined by

    !df f. name df f = {BIGUNION {BIGUNION (model_X c (f c)) | c IN df}}

   and it also derives the theorem

    |- c IN df ==> (model_X c d * name (df DELETE c) f = name df ((c =+ d) f))

   ------------------------------------------------------------------------ *)

fun define_map_component (s, f, def) =
   let
      val thm = Drule.MATCH_MP stateTheory.MAPPED_COMPONENT_INSERT_OPT def
                handle HOL_ERR _ =>
                   Drule.MATCH_MP stateTheory.MAPPED_COMPONENT_INSERT1 def
      val map_c = fst (boolSyntax.dest_forall (Thm.concl thm))
      val map_c = Term.mk_var (s, Term.type_of map_c)
      val (tm_11, def_tm) = thm |> Thm.SPEC map_c
                                |> Thm.concl
                                |> boolSyntax.dest_imp |> fst
                                |> boolSyntax.dest_conj
      val comp_11 = simpLib.SIMP_PROVE (srw_ss()) [] tm_11
      val (v_df, def_tm) = boolSyntax.dest_forall def_tm
      val (v_f, def_tm) = boolSyntax.dest_forall def_tm
      val v_df' = Term.mk_var ("d" ^ f, Term.type_of v_df)
      val v_f' = Term.mk_var (f, Term.type_of v_f)
      val def_tm = Term.subst [v_df |-> v_df', v_f |-> v_f'] def_tm
      val mdef = Definition.new_definition (s ^ "_def", def_tm)
      val thm = Theory.save_thm
                  (s ^ "_INSERT",
                   Drule.SPECL [v_f', v_df']
                      (MATCH_MP thm (Thm.CONJ comp_11 mdef)))
   in
      (mdef, thm)
   end
   handle HOL_ERR {message, ...} => raise ERR "define_map_component" message

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
   fun is_gen s = String.sub (s, 0) = #"%"
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
         SOME (s, _) => is_gen s
       | NONE => false
   fun is_nvvar tm =
      case Lib.total Term.dest_var tm of
         SOME (s, _) => not (is_gen s)
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

   fun map_rws rws =
      List.concat o
        (List.map (boolSyntax.strip_conj o utilsLib.rhsc o
                   Conv.QCONV (REWRITE_CONV rws)))

   val tidyup = map_rws [optionTheory.SOME_11]

   fun is_ok_rhs tm =
      is_nvvar tm orelse
      (case Lib.total optionSyntax.dest_some tm of
          SOME v => is_nvvar v
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
   write_footprint syntax1 syntax2 l1 l2 l3 l4 P (p, q, tm)

   Extend p (pre) and q (post) proposition lists with entries for
   component updates.

   l1 is a list of updates for map components
   l2 is a list of updates for regular components
   l3 is a list of updates for regular components (known to be read)
   l4 is a list of user defined updates for sub components

   P is a predicate this is used to test whether all updates have been
   considered
   ------------------------------------------------------------------------ *)

local
   fun strip_assign (a, b) =
      let
         val (x, y) = combinSyntax.strip_update (combinSyntax.dest_K_1 a)
      in
         if b <> y
            then (Parse.print_term b
                  ; print "\n\n"
                  ; Parse.print_term y
                  ; raise ERR "write_footprint" "strip_assign")
         else ()
         ; x
      end
   fun not_in_asserts p (dst: term -> term) =
      List.filter
         (fn x =>
            let
               val d = dst x
            in
               not (Lib.exists (fn y => case Lib.total dst y of
                                           SOME c => c = d
                                         | NONE => false) p)
            end)
   fun prefix tm = case boolSyntax.strip_comb tm of
                      (a, [_]) => a
                    | (a, [b, _]) => Term.mk_comb (a, b)
                    | _ => raise ERR "prefix" ""
   fun fillIn f ty =
      fn []: term list => []
       | _ => [f (vvar ty)]: term list
   datatype footprint =
       MapComponent of
          term * (term * term -> term) * (term -> term) * (term -> term)
     | Component of term list * term list * term -> term list * term list
   fun mk_map_footprint syntax2 (c:string, t) =
      let
         val (tm, mk, dst:term -> term * term, _:term -> bool) = syntax2 c
         val ty = utilsLib.dom (utilsLib.rng (Term.type_of tm))
         val c = fst o dst
         fun d tm = mk (c tm, vvar ty)
      in
         MapComponent (t, mk, c, d)
      end
   fun mk_footprint1 syntax1 (c:string) =
      let
         val (tm, mk, _:term -> term, _:term -> bool) = syntax1 c
         val ty = utilsLib.dom (Term.type_of tm)
      in
         Component
            (fn (p, q, v) =>
               let
                   val x = mk v
                   val l = fillIn mk ty (not_in_asserts p Term.rator [x])
               in
                  (l @ p, x :: q)
               end)
      end
   fun mk_footprint1b syntax1 (c:string) =
      let
         val (_, mk, _, _) = syntax1 c
      in
         Component (fn (p, q, v) => (p, mk v :: q))
      end
in
   fun sort_finish psort (p, q) =
      let
         val q = psort (q @ not_in_asserts q prefix p)
      in
         (psort p, q)
      end
   fun write_footprint syntax1 syntax2 l1 l2 l3 l4 P =
      let
         val mk_map_f = mk_map_footprint syntax2
         val l1 = List.map (fn (s, c, tm) => (s, mk_map_f (c, tm))) l1
         val l2 = List.map (I ## mk_footprint1 syntax1) l2
         val l3 = List.map (I ## mk_footprint1b syntax1) l3
         val l4 = List.map (I ## Component) l4
         val m = Redblackmap.fromList String.compare (l1 @ l2 @ l3 @ l4)
         fun default (s, l, p, q) =
            if P (s, l) then (p, q) else raise ERR "write_footprint" s
         fun loop (p, q, tm) =
            (case boolSyntax.dest_strip_comb tm of
                (f_upd, l as [v, rst]) =>
                  (case Redblackmap.peek (m, f_upd) of
                      SOME (Component f) =>
                         let
                            val (p', q') = f (p, q, combinSyntax.dest_K_1 v)
                         in
                            loop (p', q', rst)
                         end
                    | SOME (MapComponent (t, mk, c, d)) =>
                         let
                            val l = List.map mk (strip_assign (v, t))
                            val l2 = List.map d (not_in_asserts p c l)
                         in
                            loop (l2 @ p, l @ q, rst)
                         end
                    | NONE => default (f_upd, l, p, q))
              | (s, l) => default (s, l, p, q) : (term list * term list))
            handle HOL_ERR {message = "not a const", ...} => (p, q)
      in
         loop
      end
end

(* ------------------------------------------------------------------------
   mk_pre_post

   Generate pre-codition, code-pool and post-condition for step-theorem
   ------------------------------------------------------------------------ *)

local
   val temporal = ref false
in
   fun set_temporal b = temporal := b
   fun generate_temporal () = !temporal
end

local
   fun get_def tm =
      let
         val {Name, Thy, ...} = Term.dest_thy_const (Term.rand tm)
      in
         DB.fetch Thy (Name ^ "_def")
      end
in
   fun mk_pre_post model_def comp_defs cpool extras write_fn psort =
      let
         val (model_tm, tm) = boolSyntax.dest_eq (Thm.concl model_def)
         val proj_def = case pairSyntax.strip_pair tm of
                           [a, _, _, _, _] => get_def a
                         | _ => raise ERR "mk_pre_post" "bad model definition"
         val read = read_footprint proj_def comp_defs cpool extras
         val mk_spec_or_temporal_next =
            temporal_stateSyntax.mk_spec_or_temporal_next model_tm
         val write = (progSyntax.list_mk_star ## progSyntax.list_mk_star) o
                     sort_finish psort o write_fn
      in
         fn thm: thm =>
            let
               val (p, pool, c, tm) = read thm
               val (p, q) = write (p, []: term list, tm)
               val p = if c = boolSyntax.T
                          then p
                       else progSyntax.mk_star (progSyntax.mk_cond c, p)
            in
               mk_spec_or_temporal_next (generate_temporal()) (p, pool, q)
            end
      end
end

(* ------------------------------------------------------------------------
   rename_vars (rename1, rename2, bump)

   Rename generated variables "%v" is a SPEC theorem.
   ------------------------------------------------------------------------ *)

fun rename_vars (rename1, rename2, bump) =
   let
      fun rename f tm =
         case boolSyntax.dest_strip_comb tm of
            (c, [v]) =>
               if is_vvar v
                  then case rename1 c of
                          SOME s => SOME (v |-> f (s, Term.type_of v))
                        | NONE => NONE
               else NONE
          | (c, [x, v]) =>
               if is_vvar v
                  then case rename2 c of
                          SOME g =>
                             (case Lib.total g x of
                                 SOME s => SOME (v |-> f (s, Term.type_of v))
                               | NONE => NONE)
                        | NONE => NONE
               else NONE
          | _ => NONE
   in
      fn thm =>
         let
            val p = temporal_stateSyntax.dest_pre' (Thm.concl thm)
            val () = varReset()
            val () = List.app (fn s => General.ignore (gvar s Type.alpha)) bump
            val avoid = utilsLib.avoid_name_clashes p o Lib.uncurry gvar
            val p = progSyntax.strip_star p
         in
            Thm.INST (List.mapPartial (rename avoid) p) thm
         end
         handle e as HOL_ERR _ => Raise e
   end

(* ------------------------------------------------------------------------
   introduce_triple_definition (duplicate, thm_def) thm

   Given a thm_def of the form

    |- !x. f x = p1 * ... * pn * cond c1 * ... * cond cm

   (where the conds need not be at the end) and a theorem "thm" of the form

    |- SPEC (cond r * p) c q

   the function introduce_triple_definition gives a theorem of form

    |- SPEC (cond r' * p' * f x1) c (q' * f x2)

   The condition "r'" is related to "r" but will no longer incorporate
   conditions found in "c1" to "cm". Similarly "p'" and "q'" will no
   longer contain components "p1" to "pn".

   The "duplicate" flag controls whether or not conditions in "r" are
   added to the postcondition in order to introduce "f".
   ------------------------------------------------------------------------ *)

local
   val get_conds = List.filter progSyntax.is_cond o progSyntax.strip_star
   val err = ERR "introduce_triple"
   fun move_match (pat, t) =
      MOVE_COND_RULE
        (case Lib.mk_set (find_terms (Lib.can (Term.match_term pat)) t) of
            [] => raise (err "missing condition")
          | [m] => m
          | l => Lib.with_exn (Lib.first (Lib.equal pat)) l
                   (err "ambiguous condition"))
in
   fun introduce_triple_definition (duplicate, thm_def) =
      let
         val ts = thm_def
                  |> Thm.concl
                  |> boolSyntax.strip_forall |> snd
                  |> boolSyntax.dest_eq |> snd
                  |> progSyntax.strip_star
         val (cs, ps) = List.partition progSyntax.is_cond ts
         val cs = List.map progSyntax.dest_cond cs
         val rule =
            helperLib.PRE_POST_RULE (helperLib.STAR_REWRITE_CONV (GSYM thm_def))
         fun d_rule th =
            if duplicate
               then MATCH_MP progTheory.SPEC_DUPLICATE_COND th
                    handle HOL_ERR _ =>
                      MATCH_MP
                        temporal_stateTheory.TEMPORAL_NEXT_DUPLICATE_COND th
            else th
      in
         fn thm =>
            let
               val p = temporal_stateSyntax.dest_pre' (Thm.concl thm)
               val move_cs =
                  List.map
                     (fn t => List.map (fn c => d_rule o move_match (c, t)) cs)
                     (get_conds p)
            in
               thm |> SPECL_FRAME_RULE ps
                   |> Lib.C (List.foldl (fn (f, t) => f t))
                            (List.concat move_cs)
                   |> rule
            end
      end
end

(* ------------------------------------------------------------------------
   introduce_map_definition (insert_thm, dom_eq_conv) thm

   Given an insert_thm of the form

     |- c IN df ==> (model_X c d * name (df DELETE c) f = name df ((c =+ d) f))

   (which may be generated by define_map_component) and a theorem "thm" of the
   form

     |- SPEC (cond r * p) c q

   where "p" and "q" contain instances of "model_X c d", a theorem new is
   generated of the form

     |- SPEC (p' * name df f * cond (r /\ z)) x (q' * name df f')

   where "p'" and "q'" are modified versions of "p" and "q" that no longer
   contain any instances of "model_X c d".

   The predicate "z" will specify which values are contained in "df",
   which represents the domain of the newly intoruced map "f".

   The conversion "dom_eq_conv" can be used to simplify "z" by deciding
   equality over elements of the domain of "f".
   ------------------------------------------------------------------------ *)

local
   fun strip2 f = case boolSyntax.strip_comb f of
                     (f, [a, b]) => (f, (a, b))
                   | _ => raise ERR "strip2" ""
   val tidy_up_rule =
      helperLib.MERGE_CONDS_RULE o
      PURE_REWRITE_RULE [GSYM progTheory.SPEC_MOVE_COND,
                         GSYM temporal_stateTheory.TEMPORAL_NEXT_MOVE_COND] o
      Drule.DISCH_ALL
   val is_ineq = Lib.can (boolSyntax.dest_eq o boolSyntax.dest_neg)
   val apply_id_rule = PURE_REWRITE_RULE [updateTheory.APPLY_UPDATE_ID]
in
   fun introduce_map_definition (insert_thm, dom_eq_conv) =
      let
         val insert_thm = Drule.SPEC_ALL insert_thm
         val ((f_tm, (c, d)), (m_tm, (df, f))) =
            insert_thm
            |> Thm.concl
            |> boolSyntax.dest_imp |> snd
            |> boolSyntax.dest_eq |> fst
            |> progSyntax.dest_star
            |> (strip2 ## strip2)
         val is_f = Lib.equal f_tm o fst o boolSyntax.strip_comb
         val get_f =
            List.filter is_f o progSyntax.strip_star o
            temporal_stateSyntax.dest_pre' o Thm.concl
         val c_ty = Term.type_of c
         val d_ty = Term.type_of d
         val c_set_ty = pred_setSyntax.mk_set_type c_ty
         val df = fst (pred_setSyntax.dest_delete df)
         val df_intro = List.foldl (pred_setSyntax.mk_delete o Lib.swap) df
         fun mk_frame cs = Term.mk_comb (Term.mk_comb (m_tm, df_intro cs), f)
         val insert_conv =
            utilsLib.ALL_HYP_CONV_RULE
               (PURE_REWRITE_CONV [pred_setTheory.IN_DELETE]) o
            utilsLib.INST_REWRITE_CONV [Drule.UNDISCH_ALL insert_thm]
         val (mk_dvar, mk_subst) =
            case Lib.total optionSyntax.dest_option d_ty of
               SOME ty =>
                 (fn () => optionSyntax.mk_some (Term.genvar ty),
                  fn (d, c) => optionSyntax.dest_some d |-> Term.mk_comb (f, c))
             | NONE =>
                 (fn () => Term.genvar d_ty,
                  fn (d, c) => d |-> Term.mk_comb (f, c))
         val update_ss =
            bool_ss ++
            simpLib.rewrites
               [updateTheory.APPLY_UPDATE_ID, combinTheory.UPDATE_APPLY,
                combinTheory.UPDATE_APPLY_IMP_ID]
      in
         fn th =>
            let
               val xs = get_f th
            in
               if List.null xs
                  then th
               else let
                       val xs =
                          List.map
                             (fn t =>
                                let
                                   val (g, d) = Term.dest_comb t
                                   val c = Term.rand g
                                in
                                   (Term.mk_comb (g, mk_dvar ()),
                                    (Term.rand g, mk_subst (d, c)))
                                end) xs
                       val (xs, cs_ds) = ListPair.unzip xs
                       val (cs, ds) = ListPair.unzip cs_ds
                       val frame = mk_frame cs
                       val rwt =
                          insert_conv (List.foldr progSyntax.mk_star frame xs)
                       val ineqs =
                          rwt |> Thm.hyp
                              |> List.map boolSyntax.strip_conj
                              |> List.concat
                              |> List.filter is_ineq
                              |> List.map
                                   (utilsLib.ALL_HYP_CONV_RULE dom_eq_conv o
                                    ASSUME)
                       val (rwt, rule) =
                          if List.null ineqs
                             then (rwt, apply_id_rule)
                          else (utilsLib.ALL_HYP_CONV_RULE
                                  (REWRITE_CONV ineqs) rwt,
                                SIMP_RULE (update_ss++simpLib.rewrites ineqs)[])
                    in
                       th |> SPECC_FRAME_RULE frame
                          |> helperLib.PRE_POST_RULE
                               (helperLib.STAR_REWRITE_CONV rwt)
                          |> Thm.INST ds
                          |> rule
                          |> tidy_up_rule
                    end
            end
      end
      handle HOL_ERR _ => raise ERR "introduce_map_definition" ""
end

(* ------------------------------------------------------------------------
   fix_precond

   Given a list of theorems of the form

     [
       |- SPEC m (p1 * cond (... /\ c /\ ...)) code q1,
       |- SPEC m (p2 * cond ~c) code q2
     ]

   (where the "cond" terms are not necessarily outermost) return theorems

     [
       |- SPEC m (p1 * cond (...) * precond c) code q1,
       |- SPEC m (p2 * precond ~c) code q2
     ]

   Is an identity function for single element lists and raises and error
   for all other lists.
   ------------------------------------------------------------------------ *)

local
   val pecond_rule =
      Conv.CONV_RULE
         (Conv.TRY_CONV
            (helperLib.PRE_CONV
               (Conv.RAND_CONV
                  (Conv.RATOR_CONV
                     (Conv.REWR_CONV (GSYM set_sepTheory.precond_def))))))
   fun rule c th = pecond_rule (MOVE_COND_RULE c th)
   val get_cond =
      Term.rand o Lib.first progSyntax.is_cond o progSyntax.strip_star o
      temporal_stateSyntax.dest_pre' o Thm.concl
in
   val fix_precond =
      fn [th1, th2] =>
            let
               val c = get_cond th2
            in
               [rule (utilsLib.mk_negation c) th1, rule c th2]
            end
        | thms as [_] => thms
        | _ => raise ERR "fix_precond" ""
end

(* ------------------------------------------------------------------------
   get_delta pc_var pc
   get_pc_delta is_pc
   ------------------------------------------------------------------------ *)

fun get_delta pc_var pc =
   case Lib.total wordsSyntax.dest_word_add pc of
      SOME (x, n) =>
         if x = pc_var
            then Lib.total wordsSyntax.uint_of_word n
         else NONE
    | NONE =>
        (case Lib.total wordsSyntax.dest_word_sub pc of
            SOME (x, n) =>
               if x = pc_var
                  then Lib.total (Int.~ o wordsSyntax.uint_of_word) n
               else NONE
          | NONE => if pc = pc_var then SOME 0 else NONE)

fun get_pc_delta is_pc =
   let
      val get_pc = Term.rand o Lib.first is_pc o progSyntax.strip_star
   in
      fn th =>
         let
            val (p, q) = progSyntax.dest_pre_post (Thm.concl th)
         in
            get_delta (get_pc p) (get_pc q)
         end
   end

(* ------------------------------------------------------------------------
   PC_CONV
   ------------------------------------------------------------------------ *)

local
   val ARITH_SUB_CONV = wordsLib.WORD_ARITH_CONV THENC wordsLib.WORD_SUB_CONV
   fun is_word_lit tm =
      case Lib.total wordsSyntax.dest_mod_word_literal tm of
         SOME (n, s) =>
            n = wordsSyntax.dest_word_literal tm andalso
            Lib.funpow (Arbnum.toInt s - 1) Arbnum.div2 n = Arbnum.zero
       | NONE => false
   fun is_irreducible tm =
      Term.is_var tm orelse
      (case Lib.total wordsSyntax.dest_word_add tm of
          SOME (p, i) => Term.is_var p andalso is_word_lit i
        | NONE => false) orelse
      (case Lib.total wordsSyntax.dest_word_sub tm of
          SOME (p, i) => Term.is_var p andalso is_word_lit i
        | NONE => false) orelse
      (case Lib.total boolSyntax.dest_cond tm of
          SOME (_, x, y) => is_irreducible x andalso is_irreducible y
        | NONE => false)
in
   fun PC_CONV s =
      Conv.ONCE_DEPTH_CONV
         (fn tm =>
            case boolSyntax.dest_strip_comb tm of
              (c, [t]) =>
                 if c = s andalso not (is_irreducible t)
                    then Conv.RAND_CONV ARITH_SUB_CONV tm
                 else raise ERR "PC_CONV" ""
             | _ => raise ERR "PC_CONV" "")
end

(* ------------------------------------------------------------------------
   group_into_chunks (dst, n, mk, is_big_end) l

   Helper function for collecting together multiple map accesses. Assumes
   that the list "l" is suitably ordered.

   dst - identifies the access, e.g. arm_MEM
   n - number of accesses to be grouped togther, e.g. 4 bytes
   mk - used when reversing endianness
   is_big_end - identify big-endian mode
   ------------------------------------------------------------------------ *)

local
   fun err i = ERR "group_into_chunks" ("missing chunk: " ^ Int.toString i)
   fun get i l =
      if i = 0
         then snd (hd l) : term
      else case Lib.total (wordsSyntax.dest_word_add ## I) (List.nth (l, i)) of
              SOME ((a, b), d) =>
                 ( wordsSyntax.uint_of_word b = i orelse raise (err i)
                 ; d
                 )
            | NONE => raise (err i)
   fun mk_chunk (w, ty) =
      fn (h, l) =>
         let
            val hi = numSyntax.term_of_int h
            val li = numSyntax.term_of_int l
         in
            wordsSyntax.mk_word_extract (hi, li, w, ty)
         end
   fun prim_mk_word_var (i, ty) = Term.mk_var ("w" ^ Int.toString i, ty)
   fun mk_word_var (d, i, ty) =
      case Lib.total wordsSyntax.dest_word_extract d of
         SOME (_, _, v, _) => v
       | NONE => prim_mk_word_var (i, ty)
   fun process be n j =
      fn [] => raise ERR "group_into_n_chunks" "empty"
       | l as ((a, d) :: _) =>
            let
               val dty = wordsSyntax.dest_word_type (Term.type_of d)
               val dsz = fcpSyntax.dest_int_numeric_type dty
               val ty = wordsSyntax.mk_int_word_type (dsz * n)
               val w = mk_word_var (d, j, ty)
               val mk = mk_chunk (w, dty)
               fun mk_i i = let val l = i * dsz in mk (l + dsz - 1, l) end
            in
              (List.rev
                (List.tabulate
                  (n, fn i => get i l |-> mk_i (if be then n - 1 - i else i))),
                (w, a))
            end
   fun group_into_n n =
      let
         fun iter a l =
            if List.null l
               then List.rev a
            else iter (List.take (l, n) :: a) (List.drop (l, n))
                 handle General.Subscript => raise ERR "group_into_n" "too few"
      in
         iter []
      end
in
   fun group_into_chunks (dst, n, be) =
      ListPair.unzip o Lib.mapi (process be n) o
      group_into_n n o List.mapPartial (Lib.total dst)
end

(* ------------------------------------------------------------------------
   ------------------------------------------------------------------------ *)

fun pick_endian_rule (is_big_end, rule1, rule2) =
   let
      val P = List.exists is_big_end o progSyntax.strip_star o
              temporal_stateSyntax.dest_pre' o Thm.concl
   in
      fn th => if P th then rule1 th else rule2 th : thm
   end

fun chunk_for m_def =
   let
      val (l, r) = boolSyntax.dest_eq (Thm.concl (Drule.SPEC_ALL m_def))
      val m_tm = fst (boolSyntax.strip_comb l)
      val (c_tm, n) = case progSyntax.strip_star r of
                         [] => raise ERR "chunks_intro" ""
                       | l as h :: _ =>
                            (fst (boolSyntax.strip_comb h), List.length l)
   in
      (HolKernel.dest_binop c_tm (ERR "dest" "chunks"), n, m_tm)
   end

fun not_refl thm =
   case Lib.total (boolSyntax.dest_eq o Thm.concl) thm of
      SOME (l, r) => l <> r
    | NONE => false

fun chunks_intro_pre_process m_def =
   let
      val (dst, n, _) = chunk_for m_def
      val dst = fst o dst
   in
      fn thm =>
         let
            val p = temporal_stateSyntax.dest_pre' (Thm.concl thm)
            val l = List.filter (Lib.can dst) (progSyntax.strip_star p)
         in
            if List.null l
               then thm
            else let
                    val base = dst (hd l)
                    val ty = wordsSyntax.dim_of base
                    fun lit i = wordsSyntax.mk_n2w (numLib.term_of_int i, ty)
                    fun mk0 i = wordsSyntax.mk_word_add (base, lit i)
                    fun mk (0, 0) = base
                      | mk (0, j) = mk0 j
                      | mk (i, 0) = mk0 i
                      | mk (i, j) = wordsSyntax.mk_word_add (mk0 i, lit j)
                    fun rwt tm (i, j) =
                       let
                          val r =
                             Drule.EQT_ELIM
                               (wordsLib.WORD_ARITH_CONV
                                  (boolSyntax.mk_eq (dst tm, mk (i, j))))
                       in
                          Conv.RATOR_CONV (Conv.RAND_CONV (Conv.REWR_CONV r)) tm
                       end
                     val (rwts, _) =
                        List.foldl
                           (fn (tm, (acc, (i, j))) =>
                              let
                                 val r = rwt tm (i, j)
                              in
                                 (if not_refl r then r :: acc else acc,
                                  if j = n - 1 then (i + n, 0) else (i, j + 1))
                              end) ([], (0, 0)) l
                 in
                    PURE_REWRITE_RULE rwts thm
                 end
                 handle HOL_ERR {origin_function = "EQT_ELIM", ...} => thm
         end
   end

fun chunks_intro be m_def =
   let
      val (dst, n, _) = chunk_for m_def
      val chunks = group_into_chunks (dst, n, be)
      val cnv = REPEATC (helperLib.STAR_REWRITE_CONV (GSYM m_def))
   in
      fn thm =>
         let
            val p = temporal_stateSyntax.dest_pre' (Thm.concl thm)
            val (s, wa) = chunks (progSyntax.strip_star p)
         in
            if List.null wa
               then thm
            else helperLib.PRE_POST_RULE cnv (Thm.INST (List.concat s) thm)
         end
         handle HOL_ERR {origin_function = "group_into_n",
                         message = "too few", ...} => thm
   end

(* ------------------------------------------------------------------------
   sep_array_intro mk_rev is_big_end m_def rwts

   Introduce a SEP_ARRAY.
   ------------------------------------------------------------------------ *)

local
   val (sep_array_tm, mk_sep_array, dest_sep_array, _) =
      HolKernel.syntax_fns
         {n = 5, dest = HolKernel.dest_quadop, make = HolKernel.mk_quadop}
         "set_sep" "SEP_ARRAY"
   val list_mk_concat =
      HolKernel.list_mk_rbinop (Lib.curry wordsSyntax.mk_word_concat)
   val list_mk_add =
      HolKernel.list_mk_lbinop (Lib.curry wordsSyntax.mk_word_add)
   val emp_right = set_sepTheory.SEP_CLAUSES |> SPEC_ALL |> CONJUNCTS |> last
   fun mk_array prj be (s1: (term, term) subst list) =
      let
         val f = if be then List.rev else Lib.I
      in
         List.map (fn l => list_mk_concat (List.map prj (f l))) s1
      end
   val mk_array1 = mk_array (#residue)
   val mk_array2 = mk_array (#redex)
   fun array_iter_rwts base wa delta =
      Lib.mapi (fn i => fn (_, a) =>
                  let
                     val t = list_mk_add (base :: List.tabulate (i, K delta))
                  in
                     if t = a then boolTheory.TRUTH
                     else wordsLib.WORD_ARITH_PROVE (boolSyntax.mk_eq (t, a))
                  end) wa
   val cnv1 = REWRITE_CONV [emp_right, set_sepTheory.SEP_ARRAY_def]
   fun frame_rule thm =
      Drule.SPEC_ALL
         (MATCH_MP (if generate_temporal ()
                       then temporal_stateTheory.SEP_ARRAY_TEMPORAL_FRAME
                    else stateTheory.SEP_ARRAY_FRAME) thm)
   fun length_list rwt =
      let
         val (_, _, _, l) = dest_sep_array (utilsLib.rhsc rwt)
      in
         listSyntax.mk_length l
      end
   val length_eq =
      Drule.EQT_ELIM o
      (Conv.BINOP_CONV listLib.LENGTH_CONV THENC reduceLib.NEQ_CONV) o
      boolSyntax.mk_eq
in
   fun sep_array_intro be m_def rwts =
      let
         val (dst, n, m_tm) = chunk_for m_def
         val chunks = group_into_chunks (dst, n, be)
         val rule = SYM o PURE_REWRITE_RULE rwts
         val cnv1 = REWRITE_CONV [m_def, emp_right, set_sepTheory.SEP_ARRAY_def]
         fun star rwt = helperLib.STAR_REWRITE_CONV rwt
                        THENC PURE_REWRITE_CONV rwts
      in
         fn thm =>
            let
               val p = temporal_stateSyntax.dest_pre' (Thm.concl thm)
               val (s, wa) = chunks (progSyntax.strip_star p)
            in
               if List.null wa
                  then thm
               else let
                       val (w, base) = hd wa
                       val sz = wordsSyntax.size_of base
                       val delta = wordsSyntax.mk_word (Arbnum.fromInt n, sz)
                       val iter_rwts = array_iter_rwts base wa delta
                       val r = rule o (cnv1 THENC PURE_REWRITE_CONV iter_rwts)
                       val l1_tm =
                          listSyntax.mk_list (mk_array1 be s, Term.type_of w)
                       val sep_array1 = mk_sep_array (m_tm, delta, base, l1_tm)
                       val rwt1 = r sep_array1
                       val thm' = Thm.INST (List.concat s) thm
                       val lq =
                          progSyntax.strip_star
                             (temporal_stateSyntax.dest_post' (Thm.concl thm'))
                       val (s2, _) = chunks lq
                       val array =
                          (if s = s2 then mk_array2 else mk_array1) be s2
                       val l2_tm = listSyntax.mk_list (array, Term.type_of w)
                       val sep_array2 = mk_sep_array (m_tm, delta, base, l2_tm)
                       val rwt2 = r sep_array2
                       val length_l2_l1 =
                          length_eq (length_list rwt2, length_list rwt1)
                    in
                       frame_rule
                          (Thm.CONJ length_l2_l1
                             (Conv.CONV_RULE
                                (helperLib.PRE_CONV (star rwt1)
                                 THENC helperLib.POST_CONV (star rwt2)) thm'))
                    end
            end
            handle HOL_ERR {origin_function = "group_into_n",
                            message = "too few", ...} => thm
      end
end

(* ------------------------------------------------------------------------
   register_combinations

   Take a next-state (step) theorem and SPEC term and generate all valid
   variants based on register equivalences.
   ------------------------------------------------------------------------ *)

local
   fun concat_unzip l = (List.concat ## List.concat) (ListPair.unzip l)
   fun instantiate (a, b) =
      if Term.is_var a then SOME (a |-> b)
      else if a = b then NONE else raise ERR "instantiate" "bad constant match"
   fun mk_assign f (p, q) =
      List.map
         (fn ((r1, a), (r2, b)) => (Lib.assert (op =) (r1, r2); (r1, a, b)))
         (ListPair.zip (f p, f q))
   fun takeWhile P =
      let
         fun iter [] = []
           | iter (h :: t) = if P h then h :: iter t else []
      in
         iter
      end
in
   fun register_combinations
         (dest_reg, reg_width, proj_reg, reg_conv, ok_conv, asm, model_tm) =
      let
         val mk = temporal_stateSyntax.mk_spec_or_temporal_next model_tm
         val regs = List.mapPartial (Lib.total dest_reg)
         val reg_rule = utilsLib.FULL_CONV_RULE reg_conv
         val bits = List.map bitstringSyntax.mk_b o
                    utilsLib.padLeft false reg_width o
                    bitstringSyntax.int_to_bitlist
         fun proj_reg0 tm =
            case Lib.total (fst o bitstringSyntax.dest_v2w) tm of
               SOME l => fst (listSyntax.dest_list l)
             | NONE => bits (wordsSyntax.uint_of_word tm)
         val proj = case proj_reg of
                       SOME f =>
                          (fn t => case Lib.total f t of
                                      SOME i => bits i
                                    | NONE => proj_reg0 (Term.rand t))
                     | NONE => proj_reg0
         fun err s = ERR "register_combinations: explode_reg" s
         fun explode_reg tm =
            let
               val l = proj tm
            in
               List.length l = reg_width orelse raise (err "assertion failed")
               ; l
            end
            handle HOL_ERR {message = s, ...} => raise (err s)
         fun match_register (tm1, v1, _) (tm2, v2, v3) =
            let
               val _ = v3 = v2 orelse raise ERR "match_register" "changed"
               val l = ListPair.zip (explode_reg tm2, explode_reg tm1)
            in
               ((v2 |-> v1) :: List.mapPartial instantiate l, [tm2])
            end
         val frees = List.filter Term.is_var o explode_reg
         fun no_free (t, _: term, _: term) = List.null (frees t)
         val exists_free = List.exists (not o no_free)
         fun no_good l = List.length (takeWhile no_free l) > 1
         fun groupings ok rs =
            let
               val (cs, vs) = List.partition no_free rs
            in
               (cs @ vs)
               |> utilsLib.partitions
               |> List.filter (not o Lib.exists no_good)
               |> List.map
                     (List.mapPartial
                         (fn l =>
                            let
                               val (unchanged, changed) =
                                  List.partition (fn (_, a, b) => a = b) l
                            in
                               if 1 < List.length l
                                  andalso List.length changed < 2
                                  andalso exists_free l
                                  then SOME (changed @ unchanged)
                               else NONE
                            end))
               |> Lib.mk_set
               |> Lib.mapfilter
                    (fn p =>
                       concat_unzip
                         (List.map
                            (fn l =>
                               let
                                  val (h, t) =
                                     Lib.pluck no_free l
                                     handle
                                        HOL_ERR
                                           {message = "predicate not satisfied",
                                            ...} => (hd l, tl l)
                                  fun mtch x =
                                     let
                                        val s = match_register h x
                                     in
                                        Lib.assert ok (fst s); s
                                     end
                               in
                                  concat_unzip (List.map mtch t)
                               end) p))
            end
         (* check that the pre-condition predictate (from "cond P" terms) is not
            violated *)
         val conv = reg_conv THENC ok_conv
         fun assign_ok p =
            let
               val l = List.mapPartial (Lib.total progSyntax.dest_cond) p
               val c = boolSyntax.list_mk_conj l
            in
               fn s => utilsLib.rhsc (conv (Term.subst s c)) <> boolSyntax.F
            end
         fun star_subst s = List.map (utilsLib.rhsc o reg_conv o Term.subst s)
      in
         fn (thm, t) =>
            let
               val (_, p, c, q) = temporal_stateSyntax.dest_spec' t
               val pl = progSyntax.strip_star p
               val ql = progSyntax.strip_star q
               val rs = mk_assign regs (pl, ql)
               val groups = groupings (assign_ok pl) rs
            in
               if List.null groups
                  then [(thm, t)]
               else List.map
                       (fn (s, d) =>
                           let
                              val do_reg =
                                 star_subst s o
                                 List.filter
                                    (fn tm =>
                                       case Lib.total dest_reg tm of
                                          SOME (a, _) => not (Lib.mem a d)
                                        | NONE => true)
                              val pl' = do_reg pl
                              val p' = progSyntax.list_mk_star pl'
                              val q' = progSyntax.list_mk_star (do_reg ql)
                              val rwts = Lib.mapfilter (asm o Term.rand o fst)
                                           (regs pl')
                              val asm_conv = Conv.QCONV (REWRITE_CONV rwts)
                           in
                              (Conv.CONV_RULE asm_conv
                                 (reg_rule (Thm.INST s thm)),
                               mk (generate_temporal())
                                  (p', Term.subst s c,
                                   utilsLib.rhsc (asm_conv q')): Term.term)
                           end) groups
            end
      end
end

(* ------------------------------------------------------------------------
   spec

   Generate a tool for proving theorems of the form

     |- SPEC p c q

   The goal is expected to be generated by mk_pre_post based on a
   step-theorem, which is in turn used to prove the goal.
   ------------------------------------------------------------------------ *)

(*
open lcsymtacs
val () = set_trace "Goalstack.print_goal_at_top" 0
val () = set_trace "Goalstack.print_goal_at_top" 1
*)

local
   val spec_debug = ref false
   val () = Feedback.register_btrace ("stateLib.spec", spec_debug)
   val PRINT_TAC =
      RULE_ASSUM_TAC (CONV_RULE PRINT_CONV) THEN CONV_TAC PRINT_CONV
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
   val cond_STAR1_I =
      utilsLib.qm [cond_STAR1, combinTheory.I_THM]
         ``(set_sep$cond c * p) (s:'a set) = I c /\ p s``
in
   fun spec imp_spec imp_temp read_thms write_thms select_state_thms frame_thms
            component_11 map_tys EXTRA_TAC STATE_TAC =
      let
         open lcsymtacs
         val sthms = cond_STAR1_I :: select_state_thms
         val pthms = [boolTheory.DE_MORGAN_THM, pred_setTheory.NOT_IN_EMPTY,
                      pred_setTheory.IN_DIFF, pred_setTheory.IN_INSERT]
         val UPD_TAC = UPDATE_TAC map_tys
         val PRE_TAC =
            GEN_TAC
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
                ASM_SIMP_TAC (pure_ss++simpLib.rewrites frame_thms) []
                \\ (
                    REFL_TAC
                    ORELSE (RW_TAC pure_ss frame_thms
                            \\ (REFL_TAC ORELSE PRINT_TAC))
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
            \\ (REFL_TAC ORELSE ALL_TAC)
         val NEXT_TAC =
            RULE_ASSUM_TAC (PURE_REWRITE_RULE [combinTheory.I_THM])
            \\ ASM_REWRITE_TAC read_thms
            \\ EXTRA_TAC
            \\ PRINT_TAC
         fun tac (v, dthm) =
            MATCH_MP_TAC (if generate_temporal () then imp_temp else imp_spec)
            \\ PRE_TAC
            \\ Tactic.EXISTS_TAC v
            \\ CONJ_TAC
            >- (
                MATCH_MP_TAC dthm
                \\ NEXT_TAC
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
            handle e as HOL_ERR _ =>
                   (if !spec_debug
                       then (proofManagerLib.set_goal ([], t); thm)
                    else raise e)
      end
end

(* ------------------------------------------------------------------------ *)

end
