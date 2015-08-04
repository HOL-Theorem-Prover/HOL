structure utilsLib :> utilsLib =
struct

open HolKernel boolLib bossLib
open state_transformerTheory
open wordsLib integer_wordLib bitstringLib

val ERR = Feedback.mk_HOL_ERR "utilsLib"
val WARN = Feedback.HOL_WARNING "utilsLib"

(* ------------------------------------------------------------------------- *)

fun cache size cmp f =
   let
      val d = ref (Redblackmap.mkDict cmp)
      val k = ref []
      val finite = 0 < size
   in
      fn v =>
         case Redblackmap.peek (!d, v) of
            SOME r => r
          | NONE =>
               let
                  val r = f v
               in
                  if finite
                     then (k := !k @ [v]
                           ; if size < Redblackmap.numItems (!d)
                                then case List.getItem (!k) of
                                        SOME (h, t) =>
                                          (d := fst (Redblackmap.remove (!d, h))
                                           ; k := t)
                                      | NONE => raise ERR "cache" "empty"
                              else ())
                  else ()
                  ; d := Redblackmap.insert (!d, v, r)
                  ; r
               end
   end

(* ------------------------------------------------------------------------- *)

fun partitions [] = []
  | partitions [x] = [[[x]]]
  | partitions (h::t) =
      let
         val ps = partitions t
      in
         List.concat
           (List.map
              (fn p =>
                  List.tabulate
                     (List.length p,
                      fn i =>
                         Lib.mapi (fn j => fn l =>
                                      if i = j then h :: l else l) p)) ps) @
          List.map (fn l => [h] :: l) ps
      end

fun classes eq =
   let
      fun add x =
         let
            fun iter a =
               fn [] => [x] :: a
                | h :: t => if eq (x, hd h)
                               then a @ ((x :: h) :: t)
                            else iter (h :: a) t
         in
            iter []
         end
      fun iter a =
         fn [] => a
          | h :: t => iter (add h a) t
   in
      iter []
   end

(* ------------------------------------------------------------------------- *)

local
   fun loop a =
      fn [] => a
       | r => (case Lib.total (Lib.split_after 8) r of
                  SOME (x, y) => loop (x :: a) y
                | NONE => r :: a)
in
   fun rev_endian l = List.concat (loop [] l)
end

(* ------------------------------------------------------------------------- *)

local
   fun find_pos P =
      let
         fun iter n [] = n
           | iter n (h::t) = if P h then n else iter (n + 1) t
      in
         iter 0
      end
in
   fun process_option P g s d l f =
      let
         val (l, r) = List.partition P l
         val positions = Lib.mk_set (List.map g l)
         val result =
            if List.null positions
               then d
            else if List.length positions = 1
               then f (hd positions)
            else raise ERR "process_option" ("More than one " ^ s ^ " option.")
      in
         (result, r)
      end
   fun process_opt opt = process_option (Lib.C Lib.mem (List.concat opt))
                           (fn option => find_pos (Lib.mem option) opt)
end

(* ------------------------------------------------------------------------- *)

fun maximal (cmp: 'a cmp) f =
   let
      fun max_acc (best as (left, vm, m, right)) l =
         fn [] => (m, List.revAppend (left, right))
          | h :: t =>
              let
                 val vh = f h
                 val best' = case cmp (vh, vm) of
                                General.GREATER => (l, vh, h, t)
                              | _ => best
              in
                 max_acc best' (h :: l) t
              end
   in
      fn [] => raise ERR "maximal" "empty"
       | h :: t => max_acc ([], f h, h, t) [h] t
   end

fun minimal cmp = maximal (Lib.flip_cmp cmp)

(* ------------------------------------------------------------------------- *)

fun padLeft c n l = List.tabulate (n - List.length l, fn _ => c) @ l
(* fun padRight c n l = l @ List.tabulate (n - List.length l, fn _ => c) *)

fun pick [] l2 = (WARN "pick" "not picking"; l2)
  | pick l1 l2 =
      let
         val l = Lib.zip l1 l2
      in
         List.mapPartial (fn (a, b) => if a then SOME b else NONE) l
      end

type cover = {redex: term frag list, residue: term} list list

fun augment (v, l1) l2 =
   List.concat (List.map (fn x => List.map (fn c => ((v |-> x) :: c)) l2) l1)

fun zipLists f =
   let
      fun loop a l =
         if List.null (hd l) then List.map f (List.rev a)
         else loop (List.map List.hd l::a) (List.map List.tl l)
   in
      loop []
   end

fun list_mk_wordii w = List.map (fn i => wordsSyntax.mk_wordii (i, w))

fun tab_fixedwidth m w =
   List.tabulate (m, fn n => bitstringSyntax.padded_fixedwidth_of_int (n, w))

local
   fun liftSplit f = (Substring.string ## Substring.string) o f o Substring.full
in
   fun splitAtChar P = liftSplit (Substring.splitl (not o P))
   fun splitAtPos n = liftSplit (fn s => Substring.splitAt (s, n))
end

val lowercase = String.map Char.toLower
val uppercase = String.map Char.toUpper

val removeSpaces =
   String.translate (fn c => if Char.isSpace c then "" else String.str c)

val long_term_to_string =
   Lib.with_flag (Globals.linewidth, 1000) Hol_pp.term_to_string

val lhsc = boolSyntax.lhs o Thm.concl
val rhsc = boolSyntax.rhs o Thm.concl
val eval = rhsc o bossLib.EVAL
val dom = fst o Type.dom_rng
val rng = snd o Type.dom_rng

local
   val cnv = Conv.QCONV (REWRITE_CONV [boolTheory.DE_MORGAN_THM])
in
   fun mk_negation tm = rhsc (cnv (boolSyntax.mk_neg tm))
end

local
   fun mk_x (s, ty) = Term.mk_var ("x" ^ String.extract (s, 1, NONE), ty)
   fun rename v =
      case Lib.total Term.dest_var v of
         SOME (s_ty as (s, _)) =>
           if String.sub (s, 0) = #"_" then SOME (v |-> mk_x s_ty) else NONE
       | NONE => NONE
   val mk_l = String.implode o Lib.separate #";" o String.explode o uppercase
in
   fun pattern s =
      let
         val tm = Parse.Term [HOLPP.QUOTE ("[" ^ mk_l s ^ "]")]
      in
         Term.subst (List.mapPartial rename (Term.free_vars tm)) tm
      end
end

val strip_add_or_sub =
   let
      fun iter a t =
         case Lib.total wordsSyntax.dest_word_add t of
            SOME (l, r) => iter ((true, r) :: a) l
          | NONE => (case Lib.total wordsSyntax.dest_word_sub t of
                        SOME (l, r) => iter ((false, r) :: a) l
                      | NONE => (t, a))
   in
      iter []
   end

val get_function =
   fst o boolSyntax.strip_comb o boolSyntax.lhs o
   snd o boolSyntax.strip_forall o List.hd o boolSyntax.strip_conj o Thm.concl

fun vacuous thm =
   let
      val (h, c) = Thm.dest_thm thm
   in
      c = boolSyntax.T orelse List.exists (Lib.equal boolSyntax.F) h
   end

fun add_to_rw_net f (thm: thm, n) = LVTermNet.insert (n, ([], f thm), thm)

fun mk_rw_net f = List.foldl (add_to_rw_net f) LVTermNet.empty

fun find_rw net tm =
   case LVTermNet.match (net, tm) of
      [] => raise ERR "find_rw" "not found"
    | l => List.map snd l: thm list

(* ---------------------------- *)

local
   val cmp = reduceLib.num_compset ()
   val () = computeLib.add_thms
              [pairTheory.UNCURRY, combinTheory.o_THM,
               state_transformerTheory.FOR_def,
               state_transformerTheory.BIND_DEF,
               state_transformerTheory.UNIT_DEF] cmp
   val FOR_CONV = computeLib.CBV_CONV cmp
   fun term_frag_of_int i = [QUOTE (Int.toString i)]: term frag list
in
   fun for_thm (h, l) =
      state_transformerTheory.FOR_def
      |> Conv.CONV_RULE (Conv.DEPTH_CONV Conv.FUN_EQ_CONV)
      |> Q.SPECL [term_frag_of_int h, term_frag_of_int l, `a`, `s`]
      |> Conv.RIGHT_CONV_RULE FOR_CONV
      |> Drule.GEN_ALL
end

(* ---------------------------- *)

(* Variant of UNDISCH
   [..] |- a1 /\ ... /\ aN ==> t    |->
   [.., a1, .., aN] |- t
*)

local
   fun AND_INTRO_CONV n tm =
      if n = 0 then ALL_CONV tm
      else (Conv.REWR_CONV satTheory.AND_IMP
            THENC Conv.RAND_CONV (AND_INTRO_CONV (n - 1))) tm
in
   fun STRIP_UNDISCH th =
      let
         val ps =
            boolSyntax.strip_conj (fst (boolSyntax.dest_imp (Thm.concl th)))
         val th' = Conv.CONV_RULE (AND_INTRO_CONV (List.length ps - 1)) th
      in
         Drule.LIST_MP (List.map Thm.ASSUME ps) th'
      end
end

val save_as = Lib.curry Theory.save_thm
fun usave_as s = save_as s o STRIP_UNDISCH
fun ustore_thm (s, t, tac) = usave_as s (Q.prove (t, tac))

(* Variant of UNDISCH
   [..] |- T ==> t    |->   [..] |- t
   [..] |- F ==> t    |->   [..] |- T
   [..] |- p ==> t    |->   [.., p] |- t
*)

local
   val thms = Drule.CONJUNCTS (Q.SPEC `t` boolTheory.IMP_CLAUSES)
   val T_imp = Drule.GEN_ALL (hd thms)
   val F_imp = Drule.GEN_ALL (List.nth (thms, 2))
   val NT_imp = DECIDE ``(~F ==> t) = t``
   val T_imp_rule = Conv.CONV_RULE (Conv.REWR_CONV T_imp)
   val F_imp_rule = Conv.CONV_RULE (Conv.REWR_CONV F_imp)
   val NT_imp_rule = Conv.CONV_RULE (Conv.REWR_CONV NT_imp)
   fun dest_neg_occ_var tm1 tm2 =
      case Lib.total boolSyntax.dest_neg tm1 of
         SOME v => if Term.is_var v andalso not (Term.var_occurs v tm2)
                      then SOME v
                   else NONE
       | NONE => NONE
in
   fun ELIM_UNDISCH thm =
      case Lib.total boolSyntax.dest_imp (Thm.concl thm) of
         SOME (l, r) =>
            if l = boolSyntax.T
               then T_imp_rule thm
            else if l = boolSyntax.F
               then F_imp_rule thm
            else if Term.is_var l andalso not (Term.var_occurs l r)
               then T_imp_rule (Thm.INST [l |-> boolSyntax.T] thm)
            else (case dest_neg_occ_var l r of
                     SOME v => F_imp_rule (Thm.INST [v |-> boolSyntax.F] thm)
                   | NONE => Drule.UNDISCH thm)
       | NONE => raise ERR "ELIM_UNDISCH" ""
end

fun LIST_DISCH tms thm = List.foldl (Lib.uncurry Thm.DISCH) thm tms

(* ---------------------------- *)

local
   val rl =
      REWRITE_RULE [boolTheory.NOT_CLAUSES, GSYM boolTheory.AND_IMP_INTRO,
                    boolTheory.DE_MORGAN_THM]
   val pats = [``~ ~a: bool``, ``a /\ b``, ``~(a \/ b)``]
   fun mtch tm = List.exists (fn p => Lib.can (Term.match_term p) tm) pats
in
   fun HYP_CANON_RULE thm =
      let
         val hs = List.filter mtch (Thm.hyp thm)
      in
         List.foldl
           (fn (h, t) => repeat ELIM_UNDISCH (rl (Thm.DISCH h t))) thm hs
      end
end

(* Apply rule to hyphothesis tm *)

fun HYP_RULE r tm = ELIM_UNDISCH o r o Thm.DISCH tm

(* Apply rule to hyphotheses satisfying P *)

fun PRED_HYP_RULE r P thm =
   List.foldl (Lib.uncurry (HYP_RULE r)) thm (List.filter P (Thm.hyp thm))

(* Apply rule to hyphotheses matching pat *)

fun MATCH_HYP_RULE r pat = PRED_HYP_RULE r (Lib.can (Term.match_term pat))

(* Apply conversion c to all hyphotheses *)

fun ALL_HYP_RULE r = PRED_HYP_RULE r (K true)

local
   fun LAND_RULE c = Conv.CONV_RULE (Conv.LAND_CONV c)
in
   fun HYP_CONV_RULE c = HYP_RULE (LAND_RULE c)
   fun PRED_HYP_CONV_RULE c = PRED_HYP_RULE (LAND_RULE c)
   fun MATCH_HYP_CONV_RULE c = MATCH_HYP_RULE (LAND_RULE c)
   fun ALL_HYP_CONV_RULE c = ALL_HYP_RULE (LAND_RULE c)
   fun FULL_CONV_RULE c = ALL_HYP_CONV_RULE c o Conv.CONV_RULE c
end

(* ---------------------------- *)

(* CBV_CONV but fail if term unchanged *)
fun CHANGE_CBV_CONV cmp = Conv.CHANGED_CONV (computeLib.CBV_CONV cmp)

local
   val alpha_rwts =
        [boolTheory.COND_ID, wordsTheory.WORD_SUB_RZERO,
         wordsTheory.WORD_ADD_0, wordsTheory.WORD_MULT_CLAUSES,
         wordsTheory.WORD_AND_CLAUSES, wordsTheory.WORD_OR_CLAUSES,
         wordsTheory.WORD_XOR_CLAUSES, wordsTheory.WORD_EXTRACT_ZERO2,
         wordsTheory.w2w_0, wordsTheory.WORD_SUB_REFL, wordsTheory.SHIFT_ZERO]
in
   val WALPHA_CONV = REWRITE_CONV alpha_rwts
   val WGROUND_CONV =
      Conv.DEPTH_CONV (wordsLib.WORD_GROUND_CONV false)
      THENC PURE_REWRITE_CONV alpha_rwts
end

fun NCONV n conv = Lib.funpow n (Lib.curry (op THENC) conv) Conv.ALL_CONV
fun SRW_CONV thms = SIMP_CONV (srw_ss()) thms
val EXTRACT_CONV = SIMP_CONV (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
val SET_CONV = SIMP_CONV (bool_ss++pred_setLib.PRED_SET_ss) []
fun SRW_RULE thms = Conv.CONV_RULE (SRW_CONV thms)
val SET_RULE = Conv.CONV_RULE SET_CONV
val o_RULE = REWRITE_RULE [combinTheory.o_THM]

fun qm l = Feedback.trace ("metis", 0) (metisLib.METIS_PROVE l)
fun qm_tac l = Feedback.trace ("metis", 0) (metisLib.METIS_TAC l)

local
   val f = Term.rator o lhsc o Drule.SPEC_ALL
   fun g tm =
      let
         val ty = dom (dom (Term.type_of tm))
         val v = Term.mk_var ("v", ty)
         val kv = boolSyntax.mk_icomb (combinSyntax.K_tm, v)
      in
         Term.mk_comb (tm, Term.inst [Type.beta |-> ty] kv)
      end
in
   fun accessor_fns ty = List.map f (TypeBase.accessors_of ty)
   fun update_fns ty = List.map (g o Term.rator o f) (TypeBase.updates_of ty)
end

fun map_conv (cnv: conv) = Drule.LIST_CONJ o List.map cnv

local
   val thm2l =
      qm [] ``!f:'a -> 'b -> 'c.
                f (if b then x else y) z = (if b then f x z else f y z)``
   val thm2r =
      qm [] ``!f:'a -> 'b -> 'c.
                f z (if b then x else y) = (if b then f z x else f z y)``
   fun is_binop tm =
      case boolSyntax.strip_fun (Term.type_of tm) of
         ([ty1, ty2], ty3) =>
            ty1 = ty2 andalso (ty3 = Type.bool orelse ty3 = ty1)
       | _ => false
   fun spec_thm tm =
      let
         val rule = Drule.GEN_ALL o o_RULE o Drule.ISPEC tm
      in
         if is_binop tm
            then Thm.CONJ (rule thm2l) (rule thm2r)
         else rule boolTheory.COND_RAND
      end
in
   val mk_cond_rand_thms = map_conv spec_thm
end

local
   val COND_UPDATE0 = Q.prove(
      `!b s1 s2. (if b then ((), s1) else ((), s2)) =
                 ((), if b then s1 else s2)`,
      RW_TAC std_ss [])
   val COND_UPDATE1 = Q.prove(
      `!f b v1 v2 s1 s2.
         (if b then f (K v1) s1 else f (K v2) s2) =
         f (K (if b then v1 else v2)) (if b then s1 else s2)`,
      Cases_on `b` THEN REWRITE_TAC [])
   val COND_UPDATE2 = Q.prove(
      `(!b a x y f.
         (if b then (a =+ x) f else (a =+ y) f) =
         (a =+ if b then x else y) f) /\
       (!b a x y f.
         (if b then f else (a =+ y) f) = (a =+ if b then f a else y) f) /\
       (!b a x y f.
         (if b then (a =+ x) f else f) = (a =+ if b then x else f a) f)`,
      REPEAT CONJ_TAC
      THEN Cases
      THEN REWRITE_TAC [combinTheory.APPLY_UPDATE_ID])
   val COND_UPDATE3 = qm [] ``!b. (if b then T else F) = b``
   fun cond_update_thms ty =
      let
         val {Thy, Tyop, ...} = Type.dest_thy_type ty
         val component_equality = DB.fetch Thy (Tyop ^ "_component_equality")
      in
         List.map
           (fn (t1, t2) =>
              let
                 val thm = Drule.ISPEC (boolSyntax.rator t2) COND_UPDATE1
                 val thm0 = Drule.SPEC_ALL thm
                 val v = hd (Term.free_vars t2)
                 val (v1, v2, s1, s2) =
                    case boolSyntax.strip_forall (Thm.concl thm) of
                       ([_, v1, v2, s1, s2], _) => (v1, v2, s1, s2)
                     | _ => raise ERR "mk_cond_update_thms" ""
                 val s1p = Term.mk_comb (t1, s1)
                 val s2p = Term.mk_comb (t1, s2)
                 val id_thm =
                    Tactical.prove(
                       boolSyntax.mk_eq
                          (Term.subst [v |-> s1p] (Term.mk_comb (t2, s1)), s1),
                       SRW_TAC [] [component_equality])
                 val rule = Drule.GEN_ALL o REWRITE_RULE [id_thm]
                 val thm1 = rule (Thm.INST [v1 |-> s1p] thm0)
                 val thm2 = rule (Thm.INST [v2 |-> s2p] thm0)
              in
                 [thm, thm1, thm2]
              end)
           (ListPair.zip (accessor_fns ty, update_fns ty))
           |> List.concat
      end
in
   fun mk_cond_update_thms l =
      [boolTheory.COND_ID, COND_UPDATE0, COND_UPDATE2, COND_UPDATE3] @
      List.concat (List.map cond_update_thms l)
end

(* Substitution allowing for type match *)

local
   fun match_residue {redex = a, residue = b} =
      let
         val m = Type.match_type (Term.type_of b) (Term.type_of a)
      in
         a |-> Term.inst m b
      end
in
   fun match_subst s = Term.subst (List.map match_residue s)
end

(*
fun match_mk_eq (a, b) =
   let
      val m = Type.match_type (Term.type_of b) (Term.type_of a)
   in
      boolSyntax.mk_eq (a, Term.inst m b)
   end

fun mk_eq_contexts (a, l) = List.map (fn b => [match_mk_eq (a, b)]) l
*)

fun avoid_name_clashes tm2 tm1 =
   let
      val v1 = Term.free_vars tm1
      val v2 = Term.free_vars tm2
      val ns = List.map (fst o Term.dest_var) v2
      val (l, r) =
         List.partition (fn v => Lib.mem (fst (Term.dest_var v)) ns) v1
      val v2 = v2 @ r
      val sb = List.foldl
                  (fn (v, (sb, avoids)) =>
                     let
                        val v' = Lib.with_flag (Globals.priming, SOME "_")
                                    (Term.variant avoids) v
                     in
                        ((v |-> v') :: sb, v' :: avoids)
                     end) ([], v2) l
   in
      Term.subst (fst sb) tm1
   end

local
   fun mk_fupd s f = s ^ "_" ^ f ^ "_fupd"
   val name = fst o Term.dest_const o fst o Term.dest_comb
in
   fun mk_state_id_thm eqthm =
      let
         val ty = Term.type_of (fst (boolSyntax.dest_forall (Thm.concl eqthm)))
         fun mk_thm l =
            let
               val {Tyop, Thy, ...} = Type.dest_thy_type ty
               val mk_f = mk_fupd Tyop
               val fns = update_fns ty
               fun get s = List.find (fn f => name f = mk_f s) fns
               val l1 = List.mapPartial get l
               val s = Term.mk_var ("s", ty)
               val h = hd l1
               val id = Term.prim_mk_const {Thy = Thy, Name = Tyop ^ "_" ^ hd l}
               val id =
                  Term.subst [hd (Term.free_vars h) |-> Term.mk_comb (id, s)] h
               val after = List.foldr
                              (fn (f, tm) =>
                                 let
                                    val f1 = avoid_name_clashes tm f
                                 in
                                    Term.mk_comb (f1, tm)
                                 end) s (tl l1)
               val goal = boolSyntax.mk_eq (Term.mk_comb (id, after), after)
            in
               Drule.GEN_ALL (Tactical.prove (goal, bossLib.SRW_TAC [] [eqthm]))
            end
      in
         Drule.LIST_CONJ o List.map mk_thm
      end
end

(* ---------------------------- *)

(* Rewrite tm using theorem thm, instantiating free variables from hypotheses
   as required *)

local
   fun TRY_EQ_FT thm =
      if boolSyntax.is_eq (Thm.concl thm)
         then thm
      else (Drule.EQF_INTRO thm handle HOL_ERR _ => Drule.EQT_INTRO thm)
in
   fun INST_REWRITE_CONV1 thm =
      let
         val mtch = Term.match_term (boolSyntax.lhs (Thm.concl thm))
      in
         fn tm => PURE_ONCE_REWRITE_CONV [Drule.INST_TY_TERM (mtch tm) thm] tm
                  handle HOL_ERR _ => raise ERR "INST_REWRITE_CONV1" ""
      end
   fun INST_REWRITE_CONV l =
      let
         val thms =
            l |> List.map (Drule.CONJUNCTS o Drule.SPEC_ALL)
              |> List.concat
              |> List.map (TRY_EQ_FT o Drule.SPEC_ALL)
         val net = List.partition (List.null o Thm.hyp) o
                   find_rw (mk_rw_net lhsc thms)
      in
         Conv.REDEPTH_CONV
           (fn tm =>
               case net tm of
                  ([], []) => raise Conv.UNCHANGED
                | (thm :: _, _) => Conv.REWR_CONV thm tm
                | ([], thm :: _) => INST_REWRITE_CONV1 thm tm)
      end
   fun INST_REWRITE_RULE thm = Conv.CONV_RULE (INST_REWRITE_CONV thm)
end

(* ---------------------------- *)

(*
  Given two theorems of the form:

    [..., tm, ...] |- a
    [..., ~tm, ...] |- a

  produce theorem of the form

    [...] |- a
*)
local
   val rule =
      Conv.CONV_RULE
         (Conv.CHANGED_CONV
             (REWRITE_CONV [DECIDE ``(b ==> a) /\ (~b ==> a) = a``,
                            DECIDE ``(~b ==> a) /\ (b ==> a) = a``]))
   fun SMART_DISCH tm thm =
      let
         val l = Thm.hyp thm
         val thm' = Thm.DISCH tm thm
         val l' = Thm.hyp thm'
      in
         if List.length l' < List.length l
            then thm'
         else let
                 val thm' = Thm.DISCH (boolSyntax.mk_neg tm) thm
                 val l' = Thm.hyp thm'
              in
                 if List.length l' < List.length l
                    then thm'
                 else raise ERR "SMART_DISCH" "Term not in hypotheses"
              end
      end
in
   fun MERGE_CASES tm thm1 thm2 =
      let
         val thm3 = SMART_DISCH tm thm1
         val thm4 = SMART_DISCH tm thm2
      in
         rule (Thm.CONJ thm3 thm4)
      end
end

(* ---------------------------- *)

local
   fun base t =
      case Lib.total boolSyntax.dest_neg t of
         SOME s => base s
       | NONE =>
          (case Lib.total boolSyntax.lhs t of
              SOME s => s
            | NONE => t)
   fun find_occurance r t =
      Lib.can (HolKernel.find_term (Lib.equal (base t))) r
   val modified = ref 0
   fun specialize (conv, tms) thm =
      let
         val hs = Thm.hyp thm
         val hs = List.filter (fn h => List.exists (find_occurance h) tms) hs
         val sthm = thm |> LIST_DISCH hs
                        |> REWRITE_RULE (List.map ASSUME tms)
                        |> Conv.CONV_RULE conv
                        |> Drule.UNDISCH_ALL
      in
         if vacuous sthm then NONE else (Portable.inc modified; SOME sthm)
      end handle Conv.UNCHANGED => SOME thm
in
   fun specialized msg ctms thms =
      let
         val sz = Int.toString o List.length
         val () = print ("Specializing " ^ msg ^ ": " ^ sz thms ^ " -> ")
         val () = modified := 0
         val r = List.mapPartial (specialize ctms) thms
      in
         print (sz r ^ "(" ^ Int.toString (!modified) ^ ")\n"); r
      end
end

(* ---------------------------- *)

(* case split theorem. For example: split_conditions applied to

     |- q = ((if b then x else y), c)

   gives theorems

     [[~b] |- q = (y, c), [b] |- q = (x, c)]
*)

local
   fun p q = Drule.UNDISCH (Q.prove(q, RW_TAC bool_ss []))
   val split_xt = p `b ==> ((if b then x else y) = x: 'a)`
   val split_yt = p `~b ==> ((if b then x else y) = y: 'a)`
   val split_zt = p `b ==> ((if ~b then x else y) = y: 'a)`
   val split_xl = p `b ==> (((if b then x else y), c) = (x, c): 'a # 'b)`
   val split_yl = p `~b ==> (((if b then x else y), c) = (y, c): 'a # 'b)`
   val split_zl = p `b ==> (((if ~b then x else y), c) = (y, c): 'a # 'b)`
   val split_xr = p `b ==> ((c, (if b then x else y)) = (c, x): 'b # 'a)`
   val split_yr = p `~b ==> ((c, (if b then x else y)) = (c, y): 'b # 'a)`
   val split_zr = p `b ==> ((c, (if ~b then x else y)) = (c, y): 'b # 'a)`
   val vb = Term.mk_var ("b", Type.bool)
   fun REWR_RULE thm = Conv.RIGHT_CONV_RULE (Conv.REWR_CONV thm)
   fun cond_true b = Thm.INST [vb |-> b] split_xt
   fun cond_false b = Thm.INST [vb |-> b] split_yt
   fun split_cond tm =
      case Lib.total pairSyntax.dest_pair tm of
         SOME (a, b) =>
          (case Lib.total boolSyntax.dest_cond a of
              SOME bxy => SOME (split_xl, split_yl, split_zl, bxy)
            | NONE => (case Lib.total boolSyntax.dest_cond b of
                          SOME bxy => SOME (split_xr, split_yr, split_zr, bxy)
                        | NONE => NONE))
       | NONE => Lib.total
                     (fn t => (split_xt, split_yt, split_zt,
                               boolSyntax.dest_cond t)) tm
in
   val split_conditions =
      let
         fun loop a t =
            case split_cond (rhsc t) of
               SOME (splitx, splity, splitz, (b, x, y)) =>
                  let
                     val ty = Term.type_of x
                     val vx = Term.mk_var ("x", ty)
                     val vy = Term.mk_var ("y", ty)
                     fun s cb = Drule.INST_TY_TERM
                                 ([vb |-> cb, vx |-> x, vy |-> y],
                                  [Type.alpha |-> ty])
                     val (split_yz, nb) =
                        case Lib.total boolSyntax.dest_neg b of
                           SOME nb => (splitz, nb)
                         | NONE => (splity, b)
                  in
                     loop (loop a (REWR_RULE (s b splitx) t))
                                  (REWR_RULE (s nb split_yz) t)
                  end
             | NONE => t :: a
      in
         loop []
      end
   fun paths [] = []
     | paths (h :: t) =
         [[cond_false h]] @ (List.map (fn p => cond_true h :: p) (paths t))
end

(* ---------------------------- *)

(* Support for rewriting/evaluation *)

val basic_rewrites =
   [state_transformerTheory.FOR_def,
    state_transformerTheory.BIND_DEF,
    combinTheory.APPLY_UPDATE_THM,
    combinTheory.K_o_THM,
    combinTheory.K_THM,
    combinTheory.o_THM,
    pairTheory.FST,
    pairTheory.SND,
    pairTheory.pair_case_thm,
    pairTheory.CURRY_DEF,
    optionTheory.option_case_compute,
    optionTheory.IS_SOME_DEF,
    optionTheory.THE_DEF]

local
   fun in_conv conv tm =
      case Lib.total pred_setSyntax.dest_in tm of
         SOME (a1, a2) =>
            if pred_setSyntax.is_set_spec a2
               then pred_setLib.SET_SPEC_CONV tm
            else pred_setLib.IN_CONV conv tm
       | NONE => raise ERR "in_conv" "not an IN term";
in
   fun add_base_datatypes cmp =
      let
         val cnv = computeLib.CBV_CONV cmp
      in
         computeLib.add_thms basic_rewrites cmp
         ; List.app (fn x => computeLib.add_conv x cmp)
             [(pred_setSyntax.in_tm, 2, in_conv cnv),
              (pred_setSyntax.insert_tm, 2, pred_setLib.INSERT_CONV cnv)]
      end
end

local
   (* Taken from src/datatype/EnumType.sml *)
   fun gen_triangle l =
      let
         fun gen_row i [] acc = acc
           | gen_row i (h::t) acc = gen_row i t ((i,h)::acc)
         fun doitall [] acc = acc
           | doitall (h::t) acc = doitall t (gen_row h t acc)
      in
         List.rev (doitall l [])
      end
   fun datatype_rewrites1 ty =
      case TypeBase.simpls_of ty of
        {convs = [], rewrs = r} => r
      | {convs = {conv = c, name = n, ...} :: _, rewrs = r} =>
            if String.isSuffix "const_eq_CONV" n
               then let
                       val neq = Drule.EQF_ELIM o
                                 c (K Conv.ALL_CONV) [] o
                                 boolSyntax.mk_eq
                       val l = ty |> TypeBase.constructors_of
                                  |> gen_triangle
                                  |> List.map neq
                                  |> Drule.LIST_CONJ
                    in
                       [l, GSYM l] @ r
                    end
            else r
in
   fun datatype_rewrites extra thy l =
      let
         fun typ name = Type.mk_thy_type {Thy = thy, Args = [], Tyop = name}
      in
         (if extra then List.drop (basic_rewrites, 2) else []) @
         List.concat (List.map (datatype_rewrites1 o typ) l)
      end
end

local
   fun fetch1 thy name =
      case Lib.total (DB.fetch thy) name of
         SOME thm => [thm]
       | NONE => []
   val err = ERR "enum_eq_CONV" "Equality not between constants"
   fun add_datatype cmp ty =
      case Type.dest_thy_type ty of
         {Thy = thy, Args = [], Tyop = name} =>
         let
            val ftch = fetch1 thy
            val ty2num = ftch (name ^ "2num_thm")
            val num2ty = ftch ("num2" ^ name ^ "_thm")
            val fupds = TypeBase.updates_of ty
            fun add r = computeLib.add_thms (r @ ty2num @ num2ty @ fupds) cmp
         in
            (case Lib.total TypeBase.case_const_of ty of
                SOME tm => computeLib.set_skip cmp tm NONE
              | NONE => ())
            ; case TypeBase.simpls_of ty of
                 {convs = [], rewrs = r} => add r
               | {convs = {name = n, ...} :: _, rewrs = r} =>
                 ( add r
                 ; if String.isSuffix "const_eq_CONV" n (* enumerated *)
                      then case (ftch (name ^ "_EQ_" ^ name), ty2num) of
                              ([eq_elim_thm], [_]) =>
                              let
                                 val cnv =
                                    Conv.REWR_CONV eq_elim_thm
                                    THENC PURE_REWRITE_CONV ty2num
                                    THENC reduceLib.REDUCE_CONV
                                 fun ecnv tm =
                                    let
                                       val (l, r) = boolSyntax.dest_eq tm
                                       val _ = Term.is_const l
                                               andalso Term.is_const r
                                               orelse raise err
                                    in
                                       cnv tm
                                    end
                              in
                                 computeLib.add_conv
                                    (boolSyntax.equality, 2, ecnv) cmp
                              end
                            | _ => ()
                   else ())
         end
       | _ => computeLib.add_thms (#rewrs (TypeBase.simpls_of ty)) cmp
in
   fun add_datatypes l cmp = List.app (add_datatype cmp) l
end

type inventory = {C: string list, N: int list, T: string list, Thy: string}

fun theory_types (i: inventory)  =
   let
      val {Thy = thy, T = l, ...} = i
   in
      List.map (fn t => Type.mk_thy_type {Thy = thy, Args = [], Tyop = t}) l
   end

fun filter_inventory names ({Thy = thy, C = l, N = n, T = t}: inventory) =
   let
      val es = List.map (fn s => s ^ "_def") names
   in
      {Thy = thy, C = List.filter (fn t => not (Lib.mem t es)) l, N = n, T = t}
   end

local
   fun bool_bit_thms i =
      let
         val s = Int.toString i
         val b = "boolify" ^ s
      in
         ["bitify" ^ s ^ "_def", b ^ "_n2w", b ^ "_v2w"]
      end
   val get_name = fst o Term.dest_const o fst o HolKernel.strip_comb o
                  boolSyntax.lhs o snd o boolSyntax.strip_forall o
                  List.hd o boolSyntax.strip_conj o Thm.concl
in
   fun theory_rewrites (thms, i: inventory) =
      let
         val thm_names = List.map get_name thms
         val {Thy = thy, C = l, N = n, ...} = filter_inventory thm_names i
         val m = List.concat (List.map bool_bit_thms n)
      in
         List.map (fn t => DB.fetch thy t) (l @ m) @ thms
      end
end

fun add_theory (x as (_, i)) cmp =
   (add_datatypes (theory_types i) cmp
    ; computeLib.add_thms (theory_rewrites x) cmp)

fun add_to_the_compset x = computeLib.add_funs (theory_rewrites x)

fun theory_compset x =
   let
      val cmp = wordsLib.words_compset ()
   in
      add_base_datatypes cmp; add_theory x cmp; cmp
   end

(* ---------------------------- *)

(* Help prove theorems of the form:

|- rec'r (bit_field_insert h l w (reg'r q)) = q with <| ? := ?; ... |>

Where "r" is some register (record) component in the theory "thy".

*)

local
   fun EXTRACT_BIT_CONV tm =
      if fcpSyntax.is_fcp_index tm
         then blastLib.BBLAST_CONV tm
      else Conv.NO_CONV tm
   val bit_field_insert_tm =
      ``bit_field_insert a b (w: 'a word) : 'b word -> 'b word``
in
   fun BIT_FIELD_INSERT_CONV thy r =
      let
         val s = thy ^ "_state"
         val ty1 = Type.mk_thy_type {Thy = thy, Tyop = r, Args = []}
         val ty2 = Type.mk_thy_type {Thy = thy, Tyop = s, Args = []}
         val a = accessor_fns ty1 @ accessor_fns ty2
         val u = update_fns ty1 @ update_fns ty2
      in
         REWRITE_CONV
           ([boolTheory.COND_ID,
             mk_cond_rand_thms (bit_field_insert_tm :: a @ u)] @
             datatype_rewrites true thy [r, s])
         THENC Conv.DEPTH_CONV EXTRACT_BIT_CONV
         THENC Conv.DEPTH_CONV (wordsLib.WORD_BIT_INDEX_CONV true)
      end
   fun REC_REG_BIT_FIELD_INSERT_TAC thy r =
      let
         val cnv = BIT_FIELD_INSERT_CONV thy r
         val f = DB.fetch thy
         val reg' = f ("reg'" ^ r ^ "_def")
         val rec' = f ("rec'" ^ r ^ "_def")
         val eq = f (r ^ "_component_equality")
      in
         fn q =>
            Cases_on q
            THEN TRY STRIP_TAC
            THEN REWRITE_TAC [reg']
            THEN CONV_TAC cnv
            THEN BETA_TAC
            THEN REWRITE_TAC [rec', eq, wordsTheory.bit_field_insert_def]
            THEN CONV_TAC cnv
            THEN REPEAT CONJ_TAC
            THEN blastLib.BBLAST_TAC
      end
end

(* Make a theorem of the form

|- !x. reg'r x = v2w [x.?; ...]

*)

local
   fun mk_component_subst v =
      fn h =>
         let
            val (x, y) = boolSyntax.dest_eq h
         in
            x |-> Term.mk_comb (Term.rator y, v)
         end
   fun eval_idx c i =
      rhsc (numLib.REDUCE_CONV (Term.mk_comb (c, numSyntax.term_of_int i)))
in
   fun mk_reg_thm thy r =
      let
         val ftch = DB.fetch thy
         val reg' = ftch ("reg'" ^ r ^ "_def")
         val a = ftch (r ^ "_accessors")
         val ((_, v), (vs, m)) =
            reg'
            |> Drule.SPEC_ALL
            |> rhsc
            |> Term.dest_comb
            |> (Term.dest_comb ## boolSyntax.strip_abs)
         val ty = Term.type_of v
         val f = case TypeBase.constructors_of ty of
                    [f] => f
                  | _ => raise ERR "" ""
         val mk_s = mk_component_subst v o Thm.concl o SYM o Drule.SPECL vs
         val s = List.map mk_s (Drule.CONJUNCTS a)
         val (ix, cnds) = m |> wordsSyntax.dest_word_modify |> fst
                            |> Term.rand
                            |> pairSyntax.dest_pabs
         val cnds = Term.mk_abs (fst (pairSyntax.dest_pair ix), cnds)
         val ty = wordsSyntax.dim_of m
         val l =
            List.tabulate (fcpSyntax.dest_int_numeric_type ty, eval_idx cnds)
         val tm = (Term.subst s o bitstringSyntax.mk_v2w)
                     (listSyntax.mk_list (List.rev l, Type.bool), ty)
      in
         Tactical.prove
            (boolSyntax.mk_eq (Term.mk_comb (get_function reg', v), tm),
             REC_REG_BIT_FIELD_INSERT_TAC thy r `^v`)
         |> Drule.GEN_ALL
      end
end

(* ---------------------------- *)

local
   val dr = Type.dom_rng o Term.type_of
   val dom = fst o dr
   val rng = snd o dr
   fun mk_def thy tm =
      let
         val name = fst (Term.dest_const tm)
         val (l, r) = splitAtChar (Lib.equal #"@") name
      in
         if r = "" orelse
            Option.isSome (Int.fromString (String.extract (r, 1, NONE)))
            then Term.prim_mk_const {Thy = thy, Name = "dfn'" ^ l}
         else raise ERR "mk_def" ""
      end
   fun buildAst thy ty =
      let
         val cs = TypeBase.constructors_of ty
         val (t0, n) = List.partition (Lib.equal ty o Term.type_of) cs
         val (t1, n) = List.partition (Lib.can (mk_def thy)) n
         val t1 =
            List.map (fn t => Term.mk_comb (t, Term.mk_var ("x", dom t))) t1
         val n =
            List.map (fn t =>
                        let
                           val l = buildAst thy (dom t)
                        in
                           List.map (fn x => Term.mk_comb (t, x)
                           handle HOL_ERR {origin_function = "mk_comb", ...} =>
                             (Parse.print_term t; print "\n";
                              Parse.print_term x; raise ERR "buildAst" "")) l
                        end) n
      in
         t0 @ t1 @ List.concat n
      end
   fun is_call x tm =
      case Lib.total Term.rand tm of
        SOME y => x = y
      | NONE => false
   fun leaf tm =
      case Lib.total Term.rand tm of
        SOME y => leaf y
      | NONE => tm
   fun run_thm0 pv thy ast =
      let
         val tac = SIMP_TAC (srw_ss()) [DB.fetch thy "Run_def"]
         val f = mk_def thy (leaf ast)
      in
         pv (if Term.type_of f = oneSyntax.one_ty
                then `!s. Run ^ast s = (^f, s)`
             else `!s. Run ^ast s = ^f s`) : thm
      end
   fun run_thm pv thy ast =
      let
         val tac = SIMP_TAC (srw_ss()) [DB.fetch thy "Run_def"]
         val x = hd (Term.free_vars ast)
         val tm = Term.rator (HolKernel.find_term (is_call x) ast)
         val f = boolSyntax.mk_icomb (mk_def thy tm, x)
      in
         pv (if Term.type_of f = oneSyntax.one_ty
                then `!s. Run ^ast s = (^f, s)`
             else `!s. Run ^ast s = ^f s`) : thm
      end
   fun run_rwts thy =
      let
         val ty = Type.mk_thy_type {Thy = thy, Args = [], Tyop = "instruction"}
         val (arg0, args) =
            List.partition (List.null o Term.free_vars) (buildAst thy ty)
         val tac = SIMP_TAC (srw_ss()) [DB.fetch thy "Run_def"]
         fun pv q = Q.prove (q, tac)
      in
         List.map (run_thm0 pv thy) arg0 @ List.map (run_thm pv thy) args
      end
   fun run_tm thy = Term.prim_mk_const {Thy = thy, Name = "Run"}
in
   fun mk_run (thy, st) = fn ast => Term.list_mk_comb (run_tm thy, [ast, st])
   fun Run_CONV (thy, st) =
      Thm.GEN st o PURE_REWRITE_CONV (run_rwts thy) o mk_run (thy, st)
end

(* ---------------------------- *)

local
   val rwts = [pairTheory.UNCURRY, combinTheory.o_THM, combinTheory.K_THM]
   val no_hyp = List.partition (List.null o Thm.hyp)
   val add_word_eq =
      computeLib.add_conv (``$= :'a word -> 'a word -> bool``, 2,
                           bitstringLib.word_eq_CONV)
   fun context_subst tm =
      let
         val f = Parse.parse_in_context (Term.free_vars tm)
      in
         List.map (List.map (fn {redex, residue} => f redex |-> residue))
      end
   val step_conv = ref Conv.ALL_CONV
in
   fun resetStepConv () = step_conv := Conv.ALL_CONV
   fun setStepConv c = step_conv := c
   fun STEP (datatype_thms, st) =
      let
         val DATATYPE_CONV = REWRITE_CONV (datatype_thms [])
         fun fix_datatype tm = rhsc (Conv.QCONV DATATYPE_CONV tm)
         val SAFE_ASSUME = Thm.ASSUME o fix_datatype
      in
         fn l => fn ctms => fn s => fn tm =>
            let
               val (nh, h) = no_hyp l
               val c = INST_REWRITE_CONV h
               val cmp = reduceLib.num_compset ()
               val () = computeLib.add_thms (rwts @ nh) cmp
               val () = add_word_eq cmp
               fun cnv rwt =
                  Conv.REPEATC
                    (Conv.TRY_CONV (CHANGE_CBV_CONV cmp)
                     THENC REWRITE_CONV (datatype_thms (rwt @ h))
                     THENC (!step_conv)
                     THENC c)
               val stm = Term.mk_comb (tm, st) handle HOL_ERR _ => tm
               val sbst = context_subst stm s
               fun cnvs rwt =
                  if List.null sbst
                     then [cnv rwt stm]
                  else List.map (fn sub => cnv rwt (match_subst sub stm)) sbst
               val ctxts = List.map (List.map SAFE_ASSUME) ctms
            in
               if List.null ctxts
                  then cnvs []
               else List.concat (List.map cnvs ctxts)
            end
      end
end

end
