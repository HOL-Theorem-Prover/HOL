(* wlogLib.sml - Without loss of generality tacticals

   by Mario Castelán Castro
      (see doc/copyrights/public-domain-contributions.txt)
*)

structure wlogLib :> wlogLib =
struct

open HolKernel Parse boolLib

val ERR = mk_HOL_ERR "wlogLib"

fun LIST_SPLICE l =
  case l of
  [] => raise ERR "LIST_SPLICE" "Empty list"
  | [t1] => REFL t1
  | [t1, t2] => QCONV (SPLICE_CONJ_CONV) (mk_conj (t1, t2))
  | (t::l) =>
    let
      val deep_thm = LIST_SPLICE l
      (* If “deep_thm” is «l ⇔ r», “lifted_deep_thm” is «t ∧ l ⇔ t ∧ r». UOK *)
      val lifted_deep_thm = AP_TERM (mk_comb (conjunction, t)) deep_thm
    in
      RIGHT_CONV_RULE SPLICE_CONJ_CONV lifted_deep_thm
    end

fun DISCH_CONJ l thm =
  let
    fun loop l conj_thm thm =
      case l of
      [x] =>
        PROVE_HYP conj_thm thm
      | [] =>
        thm
      | (x::rest) =>
        loop rest (CONJUNCT2 conj_thm) (PROVE_HYP (CONJUNCT1 conj_thm) thm)
  in
    case l of
      [] => thm
    | [x] => DISCH x thm
    | _ => let val t = list_mk_conj l in DISCH t (loop l (ASSUME t) thm) end
  end

fun UNDISCH_CONJ l thm =
  let
    fun fold_rator (t, acc) =
      CONJ (ASSUME t) acc
  in
    case l of
    [] => thm
    | [t] => MP thm (ASSUME t)
    | _ =>
      let
        val l = rev l
      in
        MP thm (foldl fold_rator (ASSUME (hd l)) (tl l))
      end
  end
  handle HOL_ERR _ => raise ERR "UNDISCH_CONJ" ""

(* Proves
  ⊢ (¬P ⇒ (∀(vars). P_hyp ⇒ t) ⇒ t) ⇒   (* “wlog_thm”. *)                  UOK
     (∀(vars). P ∧ hyp ⇒ t) ⇒           (* “new_sg_thm”. *)                UOK
     hyp ⇒                                                                 UOK
     t»                                                                    UOK
except that when "hyp" is "NONE", it is omitted the obvious way. If "hyp" is
none then "p_hyp" is just "hyp" else it is the splice of "p" with "hyp". The
tuple returned is the aforementioned theorem and "P_hyp". *)
fun wlog_rule vars p hyp t =
  let
    (* val the = liteLib.the (broken in mosml) *)
    fun the (SOME x) = x
      | the _ = failwith "the: can't take \"the\" of NONE"

    fun forall vars t = list_mk_forall (vars, t)
    fun implies t1 t2 = mk_imp (t1, t2)
    val new_sg_t = forall vars (implies (case hyp of
                                           SOME hyp_t => mk_conj (p, hyp_t)
                                         | NONE       => p)
                                        t)
    val new_sg_thm = ASSUME new_sg_t
    val thm_p = MP (SPECL vars new_sg_thm)
                   (case hyp of
                      SOME hyp_t => CONJ (ASSUME p) (ASSUME hyp_t)
                    | NONE       => (ASSUME p))
    val wlog_ant = ref NONE
    val splice_thm = ref NONE
    val _ =
      case hyp of
      NONE =>
        wlog_ant := SOME new_sg_t
      | SOME hyp_t =>
        case SOME (SPLICE_CONJ_CONV (mk_conj (p, hyp_t)))
             handle UNCHANGED => NONE of
        NONE =>
          wlog_ant := SOME new_sg_t
        | SOME thm =>
          (wlog_ant := SOME (forall vars (implies (rhs (concl thm)) t));
           splice_thm := SOME thm)
    val wlog_t = implies (mk_neg p) (implies (the (!wlog_ant)) t)
    val wlog_thm = ASSUME wlog_t
    val (new_sg_thm2, wlog_hyp) =
      case !splice_thm of
      NONE => (new_sg_thm, new_sg_t)
      | SOME thm =>
        let
          val gen_thm = GEN_ABS (SOME universal)
                                vars
                                (AP_THM (AP_TERM implication thm) t)
          val new_sg_thm2 = EQ_MP gen_thm new_sg_thm
        in
          (new_sg_thm2, concl new_sg_thm2)
        end
    val thm_not_p = MP (UNDISCH wlog_thm) new_sg_thm2
    val em_thm = SPEC p EXCLUDED_MIDDLE
    val merged_thm = DISJ_CASES em_thm thm_p thm_not_p
    val final_thm = (case hyp of
                       SOME hyp_t => DISCH hyp_t merged_thm
                     | NONE       => merged_thm) |>
                    DISCH new_sg_t |>
                    DISCH wlog_t
  in
    (final_thm, wlog_hyp)
  end

fun wlog_then q vars_q (ttac :thm_tactic) (g as (asm, c)) =
  let
    open Parse
    val mem = curry HOLset.member
    val lconst = FVL asm empty_tmset
    val context = HOLset.listItems (FVL [c] lconst)
    val p = typed_parse_in_context bool context q
    val extra_vars = map (parse_in_context context) vars_q
    val extra_var_set = HOLset.addList (empty_varset, extra_vars)
    val efv = filter (fn t => not (mem lconst t orelse mem extra_var_set t))
                     (* The conjunction is just an arbitrary way to put p and
                     c into a single term. *)
                     (free_vars_lr (mk_conj (p, c)))
    val gen_vars = extra_vars @ efv
    val marked_asm = filter (fn t => exists (mem extra_var_set) (free_vars t))
                            asm
    val (splice_info_opt, ant, (lemma, wlog_hyp)) =
      if null marked_asm then
        (NONE,
         p,
         wlog_rule gen_vars p NONE c)
      else
        let
          val thm = LIST_SPLICE marked_asm
          val (unspliced_t, spliced_t) = dest_eq (concl thm)
        in
          (SOME {thm = thm, unspliced_t = unspliced_t, spliced_t = spliced_t},
           mk_conj (p, spliced_t),
           wlog_rule gen_vars p (SOME spliced_t) c)
        end
    val not_p = mk_neg p
    val sg1 = (not_p::wlog_hyp::asm, c)
    val (ttac_sg, ttac_verify) = ttac (ASSUME p) (asm, c)
    fun verify (thm1::thm_l) =
      let
        val ttac_thm = ttac_verify thm_l
        (* Corresponds to the subgoal we added in this tactical. *)
        val wlog_thm = DISCH not_p (DISCH wlog_hyp thm1)
      in
        case splice_info_opt of
        SOME splice_info =>
          let
            val (imp_splice, imp_unsplice) =
              EQ_IMP_RULE (#thm splice_info)
            (* Corresponds to the original subgoal processed by the
            user-provided theorem-tactic. *)
            val other_thm =
              MP (DISCH_CONJ marked_asm ttac_thm) (UNDISCH imp_unsplice) |>
              DISCH_CONJ [p, #spliced_t splice_info] |>
              GENL gen_vars
          in
            UNDISCH_CONJ marked_asm (MP (MP lemma wlog_thm) other_thm)
          end
        | NONE =>
          let
            val other_thm = GENL gen_vars (DISCH p ttac_thm)
          in
            MP (MP lemma wlog_thm) other_thm
          end
      end
    | verify _ = raise ERR "wlog_then" "Verification"
  in
    (sg1::ttac_sg, verify)
  end

(* Convenience entry points for var_wlog_then. *)
fun wlog_tac q vars = wlog_then q vars STRIP_ASSUME_TAC

end (* struct *)
