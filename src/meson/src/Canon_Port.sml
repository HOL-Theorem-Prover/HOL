structure Canon_Port :> Canon_Port =
struct

open HolKernel Parse boolLib liteLib Ho_Rewrite tautLib;

(* Fix the grammar used by this file *)
val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars combinTheory.combin_grammars;

val RIGHT_AND_EXISTS_THM = GSYM RIGHT_EXISTS_AND_THM;
val LEFT_AND_EXISTS_THM  = GSYM LEFT_EXISTS_AND_THM;
val OR_EXISTS_THM        = GSYM EXISTS_OR_THM;
val AND_FORALL_THM       = GSYM FORALL_AND_THM;
val LEFT_OR_FORALL_THM   = GSYM LEFT_FORALL_OR_THM;
val RIGHT_OR_FORALL_THM  = GSYM RIGHT_FORALL_OR_THM;
val LEFT_IMP_FORALL_THM  = GSYM LEFT_EXISTS_IMP_THM;
val RIGHT_IMP_FORALL_THM = GSYM RIGHT_FORALL_IMP_THM;
val LEFT_IMP_EXISTS_THM  = boolTheory.LEFT_EXISTS_IMP_THM;
val RIGHT_IMP_EXISTS_THM = GSYM RIGHT_EXISTS_IMP_THM;

val freesl = free_varsl

fun is_eqc tm = same_const equality tm

local
  fun tmi_eq (tm1,i1:int) (tm2,i2) = aconv tm1 tm2 andalso i1 = i2
  val insert = op_insert tmi_eq

  fun get_heads lconsts tm (sofar as (cheads,vheads)) =
        let val (v,bod) = dest_forall tm
        in get_heads (op_set_diff aconv lconsts [v]) bod sofar
        end
        handle HOL_ERR _ =>
            let val (l,r) = dest_conj tm handle HOL_ERR _ => dest_disj tm
            in get_heads lconsts l (get_heads lconsts r sofar)
            end
        handle HOL_ERR _ =>
            let val tm' = dest_neg tm
            in get_heads lconsts tm' sofar
            end
        handle HOL_ERR _ =>
            let val (hop,args) = strip_comb tm
                val len = length args
                val newheads =
                  if is_const hop orelse op_mem aconv hop lconsts
                  then (insert (hop,len) cheads, vheads)
                  else if len > 0
                       then (cheads,insert (hop,len) vheads)
                       else sofar
        in
          itlist (get_heads lconsts) args newheads
        end
in
  fun get_thm_heads th sofar = get_heads (freesl(hyp th)) (concl th) sofar;
end;


local
  val APP_CONV =
    let val eq = ``!f:'a->'b. !x. f x = I f x``
    in REWR_CONV (prove (eq, REWRITE_TAC[combinTheory.I_THM]))
    end

  fun APP_N_CONV n tm =
    if n = 1 then APP_CONV tm
    else (RATOR_CONV (APP_N_CONV (n - 1)) THENC APP_CONV) tm

  fun FOL_CONV hddata tm =
    if is_forall tm then
      BINDER_CONV (FOL_CONV hddata) tm
    else
      if is_conj tm orelse is_disj tm then
        BINOP_CONV (FOL_CONV hddata) tm
      else
        let
          val (opn,args) = strip_comb tm
          val th = rev_itlist (C (curry MK_COMB))
            (map (FOL_CONV hddata) args) (REFL opn)
          val tm' = rand(concl th)
          val n = length args - op_assoc aconv opn hddata
                  handle HOL_ERR _ => 0
        in
          if n = 0 then th
          else TRANS th (APP_N_CONV n tm')
        end
in
  fun GEN_FOL_CONV (cheads,vheads) =
    let val hddata =
          if null vheads
          then let val hops = op_mk_set aconv (map fst cheads)
                   fun getmin h =
                    let val ns = mapfilter
                          (fn (k,n) => if aconv k h then n else fail()) cheads
                    in (if length ns < 2 then fail() else h,
                        end_itlist (curry Int.min) ns)
                    end
               in mapfilter getmin hops
               end
          else map (fn t => if is_eqc t then (t,2) else (t,0))
                   (op_mk_set aconv (map fst (vheads @ cheads)))
    in FOL_CONV hddata
    end
end


local
  val NOT_EXISTS_UNIQUE_THM = Tactical.prove(
    ``~(?!x:'a. P x) = (!x. ~P x) \/ ?x x'. P x /\ P x' /\ ~(x = x')``,
    REWRITE_TAC [EXISTS_UNIQUE_THM, DE_MORGAN_THM,NOT_EXISTS_THM]
     THEN CONV_TAC (REDEPTH_CONV NOT_FORALL_CONV)
     THEN REWRITE_TAC [NOT_IMP, CONJ_ASSOC])
  val common_tauts =
    [TAUT `~~p:bool = p`,
     TAUT `~(p /\ q) = ~p \/ ~q`,
     TAUT `~(p \/ q) = ~p /\ ~q`,
     TAUT `~(p ==> q) = p /\ ~q`,
     TAUT `p ==> q = ~p \/ q`,
     NOT_FORALL_THM,
     NOT_EXISTS_THM,
     EXISTS_UNIQUE_THM,
     NOT_EXISTS_UNIQUE_THM]
  and dnf_tauts =
    map TAUT [`~(p = q) = (p /\ ~q) \/ (~p /\ q)`,
              `(p = q) = (p /\ q) \/ (~p /\ ~q)`]
  and cnf_tauts =
    map TAUT [`~(p = q) = (p \/ q) /\ (~p \/ ~q)`,
              `(p = q) = (p \/ ~q) /\ (~p \/ q)`]
  val NNFC_CONV0 =
    GEN_REWRITE_CONV TOP_SWEEP_CONV (common_tauts @ cnf_tauts)
in
val NNFC_CONV = let
  fun SINGLE_SWEEP_CONV conv tm = let
    fun continue tm = if is_abs tm then NNFC_CONV0 tm
                      else SUB_CONV (SINGLE_SWEEP_CONV conv) tm
  in
    (conv THENC continue) ORELSEC continue
  end tm
in
  SINGLE_SWEEP_CONV (GEN_REWRITE_CONV I (common_tauts @ dnf_tauts))
end
end (* local *)


fun has_abs tm =
  case dest_term tm
   of LAMB _ => true
    | COMB(M,N) => if is_const M andalso is_abs N  (* binder *)
                    then has_abs (body N)
                    else has_abs N orelse has_abs M
    | other => false

val DELAMB_CONV =
  let val pth = prove(
        ``(((\x. s x) = t) = (!x:'a. s x:'b = t x)) /\
           ((s = \x. t x) = (!x. s x = t x))``,
        CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC THEN
        REWRITE_TAC [])
      val qconv =
          TOP_DEPTH_CONV BETA_CONV THENC
          REPEATC (QCHANGED_CONV (GEN_REWRITE_CONV ONCE_DEPTH_CONV [pth]) THENC
                   TOP_DEPTH_CONV BETA_CONV)

      (* used to be:
          THENQC (TOP_DEPTH_QCONV BETA_CONV,
                  REPEATQC (THENCQC
                             (GEN_REWRITE_CONV ONCE_DEPTH_QCONV [pth],
                              TRY_CONV(TOP_DEPTH_QCONV BETA_CONV))))
         using the liteLib converionals.  Here's the argument as to why the
         replacement has the right effect, and fixes a bug when UNCHANGED
         exceptions might be flying around

           THENQC(c1, c2) raises a HOL_ERR iff c1 and c2 both raise errors
           THENCQC(c1, c2) raises a HOL_ERR iff c1 raises an error

         so

           if TOP_DEPTH_QCONV raises a HOL_ERR it will be because it
           hasn't managed to change the input term at all.  The outermost
           THENQC traps this and moves onto its second argument, which is a
           REPEATQC.  This will raise an error if its argument fails
           immediately.  Its argument will fail iff the GEN_REWRITE_CONV
           fails, which will happen only if it doesn't change the argument.

           This suggests that the TRY_CONV is redundant.  Not only is it
           redundant, but when it introduces UNCHANGED, it causes the
           whole conversion to raise UNCHANGED, even though the rewriting
           has actually done some good.

         so

           the replacement drops the TRY_CONV, and replaces THENQC with
           THENC, and THENCQC with (QCHANGED_CONV ... THENC ...)  This
           is not always valid, because THENC only traps UNCHANGED, whereas
           THENQC traps everything, but here the only exceptions coming out
           of the first argument to THENC will be caused by the input term
           not changing.
       *)
  in
    fn tm => if has_abs tm then TRY_CONV qconv tm else ALL_CONV tm
  end;

val PROP_CNF_CONV =
  GEN_REWRITE_CONV REDEPTH_CONV
   [TAUT `a \/ (b /\ c) = (a \/ b) /\ (a \/ c)`,
    TAUT `(a /\ b) \/ c = (a \/ c) /\ (b \/ c)`,
    GSYM CONJ_ASSOC, GSYM DISJ_ASSOC];;


val PRESIMP_CONV =
  GEN_REWRITE_CONV DEPTH_CONV
   [NOT_CLAUSES, AND_CLAUSES, OR_CLAUSES, IMP_CLAUSES, EQ_CLAUSES,
    FORALL_SIMP, EXISTS_SIMP, EXISTS_OR_THM, FORALL_AND_THM,
    LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM,
    LEFT_FORALL_OR_THM, RIGHT_FORALL_OR_THM];


val REFUTE_THEN =
  let val conv = REWR_CONV(TAUT `p = ~p ==> F`)
  in fn ttac => CONV_TAC conv THEN DISCH_THEN ttac
  end;;

val SKOLEM_CONV =
  GEN_REWRITE_CONV REDEPTH_CONV
     [RIGHT_AND_EXISTS_THM,
      LEFT_AND_EXISTS_THM,
      OR_EXISTS_THM,
      RIGHT_OR_EXISTS_THM,
      LEFT_OR_EXISTS_THM,
      SKOLEM_THM];

local fun STRIP conv tm opt =
        let val (vlist,M) = strip_binder opt tm
        in GEN_ABS opt vlist (conv M)
        end
in
fun STRIP_BINDER_CONV conv tm =
  let val Z = STRIP conv tm
  in if is_abs tm then Z NONE else
     if is_forall tm  then Z (SOME boolSyntax.universal) else
     if is_exists tm  then Z (SOME boolSyntax.existential) else
     if is_select tm  then Z (SOME boolSyntax.select) else
     if is_exists1 tm then Z (SOME boolSyntax.exists1)
                      else failwith "STRIP_BINDER_CONV"
  end
end;

val PRENEX_CONV =
 let val PRENEX1_QCONV = GEN_REWRITE_CONV I
      [NOT_FORALL_THM, NOT_EXISTS_THM,
       AND_FORALL_THM, LEFT_AND_FORALL_THM, RIGHT_AND_FORALL_THM,
       LEFT_OR_FORALL_THM, RIGHT_OR_FORALL_THM,
       LEFT_IMP_FORALL_THM, RIGHT_IMP_FORALL_THM,
       LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM,
       OR_EXISTS_THM, LEFT_OR_EXISTS_THM, RIGHT_OR_EXISTS_THM,
       LEFT_IMP_EXISTS_THM, RIGHT_IMP_EXISTS_THM]
     fun PRENEX2_QCONV tm = THENCQC(PRENEX1_QCONV,BINDER_CONV PRENEX2_QCONV) tm
     fun PRENEX_QCONV tm =
       let val (lop,r) = dest_comb tm
       in if is_const lop
          then if same_const lop boolSyntax.universal orelse
                  same_const lop boolSyntax.existential
               then STRIP_BINDER_CONV PRENEX_QCONV tm
(*               then AP_TERM lop (ABS_CONV PRENEX_QCONV r) *)
               else if same_const lop boolSyntax.negation
                    then THENQC (RAND_CONV PRENEX_QCONV, PRENEX2_QCONV) tm
                    else failwith "unchanged"
          else let val (oper,l) = dest_comb lop
               in if same_const oper boolSyntax.conjunction orelse
                     same_const oper boolSyntax.disjunction orelse
                     same_const oper boolSyntax.implication
                  then let val th =
                         (let val lth = PRENEX_QCONV l
                          in let val rth = PRENEX_QCONV r
                             in MK_COMB(AP_TERM oper lth,rth)
                             end handle HOL_ERR _ => AP_THM(AP_TERM oper lth) r
                          end handle HOL_ERR _ => AP_TERM lop (PRENEX_QCONV r)
                         ) handle HOL_ERR _ => REFL tm
                       in
                          TRANS th (PRENEX2_QCONV (rand(concl th)))
                       end
                  else failwith "unchanged"
               end
       end
 in
   fn tm => TRY_CONV PRENEX_QCONV tm
 end;

val _ = Parse.temp_set_grammars ambient_grammars;

end
