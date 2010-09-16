(* ===================================================================== *)
(* FILE          : Conv.sml                                              *)
(* DESCRIPTION   : Many conversions. A conversion is an ML function of   *)
(*                 type :term -> thm. The theorem is an equality whose   *)
(*                 lhs is the argument term. Translated from hol88.      *)
(*                                                                       *)
(* AUTHORS       : (c) Many people at Cambridge:                         *)
(*                        Larry Paulson                                  *)
(*                        Mike Gordon                                    *)
(*                        Richard Boulton and                            *)
(*                        Tom Melham, University of Cambridge plus       *)
(*                     Paul Loewenstein, for hol88                       *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* Many micro-optimizations added, February 24, 1992, KLS                *)
(* ===================================================================== *)

structure Conv :> Conv =
struct

open HolKernel Parse boolTheory Drule boolSyntax Rsyntax Abbrev

exception UNCHANGED

fun QCONV c tm = c tm handle UNCHANGED => REFL tm

val ERR = mk_HOL_ERR "Conv";


(* ---------------------------------------------------------------------*)
(* Conversion for rewrite rules of the form |- !x1 ... xn. t == u       *)
(* Matches x1 ... xn :   t'  ---->  |- t' == u'                         *)
(* Matches all types in conclusion except those mentioned in hypotheses.*)
(*                                                                      *)
(* Rewritten such that the lhs of |- t' = u' is syntactically equal to  *)
(* the input term, not just alpha-equivalent.            [TFM 90.07.11] *)
(*                                                                      *)
(* OLD CODE:                                                            *)
(*                                                                      *)
(*   let REWRITE_CONV =                                                 *)
(*       set_fail_prefix `REWRITE_CONV`                                 *)
(*         (PART_MATCH (fst o dest_eq));;                               *)
(* ---------------------------------------------------------------------*)

fun REWR_CONV0 (part_matcher,fn_name) th =
  let val instth = part_matcher lhs th handle e
           => raise (wrap_exn "Conv"
                 (fn_name^": bad theorem argument: "
                  ^term_to_string (concl th)) e)
  in fn tm =>
    let val eqn = instth tm
        val l   = lhs(concl eqn)
    in if l = tm then eqn else TRANS (ALPHA tm l) eqn
    end
    handle HOL_ERR _ => raise ERR fn_name "lhs of thm doesn't match term"
  end;

val REWR_CONV    = REWR_CONV0 (PART_MATCH,    "REWR_CONV")
val HO_REWR_CONV = REWR_CONV0 (HO_PART_MATCH, "HO_REWR_CONV");


(* ---------------------------------------------------------------------*)
(* RAND_CONV conv "t1 t2" applies conv to t2                            *)
(*                                                                      *)
(* Added TFM 88.03.31                                                   *)
(* Revised TFM 91.03.08                                                 *)
(* Revised RJB 91.04.17                                                 *)
(* Revised Michael Norrish 2000.03.27                                   *)
(*    now passes on information about nested failure                    *)
(* ---------------------------------------------------------------------*)

fun RAND_CONV conv tm = let
  val {Rator,Rand} =
    dest_comb tm handle (HOL_ERR _) => raise ERR "RAND_CONV" "not a comb"
  val newrand = conv Rand
    handle HOL_ERR {origin_function, message, origin_structure} =>
      if Lib.mem origin_function  ["RAND_CONV", "RATOR_CONV", "ABS_CONV"]
         andalso origin_structure = "Conv"
      then
        raise ERR "RAND_CONV" message
      else
        raise ERR "RAND_CONV" (origin_function ^ ": " ^ message)
in
  AP_TERM Rator newrand handle (HOL_ERR {message,...}) =>
    raise ERR "RAND_CONV" ("Application of AP_TERM failed: "^message)
end


(* ---------------------------------------------------------------------*)
(* RATOR_CONV conv "t1 t2" applies conv to t1                           *)
(*                                                                      *)
(* Added TFM 88.03.31                                                   *)
(* Revised TFM 91.03.08                                                 *)
(* Revised RJB 91.04.17                                                 *)
(* Revised Michael Norrish 2000.03.27                                   *)
(*    now passes on information about nested failure                    *)
(* ---------------------------------------------------------------------*)

fun RATOR_CONV conv tm = let
  val {Rator,Rand} =
    dest_comb tm handle (HOL_ERR _) => raise ERR "RATOR_CONV" "not a comb"
  val newrator = conv Rator
    handle HOL_ERR {origin_function, origin_structure, message} =>
      if Lib.mem origin_function  ["RAND_CONV", "RATOR_CONV", "ABS_CONV"]
         andalso origin_structure = "Conv"
      then
        raise ERR "RATOR_CONV" message
      else
        raise ERR "RATOR_CONV" (origin_function ^ ": " ^ message)
in
  AP_THM newrator Rand handle  (HOL_ERR {message,...}) =>
    raise ERR "RATOR_CONV" ("Application of AP_THM failed: "^message)
end

(* remember this as "left-hand conv", where RAND_CONV is "right-hand conv". *)
fun LAND_CONV c = RATOR_CONV (RAND_CONV c)

(* ----------------------------------------------------------------------
    ABS_CONV conv "\x. t[x]" applies conv to t[x]

    Added TFM 88.03.31
    Revised RJB 91.04.17
    Revised Michael Norrish 2000.03.27
       now passes on information about nested failure
    Revised Michael Norrish 2003.03.20
       now does SUB_CONV-like tricks to handle ABS failing
   ---------------------------------------------------------------------- *)

fun ABS_CONV conv tm =
    case dest_term tm of
      LAMB{Bvar,Body} => let
        val newbody = conv Body
      in
        ABS Bvar newbody
        handle HOL_ERR _ =>
               let
                 val v = genvar (type_of Bvar)
                 val th1 = ALPHA_CONV v tm
                 val r = rhs (concl th1)
                 val {Body = Body',...} = dest_abs r
                 val eq_thm' = ABS v (conv Body')
                 val at = rhs (concl eq_thm')
                 val v' = variant (free_vars at) Bvar
                 val th2 = ALPHA_CONV v' at
               in
                 TRANS (TRANS th1 eq_thm') th2
               end
                 handle HOL_ERR {origin_function, origin_structure, message} =>
                        if Lib.mem origin_function  ["RAND_CONV", "RATOR_CONV",
                                                     "ABS_CONV"]
                           andalso origin_structure = "Conv"
                        then
                          raise ERR "ABS_CONV" message
                        else
                          raise ERR "ABS_CONV"
                                    (origin_function ^ ": " ^ message)
      end
    | _ => raise ERR "ABS_CONV" "Term not an abstraction"

(* -------------------------------------------------------------------- *)
(* LHS_CONV conv "t1 = t2" applies conv to t1                           *)
(*                                                                      *)
(* Added MN 99.06.14                                                    *)
(* -------------------------------------------------------------------- *)

fun LHS_CONV conv tm =
  if not (is_eq tm) then
    raise ERR "LHS_CONV" "not an equality"
  else
    RATOR_CONV (RAND_CONV conv) tm

(* -------------------------------------------------------------------- *)
(* RHS_CONV conv "t1 = t2" applies conv to t2                           *)
(*                                                                      *)
(* Added MN 99.06.14                                                    *)
(* -------------------------------------------------------------------- *)

fun RHS_CONV conv tm =
  if not (is_eq tm) then
    raise ERR "RHS_CONV" "not an equality"
  else
    RAND_CONV conv tm



(*---------------------------------------------------------------------------
 * Conversion that always fails;  identity element for ORELSEC.
 *---------------------------------------------------------------------------*)

fun NO_CONV _ = raise ERR "NO_CONV" "";

(* ----------------------------------------------------------------------
    Conversion that always succeeds, but does nothing.
    Indicates this by raising the UNCHANGED exception.
   ---------------------------------------------------------------------- *)

fun ALL_CONV t = raise UNCHANGED

(* ----------------------------------------------------------------------
    Apply two conversions in succession;  fail if either does.  Handle
    UNCHANGED appropriately.
   ---------------------------------------------------------------------- *)

fun (conv1 THENC conv2) t = let
  val th1 = conv1 t
in
  TRANS th1 (conv2 (rhs (concl th1))) handle UNCHANGED => th1
end handle UNCHANGED => conv2 t

(* ----------------------------------------------------------------------
    Apply conv1;  if it raises a HOL_ERR then apply conv2. Note that
    interrupts and other exceptions (including UNCHANGED) will sail on
    through.
   ---------------------------------------------------------------------- *)

fun (conv1 ORELSEC conv2) t = conv1 t handle HOL_ERR _ => conv2 t;


(*---------------------------------------------------------------------------*
 * Perform the first successful conversion of those in the list.             *
 *---------------------------------------------------------------------------*)

fun FIRST_CONV [] tm = NO_CONV tm
  | FIRST_CONV (c::rst) tm = c tm handle (HOL_ERR _) => FIRST_CONV rst tm;

(*---------------------------------------------------------------------------
 * Perform every conversion in the list.
 *---------------------------------------------------------------------------*)

fun EVERY_CONV convl tm =
   itlist (curry (op THENC)) convl ALL_CONV tm
   handle HOL_ERR _ => raise ERR "EVERY_CONV" "";


(*---------------------------------------------------------------------------
 * Cause the conversion to fail if it does not change its input.
 *---------------------------------------------------------------------------*)

fun CHANGED_CONV conv tm =
   let val th = conv tm
           handle UNCHANGED => raise ERR "CHANGED_CONV" "Input term unchanged"
       val {lhs,rhs} = dest_eq (concl th)
   in if aconv lhs rhs then raise ERR"CHANGED_CONV" "Input term unchanged"
      else th
   end;

(* ----------------------------------------------------------------------
    Cause a failure if the conversion causes the UNCHANGED exception to
    be raised.  Doesn't "waste time" doing an equality check.  Mnemonic:
    "quick changed_conv".
   ---------------------------------------------------------------------- *)

fun QCHANGED_CONV conv tm =
    conv tm
    handle UNCHANGED => raise ERR "QCHANGED_CONV" "Input term unchanged"

(*---------------------------------------------------------------------------
 * Apply a conversion zero or more times.
 *---------------------------------------------------------------------------*)

fun REPEATC conv t =
    ((QCHANGED_CONV conv THENC (REPEATC conv)) ORELSEC ALL_CONV) t;

fun TRY_CONV conv = conv ORELSEC ALL_CONV;

fun COMB_CONV conv tm = let
  val {Rator, Rand} = dest_comb tm
in
  let
    val th = conv Rator
  in
    MK_COMB (th, conv Rand) handle UNCHANGED => AP_THM th Rand
  end handle UNCHANGED => AP_TERM Rator (conv Rand)
end

fun SUB_CONV conv =
    TRY_CONV (COMB_CONV conv ORELSEC ABS_CONV conv)

fun FORK_CONV (conv1,conv2) tm = let
  open Term (* get rid of overlying Rsyntax *)
  val (fx,y) = with_exn dest_comb tm (ERR "FORK_CONV" "term not a comb")
  val (f,x)  = with_exn dest_comb fx (ERR "FORK_CONV" "term not f x y")
in
  let val th = AP_TERM f (conv1 x)
  in MK_COMB (th,conv2 y) handle UNCHANGED => AP_THM th y
  end handle UNCHANGED => AP_TERM fx (conv2 y)
 end;

fun BINOP_CONV conv tm = FORK_CONV (conv,conv) tm;

val OR_CLAUSES' =
    map GEN_ALL (CONJUNCTS (SPEC_ALL boolTheory.OR_CLAUSES))
val T_or = List.nth(OR_CLAUSES', 0);
val or_T = List.nth(OR_CLAUSES', 1);
val F_or = List.nth(OR_CLAUSES', 2);
val or_F = List.nth(OR_CLAUSES', 3);


fun EVERY_DISJ_CONV c tm = let
in
  if is_disj tm then
    LAND_CONV (EVERY_DISJ_CONV c) THENC
    (REWR_CONV T_or ORELSEC
     (REWR_CONV F_or THENC EVERY_DISJ_CONV c) ORELSEC
     (RAND_CONV (EVERY_DISJ_CONV c) THENC
      TRY_CONV (REWR_CONV or_T ORELSEC REWR_CONV or_F)))
  else c
end tm

val AND_CLAUSES' = map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES))
val T_and = List.nth(AND_CLAUSES', 0)
val and_T = List.nth(AND_CLAUSES', 1)
val F_and = List.nth(AND_CLAUSES', 2)
val and_F = List.nth(AND_CLAUSES', 3)

fun EVERY_CONJ_CONV c tm = let
in
  if is_conj tm then
    LAND_CONV (EVERY_CONJ_CONV c) THENC
    (REWR_CONV F_and ORELSEC
     (REWR_CONV T_and THENC EVERY_DISJ_CONV c) ORELSEC
     (RAND_CONV (EVERY_CONJ_CONV c) THENC
      TRY_CONV (REWR_CONV and_F ORELSEC REWR_CONV or_T)))
  else c
end tm

fun QUANT_CONV conv  = RAND_CONV(ABS_CONV conv);
fun BINDER_CONV conv = ABS_CONV conv ORELSEC QUANT_CONV conv;

fun STRIP_BINDER_CONV opt conv tm = let
  val (vlist,M) = strip_binder opt tm
in
  GEN_ABS opt vlist (conv M)
  handle HOL_ERR _ => let
           val gvs = map (genvar o type_of) vlist
           fun rename vs t =
               case vs of
                 [] => ALL_CONV t
               | (v::vs) =>
                 (GEN_ALPHA_CONV v THENC BINDER_CONV (rename vs)) t
           fun variant_list acc avds [] = List.rev acc
             | variant_list acc avds (v::vs) = let
                 val v' = variant avds v
               in
                 variant_list (v'::acc) (v'::avds) vs
               end
           val th1 = rename gvs tm
           val {rhs,...} = Rsyntax.dest_eq(Thm.concl th1)
           val (_, M') = strip_binder opt rhs (* v = Bvar *)
           val eq_thm' = GEN_ABS opt gvs (conv M')
           val at  = #rhs(Rsyntax.dest_eq(concl eq_thm'))
           val vs'  = variant_list [] (free_vars at) vlist
           val th2 = rename vs' at
         in
           TRANS (TRANS th1 eq_thm') th2
         end
end


fun STRIP_QUANT_CONV conv tm =
 (if is_forall tm then STRIP_BINDER_CONV (SOME boolSyntax.universal) else
  if is_exists tm then STRIP_BINDER_CONV (SOME boolSyntax.existential) else
  if is_select tm then STRIP_BINDER_CONV (SOME boolSyntax.select) else
  if is_exists1 tm then STRIP_BINDER_CONV (SOME boolSyntax.exists1)
  else K conv) conv tm;

fun LAST_EXISTS_CONV c tm = let
  val (bv, body) = Psyntax.dest_exists tm
in
  if is_exists body then BINDER_CONV (LAST_EXISTS_CONV c) tm
  else c tm
end

fun LAST_FORALL_CONV c tm =
  if is_forall (#2 (Psyntax.dest_forall tm)) then
    BINDER_CONV (LAST_FORALL_CONV c) tm
  else c tm

(* ----------------------------------------------------------------------
    traversal conversionals.

    DEPTH_CONV c
      bottom-up, recurse over sub-terms, and then repeatedly apply c at
      top-level.

    REDEPTH_CONV c
      bottom-up. recurse over sub-terms, apply c at top, and if this
      succeeds, repeat from start.

    TOP_DEPTH_CONV c
      top-down. Repeatedly apply c at top-level, then descend.  If descending
      doesn't change anything then stop.  If there was a change then
      come back to top and try c once more at top-level.  If this succeeds
      repeat.

    TOP_SWEEP_CONV c
      top-down.  Like TOP_DEPTH_CONV but only makes one pass over the term,
      never coming back to the top level once descent starts.

    ONCE_DEPTH_CONV c
      top-down (confusingly).  Descends term looking for position at
      which c works.  Does this "in parallel", so c may be applied multiple
      times at highest possible positions in distinct sub-terms.

   ---------------------------------------------------------------------- *)


fun DEPTH_CONV conv tm =
    (SUB_CONV (DEPTH_CONV conv) THENC REPEATC conv) tm

fun REDEPTH_CONV conv tm =
    (SUB_CONV (REDEPTH_CONV conv) THENC
     TRY_CONV (conv THENC REDEPTH_CONV conv)) tm

fun TOP_DEPTH_CONV conv tm =
    (REPEATC conv THENC
     TRY_CONV (CHANGED_CONV (SUB_CONV (TOP_DEPTH_CONV conv)) THENC
               TRY_CONV (conv THENC TOP_DEPTH_CONV conv))) tm

fun ONCE_DEPTH_CONV conv tm =
    TRY_CONV (conv ORELSEC SUB_CONV (ONCE_DEPTH_CONV conv)) tm

fun TOP_SWEEP_CONV conv tm =
    (REPEATC conv THENC SUB_CONV (TOP_SWEEP_CONV conv)) tm

(*---------------------------------------------------------------------------*
 * Convert a conversion to a rule                                            *
 *---------------------------------------------------------------------------*)

fun CONV_RULE conv th = EQ_MP (conv(concl th)) th handle UNCHANGED => th

(*---------------------------------------------------------------------------*
 * Rule for beta-reducing on all beta-redexes                                *
 *---------------------------------------------------------------------------*)

val BETA_RULE = CONV_RULE(DEPTH_CONV BETA_CONV)

fun UNBETA_CONV arg_t t = let
  open Term (* counteract prevailing Rsyntax *)
in
  if is_var arg_t then
    SYM (BETA_CONV (mk_comb(mk_abs(arg_t,t), arg_t)))
  else let
      (* find all instances of arg_t in t, and convert t
         to (\v. t[v/arg_t]) arg_t
         v can be a genvar because we expect to get rid of it later. *)
      val gv = genvar (type_of arg_t)
      val newbody = Term.subst [arg_t |-> gv] t
    in
      SYM (BETA_CONV (Term.mk_comb(mk_abs(gv,newbody), arg_t)))
    end
end

(* =====================================================================*)
(* What follows is a complete set of conversions for moving ! and ? into*)
(* and out of the basic logical connectives ~, /\, \/, ==>, and =.      *)
(*                                                                      *)
(* Naming scheme:                                                       *)
(*                                                                      *)
(*   1: for moving quantifiers inwards:  <quant>_<conn>_CONV            *)
(*                                                                      *)
(*   2: for moving quantifiers outwards: [dir]_<conn>_<quant>_CONV      *)
(*                                                                      *)
(* where                                                                *)
(*                                                                      *)
(*   <quant> := FORALL | EXISTS                                         *)
(*   <conn>  := NOT | AND | OR | IMP | EQ                               *)
(*   [dir]   := LEFT | RIGHT                    (optional)              *)
(*                                                                      *)
(*                                                                      *)
(* [TFM 90.11.09]                                                       *)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* NOT_FORALL_CONV, implements the following axiom scheme:              *)
(*                                                                      *)
(*      |- (~!x.tm) = (?x.~tm)                                          *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)
fun NOT_FORALL_CONV tm =
   let val all = dest_neg tm
       val {Bvar,Body} = dest_forall all
       val exists = mk_exists{Bvar = Bvar, Body = mk_neg Body}
       val nott = ASSUME (mk_neg Body)
       val not_all = mk_neg all
       val th1 = DISCH all (MP nott (SPEC Bvar (ASSUME all)))
       val imp1 = DISCH exists (CHOOSE (Bvar, ASSUME exists) (NOT_INTRO th1))
       val th2 = CCONTR Body (MP (ASSUME(mk_neg exists))
                              (EXISTS(exists,Bvar) nott))
       val th3 = CCONTR exists (MP (ASSUME not_all) (GEN Bvar th2))
   in
     IMP_ANTISYM_RULE (DISCH not_all th3) imp1
   end
   handle HOL_ERR _ => raise ERR "NOT_FORALL_CONV" "";

(* ---------------------------------------------------------------------*)
(* NOT_EXISTS_CONV, implements the following axiom scheme.              *)
(*                                                                      *)
(*      |- (~?x.tm) = (!x.~tm)                                          *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)
fun NOT_EXISTS_CONV tm =
   let val {Bvar,Body} = dest_exists (dest_neg tm)
       val all = mk_forall{Bvar=Bvar, Body=mk_neg Body}
       val rand_tm = rand tm
       val asm1 = ASSUME Body
       val thm1 = MP (ASSUME tm) (EXISTS (rand_tm, Bvar) asm1)
       val imp1 = DISCH tm (GEN Bvar (NOT_INTRO (DISCH Body thm1)))
       val asm2 = ASSUME  all
       and asm3 = ASSUME rand_tm
       val thm2 = DISCH rand_tm (CHOOSE (Bvar,asm3) (MP (SPEC Bvar asm2) asm1))
       val imp2 = DISCH all (NOT_INTRO thm2)
   in
     IMP_ANTISYM_RULE imp1 imp2
   end
   handle HOL_ERR _ => raise ERR "NOT_EXISTS_CONV" "";

(* ---------------------------------------------------------------------*)
(* EXISTS_NOT_CONV, implements the following axiom scheme.              *)
(*                                                                      *)
(*      |- (?x.~tm) = (~!x.tm)                                          *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)
fun EXISTS_NOT_CONV tm =
   let val {Bvar,Body} = dest_exists tm
   in
     SYM(NOT_FORALL_CONV (mk_neg (mk_forall{Bvar=Bvar, Body=dest_neg Body})))
   end
   handle HOL_ERR _ => raise ERR "EXISTS_NOT_CONV" "";

(* ---------------------------------------------------------------------*)
(* FORALL_NOT_CONV, implements the following axiom scheme.              *)
(*                                                                      *)
(*      |- (!x.~tm) = (~?x.tm)                                          *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)
fun FORALL_NOT_CONV tm =
   let val {Bvar,Body} = dest_forall tm
   in
     SYM (NOT_EXISTS_CONV (mk_neg (mk_exists{Bvar=Bvar,Body=dest_neg Body})))
   end
   handle HOL_ERR _ => raise ERR "FORALL_NOT_CONV" "";

(* ---------------------------------------------------------------------*)
(* FORALL_AND_CONV : move universal quantifiers into conjunction.       *)
(*                                                                      *)
(* A call to FORALL_AND_CONV "!x. P /\ Q"  returns:                     *)
(*                                                                      *)
(*   |- (!x. P /\ Q) = (!x.P) /\ (!x.Q)                                 *)
(* ---------------------------------------------------------------------*)
fun FORALL_AND_CONV tm =
    let val {Bvar,Body} = dest_forall tm
        val {...} = dest_conj Body
        val (Pth,Qth) = CONJ_PAIR (SPEC Bvar (ASSUME tm))
        val imp1 = DISCH tm (CONJ (GEN Bvar Pth) (GEN Bvar Qth))
        val xtm = rand(concl imp1)
        val spec_bv = SPEC Bvar
        val (t1,t2) = (spec_bv##spec_bv) (CONJ_PAIR (ASSUME xtm))
    in
      IMP_ANTISYM_RULE imp1 (DISCH xtm (GEN Bvar (CONJ t1 t2)))
    end
    handle HOL_ERR _ => raise ERR "FORALL_AND_CONV" "";

(* ---------------------------------------------------------------------*)
(* EXISTS_OR_CONV : move existential quantifiers into disjunction.      *)
(*                                                                      *)
(* A call to EXISTS_OR_CONV "?x. P \/ Q"  returns:                      *)
(*                                                                      *)
(*   |- (?x. P \/ Q) = (?x.P) \/ (?x.Q)                                 *)
(* ---------------------------------------------------------------------*)
(*
fun EXISTS_OR_CONV tm =
   let val {Bvar,Body} = dest_exists tm
       val {disj1,disj2} = dest_disj Body
       val ep = mk_exists{Bvar=Bvar, Body=disj1}
       and eq = mk_exists{Bvar=Bvar, Body=disj2}
       val ep_or_eq = mk_disj{disj1=ep, disj2=eq}
       val aP = ASSUME disj1
       val aQ = ASSUME disj2
       val Pth = EXISTS(ep,Bvar) aP
       and Qth = EXISTS(eq,Bvar) aQ
       val thm1 = DISJ_CASES_UNION (ASSUME Body) Pth Qth
       val imp1 = DISCH tm (CHOOSE (Bvar,ASSUME tm) thm1)
       val t1 = DISJ1 aP disj2
       and t2 = DISJ2 disj1 aQ
       val th1 = EXISTS(tm,Bvar) t1
       and th2 = EXISTS(tm,Bvar) t2
       val e1 = CHOOSE (Bvar,ASSUME ep) th1
       and e2 = CHOOSE (Bvar,ASSUME eq) th2
   in
    IMP_ANTISYM_RULE imp1 (DISCH ep_or_eq (DISJ_CASES (ASSUME ep_or_eq) e1 e2))
   end
   handle HOL_ERR _ => raise ERR "EXISTS_OR_CONV" "";
*)

local val alpha = Type.alpha
      val spotBeta = FORK_CONV (QUANT_CONV (BINOP_CONV BETA_CONV),
                                BINOP_CONV (QUANT_CONV BETA_CONV))
      open boolTheory
      val [P0,Q0] = fst(strip_forall(concl EXISTS_OR_THM))
      val thm0 = SPEC Q0 (SPEC P0 EXISTS_OR_THM)
      val Pname = #Name(dest_var P0)
      val Qname = #Name(dest_var Q0)
in
fun EXISTS_OR_CONV tm =
  let val {Bvar,Body} = dest_exists tm
      val thm = CONV_RULE (RAND_CONV (BINOP_CONV (GEN_ALPHA_CONV Bvar)))
                          (INST_TYPE [alpha |-> type_of Bvar] thm0)
      val ty = type_of Bvar --> Type.bool
      val P = mk_var{Name=Pname, Ty=ty}
      val Q = mk_var{Name=Qname, Ty=ty}
      val {disj1,disj2} = dest_disj Body
      val lamP = mk_abs{Bvar=Bvar, Body=disj1}
      val lamQ = mk_abs{Bvar=Bvar, Body=disj2}
  in
    CONV_RULE spotBeta (INST [P |-> lamP, Q |-> lamQ] thm)
  end
  handle HOL_ERR _ => raise ERR "EXISTS_OR_CONV" "";
end;

(* ---------------------------------------------------------------------*)
(* AND_FORALL_CONV : move universal quantifiers out of conjunction.     *)
(*                                                                      *)
(* A call to AND_FORALL_CONV "(!x. P) /\ (!x. Q)"  returns:             *)
(*                                                                      *)
(*   |- (!x.P) /\ (!x.Q) = (!x. P /\ Q)                                 *)
(* ---------------------------------------------------------------------*)

fun AND_FORALL_CONV tm =
   let val {conj1,conj2} = dest_conj tm
       val {Bvar=x, Body=P} = dest_forall conj1
       val {Bvar=y, Body=Q} = dest_forall conj2
   in
   if (not (x=y))
   then raise ERR "AND_FORALL_CONV" "forall'ed variables not the same"
   else let val specx = SPEC x
            val (t1,t2) = (specx##specx) (CONJ_PAIR (ASSUME tm))
            val imp1 = DISCH tm (GEN x (CONJ t1 t2))
            val rtm = rand(concl imp1)
            val (Pth,Qth) = CONJ_PAIR (SPEC x (ASSUME rtm))
        in
        IMP_ANTISYM_RULE imp1 (DISCH rtm (CONJ (GEN x Pth) (GEN x Qth)))
        end
   end
   handle HOL_ERR _ => raise ERR "AND_FORALL_CONV" "";


(* ---------------------------------------------------------------------*)
(* LEFT_AND_FORALL_CONV : move universal quantifier out of conjunction. *)
(*                                                                      *)
(* A call to LEFT_AND_FORALL_CONV "(!x.P) /\  Q"  returns:              *)
(*                                                                      *)
(*   |- (!x.P) /\ Q = (!x'. P[x'/x] /\ Q)                               *)
(*                                                                      *)
(* Where x' is a primed variant of x not free in the input term         *)
(* ---------------------------------------------------------------------*)
fun LEFT_AND_FORALL_CONV tm =
   let val {conj1,...} = dest_conj tm
       val {Bvar,...} = dest_forall conj1
       val x' = variant (free_vars tm) Bvar
       val specx' = SPEC x'
       and genx' = GEN x'
       val (t1,t2) = (specx' ## I) (CONJ_PAIR (ASSUME tm))
       val imp1 = DISCH tm (genx' (CONJ t1 t2))
       val rtm = rand(concl imp1)
       val (Pth,Qth) = CONJ_PAIR (specx' (ASSUME rtm))
   in
     IMP_ANTISYM_RULE imp1 (DISCH rtm (CONJ (genx' Pth)  Qth))
   end
   handle HOL_ERR _ => raise ERR "LEFT_AND_FORALL_CONV" "";

(* ---------------------------------------------------------------------*)
(* RIGHT_AND_FORALL_CONV : move universal quantifier out of conjunction.*)
(*                                                                      *)
(* A call to RIGHT_AND_FORALL_CONV "P /\ (!x.Q)"  returns:              *)
(*                                                                      *)
(*   |-  P /\ (!x.Q) = (!x'. P /\ Q[x'/x])                              *)
(*                                                                      *)
(* where x' is a primed variant of x not free in the input term         *)
(* ---------------------------------------------------------------------*)
fun RIGHT_AND_FORALL_CONV tm =
   let val {conj2, ...} = dest_conj tm
       val {Bvar,...} = dest_forall conj2
       val x' = variant (free_vars tm) Bvar
       val specx' = SPEC x'
       val genx' = GEN x'
       val (t1,t2) = (I ## specx') (CONJ_PAIR (ASSUME tm))
       val imp1 = DISCH tm (genx' (CONJ t1 t2))
       val rtm = rand(concl imp1)
       val (Pth,Qth) = CONJ_PAIR (specx' (ASSUME rtm))
   in
     IMP_ANTISYM_RULE imp1 (DISCH rtm (CONJ Pth (genx' Qth)))
   end
   handle HOL_ERR _ => raise ERR "RIGHT_AND_FORALL_CONV" "";

(* ---------------------------------------------------------------------*)
(* OR_EXISTS_CONV : move existential quantifiers out of disjunction.    *)
(*                                                                      *)
(* A call to OR_EXISTS_CONV "(?x. P) \/ (?x. Q)"  returns:              *)
(*                                                                      *)
(*   |- (?x.P) \/ (?x.Q) = (?x. P \/ Q)                                 *)
(* ---------------------------------------------------------------------*)
fun OR_EXISTS_CONV tm =
   let val {disj1,disj2} = dest_disj tm
       val {Bvar=x, Body=P} = dest_exists disj1
       val {Bvar=y, Body=Q} = dest_exists disj2
   in
   if (not (x=y)) then raise ERR "OR_EXISTS_CONV" ""
   else let val aP = ASSUME P
            and aQ = ASSUME Q
            and P_or_Q = mk_disj{disj1 = P, disj2 = Q}
            val otm = mk_exists {Bvar = x, Body = P_or_Q}
            val t1 = DISJ1 aP Q
            and t2 = DISJ2 P aQ
            val eotm = EXISTS(otm,x)
            val e1 = CHOOSE (x,ASSUME disj1) (eotm t1)
            and e2 = CHOOSE (x,ASSUME disj2) (eotm t2)
            val thm1 = DISJ_CASES (ASSUME tm) e1 e2
            val imp1 = DISCH tm thm1
            val Pth = EXISTS(disj1,x) aP
            and Qth = EXISTS(disj2,x) aQ
            val thm2 = DISJ_CASES_UNION (ASSUME P_or_Q) Pth Qth
        in
          IMP_ANTISYM_RULE imp1 (DISCH otm (CHOOSE (x,ASSUME otm) thm2))
        end
   end
   handle HOL_ERR _ => raise ERR "OR_EXISTS_CONV" "";

(* ---------------------------------------------------------------------*)
(* LEFT_OR_EXISTS_CONV : move existential quantifier out of disjunction.*)
(*                                                                      *)
(* A call to LEFT_OR_EXISTS_CONV "(?x.P) \/  Q"  returns:               *)
(*                                                                      *)
(*   |- (?x.P) \/ Q = (?x'. P[x'/x] \/ Q)                               *)
(*                                                                      *)
(* Where x' is a primed variant of x not free in the input term         *)
(* ---------------------------------------------------------------------*)

fun LEFT_OR_EXISTS_CONV tm =
   let val {disj1,disj2} = dest_disj tm
       val {Bvar,Body} = dest_exists disj1
       val x' = variant (free_vars tm) Bvar
       val newp = subst[Bvar |-> x'] Body
       val newp_thm = ASSUME newp
       val new_disj = mk_disj {disj1=newp, disj2=disj2}
       val otm = mk_exists {Bvar=x', Body=new_disj}
       and Qth = ASSUME disj2
       val t1 = DISJ1 newp_thm disj2
       and t2 = DISJ2 newp (ASSUME disj2)
       val th1 = EXISTS(otm,x') t1
       and th2 = EXISTS(otm,x') t2
       val thm1 = DISJ_CASES (ASSUME tm) (CHOOSE(x',ASSUME disj1)th1) th2
       val imp1 = DISCH tm thm1
       val Pth = EXISTS(disj1,x') newp_thm
       val thm2 = DISJ_CASES_UNION (ASSUME new_disj) Pth Qth
   in
     IMP_ANTISYM_RULE imp1 (DISCH otm (CHOOSE (x',ASSUME otm) thm2))
   end
   handle HOL_ERR _  => raise ERR "LEFT_OR_EXISTS_CONV" "";

(* ---------------------------------------------------------------------*)
(* RIGHT_OR_EXISTS_CONV: move existential quantifier out of disjunction.*)
(*                                                                      *)
(* A call to RIGHT_OR_EXISTS_CONV "P \/ (?x.Q)"  returns:               *)
(*                                                                      *)
(*   |-  P \/ (?x.Q) = (?x'. P \/ Q[x'/x])                              *)
(*                                                                      *)
(* where x' is a primed variant of x not free in the input term         *)
(* ---------------------------------------------------------------------*)
fun RIGHT_OR_EXISTS_CONV tm =
   let val {disj1,disj2} = dest_disj tm
       val {Bvar,Body} = dest_exists disj2
       val x' = variant (free_vars tm) Bvar
       val newq = subst[Bvar |-> x'] Body
       val newq_thm = ASSUME newq
       and Pth = ASSUME disj1
       val P_or_newq = mk_disj{disj1 = disj1, disj2 = newq}
       val otm = mk_exists{Bvar = x',Body = P_or_newq}
       val eotm' = EXISTS(otm,x')
       val th1 = eotm' (DISJ2 disj1 newq_thm)
       and th2 = eotm' (DISJ1 Pth newq)
       val thm1 = DISJ_CASES (ASSUME tm) th2 (CHOOSE(x',ASSUME disj2) th1)
       val imp1 = DISCH tm thm1
       val Qth = EXISTS(disj2,x') newq_thm
       val thm2 = DISJ_CASES_UNION (ASSUME P_or_newq) Pth Qth
   in
     IMP_ANTISYM_RULE imp1 (DISCH otm (CHOOSE (x',ASSUME otm) thm2))
   end
   handle HOL_ERR _ => raise ERR "RIGHT_OR_EXISTS_CONV" "";

(* ---------------------------------------------------------------------*)
(* EXISTS_AND_CONV : move existential quantifier into conjunction.      *)
(*                                                                      *)
(* A call to EXISTS_AND_CONV "?x. P /\ Q"  returns:                     *)
(*                                                                      *)
(*    |- (?x. P /\ Q) = (?x.P) /\ Q        [x not free in Q]            *)
(*    |- (?x. P /\ Q) = P /\ (?x.Q)        [x not free in P]            *)
(*    |- (?x. P /\ Q) = (?x.P) /\ (?x.Q)   [x not free in P /\ Q]       *)
(* ---------------------------------------------------------------------*)
fun EXISTS_AND_CONV tm =
   let val {Bvar, Body} = dest_exists tm handle HOL_ERR _
           => raise ERR"EXISTS_AND_CONV" "expecting `?x. P /\\ Q`"
       val {conj1,conj2} = dest_conj Body handle HOL_ERR _
           => raise ERR "EXISTS_AND_CONV" "expecting `?x. P /\\ Q`"
       val fP = free_in Bvar conj1
       and fQ = free_in Bvar conj2
   in
   if (fP andalso fQ)
   then raise ERR"EXISTS_AND_CONV"
                      ("`"^(#Name(dest_var Bvar))^ "` free in both conjuncts")
   else let val (t1,t2) = CONJ_PAIR(ASSUME Body)
            val econj1 = mk_exists{Bvar = Bvar, Body = conj1}
            val econj2 = mk_exists{Bvar = Bvar, Body = conj2}
            val eP = if fQ then t1 else EXISTS (econj1,Bvar) t1
            and eQ = if fP then t2 else EXISTS (econj2,Bvar) t2
            val imp1 = DISCH tm (CHOOSE(Bvar,ASSUME tm) (CONJ eP eQ))
            val th = EXISTS (tm,Bvar) (CONJ(ASSUME conj1) (ASSUME conj2))
            val th1 = if (fP orelse (not fQ))
                      then CHOOSE(Bvar,ASSUME econj1)th
                      else th
            val thm1 = if (fQ orelse (not fP))
                       then CHOOSE(Bvar,ASSUME econj2)th1
                       else th1
            val otm = rand(concl imp1)
            val (t1,t2) = CONJ_PAIR(ASSUME otm)
            val thm2 = PROVE_HYP t1 (PROVE_HYP t2 thm1)
        in
          IMP_ANTISYM_RULE imp1 (DISCH otm thm2)
        end
   end
   handle (e as HOL_ERR{origin_structure = "Conv",
                        origin_function = "EXISTS_AND_CONV",...}) => raise e
        | HOL_ERR _ => raise ERR"EXISTS_AND_CONV" "";





(* ---------------------------------------------------------------------*)
(* AND_EXISTS_CONV : move existential quantifier out of conjunction.    *)
(*                                                                      *)
(*   |- (?x.P) /\ (?x.Q) = (?x. P /\ Q)                                 *)
(*                                                                      *)
(* provided x is free in neither P nor Q.                               *)
(* ---------------------------------------------------------------------*)
local val AE_ERR = ERR"AND_EXISTS_CONV" "expecting `(?x.P) /\\ (?x.Q)`"
in
fun AND_EXISTS_CONV tm =
 let val {conj1,conj2} = dest_conj tm handle HOL_ERR _ => raise AE_ERR
     val {Bvar=x, Body=P} = dest_exists conj1 handle HOL_ERR _ => raise AE_ERR
     val {Bvar=y, Body=Q} = dest_exists conj2 handle HOL_ERR_ => raise AE_ERR
 in
   if (not(x=y)) then raise AE_ERR else
   if (free_in x P orelse free_in x Q)
   then raise ERR "AND_EXISTS_CONV"
            ("`"^(#Name(dest_var x))^"` free in conjunct(s)")
   else SYM (EXISTS_AND_CONV
              (mk_exists{Bvar=x, Body=mk_conj{conj1=P, conj2=Q}}))
 end
 handle (e as HOL_ERR{origin_structure = "Conv",
                        origin_function = "AND_EXISTS_CONV",...}) => raise e
      | HOL_ERR _ => raise ERR"AND_EXISTS_CONV" ""
end;

(* ---------------------------------------------------------------------*)
(* LEFT_AND_EXISTS_CONV: move existential quantifier out of conjunction *)
(*                                                                      *)
(* A call to LEFT_AND_EXISTS_CONV "(?x.P) /\  Q"  returns:              *)
(*                                                                      *)
(*   |- (?x.P) /\ Q = (?x'. P[x'/x] /\ Q)                               *)
(*                                                                      *)
(* Where x' is a primed variant of x not free in the input term         *)
(* ---------------------------------------------------------------------*)
fun LEFT_AND_EXISTS_CONV tm =
   let val {conj1,conj2} = dest_conj tm
       val {Bvar,Body} = dest_exists conj1
       val x' = variant (free_vars tm) Bvar
       val newp = subst[Bvar |-> x'] Body
       val new_conj = mk_conj {conj1 = newp, conj2 = conj2}
       val otm = mk_exists{Bvar = x', Body = new_conj}
       val (EP,Qth) = CONJ_PAIR(ASSUME tm)
       val thm1 = EXISTS(otm,x')(CONJ(ASSUME newp)(ASSUME conj2))
       val imp1 = DISCH tm (MP (DISCH conj2 (CHOOSE(x',EP)thm1)) Qth)
       val (t1,t2) = CONJ_PAIR (ASSUME new_conj)
       val thm2 = CHOOSE (x',ASSUME otm) (CONJ (EXISTS (conj1,x') t1) t2)
   in
     IMP_ANTISYM_RULE imp1 (DISCH otm thm2)
   end
   handle HOL_ERR _ => raise ERR "LEFT_AND_EXISTS_CONV" "";

(* ---------------------------------------------------------------------*)
(* RIGHT_AND_EXISTS_CONV: move existential quantifier out of conjunction*)
(*                                                                      *)
(* A call to RIGHT_AND_EXISTS_CONV "P /\ (?x.Q)"  returns:              *)
(*                                                                      *)
(*   |- P /\ (?x.Q) = (?x'. P /\ (Q[x'/x])                              *)
(*                                                                      *)
(* where x' is a primed variant of x not free in the input term         *)
(* ---------------------------------------------------------------------*)
fun RIGHT_AND_EXISTS_CONV tm =
   let val {conj1,conj2} = dest_conj tm
       val {Bvar,Body} = dest_exists conj2
       val x' = variant (free_vars tm) Bvar
       val newq = subst[Bvar |-> x'] Body
       val new_conj = mk_conj{conj1 = conj1,conj2 = newq}
       val otm = mk_exists{Bvar = x',Body = new_conj}
       val (Pth,EQ) = CONJ_PAIR(ASSUME tm)
       val thm1 = EXISTS(otm,x')(CONJ(ASSUME conj1)(ASSUME newq))
       val imp1 = DISCH tm (MP (DISCH conj1 (CHOOSE(x',EQ)thm1)) Pth)
       val (t1,t2) = CONJ_PAIR (ASSUME new_conj)
       val thm2 = CHOOSE (x',ASSUME otm) (CONJ t1 (EXISTS (conj2,x') t2))
   in
     IMP_ANTISYM_RULE imp1 (DISCH otm thm2)
   end
   handle HOL_ERR _ => raise ERR "RIGHT_AND_EXISTS_CONV" "";


(* ---------------------------------------------------------------------*)
(* FORALL_OR_CONV : move universal quantifier into disjunction.         *)
(*                                                                      *)
(* A call to FORALL_OR_CONV "!x. P \/ Q"  returns:                      *)
(*                                                                      *)
(*   |- (!x. P \/ Q) = (!x.P) \/ Q       [if x not free in Q]           *)
(*   |- (!x. P \/ Q) = P \/ (!x.Q)       [if x not free in P]           *)
(*   |- (!x. P \/ Q) = (!x.P) \/ (!x.Q)  [if x free in neither P nor Q] *)
(* ---------------------------------------------------------------------*)
local val FO_ERR = ERR"FORALL_OR_CONV" "expecting `!x. P \\/ Q`"
in
fun FORALL_OR_CONV tm =
 let val {Bvar,Body} = dest_forall tm handle HOL_ERR _ => raise FO_ERR
     val {disj1,disj2} = dest_disj Body handle HOL_ERR _ => raise FO_ERR
     val fdisj1 = free_in Bvar disj1
     and fdisj2 = free_in Bvar disj2
 in
   if (fdisj1 andalso fdisj2)
   then raise ERR "FORALL_OR_CONV"
               ("`"^(#Name(dest_var Bvar))^"` free in both disjuncts")
   else
   let val disj1_thm = ASSUME disj1
     val disj2_thm = ASSUME disj2
     val thm1 = SPEC Bvar (ASSUME tm)
     val imp1 =
      if fdisj1
      then let val thm2 = CONTR disj1 (MP (ASSUME (mk_neg disj2)) disj2_thm)
               val thm3 = DISJ1(GEN Bvar(DISJ_CASES thm1 disj1_thm thm2)) disj2
               val thm4 = DISJ2(mk_forall{Bvar=Bvar, Body=disj1})(ASSUME disj2)
           in
             DISCH tm (DISJ_CASES(SPEC disj2 EXCLUDED_MIDDLE) thm4 thm3)
           end
      else
      if fdisj2
      then let val thm2 = CONTR disj2(MP (ASSUME (mk_neg disj1)) (ASSUME disj1))
               val thm3 = DISJ2 disj1 (GEN Bvar(DISJ_CASES thm1 thm2 disj2_thm))
               val thm4 = DISJ1(ASSUME disj1)(mk_forall{Bvar=Bvar, Body=disj2})
           in
             DISCH tm (DISJ_CASES (SPEC disj1 EXCLUDED_MIDDLE) thm4 thm3)
           end
      else
      let val t1 = GEN Bvar(ASSUME disj1)
          val t2 = GEN Bvar(ASSUME disj2)
      in
        DISCH tm (DISJ_CASES_UNION thm1 t1 t2)
      end
     val otm = rand(concl imp1)
     val {disj1,disj2} = dest_disj otm
     val thm5 = (if (fdisj1 orelse (not fdisj2)) then SPEC Bvar else I)
                (ASSUME disj1)
     val thm6 = (if (fdisj2 orelse (not fdisj1)) then SPEC Bvar else I)
                (ASSUME disj2)
     val imp2 = GEN Bvar (DISJ_CASES_UNION (ASSUME otm) thm5 thm6)
   in
     IMP_ANTISYM_RULE imp1 (DISCH otm imp2)
   end
 end
 handle (e as HOL_ERR{origin_structure = "Conv",
                        origin_function = "FORALL_OR_CONV",...}) => raise e
      | HOL_ERR _ => raise ERR "FORALL_OR_CONV" ""
end;

(* ---------------------------------------------------------------------*)
(* OR_FORALL_CONV : move existential quantifier out of conjunction.     *)
(*                                                                      *)
(*   |- (!x.P) \/ (!x.Q) = (!x. P \/ Q)                                 *)
(*                                                                      *)
(* provided x is free in neither P nor Q.                               *)
(* ---------------------------------------------------------------------*)
local val OF_ERR = ERR "OR_FORALL_CONV" "expecting `(!x.P) \\/ (!x.Q)`"
in
fun OR_FORALL_CONV tm =
 let val {disj1,disj2} = dest_disj tm handle HOL_ERR _ => raise OF_ERR
     val {Bvar=x, Body=P} = dest_forall disj1 handle HOL_ERR _ => raise OF_ERR
     val {Bvar=y, Body=Q} = dest_forall disj2 handle HOL_ERR _ => raise OF_ERR
 in
   if not(x=y) then raise OF_ERR else
   if (free_in x P orelse free_in x Q)
   then raise ERR"OR_FORALL_CONV"
             ("`"^(#Name(dest_var x))^ "` free in disjuncts(s)")
   else SYM(FORALL_OR_CONV(mk_forall{Bvar=x,Body=mk_disj{disj1=P,disj2=Q}}))
 end
 handle (e as HOL_ERR{origin_structure = "Conv",
                        origin_function = "OR_FORALL_CONV",...}) => raise e
      | HOL_ERR _ => raise ERR "OR_FORALL_CONV" ""
end;

(* ---------------------------------------------------------------------*)
(* LEFT_OR_FORALL_CONV : move universal quantifier out of conjunction.  *)
(*                                                                      *)
(* A call to LEFT_OR_FORALL_CONV "(!x.P) \/  Q"  returns:               *)
(*                                                                      *)
(*   |- (!x.P) \/ Q = (!x'. P[x'/x] \/ Q)                               *)
(*                                                                      *)
(* Where x' is a primed variant of x not free in the input term         *)
(* ---------------------------------------------------------------------*)
fun LEFT_OR_FORALL_CONV tm =
   let val {disj1,disj2} = dest_disj tm
       val {Bvar,Body} = dest_forall disj1
       val x' = variant (free_vars tm) Bvar
       val newp = subst[Bvar |-> x'] Body
       val aQ = ASSUME disj2
       val Pth = DISJ1 (SPEC x' (ASSUME disj1)) disj2
       val Qth = DISJ2 newp aQ
       val imp1 = DISCH tm (GEN x' (DISJ_CASES (ASSUME tm) Pth Qth))
       val otm = rand(concl imp1)
       val thm1 = SPEC x' (ASSUME otm)
       val thm2 = CONTR newp (MP(ASSUME(mk_neg disj2)) aQ)
       val thm3 = DISJ1 (GEN x' (DISJ_CASES thm1 (ASSUME newp) thm2)) disj2
       val thm4 = DISJ2 disj1 aQ
       val imp2 = DISCH otm(DISJ_CASES(SPEC disj2 EXCLUDED_MIDDLE)thm4 thm3)
   in
     IMP_ANTISYM_RULE imp1 imp2
   end
   handle HOL_ERR _ => raise ERR "LEFT_OR_FORALL_CONV" "";

(* ---------------------------------------------------------------------*)
(* RIGHT_OR_FORALL_CONV : move universal quantifier out of conjunction. *)
(*                                                                      *)
(* A call to RIGHT_OR_FORALL_CONV "P \/ (!x.Q)"  returns:               *)
(*                                                                      *)
(*   |- P \/ (!x.Q) = (!x'. P \/ (Q[x'/x])                              *)
(*                                                                      *)
(* where x' is a primed variant of x not free in the input term         *)
(* ---------------------------------------------------------------------*)
fun RIGHT_OR_FORALL_CONV tm =
   let val {disj1,disj2} = dest_disj tm
       val {Bvar,Body} = dest_forall disj2
       val x' = variant (free_vars tm) Bvar
       val newq = subst[Bvar |-> x'] Body
       val Qth = DISJ2 disj1 (SPEC x' (ASSUME disj2))
       val Pthm = ASSUME disj1
       val Pth = DISJ1 Pthm newq
       val imp1 = DISCH tm (GEN x' (DISJ_CASES (ASSUME tm) Pth Qth))
       val otm = rand(concl imp1)
       val thm1 = SPEC x' (ASSUME otm)
       val thm2 = CONTR newq (MP(ASSUME(mk_neg disj1)) Pthm)
       val thm3 = DISJ2 disj1 (GEN x' (DISJ_CASES thm1 thm2 (ASSUME newq)))
       val thm4 = DISJ1 Pthm disj2
       val imp2 = DISCH otm(DISJ_CASES(SPEC disj1 EXCLUDED_MIDDLE)thm4 thm3)
   in
     IMP_ANTISYM_RULE imp1 imp2
   end
   handle HOL_ERR _ => raise ERR "RIGHT_OR_FORALL_CONV" "";

(* ---------------------------------------------------------------------*)
(* FORALL_IMP_CONV, implements the following axiom schemes.             *)
(*                                                                      *)
(*      |- (!x. P==>Q[x]) = (P ==> (!x.Q[x]))     [x not free in P]     *)
(*                                                                      *)
(*      |- (!x. P[x]==>Q) = ((?x.P[x]) ==> Q)     [x not free in Q]     *)
(*                                                                      *)
(*      |- (!x. P==>Q) = ((?x.P) ==> (!x.Q))      [x not free in P==>Q] *)
(* ---------------------------------------------------------------------*)
local val FI_ERR = ERR "FORALL_IMP_CONV" "expecting `!x. P ==> Q`"
in
fun FORALL_IMP_CONV tm =
   let val {Bvar,Body} = dest_forall tm handle HOL_ERR _ => raise FI_ERR
       val {ant,conseq} = dest_imp Body handle HOL_ERR _ => raise FI_ERR
       val fant = free_in Bvar ant
       and fconseq =  free_in Bvar conseq
       val ant_thm = ASSUME ant
       val tm_thm = ASSUME tm
   in
     if (fant andalso fconseq)
     then raise ERR "FORALL_IMP_CONV"
             ("`"^(#Name(dest_var Bvar))^"` free on both sides of `==>`")
     else
     if fant
     then let val asm = mk_exists{Bvar = Bvar, Body = ant}
              val th1 = CHOOSE(Bvar,ASSUME asm) (UNDISCH(SPEC Bvar tm_thm))
              val imp1 = DISCH tm (DISCH asm th1)
              val cncl = rand(concl imp1)
              val th2 = MP (ASSUME cncl) (EXISTS (asm,Bvar) ant_thm)
              val imp2 = DISCH cncl (GEN Bvar (DISCH ant th2))
          in
             IMP_ANTISYM_RULE imp1 imp2
          end
     else
     if fconseq
     then let val imp1 = DISCH ant(GEN Bvar(UNDISCH(SPEC Bvar tm_thm)))
              val cncl = concl imp1
              val imp2 = GEN Bvar(DISCH ant(SPEC Bvar(UNDISCH(ASSUME cncl))))
          in
             IMP_ANTISYM_RULE (DISCH tm imp1) (DISCH cncl imp2)
          end
     else let val asm = mk_exists{Bvar = Bvar, Body = ant}
              val tmp = UNDISCH (SPEC Bvar tm_thm)
              val th1 = GEN Bvar (CHOOSE(Bvar,ASSUME asm) tmp)
              val imp1 = DISCH tm (DISCH asm th1)
              val cncl = rand(concl imp1)
              val th2 = SPEC Bvar (MP(ASSUME cncl) (EXISTS (asm,Bvar) ant_thm))
              val imp2 = DISCH cncl (GEN Bvar (DISCH ant th2))
          in
             IMP_ANTISYM_RULE imp1 imp2
          end
   end
   handle (e as HOL_ERR{origin_structure = "Conv",
                        origin_function = "FORALL_IMP_CONV",...}) => raise e
        | HOL_ERR _ => raise ERR"FORALL_IMP_CONV" ""
end;

(* ---------------------------------------------------------------------*)
(* LEFT_IMP_EXISTS_CONV, implements the following theorem-scheme:       *)
(*                                                                      *)
(*    |- (?x. t1[x]) ==> t2  =  !x'. t1[x'] ==> t2                      *)
(*                                                                      *)
(* where x' is a variant of x chosen not to be free in (?x.t1[x])==>t2  *)
(*                                                                      *)
(* Author: Tom Melham                                                   *)
(* Revised: [TFM 90.07.01]                                              *)
(*----------------------------------------------------------------------*)
fun LEFT_IMP_EXISTS_CONV tm =
   let val {ant, ...} = dest_imp tm
       val {Bvar,Body} = dest_exists ant
       val x' = variant (free_vars tm) Bvar
       val t' = subst [Bvar |-> x'] Body
       val th1 = GEN x' (DISCH t'(MP(ASSUME tm)(EXISTS(ant,x')(ASSUME t'))))
       val rtm = concl th1
       val th2 = CHOOSE (x',ASSUME ant) (UNDISCH(SPEC x'(ASSUME rtm)))
   in
     IMP_ANTISYM_RULE (DISCH tm th1) (DISCH rtm (DISCH ant th2))
   end
   handle HOL_ERR _ => raise ERR "LEFT_IMP_EXISTS_CONV" "";

(* ---------------------------------------------------------------------*)
(* RIGHT_IMP_FORALL_CONV, implements the following theorem-scheme:      *)
(*                                                                      *)
(*    |- (t1 ==> !x. t2)  =  !x'. t1 ==> t2[x'/x]                       *)
(*                                                                      *)
(* where x' is a variant of x chosen not to be free in the input term.  *)
(*----------------------------------------------------------------------*)
fun RIGHT_IMP_FORALL_CONV tm =
   let val {ant,conseq} = dest_imp tm
       val {Bvar,Body} = dest_forall conseq
       val x' = variant (free_vars tm) Bvar
       val t' = subst [Bvar |-> x'] Body
       val imp1 = DISCH tm (GEN x' (DISCH ant(SPEC x'(UNDISCH(ASSUME tm)))))
       val ctm = rand(concl imp1)
       val alph = GEN_ALPHA_CONV Bvar (mk_forall{Bvar = x', Body = t'})
       val thm1 = EQ_MP alph (GEN x'(UNDISCH (SPEC x' (ASSUME ctm))))
       val imp2 = DISCH ctm (DISCH ant thm1)
   in
     IMP_ANTISYM_RULE imp1 imp2
   end
   handle HOL_ERR _ => raise ERR "RIGHT_IMP_FORALL_CONV" "";

(* ---------------------------------------------------------------------*)
(* EXISTS_IMP_CONV, implements the following axiom schemes.             *)
(*                                                                      *)
(*      |- (?x. P==>Q[x]) = (P ==> (?x.Q[x]))     [x not free in P]     *)
(*                                                                      *)
(*      |- (?x. P[x]==>Q) = ((!x.P[x]) ==> Q)     [x not free in Q]     *)
(*                                                                      *)
(*      |- (?x. P==>Q) = ((!x.P) ==> (?x.Q))      [x not free in P==>Q] *)
(* ---------------------------------------------------------------------*)
local val EI_ERR = ERR"EXISTS_IMP_CONV" "expecting `?x. P ==> Q`"
in
fun EXISTS_IMP_CONV tm =
 let val {Bvar,Body} = dest_exists tm handle HOL_ERR _ => raise EI_ERR
     val {ant = P,conseq = Q} = dest_imp Body handle HOL_ERR _ => raise EI_ERR
     val fP = free_in Bvar P
     and fQ =  free_in Bvar Q
 in
   if (fP andalso fQ) then raise ERR "EXISTS_IMP_CONV"
          ("`"^(#Name(dest_var Bvar))^ "` free on both sides of `==>`") else
   if fP
   then let val allp = mk_forall{Bvar = Bvar, Body = P}
            val th1 = SPEC Bvar (ASSUME allp)
            val thm1 = MP (ASSUME Body) th1
            val imp1 = DISCH tm (CHOOSE(Bvar,ASSUME tm)(DISCH allp thm1))
            val otm = rand(concl imp1)
            val thm2 = EXISTS(tm,Bvar)(DISCH P (UNDISCH(ASSUME otm)))
            val notP = mk_neg P
            val notP_thm = ASSUME notP
            val nex =  mk_exists{Bvar = Bvar, Body = notP}
            val asm1 = EXISTS (nex, Bvar) notP_thm
            val th2 = CCONTR P (MP (ASSUME (mk_neg nex)) asm1)
            val th3 = CCONTR nex (MP (ASSUME (mk_neg allp)) (GEN Bvar th2))
            val thm4 = DISCH P (CONTR Q (UNDISCH notP_thm))
            val thm5 = CHOOSE(Bvar,th3)(EXISTS(tm,Bvar)thm4)
            val thm6 = DISJ_CASES (SPEC allp EXCLUDED_MIDDLE) thm2 thm5
        in
          IMP_ANTISYM_RULE imp1 (DISCH otm thm6)
        end
   else
   if fQ
   then let val thm1 = EXISTS (mk_exists{Bvar=Bvar, Body=Q},Bvar)
                                (UNDISCH(ASSUME Body))
            val imp1 = DISCH tm (CHOOSE(Bvar,ASSUME tm) (DISCH P thm1))
            val thm2 = UNDISCH (ASSUME (rand(concl imp1)))
            val thm3 = CHOOSE(Bvar,thm2) (EXISTS(tm,Bvar)(DISCH P(ASSUME Q)))
            val thm4 = EXISTS(tm,Bvar)
                          (DISCH P (CONTR Q(UNDISCH(ASSUME(mk_neg P)))))
            val thm5 = DISJ_CASES (SPEC P EXCLUDED_MIDDLE) thm3 thm4
        in
          IMP_ANTISYM_RULE imp1 (DISCH(rand(concl imp1)) thm5)
        end
   else let val eQ = mk_exists{Bvar = Bvar, Body = Q}
            and aP = mk_forall{Bvar = Bvar, Body = P}
            val thm1 = EXISTS(eQ,Bvar)(UNDISCH(ASSUME Body))
            val thm2 = DISCH aP (PROVE_HYP (SPEC Bvar (ASSUME aP)) thm1)
            val imp1 = DISCH tm (CHOOSE(Bvar,ASSUME tm) thm2)
            val thm2 = CHOOSE(Bvar,UNDISCH(ASSUME(rand(concl imp1))))
                           (ASSUME Q)
            val thm3 = DISCH P (PROVE_HYP (GEN Bvar (ASSUME P)) thm2)
            val imp2 = DISCH (rand(concl imp1)) (EXISTS(tm,Bvar) thm3)
        in
          IMP_ANTISYM_RULE imp1 imp2
        end
 end
   handle (e as HOL_ERR{origin_structure = "Conv",
             origin_function = "EXISTS_IMP_CONV",...}) => raise e
        | HOL_ERR _ => raise ERR"EXISTS_IMP_CONV" ""
end;



(* ---------------------------------------------------------------------*)
(* LEFT_IMP_FORALL_CONV, implements the following theorem-scheme:       *)
(*                                                                      *)
(*    |- (!x. t1[x]) ==> t2  =  ?x'. t1[x'] ==> t2                      *)
(*                                                                      *)
(* where x' is a variant of x chosen not to be free in the input term   *)
(*----------------------------------------------------------------------*)
fun LEFT_IMP_FORALL_CONV tm =
   let val {ant,conseq} = dest_imp tm
       val {Bvar,Body} = dest_forall ant
       val x' = variant (free_vars tm) Bvar
       val t1' = subst [Bvar |-> x'] Body
       val not_t1'_thm = ASSUME (mk_neg t1')
       val th1 = SPEC x' (ASSUME ant)
       val new_imp = mk_imp{ant = t1', conseq = conseq}
       val thm1 = MP (ASSUME new_imp) th1
       val otm = mk_exists{Bvar = x', Body = new_imp}
       val imp1 = DISCH otm (CHOOSE(x',ASSUME otm)(DISCH ant thm1))
       val thm2 = EXISTS(otm,x') (DISCH t1' (UNDISCH(ASSUME tm)))
       val nex =  mk_exists{Bvar = x', Body = mk_neg t1'}
       val asm1 = EXISTS (nex, x') not_t1'_thm
       val th2 = CCONTR t1' (MP (ASSUME (mk_neg nex)) asm1)
       val th3 = CCONTR nex (MP(ASSUME(mk_neg ant)) (GEN x' th2))
       val thm4 = DISCH t1' (CONTR conseq (UNDISCH not_t1'_thm))
       val thm5 = CHOOSE(x',th3)
                      (EXISTS(mk_exists{Bvar = x',Body = concl thm4},x')thm4)
       val thm6 = DISJ_CASES (SPEC ant EXCLUDED_MIDDLE) thm2 thm5
   in
     IMP_ANTISYM_RULE (DISCH tm thm6) imp1
   end
   handle HOL_ERR _ => raise ERR "LEFT_IMP_FORALL_CONV" "";

(* ---------------------------------------------------------------------*)
(* RIGHT_IMP_EXISTS_CONV, implements the following theorem-scheme:      *)
(*                                                                      *)
(*    |- (t1 ==> ?x. t2)  =  ?x'. t1 ==> t2[x'/x]                       *)
(*                                                                      *)
(* where x' is a variant of x chosen not to be free in the input term.  *)
(*----------------------------------------------------------------------*)
fun RIGHT_IMP_EXISTS_CONV tm =
   let val {ant,conseq} = dest_imp tm
       val {Bvar,Body} = dest_exists conseq
       val x' = variant (free_vars tm) Bvar
       val t2' = subst [Bvar |-> x'] Body
       val new_imp = mk_imp{ant = ant, conseq = t2'}
       val otm = mk_exists{Bvar = x', Body = new_imp}
       val thm1 = EXISTS(conseq,x')(UNDISCH(ASSUME new_imp))
       val imp1 = DISCH otm (CHOOSE(x',ASSUME otm) (DISCH ant thm1))
       val thm2 = UNDISCH (ASSUME tm)
       val thm3 = CHOOSE (x',thm2) (EXISTS (otm,x') (DISCH ant (ASSUME t2')))
       val thm4 = DISCH ant (CONTR t2'(UNDISCH(ASSUME(mk_neg ant))))
       val thm5 = EXISTS(otm,x') thm4
       val thm6 = DISJ_CASES (SPEC ant EXCLUDED_MIDDLE) thm3 thm5
   in
     IMP_ANTISYM_RULE (DISCH tm thm6) imp1
   end
   handle HOL_ERR _ => raise ERR "RIGHT_IMP_EXISTS_CONV" "";

(* ---------------------------------------------------------------------*)
(* X_SKOLEM_CONV : introduce a skolem function.                         *)
(*                                                                      *)
(*   |- (!x1...xn. ?y. tm[x1,...,xn,y])                                 *)
(*        =                                                             *)
(*      (?f. !x1...xn. tm[x1,..,xn,f x1 ... xn]                         *)
(*                                                                      *)
(* The first argument is the function f.                                *)
(* ---------------------------------------------------------------------*)

fun X_SKOLEM_CONV v =
   if not(is_var v)
   then raise ERR "X_SKOLEM_CONV"  "first argument not a variable"
  else
 fn tm =>
  let val (xs,ex) = strip_forall tm
      val (ab as {Bvar,Body}) = dest_exists ex handle HOL_ERR _
        =>  raise ERR "X_SKOLEM_CONV" "expecting `!x1...xn. ?y.tm`"
      val fx = Term.list_mk_comb(v,xs) handle HOL_ERR _
        => raise ERR "X_SKOLEM_CONV" "function variable has wrong type"
  in
  if free_in v tm then raise ERR"X_SKOLEM_CONV"
                     ("`"^(#Name(dest_var v))^"` free in the input term")
  else let val pat_bod = list_mk_forall(xs,subst[Bvar |-> fx]Body)
           val pat = mk_exists{Bvar = v, Body = pat_bod}
           val fnn = list_mk_abs(xs,mk_select ab)
           val bth = SYM(LIST_BETA_CONV (Term.list_mk_comb(fnn,xs)))
           val thm1 = SUBST [Bvar |-> bth] Body
                            (SELECT_RULE (SPECL xs (ASSUME tm)))
           val imp1 = DISCH tm (EXISTS (pat,fnn) (GENL xs thm1))
           val thm2 = SPECL xs (ASSUME pat_bod)
           val thm3 = GENL xs (EXISTS (ex,fx) thm2)
           val imp2 = DISCH pat (CHOOSE (v,ASSUME pat) thm3)
       in
       IMP_ANTISYM_RULE imp1 imp2
       end
  end
  handle (e as HOL_ERR{origin_structure = "Conv",
                       origin_function = "X_SKOLEM_CONV",...}) => raise e
        | HOL_ERR _ => raise ERR "X_SKOLEM_CONV" "";

(* ---------------------------------------------------------------------*)
(* SKOLEM_CONV : introduce a skolem function.                           *)
(*                                                                      *)
(*   |- (!x1...xn. ?y. tm[x1,...,xn,y])                                 *)
(*        =                                                             *)
(*      (?y'. !x1...xn. tm[x1,..,xn,y' x1 ... xn]                       *)
(*                                                                      *)
(* Where y' is a primed variant of y not free in the input term.        *)
(* ---------------------------------------------------------------------*)

local fun mkfty tm ty = type_of tm --> ty
in
fun SKOLEM_CONV tm =
   let val (xs,ex) = strip_forall tm
       val {Bvar, ...} = dest_exists ex
       val {Name,Ty} = dest_var Bvar
       val fv = mk_var{Name=Name, Ty = itlist mkfty xs Ty}
   in
     X_SKOLEM_CONV (variant (free_vars tm) fv) tm
   end
   handle HOL_ERR _ => raise ERR "SKOLEM_CONV" ""
end;


(*----------------------------------------------------------------------*)
(* SYM_CONV : a conversion for symmetry of equality.                    *)
(*                                                                      *)
(* e.g. SYM_CONV "x=y"   ---->   (x=y) = (y=x).                         *)
(*----------------------------------------------------------------------*)

fun SYM_CONV tm =
   let val {lhs,rhs} = dest_eq tm
       val th = INST_TYPE [Type.alpha |-> type_of lhs] EQ_SYM_EQ
   in
     SPECL [lhs,rhs] th
   end
   handle HOL_ERR _ => raise ERR "SYM_CONV" "";


(*---------------------------------------------------------------------------
 *
 *     A |- t1 = t2
 *    --------------   (t2' got from t2 using a conversion)
 *     A |- t1 = t2'
 *---------------------------------------------------------------------------*)

fun RIGHT_CONV_RULE conv th =
    TRANS th (conv(rhs(concl th))) handle UNCHANGED => th

(* ---------------------------------------------------------------------*)
(* FUN_EQ_CONV "f = g"  returns:  |- (f = g) = !x. (f x = g x).         *)
(*                                                                      *)
(* Notes: f and g must be functions. The conversion choses an "x" not   *)
(* free in f or g. This conversion just states that functions are equal *)
(* IFF the results of applying them to an arbitrary value are equal.    *)
(*                                                                      *)
(* New version: TFM 88.03.31                                            *)
(* ---------------------------------------------------------------------*)
fun FUN_EQ_CONV tm =
 let val (ty1,_) = dom_rng(type_of (lhs tm))
     val vars = free_vars tm
     val varnm = if Type.is_vartype ty1 then "x"
                  else Char.toString (Lib.trye hd
                       (String.explode (fst(Type.dest_type ty1))))
     val x = variant vars (mk_var{Name=varnm, Ty=ty1})
     val imp1 = DISCH_ALL (GEN x (AP_THM (ASSUME tm) x))
     val asm = ASSUME (concl (GEN x (AP_THM (ASSUME tm) x)))
 in
   IMP_ANTISYM_RULE imp1 (DISCH_ALL (EXT asm))
 end
 handle HOL_ERR _ => raise ERR "FUN_EQ_CONV" "";


(* --------------------------------------------------------------------- *)
(* X_FUN_EQ_CONV "x" "f = g"                                             *)
(*                                                                       *)
(* yields |- (f = g) = !x. f x = g x                                     *)
(*                                                                       *)
(* fails if x free in f or g, or x not of the right type.                *)
(* --------------------------------------------------------------------- *)

fun X_FUN_EQ_CONV x tm =
 if not(is_var x)
 then raise ERR "X_FUN_EQ_CONV" "first arg is not a variable"
 else
 if mem x (free_vars tm)
 then raise ERR"X_FUN_EQ_CONV" (#Name(dest_var x)^" is a free variable")
 else
 let val (ty,_) = with_exn dom_rng(type_of(lhs tm))
                   (ERR "X_FUN_EQ_CONV" "lhs and rhs not functions")
 in
   if ty = type_of x
   then let val imp1 = DISCH_ALL (GEN x (AP_THM (ASSUME tm) x))
            val asm  = ASSUME (concl (GEN x (AP_THM (ASSUME tm) x)))
        in IMP_ANTISYM_RULE imp1 (DISCH_ALL (EXT asm))
        end
   else raise ERR "X_FUN_EQ_CONV" (#Name(dest_var x)^" has the wrong type")
 end
 handle e => raise (wrap_exn "Conv" "X_FUN_EQ_CONV" e);

(* ---------------------------------------------------------------------*)
(* SELECT_CONV: a conversion for introducing "?" when P [@x.P[x]].      *)
(*                                                                      *)
(* SELECT_CONV "P [@x.P [x]]" ---> |- P [@x.P [x]] = ?x. P[x]           *)
(*                                                                      *)
(* Added: TFM 88.03.31                                                  *)
(* ---------------------------------------------------------------------*)
(* fun SELECT_CONV tm =
**   let val epsl = find_terms is_select tm
**       fun findfn t = (tm = subst [{redex = #Bvar (dest_select t),
**                                    residue = t}]
**                                  (#Body (dest_select t)))
**       val sel = first findfn epsl
**       val ex  = mk_exists(dest_select sel)
**       val imp1 = DISCH_ALL (SELECT_RULE (ASSUME ex))
**       and imp2 = DISCH_ALL (EXISTS (ex,sel) (ASSUME tm))
**   in
**   IMP_ANTISYM_RULE imp2 imp1
**   end
**   handle _ => raise ERR{function = "SELECT_CONV", message = ""};
*)

local val f = mk_var{Name="f",Ty=alpha-->bool}
      val th1 = AP_THM EXISTS_DEF f
      val th2 = CONV_RULE (RAND_CONV BETA_CONV) th1
      val tyv = Type.mk_vartype "'a"
      fun EXISTS_CONV{Bvar,Body} =
        let val ty = type_of Bvar
            val ins = INST_TYPE [tyv |-> ty] th2
            val theta = [inst [tyv |-> ty] f |-> mk_abs{Bvar=Bvar,Body=Body}]
            val th = INST theta ins
        in
          CONV_RULE (RAND_CONV BETA_CONV) th
        end
      fun find_first p tm =
        if (p tm) then tm
        else if (is_abs tm)
         then find_first p (body tm)
        else if is_comb tm
             then let val {Rator,Rand} = dest_comb tm
                  in find_first p Rator
                      handle HOL_ERR _ => find_first p Rand
                  end
             else raise ERR"SELECT_CONV.find_first" ""
in
fun SELECT_CONV tm =
   let fun right t =
          let val {Bvar,Body} = dest_select t
          in Term.aconv (subst[Bvar |-> t] Body) tm
          end handle HOL_ERR _ => false
       val epi = find_first right tm
   in
     SYM (EXISTS_CONV (dest_select epi))
   end
   handle HOL_ERR _ => raise ERR "SELECT_CONV" ""
end;

(* ---------------------------------------------------------------------*)
(* CONTRAPOS_CONV: convert an implication to its contrapositive.        *)
(*                                                                      *)
(* CONTRAPOS_CONV "a ==> b" --> |- (a ==> b) = (~b ==> ~a)              *)
(*                                                                      *)
(* Added: TFM 88.03.31                                                  *)
(* Revised: TFM 90.07.13                                                *)
(* ---------------------------------------------------------------------*)

fun CONTRAPOS_CONV tm =
   let val {ant,conseq} = dest_imp tm
       val negc = mk_neg conseq
       and contra = mk_imp{ant = mk_neg conseq, conseq = mk_neg ant}
       val imp1 = DISCH negc (NOT_INTRO(IMP_TRANS(ASSUME tm)(ASSUME negc)))
       and imp2 = DISCH ant (CCONTR conseq (UNDISCH (UNDISCH (ASSUME contra))))
   in
     IMP_ANTISYM_RULE (DISCH tm imp1) (DISCH contra imp2)
   end
   handle HOL_ERR _ => raise ERR "CONTRAPOS_CONV" "";

(* ---------------------------------------------------------------------*)
(* ANTE_CONJ_CONV: convert an implication with conjuncts in its         *)
(*                antecedant to a series of implications.               *)
(*                                                                      *)
(* ANTE_CONJ_CONV "a1 /\ a2 ==> c"                                      *)
(*      ----> |- a1 /\ a2 ==> c = (a1 ==> (a2 ==> c))                   *)
(*                                                                      *)
(* Added: TFM 88.03.31                                                  *)
(* ---------------------------------------------------------------------*)
val ANTE_CONJ_CONV = REWR_CONV (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) AND_IMP_INTRO);

(* ---------------------------------------------------------------------*)
(* AND_IMP_INTRO_CONV: convert a series of implications to an           *)
(*                     implication with conjuncts in its antecedent     *)
(*                                                                      *)
(* AND_IMP_INTRO_CONV "a1 ==> a2 ==> c"                                 *)
(*      ----> |- (a1 ==> (a2 ==> c)) = (a1 /\ a2 ==> c)                 *)
(*                                                                      *)
(* Added: Thomas Tuerk, 2nd August 2010                                 *)
(* ---------------------------------------------------------------------*)
val AND_IMP_INTRO_CONV = REWR_CONV AND_IMP_INTRO;

(* ---------------------------------------------------------------------*)
(* SWAP_EXISTS_CONV: swap the order of existentially quantified vars.   *)
(*                                                                      *)
(* SWAP_EXISTS_CONV "?x y.t[x,y]" ---> |- ?x y.t[x,y] = ?y x.t[x,y]     *)
(*                                                                      *)
(* AUTHOR: Paul Loewenstein 3 May 1988                                  *)
(* ---------------------------------------------------------------------*)

fun SWAP_EXISTS_CONV xyt =
   let val {Bvar=x, Body=yt} = dest_exists xyt
       val {Bvar=y, Body=t} = dest_exists yt
       val xt  = mk_exists {Bvar=x, Body=t}
       val yxt = mk_exists{Bvar=y, Body=xt}
       val t_thm = ASSUME t
   in
     IMP_ANTISYM_RULE
         (DISCH xyt (CHOOSE (x,ASSUME xyt) (CHOOSE (y, (ASSUME yt))
          (EXISTS (yxt,y) (EXISTS (xt,x) t_thm)))))
         (DISCH yxt (CHOOSE (y,ASSUME yxt) (CHOOSE (x, (ASSUME xt))
         (EXISTS (xyt,x) (EXISTS (yt,y) t_thm)))))
   end
   handle HOL_ERR _ => raise ERR "SWAP_EXISTS_CONV" "";



(* ---------------------------------------------------------------------*)
(* EXISTS_SIMP_CONV: gets rid of unused allquantification               *)
(*                                                                      *)
(* |- ?x. P = P                                                         *)
(* ---------------------------------------------------------------------*)
fun EXISTS_SIMP_CONV xt =
   let
     val {Bvar=x, Body=t} = dest_exists xt
   in
     IMP_ANTISYM_RULE
         (DISCH xt (CHOOSE (x, ASSUME xt) (ASSUME t)))
         (DISCH t (EXISTS(xt, x) (ASSUME t)))
   end


(* ---------------------------------------------------------------------*)
(* RESORT_EXISTS_CONV: resorts the order of existentially quantified    *)
(*  vars, as specified by a given resort function                       *)
(*                                                                      *)
(* RESORT_EXISTS_CONV rev "?x1 x2 x3. t" ---> |-                        *)
(*                         ?x1 x2 x3. t = ?x3 x2 x1. t                  *)
(*                                                                      *)
(* The standard use of this conversion is with a resort function, that  *)
(* returns a permutation of the original variables. However, it can     *)
(* also introduce or eliminate variables, provided that these variables *)
(* are not free in t.                                                   *)
(*                                                                      *)
(* RESORT_EXISTS_CONV (K [``x2``, ``new``]) ``?x1 x2 x3. t`` --->       *)
(*                   |- ?x1 x2 x3. t = ?x2 new. t                       *)
(* ---------------------------------------------------------------------*)
local
   fun mk_list_exists_thm ys xs t =
   let
      val thm1 = foldr (fn (v, thm) =>
        (EXISTS (mk_exists {Bvar = v, Body = (concl thm)}, v) thm))
        (ASSUME t) xs
      val (t',thm2) = foldr (fn (v, (t,thm)) =>
         let val t' = (mk_exists {Bvar = v, Body = t}) in
             (t', (CHOOSE (v, ASSUME t') thm)) end) (t, thm1) ys
   in
      DISCH t' thm2
   end;
in

fun RESORT_EXISTS_CONV rs xst =
   let val (xs, t) = strip_exists xst
       val ys = rs xs;
   in
     IMP_ANTISYM_RULE
        (mk_list_exists_thm xs ys t)
        (mk_list_exists_thm ys xs t)
   end

end;

(* ---------------------------------------------------------------------*)
(* SWAP_FORALL_CONV: swap the order of existentially quantified vars.   *)
(*                                                                      *)
(* SWAP_FORALL_CONV "!x y.t[x,y]" ---> |- !x y.t[x,y] = !y x.t[x,y]     *)
(* ---------------------------------------------------------------------*)
fun SWAP_FORALL_CONV xyt =
   let val {Bvar=x, Body=yt} = dest_forall xyt
       val {Bvar=y, Body=t} = dest_forall yt
       val xt  = mk_forall {Bvar=x, Body=t}
       val yxt = mk_forall {Bvar=y, Body=xt}
   in
     IMP_ANTISYM_RULE
         (DISCH xyt (GENL [y,x] (SPECL [x,y] (ASSUME xyt))))
         (DISCH yxt (GENL [x,y] (SPECL [y,x] (ASSUME yxt))))
   end

(* ---------------------------------------------------------------------*)
(* RESORT_FORALL_CONV: resorts the order of allquantified vars, as      *)
(*    specified by a given resort function                              *)
(*                                                                      *)
(* RESORT_FORALL_CONV rev "!x1 x2 x3. t" ---> |-                        *)
(*                         !x1 x2 x3. t = !x3 x2 x1. t                  *)
(*                                                                      *)
(* The standard use of this conversion is with a resort function, that  *)
(* returns a permutation of the original variables. However, it can     *)
(* also introduce or eliminate variables, provided that these variables *)
(* are not free in t.                                                   *)
(*                                                                      *)
(* RESORT_FORALL_CONV (K [``x2``, ``new``]) ``!x1 x2 x3. t`` --->       *)
(*                   |- !x1 x2 x3. t = !x2 new. t                       *)
(* ---------------------------------------------------------------------*)
fun RESORT_FORALL_CONV rs xst =
   let val (xs, t) = strip_forall xst
       val ys = rs xs;
       val yst = list_mk_forall (ys, t)
   in
     IMP_ANTISYM_RULE
         (DISCH xst (GENL ys (SPECL xs (ASSUME xst))))
         (DISCH yst (GENL xs (SPECL ys (ASSUME yst))))
   end

(* ---------------------------------------------------------------------*)
(* FORALL_SIMP_CONV: gets rid of unused allquantification               *)
(*                                                                      *)
(* |- !x. P = P                                                         *)
(* ---------------------------------------------------------------------*)
fun FORALL_SIMP_CONV xt =
   let
     val {Bvar=x, Body=t} = dest_forall xt
   in
     IMP_ANTISYM_RULE
         (DISCH xt (SPEC x (ASSUME xt)))
         (DISCH t (GEN x (ASSUME t)))
   end


(* ---------------------------------------------------------------------*)
(* LIST version of some conversions defined above. The final goal is    *)
(* to minimise the scope of universal quantifiers.                      *)
(* ---------------------------------------------------------------------*)

local
   fun FORALL_DEPTH_CONV c t =
      let
         val (_, body) = Psyntax.dest_forall t;
      in
         if is_forall body then
            (QUANT_CONV (FORALL_DEPTH_CONV c) THENC c) t
         else c t
      end;

   fun NUM_QUANT_CONV n =
      (funpow n QUANT_CONV)

in

   (* -------------------------------------------------- *)
   (* Gets rid of unused quantifiers                     *)
   (*                                                    *)
   (* ``!x1 x2 x3. P x2`` --> ``!x2. P x2``              *)
   (* -------------------------------------------------- *)
   fun LIST_FORALL_SIMP_CONV t =
   let
      val (vs, body) = strip_forall t;
      val _ = if null vs then Feedback.fail() else ()
      val fv_set = FVL [body] empty_tmset
      val (vs_free, vs_rest) = partition (fn v => HOLset.member (fv_set, v)) vs;
      val _ = if null vs_rest then Feedback.fail() else ()
      val thm = RESORT_FORALL_CONV (K vs_free) t
   in
      thm
   end;

   (* -------------------------------------------------- *)
   (* Moves over conjunctions                            *)
   (*                                                    *)
   (* ``!x1 x2 x3. P1 /\ P2`` -->                        *)
   (* ``!x1 x2 x3. P1 /\ !x1 x2 x3. P2``                 *)
   (* -------------------------------------------------- *)
   val LIST_FORALL_AND_CONV =
      FORALL_DEPTH_CONV FORALL_AND_CONV


   (* -------------------------------------------------- *)
   (* Moves over implications                            *)
   (*                                                    *)
   (* ``!x1 x2 x3. P1 x1 x2 ==> P2 x2 x3`` -->           *)
   (* ``!x2.    (?x1. P1 x1 x2) ==> (!x3. P2 x2 x3)`` or *)
   (* ``!x1 x2.       P1 x1 x2) ==> (!x3. P2 x2 x3)``    *)
   (* depending on the value of exists_intro             *)
   (* -------------------------------------------------- *)
   fun LIST_FORALL_IMP_CONV exists_intro t =
   let
      val (vs, body) = strip_forall t;
      val (b1, b2) = Psyntax.dest_imp_only body;

      val fvs_1 = FVL [b1] empty_tmset
      val fvs_2 = FVL [b2] empty_tmset

      val (vs_b1x, vs_rest) = partition (fn v => HOLset.member (fvs_1, v)) vs;
      val (vs_b12, vs_b1)  = partition (fn v => HOLset.member (fvs_2, v)) vs_b1x;
      val (vs_b2 , _)  = partition (fn v => HOLset.member (fvs_2, v)) vs_rest;

      val _ = if (null vs_b2) andalso
                 ((not exists_intro) orelse (null vs_b1)) then
                 raise UNCHANGED else ()

      val (n, rs) = if exists_intro then (length vs_b12, vs_b12 @ vs_b1 @ vs_b2) else
                        (length vs_b1x, vs_b1x @ vs_b2)
      val conv1 = RESORT_FORALL_CONV (K rs)
      val conv2 = NUM_QUANT_CONV n (FORALL_DEPTH_CONV FORALL_IMP_CONV)
   in
      (conv1 THENC conv2) t
   end;


   (* -------------------------------------------------- *)
   (* Moves over or                                      *)
   (*                                                    *)
   (* ``!x1 x2 x3. P1 x1 x2 \/ P2 x2 x3`` -->            *)
   (* ``!x2. (!x1. P1 x1 x2) \/ (!x3. P2 x2 x3)``        *)
   (* -------------------------------------------------- *)
   fun LIST_FORALL_OR_CONV t =
   let
      val (vs, body) = strip_forall t;
      val (b1, b2) = Psyntax.dest_disj body;

      val fvs_1 = FVL [b1] empty_tmset
      val fvs_2 = FVL [b2] empty_tmset

      val (vs_b1x, vs_rest) = partition (fn v => HOLset.member (fvs_1, v)) vs;
      val (vs_b12, vs_b1)  = partition (fn v => HOLset.member (fvs_2, v)) vs_b1x;
      val (vs_b2 , _)  = partition (fn v => HOLset.member (fvs_2, v)) vs_rest;

      val _ = if (null vs_b1) andalso (null vs_b2) then
              raise UNCHANGED else ()
      val conv1 = RESORT_FORALL_CONV (K (vs_b12 @ vs_b1 @ vs_b2))
      val conv2 = NUM_QUANT_CONV (length vs_b12) (FORALL_DEPTH_CONV FORALL_OR_CONV)
   in
      (conv1 THENC conv2) t
   end;


   (* -------------------------------------------------- *)
   (* Moves over negation                                *)
   (*                                                    *)
   (* ``!x1 x2 x3. ~P1`` --> ``~?x1 x2 x3. P1``          *)
   (* -------------------------------------------------- *)
   val LIST_FORALL_NOT_CONV =
     FORALL_DEPTH_CONV FORALL_NOT_CONV


   (* -------------------------------------------------- *)
   (* Tries to minimise the scope of universal           *)
   (* quantifiers using all the conversions above        *)
   (* -------------------------------------------------- *)
   fun MINISCOPE_FORALL_CONV exists_intro t =
   let
      val (vs, body) = strip_forall t;
      val _ = if null vs then raise UNCHANGED else ()
   in
      (if (is_conj body) then LIST_FORALL_AND_CONV else
      if (is_disj body) then LIST_FORALL_OR_CONV else
      if (is_imp_only body) then LIST_FORALL_IMP_CONV exists_intro else
      if (is_neg body andalso exists_intro) then LIST_FORALL_NOT_CONV else
         LIST_FORALL_SIMP_CONV) t
   end
end;


(* ---------------------------------------------------------------------*)
(* LIST version of some conversions defined above. The final goal is    *)
(* to minimise the scope of existential quantifiers.                    *)
(* ---------------------------------------------------------------------*)

local
   fun EXISTS_DEPTH_CONV c t =
      let
         val (_, body) = Psyntax.dest_exists t;
      in
         if is_exists body then
            (QUANT_CONV (EXISTS_DEPTH_CONV c) THENC c) t
         else c t
      end;

   fun NUM_QUANT_CONV n =
      (funpow n QUANT_CONV)

in

   (* -------------------------------------------------- *)
   (* Gets rid of unused quantifiers                     *)
   (*                                                    *)
   (* ``?x1 x2 x3. P x2`` --> ``?x2. P x2``              *)
   (* -------------------------------------------------- *)
   fun LIST_EXISTS_SIMP_CONV t =
   let
      val (vs, body) = strip_exists t;
      val _ = if null vs then Feedback.fail() else ()
      val fv_set = FVL [body] empty_tmset
      val (vs_free, vs_rest) = partition (fn v => HOLset.member (fv_set, v)) vs;
      val _ = if null vs_rest then Feedback.fail() else ()
      val thm = RESORT_EXISTS_CONV (K vs_free) t
   in
      thm
   end;

   (* -------------------------------------------------- *)
   (* Moves over disjunctions                            *)
   (*                                                    *)
   (* ``?x1 x2 x3. P1 \/ P2`` -->                        *)
   (* ``?x1 x2 x3. P1 \/ ?x1 x2 x3. P2``                 *)
   (* -------------------------------------------------- *)
   val LIST_EXISTS_OR_CONV =
      EXISTS_DEPTH_CONV EXISTS_OR_CONV


   (* -------------------------------------------------- *)
   (* Moves over implications                            *)
   (*                                                    *)
   (* ``?x1 x2 x3. P1 x1 x2 ==> P2 x2 x3`` -->           *)
   (* ``?x2.    (!x1. P1 x1 x2) ==> (?x3. P2 x2 x3)`` or *)
   (* ``?x1 x2.       P1 x1 x2) ==> (?x3. P2 x2 x3)``    *)
   (* depending on the value of forall_intro             *)
   (* -------------------------------------------------- *)
   fun LIST_EXISTS_IMP_CONV forall_intro t =
   let
      val (vs, body) = strip_exists t;
      val (b1, b2) = Psyntax.dest_imp_only body;

      val fvs_1 = FVL [b1] empty_tmset
      val fvs_2 = FVL [b2] empty_tmset

      val (vs_b1x, vs_rest) = partition (fn v => HOLset.member (fvs_1, v)) vs;
      val (vs_b12, vs_b1)  = partition (fn v => HOLset.member (fvs_2, v)) vs_b1x;
      val (vs_b2 , _)  = partition (fn v => HOLset.member (fvs_2, v)) vs_rest;

      val _ = if (null vs_b2) andalso
                 ((not forall_intro) orelse (null vs_b1)) then
                 raise UNCHANGED else ()

      val (n, rs) = if forall_intro then (length vs_b12, vs_b12 @ vs_b1 @ vs_b2) else
                        (length vs_b1x, vs_b1x @ vs_b2)
      val conv1 = RESORT_EXISTS_CONV (K rs)
      val conv2 = NUM_QUANT_CONV n (EXISTS_DEPTH_CONV EXISTS_IMP_CONV)
   in
      (conv1 THENC conv2) t
   end;


   (* ---------------------------------------------------------------------*)
   (* BOTH_EXISTS_IMP_CONV, implements the following axiom scheme.         *)
   (*                                                                      *)
   (*      |- (?x. P[x]==>Q[x]) = ((!x.P[x]) ==> (?x.Q[x])                 *)
   (*                                                                      *)
   (* Thus, it handles thes missing case of EXISTS_IMP_CONV, where         *)
   (* x is free in both P an Q                                             *)
   (* ---------------------------------------------------------------------*)
   val BOTH_EXISTS_IMP_CONV =
   let
       val conv1 = QUANT_CONV (PART_MATCH lhs boolTheory.IMP_DISJ_THM)
       val conv2 = EXISTS_OR_CONV
       val conv3 = (RATOR_CONV o RAND_CONV) EXISTS_NOT_CONV
       val conv4 = PART_MATCH lhs (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) boolTheory.IMP_DISJ_THM)
   in
       (conv1 THENC conv2 THENC conv3 THENC conv4)
   end;


   (* -------------------------------------------------- *)
   (* Moves over conjunctions                            *)
   (*                                                    *)
   (* ``?x1 x2 x3. P1 x1 x2 /\ P2 x2 x3`` -->            *)
   (* ``?x2. (?x1. P1 x1 x2) /\ (?x3. P2 x2 x3)``        *)
   (* -------------------------------------------------- *)
   fun LIST_EXISTS_AND_CONV t =
   let
      val (vs, body) = strip_exists t;
      val (b1, b2) = Psyntax.dest_conj body;

      val fvs_1 = FVL [b1] empty_tmset
      val fvs_2 = FVL [b2] empty_tmset

      val (vs_b1x, vs_rest) = partition (fn v => HOLset.member (fvs_1, v)) vs;
      val (vs_b12, vs_b1)  = partition (fn v => HOLset.member (fvs_2, v)) vs_b1x;
      val (vs_b2 , _)  = partition (fn v => HOLset.member (fvs_2, v)) vs_rest;

      val _ = if (null vs_b1) andalso (null vs_b2) then
              raise UNCHANGED else ()
      val conv1 = RESORT_EXISTS_CONV (K (vs_b12 @ vs_b1 @ vs_b2))
      val conv2 = NUM_QUANT_CONV (length vs_b12) (EXISTS_DEPTH_CONV EXISTS_AND_CONV)
   in
      (conv1 THENC conv2) t
   end;


   (* -------------------------------------------------- *)
   (* Moves over negation                                *)
   (*                                                    *)
   (* ``?x1 x2 x3. ~P1`` --> ``~!x1 x2 x3. P1``          *)
   (* -------------------------------------------------- *)
   val LIST_EXISTS_NOT_CONV =
     EXISTS_DEPTH_CONV EXISTS_NOT_CONV


   (* -------------------------------------------------- *)
   (* Tries to minimise the scope of universal           *)
   (* quantifiers using all the conversions above        *)
   (* -------------------------------------------------- *)
   fun MINISCOPE_EXISTS_CONV forall_intro t =
   let
      val (vs, body) = strip_exists t;
      val _ = if null vs then raise UNCHANGED else ()
   in
      (if (is_disj body) then LIST_EXISTS_OR_CONV else
      if (is_conj body) then LIST_EXISTS_AND_CONV else
      if (is_imp_only body) then LIST_EXISTS_IMP_CONV forall_intro else
      if (is_neg body andalso forall_intro) then LIST_EXISTS_NOT_CONV else
         LIST_EXISTS_SIMP_CONV) t
   end
end;



(* ---------------------------------------------------------------------*)
(* bool_EQ_CONV: conversion for boolean equality.                       *)
(*                                                                      *)
(* bool_EQ_CONV "b1 = b2" returns:                                      *)
(*                                                                      *)
(*    |- (b1 = b2) = T     if b1 and b2 are identical boolean terms     *)
(*    |- (b1 = b2)  = b2           if b1 = "T"                          *)
(*    |- (b1 = b2)  = b1           if b2 = "T"                          *)
(*                                                                      *)
(* Added TFM 88.03.31                                                   *)
(* Revised TFM 90.07.24                                                 *)
(* ---------------------------------------------------------------------*)

local val (Tb::bT::_) = map (GEN (--`b:bool`--))
                            (CONJUNCTS (SPEC (--`b:bool`--) EQ_CLAUSES))
in
fun bool_EQ_CONV tm =
   let val {lhs,rhs} = dest_eq tm
       val _ = if type_of rhs = Type.bool then ()
               else raise ERR"bool_EQ_CONV" "does not have boolean type"
   in if lhs=rhs then EQT_INTRO (REFL lhs) else
      if lhs=T then SPEC rhs Tb else
      if rhs=T then SPEC lhs bT
      else raise ERR"bool_EQ_CONV" "inapplicable"
   end
   handle e => raise (wrap_exn "Conv" "bool_EQ_CONV" e)
end;

(* ---------------------------------------------------------------------*)
(* EXISTS_UNIQUE_CONV: expands with the definition of unique existence. *)
(*                                                                      *)
(*                                                                      *)
(* EXISTS_UNIQUE_CONV "?!x.P[x]" yields the theorem:                    *)
(*                                                                      *)
(*     |- ?!x.P[x] = ?x.P[x] /\ !x y. P[x] /\ P[y] ==> (x=y)            *)
(*                                                                      *)
(* ADDED: TFM 90.05.06                                                  *)
(*                                                                      *)
(* REVISED: now uses a variant of x for y in 2nd conjunct [TFM 90.06.11]*)
(* ---------------------------------------------------------------------*)

local val v = genvar Type.bool
      val AND = boolSyntax.conjunction
      val IMP = boolSyntax.implication
      val check = assert boolSyntax.is_exists1
      fun MK_BIN f (e1,e2) = MK_COMB((AP_TERM f e1),e2)
      val rule = CONV_RULE o RAND_CONV o GEN_ALPHA_CONV
      fun MK_ALL x y tm = rule y (FORALL_EQ x tm)
      fun handle_ant{conj1, conj2} = (BETA_CONV conj1, BETA_CONV conj2)
      fun conv (nx,ny) t =
        case strip_forall t
         of ([ox,oy],imp) =>
             let val {ant,conseq} = dest_imp imp
                 val ant' = MK_BIN AND (handle_ant (dest_conj ant))
             in MK_ALL ox nx
                  (MK_ALL oy ny (MK_BIN IMP (ant',REFL conseq)))
             end
          | otherwise => raise ERR "EXISTS_UNIQUE" ""
in
fun EXISTS_UNIQUE_CONV tm =
   let val _ = check tm
       val {Rator,Rand} = dest_comb tm
       val (ab as {Bvar,Body}) = dest_abs Rand
       val def = INST_TYPE [alpha |-> type_of Bvar] EXISTS_UNIQUE_DEF
       val exp = RIGHT_BETA(AP_THM def Rand)
       and y = variant (all_vars Body) Bvar
   in
     SUBST [v |-> conv (Bvar,y) (rand(rand(concl exp)))]
           (mk_eq{lhs=tm, rhs=mk_conj{conj1=mk_exists ab, conj2=v}}) exp
   end
   handle HOL_ERR _ => raise ERR "EXISTS_UNIQUE_CONV" ""
end;


(* ---------------------------------------------------------------------*)
(* COND_CONV: conversion for simplifying conditionals:                  *)
(*                                                                      *)
(*   --------------------------- COND_CONV "T => u | v"                 *)
(*     |- (T => u | v) = u                                              *)
(*                                                                      *)
(*                                                                      *)
(*   --------------------------- COND_CONV "F => u | v"                 *)
(*     |- (F => u | v) = v                                              *)
(*                                                                      *)
(*                                                                      *)
(*   --------------------------- COND_CONV "b => u | u"                 *)
(*     |- (b => u | u) = u                                              *)
(*                                                                      *)
(*   --------------------------- COND_CONV "b => u | v" (u =alpha v)    *)
(*     |- (b => u | v) = u                                              *)
(*                                                                      *)
(* COND_CONV "P=>u|v" fails if P is neither "T" nor "F" and u =/= v.    *)
(* ---------------------------------------------------------------------*)

local val vt = genvar alpha
      and vf =  genvar alpha
      val gen = GENL [vt,vf]
      val (CT,CF) = (gen ## gen) (CONJ_PAIR (SPECL [vt,vf] COND_CLAUSES))
in
fun COND_CONV tm =
 let val {cond,larm,rarm} = dest_cond tm
     val INST_TYPE' = INST_TYPE [alpha |-> type_of larm]
 in
   if (cond=T) then SPEC rarm (SPEC larm (INST_TYPE' CT)) else
   if (cond=F) then SPEC rarm (SPEC larm (INST_TYPE' CF)) else
   if (larm=rarm) then SPEC larm (SPEC cond (INST_TYPE' COND_ID)) else
   if (aconv larm rarm)
     then let val cnd = AP_TERM (rator tm) (ALPHA rarm larm)
              val th = SPEC larm (SPEC cond (INST_TYPE' COND_ID))
          in TRANS cnd th
          end
     else raise ERR "" ""
 end
 handle HOL_ERR _ => raise ERR "COND_CONV" ""
end;


(* ===================================================================== *)
(* A rule defined using conversions.                                     *)
(* ===================================================================== *)


(* ---------------------------------------------------------------------*)
(* EXISTENCE: derives existence from unique existence:                  *)
(*                                                                      *)
(*    |- ?!x. P[x]                                                      *)
(* --------------------                                                 *)
(*    |- ?x. P[x]                                                       *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)

local val EXISTS_UNIQUE_DEF = boolTheory.EXISTS_UNIQUE_DEF
      val P = mk_var{Name="P", Ty=alpha-->bool}
      val th1 = SPEC P (CONV_RULE (X_FUN_EQ_CONV P) EXISTS_UNIQUE_DEF)
      val th2 = CONJUNCT1(UNDISCH(fst(EQ_IMP_RULE(RIGHT_BETA th1))))
      val ex1P = mk_comb{Rator=boolSyntax.exists1, Rand=P}

in
fun EXISTENCE th =
   let val _ = assert boolSyntax.is_exists1 (concl th)
       val {Rator,Rand} = dest_comb(concl th)
       val {Bvar,...} = dest_abs Rand
   in
     MP (SPEC Rand (INST_TYPE [alpha |-> type_of Bvar]
                      (GEN P (DISCH ex1P th2)))) th
   end
   handle HOL_ERR _ => raise ERR "EXISTENCE" ""
end;


(*-----------------------------------------------------------------------*)
(* AC_CONV - Prove equality using associative + commutative laws         *)
(*                                                                       *)
(* The conversion is given an associative and commutative law (it deduces*)
(* the relevant operator and type from these) in the form of the inbuilt *)
(* ones, and an equation to prove. It will try to prove this. Example:   *)
(*                                                                       *)
(*  AC_CONV(ADD_ASSOC,ADD_SYM) "(1 + 3) + (2 + 4) = 4 + (3 + (2 + 1))"   *)
(* [JRH 91.07.17]                                                        *)
(*-----------------------------------------------------------------------*)

fun AC_CONV(associative,commutative) =
 let val opr = (rator o rator o lhs o snd o strip_forall o concl) commutative
     val ty = (hd o #Args o dest_type o type_of) opr
     val x = mk_var{Name="x",Ty=ty}
     and y = mk_var{Name="y",Ty=ty}
     and z = mk_var{Name="z",Ty=ty}
     val xy = mk_comb{Rator=mk_comb{Rator=opr,Rand=x},Rand=y}
     and yz = mk_comb{Rator=mk_comb{Rator=opr,Rand=y},Rand=z}
     and yx = mk_comb{Rator=mk_comb{Rator=opr,Rand=y},Rand=x}
     val comm = PART_MATCH I commutative (mk_eq{lhs=xy,rhs=yx})
     and ass = PART_MATCH I (SYM (SPEC_ALL associative))
               (mk_eq{lhs=mk_comb{Rator=mk_comb{Rator=opr,Rand=xy},Rand=z},
                      rhs=mk_comb{Rator=mk_comb{Rator=opr,Rand=x},Rand=yz}})
     val asc = TRANS (SUBS [comm] (SYM ass)) (INST [y |-> x, x |-> y] ass)

     fun bubble head expr =
       let val {Rator,Rand=r} = dest_comb expr
           val {Rator=xopr, Rand = l} = dest_comb Rator
       in
       if term_eq xopr opr
       then if term_eq l head then REFL expr
            else if term_eq r head then INST [x |-> l, y |-> r] comm
              else let val subb = bubble head r
                    val eqv = AP_TERM (mk_comb{Rator=xopr,Rand=l}) subb
                 val {Rator,Rand=r'} = dest_comb(#rhs(dest_eq(concl subb)))
                 val {Rator=yopr,Rand=l'} = dest_comb Rator
               in
                 TRANS eqv (INST[x |-> l, y |-> l', z |-> r'] asc)
               end
       else raise ERR"AC_CONV" "bubble"
       end

     fun asce {lhs,rhs} =
       if term_eq lhs rhs then REFL lhs
       else let val {Rator,Rand=r'} = dest_comb lhs
                val {Rator=zopr,Rand=l'} = dest_comb Rator
            in
            if term_eq zopr opr
            then let val beq = bubble l' rhs
                     val rt = boolSyntax.rhs (concl beq)
                 in TRANS (AP_TERM (mk_comb{Rator=opr,Rand=l'})
                                   (asce{lhs=rand lhs, rhs=rand rt}))
                          (SYM beq)
                 end
            else raise ERR"AC_CONV" "asce"
            end
 in
  fn tm =>
    let val init = QCONV (TOP_DEPTH_CONV (REWR_CONV ass)) tm
        val gl = rhs (concl init)
    in EQT_INTRO (EQ_MP (SYM init) (asce (dest_eq gl)))
    end
 end
 handle e => raise (wrap_exn "Conv" "AC_CONV" e);

(*-----------------------------------------------------------------------*)
(* GSYM - General symmetry rule                                          *)
(*                                                                       *)
(* Reverses the first equation(s) encountered in a top-down search.      *)
(*                                                                       *)
(* [JRH 92.03.28]                                                        *)
(*-----------------------------------------------------------------------*)

val GSYM = CONV_RULE(ONCE_DEPTH_CONV SYM_CONV);

(*---------------------------------------------------------------------------
   Conversions for messing with bound variables.

   RENAME_VARS_CONV  renames variables under \ ! ? ?! or @ .
   SWAP_VARS_CONV    swaps variables under ! and ?,
                      e.g, given !x y. ... gives   !y x. ...
 ---------------------------------------------------------------------------*)
local
  fun rename vname t = let
    val (accessor, C_ACC) =
        if is_exists t orelse is_forall t orelse is_select t orelse
           is_exists1 t
        then (rand, RAND_CONV)
        else if is_abs t then (I, I)
        else raise ERR "rename_vars" "Term not a binder"
    val (ty, _) = dom_rng (type_of (accessor t))
    val newv = mk_var{Name=vname, Ty=ty}
  in
    C_ACC (ALPHA_CONV newv) t
  end
in
  fun RENAME_VARS_CONV varlist  =
    case varlist of
      [] => REFL
    | (v::vs) => rename v THENC BINDER_CONV (RENAME_VARS_CONV vs)

  fun SWAP_VARS_CONV t =
    if is_exists t then SWAP_EXISTS_CONV t else SWAP_FORALL_CONV t

end

(* ----------------------------------------------------------------------
    EXISTS_AND_REORDER_CONV

    moves an existential quantifier into a conjunctive body, first sorting
    the body so that conjuncts where the bound variable appears are
    put first.
   ---------------------------------------------------------------------- *)

fun EXISTS_AND_REORDER_CONV t = let
  open Psyntax
  val (var, body) = dest_exists t
      handle HOL_ERR _ => raise ERR "EXISTS_AND_REORDER_CONV"
                                    "Term not an existential"
  val conjs = strip_conj body
  val _ = length conjs > 1 orelse raise UNCHANGED
  val (there, notthere) = partition (free_in var) conjs
  val _ = (not (null notthere) andalso not (null there)) orelse raise UNCHANGED
  val newbody = mk_conj (list_mk_conj notthere, list_mk_conj there)
  val bodies_eq_thm =
      EQT_ELIM (AC_CONV (CONJ_ASSOC, CONJ_COMM) (mk_eq(body, newbody)))
in
  QUANT_CONV (K bodies_eq_thm) THENC EXISTS_AND_CONV
end t

(*---------------------------------------------------------------------------*)
(* Support for debugging complicated conversions                             *)
(*---------------------------------------------------------------------------*)

fun PRINT_CONV tm = (Parse.print_term tm; print "\n"; ALL_CONV tm);

(*---------------------------------------------------------------------------*)
(* Map a conversion over a theorem, preserving order of hypotheses.          *)
(*---------------------------------------------------------------------------*)

fun cnvMP eqth impth =
 let open boolSyntax
     val tm = snd(dest_imp(concl impth))
     val imp_refl = REFL implication
 in
   UNDISCH
    (EQ_MP (MK_COMB (MK_COMB(imp_refl,eqth),REFL tm)) impth)
 end;

fun MAP_THM cnv th =
 let val (hyps,c) = dest_thm th
     val cth = cnv c
     val hypths = map cnv hyps
 in itlist cnvMP hypths (DISCH_ALL (EQ_MP cth th))
 end
 handle HOL_ERR _ => raise ERR "MAP_THM" "";

end (* Conv *)
