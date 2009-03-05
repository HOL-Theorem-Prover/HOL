(*---------------------------------------------------------------------------
       Some proof automation, which moreover has few theory
       dependencies, and so can be used in places where bossLib
       is overkill.
 ---------------------------------------------------------------------------*)

structure BasicProvers :> BasicProvers =
struct

type simpset = simpLib.simpset;

open HolKernel boolLib markerLib;

val op++ = simpLib.++;
val op&& = simpLib.&&;

val ERR = mk_HOL_ERR "BasicProvers";

local val EXPAND_COND_CONV =
           simpLib.SIMP_CONV (pureSimps.pure_ss ++ boolSimps.COND_elim_ss) []
      val EXPAND_COND_TAC = CONV_TAC EXPAND_COND_CONV
      val EXPAND_COND = CONV_RULE EXPAND_COND_CONV
      val NORM_RULE = CONV_RULE (EXPAND_COND_CONV THENC
                                 REWRITE_CONV [markerTheory.Abbrev_def])
in
fun PROVE thl tm = Tactical.prove (tm,
  EXPAND_COND_TAC THEN mesonLib.MESON_TAC (map NORM_RULE thl))

fun PROVE_TAC thl (asl, w) = let
  val working = LLABEL_RESOLVE thl asl
in
  EXPAND_COND_TAC THEN CONV_TAC (DEST_LABELS_CONV) THEN
  mesonLib.MESON_TAC (map NORM_RULE working)
end (asl, w)

fun GEN_PROVE_TAC x y z thl (asl, w) = let
  val working = LLABEL_RESOLVE thl asl
in
  EXPAND_COND_TAC THEN CONV_TAC (DEST_LABELS_CONV) THEN
  mesonLib.GEN_MESON_TAC x y z (map NORM_RULE working)
end (asl, w)

end; (* local *)


(*---------------------------------------------------------------------------*
 * When invoked, we know that th is an equality, at least one side of which  *
 * is a variable.                                                            *
 *---------------------------------------------------------------------------*)

fun is_bool_atom tm =
  is_var tm andalso (type_of tm = bool)
  orelse is_neg tm andalso is_var (dest_neg tm);


fun orient th =
 let val c = concl th
 in if is_bool_atom c
    then (if is_neg c then EQF_INTRO th else EQT_INTRO th)
    else let val (lhs,rhs) = dest_eq c
         in if is_var lhs
            then if is_var rhs
                 then case Term.compare (lhs, rhs)
                       of LESS  => SYM th
                        | other => th
                 else th
            else SYM th
         end
 end;

fun VSUBST_TAC tm = UNDISCH_THEN tm (SUBST_ALL_TAC o orient);

fun var_eq tm =
   let val (lhs,rhs) = dest_eq tm
   in
       aconv lhs rhs
     orelse
       (is_var lhs andalso not (free_in lhs rhs))
     orelse
       (is_var rhs andalso not (free_in rhs lhs))
   end
   handle HOL_ERR _ => is_bool_atom tm


fun grab P f v =
  let fun grb [] = v
        | grb (h::t) = if P h then f h else grb t
  in grb
  end;

fun ASSUM_TAC f P = W (fn (asl,_) => grab P f NO_TAC asl)

val VAR_EQ_TAC = ASSUM_TAC VSUBST_TAC var_eq;

fun ASSUMS_TAC f P = W (fn (asl,_) =>
  case filter P asl
   of []     => NO_TAC
    | assums => MAP_EVERY f (List.rev assums));

fun CONCL_TAC f P = W (fn (_,c) => if P c then f else NO_TAC);

fun LIFT_SIMP ss tm =
  UNDISCH_THEN tm (STRIP_ASSUME_TAC o simpLib.SIMP_RULE ss []);

local
  fun DTHEN ttac = fn (asl,w) =>
   let val (ant,conseq) = dest_imp_only w
       val (gl,prf) = ttac (ASSUME ant) (asl,conseq)
   in (gl, Thm.DISCH ant o prf)
   end
in
val BOSS_STRIP_TAC = Tactical.FIRST [GEN_TAC,CONJ_TAC, DTHEN STRIP_ASSUME_TAC]
end;

fun tyi_to_ssdata tyinfo =
 let open simpLib
  val (thy,tyop) = TypeBasePure.ty_name_of tyinfo
  val {rewrs, convs} = TypeBasePure.simpls_of tyinfo;
in
  SSFRAG {name = SOME("Datatype "^thy^"$"^tyop),
          convs = convs, rewrs = rewrs, filter = NONE,
           dprocs = [], ac = [], congs = []}
end

fun add_simpls tyinfo ss = (ss ++ tyi_to_ssdata tyinfo) handle HOL_ERR _ => ss;

fun is_dneg tm = 1 < snd(strip_neg tm);

val notT = mk_neg T
val notF = mk_neg F;

fun breakable tm =
    is_exists tm orelse
    is_conj tm   orelse
    is_disj tm   orelse
    is_dneg tm   orelse
    notT = tm    orelse
    notF = tm    orelse
    T=tm orelse F=tm

(* ----------------------------------------------------------------------
    LET_ELIM_TAC

    eliminates lets by pulling them up, turning them into universal
    quantifiers, and eventually moving new abbreviations into the
    assumption list.
   ---------------------------------------------------------------------- *)

val let_movement_thms = let
  open combinTheory
in
  ref [o_THM, o_ABS_R, C_ABS_L, C_THM,
       GEN_literal_case_RAND, GEN_literal_case_RATOR,
       GEN_LET_RAND, GEN_LET_RATOR, S_ABS_R]
end

val IMP_CONG' = REWRITE_RULE [GSYM AND_IMP_INTRO] (SPEC_ALL IMP_CONG)

fun ABBREV_CONV tm = let
  val t = rand tm
  val (l,r) = dest_eq t
in
  if not (is_var l) orelse is_var r then
    REWR_CONV markerTheory.Abbrev_def THENC
    REWR_CONV EQ_SYM_EQ
  else ALL_CONV
end tm

val ABBREV_ss =
    simpLib.SSFRAG {name=SOME"ABBREV",
                    ac = [], congs = [],
                      convs = [{conv = K (K ABBREV_CONV),
                                key = SOME ([], ``marker$Abbrev x``),
                                trace = 2, name = "ABBREV_CONV"}],
                      dprocs = [], filter = NONE, rewrs = []}

(*---------------------------------------------------------------------------*)
(* The staging of first two successive calls to SIMP_CONV ensure that the    *)
(* LET_FORALL_ELIM theorem is applied after all the movement is possible.    *)
(*---------------------------------------------------------------------------*)

fun LET_ELIM_TAC goal =
 let open simpLib pureSimps boolSimps
 in
  CONV_TAC
    (QCHANGED_CONV
       (SIMP_CONV pure_ss (!let_movement_thms) THENC
        SIMP_CONV pure_ss (combinTheory.LET_FORALL_ELIM ::
                           combinTheory.literal_case_FORALL_ELIM ::
                           !let_movement_thms) THENC
        SIMP_CONV (pure_ss ++ ABBREV_ss ++ UNWIND_ss) [Cong IMP_CONG'])) THEN
  REPEAT BOSS_STRIP_TAC THEN markerLib.REABBREV_TAC
 end goal

fun new_let_thms thl = let_movement_thms := thl @ !let_movement_thms


(*---------------------------------------------------------------------------
      STP_TAC (Simplify then Prove)

   The following is a straightforward but quite helpful simplification
   procedure. It treats the rewrite rules for all declared datatypes as
   being built-in, so that the user does not have to mention them.

   0. Build a simpset from the given ss and the rewrites coming from
      any constructors that are found in TypeBase.

   1. Remove all universal quantifiers and break down all conjunctions

   2. Eliminate all "var-equalities" from the assumptions

   3. Simplify the goal with respect to the assumptions and the given
      simplification set.

   4. Case split on conditionals as much as possible.

   5. Strip as much as possible to the assumptions.

   6. Until there is no change in the complete goal, attempt to do one
      of the following:

         * eliminate a var-equality

         * break up an equation between constructors in the assumptions

         * break up an equation between constructors in the goal

         * break up conjunctions, disjunctions, existentials, or
           double negations occurring in the assumptions

         * eliminate occurrences of T (toss it away) and F (prove the goal)
           in the assumptions

         * eliminate lets in the goal, by lifting into the assumptions as
           abbreviations (using LET_ELIM_TAC)

    7. Apply the finishing tactic.

 ---------------------------------------------------------------------------*)

fun tyinfol() = TypeBasePure.listItems (TypeBase.theTypeBase());

fun mkCSET () =
 let val CSET =
         ref (HOLset.empty (inv_img_cmp (fn {Thy,Name,Ty} =>(Thy,Name))
                                        (pair_compare(String.compare,
                                                      String.compare))))
     fun inCSET t = HOLset.member(!CSET, dest_thy_const t)
     fun addCSET c = (CSET := HOLset.add(!CSET, dest_thy_const c))
     val _ = List.app
               (List.app addCSET o TypeBasePure.constructors_of) (tyinfol())
     fun constructed tm =
      let val (lhs,rhs) = dest_eq tm
      in aconv lhs rhs orelse
         let val maybe1 = fst(strip_comb lhs)
             val maybe2 = fst(strip_comb rhs)
         in is_const maybe1 andalso is_const maybe2
            andalso
            inCSET maybe1 andalso inCSET maybe2
         end
      end handle HOL_ERR _ => false
  in
    Lib.can (find_term constructed)
 end;

val leave_lets_var = mk_var("__leave_lets_alone__", bool)
val LEAVE_LETS = ASSUME leave_lets_var

fun PRIM_STP_TAC ss finisher =
 let val has_constr_eqn = mkCSET ()
     val ASM_SIMP = simpLib.ASM_SIMP_TAC ss []
     (* we don't have access to any theorem list that might have been passed
        to RW_TAC or SRW_TAC at this point, but we can look for the effect of
        the LEAVE_LETS theorem by attempting to rewrite something that only it
        should affect; if the simplifier doesn't change the leave_lets_var,
        then LEAVE_LETS is not part of the ss, so we should do LET_ELIM_TAC,
        otherwise, we shouldn't.

        Also, if there are no lets about then
        don't attempt LET_ELIM_TAC at all.  This is because LET_ELIM_TAC
        includes rewrites like |- f o (\x. g x) = \x. f (g x) and these
        can alter goals that don't have any lets in them at all, possibly
        against user expectations.  A less sledge-hammer implementation of
        LET_ELIM_TAC might not have this problem... *)
     val do_lets = (simpLib.SIMP_CONV ss [] leave_lets_var ; false)
                   handle Conv.UNCHANGED => true
     val LET_ELIM_TAC =
        if do_lets then
          (fn g as (_,w) =>
                if can (find_term is_let) w
                   then LET_ELIM_TAC g
                   else NO_TAC g)
        else NO_TAC
  in
    REPEAT (GEN_TAC ORELSE CONJ_TAC)
     THEN REPEAT VAR_EQ_TAC
     THEN ASM_SIMP
     THEN TRY (IF_CASES_TAC THEN REPEAT IF_CASES_TAC THEN ASM_SIMP)
     THEN REPEAT BOSS_STRIP_TAC
     THEN REPEAT (CHANGED_TAC
            (VAR_EQ_TAC
               ORELSE ASSUMS_TAC (LIFT_SIMP ss) has_constr_eqn
               ORELSE ASSUM_TAC (LIFT_SIMP ss) breakable
               ORELSE CONCL_TAC ASM_SIMP has_constr_eqn
               ORELSE LET_ELIM_TAC))
     THEN TRY finisher
  end

(*---------------------------------------------------------------------------
    PRIM_NORM_TAC: preliminary attempt at keeping the goal in a
    fully constructor-reduced format. The idea is that there should
    be no equations between constructor terms anywhere in the goal.
    (This is what PRIM_STP_TAC already does.)

    Also, no conditionals should occur in the resulting goal.
    This seems to be an expensive test, especially since the work
    in detecting the conditional is replicated in IF_CASES_TAC.

    Continuing in this light, it seems possible to eliminate all
    case expressions in the goal, but that hasn't been implemented yet.
 ---------------------------------------------------------------------------*)

fun splittable w =
 Lib.can (find_term (fn tm => is_cond tm andalso free_in tm w)) w;

fun LIFT_SPLIT_SIMP ss simp tm =
   UNDISCH_THEN tm
     (fn th => MP_TAC (simpLib.SIMP_RULE ss [] th)
                 THEN IF_CASES_TAC
                 THEN simp
                 THEN REPEAT BOSS_STRIP_TAC);

fun SPLIT_SIMP simp = TRY IF_CASES_TAC THEN simp ;

fun PRIM_NORM_TAC ss =
 let val has_constr_eqn = mkCSET()
     val ASM_SIMP = simpLib.ASM_SIMP_TAC ss []
  in
    REPEAT (GEN_TAC ORELSE CONJ_TAC)
     THEN REPEAT VAR_EQ_TAC
     THEN ASM_SIMP
     THEN TRY (IF_CASES_TAC THEN REPEAT IF_CASES_TAC THEN ASM_SIMP)
     THEN REPEAT BOSS_STRIP_TAC
     THEN REPEAT (CHANGED_TAC
            (VAR_EQ_TAC
               ORELSE ASSUMS_TAC (LIFT_SIMP ss) has_constr_eqn
               ORELSE ASSUM_TAC (LIFT_SIMP ss) breakable
               ORELSE CONCL_TAC ASM_SIMP has_constr_eqn
               ORELSE ASSUM_TAC (LIFT_SPLIT_SIMP ss ASM_SIMP) splittable
               ORELSE CONCL_TAC (SPLIT_SIMP ASM_SIMP) splittable
               ORELSE LET_ELIM_TAC))
  end


(*---------------------------------------------------------------------------
    Adding simplification sets in for all datatypes each time
    STP_TAC is invoked can be slow. In such cases, use
    PRIM_STP tac instead.
 ---------------------------------------------------------------------------*)

fun STP_TAC ss finisher
  = PRIM_STP_TAC (rev_itlist add_simpls (tyinfol()) ss) finisher

fun RW_TAC ss thl g = markerLib.ABBRS_THEN
                          (fn thl => STP_TAC (ss && thl) NO_TAC) thl
                          g

fun NORM_TAC ss thl g =
    markerLib.ABBRS_THEN
      (fn thl => PRIM_NORM_TAC (rev_itlist add_simpls (tyinfol()) (ss && thl)))
      thl
      g

val bool_ss = boolSimps.bool_ss;

(*---------------------------------------------------------------------------
       Stateful version of RW_TAC: doesn't load the constructor
       simplifications into the simpset at each invocation, but
       just when a datatype is declared.
 ---------------------------------------------------------------------------*)

val (srw_ss : simpset ref) = ref (bool_ss ++ combinSimps.COMBIN_ss);

val srw_ss_initialised = ref false;

val pending_updates = ref ([]: simpLib.ssfrag list);

fun initialise_srw_ss() =
  if !srw_ss_initialised then !srw_ss
  else let in
     HOL_PROGRESS_MESG ("Initialising SRW simpset ... ", "done")
     (fn () =>
         (srw_ss := rev_itlist add_simpls (tyinfol()) (!srw_ss) ;
          srw_ss := foldl (fn (ssd,ss) => ss ++ ssd) (!srw_ss)
                          (!pending_updates) ;
          srw_ss_initialised := true)) () ;
     !srw_ss
  end;

fun augment_srw_ss ssdl =
    if !srw_ss_initialised then
      srw_ss := foldl (fn (ssd,ss) => ss ++ ssd) (!srw_ss) ssdl
    else
      pending_updates := !pending_updates @ ssdl;

fun update_fn tyi =
  augment_srw_ss ([tyi_to_ssdata tyi] handle HOL_ERR _ => [])

val () =
  TypeBase.register_update_fn (fn tyinfos => (app update_fn tyinfos; tyinfos))

fun srw_ss () = initialise_srw_ss();

fun SRW_TAC ssdl thl g = let
  val ss = foldl (fn (ssd, ss) => ss ++ ssd) (srw_ss()) ssdl
in
  markerLib.ABBRS_THEN (fn thl => PRIM_STP_TAC (ss && thl) NO_TAC) thl
end g;

val Abbr = markerSyntax.Abbr

(*---------------------------------------------------------------------------
       Make some additions to the srw_ss persistent
 ---------------------------------------------------------------------------*)

val exports = ref ([] : string list)

fun setup_exports (oldname, thyname) = let
  val rwts_name = thyname ^ "_rwts"
  fun print_sig pps =
      if not (null (!exports)) then
        Portable.add_string pps ("val "^rwts_name^" : simpLib.ssfrag")
      else ()
  fun print_export pps =
      if not (null (!exports)) then let
          open Portable
          val {add_string, add_break, begin_block, end_block,add_newline,...} =
              with_ppstream pps
        in
          add_string ("val "^rwts_name^" = simpLib.named_rewrites "
                           ^Lib.quote rwts_name^" [");
          add_break(0,10);
          begin_block INCONSISTENT 0;
          pr_list add_string (fn () => add_string ",")
                  (fn () => add_break(1,0)) (!exports);
          end_block();
          add_string "];";
          add_newline();
          add_string ("val _ = BasicProvers.augment_srw_ss ["^rwts_name^"]\n")
        end
      else ()
in
  if not (null (!exports)) andalso thyname <> oldname then
    HOL_WARNING "BasicProvers" "setup_exports"
                ("\"new_theory\" is throwing away rewrite exports for "^
                 "theory "^Lib.quote oldname)
  else ();
  exports := [];
  adjoin_to_theory {sig_ps = SOME print_sig, struct_ps = SOME print_export}
end

val _ = Theory.after_new_theory setup_exports

fun export_rewrites slist = let
in
  exports := !exports @ slist;
  augment_srw_ss [simpLib.named_rewrites (current_theory())
                                         (map (DB.fetch "-") slist)]
end

end
