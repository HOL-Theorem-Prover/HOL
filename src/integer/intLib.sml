structure intLib :> intLib =
struct

open HolKernel boolLib bossLib liteLib;

open integerTheory intSimps Omega Cooper intSyntax intReduce Canon hurdUtils
     mesonLib tautLib integerRingLib;

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars integer_grammars
end

open Parse;

val ERR = mk_HOL_ERR "intLib";
fun failwith function = raise (ERR function "");

val operators = [("+", intSyntax.plus_tm),
                   ("-", intSyntax.minus_tm),
                   ("~", intSyntax.negate_tm),
                   ("numeric_negate", intSyntax.negate_tm),
                   ("*", intSyntax.mult_tm),
                   ("/", intSyntax.div_tm),
                   ("<", intSyntax.less_tm),
                   ("<=", intSyntax.leq_tm),
                   (">", intSyntax.greater_tm),
                   (">=", intSyntax.geq_tm),
                   ("**", intSyntax.exp_tm),
                   (GrammarSpecials.fromNum_str, intSyntax.int_injection),
                   (GrammarSpecials.num_injection, intSyntax.int_injection)];

fun deprecate_int () = let
  fun doit (s, t) =
     let val {Name,Thy,...} = dest_thy_const t in
        Parse.temp_send_to_back_overload s {Name = Name, Thy = Thy}
     end
in
  List.app doit operators
end

fun prefer_int () = let
  fun doit (s, t) =
     let val {Name,Thy,...} = dest_thy_const t in
        Parse.temp_bring_to_front_overload s {Name = Name, Thy = Thy}
     end
in
  List.app doit operators
end

val ARITH_CONV = Omega.OMEGA_CONV
val ARITH_TAC = Omega.OMEGA_TAC
val ARITH_PROVE = Omega.OMEGA_PROVE

(* ------------------------------------------------------------------------- *)
(* A tactic for simple divisibility/congruence/coprimality goals.            *)
(* ------------------------------------------------------------------------- *)

local
  val INT_POLYEQ_CONV =
      GEN_REWRITE_CONV I empty_rewrites[GSYM INT_SUB_0] THENC
      LAND_CONV INT_POLY_CONV;
  val INT_ARITH = OMEGA_PROVE;
  val pth = INT_ARITH “!a x. a = &0 <=> x = x + a :int”;
  fun is_defined v t =
    let val mons = HOLset.addList (empty_tmset,striplist(dest_binop "int_add") t)
    in
        HOLset.member(mons,v) andalso
        forall (fn m => v ~~ m orelse not(free_in v m)) (HOLset.listItems mons)
    end;
  fun ISOLATE_VARIABLE vars tm =
    let val th = INT_POLYEQ_CONV tm
        and th' = (SYM_CONV THENC INT_POLYEQ_CONV) tm;
        val (v,th1) =
            (case (List.find (fn v => is_defined v (lhand(rand(concl th)))) vars) of
               SOME v => (v,th')
             | NONE   =>
               case (List.find (fn v => is_defined v (lhand(rand(concl th')))) vars) of
                 SOME v => (v,th)
               | NONE   => failwith "ISOLATE_VARIABLE failed");
        val th2 = TRANS th1 (SPECL [lhs(rand(concl th1)), v] pth)
    in
        CONV_RULE(RAND_CONV(RAND_CONV INT_POLY_CONV)) th2
    end;
  fun subtract' tms tm =
      List.filter (fn t => not(t ~~ tm)) tms;
  fun UNWIND_POLYS_CONV tm = let
    val (vars,bod) = strip_exists tm;
    val cjs = conjuncts bod;
    val th1 = tryfind (ISOLATE_VARIABLE vars) cjs;
    val eq = lhand(concl th1);
    val bod' = list_mk_conj(eq::(subtract' cjs eq)); (* eq is moved in front of cjs *)
    val th2 = CONJ_ACI_RULE(mk_eq(bod,bod'));
    val th3 = TRANS th2 (MK_CONJ th1 (REFL(rand(rand(concl th2)))));
    val v = lhs(lhand(rand(concl th3)));
    val vars' = (subtract' vars v) @ [v]; (* v is moved to the end of vars *)
    fun MK_EXISTS t th = LIST_MK_EXISTS [t] th;
    val th4 = CONV_RULE(RAND_CONV(REWR_CONV UNWIND_THM2)) (MK_EXISTS v th3);
    fun IMP_RULE v v' =
        DISCH_ALL(itlist SIMPLE_CHOOSE v (itlist SIMPLE_EXISTS v' (ASSUME bod)));
    val th5 = IMP_ANTISYM_RULE (IMP_RULE vars vars') (IMP_RULE vars' vars)
  in
    TRANS th5 (itlist MK_EXISTS (subtract' vars v) th4)
  end;
  val isolate_monomials = let
    val mul_tm = mult_tm and add_tm = plus_tm
    and neg_tm = negate_tm;
    val dest_mul = liteLib.dest_binop mult_tm
    and dest_add = liteLib.dest_binop add_tm
    and mk_mul = curry (mk_binop mult_tm)
    and mk_add = curry (mk_binop add_tm);
    fun scrub_var v m =
      let val ps = striplist dest_mul m;
          val ps' = subtract' ps v
      in
         if null ps' then one_tm else end_itlist mk_mul ps'
      end;
    fun find_multipliers v mons =
      let val mons1 = List.filter (fn m => free_in v m) mons;
          val mons2 = map (scrub_var v) mons1
      in
         if null mons2 then zero_tm else end_itlist mk_add mons2
      end;
    fun disjoint tms1 tms2 =
      HOLset.isEmpty(HOLset.intersection(HOLset.addList(empty_tmset,tms1),
                                         HOLset.addList(empty_tmset,tms2)));
  in
    fn vars => fn tm =>
      let val (cmons,vmons) =
              partition (fn m => disjoint (free_vars m) vars)
                        (striplist dest_add tm);
          val cofactors = map (fn v => find_multipliers v vmons) vars
          and cnc = if null cmons then zero_tm
                    else mk_comb(neg_tm,end_itlist mk_add cmons)
      in
        (cofactors,cnc)
      end
  end;
  fun isolate_variables evs ps eq =
    let val vars = List.filter (fn v => free_in v eq) evs;
        val (qs,p) = isolate_monomials vars eq;
        val rs = List.filter (fn t => type_of t = int_ty) (qs @ ps);
        val rs = int_ideal_cofactors rs p;
    in
      (eq,zip (fst(chop_list(length qs) rs)) vars)
    end;
  fun subst_in_poly i p =
      let val i' = map (fn s => snd s |-> fst s) i in
        rhs(concl(INT_POLY_CONV (subst i' p)))
      end;
  fun subtract2 tms1 tms2 = 
      HOLset.listItems(HOLset.difference(HOLset.addList(empty_tmset,tms1),
                                         HOLset.addList(empty_tmset,tms2)));
  fun solve_idealism evs ps eqs =
    if null evs then [] else
    let val (eq,cfs) = tryfind (isolate_variables evs ps) eqs;
        val evs' = subtract2 evs (map snd cfs)
        and eqs' = map (subst_in_poly cfs) (subtract' eqs eq)
    in
        cfs @ solve_idealism evs' ps eqs'
    end;
  fun GENVAR_EXISTS_CONV tm =
    if not(is_exists tm) then REFL tm else
    let val (ev,bod) = dest_exists tm;
        val gv = genvar(type_of ev)
    in
       (GEN_ALPHA_CONV gv THENC BINDER_CONV GENVAR_EXISTS_CONV) tm
    end;
  fun check p x = if p x then x else failwith "check in EXISTS_POLY_TAC";
  fun rev_assocd item = (* modified from Lib.rev_assoc *)
   let
      fun assc ((ob, key) :: rst) d = if item ~~ key then ob else assc rst d
        | assc [] d = d
   in
      assc
   end;
  fun EXISTS_POLY_TAC (gl as (asl,w) :goal) =
    let val (evs,bod) = strip_exists w;
        (* NOTE: In HOL4, the type of goal is (term list * term), while in
                 HOL-Light it's (string * thm) list * term *)
        val ps = mapfilter (check (fn t => type_of t = int_ty) o
                           lhs (* o concl o snd *)) asl;
        val cfs = solve_idealism evs ps (map lhs (conjuncts bod))
    in
       (MAP_EVERY EXISTS_TAC(map (fn v => rev_assocd v cfs zero_tm) evs) THEN
        REPEAT(POP_ASSUM MP_TAC) THEN
     (* NOTE: EQT_INTRO must be added in HOL4 to make INT_RING conv-like *)
        CONV_TAC (EQT_INTRO o INT_RING)) gl
    end;
  val SCRUB_NEQ_TAC = MATCH_MP_TAC o MATCH_MP (MESON[]
     “~(x = y) ==> x = y \/ p ==> p”);
  (* |- !P Q. P /\ (?x. Q x) <=> ?x. P /\ Q x *)
  val RIGHT_AND_EXISTS_THM = GSYM RIGHT_EXISTS_AND_THM;
  (* |- !P Q. (?x. P x) /\ Q <=> ?x. P x /\ Q *)
  val LEFT_AND_EXISTS_THM = GSYM LEFT_EXISTS_AND_THM;
in
val INTEGER_TAC =
  (* NOTE: int_coprime and int_congruent are not available in HOL4's
           integerTheory, thus are not supported, for now. *)
  REWRITE_TAC[(* int_coprime, int_congruent *) int_divides] THEN
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM,
              LEFT_OR_EXISTS_THM, RIGHT_OR_EXISTS_THM] THEN
  CONV_TAC(REPEATC UNWIND_POLYS_CONV) THEN
  REPEAT(FIRST_X_ASSUM SCRUB_NEQ_TAC) THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM,
              LEFT_OR_EXISTS_THM, RIGHT_OR_EXISTS_THM] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POLYEQ_CONV) THEN
  REWRITE_TAC[GSYM INT_ENTIRE,
              TAUT `a \/ (b /\ c) <=> (a \/ b) /\ (a \/ c)`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REPEAT DISCH_TAC THEN CONV_TAC GENVAR_EXISTS_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POLYEQ_CONV) THEN EXISTS_POLY_TAC;

fun INTEGER_RULE tm = prove(tm,INTEGER_TAC);
end; (* local *)

val _ = if !Globals.interactive then
          Feedback.HOL_MESG ("intLib loaded.  Use intLib.deprecate_int()"^
                             " to turn off integer parsing")
        else ()

end;
