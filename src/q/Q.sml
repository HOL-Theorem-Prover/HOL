(*---------------------------------------------------------------------------
 * A bunch of functions that fold quotation parsing in, sometimes to good
 * effect.
 *---------------------------------------------------------------------------*)
structure Q :> Q =
struct

open HolKernel basicHol90Lib;
infix ORELSE THEN THENL |-> ## -->;

 type hol_type = Type.hol_type
 type fixity = Parse.fixity
 type term = Term.term
 type thm = Thm.thm
 type tactic = Abbrev.tactic
 type thm_tactic = Abbrev.thm_tactic
 type conv = Abbrev.conv
 type ('a,'b) subst = ('a,'b) Lib.subst
 type 'a quotation = 'a frag list


fun Q_ERR func mesg =
    HOL_ERR{origin_structure = "Q",
            origin_function = func, message = mesg};

val ptm = Parse.Term
val pty = Parse.Type;
fun normalise_quotation frags =
  case frags of
    [] => []
  | [x] => [x]
  | (QUOTE s1::QUOTE s2::rest) => normalise_quotation (QUOTE (s1^s2) :: rest)
  | x::xs => x :: normalise_quotation xs

fun ptm_with_ctxtty ctxt ty q = let
  val q' = QUOTE "(" :: (q @ [QUOTE "):", ANTIQUOTE(Term.ty_antiq ty),
                              QUOTE ""])
in
  Parse.parse_in_context ctxt (normalise_quotation q')
end


val ptm_with_ty = Parse.typedTerm;
fun btm q = ptm_with_ty q bool;

val mk_term_rsubst =
  map (fn {redex,residue} =>
          let val residue' = ptm residue
              val redex' = ptm_with_ty redex (type_of residue')
          in redex' |-> residue'
          end);

val mk_type_rsubst = map (fn {redex,residue} => (pty redex |-> pty residue));


(* The jrh abomination *)
local fun bval w t = (type_of t = bool)
             andalso (can (find_term is_var) t)
             andalso (free_in t w)
in
val TAUT_CONV =
  C (curry prove)
    (REPEAT GEN_TAC THEN (REPEAT o CHANGED_TAC o W)
      (C (curry op THEN) (Rewrite.REWRITE_TAC[])
                    o BOOL_CASES_TAC o Lib.trye hd
                    o sort free_in
                    o Lib.W (find_terms o bval) o snd))
  o btm
end;

fun store_thm(s,q,t) = Tactical.store_thm(s,btm q,t);
fun prove q t = Tactical.prove(btm q,t);
fun new_definition(s,q) = Const_def.new_definition(s,btm q);
fun new_infixl_definition(s,q,f) = Parse.new_infixl_definition(s,btm q,f);
fun new_infixr_definition(s,q,f) = Parse.new_infixr_definition(s,btm q,f);
fun define q s f = Parse.new_gen_definition(s, btm q, f)

val ABS = Thm.ABS o ptm;
val BETA_CONV = Thm.BETA_CONV o ptm;
val REFL = Thm.REFL o ptm;

fun DISJ1 th = Thm.DISJ1 th o btm;
val DISJ2 = Thm.DISJ2 o btm;


(* val GEN = Drule.GEN o ptm; *)
fun GEN [QUOTE s] th =
     let val V = free_vars (concl th)
     in
       case (Lib.assoc2 s (Lib.zip V (map (#Name o dest_var) V)))
         of NONE => raise Q_ERR "GEN" "variable not found"
          | (SOME (v,_)) => Thm.GEN v th
     end
  | GEN _ _ = raise Q_ERR "GEN" "unexpected quote format"

fun SPEC q =
    W(Thm.SPEC o ptm_with_ty q o (type_of o #Bvar o dest_forall o concl));

val SPECL = rev_itlist SPEC;
val ISPEC = Drule.ISPEC o ptm;
val ISPECL = Drule.ISPECL o map ptm;
val ID_SPEC = W(Thm.SPEC o (#Bvar o dest_forall o concl))


fun SPEC_TAC (q1,q2) (g as (asl,w)) = let
  val ctxt = free_varsl (w::asl)
  val T1 = Parse.parse_in_context ctxt q1
  val T2 = ptm_with_ctxtty ctxt (type_of T1) q2
in
  Tactic.SPEC_TAC(T1, T2) g
end;

(* Generalizes first free variable with given name to itself. *)

fun ID_SPEC_TAC q (g as (asl,w)) = let
  val ctxt = free_varsl (w::asl)
  val tm = Parse.parse_in_context ctxt q
in
  Tactic.SPEC_TAC (tm, tm) g
end

val EXISTS = Thm.EXISTS o (btm##btm);

fun EXISTS_TAC q (g as (asl, w)) = let
  val ctxt = free_varsl (w::asl)
  val exvartype = type_of (#Bvar (Rsyntax.dest_exists w))
in
  Tactic.EXISTS_TAC (ptm_with_ctxtty ctxt exvartype q) g
end
fun ID_EX_TAC(g as (_,w)) = Tactic.EXISTS_TAC (#Bvar(Dsyntax.dest_exists w)) g;

fun X_CHOOSE_THEN q ttac thm (g as (asl,w))= let
  val ty = type_of (#Bvar (dest_exists (concl thm)))
  val ctxt = free_varsl (w::asl)
in
  Thm_cont.X_CHOOSE_THEN (ptm_with_ctxtty ctxt ty q) ttac thm g
end
val X_CHOOSE_TAC = C X_CHOOSE_THEN Tactic.ASSUME_TAC;

val DISCH = Thm.DISCH o btm;
val PAT_UNDISCH_TAC = fn q =>
     W(Tactic.UNDISCH_TAC o first (can (Term.match_term (ptm q))) o fst);
fun UNDISCH_THEN q ttac = PAT_UNDISCH_TAC q THEN DISCH_THEN ttac;
fun PAT_ASSUM q ttac = Ho_tactics.PAT_ASSUM (ptm q) ttac;
val UNDISCH_TAC = Tactic.UNDISCH_TAC o btm;

fun SUBGOAL_THEN q ttac (g as (asl,w)) = let
  val ctxt = free_varsl (w::asl)
in
  Tactical.SUBGOAL_THEN (ptm_with_ctxtty ctxt Type.bool q) ttac g
end
val ASSUME = ASSUME o btm

fun X_GEN_TAC q (g as (asl, w)) = let
  val ctxt = free_varsl (w::asl)
  val ty = type_of (#Bvar (dest_forall w))
in
  Tactic.X_GEN_TAC (ptm_with_ctxtty ctxt ty q) g
end

fun X_FUN_EQ_CONV q tm = let
  val ctxt = free_vars tm
  val ty = #1 (dom_rng (type_of (lhs tm)))
in
  Conv.X_FUN_EQ_CONV (ptm_with_ctxtty ctxt ty q) tm
end

val list_mk_type = itlist (curry(op -->));

fun skolem_ty tm =
 let val (V,tm') = Dsyntax.strip_forall tm
 in if V<>[]
    then list_mk_type (map type_of V) (type_of(#Bvar(dest_exists tm')))
    else raise Q_ERR"XSKOLEM_CONV" "no universal prefix"
  end;

fun X_SKOLEM_CONV q tm = let
  val ctxt = free_vars tm
  val ty = skolem_ty tm
in
  Conv.X_SKOLEM_CONV (ptm_with_ctxtty ctxt ty q) tm
end

fun AP_TERM (q as [QUOTE s]) th =
     (let val {const,...} = Term.const_decl s
          val pat = Lib.trye hd (#Args(Type.dest_type(Term.type_of const)))
          val ty = Term.type_of (#lhs(Dsyntax.dest_eq (Thm.concl th)))
          val theta = Type.match_type pat ty
      in
        Thm.AP_TERM (Term.inst theta const) th
      end
      handle HOL_ERR _ => Thm.AP_TERM(ptm q) th)
  | AP_TERM q th = Thm.AP_TERM (ptm q) th

fun AP_THM th q = let
  val {lhs,rhs} = dest_eq(concl th)
  val ty = fst (dom_rng (type_of lhs))
  val ctxt = free_vars (concl th)
in
  Thm.AP_THM th (ptm_with_ctxtty ctxt ty q)
end;

fun ASM_CASES_TAC q (g as (asl,w)) = let
  val ctxt = free_varsl (w::asl)
  val ty = Type.bool
in
  Tactic.ASM_CASES_TAC (ptm_with_ctxtty ctxt ty q) g
end
fun AC_CONV p = Conv.AC_CONV p o ptm;

(* Could be smarter *)
val INST = Thm.INST o mk_term_rsubst;
val INST_TYPE = Thm.INST_TYPE o mk_type_rsubst;


(*---------------------------------------------------------------------------
 * A couple from jrh.
 *---------------------------------------------------------------------------*)
fun ABBREV_TAC q (g as (asl,w)) = let
  val ctxt = free_varsl(w::asl)
  val {lhs,rhs} = Dsyntax.dest_eq (Parse.parse_in_context ctxt q)
in
  CHOOSE_THEN (fn th => SUBST_ALL_TAC th THEN ASSUME_TAC th)
  (Thm.EXISTS (mk_exists{Bvar=lhs,Body=mk_eq{lhs=rhs,rhs=lhs}},rhs)
   (Thm.REFL rhs))
  g
end;

fun UNABBREV_TAC [QUOTE s] =
        FIRST_ASSUM(SUBST1_TAC o SYM o
             assert(curry op = s o #Name o dest_var o rhs o concl))
         THEN BETA_TAC
  | UNABBREV_TAC _ = raise Q_ERR "UNABBREV_TAC" "unexpected quote format"

end; (* Q *)
