(*---------------------------------------------------------------------------
 * A bunch of functions that fold quotation parsing in, sometimes to good
 * effect. 
 *---------------------------------------------------------------------------*)
structure Q :> Q =
struct

open HolKernel basicHol90Lib;
infix ORELSE THEN THENL |-> ## -->;

 type hol_type = Type.hol_type
 type fixity = Term.fixity
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
val ptm_with_ty = Parse.typedTerm
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
fun new_infix_definition(s,q,f) = Const_def.new_infix_definition(s,btm q,f);
fun define q s f = Const_def.new_gen_definition
                      {def = btm q, fixity = f, name = s};

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


fun same_const_name s tm = (s = #Name(dest_const tm)) handle _ => false;

fun assocName s =
   let fun assq [] = NONE
         | assq (v::rst) = 
            if (s = #Name(dest_var v)) then SOME v else assq rst
   in assq
   end;

(*---------------------------------------------------------------------------*
 * If q1 is a variable, then find free var occurrence with same name. Use    *
 * that to get the type with which to parse q2 (which has to be a variable). *
 * If it's not a var, then it might be a constant, and the same applies.     *
 * Otherwise it's a comb or an abs. Look for an exact (aconv) occurrence.    *
 * If there isn't one, look for a match.                                     *
 *---------------------------------------------------------------------------*)

fun SPEC_TAC (q1,q2) (g as (_,w)) = 
  let val N = ptm q1
      val N' = (case (dest_term N)
           of VAR {Name,...} => 
                (case (assocName Name (free_vars w))
                 of NONE => raise Q_ERR"SPEC_TAC" "variable not found"
                  | SOME v => v)
           | CONST{Name,...} => find_term (same_const_name Name) w
           | _ =>  find_term (aconv N) w 
                      handle HOL_ERR _ => find_term (Lib.can (match_term N)) w)
  in
    Tactic.SPEC_TAC(N', ptm_with_ty q2 (type_of N')) g
  end;

(* Generalizes first free variable with given name to itself. *)

fun ID_SPEC_TAC [QUOTE s] (g as (_,w)) =
     let val V = free_vars w
     in case (Lib.assoc2 s (Lib.zip V (map (#Name o dest_var) V)))
          of NONE => raise Q_ERR"ID_SPEC_TAC" "variable not found"
           | (SOME (v,_)) => Tactic.SPEC_TAC(v,v) g
     end
  | ID_SPEC_TAC _ _ = raise Q_ERR "ID_SPEC_TAC" "unexpected quote format"
   
val EXISTS = Thm.EXISTS o (btm##btm);

val EXISTS_TAC = fn q => 
  W(Tactic.EXISTS_TAC o ptm_with_ty q o (type_of o #Bvar o dest_exists o snd));

fun ID_EX_TAC(g as (_,w)) = Tactic.EXISTS_TAC (#Bvar(Dsyntax.dest_exists w)) g;

val X_CHOOSE_THEN = fn q => fn ttac =>
      W(C X_CHOOSE_THEN ttac o ptm_with_ty q 
                             o (type_of o #Bvar o dest_exists o concl));
val X_CHOOSE_TAC = C X_CHOOSE_THEN Tactic.ASSUME_TAC;

val DISCH = Thm.DISCH o btm;
val PAT_UNDISCH_TAC = fn q => 
     W(Tactic.UNDISCH_TAC o first (can (Term.match_term (ptm q))) o fst);
fun UNDISCH_THEN q ttac = PAT_UNDISCH_TAC q THEN DISCH_THEN ttac;
fun PAT_ASSUM q ttac = Tactical.PAT_ASSUM (ptm q) ttac;
val UNDISCH_TAC = Tactic.UNDISCH_TAC o btm;

(* val num_CONV = Num_conv.num_CONV o ptm *)

val SUBGOAL_THEN = Tactical.SUBGOAL_THEN o btm
val ASSUME = ASSUME o btm
val X_GEN_TAC = fn q =>
  W(Tactic.X_GEN_TAC o ptm_with_ty q o (type_of o #Bvar o dest_forall o snd))

fun X_FUN_EQ_CONV q =
 W(Conv.X_FUN_EQ_CONV o ptm_with_ty q 
                      o (Lib.trye hd o #Args o dest_type o type_of o lhs));

val list_mk_type = itlist (curry(op -->));

fun skolem_ty tm =
 let val (V,tm') = Dsyntax.strip_forall tm
 in if V<>[] 
    then list_mk_type (map type_of V) (type_of(#Bvar(dest_exists tm')))
    else raise Q_ERR"XSKOLEM_CONV" "no universal prefix"
  end;

fun X_SKOLEM_CONV q = W(Conv.X_SKOLEM_CONV o ptm_with_ty q o skolem_ty)

fun AP_TERM (q as [QUOTE s]) th = 
     (let val {const,...} = Term.const_decl s
          val pat = Lib.trye hd (#Args(Type.dest_type(Term.type_of const)))
          val ty = Term.type_of (#lhs(Dsyntax.dest_eq (Thm.concl th)))
          val theta = Type.match_type pat ty
      in 
        Thm.AP_TERM (Term.inst theta const) th
      end
      handle HOL_ERR _ => Thm.AP_TERM(ptm q) th)
  | AP_TERM _ _ = raise Q_ERR "AP_TERM" "unexpected quote format"


fun AP_THM th = 
   let val {lhs,rhs} = dest_eq(concl th)
       val ty = fst (dom_rng (type_of lhs))
   in 
     Thm.AP_THM th o (Lib.C ptm_with_ty ty)
   end;

val ASM_CASES_TAC = Tactic.ASM_CASES_TAC o btm
fun AC_CONV p = Conv.AC_CONV p o ptm;

(* Could be smarter *)
val INST = Thm.INST o mk_term_rsubst;
val INST_TYPE = Thm.INST_TYPE o mk_type_rsubst;


(*---------------------------------------------------------------------------
 * A couple from jrh.
 *---------------------------------------------------------------------------*)
fun ABBREV_TAC q =
  let val {lhs,rhs} = Dsyntax.dest_eq (ptm q)
  in CHOOSE_THEN (fn th => SUBST_ALL_TAC th THEN ASSUME_TAC th)
       (Thm.EXISTS (mk_exists{Bvar=lhs,Body=mk_eq{lhs=rhs,rhs=lhs}},rhs)
                     (Thm.REFL rhs))
  end;

fun UNABBREV_TAC [QUOTE s] = 
        FIRST_ASSUM(SUBST1_TAC o SYM o
             assert(curry op = s o #Name o dest_var o rhs o concl)) 
         THEN BETA_TAC
  | UNABBREV_TAC _ = raise Q_ERR "UNABBREV_TAC" "unexpected quote format"

end; (* Q *)
