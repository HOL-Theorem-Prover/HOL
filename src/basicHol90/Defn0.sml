structure Defn0 :> Defn0 = 
struct

open HolKernel Drule Conv;

type hol_type     = Type.hol_type
type term         = Term.term
type thm          = Thm.thm
type conv         = Abbrev.conv
type tactic       = Abbrev.tactic

infixr 3 -->;
infix 3 |->;
infix 4 ##; 

fun ERR func mesg = HOL_ERR{origin_structure = "Defn0", 
                            origin_function = func, message = mesg};

(*---------------------------------------------------------------------------
    The type of definitions. This is an attempt to gather all the 
    information about a definition in one place.
 ---------------------------------------------------------------------------*)

datatype defn
   = NONREC  of {eqs:thm, ind: thm option}
   | PRIMREC of {eqs:thm, ind:thm}
   | STDREC  of {eqs:thm, ind:thm, R:term, SV:term list}
   | NESTREC of {eqs:thm, ind:thm, R:term, SV:term list,aux:defn}
   | MUTREC  of {eqs:thm, ind:thm, R:term, SV:term list,union:defn};

fun is_nonrec  (NONREC _)  = true | is_nonrec _  = false;
fun is_primrec (PRIMREC _) = true | is_primrec _ = false;
fun is_nestrec (NESTREC _) = true | is_nestrec _ = false;
fun is_mutrec  (MUTREC _)  = true | is_mutrec _  = false;

fun eqns_of (NONREC  {eqs, ...}) = eqs
  | eqns_of (PRIMREC {eqs, ...}) = eqs
  | eqns_of (STDREC  {eqs, ...}) = eqs
  | eqns_of (NESTREC {eqs, ...}) = eqs
  | eqns_of (MUTREC  {eqs, ...}) = eqs;

fun eqnl_of d = CONJUNCTS (eqns_of d)

fun aux_defn (NESTREC {aux, ...}) = SOME aux
  | aux_defn     _  = NONE;

fun union_defn (MUTREC {union, ...}) = SOME union
  | union_defn     _  = NONE;

fun ind_of (NONREC  {ind, ...}) = ind
  | ind_of (PRIMREC {ind, ...}) = SOME ind
  | ind_of (STDREC  {ind, ...}) = SOME ind
  | ind_of (NESTREC {ind, ...}) = SOME ind
  | ind_of (MUTREC  {ind, ...}) = SOME ind;


fun params_of (NONREC _)  = []
  | params_of (PRIMREC _) = []
  | params_of (STDREC  {SV, ...}) = SV
  | params_of (NESTREC {SV, ...}) = SV
  | params_of (MUTREC  {SV, ...}) = SV;

fun schematic defn = not(List.null (params_of defn));

fun tcs_of (NONREC _)  = []
  | tcs_of (PRIMREC _) = []
  | tcs_of (STDREC  {ind, ...}) = hyp ind
  | tcs_of (NESTREC {ind, ...}) = hyp ind  (* this is wrong! *)
  | tcs_of (MUTREC  {ind, ...}) = hyp ind;


fun reln_of (NONREC _)  = NONE
  | reln_of (PRIMREC _) = NONE
  | reln_of (STDREC  {R, ...}) = SOME R
  | reln_of (NESTREC {R, ...}) = SOME R
  | reln_of (MUTREC  {R, ...}) = SOME R;


fun nUNDISCH n th = if n<1 then th else nUNDISCH (n-1) (UNDISCH th)

fun INST_THM theta th =
  let val asl = hyp th
      val th1 = rev_itlist DISCH asl th
      val th2 = INST_TY_TERM theta th1
  in
   nUNDISCH (length asl) th2
  end;

fun isubst (tmtheta,tytheta) tm = subst tmtheta (inst tytheta tm);

fun inst_defn (STDREC{eqs,ind,R,SV}) theta =
      STDREC {eqs=INST_THM theta eqs,
              ind=INST_THM theta ind,
              R=isubst theta R,
              SV=map (isubst theta) SV}
  | inst_defn (NESTREC{eqs,ind,R,SV,aux}) theta =
      NESTREC {eqs=INST_THM theta eqs,
               ind=INST_THM theta ind,
               R=isubst theta R,
               SV=map (isubst theta) SV,
               aux=inst_defn aux theta}
  | inst_defn (MUTREC{eqs,ind,R,SV,union}) theta =
      MUTREC {eqs=INST_THM theta eqs,
              ind=INST_THM theta ind,
              R=isubst theta R,
              SV=map (isubst theta) SV,
              union=inst_defn union theta}
  | inst_defn (PRIMREC{eqs,ind}) theta =
      PRIMREC{eqs=INST_THM theta eqs,
              ind=INST_THM theta ind}
  | inst_defn (NONREC {eqs,ind=NONE}) theta = 
      NONREC {eqs=INST_THM theta eqs, ind=NONE}
  | inst_defn (NONREC {eqs,ind=SOME th}) theta = 
      NONREC {eqs=INST_THM theta eqs, ind=SOME(INST_THM theta th)}


fun set_reln def R =
   case reln_of def
    of NONE => def
     | SOME Rpat => inst_defn def (Term.match_term Rpat R);


fun PROVE_HYPL thl th =
  let val thm = itlist PROVE_HYP thl th
  in if null(hyp thm) then thm
     else raise ERR "PROVE_HYPL" "remaining termination conditions"
  end;


(* Should perhaps be extended to existential theorems. *)

fun elim_tcs (STDREC {eqs, ind, R, SV}) thms =
     STDREC{R=R, SV=SV,
            eqs=PROVE_HYPL thms eqs,
            ind=PROVE_HYPL thms ind}
  | elim_tcs (NESTREC {eqs, ind, R,  SV, aux}) thms =
     NESTREC{R=R, SV=SV,
            eqs=PROVE_HYPL thms eqs,
            ind=PROVE_HYPL thms ind,
            aux=elim_tcs aux thms}
  | elim_tcs (MUTREC {eqs, ind, R, SV, union}) thms =
     MUTREC{R=R, SV=SV,
            eqs=PROVE_HYPL thms eqs,
            ind=PROVE_HYPL thms ind,
            union=elim_tcs union thms}
  | elim_tcs x _ = x;


local fun isT M = (#Name(dest_const M) = "T") handle HOL_ERR _ => false
      val lem = let val M = mk_var{Name="M",Ty=Type.bool}
                    val M1 = mk_var{Name="M1",Ty=Type.bool}
                    val P = mk_var{Name="P",Ty=Type.bool}
                    val tm1 = mk_eq{lhs=M,rhs=M1}
                    val tm2 = mk_imp{ant=M,conseq=P}
                in DISCH tm1 (DISCH tm2 (SUBS [ASSUME tm1] (ASSUME tm2)))
                end
in
fun simp_assum conv tm th =
  let val th' = DISCH tm th
      val tmeq = conv tm
      val tm' = rhs(concl tmeq)
  in
    if isT tm' then MP th' (EQT_ELIM tmeq)
    else UNDISCH(MATCH_MP (MATCH_MP lem tmeq) th')
  end
end;

fun SIMP_HYPL conv th = itlist (simp_assum conv) (hyp th) th;

fun simp_tcs (STDREC {eqs, ind, R, SV}) conv =
     STDREC{R=rhs(concl(conv R)), SV=SV,
            eqs=SIMP_HYPL conv eqs,
            ind=SIMP_HYPL conv ind}
  | simp_tcs (NESTREC {eqs, ind, R,  SV, aux}) conv =
     NESTREC{R=rhs(concl(conv R)), SV=SV,
            eqs=SIMP_HYPL conv eqs,
            ind=SIMP_HYPL conv ind,
            aux=simp_tcs aux conv}
  | simp_tcs (MUTREC {eqs, ind, R, SV, union}) conv =
     MUTREC{R=rhs(concl(conv R)), SV=SV,
            eqs=SIMP_HYPL conv eqs,
            ind=SIMP_HYPL conv ind,
            union=simp_tcs union conv}
  | simp_tcs x _ = x;


fun TAC_HYPL tac th = 
  PROVE_HYPL (mapfilter (C (curry Tactical.prove) tac) (hyp th)) th;

fun prove_tcs (STDREC {eqs, ind, R, SV}) tac =
     STDREC{R=R, SV=SV,
            eqs=TAC_HYPL tac eqs,
            ind=TAC_HYPL tac ind}
  | prove_tcs (NESTREC {eqs, ind, R,  SV, aux}) tac =
     NESTREC{R=R, SV=SV,
            eqs=TAC_HYPL tac eqs,
            ind=TAC_HYPL tac ind,
            aux=prove_tcs aux tac}
  | prove_tcs (MUTREC {eqs, ind, R, SV, union}) tac =
     MUTREC{R=R, SV=SV,
            eqs=TAC_HYPL tac eqs,
            ind=TAC_HYPL tac ind,
            union=prove_tcs union tac}
  | prove_tcs x _ = x;



local open Portable
      fun kind (NONREC  _) = "non-recursive"
        | kind (STDREC  _) = "recursive"
        | kind (PRIMREC _) = "primitive recursion"
        | kind (NESTREC _) = "nested recursion"
        | kind (MUTREC  _) = "mutual recursion"
in
fun pp_defn ppstrm = 
 let val {add_string,add_break,
          begin_block,end_block,...} = with_ppstream ppstrm
     val pp_term = Parse.pp_term ppstrm
     val pp_thm  = Parse.pp_thm ppstrm
   fun pp (NONREC {eqs, ind}) = 
          (begin_block CONSISTENT 0;
           add_string "Equation(s) :"; 
           add_break(1,0);
           pp_thm eqs; 
           (case ind 
             of NONE => ()
              | SOME th => 
                 (add_newline ppstrm; add_newline ppstrm; 
                  add_string "Case analysis:"; 
                 add_break(1,0); pp_thm th));
           end_block())
     | pp (PRIMREC{eqs, ind}) = 
          (begin_block CONSISTENT 0;
           add_string "Equation(s) :"; 
           add_break(1,0);
           pp_thm eqs; end_block())
     | pp (STDREC {eqs, ind, R, SV}) = 
          (begin_block CONSISTENT 0;
           add_string "Equation(s) :"; 
           add_break(1,0);
           pp_thm eqs; add_newline ppstrm; add_newline ppstrm;
           add_string "Induction :"; 
           add_break(1,0);
           pp_thm ind; end_block())
     | pp (NESTREC{eqs, ind, R, SV, aux}) = 
          (begin_block CONSISTENT 0;
           add_string "Equation(s) :"; 
           add_break(1,0);
           pp_thm eqs; add_newline ppstrm; add_newline ppstrm;
           add_string "Induction :"; 
           add_break(1,0);
           pp_thm ind; end_block())
     | pp (MUTREC {eqs, ind, R, SV, union}) =
          (begin_block CONSISTENT 0;
           add_string "Equation(s) :"; 
           add_break(1,0);
           pp_thm eqs; add_newline ppstrm; add_newline ppstrm;
           add_string "Induction :"; 
           add_break(1,0);
           pp_thm ind; end_block())
 in
   fn d =>
       (begin_block CONSISTENT 0;
        add_string "HOL function definition "; 
        add_string (String.concat ["(",kind d,")"]);
        add_break(1,0);
        pp d;
        end_block())
 end
end;



local open boolTheory
      val non_datatype_context = ref [LET_CONG, COND_CONG]
in
  fun read_context() = !non_datatype_context
  fun write_context L = (non_datatype_context := L)
end;

end;
