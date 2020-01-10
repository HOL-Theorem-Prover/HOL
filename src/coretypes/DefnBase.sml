structure DefnBase :> DefnBase =
struct

open HolKernel boolTheory boolSyntax Drule Conv Rewrite

val ERR = mk_HOL_ERR "DefnBase";

(*---------------------------------------------------------------------------
    The type of definitions. This is an attempt to gather all the
    information about a definition in one place.
 ---------------------------------------------------------------------------*)

datatype defn
   = ABBREV  of {eqn:thm, bind:string}
   | PRIMREC of {eqs:thm, ind:thm, bind:string}
   | NONREC  of {eqs:thm, ind:thm, SV:term list, stem:string}
   | STDREC  of {eqs:thm list, ind:thm, R:term,SV:term list,stem:string}
   | MUTREC  of {eqs:thm list, ind:thm, R:term, SV:term list,
                 stem:string,union:defn}
   | NESTREC of {eqs:thm list, ind:thm, R:term, SV:term list,
                 stem:string, aux:defn}
   | TAILREC of {eqs:thm list, ind:thm, R:term, SV:term list, stem:string}

fun all_terms d =
  case d of
      ABBREV{eqn,...} => [concl eqn]
    | PRIMREC {eqs,ind,...} => [concl eqs, concl ind]
    | NONREC {eqs,ind,SV,...} => concl eqs::concl ind::SV
    | STDREC {eqs,ind,R,SV,...} => R :: concl ind :: map concl eqs @ SV
    | MUTREC {eqs,ind,R,SV,union,...} =>
        R :: concl ind :: map concl eqs @ SV @ all_terms union
    | NESTREC {eqs,ind,R,SV,aux,...} =>
        R :: concl ind :: map concl eqs @ SV @ all_terms aux
    | TAILREC {eqs,ind,R,SV,...} => R :: concl ind :: map concl eqs @ SV

local open Portable
      fun kind (ABBREV _)  = "abbreviation"
        | kind (NONREC  _) = "non-recursive"
        | kind (STDREC  _) = "recursive"
        | kind (PRIMREC _) = "primitive recursion"
        | kind (MUTREC  _) = "mutual recursion"
        | kind (NESTREC _) = "nested recursion"
        | kind (TAILREC _) = "nonterminating tail recursion"
      fun hyps thl = HOLset.listItems
                       (foldl (fn (th,s) => HOLset.union(hypset th, s))
                              empty_tmset thl)
in
fun pp_defn d =
  let open smpp
      val pp_term = lift Parse.pp_term
      val pp_thm  = lift Parse.pp_thm
      fun pp_rec (eqs,ind,tcs) =
        block CONSISTENT 0 (
          add_string "Equation(s) :" >>
          add_break(1,0) >>
          pr_list pp_thm add_newline eqs >>
          add_newline >> add_newline >>
          add_string "Induction :" >>
          add_break(1,0) >>
          pp_thm ind >>
          (if null tcs then nothing
           else
             (add_newline >> add_newline >>
              add_string "Termination conditions :" >>
              add_break(1,2) >>
              block CONSISTENT 0 (
                 pr_list (fn (n,tm) =>
                             block CONSISTENT 3 (
                               add_string (Lib.int_to_string n^". ") >>
                               pp_term tm
                             )
                         )
                         add_newline
                         (Lib.enumerate 0 tcs)
               ))
          )
        )
   fun pp (ABBREV {eqn, ...}) =
          block CONSISTENT 0 (
            add_string "Equation :" >>
            add_break(1,0) >>
            pp_thm eqn
          )
     | pp (PRIMREC{eqs, ind, bind}) =
          block CONSISTENT 0 (
            add_string "Equation(s) :" >>
            add_break(1,0) >>
            pp_thm eqs
          )
     | pp (NONREC {eqs, ind, SV, stem}) =
          block CONSISTENT 0 (
             add_string "Equation(s) :" >>
             add_break(1,0) >>
             pp_thm eqs >>
             add_newline >> add_newline >>
             add_string "Case analysis:" >>
             add_break(1,0) >> pp_thm ind
          )
     | pp (STDREC {eqs, ind, R, SV, stem})        = pp_rec(eqs,ind, hyps eqs)
     | pp (NESTREC{eqs, ind, R, SV, aux, stem})   = pp_rec(eqs,ind, hyps eqs)
     | pp (MUTREC {eqs, ind, R, SV, union, stem}) = pp_rec(eqs,ind, hyps eqs)
     | pp (TAILREC{eqs, ind, R, SV, stem})        = pp_rec(eqs,ind, hyps eqs)
   val m =
     block CONSISTENT 0 (
       add_string "HOL function definition " >>
       add_string (String.concat ["(",kind d,")"]) >>
       add_newline >> add_newline >>
       pp d
     )
  in
    Parse.mlower m
  end
end;


(*---------------------------------------------------------------------------
    Congruence rules for termination condition extraction. Before
    t.c. extraction is performed, the theorems in "non_datatype_congs"
    are added to the congruence rules arising from datatype definitions,
    which are held in the TypeBase.
 ---------------------------------------------------------------------------*)


local open boolTheory
      val non_datatype_congs =
        ref ([LET_CONG, COND_CONG, IMP_CONG, literal_case_CONG,
              pairTheory.LEX_CONG, pairTheory.PROD_ALL_CONG] @
             map (REWRITE_RULE [AND_IMP_INTRO])
                 [RES_FORALL_CONG, RES_EXISTS_CONG])
in
  fun read_congs() = !non_datatype_congs
  fun write_congs L = (non_datatype_congs := L)
end;

fun add_cong thm = write_congs (thm :: read_congs());

fun drop_cong c =
 let open boolSyntax
     val P = same_const c
     val (cong,rst) =
         pluck (fn th => P (fst(strip_comb(lhs(snd
                             (strip_imp(snd(strip_forall(concl th)))))))))
               (read_congs())
     val _ = write_congs rst
 in
   cong
 end
 handle e => raise wrap_exn "DefnBase.drop_cong"
    (case total dest_thy_const c
      of NONE => "expected a constant"
       | SOME{Thy,Name,...} =>
           ("congruence rule for "
            ^Lib.quote(Thy^"$"^Name)
            ^" was not found")) e;

val {export = export_cong,...} =
    ThmSetData.new_exporter {
      settype = "defncong",
      efns = {
        add = fn {thy,named_thms} => app (add_cong o #2) named_thms,
        remove = fn _ => ()
      }
    }

(* ----------------------------------------------------------------------
    storage of definitions
   ---------------------------------------------------------------------- *)

type defnstore = (string * KernelSig.kernelname, thm) Binarymap.dict
type indnstore = (KernelSig.kernelname, thm * term list) Binarymap.dict

val the_defnstore : defnstore ref =
    ref (Binarymap.mkDict(pair_compare(String.compare, KernelSig.name_compare)))
val the_indnstore : indnstore ref =
    ref (Binarymap.mkDict KernelSig.name_compare)

fun list_insert m k v =
    case Binarymap.peek(m,k) of
        NONE => Binarymap.insert(m,k,[v])
      | SOME vs => Binarymap.insert(m,k,v::vs)

fun to_kid {Thy,Name,Ty} = {Thy = Thy, Name = Name}

fun register_defn tag thm =
    let
      val ths = thm |> CONJUNCTS
      val cs =
          map
            (fn th =>
                (th |> concl |> strip_forall |> #2 |> lhs |> strip_comb |> #1
                    |> dest_thy_const |> to_kid,
                 th))
            ths handle HOL_ERR _ => raise mk_HOL_ERR "DefnBase" "register_defn"
                                          "Malformed definition"
      val m = List.foldr (fn ((t,th),A) => list_insert A t th)
                         (Binarymap.mkDict KernelSig.name_compare)
                         cs
    in
      the_defnstore :=
      Binarymap.foldl (fn (k,cs,A) => Binarymap.insert(A,(tag,k),LIST_CONJ cs))
                      (!the_defnstore)
                      m
    end

fun lookup_defn c tag =
    let
      val {Name,Thy,...} =
          dest_thy_const c
          handle HOL_ERR _ => raise mk_HOL_ERR "DefnBase"
                                    "lookup_defn" "Not a constant"
    in
      Binarymap.peek (!the_defnstore, (tag, {Name = Name, Thy = Thy}))
    end

fun isprefix l1 l2 =
    case (l1,l2) of
        ([] , _) => true
      | (h1::t1, []) => false
      | (h1::t1, h2::t2) => h1 = h2 andalso isprefix t1 t2

fun register_indn (ind, cs) =
    let
      val _ = not (null cs) orelse
              raise mk_HOL_ERR "DefnBase" "register_indn"
                    "Must have non-empty list of constants"
      val (Ps, body) = ind |> concl |> strip_forall
      fun check (P, c) =
          let
            val (Pdoms, _) = strip_fun (type_of P)
            val (cdoms, _) = strip_fun (type_of c)
          in
            isprefix Pdoms cdoms orelse
            raise mk_HOL_ERR "DefnBase" "register_indn"
                    ("Induction variable type of ivar "^ #1 (dest_var P) ^
                     " doesn't match that of constant " ^ #1 (dest_const c))
          end
      val _ = ListPair.all check (Ps, cs)
    in
      the_indnstore :=
      List.foldl (fn (c, A) =>
                     Binarymap.insert(A, c |> dest_thy_const |> to_kid,
                                      (ind,cs)))
                 (!the_indnstore)
                 cs
    end

fun lookup_indn c =
    let
      val {Name,Thy,...} =
          dest_thy_const c
          handle HOL_ERR _ => raise mk_HOL_ERR "DefnBase"
                                    "lookup_indn" "Not a constant"
    in
      Binarymap.peek (!the_indnstore, {Name = Name, Thy = Thy})
    end

(* ----------------------------------------------------------------------

    Once patterns are instantiated and the clauses are simplified,
    there can still remain right-hand sides with occurrences of fully
    concrete tests on literals. Here we simplify those away.

    const_eq_ref is a reference cell that decides equality of literals
    such as 23, "foo", #"G", 6w, 0b1000w. It gets updated in
    reduceLib, stringLib and wordsLib.

   ---------------------------------------------------------------------- *)
val const_eq_ref = ref Conv.NO_CONV;

fun elim_triv_literal_CONV tm =
   let
      val const_eq_conv = !const_eq_ref
      val cnv = TRY_CONV (REWR_CONV literal_case_THM THENC BETA_CONV) THENC
                RATOR_CONV (RATOR_CONV (RAND_CONV const_eq_conv)) THENC
                PURE_ONCE_REWRITE_CONV [COND_CLAUSES]
   in
       cnv tm
   end



(* ----------------------------------------------------------------------
    one_line_ify : thm -> thm

    Take in a theorem representing a function definition for a single
    constant (as returned by lookup_defn), and prove a reformulation where
    all the pattern matching in separate clauses has been replaced by
    "one" case expression under a single all-variable-argument LHS.
   ---------------------------------------------------------------------- *)
fun ERR f msg = mk_HOL_ERR "DefnBase" f msg
exception FastExit of thm

fun thry (arg as {Thy,Tyop}) =
    Option.map (fn tyi => {case_const = TypeBasePure.case_const_of tyi,
                           constructors = TypeBasePure.constructors_of tyi})
               (TypeBase.read arg)

fun foldli f A list =
    let fun foldthis (x, (A, i)) = (f i x A, i + 1)
    in
      #1 (List.foldl foldthis (A,0) list)
    end
fun foldri f A list =
    let fun recurse _ acc [] = acc
          | recurse j acc (h::t) = f j h (recurse (j + 1) acc t)
    in
      recurse 0 A list
    end
local
  val P = mk_var("P", bool)
  val x = mk_var("x", alpha)
  val y = mk_var("y", alpha)
  val z = mk_var("z", alpha)
  val goal = mk_eq(mk_cond(P, x, mk_cond(P, y, z)), mk_cond(P, x, z))
    (* |- if P then x else if P then y else z = if P then x else z *)
in
val COND_COND =
  DISJ_CASES (SPEC P BOOL_CASES_AX)
    (PURE_REWRITE_CONV [ASSUME (mk_eq(P,T)), COND_CLAUSES, REFL_CLAUSE] goal)
    (PURE_REWRITE_CONV [ASSUME (mk_eq(P,F)), COND_CLAUSES, REFL_CLAUSE] goal)
    |> EQT_ELIM
end

fun GENASSUME t = SPEC_ALL (ASSUME (gen_all t))
infix pTHENC
fun (c pTHENC k) t =
    case Exn.capture c t of
        Exn.Res th => EQ_MP (SYM th) (k (rhs (concl th)))
      | Exn.Exn Conv.UNCHANGED => k t
      | r => Exn.release r (* will be an exception *)

fun BETAS_CONV t =
    let
      val (f, args) = strip_comb t
    in
      if is_abs f then
        if length args = 1 then BETA_CONV t
        else (RATOR_CONV BETAS_CONV THENC BETA_CONV) t
      else ALL_CONV t
    end

val litresolve_conv = REPEATC elim_triv_literal_CONV
fun cases_prove case_const_def th k t =
    let
      fun recurse th =
          if is_eq (concl th) then
            let
              val ths = if is_var (lhs (concl th)) then [th]
                        else
                          CONJUNCTS (PURE_REWRITE_RULE [pairTheory.PAIR_EQ] th)
            in
              ((PURE_REWRITE_CONV ths THENC
                PURE_REWRITE_CONV [case_const_def, literal_case_THM] THENC
                RAND_CONV BETAS_CONV THENC
                RAND_CONV litresolve_conv) pTHENC k) t
            end
          else if is_disj (concl th) then
            let val (th1, th2) = (ASSUME ## ASSUME) (dest_disj (concl th))
                val t1_th = recurse th1
                val t2_th = recurse th2
            in
              DISJ_CASES th t1_th t2_th
            end
          else if is_exists (concl th) then
            let val (v, bod) = dest_exists (concl th)
                val v' = variant (free_vars t) v
                val bod' = subst[v |-> v'] bod
                val t_th = recurse (ASSUME bod')
            in
              CHOOSE (v',th) t_th
            end
          else raise ERR "cases_conv" "Badly formed case theorem"
    in
      recurse th
    end

fun attack_top_case stoppers k t =
    if List.exists (fn pat => can (match_term pat) (lhs t)) stoppers then
      k t
    else if Pmatch.is_case thry (rhs t) then
      let
        val(cc,args) = strip_comb (rhs t)
      in
        if same_const cc boolSyntax.literal_case then
          let
            val _ = HOL_MESG "Saw unexpected literal_case"
          in
            GENASSUME t
          end
        else
          let
            val a = hd args
            val ty = type_of (hd args)
            val {Thy,Tyop,...} = dest_thy_type ty
            val tyi =
                valOf (TypeBase.read {Thy = Thy,Tyop=Tyop})
                handle Option => raise ERR "attack_top_case"
                                       ("No tyinfo for "^Thy^"$"^Tyop)
          in
            if is_var a then
              cases_prove (TypeBasePure.case_def_of tyi)
                          (ISPEC a (TypeBasePure.nchotomy_of tyi))
                          (attack_top_case stoppers k)
                          t
            else
              (RAND_CONV (PURE_REWRITE_CONV [TypeBasePure.case_def_of tyi] THENC
                                    BETAS_CONV) pTHENC
                         attack_top_case stoppers k) t
          end
      end
    else k t



fun one_line_ify heuristic def =
    let
      val conjs = CONJUNCTS (SPEC_ALL def)
      fun munge_row th =
          let
            val (l,r) = th |> concl |> strip_forall |> #2 |> dest_eq
          in
            (strip_comb l, r, th)
          end
      val fs_args0 = map munge_row conjs
          handle HOL_ERR _ => raise ERR "one_line_ify" "Malformed def'n"
      val stoppers = map (list_mk_comb o #1) fs_args
      val _ =
          case List.find (fn((_, row), _, _) => List.all is_var row) fs_args0 of
              NONE => ()
            | SOME (_, _, th) => raise FastExit th
      val fs_args = map (fn (x,y,_) => (x,y)) fs_args0
      val ((f,args1),rhs1) = hd fs_args
      val _ = List.all (aconv f o #1 o #1) fs_args orelse
              raise ERR "one_line_ify" "Clauses defining more than one function"
      fun rowfoldthis i arg (A as (patcols,patfvs)) =
          if is_var arg then A
          else (HOLset.add(patcols,i), FVL [arg] patfvs)
      fun foldthis (((_, row), _), A) = foldli rowfoldthis A row
      val (patcols,patfvs) =
          List.foldl foldthis (HOLset.empty Int.compare, empty_tmset) fs_args
      val (_, safe_row1_vs) =
          foldri (fn i => fn a => fn (A as (avoids, newvs)) =>
                     if HOLset.member (patcols, i) then A
                     else let val v' = variant avoids a
                          in
                            (v'::avoids, v'::newvs)
                          end)
                 (HOLset.listItems patfvs, [])
                 args1
      (* now make var-columns use same vars as first row, except that
         non-pattern variables in the first row can't be the same as variables
         that occur in any of the patterns *)
      fun rowfoldthis i arg (A as (theta, safevs)) =
          if HOLset.member(patcols, i) then A
          else ({redex=arg,residue = hd safevs} :: theta, tl safevs)
      fun foldthis (((_, row), r), cs) =
          let val (theta, _) = foldli rowfoldthis ([], safe_row1_vs) row
          in
            (map (Term.subst theta) row, Term.subst theta r) :: cs
          end
      val patexps0 = List.foldr foldthis [] fs_args
      val (actual_args, _, _) =
          foldri (fn i => fn a => fn (A,avds,safes) =>
                     if HOLset.member(patcols, i) then
                       let val v = numvariant avds (mk_var("v", type_of a))
                       in
                         (v::A, v::avds, safes)
                       end
                     else (hd safes :: A, avds, tl safes))
                 ([], safe_row1_vs, List.rev safe_row1_vs)
                 args1
      (* build (patterns,exp) pairs that will be body of case expression *)
      fun rowfold i a A =
          if HOLset.member(patcols, i) then
            case A of NONE => SOME a | SOME b => SOME (pairSyntax.mk_pair(a,b))
          else A
      fun foldthis ((pat,r), A) = (valOf (foldri rowfold NONE pat),r) :: A
      val pats = List.foldr foldthis [] patexps0
      val selector_term = valOf (foldri rowfold NONE actual_args)
      val fakef = genvar(type_of (#1 (hd pats)) --> type_of (#2 (hd pats)))
      val {functional = abs_body0,...} =
          let
            val f = case heuristic of
                        NONE => (fn f => f)
                      | SOME h => PmatchHeuristics.with_heuristic h
          in
            f (Feedback.quiet_messages (Pmatch.mk_functional thry))
              (map (fn (l,r) => mk_eq(mk_comb(fakef, l), r)) pats
                   |> list_mk_conj)
          end
      val (_, abs_body) = dest_abs abs_body0
      val body = beta_conv (mk_comb(abs_body, selector_term))
      val (seltm, cases) = Pmatch.strip_case thry body
      val finisher =
          DEPTH_CONV BETA_CONV THENC
          PURE_REWRITE_CONV (REFL_CLAUSE::COND_COND::conjs) pTHENC
          GENASSUME
      val neweqn = mk_eq(list_mk_comb(f, actual_args), body)
    in
      if List.exists (fn (_, r) => same_const boolSyntax.arb r) cases then
        let
          fun mapthis (l,r) =
              if same_const boolSyntax.arb r then NONE
              else SOME (list_mk_exists (free_vars l, mk_eq(seltm, l)))
          val aa_asm = List.mapPartial mapthis cases
                                       |> list_mk_disj |> ASSUME
        in
          cases_prove pairTheory.pair_case_def aa_asm
                      (attack_top_case stoppers finisher)
                      neweqn |> PROVE_HYP TRUTH
        end
      else
        attack_top_case stoppers finisher neweqn |> PROVE_HYP TRUTH
    end handle FastExit th => th

end
