(* ----------------------------------------------------------------------
    Proves theorems about record types.  A record type is set up by first
    calling standard datatype code to set up a new type with one
    constructor and as many arguments to that constructor as there are
    fields in the desired record type, and with the corresponding types.

    The main function takes this new type's tyinfo data, as well as a
    list of the field names.

    Author: Michael Norrish
   ---------------------------------------------------------------------- *)

structure RecordType :> RecordType =
struct

open HolKernel Parse boolLib

val (Type,Term) = parse_from_grammars boolTheory.bool_grammars
fun -- q x = Term q
fun == q x = Type q

val ERR = mk_HOL_ERR "RecordType";

(* ----------------------------------------------------------------------
    General utilities
   ---------------------------------------------------------------------- *)

fun map3 f ([], _, _) = []
  | map3 f (x::xs, ys, zs) = f (x, hd ys, hd zs) :: map3 f (xs, tl ys, tl zs)

fun insert n e l =
    if n < 1 then raise Fail "Bad position to insert at" else
    if n = 1 then e::l else (hd l)::(insert (n-1) e (tl l));
fun delete n l =
    if n < 1 then raise Fail "Bad position to delete at" else
    if n = 1 then tl l
    else (hd l)::(delete (n-1) (tl l));
fun update n e = (insert n e) o (delete n);
fun findi e [] = raise Fail "Couldn't find element"
  | findi e (x::xs) = if e = x then 1 else 1 + findi e xs;
fun foldr f zero []      = zero
  | foldr f zero (x::xs) = f x (foldr f zero xs)
fun foldl f zero []      = zero
  | foldl f zero (x::xs) = foldl f (f zero x) xs

fun dest_all_type ty =
    dest_type ty handle HOL_ERR _ => (dest_vartype ty, [])

fun variant tml tm = let
  fun name_of tm = if is_var tm then SOME (fst(dest_var tm)) else NONE
  val avoidstrs = List.mapPartial name_of tml
  val (Name, Ty) = Term.dest_var tm
in
  Term.mk_var(Lexis.gen_variant Lexis.tmvar_vary avoidstrs Name,Ty)
end


(* app_letter = "appropriate letter" *)
fun app_letter ty =
    if is_vartype ty then String.substring(dest_vartype ty, 1, 1)
    else String.substring(#Tyop (dest_thy_type ty), 0, 1)

(* Given a list of variables l, this returns a list of           *)
(* variable-variable list pairs, such that for each element      *)
(* (x,xl), xl is just the same as l except one element will have *)
(* been replaced by x.                                           *)
fun gen_update_pairs tls =
    let fun rec_upd_pairs [] front = []
          | rec_upd_pairs (hd::tl) front =
            let val newvar = variant tls hd
                val newhd = (newvar,front@(newvar::tl))
            in
              newhd :: (rec_upd_pairs tl (front @ [hd]))
            end
    in
      rec_upd_pairs tls []
    end

(* given two lists of equal length n, produce a list of length *)
(* n(n-1) where each element of the first list is paired with  *)
(* each of the second, except the one that corresponds to it   *)
local
  fun nrecfilter fnc [] n       = []
    | nrecfilter fnc (hd::tl) n =
      if (not (fnc (n,hd))) then
        nrecfilter fnc tl (n+1)
      else
        hd::(nrecfilter fnc tl (n+1))
in
fun nfilter fnc l = nrecfilter fnc l 1
end

fun crossprod l1 l2 =
    let
      fun pairer x y = x @ map (fn item => (y,item)) l2 in
      foldl pairer [] l1
    end

fun crosslessdiag l1 l2 =
    let
      val cross = crossprod l1 l2 and
                  diaglength = List.length l1 + 1 in
      nfilter (fn (n,_) => not (n mod diaglength = 1)) cross
    end

fun update_tyinfo new_simpls tyinfo = let
  open TypeBasePure
  val existing_simpls = simpls_of tyinfo
  fun add_rwts {convs, rewrs} newrwts =
      {convs = convs, rewrs = rewrs @ newrwts}
in
  put_simpls (add_rwts existing_simpls new_simpls) tyinfo
end

(* ----------------------------------------------------------------------
    prove_recordtype_thms

    Where all the work happens. The following function is huge and
    revolting.
   ---------------------------------------------------------------------- *)

fun prove_recordtype_thms (tyinfo, fields) = let

  fun store_thm (n, t, tac) = save_thm(n, prove(t,tac))

  val app2 = C (curry op^)
  val typthm = TypeBasePure.axiom_of tyinfo
  val typename = TypeBasePure.ty_name_of tyinfo
  val constructor =
    case TypeBasePure.constructors_of tyinfo of
      [x] => x
    | _ => raise ERR "prove_recordtype_thms"
                     "Type to be record has more than one constructor"
  val (typ, types) = let
    fun domtys acc ty = let
      val (d1, rty) = dom_rng ty
    in
      domtys (d1::acc) rty
    end handle HOL_ERR _ => (ty, List.rev acc)
  in
    domtys [] (type_of constructor)
  end

  val _ = length types = length fields orelse
    raise HOL_ERR {origin_function = "prove_recordtype_thms",
                   origin_structure = "RecordType",
                   message =
                   "Number of fields doesn't match number of types"}

  (* we now have the type actually defined in typthm *)
  fun letgen x y = x @ [variant x (mk_var (app_letter y,y))]
  val typeletters = foldl letgen [] types

  (* now generate accessor functions *)
  val accfn_types = map (fn x => (typ --> x)) types
  local
    fun constructor_args [] = map boolSyntax.mk_arb types
      | constructor_args ((f,t)::xs) = let
          val rest = constructor_args xs
          val posn = findi f fields handle _ =>
            raise Fail "Bad field name"
        in
          update posn t rest
        end
  in
    fun create_term ftl =
      list_mk_comb(constructor, constructor_args ftl)
  end
  val cons_comb = list_mk_comb(constructor,  typeletters)
  val access_fn_names = map (fn n => typename^"_"^n) fields
  val access_defn_terms =
    map3 (fn (afn_name, typeletter, accfn_type) =>
          mk_eq(mk_comb(mk_var(afn_name, accfn_type),
                        cons_comb),
                typeletter))
    (access_fn_names, typeletters, accfn_types)
  val access_defns =
    ListPair.map
    (fn (name, tm) => Prim_rec.new_recursive_definition
     {def = tm, name = name, rec_axiom = typthm})
    (access_fn_names, access_defn_terms)
  val accessor_thm =
    save_thm(typename^"_accessors", LIST_CONJ access_defns)
  val accfn_terms = ListPair.map mk_const (access_fn_names, accfn_types)

  (* now generate update functions *)
  val update_type = mk_type("fun", [typ,typ])
  val update_pairs = gen_update_pairs typeletters
  val updfn_names = map (fn s => s^ "_update") access_fn_names
  val updfn_terms =
    ListPair.map (fn (n, t) => mk_var(n,Type.-->(t,update_type)))
    (updfn_names, types)
  val updfn_defn_terms =
    ListPair.map
    (fn (updfn_term, (newvar,newvlist)) =>
     mk_eq (list_mk_comb(updfn_term, [newvar, cons_comb]),
            list_mk_comb(constructor, newvlist)))
    (updfn_terms, update_pairs)
  val updfn_defns =
    ListPair.map
    (fn (name, tm) =>
     Prim_rec.new_recursive_definition
     {rec_axiom = typthm, name = name, def = tm})
    (updfn_names, updfn_defn_terms)
  val updfn_thm =
    save_thm(typename^"_updates",  LIST_CONJ updfn_defns)
  (* updfn_terms is a list of variables, not constants, so we need to *)
  (* convert them into constants                                      *)
  val updfn_terms = map (mk_const o dest_var) updfn_terms

  (* generate functional update functions *)
  (* these are of the form :
       field_fupd f o = field_update (f (field o)) o
   *)
  val fupd_names = map (fn s => s ^ "_fupd") access_fn_names
  val fupd_fun_types = map (fn t => Type.-->(t,t)) types
  val fupd_types = map (fn t => Type.-->(t, update_type)) fupd_fun_types
  val fupd_terms = ListPair.map mk_var (fupd_names, fupd_types)
  fun combine (fld, fldupd, fldfupd) =
    (--`!f x. ^fldfupd f x = ^fldupd (f (^fld x)) x`--)
  val fupd_def_terms = map3 combine (accfn_terms, updfn_terms, fupd_terms)
  val fupdfn_thms =
    ListPair.map new_definition (fupd_names, fupd_def_terms)
  val fupdfn_thm =
    save_thm(typename^"_fn_updates", LIST_CONJ fupdfn_thms)
  val fupdfn_terms = map (mk_const o dest_var) fupd_terms


  (* do cases and induction theorem *)
  val induction_thm = TypeBasePure.induction_of tyinfo
  val cases_thm = TypeBasePure.nchotomy_of tyinfo

  fun gen_var_domty(name, tm, avoids) = let
    val v0 = mk_var(name, #1 (dom_rng (type_of tm)))
  in
    variant avoids v0
  end

  (* do access of updates theorems *)
  val var = Psyntax.mk_var(app_letter typ, typ)
  val tactic = STRUCT_CASES_TAC (SPEC var cases_thm) THEN
               REWRITE_TAC [accessor_thm,updfn_thm]
  val combinations = crosslessdiag accfn_terms updfn_terms
  fun create_goal (acc, upd) = let
    val x = gen_var_domty("x", upd, [var])
  in
    (--`^acc (^upd ^x ^var) = ^acc ^var`--)
  end
  val goals = map create_goal combinations
  fun create_goal (acc, upd) = let
    val x = gen_var_domty("x", upd, [var])
  in
    Term`^acc (^upd ^x ^var) = ^x`
  end
  val diag_goals = ListPair.map create_goal (accfn_terms, updfn_terms)
  val thms = map (C (curry prove) tactic) (goals@diag_goals)
  val accupd_thm =
    save_thm(typename^"_accupds", LIST_CONJ (map GEN_ALL thms))

  (* do acc of fupdates theorems *)
  (* i.e. thms of the form
        (r with fld1 updated by val).fld2 = r.fld2
     ( ==
         fld1 (fld2_fupd val r) = fld1 r
      )
  *)
  fun create_goal (acc, fupd) = let
    val f = gen_var_domty("f", fupd, [var])
  in
    Term`^acc (^fupd ^f ^var) = ^acc ^var`
  end
  val combinations = crosslessdiag accfn_terms fupdfn_terms
  val goals = map create_goal combinations
  fun create_goal (acc, fupd) = let
    val f = gen_var_domty("f", fupd, [var])
  in
    Term`^acc (^fupd ^f ^var) = ^f (^acc ^var)`
  end
  val diag_goals = ListPair.map create_goal (accfn_terms, fupdfn_terms)
  val tactic = STRUCT_CASES_TAC (SPEC var cases_thm) THEN
    REWRITE_TAC [accessor_thm, fupdfn_thm, updfn_thm, combinTheory.o_THM] THEN
    BETA_TAC THEN REWRITE_TAC []
  val thms = map (C (curry prove) tactic) (goals @ diag_goals)
  val accfupd_thm =
    save_thm(typename^"_accfupds", LIST_CONJ (map GEN_ALL thms))

  (* do updates of access theorems *)
  (* theorems of the form: fld_upd (fld r) r = r *)
  fun mk_accfn_and_arg t = mk_comb(t,var)
  val accessfns_and_args = map mk_accfn_and_arg accfn_terms
  val map_mk_comb = curry Psyntax.mk_comb
  val lhses = map2 map_mk_comb updfn_terms accessfns_and_args
  val goals = map (fn t => (--`^t ^var = ^var`--)) lhses
  val thms = map (C (curry prove) tactic) goals
  val updacc_thm =
    save_thm(typename^"_updaccs", LIST_CONJ (map GEN_ALL thms))

  (* do updates of (same) updates *)
  fun create_goal upd =
    (--`^upd x1 (^upd x2 ^var) = ^upd x1 ^var`--)
  val goals = map create_goal updfn_terms
  val thms = map (C (curry prove) tactic) goals
  val updupd_thm =
    save_thm(typename^"_updupds", LIST_CONJ (map GEN_ALL thms))

  (* do updates of updates, expressed with function compositions *)
  (* i.e., upd_fld1 v1 o upd_fld1 v2 = upd_fld1 v1 *)
  fun to_composition t = let
    val (f, gx) = dest_comb t
  in
    if is_comb gx then let
        val (g, x) = dest_comb gx
      in
        SYM (ISPECL [f, g, x] combinTheory.o_THM)
      end
    else REFL t
  end
  fun o_assoc_munge th = let
    (* th of form f o g = x; want to produce f o (g o h) = x o h *)
    val (l, r) = dest_eq (concl th)
    val l_ty = type_of l
    val (dom, rng) = dom_rng l_ty
    val tyvs = map dest_vartype (type_vars_in_term l)
    val newtyv = mk_vartype(Lexis.gen_variant Lexis.tyvar_vary tyvs "'a")
    val h = mk_var("h", newtyv --> dom)
    val new_o = mk_thy_const{Name = "o", Thy = "combin",
                             Ty = l_ty --> (type_of h --> (newtyv --> rng))}
    val newth = AP_THM (AP_TERM new_o th) h
  in
    REWRITE_RULE [GSYM combinTheory.o_ASSOC] newth
  end

  fun munge_to_composition thm = let
    val thm = SPEC_ALL thm
    val (l, r) = dest_eq (concl thm)
    val lthm = SYM (to_composition l)
    val rthm = to_composition r
    val new_eq = TRANS (TRANS lthm thm) rthm
    val gnew_eq = EXT (GEN (rand (rand (concl new_eq))) new_eq)
    val o_assoc_version = o_assoc_munge gnew_eq
  in
    CONJ (GEN_ALL gnew_eq) (GEN_ALL o_assoc_version)
  end
  val updupd_comp_thm =
      save_thm(typename^"_updupd_comp",
               LIST_CONJ (map munge_to_composition (CONJUNCTS updupd_thm)))


  (* do fupdates of (same) fupdates *)
  (* i.e., fupd_fld1 f (fupd_fld1 g r) = fupd_fld1 (f o g) r *)
  fun create_goal fupd = let
    val fty = #1 (dom_rng (type_of fupd))
    val f = variant [var] (mk_var("f", fty))
    val g = variant [var, f] (mk_var("g", fty))
    val x = variant [var, f, g] (mk_var("x", #1 (dom_rng fty)))
  in
    mk_eq(list_mk_comb(fupd, [f, list_mk_comb(fupd, [g, var])]),
          list_mk_comb(fupd, [combinSyntax.mk_o(f, g), var]))
  end
  val goals = map create_goal fupdfn_terms
  val thms = map (C (curry prove) tactic) goals
  val fupdfupd_thm =
      save_thm(typename^"_fupdfupds", LIST_CONJ (map GEN_ALL thms))

  (* do updates of (different) updates *)
  (* this is for canonicalisation of update sequences *)
  val combinations = crossprod updfn_terms updfn_terms
  val size = List.length updfn_terms
  val filterfn = (fn (n,_) => let val m = n - 1
                                  val d =  m div size
                                  val m = m - (d * size) in
                                    d > m end)
  val lower_triangle = nfilter filterfn combinations
  fun create_goal (f1,f2) = let
    val (x0_t,_) = dom_rng (type_of f1)
    val (z0_t,_) = dom_rng (type_of f2)
    val x = variant [var] (mk_var("x", x0_t))
    val z = variant [var] (mk_var("z", z0_t))
  in
    mk_eq(list_mk_comb(f1, [x, list_mk_comb(f2, [z,var])]),
          list_mk_comb(f2, [z, list_mk_comb(f1, [x,var])]))
  end
  val goals = map create_goal lower_triangle
  val upd_canon_thms = map (C (curry prove) tactic) goals
    (* in the case where there is only one constructor, goals and thms
     will both be empty.  In this case, we don't want to apply LIST_CONJ
     to them *)
  val (updcanon_thm, updcanon_comp_thm) =
    if (List.length upd_canon_thms > 0) then
      (save_thm(typename^"_updcanon",
                (LIST_CONJ (map GEN_ALL upd_canon_thms))),
       save_thm(typename^"_updcanon_comp",
                (LIST_CONJ (map munge_to_composition upd_canon_thms))))
    else
      (TRUTH, TRUTH)

  (* do fupdates of (different) fupdates *)
  val combinations = crossprod fupdfn_terms fupdfn_terms
  val lower_triangle = nfilter filterfn combinations
  fun create_goal(f1,f2) = let
    val (f_t, _) = dom_rng (type_of f1)
    val (g_t, _) = dom_rng (type_of f2)
    val f = variant [var] (mk_var("f", f_t))
    val g = variant [var, f] (mk_var("g", g_t))
  in
    mk_eq(list_mk_comb(f1, [f, list_mk_comb(f2, [g, var])]),
          list_mk_comb(f2, [g, list_mk_comb(f1, [f, var])]))
  end
  val goals = map create_goal lower_triangle
  val fupdcanon_thms = map (C (curry prove) tactic) goals
  val fupdcanon_thm =
      if length fupdcanon_thms > 0 then
        save_thm(typename^"_fupdcanon",
                 LIST_CONJ (map GEN_ALL fupdcanon_thms))
      else TRUTH

  val oneone_thm = valOf (TypeBasePure.one_one_of tyinfo)

  (* prove that equality of values is equivalent to equality of fields:
     i.e. for a record type with two fields:
        !r1 r2. (r1 = r2) = (r1.fld1 = r2.fld1) /\ (r1.fld2 = r2.fld2)
  *)
  local
    val var1 = mk_var(app_letter typ ^ "1", typ)
    val var2 = mk_var(app_letter typ ^ "2", typ)
    val lhs = mk_eq(var1, var2)
    val rhs_tms =
      map (fn tm => mk_eq(mk_comb(tm, var1), mk_comb(tm, var2)))
      accfn_terms
    val rhs = list_mk_conj rhs_tms
    val thmname = typename ^ "_component_equality"
    val goal = mk_eq(lhs, rhs)
    val tactic =
      REPEAT GEN_TAC THEN
      MAP_EVERY (STRUCT_CASES_TAC o C SPEC cases_thm) [var1, var2] THEN
      REWRITE_TAC [oneone_thm, accessor_thm]
    val thm0 = prove(goal, tactic)
  in
    val component_wise_equality =
      save_thm(thmname, GENL [var1, var2] thm0)
  end

  (* prove

     1.  that a complete chain of updates over any value is
         equivalent to a chain of updates over ARB.  This particular
         formulation is chosen to help the pretty-printer, which
         will print such updates over ARB as record literals.
         e.g.
             r1 with <| fld1 := v1 ; fld2 := v2 |> =
             <| fld1 := v1; fld2 := v2 |>
     2.  prove a version of the nchotomy theorem that uses literal
         notation rather than the underlying notation involving the
         constructor
         e.g.,
           !r. ?v1 v2 v3. r = <| fld1 := v1; fld2 := v2; fld3 := v3 |>

     3.  a FORALL_RECD theorem of the form
            (!r. P r) =
            (!v1 v2 v3. P <| fld1 := v1; fld2 := v2; fld3 := v3 |>)

     4.  likewise, an EXISTS_RECD

     5.  one-one ness for literals
            (<| fld1 := v11; fld2 := v21; fld3 := v31 |> =
             <| fld1 := v12; fld2 := v22; fld3 := v32 |>) =
            (v11 = v12) /\ (v21 = v22) /\ (v31 = v32)
  *)
  local
    fun mk_var_avds (nm, ty, avoids) = let
      val v0 = mk_var(nm, ty)
    in
      variant avoids v0
    end

    val value_vars =
      List.take(List.foldr
                  (fn (ty, sofar) =>
                      mk_var_avds(app_letter ty, ty, var::sofar)::sofar)
                  [var] types,
                length fields)
    fun augvar n v = let
      val (nm, ty) = dest_var v
    in
      mk_var(nm ^ Int.toString n, ty)
    end
    val vvars1 = map (augvar 1) value_vars
    val vvars2 = map (augvar 2) value_vars
    val arb = mk_const("ARB", typ)
    val updfns =
      map2 (fn upd => fn v => mk_comb(upd, v)) updfn_terms value_vars
    val lhs = List.foldr mk_comb var updfns
    val rhs = List.foldr mk_comb arb updfns

    val lit1 =
        List.foldr mk_comb arb (map2 (curry mk_comb) updfn_terms vvars1)
    val lit2 =
        List.foldr mk_comb arb (map2 (curry mk_comb) updfn_terms vvars2)

    val literal_equality =
        GENL (var::value_vars)
             (prove(mk_eq(lhs, rhs),
                    MAP_EVERY (STRUCT_CASES_TAC o C SPEC cases_thm)
                              [arb, var] THEN REWRITE_TAC [updfn_thm]))

    val literal_nchotomy =
        prove(mk_forall(var, list_mk_exists(value_vars, mk_eq(var, rhs))),
              GEN_TAC THEN
              MAP_EVERY (STRUCT_CASES_TAC o C SPEC cases_thm) [arb, var] THEN
              REWRITE_TAC [updfn_thm, accessor_thm, oneone_thm] THEN
              REPEAT Unwind.UNWIND_EXISTS_TAC)

    val pred_r = mk_var_avds("P", typ --> bool, var::value_vars)
    val P_r = mk_comb(pred_r, var)
    val P_literal = mk_comb(pred_r, rhs)
    val forall_goal = mk_eq(mk_forall(var, P_r),
                            list_mk_forall(value_vars, P_literal))
    val exists_goal = mk_eq(mk_exists(var, P_r),
                            list_mk_exists(value_vars, P_literal))
    val forall_thm =
        GEN_ALL
          (prove(forall_goal,
                 EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
                 GEN_TAC THEN
                 STRUCT_CASES_TAC (SPEC var literal_nchotomy) THEN
                 ASM_REWRITE_TAC []))
    val exists_thm =
        GEN_ALL
        (prove(exists_goal,
               EQ_TAC THENL [
                 DISCH_THEN (X_CHOOSE_THEN var ASSUME_TAC) THEN
                 EVERY_TCL (map X_CHOOSE_THEN value_vars)
                           SUBST_ALL_TAC (SPEC var literal_nchotomy) THEN
                 MAP_EVERY EXISTS_TAC value_vars THEN ASM_REWRITE_TAC [],
                 DISCH_THEN (EVERY_TCL (map X_CHOOSE_THEN value_vars)
                                       ASSUME_TAC) THEN
                 EXISTS_TAC rhs THEN ASM_REWRITE_TAC []
               ]))

    val literal_11 =
        GENL (vvars1 @ vvars2)
             (REWRITE_RULE [accupd_thm]
                           (SPECL [lit1, lit2] component_wise_equality))

  in
    val literal_equality =
        save_thm(typename ^ "_updates_eq_literal", literal_equality)
    val literal_nchotomy =
        save_thm(typename ^ "_literal_nchotomy", literal_nchotomy)
    val forall_thm = save_thm("FORALL_" ^ typename, forall_thm)
    val exists_thm = save_thm("EXISTS_"^ typename, exists_thm)
    val literal_11 = save_thm(typename ^ "_literal_11", literal_11)
  end

  (* add to the TypeBase's simpls entry for the record type *)
  val new_simpls = let
    val new_simpls0 =  [accupd_thm, accessor_thm, updfn_thm, updacc_thm,
                        updupd_thm, accfupd_thm, literal_equality,
                        literal_11, fupdfupd_thm]
  in
    if not (null upd_canon_thms) then
      updcanon_thm :: fupdcanon_thm ::  updcanon_comp_thm :: new_simpls0
    else new_simpls0
  end
  val new_tyinfo = update_tyinfo new_simpls tyinfo

  (* set up parsing for the record type *)
  val brss = GrammarSpecials.bigrec_subdivider_string
  val _ =
      if List.exists (is_substring brss) (typename :: fields) then
        ()
      else let
          fun do_updfn (name0, tm) = let val name = name0 ^ "_update"
                                     in
                                       Parse.overload_on(name, tm)
                                     end
          fun do_fupdfn (name0, tm) = let val name = name0 ^ "_fupd"
                                      in
                                        Parse.overload_on(name, tm)
                                      end
        in
          ListPair.app add_record_field (fields, accfn_terms);
          (* overload strings of the form fld_update to refer to the
             real update functions, which have names of the form
             type_fld_update.  Make sure that this overloading is
             done before the add_record_update function is called
             because this will also overload this constant to the
             "artificial" constant for special printing of record
             syntax, and we want this to be preferred where
             possible. *)
           ListPair.app do_updfn (fields, updfn_terms);
           ListPair.app add_record_update (fields, updfn_terms);
           (* Similarly for functional update functions *)
           ListPair.app do_fupdfn (fields, fupdfn_terms);
           ListPair.app add_record_fupdate (fields, fupdfn_terms)
        end

  val thm_str_list =
     map (concat typename)
     (["_accessors", "_updates", "_updates_eq_literal", "_updaccs",
       "_accupds", "_accfupds", "_updupds", "_fupdfupds",
       "_literal_11"] @
      (if not (null upd_canon_thms) then
         ["_updcanon", "_updcanon_comp", "_fupdcanon"]
       else []))
  in
    (new_tyinfo,
     "RecordType.update_tyinfo ["^String.concat (Lib.commafy thm_str_list)^
     "] ")
  end

end (* struct *)
