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

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars boolTheory.bool_grammars
end
open Parse

val K_tm = combinSyntax.K_tm

val debugp = ref false
fun DIAG s = if !debugp then print ("RecordType: " ^ s ^ "\n") else ()
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

(* given two lists of equal length n, produce a list of length *)
(* n(n-1) where each element of the first list is paired with  *)
(* each of the second, except the one that corresponds to it   *)
local
  fun nrecfilter fnc [] n       = []
    | nrecfilter fnc (hd::tl) n =
      if not (fnc (n,hd)) then
        nrecfilter fnc tl (n+1)
      else
        hd::nrecfilter fnc tl (n+1)
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

fun update_tyinfo opt new_simpls tyinfo =
 let open TypeBasePure
     val existing_simpls = simpls_of tyinfo
     fun add_rwts {convs,rewrs} newrwts = {convs=convs, rewrs=rewrs @ newrwts}
     val base = put_simpls (add_rwts existing_simpls new_simpls) tyinfo
 in
  case opt of
    NONE => base
  | SOME (flds,accs,upds) =>
      put_accessors accs
       (put_updates upds
         (put_fields flds base))
end

fun digit_suffix s =
  let
    val ss = Substring.full s
    val (l,r) = Substring.splitr Char.isDigit ss
  in
    (Substring.string l, Int.fromString (Substring.string r))
  end

fun nexttyvar ty =
  let
    val qnm = dest_vartype ty
    val nm = String.extract(qnm, 1, NONE)
  in
    if size nm = 1 andalso Char.isLower (String.sub(nm, 0)) then
      if nm <> "z" then
        mk_vartype("'" ^ String.str (Char.chr(Char.ord (String.sub(nm,0)) + 1)))
      else
        mk_vartype "'a0"
    else
      case digit_suffix qnm of
          (pfx, NONE) => mk_vartype (pfx ^ "0")
        | (pfx, SOME i) => mk_vartype (pfx ^ Int.toString (i + 1))
  end

fun tyvariant avoids ty =
  if mem ty avoids then tyvariant avoids (nexttyvar ty)
  else ty

(* assumes that avoids is a superset of tyvs *)
fun freshsubst avoids tyvs =
  let
    fun foldthis (tyv, (avoids, s)) =
      let
        val v' = tyvariant avoids tyv
      in
        (v'::avoids, (tyv |-> v') :: s)
      end
  in
    #2 (List.foldl foldthis (avoids, []) tyvs)
  end


(* ----------------------------------------------------------------------
    prove_recordtype_thms

    Where all the work happens. The following function is huge and
    revolting.
   ---------------------------------------------------------------------- *)

fun prove_recordtype_thms (tyinfo, fields) = let
  open TypeBasePure
  val save_thm = Feedback.trace ("Theory.save_thm_reporting", 0) save_thm
  fun store_thm (n, t, tac) = save_thm(n, prove(t,tac))

  val app2 = C (curry op^)
  val typthm = TypeBasePure.axiom_of tyinfo
  val (thyname,typename) = TypeBasePure.ty_name_of tyinfo
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
  val varying_tyvs = let
    val tymap = Binarymap.mkDict Type.compare : (hol_type,int) Binarymap.dict
    fun recurse m tys =
      case tys of
          [] => m
        | ty::tyrest =>
          let
            val tyvs = HOLset.fromList Type.compare (Type.type_vars ty)
            fun foldthis (tyv,m) =
                case Binarymap.peek(m, tyv) of
                    NONE => Binarymap.insert(m,tyv,1)
                  | SOME i => Binarymap.insert(m,tyv,i+1)
          in
            recurse (HOLset.foldl foldthis m tyvs) tyrest
          end
  in
    Binarymap.foldl (fn (tyv,c,acc) => if c = 1 then tyv::acc else acc)
                    []
                    (recurse tymap types)
  end

  val tysigma = let
    val avoids = Type.type_varsl types
  in
    freshsubst avoids varying_tyvs
  end
  val sigsubst = type_subst tysigma
  val var = Psyntax.mk_var(app_letter typ, typ)
  val size = length fields

  val _ = length types = length fields orelse
    raise mk_HOL_ERR "RecordType" "prove_recordtype_thms"
      "Number of fields doesn't match number of types"

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
  val access_fn_names =
      map (fn f => mk_recordtype_fieldsel{tyname=typename,fieldname=f}) fields
  val access_defn_terms =
    map3 (fn (afn_name, typeletter, accfn_type) =>
          mk_eq(mk_comb(mk_var(afn_name, accfn_type),
                        cons_comb),
                typeletter))
    (access_fn_names, typeletters, accfn_types)
  fun mk_defname s = String.translate (fn #"." => "_" | c => str c) s ^ "_def"
  val access_defns =
    ListPair.map
    (fn (name, tm) => Prim_rec.new_recursive_definition
     {def = tm, name = mk_defname name, rec_axiom = typthm})
    (access_fn_names, access_defn_terms)
  val accessor_thm =
    save_thm(typename^"_accessors", LIST_CONJ access_defns)
  fun mk_const(n,ty) = mk_thy_const{Thy=current_theory(), Name = n, Ty = ty}
  val accfn_terms = ListPair.map mk_const (access_fn_names, accfn_types)
  val _ = DIAG "generated accessors"

  (* generate functional update functions *)
  (* these are of the form :
       field_fupd f o = field_update (f (field o)) o
   *)
  val fupd_names =
      map (fn f => mk_recordtype_fieldfupd{tyname=typename,fieldname=f}) fields
  fun getredex t = let
    val tyvs = type_vars t
  in
    List.filter (fn {redex,residue} => mem redex tyvs)
  end
  val fupd_fun_types =
      map (fn t => (getredex t tysigma, t --> sigsubst t)) types
  val fupd_types =
      map (fn (s,t) => (s, t --> typ --> type_subst s typ)) fupd_fun_types
  val fupd_terms =
      ListPair.map (fn (n,(s,ty)) => (s, mk_var(n,ty))) (fupd_names, fupd_types)
  fun mk_fupd_defn ((s, fldfupd), result, (pos, acc)) = let
    val (f_ty, _) = dom_rng (type_of fldfupd)
    val f0 = mk_var("f", f_ty)
    val f = variant typeletters f0
  in
    (pos + 1,
     mk_eq(list_mk_comb(fldfupd, [f, cons_comb]),
           list_mk_comb(Term.inst s constructor,
                        update pos (mk_comb(f, result)) typeletters)) :: acc)
  end
  val (_, fupd_def_terms0) = ListPair.foldl mk_fupd_defn (1, [])
                                            (fupd_terms, typeletters)
  val fupd_def_terms = List.rev fupd_def_terms0
  fun mk_defn_th (n, t) =
      Prim_rec.new_recursive_definition
        {def = t, name = mk_defname n, rec_axiom = typthm}
  val fupdfn_thms = ListPair.map mk_defn_th (fupd_names, fupd_def_terms)
  val fupdfn_thm =
    save_thm(typename^"_fn_updates", LIST_CONJ fupdfn_thms)
  val fupdfn_terms =
      map (fn (s, v) => (s, mk_const (dest_var v))) fupd_terms
  val _ = DIAG "generated functional updates"


  (* do cases and induction theorem *)
  val induction_thm = TypeBasePure.induction_of tyinfo
  val cases_thm = TypeBasePure.nchotomy_of tyinfo

  fun gen_var_domty(name, tm, avoids) = let
    val v0 = mk_var(name, #1 (dom_rng (type_of tm)))
  in
    variant avoids v0
  end

  (* do acc of fupdates theorems *)
  (* i.e. thms of the form
        (r with fld1 updated by val).fld2 = r.fld2
     ( ==
         fld1 (fld2_fupd val r) = fld1 r
      )
  *)
  fun create_goal (acc, (s, fupd)) = let
    val f = gen_var_domty("f", fupd, [var])
  in
    Term`^(Term.inst s acc) (^fupd ^f ^var) = ^acc ^var`
  end
  val combinations = crosslessdiag accfn_terms fupdfn_terms
  val goals = map create_goal combinations
  fun create_goal (acc, (s, fupd)) = let
    val f = gen_var_domty("f", fupd, [var])
  in
    Term`^(Term.inst s acc) (^fupd ^f ^var) = ^f (^acc ^var)`
  end
  val diag_goals = ListPair.map create_goal (accfn_terms, fupdfn_terms)
  val tactic = STRUCT_CASES_TAC (SPEC var cases_thm) THEN
    REWRITE_TAC [accessor_thm, fupdfn_thm, combinTheory.o_THM] THEN
    BETA_TAC THEN REWRITE_TAC []
  val thms = map (C (curry prove) tactic) (goals @ diag_goals)
  val accfupd_thm =
    save_thm(typename^"_accfupds", LIST_CONJ (map GEN_ALL thms))
  val _ = DIAG "Generated accupds theorem"

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

  (* do fupdates of (same) fupdates *)
  (* i.e., fupd_fld1 f (fupd_fld1 g r) = fupd_fld1 (f o g) r *)
  fun create_goal (s, fupd) = let
    val fupdty = type_of fupd
    val (gty,r) = dom_rng fupdty
    val (gd, gr) = dom_rng gty
    val ftys = freshsubst (type_vars fupdty) (map #residue s)
    val fty = gr --> type_subst ftys gr
    val f = variant [var] (mk_var("f", fty))
    val g = variant [var, f] (mk_var("g", gty))
  in
    mk_eq(list_mk_comb(inst s (inst ftys fupd),
                       [f, list_mk_comb(fupd, [g, var])]),
          list_mk_comb(inst ftys fupd, [combinSyntax.mk_o(f, g), var]))
  end
  val goals = map create_goal fupdfn_terms
  val thms = map (C (curry prove) tactic) goals
  val fupdfupd_thm =
      save_thm(typename^"_fupdfupds", LIST_CONJ (map GEN_ALL thms))
  val fupdfupds_comp_thm =
      save_thm(typename^"_fupdfupds_comp",
               LIST_CONJ (map munge_to_composition thms))
  val _ = DIAG "Generated fupdfupd thms"

  (* do fupdates of (different) fupdates *)
  val combinations = crossprod fupdfn_terms fupdfn_terms
  val filterfn = (fn (n,_) => let val m = n - 1
                                  val d = m div size
                                  val m = m - (d * size) in
                                    d > m end)
  val lower_triangle = nfilter filterfn combinations
  fun create_goal((s1, f1),(s2, f2)) = let
    val (f_t, _) = dom_rng (type_of f1)
    val (g_t, _) = dom_rng (type_of f2)
    val f = variant [var] (mk_var("f", f_t))
    val g = variant [var, f] (mk_var("g", g_t))
  in
    mk_eq(list_mk_comb(inst s2 f1, [f, list_mk_comb(f2, [g, var])]),
          list_mk_comb(inst s1 f2, [g, list_mk_comb(f1, [f, var])]))
  end
  val goals = map create_goal lower_triangle
  val fupdcanon_thms = map (C (curry prove) tactic) goals
  val fupdcanon_thm =
      if length fupdcanon_thms > 0 then
        save_thm(typename^"_fupdcanon",
                 LIST_CONJ (map GEN_ALL fupdcanon_thms))
      else TRUTH
  val fupdcanon_comp_thm =
      if length fupdcanon_thms > 0 then
        save_thm(typename^"_fupdcanon_comp",
                 LIST_CONJ (map munge_to_composition fupdcanon_thms))
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

    fun rng_of_dom ty = ty |> dom_rng |> #1 |> dom_rng |> #2
    fun dom_of_dom ty = ty |> dom_rng |> #1 |> dom_rng |> #1
    val value_vars =
        List.foldr
          (fn ((_,updt), sofar) =>
              let val ty = rng_of_dom (type_of updt)
              in
                mk_var_avds(app_letter ty, ty, var::sofar)::sofar
              end)
          [var] fupdfn_terms |> (fn l => List.take(l, length fields))
    fun augvar n v = let
      val (nm, ty) = dest_var v
    in
      mk_var(nm ^ Int.toString n, ty)
    end
    val vvars1 = map (augvar 1) value_vars
    val vvars2 = map (augvar 2) value_vars
    val arb = mk_arb typ
    fun foldthis ((s,upd),v,(s0,acc)) = let
      val ty = type_of v
      val K = Term.inst [alpha |-> ty, beta |-> dom_of_dom (type_of upd)] K_tm
    in
      (s @ s0,mk_comb(mk_comb(inst s0 upd, mk_comb(K, v)), acc))
    end
    val (_, lhs) = ListPair.foldr foldthis ([], var) (fupdfn_terms, value_vars)
    val (_, rhs) = ListPair.foldr foldthis ([], arb) (fupdfn_terms, value_vars)

    val (_, lit1) = ListPair.foldr foldthis ([], arb) (fupdfn_terms, vvars1)
    val (_, lit2) = ListPair.foldr foldthis ([], arb) (fupdfn_terms, vvars2)

    val literal_equality =
        GENL (var::value_vars)
             (prove(mk_eq(lhs, rhs),
                    MAP_EVERY (STRUCT_CASES_TAC o
                               C SPEC cases_thm) [arb, var] THEN
                    REWRITE_TAC [fupdfn_thm, combinTheory.K_THM]))

    val var' = inst tysigma var
    val typ' = type_of var'
    val literal_nchotomy =
        GEN var'
            (prove(list_mk_exists(value_vars, mk_eq(var', rhs)),
                   MAP_EVERY (STRUCT_CASES_TAC o C ISPEC cases_thm)
                             [arb, var'] THEN
                             REWRITE_TAC [fupdfn_thm, accessor_thm, oneone_thm,
                                          combinTheory.K_THM] THEN
                             REPEAT Unwind.UNWIND_EXISTS_TAC))

    val pred_r = mk_var_avds("P", typ' --> bool, var::value_vars)
    val P_r = mk_comb(pred_r, var')
    val P_literal = mk_comb(pred_r, rhs)
    val forall_goal = mk_eq(mk_forall(var', P_r),
                            list_mk_forall(value_vars, P_literal))
    val exists_goal = mk_eq(mk_exists(var', P_r),
                            list_mk_exists(value_vars, P_literal))
    val forall_thm =
        GEN_ALL
          (prove(forall_goal,
                 EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
                 X_GEN_TAC var' THEN
                 STRUCT_CASES_TAC (ISPEC var' literal_nchotomy) THEN
                 ASM_REWRITE_TAC []))
    val exists_thm =
        GEN_ALL
        (prove(exists_goal,
               EQ_TAC THENL [
                 DISCH_THEN (X_CHOOSE_THEN var' ASSUME_TAC) THEN
                 EVERY_TCL (map X_CHOOSE_THEN value_vars)
                           SUBST_ALL_TAC (ISPEC var' literal_nchotomy) THEN
                 MAP_EVERY EXISTS_TAC value_vars THEN ASM_REWRITE_TAC [],
                 DISCH_THEN (EVERY_TCL (map X_CHOOSE_THEN value_vars)
                                       ASSUME_TAC) THEN
                 EXISTS_TAC rhs THEN ASM_REWRITE_TAC []
               ]))

    val literal_11 =
        GENL (vvars1 @ vvars2)
             (REWRITE_RULE [accfupd_thm, combinTheory.K_THM]
                           (ISPECL [lit1, lit2] component_wise_equality))

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
    val new_simpls0 =  [accessor_thm, accfupd_thm,
                        literal_equality, literal_11, fupdfupd_thm,
                        fupdfupds_comp_thm]
  in
    if not (null fupdcanon_thms) then
      fupdcanon_thm :: fupdcanon_comp_thm :: new_simpls0
    else new_simpls0
  end
  val finfos = map (fn (ty,a,u) => {ty = ty, accessor = a, fupd = #2 u})
                   (Portable.zip3 (types, accfn_terms, fupdfn_terms))
  val new_tyinfo =
       update_tyinfo (SOME (zip fields finfos,access_defns,fupdfn_thms))
                     new_simpls tyinfo

  (* set up parsing for the record type *)
  val _ =
      let
        fun do_fupdfn (name, (_, tm)) =
            let
              val shortname = name ^ "_fupd"
              val longname = typename ^ "_" ^ shortname
            in
              Parse.overload_on(longname, tm);
              Parse.overload_on(shortname, tm)
            end
      in
        ListPair.app (fn (s,tm) => Parse.overload_on(typename ^ "_" ^ s, tm))
                     (fields, accfn_terms);
        ListPair.app add_record_field (fields, accfn_terms);
          (* overload strings of the form fld_fupd to refer to the
             real fupdate functions, which have names of the form
             type_fld_fupd.  Make sure that this overloading is
             done before the add_record_fupdate function is called
             because this will also overload this constant to the
             "artificial" constant for special printing of record
             syntax, and we want this to be preferred where
             possible. *)
        ListPair.app do_fupdfn (fields, fupdfn_terms);
        ListPair.app (fn (n,(_,t)) => add_record_fupdate(n,t))
                     (fields, fupdfn_terms);
        Parse.overload_on(typename, constructor)
      end
  val _ = DIAG ("set up parsing for type " ^ typename)
in
  new_tyinfo
end

end (* struct *)
