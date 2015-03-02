structure constrFamiliesLib :> constrFamiliesLib =
struct

open HolKernel boolLib simpLib bossLib

(***************************************************)
(* Auxiliary definitions                           *)
(***************************************************)


fun failwith f x = 
 raise (mk_HOL_ERR "constrFamiliesLib" f x)

fun variants used_vs vs = let
 val (_, vs') = foldl (fn (v, (used_vs, vs')) =>
    let val v' = variant used_vs v
    in (v'::used_vs, v'::vs') end) (used_vs, []) vs
in
  List.rev vs'
end

(* list_mk_comb with build-in beta reduction *)
fun list_mk_comb_subst (c, args) = (case args of
    [] => c
  | (a::args') => let
      val (v, c') = dest_abs c      
    in
      list_mk_comb_subst (subst [v |-> a] c', args')
    end handle HOL_ERR _ =>
      list_mk_comb_subst (mk_comb (c, a), args')
)

(*-----------------------------------------*)
(* normalise free type variables in a type *)
(* in order to use it as a map key         *)
(*-----------------------------------------*)

fun next_ty ty = mk_vartype(Lexis.tyvar_vary (dest_vartype ty));

fun normalise_ty ty = let
  fun recurse (acc as (dict,usethis)) tylist =
      case tylist of
        [] => acc
      | ty :: rest => let
        in
          if is_vartype ty then
            case Binarymap.peek(dict,ty) of
                NONE => recurse (Binarymap.insert(dict,ty,usethis),
                                 next_ty usethis)
                                rest
              | SOME _ => recurse acc rest
          else let
              val {Args,...} = dest_thy_type ty
            in
              recurse acc (Args @ rest)
            end
        end
  val (inst0, _) = recurse (Binarymap.mkDict Type.compare, Type.alpha) [ty]
  val inst = Binarymap.foldl (fn (tyk,tyv,acc) => (tyk |-> tyv)::acc)
                             []
                             inst0
in
  Type.type_subst inst ty
end


fun base_ty ty = let
  val (tn, targs) = dest_type ty
  val targs' = List.rev (snd (List.foldl (fn (_, (v, l)) => (next_ty v, v::l)) (Type.alpha, []) targs)) 
in
  mk_type (tn, targs')
end


(*------------------------*)
(* Encoding theorem lists *)
(*------------------------*)

fun encode_term_opt_list tl = let
  val tl' = List.map (fn t => markerSyntax.mk_label ("THM_PART", Option.getOpt (t, T))) tl
  val t = list_mk_conj tl'
  val thm = (markerLib.DEST_LABELS_CONV THENC REWRITE_CONV []) t
in
  thm
end

fun decode_thm_opt_list combined_thm = let
  fun process_thm thm = let
    val thm' = CONV_RULE markerLib.DEST_LABEL_CONV thm
  in
    if (aconv (concl thm') T) then NONE else SOME thm'
  end

  val thms = CONJUNCTS combined_thm
  val thms' = List.map process_thm thms
in
  thms'
end

fun set_goal_list tl = let
  val thm = encode_term_opt_list tl 
in
  proofManagerLib.set_goal ([], rhs (concl thm))
end


fun prove_list (tl, tac) = let
  val thm = encode_term_opt_list tl
  val thm2 = prove (rhs (concl thm), tac)
  val thm3 = EQ_MP (GSYM thm) thm2
in
  decode_thm_opt_list thm3
end



(***************************************************)
(* Constructors                                    *)
(***************************************************)

(* A constructor is a combination of a term with
   a list of names for all it's arguments *)
datatype constructor = CONSTR of term * (string list)

fun mk_constructor t args = CONSTR (t, args)

fun constructor_is_const (CONSTR (_, sl)) = null sl

fun mk_constructor_term vs (CONSTR (c, args)) = let
  val (arg_tys, b_ty) = strip_fun (type_of c)
  val _ = if (length arg_tys < length args) then
    failwith "check_constructor" "too many argument names given" else ()

  val typed_args = zip args (List.take (arg_tys, length args))
  val arg_vars = List.map mk_var typed_args
  val arg_vars' = variants vs arg_vars
  val t = list_mk_comb_subst (c, arg_vars')
in
  (t, arg_vars')
end

(* Multiple constructors for a single type are usually
   grouped. These can be exhaustive or not. *)
type constructorList = {
  cl_type          : hol_type,
  cl_constructors  : constructor list,
  cl_is_exhaustive : bool
}

fun mk_constructorList is_exhaustive constrs = let
  val ts = List.map (fst o (mk_constructor_term [])) constrs
  val _ = if null ts then failwith "make_constructorList" "no constructors given" else ()
  val ty = type_of (hd ts)
  val _ = if (Lib.all (fn t => type_of t = ty) ts) then () else
     failwith "make_constructorList" "types of constructors don't match"
in
  { cl_type          = ty,
    cl_constructors  = constrs,
    cl_is_exhaustive = is_exhaustive }:constructorList
end


(***************************************************)
(* Constructor Families                            *)
(***************************************************)

(* Contructor families are lists of constructors with
   a cass-split constant + extra theorems. 
*)

type constructorFamily = {
  constructors  : constructorList,
  case_const    : term,
  one_one_thm   : thm option,
  distinct_thm  : thm option,
  case_split_thm: thm,
  nchotomy_thm  : thm option
}

fun constructorFamily_get_rewrites (cf : constructorFamily) = 
  case (#one_one_thm cf, #distinct_thm cf) of
      (NONE, NONE) => TRUTH
    | (SOME thm1, NONE) => thm1
    | (NONE, SOME thm2) => thm2
    | (SOME thm1, SOME thm2) => CONJ thm1 thm2

fun constructorFamily_get_case_split (cf: constructorFamily) =
  (#case_split_thm cf)

fun constructorFamily_get_nchotomy_thm_opt (cf: constructorFamily) =
  (#nchotomy_thm cf)

(* Test datatype 
val _ = Datatype `test_ty =
    A 
  | B 'b
  | C bool 'a bool
  | D num bool`

val SOME constrL = constructorList_of_typebase ``:('a, 'b) test_ty`` 
val case_const = TypeBase.case_const_of ``:('a, 'b) test_ty`` 

val constrL = make_constructorList false [(``{}:'a set``, []), (``\x:'a. {x}``, ["x"])]

val set_CASE_def = zDefine `
  set_CASE s c_emp c_sing c_else =
    (if s = {} then c_emp else (
     if (FINITE s /\ (CARD s = 1)) then c_sing (CHOICE s) else
     c_else))`

val case_const = ``set_CASE``
*)


fun mk_one_one_thm_term_opt (constrL : constructorList) = let
  fun mk_one_one_single cr = let
    val (l, vl) = mk_constructor_term [] cr
    val (r, vr) = mk_constructor_term vl cr
    val lr = mk_eq (l, r)
    val eqs = list_mk_conj (List.map mk_eq (zip vl vr))
    val b = mk_eq (lr, eqs)
  in
    list_mk_forall (vl @ vr, b)
  end

  val constrs = filter (not o constructor_is_const) (#cl_constructors constrL)
  val eqs = map mk_one_one_single constrs
in
  if (null eqs) then NONE else SOME (list_mk_conj eqs)
end


fun mk_distinct_thm_term_opt (constrL : constructorList) = let
  val constrs = #cl_constructors constrL
  val all_pairs = flatten (List.map (fn x =>
     List.map (fn y => (x, y)) constrs) constrs)
  val dist_pairs = List.filter (fn (CONSTR (c1, _), CONSTR (c2, _)) =>
    not (aconv c1 c2)) all_pairs
  fun mk_distinct_single (cr1, cr2) = let
    val (l, vl) = mk_constructor_term [] cr1
    val (r, vr) = mk_constructor_term vl cr2
    val lr = mk_neg (mk_eq (l, r))
  in
    list_mk_forall (vl @ vr, lr)
  end

  val eqs = map mk_distinct_single dist_pairs
in
  if (null eqs) then NONE else SOME (list_mk_conj eqs)
end


fun mk_case_expand_thm_term case_const (constrL : constructorList) = let
  val (arg_tys, res_ty) = strip_fun (type_of case_const)
  val split_arg = mk_var ("x", hd arg_tys)
  val split_fun = mk_var ("ff", hd arg_tys --> res_ty)

  fun mk_arg cr = let
    val (b, vs) = mk_constructor_term [split_fun,split_arg] cr
    val b' = mk_comb (split_fun, b)
  in
    list_mk_abs (vs, b')
  end

  val args = List.map mk_arg (#cl_constructors constrL)
  val args = if (#cl_is_exhaustive constrL) then args else
    args@[(mk_abs (split_arg, mk_comb(split_fun, split_arg)))]

  val r = list_mk_comb (case_const, split_arg::args)
  val l = mk_comb (split_fun, split_arg)

  val eq = list_mk_forall ([split_fun, split_arg], mk_eq (l, r))
in
  eq
end

fun mk_nchotomy_thm_term_opt (constrL : constructorList) = 
  if not (#cl_is_exhaustive constrL) then NONE else let
    val v = mk_var ("x", #cl_type constrL)

    fun mk_disj cr = let
      val (b, vs) = mk_constructor_term [v] cr
      val eq = mk_eq (v, b)
    in
      list_mk_exists (vs, eq)
    end
  
    val eqs = List.map mk_disj (#cl_constructors constrL)
    val eqs_t = list_mk_disj eqs
  in
    SOME (mk_forall (v, eqs_t))
  end;


fun mk_constructorFamily_terms case_const constrL = let
  val t1 = mk_one_one_thm_term_opt constrL 
  val t2 = mk_distinct_thm_term_opt constrL
  val t3 = SOME (mk_case_expand_thm_term case_const constrL)
  val t4 = mk_nchotomy_thm_term_opt constrL
in
  [t1, t2, t3, t4]
end

fun get_constructorFamily_proofObligations (constrL, case_const) = let
  val ts = mk_constructorFamily_terms case_const constrL 
  val thm = encode_term_opt_list ts
in
  rhs (concl thm)
end

fun set_constructorFamily (constrL, case_const) =
  set_goal_list (mk_constructorFamily_terms case_const constrL)

fun mk_constructorFamily (constrL, case_const, tac) = let
  val thms = prove_list (mk_constructorFamily_terms case_const constrL,  tac)
in
  {
    constructors   = constrL,
    case_const     = case_const,
    one_one_thm    = el 1 thms,
    distinct_thm   = el 2 thms,
    case_split_thm = valOf (el 3 thms),
    nchotomy_thm   = el 4 thms
  }:constructorFamily
end


(***************************************************)
(* Connection to typebase                          *)
(***************************************************)

(* given a type try to extract the constructors of a type
   from typebase. Do not use the default type-base functions
   for this but destruct the nchotomy_thm in order to get
   the default argument names as well. *)
fun constructorList_of_typebase ty = 
  if null (TypeBase.constructors_of ty) then NONE else let
  val nchotomy_thm = TypeBase.nchotomy_of ty
  val eqs = strip_disj (snd (dest_forall (concl nchotomy_thm)))

  fun dest_eq eq = let
    val (_, b) = strip_exists eq
    val (c, args) = strip_comb (rhs b)
    val args' = List.map (fst o dest_var) args
  in
    CONSTR (c, args')
  end

  val constrs = List.map dest_eq eqs
in
  SOME ({ cl_type          = ty,
    cl_constructors  = constrs,
    cl_is_exhaustive = true }:constructorList)
end

fun constructorFamily_of_typebase ty = let
  val crL = valOf (constructorList_of_typebase ty)
    handle Option => failwith "constructorList_of_typebase" "not a datatype"
  val case_split_tm = TypeBase.case_const_of ty
  val thm_distinct = TypeBase.distinct_of ty
  val thm_one_one = TypeBase.one_one_of ty
  val thm_case = TypeBase.case_def_of ty

  (*  set_constructorFamily (crL, case_split_tm) *)
  val cf = mk_constructorFamily (crL, case_split_tm, 
    SIMP_TAC std_ss [thm_distinct, thm_one_one] THEN
    REPEAT STRIP_TAC THEN (
      Cases_on `x` THEN
      SIMP_TAC std_ss [thm_distinct, thm_one_one, thm_case]
    )
  )
in
  cf
end


(***************************************************)
(* Collections of constructorFamilies +            *)
(* extra matching info                             *)
(***************************************************)

type pmatch_compile_fun = (term list * term) list -> (thm * simpLib.ssfrag) option

val typeConstrFamsDB = ref (TypeNet.empty : constructorFamily TypeNet.typenet)

type pmatch_compile_db = {
  pcdb_compile_funs  : pmatch_compile_fun list,
  pcdb_constrFams    : (constructorFamily list) TypeNet.typenet,
  pcdb_ss            : simpLib.ssfrag
}

val empty : pmatch_compile_db = {
  pcdb_compile_funs = [],
  pcdb_constrFams = TypeNet.empty,
  pcdb_ss = (simpLib.rewrites [])
}

val thePmatchCompileDB = ref empty

fun lookup_typeBase_constructorFamily ty = let
  val b_ty = base_ty ty  
in
  SOME (b_ty, TypeNet.find (!typeConstrFamsDB, b_ty)) handle 
     NotFound => let
       val cf = constructorFamily_of_typebase b_ty
       val net = !typeConstrFamsDB
       val net'= TypeNet.insert (net, b_ty, cf)
       val _ = typeConstrFamsDB := net'
     in
       SOME (b_ty, cf)
     end    
end handle HOL_ERR _ => NONE

fun lookup_constructorFamilies (db : pmatch_compile_db) col = let
  val _ = if (List.null col) then (failwith "constructorFamiliesLib" "lookup_constructorFamilies: null col") else ()
  val ty = type_of (snd (hd col))

  val cts_fams = let
    val cts_fams = TypeNet.match (#pcdb_constrFams db, ty)
    val cts_fams' = Lib.flatten (List.map (fn (ty, l) =>
       List.map (fn cf => (ty, cf)) l) cts_fams)
    val cty_opt = lookup_typeBase_constructorFamily ty  
    val cty_l = case cty_opt of
         NONE => []
       | SOME (ty, cf) => [(ty, cf)]
  in cts_fams' @ cty_l end
in
  case cts_fams of
      [] => NONE
    | cs::_ => SOME cs
end;


fun pmatch_compile_db_compile db col = (
  if (List.null col) then failwith "pmatch_compile_db_compile" "col 0" else
  case (get_first (fn f => f col handle HOL_ERR _ => NONE) (#pcdb_compile_funs db)) of
    SOME r => SOME r | NONE => (
  case lookup_constructorFamilies db col of
    NONE => NONE | SOME (ty, cf) => (
    let
      val ty_s = match_type ty (type_of (snd (hd col)))
      val thm = constructorFamily_get_case_split cf
      val thm' = INST_TYPE ty_s thm
    in
      SOME (thm', merge_ss [(#pcdb_ss db), simpLib.rewrites [
        (constructorFamily_get_rewrites cf)]])
    end
  )));

fun pmatch_compile_db_add_ssfrag (db : pmatch_compile_db) ss = {
  pcdb_compile_funs = #pcdb_compile_funs db,
  pcdb_constrFams = #pcdb_constrFams db,
  pcdb_ss = (simpLib.merge_ss [#pcdb_ss db, ss])
} : pmatch_compile_db

fun pmatch_compile_db_register_ssfrag ss =
  thePmatchCompileDB := pmatch_compile_db_add_ssfrag (!thePmatchCompileDB) ss

fun pmatch_compile_db_add_compile_fun (db : pmatch_compile_db) cf = {
  pcdb_compile_funs = cf::(#pcdb_compile_funs db),
  pcdb_constrFams = #pcdb_constrFams db,
  pcdb_ss = #pcdb_ss db
} : pmatch_compile_db

fun pmatch_compile_db_register_compile_fun cf =
  thePmatchCompileDB := pmatch_compile_db_add_compile_fun (!thePmatchCompileDB) cf

fun pmatch_compile_db_add_constrFam (db : pmatch_compile_db) cf = {
  pcdb_compile_funs = #pcdb_compile_funs db,
  pcdb_constrFams = let
    val cl = (#constructors cf)
    val ty = #cl_type cl
    val net = #pcdb_constrFams db
    val cfs = TypeNet.find (net, ty) handle NotFound => []
    val net' = TypeNet.insert (net, ty, cf::cfs)
  in
    net'
  end,
  pcdb_ss = #pcdb_ss db
} : pmatch_compile_db

fun pmatch_compile_db_register_constrFam cf =
  thePmatchCompileDB := pmatch_compile_db_add_constrFam (!thePmatchCompileDB) cf



(***************************************************)
(* complilation funs                               *)
(***************************************************)

val COND_CONG_APPLY = prove (``(if (x:'a) = c then (ff x):'b else ff x) =
  (if x = c then ff c else ff x)``,
Cases_on `x = c` THEN ASM_REWRITE_TAC[])

fun literals_compile_fun (col:(term list * term) list) = let

  fun extract_literal ((vs, c), ts) = let
     val vars = FVL [c] empty_tmset
     val is_lit = not (List.exists (fn v => HOLset.member (vars, v)) vs)
  in 
    if is_lit then HOLset.add(ts,c) else 
      (if is_var c then ts else failwith "" "extract_literal")
  end

  val ts = List.foldl extract_literal empty_tmset col
  val lits = HOLset.listItems ts
  val _ = if (List.null lits) then (failwith "" "no lits") else ()

  val rty = gen_tyvar ()
  val lit_ty = type_of (snd (List.hd col))
  val split_arg = mk_var ("x", lit_ty)
  val split_fun = mk_var ("ff", lit_ty --> rty)
  val arg = mk_comb (split_fun, split_arg)


  fun mk_expand_thm lits = case lits of
      [] => REFL arg
    | (l :: lits') => let
         val b = mk_eq (split_arg, l)
         val thm0 = GSYM (ISPEC arg (SPEC b COND_ID))
         val thm1 = CONV_RULE (RHS_CONV (REWR_CONV COND_CONG_APPLY)) thm0
         val thm2a = mk_expand_thm lits'
         val thm2 = CONV_RULE (RHS_CONV (RAND_CONV (K thm2a))) thm1
      in
         thm2
      end
    
  val thm0 = mk_expand_thm lits
  val thm1 = GEN split_fun (GEN split_arg thm0)
in
  SOME (thm1, simpLib.rewrites [Cong boolTheory.COND_CONG])
end

val _ = pmatch_compile_db_register_compile_fun literals_compile_fun

end
