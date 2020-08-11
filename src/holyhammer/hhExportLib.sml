(* ========================================================================= *)
(* FILE          : hhExportLib.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportLib :> hhExportLib =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate combinTheory

val ERR = mk_HOL_ERR "hhExportLib"
type thmid = string * string

(* -------------------------------------------------------------------------
   Directory
   ------------------------------------------------------------------------- *)

val hh_dir = HOLDIR ^ "/src/holyhammer"

(* -------------------------------------------------------------------------
   Writer shortcuts
   ------------------------------------------------------------------------- *)

fun os oc s = TextIO.output (oc,s)

fun osn oc s = TextIO.output (oc,s ^ "\n")

fun oiter_aux oc sep f l = case l of
    []     => ()
  | [a]    => f oc a
  | a :: m => (f oc a; os oc sep; oiter_aux oc sep f m)

fun oiter oc sep f l = oiter_aux oc sep f l

(* -------------------------------------------------------------------------
   Higher-order to first-order type
   ------------------------------------------------------------------------- *)

fun type_vars_in_term tm =
  type_varsl (map type_of (find_terms is_const tm @ all_vars tm))

fun strip_funty_aux ty =
  if is_vartype ty then [ty] else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if Thy = "min" andalso Tyop = "fun" then
        let val (tya,tyb) = pair_of_list Args in
          tya :: strip_funty_aux tyb
        end
      else [ty]
    end

fun strip_funty_n n ty =
  if is_vartype ty orelse n <= 0 then [ty] else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if Thy = "min" andalso Tyop = "fun" then
        let val (tya,tyb) = pair_of_list Args in
          tya :: strip_funty_n (n-1) tyb
        end
      else raise ERR "strip_funty_n" ""
    end

fun strip_funty ty = case strip_funty_aux ty of
    [] => raise ERR "strip_funty" ""
  | x => (last x, butlast x)


fun full_match_type t1 t2 =
  let
    val (sub1,al) = raw_match_type t1 t2 ([],[])
    fun id_sub a = {redex = a, residue = a}
    val sub2 = map id_sub al
    fun cmp (a,b) = Type.compare (#redex a, #redex b)
  in
    dict_sort cmp (sub1 @ sub2)
  end

fun full_apply_const c =
  let
    val (imty,argtyl) = strip_funty (type_of c)
    fun f i x = mk_var ("V" ^ its i,x)
    val vl = mapi f argtyl
  in
    list_mk_comb (c,vl)
  end

fun apply_cva (cv,a) =
  let
    val argtyl = butlast (strip_funty_n a (type_of cv))
    fun f i x = mk_var ("V" ^ its i,x)
    val vl = mapi f argtyl
  in
    (list_mk_comb (cv,vl),vl)
  end

(* -------------------------------------------------------------------------
   Polymorphism and types
   ------------------------------------------------------------------------- *)

val ttype = "$tType"
val otype = "$o"

fun typearg_of_c tm =
  let
    val {Thy, Name, Ty} = dest_thy_const tm
    val mgty = type_of (prim_mk_const {Thy = Thy, Name = Name})
    val subst = full_match_type mgty Ty
  in
    map #residue subst
  end

fun typearg_of_fv tm =
  let
    val ty = snd (dest_var tm) (* a free var is only used with one type *)
    val subst = full_match_type ty ty
  in
    map #residue subst
  end

fun typearg_of_app tm =
  let
    val ty = snd (dest_var tm)
    val mgty = type_of (prim_mk_const {Thy = "bool", Name = "LET"})
    val subst = full_match_type mgty ty
  in
    map #residue subst
  end

fun typearg_of_cvapp tm =
  if is_const tm then typearg_of_c tm
  else if is_tptp_fv tm then typearg_of_fv tm
  else if is_app tm then typearg_of_app tm
  else raise ERR "typearg_of_cvapp" ""

(* -------------------------------------------------------------------------
   Names
   ------------------------------------------------------------------------- *)

fun cid_of c = let val {Name,Thy,Ty} = dest_thy_const c in (Thy,Name) end

fun name_v v = fst (dest_var v)
fun namea_v (v,a) = name_v v ^ (escape ".") ^ its a
fun name_cid (thy,name) = escape ("c." ^ thy ^ "." ^ name)
fun name_c c = name_cid (cid_of c)
fun name_cv tm =
  if is_const tm then name_c tm else
  if is_var tm then name_v tm else raise ERR "name_cv" ""

fun name_vartype ty = "A" ^ (escape (dest_vartype ty))
fun name_tyop (thy,tyop) = escape ("tyop." ^ thy ^ "." ^ tyop)
fun name_thm (thy,name) = escape ("thm." ^ thy ^ "." ^ name)

(* first-order names *)
fun namea_cid (cid,a) = name_cid cid ^ (escape ".") ^ its a
fun namea_c (c,a) = namea_cid (cid_of c,a)
fun namea_cv (tm,a) =
  if is_const tm then namea_c (tm,a) else
  if is_var tm then namea_v (tm,a) else raise ERR "namea_cv" ""

(* polymorphic / monomorphic names *)
fun name_fo_fun_mono (s,f_arg,argl) =
  if null argl then s else
  (s ^ escape "(" ^ String.concatWith (escape ",") (map f_arg argl) ^
   escape ")")

fun name_tyu_mono_aux ty =
  if is_vartype ty then name_vartype ty else
  let
    val {Args, Thy, Tyop} = dest_thy_type ty
    val tyops = name_tyop (Thy,Tyop)
  in
    name_fo_fun_mono (tyops,name_tyu_mono_aux,Args)
  end

fun name_tyu_mono ty = escape "mono." ^ name_tyu_mono_aux ty

fun add_tyargltag s cv =
  let val tyargl = typearg_of_cvapp cv in
    if null tyargl then s else
    (s ^ escape "." ^ String.concatWith (escape " ")
    (map name_tyu_mono tyargl))
  end

(* obj: constants, bound variables and free variables *)

fun namea_obj_mono (cv,a) =
  if is_tptp_bv cv then namea_v (cv,a)
  else add_tyargltag (escape "mono." ^ namea_cv (cv,a)) cv

fun namea_obj_poly (cv,a) =
  if is_tptp_bv cv then namea_v (cv,a) else namea_cv (cv,a)


(* -------------------------------------------------------------------------
   Naming theorems
   ------------------------------------------------------------------------- *)

fun name_def i thmname = escape ("def" ^ its i ^ ".") ^ thmname

fun name_arityeq (cv,a) =
  add_tyargltag ("arityeq" ^ its a ^ escape "." ^ namea_cv (cv,a)) cv

(* -------------------------------------------------------------------------
   Definitions of boolean operators
   ------------------------------------------------------------------------- *)

local open boolSyntax in

val logic_l1 = map cid_of
  [conjunction, disjunction, negation, implication, equality]
val quant_l2 = map cid_of [universal, existential]

val boolop_cval =
  [(conjunction,2),(disjunction,2),(negation,1),(implication,2),
   (equality,2),(universal,1),(existential,1)]

end (* local *)

(* -------------------------------------------------------------------------
   Higher-order theorems in a first-order embedding
   ------------------------------------------------------------------------- *)

fun mk_combin_thm thmname fvname =
  let
    val thm = DB.fetch "combin" thmname
    val tm0 = translate_thm thm
    val oper = (fst o strip_comb o lhs o snd o strip_forall) tm0
    val lhs_combin_conv = STRIP_QUANT_CONV (LHS_CONV APP_CONV_STRIPCOMB)
    val tm1 = (rhs o concl o lhs_combin_conv) tm0
    val sub = [{redex = oper, residue = mk_var (fvname,type_of oper)}]
  in
    subst sub tm1
  end

val i_thm = mk_combin_thm "I_THM" "combin_i"
val k_thm = mk_combin_thm "K_THM" "combin_k"
val s_thm = mk_combin_thm "S_THM" "combin_s"

(* combin_axioml are already translated *)
val combin_axioml = [("i_thm",i_thm),("k_thm",k_thm),("s_thm",s_thm)]

val notfalse = EQT_ELIM (last (CONJ_LIST 3 NOT_CLAUSES))
val p_axioml =
  [("truth", TRUTH), ("notfalse", notfalse), ("bool_cases_ax", BOOL_CASES_AX)]

val app_axioml = [("eq_ext", EQ_EXT)]

(* -------------------------------------------------------------------------
   Dependencies of terms
   ------------------------------------------------------------------------- *)

val id_compare = cpl_compare String.compare String.compare
val tma_compare = cpl_compare Term.compare Int.compare
val ida_compare = cpl_compare id_compare Int.compare

fun all_tyop topty =
  let
    val l = ref []
    fun loop ty =
      if is_vartype ty then () else
      let val {Args,Thy,Tyop} = dest_thy_type ty in
        l := ((Thy,Tyop),length Args) :: !l; app loop Args
      end
  in
    loop topty; (!l)
  end

fun tyop_set topty = mk_fast_set ida_compare (all_tyop topty)

fun tyopset_of_tyl tyl =
  mk_fast_set ida_compare (List.concat (map tyop_set tyl))

fun type_set tm =
  mk_type_set (map type_of (find_terms is_const tm @ all_vars tm))

fun collect_tyop tm =
  let val tyl = mk_type_set (List.concat (map type_set (atoms tm))) in
    tyopset_of_tyl tyl
  end

fun add_zeroarity cval =
  let fun f (tm,a) = if a <> 0 then [(tm,a),(tm,0)] else [(tm,a)] in
    mk_fast_set tma_compare (List.concat (map f cval))
  end

type formula_info =
  {
  cval : (term * int) list,
  tyopl : ((string * string) * int) list
  }

fun mgc_of tm =
  if is_const tm then
    let val {Thy,Name,Ty} = dest_thy_const tm in
      prim_mk_const {Thy = Thy, Name = Name}
    end
  else raise ERR "not a constant" ""

fun mgca_of (tm,a) =
  if is_const tm then
    let val {Thy,Name,Ty} = dest_thy_const tm in
      (prim_mk_const {Thy = Thy, Name = Name},a)
    end
  else (tm,a)

fun uniq_cvdef_mgc cval = mk_fast_set tma_compare (map mgca_of cval)

fun uniq_cvdef_arity cval = mk_term_set (map fst cval)

(* -------------------------------------------------------------------------
   Theorem and theory order
   ------------------------------------------------------------------------- *)

fun fetch_thm (a,b) = DB.fetch a b

fun before_elem e l = case l of
    [] => raise ERR "before_elem" ""
  | a :: m => if a = e then [] else a :: before_elem e m

fun older_than th1 (name,th2) =
  depnumber_of_thm th2 < depnumber_of_thm th1

fun add_ancestry thy = thy :: ancestry thy

(* avoid basis_emit as it contains inconsistent theorems *)
fun sorted_ancestry thyl =
  let
    fun test x = x <> "basis_emit" andalso not (mem "basis_emit" (ancestry x))
    val l = sort_thyl (mk_string_set (List.concat (map add_ancestry thyl)))
  in
    filter test l
  end

fun depo_of_thm thm =
  let
    val (b,depl1) = intactdep_of_thm thm
    val depl2 = map (split_string "Theory.") depl1
  in
    if b then SOME depl2 else NONE
  end

fun compare_namethm ((_,th1),(_,th2)) =
  Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)

(* -------------------------------------------------------------------------
   Bushy
   ------------------------------------------------------------------------- *)

fun bushy_dep thy namethml =
  let
     fun f (name,thm) = case depo_of_thm thm of
        NONE => NONE
      | SOME depl => SOME ((thy,name),([],depl))
  in
    List.mapPartial f namethml
  end

fun depo_of_thmid thmid = depo_of_thm (uncurry DB.fetch thmid)

(* -------------------------------------------------------------------------
   Chainy dependencies
   ------------------------------------------------------------------------- *)

fun thmidl_in_thy thy = map (fn (name,_) => (thy,name)) (DB.thms thy)

fun chainy_dep thyorder thy namethml =
  let
    val thyl = before_elem thy thyorder
    fun f (name,thm) =
      let
        val namethml1 = filter (older_than thm) (DB.thms thy)
        val thmidl2 = map (fn (name,_) => (thy,name)) namethml1
      in
        ((thy,name), (thyl,thmidl2))
      end
  in
    map f (DB.theorems thy)
  end

end (* struct *)
