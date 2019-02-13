(* ========================================================================= *)
(* FILE          : hhExportLib.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportLib :> hhExportLib =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate

val ERR = mk_HOL_ERR "hhExportLib"

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
      else [ty]
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

(* -------------------------------------------------------------------------
   Names
   ------------------------------------------------------------------------- *)

fun cid_of c = let val {Name,Thy,Ty} = dest_thy_const c in (Thy,Name) end

fun name_v v = fst (dest_var v)
fun namea_v (v,a) = name_v v ^ (escape ".") ^ its a
fun name_vartype ty = "A" ^ (escape (dest_vartype ty))

fun name_cid (thy,name) = escape ("c." ^ thy ^ "." ^ name)

fun namea_cid (cid,a) = name_cid cid ^ (escape ".") ^ its a
fun name_c c = name_cid (cid_of c)
fun namea_c (c,a) = namea_cid (cid_of c,a)

fun namea_cv (tm,a) =
  if is_const tm then namea_c (tm,a) else
  if is_var tm then namea_v (tm,a) else raise ERR "namea_cv" ""

fun name_tyop (thy,tyop) = escape ("tyop." ^ thy ^ "." ^ tyop)
fun name_thm (thy,name) = escape ("thm." ^ thy ^ "." ^ name)


(* -------------------------------------------------------------------------
   Definitions of boolean operators
   ------------------------------------------------------------------------- *)

val logic_l1 = map cid_of [``$/\``,``$\/``,``$~``,``$==>``,
  ``$= : 'a -> 'a -> bool``]
val quant_l2 = map cid_of [``$! : ('a -> bool) -> bool``,
  ``$? : ('a -> bool) -> bool``]

val boolop_cval = 
  [
   (``$/\``,2),(``$\/``,2),(``$~``,1),(``$==>``,2),
   (``$= : 'a -> 'a -> bool``,2),
   (``$! : ('a -> bool) -> bool``,1),(``$? : ('a -> bool) -> bool``,1)
  ]


(* -------------------------------------------------------------------------
   Higher-order theorems in a first-order embedding
   ------------------------------------------------------------------------- *)

fun mk_combin_thm thmname fvname =
  let 
    val thm = DB.fetch "combin" thmname
    val (tm0,defl) = fof_translate_thm thm
    val _ = if null defl then () else raise ERR "mk_combin_thm" ""
    val oper = (fst o strip_comb o lhs o snd o strip_forall) tm0
    val lhs_combin_conv = STRIP_QUANT_CONV (LHS_CONV APP_CONV_AUX)
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

fun tyop_set topty = 
  let 
    val l = ref [] 
    fun loop ty = 
      if is_vartype ty then () else
      let val {Args,Thy,Tyop} = dest_thy_type ty in
        l := ((Thy,Tyop),length Args) :: !l; app loop Args 
      end
  in 
    loop topty; mk_fast_set ida_compare (!l)
  end

fun tyopl_of_tyl tyl = 
  mk_fast_set ida_compare (List.concat (map tyop_set tyl))

fun collect_tyop tm = 
  let 
    fun type_set tm = map type_of (find_terms is_const tm @ all_vars tm)  
    val tyl = mk_type_set (List.concat (map type_set (atoms tm))) 
  in
    tyopl_of_tyl tyl
  end

fun add_zeroarity cval =
  let fun f (tm,a) = if a <> 0 then [(tm,a),(tm,0)] else [(tm,a)] in
    mk_fast_set tma_compare (List.concat (map f cval))
  end

type formula_info = {
  thmid : string * string,
  cval : (term * int) list,
  tyopl : ((string * string) * int) list
  }

fun mgc_of (tm,a) =
  if is_const tm then 
    let val {Thy,Name,Ty} = dest_thy_const tm in
      (prim_mk_const {Thy = Thy, Name = Name},a)
    end
  else (tm,a)

fun uniq_cvdef_mgc cval = mk_fast_set tma_compare (map mgc_of cval)

fun zeroed_arity (c,a) = (c,0)
 
fun uniq_cvdef_arity cval = mk_fast_set tma_compare (map zeroed_arity cval) 

fun formula_info f_translate (thy,name) =
  let 
    val thm = DB.fetch thy name
    val (formula,defl) = f_translate thm
    val tml = formula :: defl 
    val cval = mk_fast_set tma_compare (List.concat (map collect_arity tml))
    val tyopl = mk_fast_set ida_compare (List.concat (map collect_tyop tml))
  in
    {thmid = (thy,name), cval = add_zeroarity cval, tyopl = tyopl}
  end

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
fun sorted_ancestry thyl = 
  sort_thyl (mk_string_set (List.concat (map add_ancestry thyl)))

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

fun write_cj dir f_translate uniq_def (tyopl_extra,cval_extra)
  (f_tyopdef_extra,
   f_tyopdef,f_cvdef_extra,f_cvdef,f_thmdef_extra,f_arityeq,f_thmdef)
  (thmid,depl) =
  let 
    val file = dir ^ "/" ^ name_thm thmid ^ ".p"
    val oc = TextIO.openOut file
    val cjinfo = formula_info f_translate thmid
    val axinfol = map (formula_info f_translate) depl
    val tyopl = 
      mk_fast_set ida_compare 
      (List.concat (tyopl_extra :: #tyopl cjinfo :: map #tyopl axinfol))
    val cval = 
      mk_fast_set tma_compare 
      (List.concat (cval_extra :: #cval cjinfo :: map #cval axinfol))
  in
    (
    f_tyopdef_extra oc;
    app (f_tyopdef oc) tyopl;
    f_cvdef_extra oc;
    app (f_cvdef oc) (uniq_def cval);
    f_thmdef_extra oc;
    app (f_arityeq oc) cval;
    app (f_thmdef "axiom" oc) depl; 
    f_thmdef "conjecture" oc thmid; 
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun add_bushy_dep thy namethml =
  let
     fun f (name,thm) = case depo_of_thm thm of
        NONE => NONE
      | SOME depl => SOME ((thy,name), depl)
  in
    List.mapPartial f namethml
  end

fun write_thy_bushy dir a b c d thy =
  let val cjdepl = add_bushy_dep thy (DB.theorems thy) in
    print (thy ^ " "); app (write_cj dir a b c d) cjdepl
  end

fun thmidl_in_thyl thyl =
  let fun f thy = map (fn (name,_) => (thy,name)) (DB.thms thy) in
    List.concat (map f thyl)
  end

fun add_chainy_dep thyorder thy namethml =
  let
    val thyl = before_elem thy thyorder
    val thmidl1 = thmidl_in_thyl thyl
    fun f (name,thm) = 
      let 
        val namethml1 = filter (older_than thm) namethml
        val thmidl2 = map (fn (name,_) => (thy,name)) namethml1
      in
        ((thy,name), thmidl1 @ thmidl2)
      end
  in
    map f namethml
  end

fun write_thy_chainy dir thyorder a b c d thy =
  let val cjdepl = add_chainy_dep thyorder thy (DB.theorems thy) in
    print (thy ^ " "); app (write_cj dir a b c d) cjdepl
  end

end (* struct *)
