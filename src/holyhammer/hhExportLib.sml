(* ========================================================================= *)
(* FILE          : hhExportLib.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(*                     Cezary Kaliszyk, University of Innsbruck              *)
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

fun typearg_of_const tm =
  let
    val {Thy, Name, Ty} = dest_thy_const tm
    val mgty = type_of (prim_mk_const {Thy = Thy, Name = Name})
    val subst = full_match_type mgty Ty
  in 
    map #residue subst
  end

fun typearg_of_var tm =
  let
    val ty = snd (dest_var tm)
    val subst = full_match_type ty ty
  in 
    map #residue subst
  end

fun typearg_of_appvar tm =
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

val combin_namespace_flag = ref false

fun cid_of c = let val {Name,Thy,Ty} = dest_thy_const c in (Thy,Name) end

fun name_v v = fst (dest_var v)
fun namea_v arity v = name_v v ^ (escape ".") ^ its arity
fun name_vartype ty = "A" ^ (escape (dest_vartype ty))

fun name_cid (thy,name) = 
  if !combin_namespace_flag 
  then escape ("ccombin." ^ thy ^ "." ^ name)
  else escape ("c." ^ thy ^ "." ^ name)

fun namea_cid arity cid = name_cid cid ^ (escape ".") ^ its arity
fun name_c c = name_cid (cid_of c)
fun namea_c arity c = namea_cid arity (cid_of c)

fun namea_cv arity tm =
  if is_const tm then namea_c arity tm else
  if is_var tm then namea_v arity tm else raise ERR "namea_cv" ""

fun name_tyop (thy,tyop) = escape ("ty." ^ thy ^ "." ^ tyop)
fun name_thm (thy,name) = 
  if !combin_namespace_flag
  then escape ("thmcombin" ^ "." ^ thy ^ "." ^ name)
  else escape ("thm" ^ "." ^ thy ^ "." ^ name)

(* -------------------------------------------------------------------------
   Dependencies of terms
   ------------------------------------------------------------------------- *)

val id_compare = cpl_compare String.compare String.compare
val ida_compare = cpl_compare id_compare Int.compare

fun atoms_of tm =
  if is_eq tm andalso type_of (lhs tm) = bool
    then atoms_of (lhs tm) @ atoms_of (rhs tm)
  else if is_eq tm then [lhs tm, rhs tm]
  else if is_conj tm orelse is_disj tm orelse is_imp_only tm
    then atoms_of (lhand tm) @ atoms_of (rand tm)
  else if is_neg tm    then atoms_of (rand tm)
  else if is_forall tm then atoms_of (snd (dest_forall tm))
  else if is_exists tm then atoms_of (snd (dest_exists tm))
  else [tm]

fun type_set tm = mk_type_set (map type_of (find_terms (fn _ => true) tm))
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

fun const_set tm = mk_term_set (find_terms is_const tm) 

fun required_def tml =
  let
    val tml' = mk_term_set (List.concat (map atoms_of tml))
    val tyl = mk_type_set (List.concat (map type_set tml'))
    val tyopl = mk_fast_set ida_compare (List.concat (map tyop_set tyl))
    val cl = mk_term_set (List.concat (map const_set tml'))
    val cidl = mk_fast_set id_compare (map cid_of cl)
  in
    (tyopl,cidl)
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

(* -------------------------------------------------------------------------
   Includes
   ------------------------------------------------------------------------- *)

fun include_thy oc thy = osn oc ("include('" ^ thy ^ ".ax').")
fun include_thytyopdef oc thy = osn oc ("include('" ^ thy ^ "-tyopdef.ax').")
fun include_thycdef oc thy = osn oc ("include('" ^ thy ^ "-cdef.ax').")
fun include_thyax oc thy = osn oc ("include('" ^ thy ^ "-ax.ax').")

(* -------------------------------------------------------------------------
   Bushy
   ------------------------------------------------------------------------- *)

fun write_cj_bushy dir (i1,i2,i3) (f_tyopdef,f_cdef,f_thmdef)
  formulal_of_pb (thmid,depl) =
  let 
    val file = dir ^ "/" ^ name_thm thmid ^ ".p"
    val oc = TextIO.openOut file
    val tml = formulal_of_pb (thmid,depl)  
    val (tyopl,cidl) = required_def tml
  in
    (
    app (include_thy oc) i1;
    app (f_tyopdef oc) tyopl; 
    app (include_thy oc) i2;
    app (f_cdef oc) cidl;
    app (include_thy oc) i3;
    app (f_thmdef "axiom" oc) depl; 
    f_thmdef "conjecture" oc thmid; 
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thy_bushy dir (i1,i2,i3) (f_tyopdef,f_cdef,f_thmdef)
  formulal_of_pb thy =
  let 
    val cjl = DB.theorems thy
    fun f (name,thm) = case depo_of_thm thm of
        NONE => NONE
      | SOME depl => SOME ((thy,name), depl)
    val cjdepl = List.mapPartial f cjl
  in
    print (thy ^ " "); 
    app (write_cj_bushy dir (i1,i2,i3) (f_tyopdef,f_cdef,f_thmdef)
    formulal_of_pb) cjdepl
  end

(* -------------------------------------------------------------------------
   Chainy
   ------------------------------------------------------------------------- *)

fun compare_namethm ((_,th1),(_,th2)) =
  Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)

fun write_thytyopdef dir f_tyopdef thy =
  let
    val file = dir ^ "/" ^ thy ^ "-tyopdef.ax"
    val oc = TextIO.openOut file
    fun mk_tyop (name,arity) = ((thy,name),arity) 
    val THEORY(_,t) = dest_theory thy
    val tyopl = map mk_tyop (#types t)
  in
    (app (f_tyopdef oc) tyopl; TextIO.closeOut oc)
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thycdef dir f_cdef thy =
  let
    val file = dir ^ "/" ^ thy ^ "-cdef.ax"
    val oc = TextIO.openOut file
    fun mk_id (name,_) = (thy,name)
    val THEORY(_,t) = dest_theory thy
    val cl = map mk_id (#consts t)
  in
    (app (f_cdef oc) cl; TextIO.closeOut oc)
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thyax dir f_thmdef thy =
  let
    val file = dir ^ "/" ^ thy ^ "-ax.ax"
    val oc = TextIO.openOut file
    fun mk_id (name,_) = (thy,name)
    val THEORY(_,t) = dest_theory thy
    val axl = map mk_id (dict_sort compare_namethm (DB.thms thy)) 
  in
    (app (f_thmdef "axiom" oc) axl; TextIO.closeOut oc)
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_cj_chainy dir (i1,i2,i3) f_thmdef (thyl,thy) (name,thm) =
  let 
    val file = dir ^ "/" ^ name_thm (thy,name) ^ ".p"
    val oc = TextIO.openOut file
    fun mk_id (x,_) = (thy,x)
    val axl1 = filter (older_than thm) (DB.thms thy)
    val axl2 = map mk_id (dict_sort compare_namethm axl1)
  in
    (
    app (include_thy oc) i1;
    app (include_thytyopdef oc) (thyl @ [thy]);
    app (include_thy oc) i2;
    app (include_thycdef oc) (thyl @ [thy]);
    app (include_thy oc) i3;
    app (include_thyax oc) thyl;
    app (f_thmdef "axiom" oc) axl2; 
    f_thmdef "conjecture" oc (thy,name); 
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thy_chainy dir (i1,i2,i3) f_thmdef thyl thy =
  let val thyl_before = before_elem thy thyl in
    print (thy ^ " ");
    app (write_cj_chainy 
      dir (i1,i2,i3) f_thmdef (thyl_before,thy)) (DB.theorems thy)
  end


end (* struct *)

(*

fun tf1_top_cdef oc arity (tfname,ty) =
  (os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":");
   tf1_tyquant_type oc arity ty; osn oc ").")
(* -------------------------------------------------------------------------
   Combinator for making it less theorem decreasing. (i.e. complete)
   ------------------------------------------------------------------------- *)

fun write_combin (f_constdef,f_thmdef) dir = 
  let
    val file = dir ^ "/combin-extra.ax"
    val oc = TextIO.openOut file
  in
    let
      val _ = combin_extra_flag := true
      val cl0 = ["S","K","I"]
      val axl0 = map (fn x => x ^ "_DEF") cl0
      val thy = "combin"
      val THEORY(_,t) = dest_theory thy
      val cl1 = #consts t
      val cl2 = filter (fn x => mem (fst x) cl0) cl1
      val _ = app (f_constdef oc thy) cl2
      val axl1 = filter (fn x => mem (fst x) axl0) (DB.definitions thy)
      val axl2 = map (fn x => (x,"axiom")) axl1
    in
      app (f_thmdef oc thy) axl2;
      combin_extra_flag := false;
      TextIO.closeOut oc
    end 
    handle Interrupt => 
    (TextIO.closeOut oc; combin_extra_flag := false; raise Interrupt)
  end 
*)
