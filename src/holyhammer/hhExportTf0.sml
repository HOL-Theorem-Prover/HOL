(* ========================================================================= *)
(* FILE          : hhExportTf0.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportTf0 :> hhExportTf0 =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate hhExportLib

val ERR = mk_HOL_ERR "hhExportTf0"

(* -------------------------------------------------------------------------
   FOF names : variables escaped by translate_tm
   ------------------------------------------------------------------------- *)

fun tf0_var arity v = fst (dest_var v) ^ "_" ^ int_to_string arity

fun tf0_const arity c =
  let val {Name, Thy, Ty} = dest_thy_const c in
    escape ("c" ^ int_to_string arity ^ "." ^ Thy ^ "." ^ Name)
  end

fun tf0_constvar arity tm =
  if is_const tm then tf0_const arity tm
  else if is_var tm then tf0_var arity tm
  else raise raise ERR "tf0_constvar" ""

fun tf0_vardomain ty = "A" ^ (escape (dest_vartype ty))

fun tf0_opdomain ty =
  let val {Args, Thy, Tyop} = dest_thy_type ty in
    escape ("ty" ^ "." ^ Thy ^ "." ^ Tyop)
  end

fun tf0_thm (thy,name) = escape ("thm" ^ "." ^ thy ^ "." ^ name)

(* -------------------------------------------------------------------------
   FOF terms
   ------------------------------------------------------------------------- *)

(* every fof type is a unit type *)

val itype = "$i" (* use to represent the result of s *)

fun tf0_type n =
  if n <= 0 then itype else
  if n = 1 then itype ^ " > " ^ itype
  else 
    "(" ^ String.concatWith " * " (List.tabulate (n,fn _ => itype)) ^ ")"
    ^ " > " ^ itype

fun tf0_domain oc ty =
  if is_vartype ty then os oc (tf0_vardomain ty) else
    let
      val {Args, Thy, Tyop} = dest_thy_type ty
      val tyops = tf0_opdomain ty
    in
      os oc tyops;
      if null Args then ()
      else (os oc "("; oiter oc "," tf0_domain Args; os oc ")")
    end

fun tf0_domain_string oc ty =
  if is_vartype ty then os oc (tf0_vardomain ty) else
    let
      val {Args, Thy, Tyop} = dest_thy_type ty
      val tyops = tf0_opdomain ty
    in
      os oc tyops;
      if null Args then ()
      else (os oc (escape "( "); oiter oc (escape " , ") 
            tf0_domain_string Args; os oc (escape " )"))
    end

fun tf0_term oc tm =
  let 
    val (rator,argl) = strip_comb tm
    val ty = type_of tm
  in
    os oc "s("; tf0_domain oc ty; os oc ",";
    (
    if polymorphic ty 
    then tf0_apply oc (rator,argl)
    else 
      (os oc "i_"; tf0_domain_string oc ty; os oc "("
       tf0_apply oc (rator,argl)
       os oc ")")
    );
    os oc ")"
  end
and tf0_apply oc (rator,argl) =
  (
  os oc (tf0_constvar (length argl) rator);
  if null argl then ()
  else (os oc "("; oiter oc "," tf0_term argl; os oc ")")
  )

fun tf0_pred oc tm =
  if is_forall tm then tf0_quant oc "!" (strip_forall tm)
  else if is_exists tm then tf0_quant oc "?" (strip_exists tm)
  else if is_conj tm then tf0_binop oc "&" (dest_conj tm)
  else if is_disj tm then tf0_binop oc "|" (dest_disj tm)
  else if is_imp_only tm then tf0_binop oc "=>" (dest_imp tm)
  else if is_neg tm then
    (os oc "~ ("; tf0_pred oc (dest_neg tm); os oc ")")
  else if is_eq tm then
    let val (l,r) = dest_eq tm in
      if must_pred l orelse must_pred r (* optimization *)
      then tf0_binop oc "<=>" (l,r)
      else (tf0_term oc l; os oc " = "; tf0_term oc r)
    end
  else (os oc "p("; tf0_term oc tm; os oc ")")
and tf0_binop oc s (l,r) =
  (os oc "("; tf0_pred oc l; os oc (" " ^ s ^ " "); 
   tf0_pred oc r; os oc ")")
and tf0_quant oc s (vl,bod) =
  (os oc s; os oc "[";
   oiter oc ", " (fn x => (fn v => os x (tf0_var 0 v))) vl;
   os oc "]: "; tf0_pred oc bod)

fun type_vars_in_term tm =
  type_varsl (map type_of (find_terms is_const tm @ all_vars tm))

fun tf0_formula oc tm =
  let val tvl = type_vars_in_term tm in
    if null tvl then ()
    else (os oc "!["; oiter oc "," tf0_domain tvl; os oc "]: ");
    tf0_pred oc tm
  end

(* -------------------------------------------------------------------------
   FOF definitions
   ------------------------------------------------------------------------- *)

val tffpar = "tff("

(*
fun tf0_tydef oc thy (tyop,arity) =
  let val tfname = tf1b_tyop (thy,tyop) in
    os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":" ^ ttype);
    os oc (tf1_ttype arity); osn oc ")."
  end
*)

fun tf0_tydef oc thy (tyop,arity) = ()

fun tf0_nameadef oc (name,arity) =
  (
  os oc (tffpar ^ name ^ ",type," ^ name ^ ":");
  os oc (tf0_type arity); osn oc ")."
  )

fun tf0_nametysdef oc (name,tys) =
  (
  os oc (tffpar ^ name ^ ",type," ^ name ^ ":");
  os oc tys; osn oc ")."
  )

fun tf0_constdef_arity oc (c,arity) =
  let val tfname = tf0_const arity c in
    os oc (tffpar ^ tfname ^ ",type," ^ tfname ^ ":");
    os oc (tf0_type arity); osn oc ").";
    (if arity = 0 then () else 
    let 
      val eq = concl (mk_arity_eq c arity) 
      val arity_prefix = escape ("arity" ^ its arity ^ ".")
    in
      (os oc (tffpar ^ arity_prefix ^ tfname ^ ",axiom,");
       tf0_formula oc eq; osn oc ").")
    end)
  end

fun tf0_constdef oc (thy,name) =
  let
    val c = prim_mk_const {Thy = thy, Name = name}
    val ty = type_of c
    val maxarity = length (snd (strip_funty ty))
    fun f n = tf0_constdef_arity oc (c,n)
  in
    ignore (List.tabulate (maxarity + 1, f))
  end

fun tf0_vardef_arity oc (v,arity) =
  if fst (dest_var v) = "app" then () else 
  let val tfname = tf0_var arity v in
    os oc (tffpar ^ tfname ^ ",type," ^ tfname ^ ":");
    os oc (tf0_type arity); osn oc ").";
    (if arity = 0 then () else
    let
      val eq = concl (mk_arity_eq v arity) 
      val arity_prefix = escape ("arity" ^ its arity ^ ".")
    in
      os oc (tffpar ^ arity_prefix ^ tfname ^ ",axiom,");
      tf0_formula oc eq; osn oc ")."
    end)
  end

(* define type of app,p,s *)
fun tf0_casterdef oc =
  (
  app (tf0_nameadef oc) [("app_2",2),("s",2)];
  tf0_nametysdef oc ("p","$i > $o")
  )
(* free variables are used for new constants *)
(* type of free variable is always most general type except for app *)
fun tf0_vardef oc v = 
  let 
    val ty = snd (dest_var v)
    val maxarity = length (snd (strip_funty ty))
    fun f n = tf0_vardef_arity oc (v,n)
  in
    ignore (List.tabulate (maxarity + 1, f))
  end

fun tf0_prep_thm thm = translate_tm (concl (DISCH_ALL thm))

fun tf0_thmdef oc thy ((name,thm),role) =
  let 
    val tml = tf0_prep_thm thm
    val vl = free_vars_lr (list_mk_conj (rev tml))
    val (cj,defl) = (hd tml, rev (tl tml))
    fun f i def = 
      (
      os oc (tffpar ^ escape ("fthm" ^ its i ^ ".") ^
      (tf0_thm (thy,name)) ^ ",axiom,");
      tf0_formula oc def; osn oc ")."
      )
  in
    app (tf0_vardef oc) vl;
    ignore (mapi f defl);
    os oc (tffpar ^ (tf0_thm (thy,name)) ^ "," ^ role ^ ",");
    tf0_formula oc cj; 
    osn oc ")."
  end
  

(* -------------------------------------------------------------------------
   Export standard
   ------------------------------------------------------------------------- *)

val tf0_dir = hh_dir ^ "/export_tf0"

fun tf0_export thyl =
  let
    val file = tf0_dir ^ "/theory_order.info"
    val fl = (tf0_tydef, tf0_constdef, tf0_thmdef, tf0_thm)
    val thyl = sorted_ancestry thyl
  in
    mkDir_err tf0_dir; app (write_thy fl tf0_dir) thyl;
    writel file [String.concatWith " " (sorted_ancestry thyl)]
  end

(* -------------------------------------------------------------------------
   Export bushy
   ------------------------------------------------------------------------- *)

val tf0_bushy_dir = hh_dir ^ "/export_tf0_bushy"

val id_compare = cpl_compare String.compare String.compare
fun const_set tm = mk_term_set (find_terms is_const tm) 

fun write_cj_bushy thy ((name,thm),depl) =
  let 
    val file = tf0_bushy_dir ^ "/" ^ tf0_thm (thy,name) ^ ".p"
    val oc = TextIO.openOut file
    fun thmfetch (a,b) = DB.fetch a b
    val pretml1 = map (tf0_prep_thm o thmfetch) ((thy,name) :: depl)
    val pretml2 = mk_term_set (List.concat pretml1)
    val tml = mk_term_set (List.concat (map atoms_of pretml2))
    val cl = mk_term_set (List.concat (map const_set tml)) 
    fun fc c =
      let 
        val {Name=cname,Thy=cthy,...} = dest_thy_const c 
        val cid = (cthy,cname)
      in
        tf0_constdef oc cid
        (* better to put them in a include file 
         if is_logicconst cid then tf0_logicdef oc cid
         else if is_quantconst cid then tf0_quantdef oc cid
         else ()
         *)
      end
    fun fax (axthy,axname) =
      let val axthm = DB.fetch axthy axname in
        tf0_thmdef oc axthy ((axname,axthm),"axiom") 
      end
  in
    (
    tf0_casterdef oc; app fc cl; app fax depl;
    tf0_thmdef oc thy ((name,thm),"conjecture"); 
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thy_bushy thy =
  let 
    val cjl = DB.theorems thy
    fun f (name,thm) = case depo_of_thm thm of
        NONE => NONE
      | SOME depl => SOME ((name,thm), depl)
    val cjdepl = List.mapPartial f cjl
  in
    print (thy ^ " ");
    app (write_cj_bushy thy) cjdepl
  end

fun tf0_export_bushy thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err tf0_bushy_dir; app write_thy_bushy thyl
  end

(* -------------------------------------------------------------------------
   Export chainy
   ------------------------------------------------------------------------- *)

val tf0_chainy_dir = hh_dir ^ "/export_tf0_chainy"

fun include_thy oc thy = osn oc ("include('" ^ thy ^ ".ax').")
fun include_thydecl oc thy = osn oc ("include('" ^ thy ^ "-decl.ax').")

fun write_thyaxiom dir thy =
  let
    val file = dir ^ "/" ^ thy ^ ".ax"
    val oc = TextIO.openOut file
  in
    let
      val THEORY(_,t) = dest_theory thy
      val _ = app (tf0_tydef oc thy) (#types t)
      val cl = map (fn (name,_) => (thy,name)) (#consts t)
      val _ = app (tf0_constdef oc) cl
      val axl0 = map (fn x => (x,"axiom")) (DB.thms thy)
      fun cmp (((_,th1),_),((_,th2),_)) =
        Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
      val axl1 = dict_sort cmp axl0
    in
      app (tf0_thmdef oc thy) axl1;
      TextIO.closeOut oc
    end
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thydecl dir thy =
  let
    val file = dir ^ "/" ^ thy ^ "-decl.ax"
    val oc = TextIO.openOut file
  in
    let
      val THEORY(_,t) = dest_theory thy
      val _ = app (tf0_tydef oc thy) (#types t)
      val cl = map (fn (name,_) => (thy,name)) (#consts t)
      val _ = app (tf0_constdef oc) cl
    in
      TextIO.closeOut oc
    end
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_cj_chainy thyl thy (name,thm) =
  let 
    val file = tf0_chainy_dir ^ "/" ^ tf0_thm (thy,name) ^ ".p"
    val oc = TextIO.openOut file
    fun thmfetch (a,b) = DB.fetch a b
    val axl0 = DB.thms thy
    val axl1 = filter (older_than thm) axl0
    fun cmp ((_,th1),(_,th2)) =
      Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
    val axl2 = map (fn (x,_) => (thy,x)) (dict_sort cmp axl1)
    fun fax (axthy,axname) =
      let val axthm = DB.fetch axthy axname in
        tf0_thmdef oc axthy ((axname,axthm),"axiom") 
      end
  in
    (
    app (include_thy oc) thyl;
    include_thydecl oc thy;
    include_thy oc "bool-extra";
    app fax axl2;
    tf0_thmdef oc thy ((name,thm),"conjecture"); 
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thy_chainy thyl thy =
  let val thyl_before = before_elem thy thyl in
    print (thy ^ " ");
    app (write_cj_chainy thyl_before thy) (DB.theorems thy)
  end

fun tf0_export_chainy thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err tf0_chainy_dir; 
    (* write_boolextra tf0_chainy_dir; *)
    app (write_thyaxiom tf0_chainy_dir) thyl;
    app (write_thydecl tf0_chainy_dir) thyl;
    app (write_thy_chainy thyl) thyl
  end

end (* struct *)
