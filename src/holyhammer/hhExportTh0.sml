(* ========================================================================= *)
(* FILE          : hhExportTh0.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(*                     Cezary Kaliszyk, University of Innsbruck              *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportTh0 :> hhExportTh0 =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate hhExportLib

val ERR = mk_HOL_ERR "hhExportTh0"

(* -------------------------------------------------------------------------
   FOF names : variables escaped by translate_tm
   ------------------------------------------------------------------------- *)

fun th0_var arity v = fst (dest_var v) ^ "_" ^ int_to_string arity

fun th0_const arity c =
  let val {Name, Thy, Ty} = dest_thy_const c in
    escape ("c" ^ int_to_string arity ^ "." ^ Thy ^ "." ^ Name)
  end

fun th0_constvar arity tm =
  if is_const tm then th0_const arity tm
  else if is_var tm then th0_var arity tm
  else raise raise ERR "th0_constvar" ""

fun th0_vardomain ty = "A" ^ (escape (dest_vartype ty))

fun th0_opdomain ty =
  let val {Args, Thy, Tyop} = dest_thy_type ty in
    escape ("ty" ^ "." ^ Thy ^ "." ^ Tyop)
  end

fun th0_thm (thy,name) = escape ("thm" ^ "." ^ thy ^ "." ^ name)

(* -------------------------------------------------------------------------
   FOF terms
   ------------------------------------------------------------------------- *)

(* every fof type is a unit type *)

val itype = "$i" (* use to represent the result of s *)

fun th0_type n =
  String.concatWith " > " (List.tabulate (n+1,fn _ => itype))

fun th0_domain oc ty =
  if is_vartype ty then os oc (th0_vardomain ty) else
    let
      val {Args, Thy, Tyop} = dest_thy_type ty
      val tyops = th0_opdomain ty
    in
      if null Args then os oc tyops else 
      (os oc "("; os oc tyops; os oc " @ ";
       oiter oc " @ " th0_domain Args; os oc ")")
    end

fun th0_term oc tm =
  let val (rator,argl) = strip_comb tm in
    os oc "(";
    os oc "s @ "; th0_domain oc (type_of tm); os oc " @ ";
    if null argl then os oc (th0_constvar (length argl) rator) else 
      (os oc "(";
       os oc (th0_constvar (length argl) rator); os oc " @ ";
       oiter oc " @ " th0_term argl;
       os oc ")");
    os oc ")"
  end

fun th0_pred oc tm =
  if is_forall tm then th0_quant oc "!" (strip_forall tm)
  else if is_exists tm then th0_quant oc "?" (strip_exists tm)
  else if is_conj tm then th0_binop oc "&" (dest_conj tm)
  else if is_disj tm then th0_binop oc "|" (dest_disj tm)
  else if is_imp_only tm then th0_binop oc "=>" (dest_imp tm)
  else if is_neg tm then
    (os oc "~ ("; th0_pred oc (dest_neg tm); os oc ")")
  else if is_eq tm then
    let val (l,r) = dest_eq tm in
      if must_pred l orelse must_pred r (* optimization *)
      then th0_binop oc "<=>" (l,r)
      else (os oc "("; th0_term oc l; os oc " = "; th0_term oc r;
            os oc ")")
    end
  else (os oc "(p @ "; th0_term oc tm; os oc ")")
and th0_binop oc s (l,r) =
  (os oc "("; th0_pred oc l; os oc (" " ^ s ^ " "); 
   th0_pred oc r; os oc ")")
and th0_quant oc s (vl,bod) =
  (os oc s; os oc "[";
   oiter oc ", " (fn x => (fn v => os x (th0_var 0 v))) vl;
   os oc "]: "; th0_pred oc bod)

fun type_vars_in_term tm =
  type_varsl (map type_of (find_terms is_const tm @ all_vars tm))

(* type variables should have type $i explicit *)

fun th0_formula oc tm =
  let val tvl = type_vars_in_term tm in
    if null tvl then ()
    else (os oc "!["; oiter oc "," th0_domain tvl; os oc "]: ");
    th0_pred oc tm
  end

(* -------------------------------------------------------------------------
   FOF definitions
   ------------------------------------------------------------------------- *)

val tffpar = "tff("

(*
fun th0_tydef oc thy (tyop,arity) =
  let val tfname = tf1b_tyop (thy,tyop) in
    os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":" ^ ttype);
    os oc (tf1_ttype arity); osn oc ")."
  end
*)

fun th0_tydef oc thy (tyop,arity) = ()

fun th0_nameadef oc (name,arity) =
  (
  os oc (tffpar ^ name ^ ",type," ^ name ^ ":");
  os oc (th0_type arity); osn oc ")."
  )

fun th0_nametysdef oc (name,tys) =
  (
  os oc (tffpar ^ name ^ ",type," ^ name ^ ":");
  os oc tys; osn oc ")."
  )

fun th0_constdef_arity oc (c,arity) =
  let val tfname = th0_const arity c in
    os oc (tffpar ^ tfname ^ ",type," ^ tfname ^ ":");
    os oc (th0_type arity); osn oc ").";
    (if arity = 0 then () else 
    let 
      val eq = concl (mk_arity_eq c arity) 
      val arity_prefix = escape ("arity" ^ its arity ^ ".")
    in
      (os oc (tffpar ^ arity_prefix ^ tfname ^ ",axiom,");
       th0_formula oc eq; osn oc ").")
    end)
  end

fun th0_constdef oc (thy,name) =
  let
    val c = prim_mk_const {Thy = thy, Name = name}
    val ty = type_of c
    val maxarity = length (snd (strip_funty ty))
    fun f n = th0_constdef_arity oc (c,n)
  in
    ignore (List.tabulate (maxarity + 1, f))
  end

fun th0_vardef_arity oc (v,arity) =
  if fst (dest_var v) = "app" then () else 
  let val tfname = th0_var arity v in
    os oc (tffpar ^ tfname ^ ",type," ^ tfname ^ ":");
    os oc (th0_type arity); osn oc ").";
    (if arity = 0 then () else
    let
      val eq = concl (mk_arity_eq v arity) 
      val arity_prefix = escape ("arity" ^ its arity ^ ".")
    in
      os oc (tffpar ^ arity_prefix ^ tfname ^ ",axiom,");
      th0_formula oc eq; osn oc ")."
    end)
  end

(* define type of app,p,s *)
fun th0_casterdef oc =
  (
  app (th0_nameadef oc) [("app_2",2),("s",2)];
  th0_nametysdef oc ("p","$i > $o")
  )
(* free variables are used for new constants *)
(* type of free variable is always most general type except for app *)
fun th0_vardef oc v = 
  let 
    val ty = snd (dest_var v)
    val maxarity = length (snd (strip_funty ty))
    fun f n = th0_vardef_arity oc (v,n)
  in
    ignore (List.tabulate (maxarity + 1, f))
  end

fun th0_prep_thm thm = translate_tm (concl (DISCH_ALL thm))

fun th0_thmdef oc thy ((name,thm),role) =
  let 
    val tml = th0_prep_thm thm
    val vl = free_vars_lr (list_mk_conj (rev tml))
    val (cj,defl) = (hd tml, rev (tl tml))
    fun f i def = 
      (
      os oc (tffpar ^ escape ("fthm" ^ its i ^ ".") ^
      (th0_thm (thy,name)) ^ ",axiom,");
      th0_formula oc def; osn oc ")."
      )
  in
    app (th0_vardef oc) vl;
    ignore (mapi f defl);
    os oc (tffpar ^ (th0_thm (thy,name)) ^ "," ^ role ^ ",");
    th0_formula oc cj; 
    osn oc ")."
  end
  

(* -------------------------------------------------------------------------
   Export standard
   ------------------------------------------------------------------------- *)

val th0_dir = hh_dir ^ "/export_tf0"

fun th0_export thyl =
  let
    val file = th0_dir ^ "/theory_order.info"
    val fl = (th0_tydef, th0_constdef, th0_thmdef, th0_thm)
    val thyl = sorted_ancestry thyl
  in
    mkDir_err th0_dir; app (write_thy fl th0_dir) thyl;
    writel file [String.concatWith " " (sorted_ancestry thyl)]
  end

(* -------------------------------------------------------------------------
   Export bushy
   ------------------------------------------------------------------------- *)

val th0_bushy_dir = hh_dir ^ "/export_th0_bushy"

val id_compare = cpl_compare String.compare String.compare
fun const_set tm = mk_term_set (find_terms is_const tm) 

fun write_cj_bushy thy ((name,thm),depl) =
  let 
    val file = th0_bushy_dir ^ "/" ^ th0_thm (thy,name) ^ ".p"
    val oc = TextIO.openOut file
    fun thmfetch (a,b) = DB.fetch a b
    val pretml1 = map (th0_prep_thm o thmfetch) ((thy,name) :: depl)
    val pretml2 = mk_term_set (List.concat pretml1)
    val tml = mk_term_set (List.concat (map atoms_of pretml2))
    val cl = mk_term_set (List.concat (map const_set tml)) 
    fun fc c =
      let 
        val {Name=cname,Thy=cthy,...} = dest_thy_const c 
        val cid = (cthy,cname)
      in
        th0_constdef oc cid
        (* better to put them in a include file 
         if is_logicconst cid then th0_logicdef oc cid
         else if is_quantconst cid then th0_quantdef oc cid
         else ()
         *)
      end
    fun fax (axthy,axname) =
      let val axthm = DB.fetch axthy axname in
        th0_thmdef oc axthy ((axname,axthm),"axiom") 
      end
  in
    (
    th0_casterdef oc; app fc cl; app fax depl;
    th0_thmdef oc thy ((name,thm),"conjecture"); 
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

fun th0_export_bushy thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err th0_bushy_dir; app write_thy_bushy thyl
  end

(* -------------------------------------------------------------------------
   Export chainy
   ------------------------------------------------------------------------- *)

val th0_chainy_dir = hh_dir ^ "/export_th0_chainy"

fun include_thy oc thy = osn oc ("include('" ^ thy ^ ".ax').")
fun include_thydecl oc thy = osn oc ("include('" ^ thy ^ "-decl.ax').")

fun write_thyaxiom dir thy =
  let
    val file = dir ^ "/" ^ thy ^ ".ax"
    val oc = TextIO.openOut file
  in
    let
      val THEORY(_,t) = dest_theory thy
      val _ = app (th0_tydef oc thy) (#types t)
      val cl = map (fn (name,_) => (thy,name)) (#consts t)
      val _ = app (th0_constdef oc) cl
      val axl0 = map (fn x => (x,"axiom")) (DB.thms thy)
      fun cmp (((_,th1),_),((_,th2),_)) =
        Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
      val axl1 = dict_sort cmp axl0
    in
      app (th0_thmdef oc thy) axl1;
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
      val _ = app (th0_tydef oc thy) (#types t)
      val cl = map (fn (name,_) => (thy,name)) (#consts t)
      val _ = app (th0_constdef oc) cl
    in
      TextIO.closeOut oc
    end
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_cj_chainy thyl thy (name,thm) =
  let 
    val file = th0_chainy_dir ^ "/" ^ th0_thm (thy,name) ^ ".p"
    val oc = TextIO.openOut file
    fun thmfetch (a,b) = DB.fetch a b
    val axl0 = DB.thms thy
    val axl1 = filter (older_than thm) axl0
    fun cmp ((_,th1),(_,th2)) =
      Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
    val axl2 = map (fn (x,_) => (thy,x)) (dict_sort cmp axl1)
    fun fax (axthy,axname) =
      let val axthm = DB.fetch axthy axname in
        th0_thmdef oc axthy ((axname,axthm),"axiom") 
      end
  in
    (
    app (include_thy oc) thyl;
    include_thydecl oc thy;
    include_thy oc "bool-extra";
    app fax axl2;
    th0_thmdef oc thy ((name,thm),"conjecture"); 
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thy_chainy thyl thy =
  let val thyl_before = before_elem thy thyl in
    print (thy ^ " ");
    app (write_cj_chainy thyl_before thy) (DB.theorems thy)
  end

fun th0_export_chainy thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err th0_chainy_dir; 
    (* write_boolextra th0_chainy_dir; *)
    app (write_thyaxiom th0_chainy_dir) thyl;
    app (write_thydecl th0_chainy_dir) thyl;
    app (write_thy_chainy thyl) thyl
  end

end (* struct *)
