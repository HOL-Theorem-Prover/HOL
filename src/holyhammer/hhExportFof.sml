(* ========================================================================= *)
(* FILE          : hhExportFof.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(*                     Cezary Kaliszyk, University of Innsbruck              *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportFof :> hhExportFof =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate hhExportLib

val ERR = mk_HOL_ERR "hhExportFof"

(* -------------------------------------------------------------------------
   FOF terms
   ------------------------------------------------------------------------- *)

(* every fof type is a unit type *)
fun fof_type oc ty =
  if is_vartype ty then os oc (name_vartype ty) else
    let
      val {Args, Thy, Tyop} = dest_thy_type ty
      val tyops = name_tyop ty
    in
      os oc tyops;
      if null Args then ()
      else (os oc "("; oiter oc "," fof_type Args; os oc ")")
    end

fun fof_term oc tm =
  let val (rator,argl) = strip_comb tm in
    os oc "s("; fof_type oc (type_of tm); os oc ",";
    os oc (namea_cv (length argl) rator);
    if null argl then ()
    else (os oc "("; oiter oc "," fof_term argl; os oc ")");
    os oc ")"
  end

fun fof_pred oc tm =
  if is_forall tm then fof_quant oc "!" (strip_forall tm)
  else if is_exists tm then fof_quant oc "?" (strip_exists tm)
  else if is_conj tm then fof_binop oc "&" (dest_conj tm)
  else if is_disj tm then fof_binop oc "|" (dest_disj tm)
  else if is_imp_only tm then fof_binop oc "=>" (dest_imp tm)
  else if is_neg tm then
    (os oc "~ ("; fof_pred oc (dest_neg tm); os oc ")")
  else if is_eq tm then
    let val (l,r) = dest_eq tm in
      if must_pred l orelse must_pred r (* optimization *)
      then fof_binop oc "<=>" (l,r)
      else (fof_term oc l; os oc " = "; fof_term oc r)
    end
  else (os oc "p("; fof_term oc tm; os oc ")")
and fof_binop oc s (l,r) =
  (os oc "("; fof_pred oc l; os oc (" " ^ s ^ " "); 
   fof_pred oc r; os oc ")")
and fof_quant oc s (vl,bod) =
  (os oc s; os oc "[";
   oiter oc ", " (fn x => (fn v => os x (namea_v 0 v))) vl;
   os oc "]: "; fof_pred oc bod)

fun type_vars_in_term tm =
  type_varsl (map type_of (find_terms is_const tm @ all_vars tm))

fun fof_formula oc tm =
  let val tvl = type_vars_in_term tm in
    if null tvl then ()
    else (os oc "!["; oiter oc "," fof_type tvl; os oc "]: ");
    fof_pred oc tm
  end

(* -------------------------------------------------------------------------
   FOF definitions
   ------------------------------------------------------------------------- *)

val fofpar = "fof("

fun fof_tydef oc _ _ = ()

fun fof_constdef_arity oc (c,arity) =
  let val tfname = namea_c arity c in
    (if arity = 0 then () else 
    let 
      val eq = concl (mk_arity_eq c arity) 
      val arity_prefix = escape ("arity" ^ its arity ^ ".")
    in
      (os oc (fofpar ^ arity_prefix ^ tfname ^ ",axiom,");
       fof_formula oc eq; osn oc ").")
    end)
  end

fun fof_constdef oc (thy,name) =
  let
    val c = prim_mk_const {Thy = thy, Name = name}
    val ty = type_of c
    val maxarity = length (snd (strip_funty ty))
    fun f n = fof_constdef_arity oc (c,n)
  in
    ignore (List.tabulate (maxarity + 1, f))
  end

fun fof_vardef_arity oc (v,arity) =
  if fst (dest_var v) = "app" orelse arity = 0 then () else 
  let 
    val tfname = fof_var arity v 
    val eq = concl (mk_arity_eq v arity) 
    val arity_prefix = escape ("arity" ^ its arity ^ ".")
  in
    (os oc (fofpar ^ arity_prefix ^ tfname ^ ",axiom,");
     fof_formula oc eq; osn oc ").")
  end

fun fof_vardef oc v = 
  let 
    val ty = snd (dest_var v)
    val maxarity = length (snd (strip_funty ty))
    fun f n = fof_vardef_arity oc (v,n)
  in
    ignore (List.tabulate (maxarity + 1, f))
  end

fun fof_prep_thm thm = translate_tm (concl (DISCH_ALL thm))

fun fof_thmdef oc thy ((name,thm),role) =
  let 
    val tml = fof_prep_thm thm
    val vl = free_vars_lr (list_mk_conj (rev tml))
    val (cj,defl) = (hd tml, rev (tl tml))
    fun f i def = 
      (
      os oc (fofpar ^ escape ("fthm" ^ its i ^ ".") ^
      (name_thm (thy,name)) ^ ",axiom,");
      fof_formula oc def; osn oc ")."
      )
  in
    app (fof_vardef oc) vl;
    ignore (mapi f defl);
    os oc (fofpar ^ (name_thm (thy,name)) ^ "," ^ role ^ ",");
    fof_formula oc cj; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Export standard
   ------------------------------------------------------------------------- *)

val fof_dir = hh_dir ^ "/export_fof"

fun fof_export thyl =
  let
    val file = fof_dir ^ "/theory_order.info"
    val fl = (fof_tydef, fof_constdef, fof_thmdef, name_thm)
    val thyl = sorted_ancestry thyl
  in
    mkDir_err fof_dir; app (write_thy fl fof_dir) thyl;
    writel file [String.concatWith " " (sorted_ancestry thyl)]
  end

(* -------------------------------------------------------------------------
   Export bushy
   ------------------------------------------------------------------------- *)

val fof_bushy_dir = hh_dir ^ "/export_fof_bushy"

val id_compare = cpl_compare String.compare String.compare
fun const_set tm = mk_term_set (find_terms is_const tm) 

fun write_cj_bushy thy ((name,thm),depl) =
  let 
    val file = fof_bushy_dir ^ "/" ^ name_thm (thy,name) ^ ".p"
    val oc = TextIO.openOut file
    fun thmfetch (a,b) = DB.fetch a b
    val pretml1 = map (fof_prep_thm o thmfetch) ((thy,name) :: depl)
    val pretml2 = mk_term_set (List.concat pretml1)
    val tml = mk_term_set (List.concat (map atoms_of pretml2))
    val cl = mk_term_set (List.concat (map const_set tml)) 
    fun fc c =
      let 
        val {Name=cname,Thy=cthy,...} = dest_thy_const c 
        val cid = (cthy,cname)
      in
        fof_constdef oc cid
        (* better to put them in a include file 
         if is_logicconst cid then fof_logicdef oc cid
         else if is_quantconst cid then fof_quantdef oc cid
         else ()
         *)
      end
    fun fax (axthy,axname) =
      let val axthm = DB.fetch axthy axname in
        fof_thmdef oc axthy ((axname,axthm),"axiom") 
      end
  in
    (
    app fc cl; app fax depl;
    fof_thmdef oc thy ((name,thm),"conjecture"); 
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

fun fof_export_bushy thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err fof_bushy_dir; app write_thy_bushy thyl
  end

(* -------------------------------------------------------------------------
   Export chainy
   ------------------------------------------------------------------------- *)

val fof_chainy_dir = hh_dir ^ "/export_fof_chainy"

fun include_thy oc thy = osn oc ("include('" ^ thy ^ ".ax').")
fun include_thydecl oc thy = osn oc ("include('" ^ thy ^ "-decl.ax').")

fun write_thyaxiom dir thy =
  let
    val file = dir ^ "/" ^ thy ^ ".ax"
    val oc = TextIO.openOut file
  in
    let
      val THEORY(_,t) = dest_theory thy
      val _ = app (fof_tydef oc thy) (#types t)
      val cl = map (fn (name,_) => (thy,name)) (#consts t)
      val _ = app (fof_constdef oc) cl
      val axl0 = map (fn x => (x,"axiom")) (DB.thms thy)
      fun cmp (((_,th1),_),((_,th2),_)) =
        Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
      val axl1 = dict_sort cmp axl0
    in
      app (fof_thmdef oc thy) axl1;
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
      val _ = app (fof_tydef oc thy) (#types t)
      val cl = map (fn (name,_) => (thy,name)) (#consts t)
      val _ = app (fof_constdef oc) cl
    in
      TextIO.closeOut oc
    end
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_cj_chainy thyl thy (name,thm) =
  let 
    val file = fof_chainy_dir ^ "/" ^ name_thm (thy,name) ^ ".p"
    val oc = TextIO.openOut file
    fun thmfetch (a,b) = DB.fetch a b
    val axl0 = DB.thms thy
    val axl1 = filter (older_than thm) axl0
    fun cmp ((_,th1),(_,th2)) =
      Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
    val axl2 = map (fn (x,_) => (thy,x)) (dict_sort cmp axl1)
    fun fax (axthy,axname) =
      let val axthm = DB.fetch axthy axname in
        fof_thmdef oc axthy ((axname,axthm),"axiom") 
      end
  in
    (
    app (include_thy oc) thyl;
    include_thydecl oc thy;
    include_thy oc "bool-extra";
    app fax axl2;
    fof_thmdef oc thy ((name,thm),"conjecture"); 
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thy_chainy thyl thy =
  let val thyl_before = before_elem thy thyl in
    print (thy ^ " ");
    app (write_cj_chainy thyl_before thy) (DB.theorems thy)
  end

fun fof_export_chainy thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err fof_chainy_dir; 
    (* write_boolextra fof_chainy_dir; *)
    app (write_thyaxiom fof_chainy_dir) thyl;
    app (write_thydecl fof_chainy_dir) thyl;
    app (write_thy_chainy thyl) thyl
  end

end (* struct *)
