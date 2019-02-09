(* ========================================================================= *)
(* FILE          : hhExportTff.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(*                     Cezary Kaliszyk, University of Innsbruck              *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportTff :> hhExportTff =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate hhExportLib

val ERR = mk_HOL_ERR "hhExportTff"

(* -------------------------------------------------------------------------
   Directories
   ------------------------------------------------------------------------- *)

val tf1_bushy_dir = hh_dir ^ "/export_tf1_bushy"
val tf1_chainy_dir = hh_dir ^ "/export_tf1_chainy"

(* -------------------------------------------------------------------------
   TF1 names : variables escaped by translate_tm
   ------------------------------------------------------------------------- *)

val combin_extra_flag = ref false

fun tf1_var arity v = fst (dest_var v) ^ "_" ^ int_to_string arity
fun tf1b_const arity (thy,name) = 
  if !combin_extra_flag 
  then escape ("c.combin-extra." ^ name) ^ "_" ^ int_to_string arity
  else escape ("c." ^ thy ^ "." ^ name) ^ "_" ^ int_to_string arity

fun tf1_const arity c =
  let val {Name,Thy,Ty} = dest_thy_const c in tf1b_const arity (Thy,Name) end

fun tf1_constvar arity tm =
  if is_const tm then tf1_const arity tm
  else if is_var tm then tf1_var arity tm
  else raise ERR "tf1_constvar" ""

fun tf1_vartype ty = "A" ^ (escape (dest_vartype ty))
fun tf1b_tyop (thy,tyop) = escape ("ty." ^ thy ^ "." ^ tyop)
fun tf1_tyop ty =
  let val {Args,Thy,Tyop} = dest_thy_type ty in tf1b_tyop (Thy,Tyop) end
fun tf1b_thm (thy,name) = escape ("thm" ^ "." ^ thy ^ "." ^ name)

(* -------------------------------------------------------------------------
   TF1 types,terms,formulas
   ------------------------------------------------------------------------- *)

fun tf1_utype oc ty =
  if is_vartype ty then os oc (tf1_vartype ty) else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if null Args then os oc (tf1_tyop ty) else 
        (os oc (tf1_tyop ty);
         os oc "("; oiter oc "," tf1_utype Args; os oc ")")
    end

fun tf1_type arity oc ty = case strip_funty_n arity ty of
    [] => raise ERR "tf1_type" ""
  | [imty] => tf1_utype oc imty
  | [imty,uty] => 
    (os oc "("; tf1_utype oc uty; os oc " > "; tf1_utype oc imty;
     os oc ")")
  | l =>
    (os oc "(("; 
     oiter oc " * " tf1_utype (butlast l); os oc ") > "; 
     tf1_utype oc (last l); os oc ")")

fun tf1_var_and_type arity oc v =  
  let val (_,ty) = dest_var v in 
    os oc (tf1_var arity v ^ ":"); tf1_utype oc ty 
  end

fun tf1_term oc tm =
  if is_var tm then os oc (tf1_var 0 tm)
  else if is_const tm then os oc (tf1_const 0 tm)
  else if is_comb tm then
    let 
      val (rator,argl) = strip_comb tm
      val arity = length argl
      val tyargl = 
        if is_var rator then  
          if fst (dest_var rator) = "app" 
          then typearg_of_appvar rator
          else typearg_of_var rator
        else typearg_of_const rator
    in
      os oc (tf1_constvar arity rator); 
      os oc "("; 
      if null tyargl then () else 
      (oiter oc "," tf1_utype tyargl; os oc ",");
      oiter oc "," tf1_term argl; 
      os oc ")"
    end
  else raise ERR "tf1_term" "abstraction"

(* there should be a p in tf1 to do a cast for bool to $o since $o
   can't occur at the term level 
*)

fun tf1_pred oc tm =
  if is_forall tm then tf1_quant oc "!" (strip_forall tm)
  else if is_exists tm then tf1_quant oc "?" (strip_exists tm)
  else if is_conj tm then tf1_binop oc "&" (dest_conj tm)
  else if is_disj tm then tf1_binop oc "|" (dest_disj tm)
  else if is_imp_only tm then tf1_binop oc "=>" (dest_imp tm)
  else if is_neg tm then
    (os oc "(~ "; tf1_pred oc (dest_neg tm); os oc ")")
  else if is_eq tm then
    let val (l,r) = dest_eq tm in
      if must_pred l orelse must_pred r
      then tf1_binop oc "<=>" (l,r)
      else (os oc "("; tf1_term oc l; os oc " = ";  
            tf1_term oc r; os oc ")")
    end
  else (os oc "p("; tf1_term oc tm; os oc ")")
and tf1_binop oc s (l,r) =
  (os oc "("; tf1_pred oc l; os oc (" " ^ s ^ " "); 
   tf1_pred oc r; os oc ")")
and tf1_quant oc s (vl,bod) =
  (os oc s; os oc "["; oiter oc ", " (tf1_var_and_type 0) vl;
   os oc "]: "; tf1_pred oc bod)

fun tf1_formula oc tm =
  let 
    val tvl = type_vars_in_term tm 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o tf1_vartype) tvl
    val s = String.concatWith ", " tvls
  in
    if null tvl then () else os oc ("![" ^ s ^ "]: ");
    tf1_pred oc tm
  end

(* -------------------------------------------------------------------------
    TF1 definitions
   ------------------------------------------------------------------------- *)

fun tf1_ttype arity =
  if arity <= 1 then String.concatWith " > " [ttype,ttype] else
  "(" ^ String.concatWith " * " (List.tabulate (arity, fn _ => ttype)) ^ ")"
  ^ " > " ^ ttype 

fun tf1_tydef oc thy (tyop,arity) =
  let val tfname = tf1b_tyop (thy,tyop) in
    os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":");
    os oc (tf1_ttype arity); osn oc ")."
  end

fun tf1_tyquant_type oc arity ty =
  let 
    val tvl = dict_sort Type.compare (type_vars ty) 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o tf1_vartype) tvl
    val s = String.concatWith "," tvls
  in
    if null tvl then () else os oc ("!>[" ^ s ^ "]: ");
    tf1_type arity oc ty
  end

fun tf1_constdef_arity_alone oc thy arity c (name,ty) =
  let val tfname = tf1b_const arity (thy,name) in
    os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":");
    tf1_tyquant_type oc arity ty; osn oc ")."
  end

fun tf1_constdef_arity oc thy arity c (name,ty) =
  let 
    val tfname = tf1b_const arity (thy,name) 
  in
    os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":");
    tf1_tyquant_type oc arity ty; osn oc ").";
    (if arity = 0 then () else 
    let 
      val eq = concl (mk_arity_eq c arity) 
      val arity_prefix = escape ("arity" ^ its arity ^ ".")
    in
      (os oc ("tff(" ^ arity_prefix ^ tfname ^ ",axiom,");
       tf1_formula oc eq; osn oc ").")
    end)
  end

fun tf1_vardef_arity oc (v,arity) =
  if fst (dest_var v) = "app" then () else 
  let 
    val tfname = tf1_var arity v 
    val ty = snd (dest_var v)
  in
    os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":");
    tf1_tyquant_type oc arity ty; osn oc ").";
    (
    if arity = 0 then () else 
    let 
      val eq = concl (mk_arity_eq v arity) 
      val arity_prefix = escape ("arity" ^ its arity ^ ".")
    in
      (os oc ("tff(" ^ arity_prefix ^ tfname ^ ",axiom,");
       tf1_formula oc eq; osn oc ").")
    end
    )
  end

fun tf1_constdef oc (thy,name) =
  let
    val ty = type_of (prim_mk_const {Thy = thy, Name = name})
    val maxarity = length (snd (strip_funty ty))
    val c = mk_thy_const {Name=name,Thy=thy,Ty=ty}
    fun f n = tf1_constdef_arity oc thy n c (name,ty)
  in
    ignore (List.tabulate (maxarity + 1, f))
  end

fun tf1_vardef oc v =
  let 
    val ty = snd (dest_var v)
    val maxarity = length (snd (strip_funty ty))
    fun f n = tf1_vardef_arity oc (v,n) 
  in
    ignore (List.tabulate (maxarity + 1, f))
  end

fun tf1_app oc = 
  let
    val ty = type_of (prim_mk_const {Thy = "bool", Name = "LET"})
    val tfname = "app_2"
  in
    os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":");
    tf1_tyquant_type oc 2 ty; osn oc ")."
  end

fun tf1_p oc = 
  let val tfname = "p" in
    os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":");
    tf1_utype oc bool; os oc " > $o"; osn oc ")."
  end

fun write_tf1_app dir =
  let
    val file = dir ^ "/app-extra.ax"
    val oc = TextIO.openOut file
  in
    (tf1_app oc; tf1_p oc; TextIO.closeOut oc)
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end   


fun tf1_prep_thm thm = translate_tm (concl (DISCH_ALL thm))

fun tf1_thmdef oc thy ((name,thm),role) =
  let 
    val tml = tf1_prep_thm thm
    val vl = free_vars_lr (list_mk_conj (rev tml))
    val (cj,defl) = (hd tml, rev (tl tml))
    fun f i def = 
      (
      os oc ("tff(" ^ escape ("fthm" ^ its i ^ ".") ^
      (tf1b_thm (thy,name)) ^ ",axiom,");
      tf1_formula oc def; osn oc ")."
      )
  in
    app (tf1_vardef oc) vl;
    ignore (mapi f defl);
    os oc ("tff(" ^ (tf1b_thm (thy,name)) ^ "," ^ role ^ ",");
    tf1_formula oc cj; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Combinators: (todo output only arity 0)
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

(* -------------------------------------------------------------------------
   Export standard
   ------------------------------------------------------------------------- *)

val tf1_dir = hh_dir ^ "/export_tf1"

fun tf1_export thyl =
  let
    val file = tf1_dir ^ "/theory_order.info"
    val fl = (tf1_tydef, tf1_constdef, tf1_thmdef, tf1b_thm)
    val thyl = sorted_ancestry thyl
  in
    mkDir_err tf1_dir;
    (* write_boolextra tf1_dir; *)
    app (write_thy fl tf1_dir) thyl;
    writel file [String.concatWith " " (sorted_ancestry thyl)]
  end

(* -------------------------------------------------------------------------
   Export bushy
   ------------------------------------------------------------------------- *)

val tf1_bushy_dir = hh_dir ^ "/export_tf1_bushy"

val id_compare = cpl_compare String.compare String.compare

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
    loop topty; mk_fast_set (cpl_compare id_compare Int.compare) (!l)
  end

fun const_set tm = mk_term_set (find_terms is_const tm) 

fun write_cj_bushy thy ((name,thm),depl) =
  let 
    val file = tf1_bushy_dir ^ "/" ^ tf1b_thm (thy,name) ^ ".p"
    val oc = TextIO.openOut file
    fun thmfetch (a,b) = DB.fetch a b
    val pretml = List.concat (map (tf1_prep_thm o thmfetch) 
      ((thy,name) :: depl))
    val tml = mk_term_set (List.concat (map atoms_of pretml))
    val tyl = mk_type_set (List.concat (map type_set tml))
    val tyopl = mk_fast_set (cpl_compare id_compare Int.compare) 
      (List.concat (map tyop_set tyl))
    val cl = mk_term_set (List.concat (map const_set tml)) 
    fun ftyop ((tyopthy,tyopname),tyoparity) = 
      tf1_tydef oc tyopthy (tyopname,tyoparity)
    fun fc c =
      let 
        val {Name=cname,Thy=cthy,...} = dest_thy_const c 
        val cid = (cthy,cname)
      in
        tf1_constdef oc cid
        (*
        if is_logicconst cid then tf1_logicdef oc cid
        else if is_quantconst cid then tf1_quantdef oc cid
        else ()
        *)
      end
    fun fax (axthy,axname) =
      let val axthm = DB.fetch axthy axname in
        tf1_thmdef oc axthy ((axname,axthm),"axiom") 
      end
  in
    (
    app ftyop tyopl; tf1_app oc; tf1_p oc; app fc cl; app fax depl;
    tf1_thmdef oc thy ((name,thm),"conjecture"); 
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

fun tf1_export_bushy thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err tf1_bushy_dir; app write_thy_bushy thyl
  end

(* -------------------------------------------------------------------------
   Export chainy
   ------------------------------------------------------------------------- *)

val tf1_chainy_dir = hh_dir ^ "/export_tf1_chainy"

fun include_thy oc thy = osn oc ("include('" ^ thy ^ ".ax').")
fun include_thydecl oc thy = osn oc ("include('" ^ thy ^ "-decl.ax').")

fun write_thyaxiom dir thy =
  let
    val file = dir ^ "/" ^ thy ^ ".ax"
    val oc = TextIO.openOut file
  in
    let
      val THEORY(_,t) = dest_theory thy
      val _ = app (tf1_tydef oc thy) (#types t)
      val cl = map (fn (name,_) => (thy,name)) (#consts t)
      val _ = app (tf1_constdef oc) cl
      val axl0 = map (fn x => (x,"axiom")) (DB.thms thy)
      fun cmp (((_,tf1),_),((_,th2),_)) =
        Int.compare (depnumber_of_thm tf1, depnumber_of_thm th2)
      val axl1 = dict_sort cmp axl0
    in
      app (tf1_thmdef oc thy) axl1;
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
      val _ = app (tf1_tydef oc thy) (#types t)
      val cl = map (fn (name,_) => (thy,name)) (#consts t)
      val _ = app (tf1_constdef oc) cl
    in
      TextIO.closeOut oc
    end
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_cj_chainy thyl thy (name,thm) =
  let 
    val file = tf1_chainy_dir ^ "/" ^ tf1b_thm (thy,name) ^ ".p"
    val oc = TextIO.openOut file
    fun thmfetch (a,b) = DB.fetch a b
    val axl0 = DB.thms thy
    val axl1 = filter (older_than thm) axl0
    fun cmp ((_,tf1),(_,th2)) =
      Int.compare (depnumber_of_thm tf1, depnumber_of_thm th2)
    val axl2 = map (fn (x,_) => (thy,x)) (dict_sort cmp axl1)
    fun fax (axthy,axname) =
      let val axthm = DB.fetch axthy axname in
        tf1_thmdef oc axthy ((axname,axthm),"axiom") 
      end
  in
    (
    app (include_thy oc) thyl;
    include_thydecl oc thy;
    include_thy oc "app-extra";
    app fax axl2;
    tf1_thmdef oc thy ((name,thm),"conjecture"); 
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_thy_chainy thyl thy =
  let val thyl_before = before_elem thy thyl in
    print (thy ^ " ");
    app (write_cj_chainy thyl_before thy) (DB.theorems thy)
  end

(* load_sigobj (); sort_thyl (ancestry "scratch"); *)
fun tf1_export_chainy thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err tf1_chainy_dir; 
    write_tf1_app tf1_chainy_dir;
    (* write_boolextra tf1_chainy_dir; *)
    app (write_thyaxiom tf1_chainy_dir) thyl;
    app (write_thydecl tf1_chainy_dir) thyl;
    app (write_thy_chainy thyl) thyl
  end



end (* struct *)
