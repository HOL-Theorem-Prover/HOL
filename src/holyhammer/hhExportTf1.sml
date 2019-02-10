(* ========================================================================= *)
(* FILE          : hhExportTf1.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(*                     Cezary Kaliszyk, University of Innsbruck              *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportTf1 :> hhExportTf1 =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate hhExportLib

val ERR = mk_HOL_ERR "hhExportTf1"

(* -------------------------------------------------------------------------
   TF1 types,terms,formulas
   ------------------------------------------------------------------------- *)

fun fo_fun oc (s,f_arg,argl) = 
  if null argl then os oc s else 
  (os oc s; os oc "("; oiter oc "," f_arg argl; os oc ")")

fun tf1_fun oc (s,f_tyarg,f_arg,tyargl,argl) =
  if null argl then raise ERR "tf1_fun" "" else
  (
  os oc s; os oc "(";
  oiter oc "," f_tyarg tyargl;
  if null tyargl then () else os oc ",";
  oiter oc "," f_arg argl; os oc ")"
  )

fun tf1_utype oc ty =
  if is_vartype ty then os oc (name_vartype ty) else
    let 
      val {Args, Thy, Tyop} = dest_thy_type ty
      val tyops = name_tyop (Thy,Tyop)
    in
      fo_fun oc (tyops, tf1_utype, Args)
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

fun tf1_vty arity oc v =  
  let val (_,ty) = dest_var v in 
    os oc (namea_v arity v ^ ":"); tf1_utype oc ty 
  end

fun tf1_term oc tm =
  if is_var tm then os oc (namea_v 0 tm)
  else if is_const tm then os oc (namea_c 0 tm)
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
      val cvs = namea_cv arity rator
    in
      tf1_fun oc (cvs, tf1_utype, tf1_term, tyargl,argl) 
    end
  else raise ERR "tf1_term" "abstraction"

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
  (os oc s; os oc "["; oiter oc ", " (tf1_vty 0) vl;
   os oc "]: "; tf1_pred oc bod)

fun tf1_formula oc tm =
  let 
    val tvl = type_vars_in_term tm 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o name_vartype) tvl
    val s = String.concatWith ", " tvls
  in
    if null tvl then () else os oc ("![" ^ s ^ "]: ");
    tf1_pred oc tm
  end

(* -------------------------------------------------------------------------
    TF1 definitions
   ------------------------------------------------------------------------- *)

val tffpar = "tff("

fun tf1_ttype arity =
  if arity <= 1 then String.concatWith " > " [ttype,ttype] else
  "(" ^ String.concatWith " * " (List.tabulate (arity, fn _ => ttype)) ^ ")"
  ^ " > " ^ ttype 

fun tf1_tydef oc thy (tyop,arity) =
  let val tfname = name_tyop (thy,tyop) in
    os oc (tffpar ^ tfname ^ ",type," ^ tfname ^ ":");
    os oc (tf1_ttype arity); osn oc ")."
  end

fun tf1_tyquant_type oc arity ty =
  let 
    val tvl = dict_sort Type.compare (type_vars ty) 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o name_vartype) tvl
    val s = String.concatWith "," tvls
  in
    if null tvl then () else os oc ("!>[" ^ s ^ "]: ");
    tf1_type arity oc ty
  end

fun tf1_cdef_arity_alone oc thy arity c (name,ty) =
  let val tfname = namea_cid arity (thy,name) in
    os oc (tffpar ^ tfname ^ ",type," ^ tfname ^ ":");
    tf1_tyquant_type oc arity ty; osn oc ")."
  end

fun tf1_vdef_arity oc (v,arity) =
  if fst (dest_var v) = "app" then () else 
  let 
    val tfname = namea_v arity v 
    val ty = snd (dest_var v)
  in
    os oc (tffpar ^ tfname ^ ",type," ^ tfname ^ ":");
    tf1_tyquant_type oc arity ty; osn oc ").";
    (
    if arity = 0 then () else 
    let 
      val eq = concl (mk_arity_eq v arity) 
      val arity_prefix = escape ("arity" ^ its arity ^ ".")
    in
      (os oc (tffpar ^ arity_prefix ^ tfname ^ ",axiom,");
       tf1_formula oc eq; osn oc ").")
    end
    )
  end

fun tf1_cdef_arity oc thy arity c (name,ty) =
  let 
    val tfname = namea_cid arity (thy,name) 
  in
    os oc (tffpar ^ tfname ^ ",type," ^ tfname ^ ":");
    tf1_tyquant_type oc arity ty; osn oc ").";
    (if arity = 0 then () else 
    let 
      val eq = concl (mk_arity_eq c arity) 
      val arity_prefix = escape ("arity" ^ its arity ^ ".")
    in
      (os oc (tffpar ^ arity_prefix ^ tfname ^ ",axiom,");
       tf1_formula oc eq; osn oc ").")
    end)
  end

fun tf1_cdef oc (thy,name) =
  let
    val ty = type_of (prim_mk_const {Thy = thy, Name = name})
    val maxarity = length (snd (strip_funty ty))
    val c = mk_thy_const {Name=name,Thy=thy,Ty=ty}
    fun f n = tf1_cdef_arity oc thy n c (name,ty)
  in
    ignore (List.tabulate (maxarity + 1, f))
  end

fun tf1_vdef oc v =
  let 
    val ty = snd (dest_var v)
    val maxarity = length (snd (strip_funty ty))
    fun f n = tf1_vdef_arity oc (v,n) 
  in
    ignore (List.tabulate (maxarity + 1, f))
  end

fun tf1_prep_thm thm = translate_tm (concl (DISCH_ALL thm))

fun tf1_thmdef role oc thy (thy,name) =
  let 
    val tml = tf1_prep_thm thm
    val vl = free_vars_lr (list_mk_conj (rev tml))
    val (cj,defl) = (hd tml, rev (tl tml))
    fun f i def = 
      (
      os oc (tffpar ^ escape ("fthm" ^ its i ^ ".") ^
      (name_thm (thy,name)) ^ ",axiom,");
      tf1_formula oc def; osn oc ")."
      )
  in
    app (tf1_vdef oc) vl;
    ignore (mapi f defl);
    os oc (tffpar ^ (name_thm (thy,name)) ^ "," ^ role ^ ",");
    tf1_formula oc cj; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Casters
   ------------------------------------------------------------------------- *)

val caster_extra = "caster-extra"

fun tf1_app oc = 
  let
    val ty = type_of (prim_mk_const {Thy = "bool", Name = "LET"})
    val tfname = "app_2"
  in
    os oc (tffpar ^ tfname ^ ",type," ^ tfname ^ ":");
    tf1_tyquant_type oc 2 ty; osn oc ")."
  end

fun tf1_p oc = 
  let val tfname = "p" in
    os oc (tffpar ^ tfname ^ ",type," ^ tfname ^ ":");
    tf1_utype oc bool; os oc " > $o"; osn oc ")."
  end

fun write_tf1_caster dir =
  let
    val file = dir ^ "/" ^ caster_extra ^ ".ax"
    val oc = TextIO.openOut file
  in
    (tf1_app oc; tf1_p oc; TextIO.closeOut oc)
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end   

(* -------------------------------------------------------------------------
   Combinators
   ------------------------------------------------------------------------- *)

val combin_extra = "combin-extra"

fun write_combin_extra (f_constdef,f_thmdef) dir = 
  let
    val file = dir ^ "/" ^ combin_extra ^ ".ax"
    val oc = TextIO.openOut file
  in
    let
      val _ = combin_namespace_flag := true
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
      combin_namespace_flag := false;
      TextIO.closeOut oc
    end 
    handle Interrupt => 
    (TextIO.closeOut oc; combin_namespace_flag := false; raise Interrupt)
  end

(* -------------------------------------------------------------------------
   Logical operators equations with term level counterpart.
   ------------------------------------------------------------------------- *)

val boolop_extra = "boolop-extra"

fun tf1_logicformula oc (thy,name) = 
  let 
    val c = prim_mk_const {Thy = thy, Name = name}
    val tm = full_apply_const c
    val tvl = type_vars_in_term tm 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o name_vartype) tvl
    val s = String.concatWith ", " tvls
    val vl = free_vars_lr tm 
  in
    if null tvl then () else os oc ("![" ^ s ^ "]: ");
    os oc "!["; oiter oc ", " tf1_vty vl; os oc "]: ";
    os oc "("; tf1_term oc tm; os oc " <=> "; tf1_pred oc tm; os oc ")"
  end

val logicconstl_glob = 
  let fun f c = let val {Thy,Name,Ty} = dest_thy_const c in (Thy,Name) end in
    map f [``$/\``,``$\/``,``$~``,``$==>``,``$= : 'a -> 'a -> bool``]
  end
fun is_logicconst x = mem x logicconstl_glob


fun tf1_logicdef oc (thy,name) =
  (
  os oc (tffpar ^ escape ("logicdef." ^ name) ^ ",axiom,"); 
  tf1_logicformula oc (thy,name); osn oc ")."
  )

fun is_quantconst x = mem x [("bool","!"),("bool","?")]

fun tf1_quantdef oc (thy,name) =
  let 
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val tm = tf1_prep_thm thm
  in
    os oc (tffpar ^ escape ("quantdef." ^ name) ^ ",axiom,"); 
    tf1_formula oc tm; osn oc ")."
  end

fun write_boolop_extra dir = 
  let
    val file = dir ^ "/" ^ boolop_extra ^ ".ax"
    val oc = TextIO.openOut file
  in
    (
    app (tf1_logicdef oc) logicconstl_glob;
    app (tf1_quantdef oc) [("bool","!"),("bool","?")];
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

(* -------------------------------------------------------------------------
   Export bushy
   ------------------------------------------------------------------------- *)

val tf1_bushy_dir = hh_dir ^ "/export_tf1_bushy"

fun write_cj_bushy thy ((name,thm),depl) =
  let 
    val file = tf1_bushy_dir ^ "/" ^ name_thm (thy,name) ^ ".p"
    val oc = TextIO.openOut file
    fun thmfetch (a,b) = DB.fetch a b
    val tml = map (tf1_prep_thm o thmfetch) ((thy,name) :: depl)
    val (tyopl,cidl) = required_def tml
    fun ftyop ((tyopthy,tyopname),tyoparity) = 
      tf1_tyopdef oc tyopthy (tyopname,tyoparity)
    fun fax (axthy,axname) =
      let val axthm = DB.fetch axthy axname in
        tf1_thmdef oc axthy ((axname,axthm),"axiom") 
      end
  in
    (
    app ftyop tyopl; app (tf1_cdef oc) cidl; 
    include_thy oc boolop_extra;
    app fax depl;
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
    print (thy ^ " "); app (write_cj_bushy thy) cjdepl
  end

fun tf1_export_bushy thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err tf1_bushy_dir; 
    write_boolop_extra tf1_bushy_dir;
    app write_thy_bushy thyl
  end


(* -------------------------------------------------------------------------
   Export chainy
   ------------------------------------------------------------------------- *)

val tf1_chainy_dir = hh_dir ^ "/export_tf1_chainy"

fun write_cj_chainy thyl thy (name,thm) =
  let 
    val file = tf1_chainy_dir ^ "/" ^ name_thm (thy,name) ^ ".p"
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
