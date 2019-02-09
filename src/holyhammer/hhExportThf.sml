(* ========================================================================= *)
(* FILE          : hhExportThf.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(*                     Cezary Kaliszyk, University of Innsbruck              *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportThf :> hhExportThf =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate hhExportLib

val ERR = mk_HOL_ERR "hhExportThf"

(* -------------------------------------------------------------------------
   Preparing and analysing the formula
   ------------------------------------------------------------------------- *)

fun th1_prep_tm tm = rename_bvarl escape (list_mk_forall (free_vars_lr tm, tm))
fun th1_prep_thm thm = th1_prep_tm (concl (DISCH_ALL thm))

(* ------------------------------------------------------------------------
   TH1 names
   ------------------------------------------------------------------------ *)

fun th1_var v = fst (dest_var v)
fun th1b_const (thy,name) = escape ("c." ^ thy ^ "." ^ name)
fun th1_const c =
  let val {Name,Thy,Ty} = dest_thy_const c in th1b_const (Thy,Name) end
fun th1_vartype ty = "A" ^ (escape (dest_vartype ty))
fun th1b_tyop (thy,tyop) = escape ("ty." ^ thy ^ "." ^ tyop)
fun th1_tyop ty =
  let val {Args,Thy,Tyop} = dest_thy_type ty in th1b_tyop (Thy,Tyop) end
fun th1b_thm (thy,name) = escape ("thm" ^ "." ^ thy ^ "." ^ name)

(* -------------------------------------------------------------------------
    TH1 types,terms,formulas
   ------------------------------------------------------------------------- *)

fun th1_type oc ty =
  if is_vartype ty then os oc (th1_vartype ty) else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if Thy = "min" andalso Tyop = "bool" then os oc "$o"
      else if Thy = "min" andalso Tyop = "fun" then
        let val (tya,tyb) = pair_of_list Args in    
          os oc "("; th1_type oc tya;
          os oc " > "; th1_type oc tyb; os oc ")"
        end
      else if null Args then os oc (th1_tyop ty)
      else (os oc "("; os oc (th1_tyop ty); os oc " @ ";
            oiter oc " @ " th1_type Args; os oc ")")
    end

fun th1_vty oc v =  
  let val (vs,ty) = dest_var v in os oc (vs ^ ":"); th1_type oc ty end

fun th1_term oc tm =
  if is_var tm then os oc (th1_var tm)
  else if is_const tm then
    let val resl = typearg_of_const tm in
      if null resl
      then os oc (th1_const tm)
      else (os oc "("; os oc (th1_const tm); os oc " @ ";
            oiter oc " @ " th1_type resl; os oc ")")
    end
  else if is_comb tm then
    let val (rator,argl) = strip_comb tm in
      os oc "("; th1_term oc rator;
      os oc " @ "; oiter oc " @ " th1_term argl; os oc ")"
    end
  else if is_abs tm then
    let val (vl,bod) = strip_abs tm in
      os oc "^[";
      oiter oc ", " th1_vty vl;
      os oc "]: "; th1_term oc bod
    end
  else raise ERR "th1_term" ""

fun th1_pred oc tm = shared_pred (th1_vty,th1_term) oc tm

fun th1_formula oc tm =
  let 
    val tvl = type_vars_in_term tm 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o th1_vartype) tvl
    val s = String.concatWith ", " tvls
  in
    if null tvl then () else os oc ("![" ^ s ^ "]: ");
    th1_pred oc tm
  end

(* -------------------------------------------------------------------------
    TH1 definitions
   ------------------------------------------------------------------------- *)

fun th1_ttype arity =
  String.concatWith " > " (List.tabulate (arity + 1, fn _ => ttype))

fun th1_tydef oc thy (tyop,arity) =
  (os oc ("thf(" ^ th1b_tyop (thy,tyop) ^ ",type,");
   os oc (th1b_tyop (thy,tyop) ^ ":"); os oc (th1_ttype arity); osn oc ").")

fun th1_tyquant_type oc ty =
  let 
    val tvl = dict_sort Type.compare (type_vars ty) 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o th1_vartype) tvl
    val s = String.concatWith "," tvls
  in
    if null tvl then () else os oc ("!>[" ^ s ^ "]: ");
    th1_type oc ty
  end

fun th1_constdef oc (thy,name) =
  let val ty = type_of (prim_mk_const {Thy = thy, Name = name}) in
    os oc ("thf(" ^ th1b_const (thy,name) ^ ",type,");
    os oc (th1b_const (thy,name) ^ ":"); th1_tyquant_type oc ty; osn oc ")."
  end

fun th1_thmdef oc thy ((name,thm),role) =
  let val tm = th1_prep_thm thm in
    os oc ("thf(" ^ (th1b_thm (thy,name)) ^ "," ^ role ^ ",");
    th1_formula oc tm; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Logical operators equations with term level counterpart.
   ------------------------------------------------------------------------- *)

fun th1_logicformula oc (thy,name) = 
  let 
    val c = prim_mk_const {Thy = thy, Name = name}
    val tm = full_apply_const c
    val tvl = type_vars_in_term tm 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o th1_vartype) tvl
    val s = String.concatWith ", " tvls
    val vl = free_vars_lr tm 
  in
    if null tvl then () else os oc ("![" ^ s ^ "]: ");
    os oc "!["; oiter oc ", " th1_vty vl; os oc "]: ";
    os oc "("; th1_term oc tm ; os oc " <=> "; th1_pred oc tm; os oc ")"
  end

val logicconstl_glob = 
  let fun f c = let val {Thy,Name,Ty} = dest_thy_const c in (Thy,Name) end in
    map f [``$/\``,``$\/``,``$~``,``$==>``,``$= : 'a -> 'a -> bool``]
  end
fun is_logicconst x = mem x logicconstl_glob


fun th1_logicdef oc (thy,name) =
  (
  os oc ("thf(" ^ escape ("logicdef." ^ name) ^ ",axiom,"); 
  th1_logicformula oc (thy,name); osn oc ")."
  )

fun is_quantconst x = mem x [("bool","!"),("bool","?")]

fun th1_quantdef oc (thy,name) =
  let 
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val tm = concl thm
  in
    os oc ("thf(" ^ escape ("logicdef." ^ name) ^ ",axiom,"); 
    th1_formula oc tm; osn oc ")."
  end

fun write_boolextra dir = 
  let
    val file = dir ^ "/bool-extra.ax"
    val oc = TextIO.openOut file
  in
    (
    app (th1_logicdef oc) logicconstl_glob;
    app (th1_quantdef oc) [("bool","!"),("bool","?")];
    TextIO.closeOut oc
    )
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

(* -------------------------------------------------------------------------
   Export standard
   ------------------------------------------------------------------------- *)

val th1_dir = hh_dir ^ "/export_th1"

fun th1_export thyl =
  let
    val file = th1_dir ^ "/theory_order.info"
    val fl = (th1_tydef, th1_constdef, th1_thmdef, th1b_thm)
    val thyl = sorted_ancestry thyl
  in
    mkDir_err th1_dir;
    write_boolextra th1_dir;
    app (write_thy fl th1_dir) thyl;
    writel file [String.concatWith " " (sorted_ancestry thyl)]
  end

(* -------------------------------------------------------------------------
   Export bushy
   ------------------------------------------------------------------------- *)

val th1_bushy_dir = hh_dir ^ "/export_th1_bushy"

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
    val file = th1_bushy_dir ^ "/" ^ th1b_thm (thy,name) ^ ".p"
    val oc = TextIO.openOut file
    fun thmfetch (a,b) = DB.fetch a b
    val pretml = map (th1_prep_thm o thmfetch) ((thy,name) :: depl)
    val tml = mk_term_set (List.concat (map atoms_of pretml))
    val tyl = mk_type_set (List.concat (map type_set tml))
    val tyopl = mk_fast_set (cpl_compare id_compare Int.compare) 
      (List.concat (map tyop_set tyl))
    val cl = mk_term_set (List.concat (map const_set tml)) 
    fun ftyop ((tyopthy,tyopname),tyoparity) = 
      th1_tydef oc tyopthy (tyopname,tyoparity)
    fun fc c =
      let 
        val {Name=cname,Thy=cthy,...} = dest_thy_const c 
        val cid = (cthy,cname)
      in
        th1_constdef oc cid;
        (
        if is_logicconst cid then th1_logicdef oc cid
        else if is_quantconst cid then th1_quantdef oc cid
        else ()
        )
      end
    fun fax (axthy,axname) =
      let val axthm = DB.fetch axthy axname in
        th1_thmdef oc axthy ((axname,axthm),"axiom") 
      end
  in
    (
    app ftyop tyopl; app fc cl; app fax depl;
    th1_thmdef oc thy ((name,thm),"conjecture"); 
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

fun th1_export_bushy thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err th1_bushy_dir; app write_thy_bushy thyl
  end

(* -------------------------------------------------------------------------
   Export chainy
   ------------------------------------------------------------------------- *)

val th1_chainy_dir = hh_dir ^ "/export_th1_chainy"

fun include_thy oc thy = osn oc ("include('" ^ thy ^ ".ax').")
fun include_thydecl oc thy = osn oc ("include('" ^ thy ^ "-decl.ax').")

fun write_thyaxiom dir thy =
  let
    val file = dir ^ "/" ^ thy ^ ".ax"
    val oc = TextIO.openOut file
  in
    let
      val THEORY(_,t) = dest_theory thy
      val _ = app (th1_tydef oc thy) (#types t)
      val cl = map (fn (name,_) => (thy,name)) (#consts t)
      val _ = app (th1_constdef oc) cl
      val axl0 = map (fn x => (x,"axiom")) (DB.thms thy)
      fun cmp (((_,th1),_),((_,th2),_)) =
        Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
      val axl1 = dict_sort cmp axl0
    in
      app (th1_thmdef oc thy) axl1;
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
      val _ = app (th1_tydef oc thy) (#types t)
      val cl = map (fn (name,_) => (thy,name)) (#consts t)
      val _ = app (th1_constdef oc) cl
    in
      TextIO.closeOut oc
    end
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

fun write_cj_chainy thyl thy (name,thm) =
  let 
    val file = th1_chainy_dir ^ "/" ^ th1b_thm (thy,name) ^ ".p"
    val oc = TextIO.openOut file
    fun thmfetch (a,b) = DB.fetch a b
    val axl0 = DB.thms thy
    val axl1 = filter (older_than thm) axl0
    fun cmp ((_,th1),(_,th2)) =
      Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
    val axl2 = map (fn (x,_) => (thy,x)) (dict_sort cmp axl1)
    fun fax (axthy,axname) =
      let val axthm = DB.fetch axthy axname in
        th1_thmdef oc axthy ((axname,axthm),"axiom") 
      end
  in
    (
    app (include_thy oc) thyl;
    include_thydecl oc thy;
    include_thy oc "bool-extra";
    app fax axl2;
    th1_thmdef oc thy ((name,thm),"conjecture"); 
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
fun th1_export_chainy thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err th1_chainy_dir; 
    write_boolextra th1_chainy_dir;
    app (write_thyaxiom th1_chainy_dir) thyl;
    app (write_thydecl th1_chainy_dir) thyl;
    app (write_thy_chainy thyl) thyl
  end

(* Example
  load "hhExportThf"; open hhExportThf;
  th1_export_bushy ["list"]; th1_export_chainy ["list"];
*)

end (* struct *)
