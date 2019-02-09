(* ===================================================================== *)
(* FILE          : hhExport.sml                                          *)
(* DESCRIPTION   : Export HOL4 theories in a s-expression format         *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2018                                                  *)
(* ===================================================================== *)

structure hhExport :> hhExport =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate holyHammer

val ERR = mk_HOL_ERR "hhExport"



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

(*
fun tf1_top_cdef oc arity (tfname,ty) =
  (os oc ("tff(" ^ tfname ^ ",type," ^ tfname ^ ":");
   tf1_tyquant_type oc arity ty; osn oc ").")

fun write_tf1_app dir = 
  let
    val file = dir ^ "/app-extra.ax"
    val oc = TextIO.openOut file
  in
    let
      val ty = type_of (prim_mk_const {Thy = "bool", Name = "LET"})
      val tfname = "app_2"
    in
      tf1_top_cdef oc arity (tfname,ty);
      TextIO.closeOut oc
    end 
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end 
*)

(* -------------------------------------------------------------------------
   Logical operators equations with term level counterpart.
   ------------------------------------------------------------------------- *)

fun full_apply_const c =
  let 
    val (imty,argtyl) = strip_funty (type_of c)
    fun f i x = mk_var ("V" ^ its i,x)
    val vl = mapi f argtyl 
  in
    list_mk_comb (c,vl)
  end    

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
    os oc "!["; oiter oc ", " th1_var_and_type vl; os oc "]: ";
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

fun is_quantconst x = mem x [("bool","!"),("bool","?")]

fun th1_quantdef oc (thy,name) =
  let 
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val tm = concl thm
  in
    comment oc (term_to_string tm);
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
   Bushy and chainy exports
   ------------------------------------------------------------------------- *)

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
    val pretml = map (prep_thm o thmfetch) depl
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

fun include_thy oc thy = osn oc ("include('" ^ thy ^ ".ax').")
fun include_thydecl oc thy = osn oc ("include('" ^ thy ^ "-decl.ax').")

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

fun before_elem e l = case l of
    [] => raise ERR "before_elem" ""
  | a :: m => if a = e then [] else a :: before_elem e m

fun older_than th1 (name,th2) = 
  depnumber_of_thm th2 < depnumber_of_thm th1

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

(* -------------------------------------------------------------------------
   Export functions
   ------------------------------------------------------------------------- *)

fun add_ancestry thy = thy :: ancestry thy
fun sorted_ancestry thyl = 
  sort_thyl (mk_string_set (List.concat (map add_ancestry thyl)))

(* load_sigobj (); sort_thyl (ancestry "scratch"); *)
fun th1_export_bushy thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err th1_bushy_dir; app write_thy_bushy thyl
  end

fun th1_export_chainy thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err th1_chainy_dir; 
    write_boolextra th1_chainy_dir;
    app (write_thyaxiom th1_chainy_dir) thyl;
    app (write_thydecl th1_chainy_dir) thyl;
    app (write_thy_chainy thyl) thyl
  end

(*
fun th1_export thyl =
  let
    val file = th1_dir ^ "/theory_order.info"
    val fl = (th1_tydef, th1_constdef, th1_thmdef, th1b_thm)
    val thyl = sorted_ancestry thyl
  in
    mkDir_err th1_dir;
    write_combin fl th1_dir;
    write_logic th1_dir;
    app (write_thy fl th1_dir) thyl;
    writel file [String.concatWith " " (sorted_ancestry thyl)]
  end

fun th1_export_decl thyl =
  let
    val fl = (th1_tydef, th1_constdef)
    val thyl = sorted_ancestry thyl
  in
    mkDir_err th1_decl_dir; app (write_thy_decl fl th1_decl_dir) thyl
  end

fun th1_export_ax thyl =
  let val thyl = sorted_ancestry thyl in
    mkDir_err th1_ax_dir; 
    app (write_thy_ax th1_thmdef th1_ax_dir) thyl
  end

fun tf1_export thyl =
  let
    val file = tf1_dir ^ "/theory_order.info"
    val fl = (tf1_tydef, tf1_constdef, tf1_thmdef, tf1b_thm)
    val thyl = sorted_ancestry thyl
  in
    mkDir_err tf1_dir;
    write_combin fl tf1_dir;
    write_logic tf1_dir;
    app (write_thy fl tf1_dir) thyl;
    writel file [String.concatWith " " (sorted_ancestry thyl)]
  end

fun sexpr_export thyl =
  let
    val file = sexpr_dir ^ "/theory_order.info"
    val fl = (sexpr_tydef, sexpr_constdef, sexpr_thmdef, sexprb_thm)
    val thyl = sorted_ancestry thyl
  in
    mkDir_err sexpr_dir;
    app (write_thy fl sexpr_dir) thyl;
    writel file [String.concatWith " " (sorted_ancestry thyl)]
  end

(* -------------------------------------------------------------------------
   fof
   ------------------------------------------------------------------------- *)

val fof_export_dir = HOLDIR ^ "/src/holyhammer/export_fof"
val fof_targets_file = fof_export_dir ^ "/fof_targets"
val fof_problems_dir = fof_export_dir ^ "/fof_problems"
val fof_chainy_dir = fof_export_dir ^ "/fof_chainy"

fun fof_export_pb (file,(premises,cj)) =
  (
  append_endline fof_targets_file file;
  translate_write_file file (premises,cj)
  )

fun fof_export_thy thy =
  let
    val _ = mkDir_err fof_export_dir
    val _ = mkDir_err fof_problems_dir
    val thml = DB.theorems thy
    val pbl1 = map_snd (fn x => (intactdep_of_thm x, x)) thml
    val pbl2 = filter (fn (_,x) => fst (fst x)) pbl1
    val pbl3 = map_snd (fn (a,b) => (snd a, list_mk_imp (dest_thm b))) pbl2
    val pbl4 = map_fst (fn x => fof_problems_dir ^ "/" ^ th1b_thm (thy,x)) pbl3
  in
    app fof_export_pb pbl4
  end
*)
(*
fun fof_export_statement_thy thy =
  let
    val _ = mkDir_err fof_export_dir
    val _ = mkDir_err fof_problems_dir
    val thml = DB.thms thy
    fun cmp ((_,th1),(_,th2)) =
      Int.compare (depnumber_of_thm th1, depnumber_of_thm th2)
    val pbl1 = map_snd (fn x => ([], x)) thml
    val pbl3 = map_snd (fn (a,b) => (a, list_mk_imp (dest_thm b))) pbl1
    val pbl4 = map_fst (fn x => fof_problems_dir ^ "/" ^ sexpr_thm (thy,x)) pbl3
  in
    app fof_export_pb pbl4
  end
*)

end (* struct *)

(* Example
  load "hhExport"; open hhExport;
  th1_export_bushy ["list"];
  
  comment_flag := true;  

*)
