(* ========================================================================= *)
(* FILE          : hhExportTh1.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(*                     Cezary Kaliszyk, University of Innsbruck              *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportTh1 :> hhExportTh1 =
struct

open HolKernel boolLib aiLib mlThmData hhTranslate hhExportLib

val ERR = mk_HOL_ERR "hhExportThf"

(* -------------------------------------------------------------------------
   Preparing and analysing the formula
   ------------------------------------------------------------------------- *)

fun th1_prep_tm tm = rename_bvarl escape (list_mk_forall (free_vars_lr tm, tm))
fun th1_prep_thm thm = th1_prep_tm (concl (DISCH_ALL thm))

(* -------------------------------------------------------------------------
    TH1 types,terms,formulas
   ------------------------------------------------------------------------- *)

fun th1_type oc ty =
  if is_vartype ty then os oc (name_vartype ty) else
    let val {Args, Thy, Tyop} = dest_thy_type ty in
      if Thy = "min" andalso Tyop = "bool" then os oc "$o"
      else if Thy = "min" andalso Tyop = "fun" then
        let val (tya,tyb) = pair_of_list Args in    
          os oc "("; th1_type oc tya;
          os oc " > "; th1_type oc tyb; os oc ")"
        end
      else if null Args then os oc (name_tyop (Thy,Tyop))
      else (os oc "("; os oc (name_tyop (Thy,Tyop)); os oc " @ ";
            oiter oc " @ " th1_type Args; os oc ")")
    end

fun th1_vty oc v =  
  let val (vs,ty) = dest_var v in os oc (vs ^ ":"); th1_type oc ty end

fun th1_term oc tm =
  if is_var tm then os oc (name_v tm)
  else if is_const tm then
    let val resl = typearg_of_const tm in
      if null resl
      then os oc (name_c tm)
      else (os oc "("; os oc (name_c tm); os oc " @ ";
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

fun th1_pred oc tm =
  if is_forall tm then th1_quant oc "!" (strip_forall tm)
  else if is_exists tm then th1_quant oc "?" (strip_exists tm)
  else if is_conj tm then th1_binop oc "&" (dest_conj tm)
  else if is_disj tm then th1_binop oc "|" (dest_disj tm)
  else if is_imp_only tm then th1_binop oc "=>" (dest_imp tm)
  else if is_neg tm then
    (os oc "(~ "; th1_pred oc (dest_neg tm); os oc ")")
  else if is_eq tm then
    let val (l,r) = dest_eq tm in
      if must_pred l orelse must_pred r
      then th1_binop oc "<=>" (l,r)
      else (os oc "("; th1_term oc l; os oc " = ";  
            th1_term oc r; os oc ")")
    end
  else th1_term oc tm
and th1_binop oc s (l,r) =
  (os oc "("; th1_pred oc l; os oc (" " ^ s ^ " "); 
   th1_pred oc r; os oc ")")
and th1_quant oc s (vl,bod) =
  (os oc s; os oc "["; oiter oc ", " th1_vty vl;
   os oc "]: "; th1_pred oc bod)

fun th1_formula oc tm =
  let 
    val tvl = type_vars_in_term tm 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o name_vartype) tvl
    val s = String.concatWith ", " tvls
  in
    if null tvl then () else os oc ("![" ^ s ^ "]: ");
    th1_pred oc tm
  end

(* -------------------------------------------------------------------------
    TH1 definitions
   ------------------------------------------------------------------------- *)

val thfpar = "thf("

fun th1_ttype arity =
  String.concatWith " > " (List.tabulate (arity + 1, fn _ => ttype))

fun th1_tyopdef oc ((thy,tyop),arity) =
  let val thfname = name_tyop (thy,tyop) in
    os oc (thfpar ^ thfname ^ ",type," ^ thfname ^ ":");
    os oc (th1_ttype arity); osn oc ")."
  end

fun th1_tyquant_type oc ty =
  let 
    val tvl = dict_sort Type.compare (type_vars ty) 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o name_vartype) tvl
    val s = String.concatWith "," tvls
  in
    if null tvl then () else os oc ("!>[" ^ s ^ "]: ");
    th1_type oc ty
  end

fun th1_cdef oc (thy,name) =
  let val ty = type_of (prim_mk_const {Thy = thy, Name = name}) in
    os oc (thfpar ^ name_cid (thy,name) ^ ",type,");
    os oc (name_cid (thy,name) ^ ":"); th1_tyquant_type oc ty; osn oc ")."
  end

fun th1_thmdef role oc (thy,name) =
  let
    val thm = DB.fetch thy name
    val tm = th1_prep_thm thm 
  in
    os oc (thfpar ^ (name_thm (thy,name)) ^ "," ^ role ^ ",");
    th1_formula oc tm; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Logical operators equations with term level counterpart.
   ------------------------------------------------------------------------- *)

val boolop_extra = "boolop-extra"

fun th1_logicformula oc (thy,name) = 
  let 
    val c = prim_mk_const {Thy = thy, Name = name}
    val tm = full_apply_const c
    val tvl = type_vars_in_term tm 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o name_vartype) tvl
    val s = String.concatWith ", " tvls
    val vl = free_vars_lr tm 
  in
    if null tvl then () else os oc ("![" ^ s ^ "]: ");
    os oc "!["; oiter oc ", " th1_vty vl; os oc "]: ";
    os oc "("; th1_term oc tm ; os oc " <=> "; th1_pred oc tm; os oc ")"
  end

fun th1_logicdef oc (thy,name) =
  (
  os oc (thfpar ^ escape ("logicdef." ^ name) ^ ",axiom,"); 
  th1_logicformula oc (thy,name); osn oc ")."
  )

fun th1_quantdef oc (thy,name) =
  let 
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val tm = th1_prep_thm thm
  in
    os oc (thfpar ^ escape ("quantdef." ^ name) ^ ",axiom,"); 
    th1_formula oc tm; osn oc ")."
  end

fun write_boolop_extra dir = 
  let
    val file = dir ^ "/" ^ boolop_extra ^ ".ax"
    val oc = TextIO.openOut file
    val l1 = map cid_of [``$/\``,``$\/``,``$~``,``$==>``,
      ``$= : 'a -> 'a -> bool``]
    val l2 = map cid_of [``$! : ('a -> bool) -> bool``,
      ``$? : ('a -> bool) -> bool``]
  in
    (app (th1_logicdef oc) l1; app (th1_quantdef oc) l2;
     TextIO.closeOut oc)
    handle Interrupt => (TextIO.closeOut oc; raise Interrupt)
  end

(* -------------------------------------------------------------------------
   Export
   ------------------------------------------------------------------------- *)

fun th1_formulal_of_pb (thmid,depl) = 
  map (th1_prep_thm o fetch_thm) (thmid :: depl)

val th1_bushy_dir = hh_dir ^ "/export_th1_bushy"
fun th1_export_bushy thyl =
  let 
    val thyl = sorted_ancestry thyl 
    val dir = th1_bushy_dir
    val inl = ([],[],[boolop_extra])
    fun f thy =
      write_thy_bushy dir inl
        (th1_tyopdef,th1_cdef,th1_thmdef)
        th1_formulal_of_pb thy
  in
    mkDir_err dir; write_boolop_extra dir; app f thyl
  end

val th1_chainy_dir = hh_dir ^ "/export_th1_chainy"
fun th1_export_chainy oldthyl =
  let 
    val thyl = sorted_ancestry oldthyl
    val dir = th1_chainy_dir
    val inl = ([],[],[boolop_extra])
    fun f thy = write_thy_chainy dir inl th1_thmdef thyl thy 
  in
    mkDir_err dir; 
    write_boolop_extra dir;
    app (write_thytyopdef dir th1_tyopdef) thyl;
    app (write_thycdef dir th1_cdef) thyl;
    app (write_thyax dir th1_thmdef) thyl;
    app f thyl
  end



end (* struct *)
