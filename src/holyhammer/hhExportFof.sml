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

val fofpar = "fof("
fun fof_prep_thm thm = 
  let val tml = translate_tm (concl (DISCH_ALL thm)) in
    (hd tml, rev (tl tml))
  end

(* -------------------------------------------------------------------------
   FOF terms
   ------------------------------------------------------------------------- *)

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
      if must_pred l orelse must_pred r
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
   Logical operators equations with term level counterpart.
   ------------------------------------------------------------------------- *)

fun fof_logicformula oc (thy,name) = 
  let 
    val c = prim_mk_const {Thy = thy, Name = name}
    val tm = full_apply_const c
    val tvl = type_vars_in_term tm 
    val tvls = map ((fn x => x ^ ":" ^ ttype) o name_vartype) tvl
    val s = String.concatWith ", " tvls
    val vl = free_vars_lr tm 
  in
    if null tvl then () else os oc ("![" ^ s ^ "]: ");
    os oc "!["; oiter oc ", " fof_vty vl; os oc "]: ";
    os oc "("; fof_term oc tm ; os oc " <=> "; fof_pred oc tm; os oc ")"
  end

fun fof_logicdef oc (thy,name) =
  (os oc (fofpar ^ escape ("logicdef." ^ name) ^ ",axiom,"); 
   fof_logicformula oc (thy,name); osn oc ").")

fun fof_quantdef oc (thy,name) =
  let 
    val thm = assoc name [("!", FORALL_THM),("?", EXISTS_THM)]
    val (tm,_) = fof_prep_thm thm
  in
    os oc (fofpar ^ escape ("quantdef." ^ name) ^ ",axiom,"); 
    fof_formula oc tm; osn oc ")."
  end

fun fof_boolopdef oc (thy,name) = 
  let
    val l1 = map cid_of [``$/\``,``$\/``,``$~``,``$==>``,
      ``$= : 'a -> 'a -> bool``]
    val l2 = map cid_of [``$! : ('a -> bool) -> bool``,
      ``$? : ('a -> bool) -> bool``]
  in
    if mem (thy,name) l1 then fof_logicdef oc (thy,name)
    else if mem (thy,name) l2 then fof_quantdef oc (thy,name)
    else ()
  end

(* -------------------------------------------------------------------------
   FOF definitions
   ------------------------------------------------------------------------- *)

fun fof_tyopdef oc _ = ()

fun fof_cdef_arity oc (c,arity) =
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

fun fof_cdef oc (thy,name) =
  let
    val c = prim_mk_const {Thy = thy, Name = name}
    val ty = type_of c
    val maxarity = length (snd (strip_funty ty))
    fun f n = fof_cdef_arity oc (c,n)
  in
    ignore (List.tabulate (maxarity + 1, f));
    fof_boolopdef oc (thy,name)
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

fun fof_thmdef role oc (thy,name) =
  let 
    val thm = DB.fetch thy name
    val (cj,defl) = fof_prep_thm thm
    val vl = free_vars_lr (list_mk_conj (cj :: defl))
    val tf1name = name_thm (thy,name)
    fun f i def = 
      (
      os oc (fofpar ^ escape ("def" ^ its i ^ ".") ^ tf1name ^ ",axiom,");
      fof_formula oc def; osn oc ")."
      )
  in
    app (fof_vdef oc) vl;
    ignore (mapi f defl);
    os oc (fofpar ^ tf1name ^ "," ^ role ^ ",");
    fof_formula oc cj; osn oc ")."
  end

(* -------------------------------------------------------------------------
   Higher-order caster
   ------------------------------------------------------------------------- *)

val hocaster_extra = "hocaster-extra"

val notfalse = EQT_ELIM (last (CONJ_LIST 3 NOT_CLAUSES))

val pcaster_axioml =
  [("truth", TRUTH), ("notfalse", notfalse), ("bool_cases_ax", BOOL_CASES_AX)]

fun fof_caster_thmdef oc (name,thm) =
  let 
    val (cj,defl) = fof_prep_thm thm
    val _ = if null defl then () else raise ERR "fof_caster_thmdef" ""
  in
    os oc (fofpar ^ name_thm (hocaster_extra,name) ^ ",axiom,");
    fof_formula oc cj; osn oc ")."
  end

fun fof_caster_app oc = fof_caster_thmdef oc ("eq_ext", EQ_EXT)
fun fof_caster_p oc = app (fof_caster_thmdef oc) pcaster_axioml

fun write_hocaster_extra dir = 
  let
    val file = dir ^ "/" ^ hocaster_extra ^ ".ax"
    val oc = TextIO.openOut file
  in
    let
      val thy = "combin"
      fun mk_id (name,_) = (thy,name)
      val THEORY(_,t) = dest_theory thy
      val cl0 = ["S","K","I"]
      val cl1 = #consts t
      val cl2 = filter (fn x => mem (fst x) cl0) cl1
      val axl0 = map (fn x => x ^ "_DEF") cl0
      val axl1 = filter (fn x => mem (fst x) axl0) (DB.definitions thy)
    in
      (
      fof_caster_app oc; fof_caster_p oc;
      combin_namespace_flag := true;
      app (fof_cdef oc) (map mk_id cl2);
      app (fof_thmdef "axiom" oc) (map mk_id axl1);
      combin_namespace_flag := false;
      TextIO.closeOut oc
      )
    end 
    handle Interrupt => 
    (TextIO.closeOut oc; combin_namespace_flag := false; raise Interrupt)
  end


(* -------------------------------------------------------------------------
   Export standard
   ------------------------------------------------------------------------- *)




end (* struct *)
