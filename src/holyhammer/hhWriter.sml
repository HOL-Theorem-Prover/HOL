(* ===================================================================== *)
(* FILE          : hhWriter.sml                                          *)
(* DESCRIPTION   : Print objects (constants, types and theorems) and     *)
(*                 dependencies  theorems for holyHammer.                *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)


structure hhWriter :> hhWriter =
struct

open HolKernel boolLib tttTools TextIO Tag Dep

val ERR = mk_HOL_ERR "hhWriter"

(*---------------------------------------------------------------------------
   Dictionaries
 ----------------------------------------------------------------------------*)

(* reserved names *)
val hollight_theorems = ["HL_TRUTH", "HL_FALSITY", "HL_BOOL_CASES", "HL_EXT"];
val conjecture_name = "conjecture"
val reserved_names = conjecture_name :: hollight_theorems
val reserved_names0 = map (fn x => (x,0)) reserved_names

(*---_-----------------------------------------------------------------------
   Save new objects in the dictionnaries.
 ----------------------------------------------------------------------------*)

fun is_tptp_sq_char c =
  let val n = Char.ord c in
    (40 <= n andalso n <= 176) andalso
    (c <> #".") andalso
    (c <> #"/") andalso
    (c <> #":") andalso
    (c <> #"|") andalso
    (c <> #"\134") (* TODO: why? *)
  end

(* TODO: use String.translate *)
fun hh_escape s =
  let
    val l1 = String.explode s
    fun image c =
      if is_tptp_sq_char c
      then [c]
      else [#"|"] @ String.explode (int_to_string (Char.ord c)) @ [#"|"]
    val l2 = map image l1
  in
    String.implode (List.concat l2)
  end

fun squotify name = "'" ^ name ^ "'"
fun full_escape name = "'" ^ hh_escape name ^ "'"

(* TODO: make robust to empty vartype name *)
(* nice printing *)
fun nice_dest_vartype v =
  let
    val s = dest_vartype v
    val l = String.explode s
  in
    if hd l = #"'" then String.implode (map Char.toUpper (tl l)) else s
  end

(* renaming *)
(* only used for variables *)
fun variant_name_dict s used =
  let
    val i = dfind s used
    fun new_name s i =
      let val si = s ^ Int.toString i in
        if dmem si used
        then new_name s (i + 1)
        else (full_escape si, dadd s (i + 1) (dadd si 0 used))
      end
  in
    new_name s i
  end
  handle NotFound => (full_escape s, dadd s 0 used)

fun store_name state name =
  let val dict = #used_names state in
    if dmem name (!dict) then () else dict := dadd name 0 (!dict)
  end

(* types *)
fun declare_perm_type state {Thy,Name} =
  let
    val name1 = "type." ^ Thy ^ "." ^ (hh_escape Name)
    val name2 = squotify name1
    val dict = #ty_names state
  in
    store_name state name1; (* may be deprecated *)
    dict := dadd {Thy=Thy,Name=Name} name2 (!dict);
    name2
  end

(* constants *)
fun declare_perm_const state {Thy,Name} =
  let
    val name1 = "const." ^ Thy ^ "." ^ (hh_escape Name)
    val name2 = squotify name1
    val dict = #const_names state
  in
    store_name state name1;
    dict := dadd {Thy=Thy,Name=Name} name2 (!dict);
    name2
  end

(* theorems *)
fun declare_perm_thm state (thy,n) name  =
  let
    val name1 = "thm." ^ thy ^ "." ^ (hh_escape name)
    val name2 = squotify name1
    val dict = #thm_names state
  in
    store_name state name1;
    dict := dadd (thy,n) name2 (!dict);
    name2
  end

(* special constants *)
fun declare_fixed state dict {Thy,Name} name =
  (
  store_name state name;
  dict := dadd {Thy=Thy,Name=Name} name (!dict);
  name
  )

(* temporary variables and type variables *)
fun declare_temp_list state get_name dict l =
  let
    val olddict = !dict
    val oldused = !(#used_names state)
    fun fold_fun (s,sl) =
      let
        val useddict = #used_names state
        val (news, newused) = variant_name_dict (get_name s) (!useddict)
      in
        dict := dadd s news (!dict);
        useddict := newused;
        news :: sl
      end
    val sl = foldl fold_fun [] l
    fun undeclare () =
      let val usedref = #used_names state in
        dict := olddict; usedref := oldused
      end
  in
    (List.rev sl, undeclare)
  end

(*---------------------------------------------------------------------------
   Streams. Objects and dependencies are written in different files.
 ----------------------------------------------------------------------------*)

fun os oc s = output (oc,s)
fun oiter_aux oc sep f =
 fn [] => ()
  | [e] => f e
  | h :: t => (f h; output (oc,sep); oiter_aux oc sep f t)
fun oiter_deps oc_deps sep f l = oiter_aux oc_deps sep f l
fun oiter oc sep f l = oiter_aux oc sep f l

(*---------------------------------------------------------------------------
   Printing objects (types, constants, theorems' conjuncts).
 ----------------------------------------------------------------------------*)

(* type *)
fun oty state oc ty =
  if is_vartype ty
    then os oc (dfind_err "tyvar" ty (!(#tyvar_names state)))
  else
    let val {Args,Thy,Tyop} = dest_thy_type ty in
    let val s = dfind {Thy=Thy,Name=Tyop} (!(#ty_names state)) in
      if null Args then os oc s else
        if (Thy ="min" andalso Tyop = "fun")
        then (os oc "("; oty state oc (hd Args); os oc " > ";
              oty state oc (hd (tl Args)); os oc ")")
        else (os oc ("(" ^ s ^ " ");
              oiter oc " " (oty state oc) Args; os oc ")")
    end end

type ('a,'b)substp = {redex : 'a, residue : 'b}
val less_ty = fn a => (fn b => Type.compare (a,b) = LESS)
fun less_red (a:(hol_type,'a)substp) (b:(hol_type,'b)substp) =
  less_ty (#redex a) (#redex b)

fun id_subst a = {redex = a, residue = a}
fun full_match_type t1 t2 =
  let
    val (subst1,al) = raw_match_type t1 t2 ([],[])
    val subst2 = map id_subst al
  in
    sort less_red (subst1 @ subst2)
  end

(* term *)
fun otm state oc tm =
  if is_var tm then os oc (dfind_err "var" tm (!(#var_names state)))
  else if is_const tm then
    let
      val {Thy, Name, Ty} = dest_thy_const tm
      val mgty = type_of (prim_mk_const {Thy = Thy, Name = Name})
      val subst = full_match_type mgty Ty
      val resl = map #residue subst
    in
      if null resl
      then os oc (dfind {Thy=Thy,Name=Name} (!(#const_names state)))
      else (os oc "(";
            os oc (dfind {Thy=Thy,Name=Name} (!(#const_names state)));
            os oc " ";
            oiter oc " " (oty state oc) resl;
            os oc ")")
    end
  else if is_eq tm       then
    (os oc "("; otm state oc (lhs tm);   os oc " = ";  otm state oc (rhs tm);  os oc ")")
  else if is_conj tm     then
    (os oc "("; otm state oc (lhand tm); os oc " & ";  otm state oc (rand tm); os oc ")")
  else if is_disj tm     then
    (os oc "("; otm state oc (lhand tm); os oc " | ";  otm state oc (rand tm); os oc ")")
  else if is_imp_only tm then
    (os oc "("; otm state oc (lhand tm); os oc " => "; otm state oc (rand tm); os oc ")")
  else if is_neg tm      then (os oc "(~ "; otm state oc (rand tm); os oc ")")
  else if is_forall tm   then hh_binder state oc "!" (strip_forall tm)
  else if is_exists tm   then hh_binder state oc "?" (strip_exists tm)
  else if is_abs tm      then hh_binder state oc "^" (strip_abs tm)
  else if is_comb tm then
    let val (v,l) = strip_comb tm in
      (os oc "("; otm state oc v; app (fn x => (os oc " "; otm state oc x)) l; os oc ")")
    end
  else raise ERR "otm" ""
and hh_binder state oc s (l,tm) =
  let
    val (vl,undeclare) =
      declare_temp_list state (fst o dest_var) (#var_names state) l
    fun f x =
      (os oc (dfind_err "var" x (!(#var_names state)));
       os oc " : "; oty state oc (type_of x))
  in
    os oc ("(" ^ s ^ "[");
    oiter oc ", " f l;
    os oc "]: "; otm state oc tm; os oc ")";
    undeclare ()
  end

(* type definition *)
fun hh_tydef state oc thy (s,arity) =
  case (thy,s) of
    ("min","bool") =>
    ignore (declare_fixed state (#ty_names state) {Thy=thy,Name=s} "$o")
  | ("min","fun")  =>
    ignore (declare_fixed state (#ty_names state) {Thy=thy,Name=s} "$fun")
  | _  =>
    let val news = declare_perm_type state {Thy=thy,Name=s} in
      os oc "tt("; os oc news; os oc ", ty, ";
      let fun tyd i = case i of
          0 => os oc "$t"
        | n => (os oc "$t > "; tyd (n - 1))
      in
        (tyd arity; os oc ").\n")
      end
    end

fun quant_tyvarl oc l =
  if null l then ()
  else (os oc "!["; oiter oc ", " (fn x => (os oc x; os oc " : $t")) l; os oc "]: ")

(* constant definition *)
fun hh_constdef state oc thy (s,ty) =
  let
    val fix = declare_fixed state (#const_names state) {Thy=thy,Name=s}
    val news = case (thy,s) of
    ("min","=")     => fix "$equals"
  | ("bool","!")    => fix "$forall"
  | ("bool","?")    => fix "$exists"
  | ("bool","/\\")  => fix "$and"
  | ("bool","\\/")  => fix "$or"
  | ("min","==>")   => fix "$imply"
  | ("bool","~")    => fix "$not"
  | ("bool","T")    => fix "$true"
  | ("bool","F")    => fix "$false"
  | _               => declare_perm_const state {Thy=thy,Name=s}
    val tv = sort less_ty (type_vars ty)
    val (newtvs, undeclare) =
      declare_temp_list state nice_dest_vartype (#tyvar_names state) tv
  in
    (
    os oc "tt("; os oc news; os oc ", ty, ";
    case newtvs of [] => () | l => quant_tyvarl oc l;
    oty state oc ty; os oc ").\n"; undeclare ()
    )
  end

(* theorems *)
fun othm state oc (name,role,tm) =
  let
    fun f x = is_var x orelse is_const x
    val l1 = type_varsl (map type_of (find_terms f tm))
    val (l2, undeclare) =
      declare_temp_list state nice_dest_vartype (#tyvar_names state) l1
  in
    (
    if uptodate_term tm
    then (os oc "tt("; os oc name;
          os oc (", " ^ role ^ ", "); quant_tyvarl oc l2;
          otm state oc tm;
          os oc ").\n")
    else ()
    handle _ => tttTools.debug ("Error: othm: " ^ term_to_string tm)
                (* TODO: reraise Interrupt *)
                (* TODO: to be removed for parallelization *)
    ;
    undeclare ()
    )
  end

fun othm_theorem state oc (name,role,thm) =
  othm state oc (name,role,concl (GEN_ALL (DISCH_ALL thm)))

(* conjecture *)
fun othm_conjecture state oc conjecture =
  othm state oc (conjecture_name, conjecture_name,
        list_mk_forall (free_vars_lr conjecture,conjecture))


(*---------------------------------------------------------------------------
   Printing dependencies.
 ----------------------------------------------------------------------------*)

fun thm_of_depid (thy,n) =
  let
    val thml = DB.thms thy
    fun find_number x =
      if (depnumber_of o depid_of o dep_of o tag o snd) x = n
      then x
      else raise ERR "find_number" ""
  in
    tryfind find_number thml
    handle _ => raise ERR "thm_of_depid" "Not found"
    (* TODO: reraise Interrupt *)
  end

fun exists_depid did = can thm_of_depid did

fun pred_of_depid (thy,n) =
  let
    val thml = DB.thms thy
    (* TODO: this function is duplicated above; write it once only *)
    fun find_number x =
      if (depnumber_of o depid_of o dep_of o tag o snd) x = n
      then x
      else raise ERR "find_number" ""
  in
    (thy, fst (tryfind find_number thml))
    handle _ => raise ERR "thmid_of_depid" "Not found"
  end

fun depl_as_pred thm =
  let
    val d = (dep_of o tag) thm
    val dl = depidl_of d
    val idl = mapfilter pred_of_depid dl
  in
    (length idl = length dl, idl)
  end

fun odep state oc_deps (name,dl) =
  let
    fun os_deps s = output (oc_deps,s)
    fun name_did did = dfind_err "thm" did (!(#thm_names state))
  in
    os_deps (name ^ " ");
    oiter_deps oc_deps " " os_deps (mapfilter name_did dl);
    os_deps "\n"
  end

(*---------------------------------------------------------------------------
   Exporting a theorem and its dependencies
 ----------------------------------------------------------------------------*)

fun export_thm state oc oc_deps ((name,thm),role) =
  let
    val d = (dep_of o tag) thm
    val did = depid_of d
    val dl = filter exists_depid (depidl_of d)
    val name' = declare_perm_thm state did name
  in
    othm_theorem state oc (name',role,thm);
    odep state oc_deps (name',dl)
  end

(*---------------------------------------------------------------------------
   Printing theories
 ----------------------------------------------------------------------------*)

(* TODO: use OS.Path.concat *)
fun write_thy dir filter_f state thy =
  let
    val oc = openOut (dir ^ "/" ^ thy ^ ".p")
    val oc_deps = openOut (dir ^ "/" ^ thy  ^ ".hd")
    val THEORY(_,t) = dest_theory thy
    val _ = app (hh_tydef state oc thy) (#types t)
    val _ = app (hh_constdef state oc thy) (#consts t)
    val axl = map (fn x => (x,"ax")) (DB.theorems thy) (* TODO: why not (#theorems t) etc.? *)
    val defl = map (fn x => (x,"def")) (DB.axioms thy @ DB.definitions thy)
    fun local_compare (((_,th1),_),((_,th2),_)) =
      let val f = depnumber_of o depid_of o dep_of o Thm.tag in
        Int.compare (f th1, f th2)
      end
    val thml = filter (filter_f thy) (dict_sort local_compare (axl @ defl))
  in
    app (export_thm state oc oc_deps) thml;
    closeOut oc;
    closeOut oc_deps
  end

fun write_thydep file thyl =
  let
    val oc = openOut file
    fun f x = (os oc x; os oc " "; oiter oc " " (os oc) (parents x); os oc "\n")
  in
    app f thyl;
    os oc namespace_tag; os oc " ";
    oiter oc " " (os oc) [current_theory ()];
    os oc "\n";
    closeOut oc
  end

fun write_thyl dir filter_f thyl =
  let
    val state =
    {
    ty_names    = ref (dempty KernelSig.name_compare),
    const_names = ref (dempty KernelSig.name_compare),
    var_names   = ref (dempty Term.compare),
    tyvar_names = ref (dempty Type.compare),
    used_names  = ref (dnew String.compare reserved_names0),
    thm_names   = ref (dempty depid_compare)
    }
  in
    app (write_thy dir filter_f state) (sort_thyl thyl)
  end

fun write_conjecture state file conjecture =
  if type_of conjecture = bool
  then
    let val oc = openOut file in
      othm_conjecture state oc conjecture;
      closeOut oc
    end
  else raise ERR "write_conjecture" "conjecture is not a boolean"

(*---------------------------------------------------------------------------
   Writing theorems from the namespace.
 ----------------------------------------------------------------------------*)

fun write_ns state dir ns_thml =
  let
    val oc = openOut (dir ^ "/" ^ namespace_tag ^ ".p")
    val oc_deps = openOut (dir ^ "/" ^ namespace_tag ^ ".hd")
    fun new_name name =
      let val (thy,nm1) = split_string "Theory." name in
        squotify ("thm." ^ thy ^ "." ^ hh_escape nm1)
      end
    fun f (name,thm) =
      let val name' = new_name name in
        othm_theorem state oc (name',"ax",thm);
        odep state oc_deps (name',[])
      end
  in
    app f ns_thml;
    closeOut oc;
    closeOut oc_deps
  end

fun write_problem dir filter_f ns_thml thyl cj =
  let
    fun sort_thyl thyl = topo_sort (map (fn x => (x, ancestry x)) thyl)
    val state =
    {
    ty_names    = ref (dempty KernelSig.name_compare),
    const_names = ref (dempty KernelSig.name_compare),
    var_names   = ref (dempty Term.compare),
    tyvar_names = ref (dempty Type.compare),
    used_names  = ref (dnew String.compare reserved_names0),
    thm_names   = ref (dempty depid_compare)
    }
  in
    app (write_thy dir filter_f state) (sort_thyl thyl);
    write_ns state dir ns_thml;
    write_conjecture state (dir ^ "/conjecture.fof") cj (* not actually fof *)
  end



end
