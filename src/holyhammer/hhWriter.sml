(* ===================================================================== *)
(* FILE          : hhWriter.sml                                          *)
(* DESCRIPTION   : Print objects (constants, types and theorems) and     *)
(*                 dependencies between conjuncts of theorems for        *)
(*                 holyHammer.                                           *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)


structure hhWriter :> hhWriter =
struct

open HolKernel boolLib TextIO Tag Dep

val ERR = mk_HOL_ERR "hhWriter"

(*---------------------------------------------------------------------------
   Dictionaries
 ----------------------------------------------------------------------------*)

(* Shorter accessors and constructors *)
fun dfind k m = Redblackmap.find (m,k)
fun dmem k m = Lib.can (dfind k) m
fun dadd i v m = Redblackmap.insert (m,i,v)
val dempty = Redblackmap.mkDict

val ty_names = ref (dempty KernelSig.name_compare)
val const_names = ref (dempty KernelSig.name_compare)
val var_names = ref (dempty Term.compare)
val tyvar_names = ref (dempty Type.compare)

val writehh_names = ref (dempty depid_compare)

(* Keeping track of which names are already used to prevent clashes. *)
val used_names = ref (dempty String.compare)

(* reserved names *)
val hollight_theorems = ["HL_TRUTH", "HL_FALSITY", "HL_BOOL_CASES", "HL_EXT"];
val conjecture_name = "conjecture"
val reserved_names = conjecture_name :: hollight_theorems
fun reserve name = used_names := dadd name 0 (!used_names)

(* Initialisation *)

fun reset_dicts () =
(
  ty_names := dempty KernelSig.name_compare;
  const_names := dempty KernelSig.name_compare;
  var_names := dempty Term.compare;
  tyvar_names := dempty Type.compare;
  used_names := dempty String.compare; (* contains non escaped names *)
  app reserve reserved_names;
  writehh_names := dempty depid_compare
)

(*---------------------------------------------------------------------------
   Absolute limit on the size of theorems (to be removed)
 ----------------------------------------------------------------------------*)
val size_limit = 200
fun size_of_term t =
       if is_abs t
    then let val (v,t') = dest_abs t in 1 + size_of_term t' end
  else if is_comb t
    then let val (t1,t2) = dest_comb t in size_of_term t1 + size_of_term t2 end
  else if is_var t orelse is_const t
    then 1
  else raise ERR "size_of_term" ""

fun is_oversized_term t = size_of_term t > size_limit

fun is_oversized_thm thm =
  let
    val thml = BODY_CONJUNCTS thm
    val terml = map (concl o GEN_ALL o DISCH_ALL) thml
  in
    exists is_oversized_term terml
  end

(*---------------------------------------------------------------------------
   Save new objects in the dictionnaries.
 ----------------------------------------------------------------------------*)
(* escaping *)
fun is_alphanumeric s =
 let val l = String.explode s in
   all (fn x => Char.isAlphaNum x orelse x = #"_") l
 end

(* now additonnally escape quotes for the feature generation algorithm *)
fun hh_escape s =
  let
    val l1 = String.explode s
    fun image x =
      case x of
        #"#"  => String.explode "#hash#"
      | #"/"  => String.explode "#slash#"
      | #"\"" => String.explode "#quote#"
      | #"\\" => String.explode "#bslash#"
      | #"'" => String.explode "#squote#"
      | _     => [x]
    val l2 = map image l1
  in
    String.implode (List.concat l2)
  end

fun squotify name = "'" ^ name ^ "'"
fun full_escape name = "'" ^ hh_escape name ^ "'"


(* TO BE MOVED *)
(* use a similar escaping than the holyhammer fof writer *)
fun reserved_escape name =
  if is_alphanumeric name andalso Char.isLower (hd (String.explode name))
  then name
  else "'" ^ name ^ "'"

val reserved_names_escaped = map reserved_escape reserved_names


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

fun store_name name =
  if dmem name (!used_names)
  then ()
  else used_names := dadd name 0 (!used_names)

fun store_name name =
  if dmem name (!used_names)
  then ()
  else used_names := dadd name 0 (!used_names)

(* types *)
fun declare_perm_type dict {Thy,Name} =
  let
    val name1 = "type/" ^ Thy ^ "/" ^ (hh_escape Name)
    val name2 = squotify name1
  in
    store_name name1;
    dict := dadd {Thy=Thy,Name=Name} name2 (!dict);
    name2
  end

(* constants *)
fun declare_perm_const dict {Thy,Name} =
  let
    val name1 = "const/" ^ Thy ^ "/" ^ (hh_escape Name)
    val name2 = squotify name1
  in
    store_name name1;
    dict := dadd {Thy=Thy,Name=Name} name2 (!dict);
    name2
  end

(* theorems *)
fun declare_perm_thm (thy,n) name  =
  let
    val name1 = "thm/" ^ thy ^ "/" ^ (hh_escape name)
    val name2 = squotify name1
  in
    store_name name1;
    writehh_names := dadd (thy,n) name2 (!writehh_names);
    name2
  end

(* special constants *)
fun declare_fixed dict {Thy,Name} name =
  (
  store_name name;
  dict := dadd {Thy=Thy,Name=Name} name (!dict);
  name
  )

(* temporary variables and type variables *)
fun declare_temp_list get_name dict l =
  let
    val olddict = !dict
    val oldused = !used_names
    fun fold_fun (s,sl) =
      let val (news, newused) =
        variant_name_dict (get_name s) (!used_names)
      in
        (dict := dadd s news (!dict);
         used_names := newused;
         news :: sl)
      end
    val sl = foldl fold_fun [] l
  in
    (List.rev sl, fn () => (dict := olddict; used_names := oldused))
  end

(*---------------------------------------------------------------------------
   Streams. Objects and dependencies are written in different files.
 ----------------------------------------------------------------------------*)

val oc = ref stdOut
val oc_deps = ref stdOut
fun os s = output (!oc,s)
fun oiter_aux oc sep f =
 fn [] => ()
  | [e] => f e
  | h :: t => (f h; output (oc,sep); oiter_aux oc sep f t)
fun oiter_deps sep f l = oiter_aux (!oc_deps) sep f l
fun oiter sep f l = oiter_aux (!oc) sep f l

(*---------------------------------------------------------------------------
   Printing objects (types, constants, theorems' conjuncts).
 ----------------------------------------------------------------------------*)

(* type *)
fun oty ty =
  if is_vartype ty then os (dfind ty (!tyvar_names)
                            handle _ => raise ERR "dfind" "type")
  else
    let val {Args,Thy,Tyop} = dest_thy_type ty in
    let val s = dfind {Thy=Thy,Name=Tyop} (!ty_names) in
      if null Args then os s else
        if (Thy ="min" andalso Tyop = "fun")
        then (os "("; oty (hd Args); os " > "; oty (hd (tl Args)); os ")")
        else (os ("(" ^ s ^ " "); oiter " " oty Args; os ")")
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
fun otm tm =
  if is_var tm        then os (dfind tm (!var_names)
                               handle _ => raise ERR "dfind" "var")
  else if is_const tm then
    let val {Thy, Name, Ty} = dest_thy_const tm in
    let val mgty = type_of (prim_mk_const {Thy = Thy, Name = Name}) in
    let val subst = full_match_type mgty Ty in
    let val resl = map #residue subst in
      if null resl then os (dfind {Thy=Thy,Name=Name} (!const_names))
      else (os "("; os (dfind {Thy=Thy,Name=Name} (!const_names)); os " ";
            oiter " " oty resl; os ")")
    end end end end
  else if is_eq tm       then
    (os "("; otm (lhs tm);   os " = ";  otm (rhs tm);  os ")")
  else if is_conj tm     then
    (os "("; otm (lhand tm); os " & ";  otm (rand tm); os ")")
  else if is_disj tm     then
    (os "("; otm (lhand tm); os " | ";  otm (rand tm); os ")")
  else if is_imp_only tm then
    (os "("; otm (lhand tm); os " => "; otm (rand tm); os ")")
  else if is_neg tm      then (os "(~ "; otm (rand tm); os ")")
  else if is_forall tm   then hh_binder "!" (strip_forall tm)
  else if is_exists tm   then hh_binder "?" (strip_exists tm)
  else if is_abs tm      then hh_binder "^" (strip_abs tm)
  else if is_comb tm then
    let val (v,l) = strip_comb tm in
      (os "("; otm v; app (fn x => (os " "; otm x)) l; os ")")
    end
  else raise ERR "otm" ""
and hh_binder s (l,tm) =
  let val (vl,undeclare) = declare_temp_list (fst o dest_var) var_names l in
    os ("(" ^ s ^ "[");
    oiter ", "
      (fn x => (os (dfind x (!var_names) handle _ => raise ERR "dfind" "var");
    os " : "; oty (type_of x))) l;
    os "]: "; otm tm; os ")";
    undeclare ()
  end

(* type definition *)
fun hh_tydef thy (s,arity) =
  case (thy,s) of
    ("min","bool") => ignore (declare_fixed ty_names {Thy=thy,Name=s} "$o")
  | ("min","fun")  => ignore (declare_fixed ty_names {Thy=thy,Name=s} "$fun")
  | _  =>
  let val news = declare_perm_type ty_names {Thy=thy,Name=s} in
    (
    os "tt("; os news; os ", ty, ";
    let fun tyd i = case i of
        0 => os "$t"
      | n => (os "$t > "; tyd (n - 1))
    in
      (tyd arity; os ").\n")
    end
    )
  end

fun quant_tyvarl l =
  if null l then ()
  else (os "!["; oiter ", " (fn x => (os x; os " : $t")) l; os "]: ")

(* constant definition *)
fun hh_constdef thy (s,ty) =
  let
    val fix = declare_fixed const_names {Thy=thy,Name=s}
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
  | _               => declare_perm_const const_names {Thy=thy,Name=s}
    val tv = sort less_ty (type_vars ty)
    val (newtvs, undeclare) =
      declare_temp_list nice_dest_vartype tyvar_names tv
  in
    (
    os "tt("; os news; os ", ty, ";
    case newtvs of [] => () | l => quant_tyvarl l;
    oty ty; os ").\n"; undeclare ()
    )
  end

(* theorems *)
fun othm (name,role,tm) =
  let
    fun f x = is_var x orelse is_const x
    val l1 = type_varsl (map type_of (find_terms f tm))
    val (l2,undeclare) = declare_temp_list nice_dest_vartype tyvar_names l1
  in
    (
    os "tt("; os name;
    os (", " ^ role ^ ", "); quant_tyvarl l2; otm tm; os ").\n";
    undeclare ()
    )
  end

fun othm_theorem (name,role,thm) =
  othm (name,role,concl (GEN_ALL (DISCH_ALL thm)))

(* conjecture *)
fun othm_conjecture conjecture =
  othm (conjecture_name, conjecture_name,
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
  end

fun exists_depid did = can thm_of_depid did

fun odep (name,dl) =
  let
    fun os_deps s = output (!oc_deps,s)
    fun name_did did = dfind did (!writehh_names)
  in
    os_deps (name ^ " ");
    oiter_deps " " os_deps (mapfilter name_did dl);
    os_deps "\n"
  end

(*---------------------------------------------------------------------------
   Exporting a theorem and its dependencies
 ----------------------------------------------------------------------------*)

fun export_thm ((name,thm),role) =
  let
    val d = (dep_of o tag) thm
    val did = depid_of d
    val dl = filter exists_depid (depidl_of d)
    val name' = declare_perm_thm did name
  in
    othm_theorem (name',role,thm);
    odep (name',dl)
  end

(*---------------------------------------------------------------------------
   Printing theories
 ----------------------------------------------------------------------------*)

fun hh_thy_start folder thy =
  (
  oc := openOut (folder ^ "/" ^ thy ^ ".p");
  oc_deps := openOut (folder ^ "/" ^ thy  ^ ".hd")
  )

fun hh_thy_end () =
  (
  closeOut (!oc); oc := stdOut;
  closeOut (!oc_deps); oc_deps := stdOut
  )

fun write_hh_thy folder thy =
  (
  hh_thy_start folder thy;
  let val l = dest_theory thy in
    case l of THEORY(_,t) =>
    (
    app (hh_tydef thy) (#types t);
    app (hh_constdef thy) (#consts t);
    let
      val axl = map (fn x => (x,"ax")) (DB.theorems thy)
      val defl = map (fn x => (x,"def")) (DB.axioms thy @ DB.definitions thy)
      fun compare ((_,th1),_) ((_,th2),_) =
        let val f = depnumber_of o depid_of o dep_of o Thm.tag in
          f th1 < f th2
        end
      (* val thml = filter (fn ((_,x),_) => not (is_oversized_thm x)) *)
      val thml = sort compare (axl @ defl)
    in
      app export_thm thml
    end
    )
  end;
  hh_thy_end ()
  )

fun sort_thyl thyl = case thyl of
    [] => []
  | thy :: m =>
      let val (l1,l2) = partition (fn a => mem a (ancestry thy)) m in
        (sort_thyl l1) @ [thy] @ (sort_thyl l2)
       end

fun write_thydep file thyl =
  (
  oc := openOut file;
  app (fn x => (os x; os " "; oiter " " os (parents x); os "\n")) thyl;
  closeOut (!oc); oc := stdOut
  )

fun write_hh_thyl folder thyl =
  (reset_dicts();
   app (write_hh_thy folder) (sort_thyl thyl))


fun write_conjecture file conjecture = (* TO DO: put it in a subdirectory *)
  (* if is_oversized_term conjecture
    then raise ERR "write_conjecture" "too large conjecture"
  else *)
  if type_of conjecture = bool
    then
    (
    oc := openOut file;
    othm_conjecture conjecture;
    closeOut (!oc); oc := stdOut
    )
  else raise ERR "write_conjecture" "conjecture is not a boolean"

end
