(* ===================================================================== *)
(* FILE          : hhWriter.sml                                         *)
(* DESCRIPTION   : Print objects (constants, types and theorems) and     *)
(*                 dependencies between conjuncts of theorems for        *)
(*                 holyHammer.                                           *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)


structure hhWriter :> hhWriter =
struct


open HolKernel Abbrev boolLib TextIO Tag hhDep Dep

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

val writehh_names = ref (dempty depid_compare) (* symmetric dictionaries *)
val readhh_names = ref (dempty String.compare)

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
  writehh_names := dempty depid_compare;
  readhh_names := dempty String.compare
)

(*---------------------------------------------------------------------------
   Save new objects in the dictionnaries.
 ----------------------------------------------------------------------------*)
(* escaping *)
fun is_alphanumeric s = 
 let val l = String.explode s in
   all (fn x => Char.isAlphaNum x orelse x = #"_") l 
 end

fun escape_slash s =
  let 
    val l1 = String.explode s
    fun image x = 
      case x of
        #"#" => String.explode "#hash#"
      | #"/" => String.explode "#slash#"
      | _    => [x]
    val l2 = map image l1
  in
    String.implode (List.concat l2)
  end

fun escape_prime s =
  let 
    val l1 = String.explode s
    val l2 = map (fn x => if x = #"'" then [#"\\",#"'"] else [x]) l1 
  in
    String.implode (List.concat l2)
  end

fun tptp_escape name = 
  if is_alphanumeric name
  then name 
  else "'" ^ escape_prime name ^ "'"

(* use a similar escaping than the holyhammer fof writer *)
fun fof_escape name =
  if is_alphanumeric name andalso Char.isLower (hd (String.explode name))
  then name
  else "'" ^ escape_prime name ^ "'"

val reserved_names_escaped = map fof_escape reserved_names

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
        else (tptp_escape si, dadd s (i + 1) (dadd si 0 used))
      end
  in
    new_name s i
  end
  handle NotFound => (tptp_escape s, dadd s 0 used)

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
    val name1 = "type/" ^ Thy ^ "/" ^ (escape_slash Name) 
    val name2 = tptp_escape name1
  in
    store_name name1;
    dict := dadd {Thy=Thy,Name=Name} name2 (!dict); 
    name2
  end

(* constant *)
fun declare_perm_const dict {Thy,Name} =
  let 
    val name1 = "const/" ^ Thy ^ "/" ^ (escape_slash Name) 
    val name2 = tptp_escape name1
  in
    store_name name1;
    dict := dadd {Thy=Thy,Name=Name} name2 (!dict); 
    name2
  end

(* theorems *)
fun declare_perm_thm (thy,n) name  =
  let
    val name1 = "thm/" ^ thy ^ "/" ^ (escape_slash name)
    val name2 = tptp_escape name1
  in
    store_name name1;
    writehh_names := dadd (thy,n) name2 (!writehh_names);
    readhh_names  := dadd name2 (thy,n) (!readhh_names);
    name2
  end

fun declare_fixed dict {Thy,Name} name =
  (
  store_name name;
  dict := dadd {Thy=Thy,Name=Name} name (!dict);
  name
  )

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
   Printing objects (types, constants, theorems' conjuncts) and dependencies.
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

val less_ty = fn a => (fn b => Type.compare (a,b) = LESS)
fun less_red a b = less_ty (#redex a) (#redex b)

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


(* dependencies *)
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
   Exporting theorem
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
   Printing theories.
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

fun write_conjecture file conjecture =
  if type_of conjecture = bool
  then
    (
    oc := openOut file;
    othm_conjecture conjecture;
    closeOut (!oc); oc := stdOut
    )
  else raise ERR "write_conjecture" "conjecture is not a boolean"


(*---------------------------------------------------------------------------
   Reading a file.
 ----------------------------------------------------------------------------*)

fun readl path =
  let
    val file = TextIO.openIn path
    fun loop file = case TextIO.inputLine file of
        SOME line => line :: loop file
      | NONE => []
    val l1 = loop file
    fun rm_last_char s = String.substring (s,0,String.size s - 1)
    fun is_empty s = s = ""
    val l2 = map rm_last_char l1 (* removing end line *)
    val l3 = filter (not o is_empty) l2 
  in
    (TextIO.closeIn file; l3)
  end

fun get_status path = hd (readl path) handle _ => "Unknown"

(*---------------------------------------------------------------------------
   Proving the conjecture.
 ----------------------------------------------------------------------------*)

(* Tools *)
fun time_metis thml conjecture time =
  let
    val oldlimit = !mlibMetis.limit
    val oldtracelevel = !mlibUseful.trace_level
    val thm =
      (
      metisTools.limit := {time = SOME time, infs = NONE};
      mlibUseful.trace_level := 0;
      metisTools.METIS_PROVE thml conjecture
      )
  in
    (metisTools.limit := oldlimit; mlibUseful.trace_level := oldtracelevel; thm)
  end

(* Minimization *)
(* Can be turned off if it takes too much time *)
val minimize_flag = ref true

fun minimize_loop l1 l2 cj =
  if null l2 then l1 else
    if can (time_metis (map snd (l1 @ tl l2)) cj) 2.0
    then minimize_loop l1 (tl l2) cj
    else minimize_loop (hd l2 :: l1) (tl l2) cj

fun minimize l cj =
  if can (time_metis (map snd l) cj) 2.0
  then (print "Minimizing...\n"; minimize_loop [] l cj)
  else l

(* Parsing and reconstruction *)
fun string_of_lemma (name,thm) =
  let val (thy,_) = depid_of (dep_of (tag thm)) in
    thy ^ "Theory." ^ name
  end

fun reconstruct axl cj =
  let
    (* reserved theorems are not interesting to Metis *)
    val axl1 = filter (fn x => not (mem x reserved_names_escaped)) axl
    val didl = map (fn x => dfind x (!readhh_names)) axl1
    val l1   = map thm_of_depid didl
    val l2   = if !minimize_flag then minimize l1 cj else l1
  in
    print 
      ("val lemmas = [" ^ 
       String.concatWith ","  (map string_of_lemma l2) ^ "]\n");
    ignore (time_metis (map snd l2) cj 30.0)
      handle _ => raise ERR "reconstruct" "Metis timed out."
  end

fun replay_atpfile (atp_status,atp_out) conjecture =
  let val s = get_status atp_status in
    if s = "Theorem"
    then reconstruct (readl atp_out) conjecture
    else raise ERR "replay_atpfile" ("Status: " ^ s)
  end

fun replay_atpfilel atpfilel conjecture =
  let
    fun process (atp_status,atp_out) =
      let val s = get_status atp_status in
        if s = "Theorem" then (s, readl atp_out) else (s, [])
      end
    val processedl = map process atpfilel
    val newl = filter (fn (x,_) => x = "Theorem") processedl
  in
    if null newl
    then
      let
        val status_list = map fst processedl
        val s = if all (fn x => x = "Unknown") status_list
                then "Unknown"
                else hd (filter (fn x => x <> "Unknown") status_list)
      in
        raise ERR "replay_atpfilel" ("Status: " ^ s)
      end
    else
      let
        fun compare_list l1 l2 = length l1 > length l2
        val axl = hd (sort compare_list (map snd newl))
      in
        reconstruct axl conjecture
      end
  end

end
