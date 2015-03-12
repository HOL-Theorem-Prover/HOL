(* ===================================================================== *)
(* FILE          : thfWriter.sml                                         *)
(* DESCRIPTION   : Print objects (constants, types and theorems) and     *)
(*                 dependencies between conjuncts of theorems for        *)
(*                 holyHammer.                                           *)                 
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)


structure thfWriter :> thfWriter =
struct


open HolKernel Abbrev boolLib TextIO Tag Dep

val ERR = mk_HOL_ERR "thfWriter"

(*---------------------------------------------------------------------------
   Dictionaries.
 ----------------------------------------------------------------------------*)

(* Shorter functions' name *)

fun dfind k m = 
  (Redblackmap.find (m,k) handle NotFound => raise ERR "dfind" "")
fun dmem k m = Lib.can (dfind k) m
fun dadd i v m = Redblackmap.insert (m,i,v)
val dempty = Redblackmap.mkDict

(* Comparisons' function *)

fun conj_compare ((did1,a1),(did2,a2)) = case depid_compare (did1,did2) of
    LESS => LESS
  | GREATER => GREATER
  | EQUAL => list_compare depchoice_compare (a1,a2)

(* Dictionaries *)

val ty_names = ref (dempty KernelSig.name_compare)
val const_names = ref (dempty KernelSig.name_compare)
val var_names = ref (dempty Term.compare)
val tyvar_names = ref (dempty Type.compare)
val conj_names = ref (dempty conj_compare) (* for theorems' conjunct *)
val used_names = ref (dempty String.compare)
(* save how a theorem split into its conjuncts *)
val depid_maxsplit = ref (dempty depid_compare)
(* read back the names returned by holyhammer *)
val readthf_names = ref (dempty String.compare)
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
  conj_names := dempty conj_compare;
  used_names := dempty String.compare;
  app reserve reserved_names;
  depid_maxsplit := dempty depid_compare;
  readthf_names := dempty String.compare
)

(*---------------------------------------------------------------------------
   Printing and reading names of objects.
 ----------------------------------------------------------------------------*)

(* Escaping *)
fun thf_escape s =
  let fun thf_escape_aux l = case l of
      []      => "" 
    | a :: m  =>          
             if Char.isAlphaNum a then String.str a ^ thf_escape_aux m
        else if Char.ord a = 95   then "__" ^ thf_escape_aux m
        else "_" ^ Int.fmt StringCvt.HEX (Char.ord a) ^ thf_escape_aux m
  in
    thf_escape_aux (String.explode s)
  end

(*---------------------------------------------------------------------------
   Save new objects in the dictionnaries.
 ----------------------------------------------------------------------------*)

(* renaming *)
fun variant_name_dict s used =
  let 
    val i = dfind s used 
    fun new_name s i =
      let val si = s ^ Int.toString i in
        if dmem si used 
        then new_name s (i + 1)
        else (si, dadd s (i + 1) (dadd si 0 used))
      end
  in 
    new_name s i 
  end
  handle NotFound => (s, dadd s 0 used)

(* constants and types *)
fun declare_perm dict {Thy,Name} =
  let val (s, new) = variant_name_dict (thf_escape Name) (!used_names) in
    (dict := dadd {Thy=Thy,Name=Name} s (!dict); used_names := new; s)
  end

(* theorems *)
fun declare_perm_thm thy (thm,name) =
  let 
    fun address_of_conj conj = address_of (depsort_of (dep_of (tag conj)))  
    fun string_of_conj (conj,name) = case depsort_of (dep_of (tag conj)) of
        DEP_NAMED _ => thf_escape thy ^ "/" ^ thf_escape (name ^ "_")
      | _           => thf_escape thy ^ "/" ^ 
                       thf_escape (name ^ "_" ^ number_address (address_of_conj conj))
    val ds = depsort_of (dep_of (tag thm)) 
    val thy = depthy_of (depid_of ds)
    val (s, new) = 
      variant_name_dict (string_of_conj (thm,name)) (!used_names) 
  in
    conj_names := dadd (depid_of ds, address_of ds) s (!conj_names); 
    readthf_names := 
      dadd s ({Thy=thy, Name=name}, address_of ds) (!readthf_names);
    used_names := new; (thm,s)
  end

fun declare_fixed dict {Thy,Name} s =
  (dict := dadd {Thy=Thy,Name=Name} s (!dict); 
   used_names := dadd s 0 (!used_names);
   s)

fun declare_temp_list get_name dict l =
  let 
    val olddict = !dict 
    val oldused = !used_names 
    fun fold_fun (s,sl) =
      let val (news, newused) = 
        variant_name_dict (thf_escape (get_name s)) (!used_names) 
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
   Streams. Objects and dependencies ware written in different files. 
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
  if is_vartype ty then os (dfind ty (!tyvar_names)) 
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
  if is_var tm        then os (dfind tm (!var_names))
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
  else if is_forall tm   then thf_binder "!" (strip_forall tm)
  else if is_exists tm   then thf_binder "?" (strip_exists tm)
  else if is_abs tm      then thf_binder "^" (strip_abs tm)
  else if is_comb tm then 
    let val (v,l) = strip_comb tm in 
      (os "("; otm v; app (fn x => (os " "; otm x)) l; os ")")
    end
  else raise ERR "otm" ""
and thf_binder s (l,tm) =
  let val (vl,undeclare) = declare_temp_list (fst o dest_var) var_names l in
    (
    os ("(" ^ s ^ "["); 
    oiter ", " 
      (fn x => (os (dfind x (!var_names)); os " : "; oty (type_of x))) l;
    os "]: "; otm tm; os ")";
    undeclare ()
    )
  end

(* type definition *)
fun thf_tydef thy (s,arity) =
  case (thy,s) of 
    ("min","bool") => ignore (declare_fixed ty_names {Thy=thy,Name=s} "$o")
  | ("min","fun")  => ignore (declare_fixed ty_names {Thy=thy,Name=s} "$fun")
  | _  =>
  let val news = declare_perm ty_names {Thy=thy,Name=s} in
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
fun thf_constdef thy (s,ty) = 
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
  | _               => declare_perm const_names {Thy=thy,Name=s}
    val tv = sort less_ty (type_vars ty)
    val (newtvs, undeclare) = declare_temp_list dest_vartype tyvar_names tv
  in
    (
    os "tt("; os news; os ", ty, ";
    case newtvs of [] => () | l => quant_tyvarl l;
    oty ty; os ").\n"; undeclare ()
    )
  end

(* theorems' conjunct *)
fun othm (name,role,tm) =
  let
    fun f x = is_var x orelse is_const x
    val l1 = type_varsl (map type_of (find_terms f tm)) 
    val (l2,undeclare) = declare_temp_list dest_vartype tyvar_names l1 
  in
    (
    os "tt("; os name;
    os (", " ^ role ^ ", "); quant_tyvarl l2; otm tm; os ").\n"; 
    undeclare ()
    ) 
  end

fun othm_theorem ((conj,name),role,thm) = 
  othm (name,role,concl (GEN_ALL (DISCH_ALL conj)))

fun othm_conjecture conjecture = 
  othm (conjecture_name, conjecture_name, 
        list_mk_forall (free_vars_lr conjecture,conjecture))
 
(*---------------------------------------------------------------------------
   Computing dependencies for each conjunct. 
 ----------------------------------------------------------------------------*)

(* Remarks:
   - Addresses are written in the reverse way.
   - Often, the maximal splitting of the original theorem is deeper than
   the splitting during dependency recording.
   - Rarely, the maximal splitting of the original theorem is less deep than 
   the splitting during dependency recording. 
   Example: SPEC ``A /\ B`` (ASSUME ``!x.x``) can be split into two conjuncts.
*)

(* Fetching the dependencies along a path in the theorem tree. *)

fun merge_path rev_address tree = case (rev_address,tree) of
    (_,DEP_LEAF dsl)                 => tree
  | ([],_)                           => merge_deptree tree
  | (DEP_LEFT :: m, DEP_NODE(t1,t2)) => merge_path m t1
  | (DEP_RIGHT :: m, DEP_NODE(t1,t2)) => merge_path m t2

fun finddepsortl (thm,conj) =
  let
    val thm_tree     = deptree_of (dep_of (tag thm))
    val conj_address = address_of (depsort_of (dep_of (tag conj)))
  in
    dest_depleaf (merge_path (rev conj_address) thm_tree)
  end

(* Maximally splitting the dependencies and naming them. *)

fun is_child_of_loop a1 a2 = case a1 of
    []      => true
  | lr :: m => if null a2 then false 
               else (lr = hd a2 andalso is_child_of_loop m (tl a2))

fun is_child_of a1 a2 = is_child_of_loop (rev a1) (rev a2)

fun closest_parent a al = (* including itself *) 
  if mem a al then a else closest_parent (tl a) al 
  handle _ => raise ERR "closest_parent" "not_found"

fun all_children a al = (* including itself *)
  let val l = List.filter (is_child_of a) al in
    if null l then raise ERR "all_children" "not_found" else l
  end

fun related a al = 
  all_children a al handle _ => [closest_parent a al] 
  
fun splitname depsort =
  let 
    exception ERASED (* theorems may be erased *)
    val depid = depid_of depsort 
    val maxsplitl = (dfind depid (!depid_maxsplit) handle _ => raise ERASED) 
    val splitl = related (address_of depsort) maxsplitl
    fun name_depsort depid x = dfind (depid,x) (!conj_names)
  in
    map (name_depsort depid) splitl
  end
  handle ERASED => []

(* Combining both previous steps. *)

fun finddepsortl_and_splitname (thm,conj) = 
  mk_set (List.concat (map splitname (finddepsortl (thm,conj))))
    
(*---------------------------------------------------------------------------
   Printing the dependencies
 ----------------------------------------------------------------------------*)

fun odep ((conj,name),role,thm) = 
  let fun os_deps s = output (!oc_deps,s) in 
    os_deps (name ^ " ");
    oiter_deps " " os_deps (finddepsortl_and_splitname (thm,conj));
    os_deps "\n"
  end

(*---------------------------------------------------------------------------
   Splitting into conjuncts.
 ----------------------------------------------------------------------------*)

(* Same as Drule.BODY_CONJUNCTS. 
   We keep it here as we rely on the precise implementation of this rule 
   to track addresses. *)
fun BODY_CONJUNCTS thm =
  if is_forall (concl thm)
    then BODY_CONJUNCTS (SPEC_ALL thm)
  else if is_conj (concl thm)
    then (BODY_CONJUNCTS(CONJUNCT1 thm) @ BODY_CONJUNCTS (CONJUNCT2 thm))
  else [thm]

fun split_thm thy ((name,thm),role) = 
  let 
    val depid = depid_of (depsort_of (dep_of (tag thm)))
    val conjl = BODY_CONJUNCTS thm
    val al = map (address_of o depsort_of o dep_of o tag) conjl
  in
    (* Remember how the theorem is split *)
    depid_maxsplit := dadd depid al (!depid_maxsplit);
    (* Remember how the conjuncts are named. *)
    map (fn x => (declare_perm_thm thy (x, name), role, thm)) conjl
  end

fun print_conjuncts thy ((name,thm),role) =
  (
  let val l = split_thm thy ((name,thm),role) in
    app othm_theorem l; 
    app odep l
  end
  )

(*---------------------------------------------------------------------------
   Printing theories.
 ----------------------------------------------------------------------------*)

fun thf_thy_start folder thy = 
  (
  oc := openOut (folder ^ "/" ^ thy ^ ".p"); 
  oc_deps := openOut (folder ^ "/" ^ thy  ^ ".hd")
  )

fun thf_thy_end () = 
  (
  closeOut (!oc); oc := stdOut;
  closeOut (!oc_deps); oc_deps := stdOut
  )

fun write_thf_thy folder thy =
  (
  thf_thy_start folder thy;
  let val l = dest_theory thy in 
    case l of THEORY(_,t) => 
    (
    app (thf_tydef thy) (#types t);
    app (thf_constdef thy) (#consts t);
    let 
      val axl = map (fn x => (x,"ax")) (DB.theorems thy)
      val defl = map (fn x => (x,"def")) (DB.axioms thy @ DB.definitions thy)
      fun compare ((_,th1),_) ((_,th2),_) =
        let val f = depnumber_of o depid_of o depsort_of o dep_of o Thm.tag in
          f th1 < f th2 
        end
      val name_thm_role_list = sort compare (axl @ defl)
    in
      app (print_conjuncts thy) name_thm_role_list
    end
    )
  end;              
  thf_thy_end ()
  )

fun sort_thyl thyl = case thyl of
    [] => []
  | thy :: m => let val (l1,l2) = partition (fn a => mem a (ancestry thy)) m in
                  (sort_thyl l1) @ [thy] @ (sort_thyl l2)
                end
     
fun write_thydep file thyl =
  (
  oc := openOut file; 
  app (fn x => (os x; os " "; oiter " " os (parents x); os "\n")) thyl;
  closeOut (!oc); oc := stdOut
  )

fun write_thf_thyl folder thyl =
  (reset_dicts(); 
   app (write_thf_thy folder) (sort_thyl thyl))

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
    val l2 = List.map rm_last_char l1 (* removing end line *) 
  in 
    (TextIO.closeIn file; l2)
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

local fun fetch_conj_helper (thm,a) = case a of
    []             => thm
  | DEP_LEFT :: m  => fetch_conj_helper (CONJUNCT1 (SPEC_ALL thm), m)
  | DEP_RIGHT :: m => fetch_conj_helper (CONJUNCT2 (SPEC_ALL thm), m)
in
  
fun fetch_conj (thm,s) = 
  GEN_ALL (fetch_conj_helper (thm, rev (read_address s)))
fun fetch_conj_internal ({Thy,Name},a) = 
  GEN_ALL (fetch_conj_helper (DB.fetch Thy Name, rev a))

end;

fun ostring_of_conjunct ({Thy,Name},a) =
  if a = [] then Thy ^ "Theory." ^ Name
  else "thfWriter.fetch_conj (" ^ Thy ^ "Theory." ^ Name ^ 
       "," ^ quote (number_address a) ^ ")"

(* Minimization *)
(* Can be turned off if it takes too much time *)
val minimize_flag = ref true

fun minimize_loop axl1 axl2 cj =
  if null axl2 then axl1 else
    let val axl = axl1 @ (tl axl2) in
      if can (time_metis (map fetch_conj_internal axl) cj) 2.0
      then minimize_loop axl1 (tl axl2) cj
      else minimize_loop (hd axl2 :: axl1) (tl axl2) cj
    end

fun minimize axl cj =
  if can (time_metis (map fetch_conj_internal axl) cj) 2.0 
  then minimize_loop [] axl cj
  else axl

(* Parsing and reconstruction *) 
fun reconstruct axl cj =
  let 
    val axl1 = filter (fn x => not (mem x reserved_names)) axl
    val axl2 = map (fn x => dfind x (!readthf_names)) axl1
    val axl3 = if !minimize_flag 
               then (print "Minimizing...\n"; minimize axl2 cj) 
               else axl2
    val s    = String.concatWith "," (map ostring_of_conjunct axl3)
    val axl4 = map fetch_conj_internal axl3
  in
    print ("val lemmas = [" ^ s ^ "]\n");
    ignore (time_metis axl4 cj 30.0 handle _ => 
              raise ERR "reconstruct" "Metis can't reconstruct the proof.")
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
