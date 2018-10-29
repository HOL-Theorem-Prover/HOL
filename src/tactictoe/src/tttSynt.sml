(* ========================================================================== *)
(* FILE          : tttSynt.sml                                                *)
(* DESCRIPTION   : Synthesis of terms for conjecturing lemmas                 *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure tttSynt :> tttSynt =
struct

open HolKernel boolLib Abbrev tttTools

val ERR = mk_HOL_ERR "tttSynt"

(* --------------------------------------------------------------------------
   Globals
   -------------------------------------------------------------------------- *)

val conjecture_limit = ref 100000
val patsub_flag = ref false
val type_errors = ref 0

(* --------------------------------------------------------------------------
   Tools
   -------------------------------------------------------------------------- *)

fun my_gen_all tm = list_mk_forall (free_vars_lr tm, tm)

fun my_gen_all_err tm = SOME (my_gen_all tm)
  handle HOL_ERR _ => (incr type_errors; NONE)

fun alpha_equal_or_error tm tm' =
  Term.compare (my_gen_all tm, my_gen_all tm') = EQUAL
  handle _ => true

fun unvalid_change tm tm' =
  alpha_equal_or_error tm tm' orelse
  (type_of tm' <> bool handle HOL_ERR _ => true)

(* --------------------------------------------------------------------------
   Debugging
   -------------------------------------------------------------------------- *)

val ttt_synt_dir = ref (tactictoe_dir ^ "/log_synt")

fun log_synt_file file s =
  append_endline (!ttt_synt_dir ^ "/" ^ file) s

fun log_synt s =
  (print_endline s; log_synt_file "log_main" s)

fun msg_synt l s =
  let val s' = int_to_string (length l) ^ " " ^ s in
    log_synt s'
  end

fun msgd_synt d s =
  let val s' = int_to_string (dlength d) ^ " " ^ s in
    log_synt s'
  end

fun time_synt s f x =
  let
    val _ = log_synt s
    val (r,t) = add_time f x
  in
    log_synt (s ^ ": " ^ Real.toString t);
    r
  end

fun writel_synt s sl = writel (!ttt_synt_dir ^ "/" ^ s) sl

(* --------------------------------------------------------------------------
   Statistics on conjecture generation.
   -------------------------------------------------------------------------- *)

fun string_of_tml tml =
  ("  " ^ String.concatWith "\n  " (map term_to_string tml) ^ "\n")

fun string_of_subst sub =
  let fun f (a,b) = "(" ^ term_to_string a ^ ", " ^ term_to_string b ^ ")" in
    "[" ^ String.concatWith ", " (map f sub) ^ "]"
  end

fun write_subdict subdict =
  let
    val _ = msgd_synt subdict "writing subdict"
    val l = dlist subdict
    fun f (sub, (cjl,score)) =
      Real.toString score ^ " " ^ int_to_string (length cjl) ^ ": " ^
      string_of_subst sub
  in
    writel_synt "substitutions" (map f l)
  end

fun write_origdict origdict =
  let
    val _ = msgd_synt origdict "writing origdict"
    val l = dlist origdict
    fun g (sub,tm) = string_of_subst sub ^ ": " ^ term_to_string tm
    fun f (cj,subtml) = String.concatWith "\n"
      (["Conjecture:", term_to_string cj] @ map g subtml)
  in
    writel_synt "origdict" (map f l)
  end

(* --------------------------------------------------------------------------
   Stateful dictionnaries
   -------------------------------------------------------------------------- *)

type psubst = (int * int) list
type tsubst = (term * term) list

(* dictionnary *)
val cdict_glob = ref (dempty Term.compare)
val icdict_glob = ref (dempty Int.compare)
val cdict_loc = ref (dempty Int.compare)
val cjinfo_glob =ref (dempty Term.compare)


fun fconst_glob c =
  dfind c (!cdict_glob) handle NotFound =>
  let val cglob = dlength (!cdict_glob) in
    cdict_glob := dadd c cglob (!cdict_glob);
    icdict_glob := dadd cglob c (!icdict_glob);
    cglob
  end

fun fconst_loc cglob =
  dfind cglob (!cdict_loc) handle NotFound =>
  let val cloc = dlength (!cdict_loc) in
    cdict_loc := dadd cglob cloc (!cdict_loc);
    cloc
  end

fun fconst c = fconst_loc (fconst_glob c)

fun init_synt () =
  (
  cdict_glob := dempty Term.compare;
  icdict_glob := dempty Int.compare;
  cjinfo_glob := dempty Term.compare;
  type_errors := 0
  )

(* --------------------------------------------------------------------------
   Conceptualization
   -------------------------------------------------------------------------- *)

val concept_threshold = ref 4
val concept_flag = ref false

fun is_varconst x = is_var x orelse is_const x

fun save_concept d tm =
  if dmem tm (!d) then () else
    let val v = mk_var ("C" ^ int_to_string (dlength (!d)), type_of tm) in
      d := dadd tm v (!d)
    end

fun concept_selection tml =
  let
    fun f x = find_terms (not o is_varconst) x
    val l0 = List.concat (map f tml)
    val freq = count_dict (dempty Term.compare) l0
    val l1 = dlist freq
    fun above_threshold x = snd x >= !concept_threshold
    val l2 = filter above_threshold l1
    val l3 = dict_sort compare_imax l2
    fun w (x,n) = int_to_string n ^ " :" ^ term_to_string x
    val _  = writel_synt "concepts" (map w l3)
    val _  = msg_synt l2 "selected concepts"
    val d = ref (dempty Term.compare)
  in
    app (save_concept d) (map fst l2);
    (!d)
  end

fun conceptualize_tm ceptdict tm =
  let
    fun is_cept x = dmem x ceptdict
    val redexl0 = find_terms is_cept tm
    fun cmp (tm1,tm2) = Int.compare (term_size tm2, term_size tm1)
    val redexl1 = dict_sort cmp redexl0
    fun f i tm = {redex = tm, residue = dfind tm ceptdict}
    val sub = mapi f redexl1
    val newtm = Term.subst sub tm
  in
    if term_eq newtm tm then [tm] else [tm,newtm]
  end

fun read_cept iceptdict c =
  let val tm = dfind c (!icdict_glob) in
    dfind tm iceptdict handle NotFound => tm
  end

fun read_subst iceptdict sub =
  let fun f (a,b) = (read_cept iceptdict a, read_cept iceptdict b) in
    map f sub
  end

(* --------------------------------------------------------------------------
   Patterns
   -------------------------------------------------------------------------- *)

datatype pattern =
    Pconst of int
  | Pcomb  of pattern * pattern
  | Plamb  of pattern * pattern

fun pattern_tm tm =
  case dest_term tm of
    VAR _   => Pconst (fconst tm)
  | CONST _ => Pconst (fconst tm)
  | COMB(Rator,Rand) => Pcomb (pattern_tm Rator, pattern_tm Rand)
  | LAMB(Var,Bod)    => Plamb (pattern_tm Var, pattern_tm Bod)

fun patternify_one tm =
  let
    val _ = cdict_loc := dempty Int.compare
    fun cmp (a,b) = Int.compare (snd a, snd b)
    val p = pattern_tm tm
    val l1 = dlist (!cdict_loc)
    val l2 = dict_sort cmp l1
  in
    (p, map fst l2)
  end

fun pattern_compare (p1,p2) = case (p1,p2) of
    (Pconst i1,Pconst i2) => Int.compare (i1,i2)
  | (Pconst _,_) => LESS
  | (_,Pconst _) => GREATER
  | (Pcomb(a1,b1),Pcomb(a2,b2)) =>
    cpl_compare pattern_compare pattern_compare ((a1,b1),(a2,b2))
  | (Pcomb _,_) => LESS
  | (_,Pcomb _) => GREATER
  | (Plamb(a1,b1),Plamb(a2,b2)) =>
    cpl_compare pattern_compare pattern_compare ((a1,b1),(a2,b2))

fun string_of_pattern p = case p of
    Pconst i => int_to_string i
  | Pcomb (p1,p2) =>
    "(" ^ String.concatWith " " ("A" :: map string_of_pattern [p1,p2]) ^ ")"
  | Plamb (p1,p2) =>
    "(" ^ String.concatWith " " ("L" :: map string_of_pattern [p1,p2]) ^ ")"

fun write_patceptdict ntot patceptdict =
  let
    val _ = log_synt "writing patceptdict"
    val l0 = dlist patceptdict
    val l1 = filter (fn (a,b) => length b > 1) l0
    val l2 = map (fn (a,b) => (a, length b)) l1
    val r2 = int_div (sum_int (map snd l2)) ntot
    val l3 = dict_sort compare_imax l2
    fun w (p,n) = int_to_string n ^ ": " ^ string_of_pattern p
    val _ = msg_synt l3 "patterns appearing at least twice"
  in
    writel_synt "patterns" (map w l3)
  end

fun write_ceptpatdict iceptdict ceptpatdict =
  let
    val _  = log_synt "writing ceptpatdict"
    val l0 = dlist ceptpatdict
    val l1 = filter (fn (a,b) => length b > 1) l0
    val l2 = map (fn (a,b) => (a, length b)) l1
    val l3 = dict_sort compare_imax l2
    fun w (cl,n) =
      int_to_string n ^ ": " ^
      String.concatWith "\n"
        (map (term_to_string o read_cept iceptdict) cl)
    val _ = msg_synt l3 "concept lists appearing at least twice"
  in
    writel_synt "concept_lists" (map w l3)
  end

fun patternify ntot ceptdict iceptdict tml =
  let
    val patceptdict = ref (dempty pattern_compare)
    val ceptpatdict = ref (dempty (list_compare Int.compare))
    val thmpatdict = ref (dempty Term.compare)
    val tml1 = mk_fast_set Term.compare tml
    fun f tm =
      let
        val (p,cl) = patternify_one tm
        val cll = dfind p (!patceptdict) handle NotFound => []
        val pl  = dfind cl (!ceptpatdict) handle NotFound => []
      in
        patceptdict := dadd p (cl :: cll) (!patceptdict);
        ceptpatdict := dadd cl (p :: pl) (!ceptpatdict);
        (p,cl)
      end
    fun g tm =
      let
        val variants =
          if !concept_flag then conceptualize_tm ceptdict tm else [tm]
        val patl = map f variants
      in
        thmpatdict := dadd tm patl (!thmpatdict)
      end
    val _ = app g tml1
    val _ = msgd_synt (!patceptdict) "patterns"
    val _ = msgd_synt (!ceptpatdict) "concept lists"
    val _ = write_patceptdict ntot (!patceptdict)
    val _ = write_ceptpatdict iceptdict (!ceptpatdict)
  in
    (!patceptdict, !ceptpatdict, !thmpatdict)
  end

fun term_of_pat idict (p,cl) = case p of
    Pconst i => read_cept idict (List.nth (cl,i))
  | Pcomb (p1,p2) =>
    mk_comb (term_of_pat idict (p1,cl), term_of_pat idict (p2,cl))
  | Plamb (p1,p2) =>
    mk_abs (term_of_pat idict (p1,cl), term_of_pat idict (p2,cl))

(* --------------------------------------------------------------------------
   Concept substitutions.
   -------------------------------------------------------------------------- *)

fun compare_kimin (a,b) = Int.compare (fst a, fst b)

fun norm_sub l =
  let val l1 = filter (fn (x,y) => x <> y) l in
    dict_sort compare_kimin l1
  end

fun pair_sub cll =
  let
    val cll' = mk_fast_set (list_compare Int.compare) cll
    val cpl  = cartesian_product cll' cll'
    val cpl' = filter (fn (x,y) => x <> y) cpl
  in
    map combine cpl'
  end

fun create_sub iceptdict patceptdict =
  let
    fun f (p,cll) = pair_sub cll
    val l1  = List.concat (map f (dlist patceptdict))
    val l2  = map norm_sub l1
    val cmp = list_compare (cpl_compare Int.compare Int.compare)
    val dfreq = count_dict (dempty cmp) l2
    val _   = msgd_synt dfreq "concept substitutions"
    val l3  = dict_sort compare_imax (dlist dfreq)
  in
    (map (read_subst iceptdict)) (map fst l3)
  end

fun unsafe_sub sub tm =
  let val redreso = List.find (fn (red,res) => red = tm) sub in
    if isSome redreso then snd (valOf (redreso)) else
      (
      case dest_term tm of
        VAR(Name,Ty)       => tm
      | CONST{Name,Thy,Ty} => tm
      | COMB(Rator,Rand)   =>
        mk_comb (unsafe_sub sub Rator, unsafe_sub sub Rand)
      | LAMB(Var,Bod)      =>
        mk_abs (unsafe_sub sub Var, unsafe_sub sub Bod)
      )
  end

fun apply_sub sub tm =
  let val tm' = unsafe_sub sub tm in
    if unvalid_change tm tm' then NONE else SOME (my_gen_all tm')
  end
  handle HOL_ERR _ => (incr type_errors; NONE)

(* --------------------------------------------------------------------------
   Pattern substitutions
   -------------------------------------------------------------------------- *)

fun pair_patsub pl =
  let
    val l1 = mk_fast_set pattern_compare pl
    val cpl = cartesian_product l1 l1
    val cpl' = filter (fn (x,y) => x <> y) cpl
  in
    cpl'
  end

fun create_patsub ceptpatdict =
  let
    fun f (cl,pl) = pair_patsub pl
    val cpl       = List.concat (map f (dlist ceptpatdict))
    val cmp       = cpl_compare pattern_compare pattern_compare
    val dfreq     = count_dict (dempty cmp) cpl
    val _         = msgd_synt dfreq "pattern substitutions"
  in
    map fst (dict_sort compare_imax (dlist dfreq))
  end

fun apply_patsub thmpatdict iceptdict (p1,p2) tm =
  let
    val patl = dfind tm thmpatdict
    fun same_pat x (p,cl) = pattern_compare (p,x) = EQUAL
  in
    case List.find (same_pat p1) patl of
      NONE => NONE
    | SOME (p,cl) =>
      (
      let val tm' = term_of_pat iceptdict (p2,cl) in
        if unvalid_change tm tm' then NONE else SOME (my_gen_all tm')
      end
      handle HOL_ERR _ => (incr type_errors; NONE)
      )
  end

(* --------------------------------------------------------------------------
   Conjecturing
   -------------------------------------------------------------------------- *)


fun update_genthmdict gencjdict genthmdict x =
  if dmem x (!genthmdict) then () else
  genthmdict := dadd x (dlength (!gencjdict), dlength (!genthmdict))
  (!genthmdict)

fun update_gencjdict gencjdict x =
  if dlength (!gencjdict) >= (!conjecture_limit) orelse dmem x (!gencjdict)
  then ()
  else gencjdict := dadd x (dlength (!gencjdict)) (!gencjdict)

fun update_gendict covdict genthmdict gencjdict x =
  if dmem x covdict
  then update_genthmdict gencjdict genthmdict x
  else update_gencjdict gencjdict x

fun conjecture_sub covdict tml subl =
  let
    val gencjdict = ref (dempty Term.compare)
    val genthmdict = ref (dempty Term.compare)
    val dsub = dnew Int.compare (number_list 0 subl)
    val tmnl = map (fn x => (x,0)) tml
    fun try_nsub n (tm,nsub) =
      if not (dmem nsub dsub) orelse n <= 0 then (tm,nsub) else
      (
      case apply_sub (dfind nsub dsub) tm of
        NONE => try_nsub (n - 1) (tm, nsub + 1)
      | SOME tm' =>
        (
        update_gendict covdict genthmdict gencjdict tm';
        (tm, nsub + 1)
        )
      )
    val mem = ref (~1)
    fun loop tmnl =
       if dlength (!gencjdict) >= (!conjecture_limit) orelse
          !mem >= dlength (!gencjdict)
       then () else
         let
           val _ = mem := dlength (!gencjdict)
           val _ = print_endline (int_to_string (!mem) ^ " conjectures")
           val newtmnl = map (try_nsub 100) tmnl
         in
           loop newtmnl
         end
  in
    loop tmnl;
    (!gencjdict,!genthmdict)
  end

fun conjecture_patsub thmpatdict iceptdict covdict tml patsubl =
  let
    val gencjdict = ref (dempty Term.compare)
    val genthmdict = ref (dempty Term.compare)
    val dsub = dnew Int.compare (number_list 0 patsubl)
    val tmnl = map (fn x => (x,0)) tml
    fun try_nsub n (tm,nsub) =
      if not (dmem nsub dsub) orelse n <= 0 then (tm,nsub) else
      (
      case apply_patsub thmpatdict iceptdict (dfind nsub dsub) tm of
        NONE => try_nsub (n - 1) (tm, nsub + 1)
      | SOME tm' =>
        (
        update_gendict covdict genthmdict gencjdict tm';
        (tm, nsub + 1)
        )
      )
    val mem = ref (~1)
    fun loop tmnl =
       if dlength (!gencjdict) >= (!conjecture_limit) orelse
          !mem >= dlength (!gencjdict)
       then () else
         let
           val _ = mem := dlength (!gencjdict)
           val _ = print_endline (int_to_string (!mem) ^ " conjectures")
           val newtmnl = map (try_nsub 100) tmnl
         in
           loop newtmnl
         end
  in
    loop tmnl;
    (!gencjdict,!genthmdict)
  end

fun gnuplotcmd filein fileout =
  let
    val plotcmd = "\"" ^ String.concatWith "; " [
      "set term postscript",
      "set output " ^ "'" ^ fileout ^ "'",
      "plot " ^ "'" ^ filein ^ "'"]
      ^ "\""
    val cmd = "gnuplot -p -e " ^ plotcmd ^ " > " ^ fileout
  in
    cmd_in_dir tactictoe_dir cmd
  end

fun write_graph ntot genthmdict =
  let
    val _    = log_synt "writing graph"
    val rcov = int_div (dlength genthmdict) ntot
    val _    = log_synt (Real.toString rcov ^ " conjecture coverage")
    val l0 = map snd (dlist genthmdict)
    val d = ref (dempty Int.compare)
    fun update_dict (a,b) =
      let val oldb = dfind a (!d) handle NotFound => 0 in
        if b > oldb then d := dadd a b (!d) else ()
      end
    val l1 = (app update_dict l0; dlist (!d))
    fun w (a,b) = int_to_string a ^ " " ^ (Real.toString (int_div b ntot))
    val header  = "# miss match"
    val _       = writel_synt "coverage_data" (header :: map w l1)
    val filein  = (!ttt_synt_dir) ^ "/coverage_data"
    val fileout = (!ttt_synt_dir) ^ "/coverage_graph.ps"
  in
    gnuplotcmd filein fileout
  end

fun conjecture tml =
  let
    val _     = init_synt ()
    val tml0 = mk_fast_set Term.compare tml
    val tml1 = map (snd o strip_forall o rename_bvarl (fn _ => "")) tml0
    val tml2 = mk_fast_set Term.compare tml1
    val tml3 = map (fn x => (my_gen_all x, 0)) tml2
    val _    = msg_synt tml3 "terms"
    val covdict = dnew Term.compare tml3
    val ntot = dlength covdict
    val ceptdict = concept_selection tml2
    val iceptdict = inv_dict Term.compare ceptdict
    val (patceptdict, ceptpatdict, thmpatdict) = time_synt "patternify"
       patternify ntot ceptdict iceptdict tml2
    val _ = msgd_synt (!cdict_glob) "constants or variables"

    (* conjecture generation from substitutions *)
    val (gencjdict,genthmdict) =
      if !patsub_flag
      then
        let val patsubl = create_patsub ceptpatdict in
          time_synt "conjecture_patsub"
          (conjecture_patsub thmpatdict iceptdict covdict tml2) patsubl
        end
      else
        let val subl = create_sub iceptdict patceptdict in
          time_synt "conjecture_sub"
          (conjecture_sub covdict tml2) subl
        end
    val _ = write_graph ntot genthmdict
    val _ = log_synt (int_to_string (!type_errors) ^ " type errors")
    val _     = msgd_synt gencjdict "generated conjectures"
    val igencjdict = inv_dict Int.compare gencjdict
  in
    map snd (dlist igencjdict)
  end

end (* struct *)
