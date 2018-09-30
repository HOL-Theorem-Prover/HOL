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

(* --------------------------------------------------------------------------
   Brute force conjecturing
   -------------------------------------------------------------------------- 
*)

fun all_split (a,b) =
  if b < 1 then [] else (a,b) :: all_split (a+1,b-1)

fun is_closed tm = type_of tm = bool andalso null (free_vars tm) 

fun all_bvl tm = 
  let val tml = find_terms is_abs tm in  
    mk_set (map (fst o dest_abs) tml) (* few variables so mk_set *)
  end 

fun inter_bvl (t1,t2) =
  let val (vl1,vl2) = (all_bvl t1, all_bvl t2) in
    exists (fn x => mem x vl2) vl1   
  end 

fun smart_mk_comb (t1,t2) =
  if is_closed t2 orelse inter_bvl (t1,t2) 
  then NONE 
  else SOME (mk_comb (t1,t2))

fun is_applicable (ty1,ty2) =
  let fun apply ty1 ty2 =
    mk_comb (mk_var ("x",ty1), mk_var ("y",ty2))
  in
    can (apply ty1) ty2
  end

fun all_mk_comb d1 d2 (ty1,ty2) =
  let 
    val tml1 = dfind ty1 d1
    val tml2 = dfind ty2 d2
    val l = cartesian_product tml1 tml2
  in
    List.mapPartial smart_mk_comb l  
  end

fun all_abs_one f tm = map (fn x => f (x,tm)) (free_vars_lr tm)

fun all_abs f tml =
  List.concat (map (all_abs_one f) tml)


fun all_forall tml = all_abs mk_forall tml
fun all_exists tml = all_abs mk_exists tml
fun all_quant tml = all_forall tml @ all_exists tml

val (gen_size_cache :  (int, (hol_type, term list) Redblackmap.dict) Redblackmap.dict ref) = ref (tttTools.dempty Int.compare)


fun init_gen_size tml =
  let
    val _    = gen_size_cache := dempty Int.compare
    val tml' = map (fn x => (type_of x, x)) tml
    val r    = dregroup Type.compare tml'
  in
    gen_size_cache := dadd 1 r (!gen_size_cache)
  end

fun gen_size filterf n =
  (if n <= 0 then raise ERR "gen_size" "" else dfind n (!gen_size_cache)) 
  handle NotFound =>
  let 
    val l = all_split (1,n-1)   
    fun all_comb (n1,n2) = 
      let
        val d1 = gen_size filterf n1
        val d2 = gen_size filterf n2
        val tytyl  = cartesian_product (dkeys d1) (dkeys d2)
        val tytyl' = filter is_applicable tytyl
      in
        List.concat (map (all_mk_comb d1 d2) tytyl')
      end
    val combl  = List.concat (map all_comb l)
    val d      = gen_size filterf (n - 1)
    val quantl = all_quant (dfind bool d handle NotFound => [])
    val tml0   = quantl @ combl
    val tml1   = filterf tml0
    val tml2   = map (fn x => (type_of x, x)) tml1
    val r      = dregroup Type.compare tml2
  in
    gen_size_cache := dadd n r (!gen_size_cache);
    log_synt ("gen_size " ^ int_to_string n ^ ": " ^ 
              int_to_string (length tml0));
    r
  end

val mk_term_set = mk_fast_set Term.compare

fun cjenum inddepth indthm depth maxperdepth filterf vcset = 
  let
    val newfilterf = filterf maxperdepth
    val _ = init_gen_size vcset
    val _ = gen_size newfilterf depth
    val dictl0 = List.tabulate (depth, fn x => gen_size newfilterf (x+1))
    val dictl1 = List.tabulate (inddepth, fn x => gen_size newfilterf (x+1))
    fun closify x = list_mk_forall (free_vars_lr x, x)
    fun extract_thml dict =
      if dmem bool dict 
      then mk_term_set (mapfilter closify (dfind bool dict))
      else []
    fun extract_ind dict =
      if dmem bool dict then 
        let 
          val absl = all_abs mk_abs (dfind bool dict) 
          fun f x = (closify o rand o only_concl o REDEPTH_CONV BETA_CONV o
            only_concl o (SPEC x)) indthm 
        in 
          mk_term_set (mapfilter f absl)
        end
      else []
    val cjl   = List.concat (map extract_thml dictl0)
    val indl  = List.concat (map extract_ind dictl1)
    val _     = msg_synt cjl "conjectures"
    val _     = msg_synt indl "induction axioms"
  in
    (shuffle cjl, shuffle indl)
  end




end (* struct *)
















