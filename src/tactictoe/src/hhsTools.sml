(* ========================================================================== *)
(* FILE          : hhsTools.sml                                               *)
(* DESCRIPTION   : Library of useful functions for TacticToe                  *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsTools :> hhsTools =
struct

open HolKernel boolLib Abbrev

val ERR = mk_HOL_ERR "hhsTools"

type lbl_t = (string * real * goal * goal list)
type fea_t = int list
type feav_t = (lbl_t * fea_t)

(* --------------------------------------------------------------------------
   Global parameters
   -------------------------------------------------------------------------- *)

val hhs_tactic_time = ref 0.0
val hhs_search_time = ref (Time.fromReal 0.0)

(* --------------------------------------------------------------------------
   Directories
   -------------------------------------------------------------------------- *)

val tactictoe_dir   = HOLDIR ^ "/src/tactictoe"
val hhs_feature_dir = tactictoe_dir ^ "/features"
val hhs_code_dir    = tactictoe_dir ^ "/code"
val hhs_search_dir  = tactictoe_dir ^ "/search_log"
val hhs_predict_dir = tactictoe_dir ^ "/predict"
val hhs_record_dir  = tactictoe_dir ^ "/record_log"
val hhs_open_dir  = tactictoe_dir ^ "/open"
val hhs_succrate_dir = tactictoe_dir ^ "/succrate"

fun mkDir_err dir = OS.FileSys.mkDir dir handle _ => ()

(* --------------------------------------------------------------------------
    Dictionaries shortcuts
   -------------------------------------------------------------------------- *)

fun dfind k m  = Redblackmap.find (m,k) 
fun drem k m   = fst (Redblackmap.remove (m,k))
fun dmem k m   = Lib.can (dfind k) m
fun dadd k v m = Redblackmap.insert (m,k,v)
fun daddl kvl m = Redblackmap.insertList (m,kvl)
val dempty     = Redblackmap.mkDict
val dnew       = Redblackmap.fromList
val dlist      = Redblackmap.listItems
val dlength    = Redblackmap.numItems
val dapp       = Redblackmap.app
fun dkeys d    = map fst (dlist d)

(* --------------------------------------------------------------------------
   References
   -------------------------------------------------------------------------- *)

fun incr x = x := (!x) + 1

(* --------------------------------------------------------------------------
   Reserved tokens
   -------------------------------------------------------------------------- *)

val reserved_dict =
  dnew String.compare
  (map (fn x => (x,()))
  ["op", "if", "then", "else", "val", "fun",
   "structure", "signature", "struct", "sig", "open",
   "infix", "infixl", "infixr", "andalso", "orelse",
   "and", "datatype", "type", "where", ":", ";" , ":>",
   "let", "in", "end", "while", "do",
   "local","=>","case","of","_","|","fn","handle","raise","#",
   "[","(",",",")","]","{","}","..."])

fun is_string s = String.sub (s,0) = #"\"" handle _ => false
fun is_number s = Char.isDigit (String.sub (s,0)) handle _ => false
fun is_chardef s = String.substring (s,0,2) = "#\"" handle _ => false

fun is_reserved s =
  dmem s reserved_dict orelse
  is_number s orelse is_string s orelse is_chardef s

(* --------------------------------------------------------------------------
   List
   -------------------------------------------------------------------------- *)

fun first_n n l =
  if n <= 0 orelse null l
  then []
  else hd l :: first_n (n - 1) (tl l)

fun number_list start l = case l of 
    []      => []
  | a :: m  => (start,a) :: number_list (start + 1) m

fun mk_fast_set compare l = 
  let 
    val empty_dict = dempty compare
    fun f (k,dict) = dadd k () dict
  in
    map fst (Redblackmap.listItems (foldl f empty_dict l))
  end

(* preserve the order of elements and take the first seen element as representant *)
fun mk_sameorder_set_aux memdict rl l =
  case l of
    [] => rev rl
  | a :: m => if dmem a memdict 
              then mk_sameorder_set_aux memdict rl m
              else mk_sameorder_set_aux (dadd a () memdict) (a :: rl) m
  
fun mk_sameorder_set compare l = mk_sameorder_set_aux (dempty compare) [] l

(* Sort elements and preserve the order of equal elements *)
fun dict_sort compare l =
  let
    val newl = number_list 0 l
    fun newcompare ((n,x),(m,y)) = 
      case compare (x,y) of
        EQUAL => Int.compare (n,m)
      | LESS => LESS
      | GREATER => GREATER
  in
    map snd (mk_fast_set newcompare newl)
  end

fun mk_string_set l = mk_fast_set String.compare l

fun count_dict startdict l = 
  let
    fun f (k,dict) = 
      let val old_n = dfind k dict handle _ => 0 in
        dadd k (old_n + 1) dict
      end
  in
    foldl f startdict l
  end

fun fold_left f l orig = case l of
    [] => orig
  | a :: m => let val new_orig = f a orig in fold_left f m new_orig end

fun list_diff l1 l2 = filter (fn x => not (mem x l2)) l1  

fun topo_sort graph =
  let val (topl,downl) = List.partition (fn (x,xl) => null xl) graph in
    case (topl,downl) of
    ([],[]) => []
  | ([],_)  => raise ERR "topo_sort" "loop or missing nodes"
  | _       =>
    let 
      val topl' = List.map fst topl 
      val graph' = List.map (fn (x,xl) => (x,list_diff xl topl')) downl
    in
      topl' @ topo_sort graph'
    end
  end




(* ---------------------------------------------------------------------------
   Reals
   -------------------------------------------------------------------------- *)

fun sum_real l = case l of [] => 0.0 | a :: m => a + sum_real m
fun sum_int l = case l of [] => 0 | a :: m => a + sum_int m

fun average_real l = sum_real l / Real.fromInt (length l)

(* --------------------------------------------------------------------------
   Goal
   -------------------------------------------------------------------------- *)

fun goal_compare ((asm1,w1), (asm2,w2)) =
  list_compare Term.compare (w1 :: asm1, w2 :: asm2)

fun string_of_goal (asm,w) =
  let 
    val mem = !show_types
    val _   = show_types := false
    val s   = 
      (if asm = [] 
         then "[]" 
         else "[``" ^ String.concatWith "``,``" (map term_to_string asm) ^ 
              "``]")
    val s1 = "(" ^ s ^ "," ^ "``" ^ (term_to_string w) ^ "``)"
  in
    show_types := mem;
    s1
  end

(* --------------------------------------------------------------------------
   Feature vectors
   -------------------------------------------------------------------------- *)

fun cpl_compare cmp1 cmp2 ((a1,a2),(b1,b2)) =
  let val r = cmp1 (a1,b1) in
    if r = EQUAL then cmp2 (a2,b2) else r
  end

fun lbl_compare ((stac1,_,g1,_),(stac2,_,g2,_)) =
  cpl_compare String.compare goal_compare ((stac1,g1),(stac2,g2))

fun feav_compare ((lbl1,_),(lbl2,_)) = lbl_compare (lbl1,lbl2)

(* --------------------------------------------------------------------------
   I/O
   -------------------------------------------------------------------------- *)

fun bare_readl path =
  let
    val file = TextIO.openIn path
    fun loop file = case TextIO.inputLine file of
        SOME line => line :: loop file
      | NONE => []
    val l = loop file
  in
    (TextIO.closeIn file; l)
  end

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

fun readl_empty path =
  let
    val file = TextIO.openIn path
    fun loop file = case TextIO.inputLine file of
        SOME line => line :: loop file
      | NONE => []
    val l1 = loop file
    fun rm_last_char s = String.substring (s,0,String.size s - 1)
    val l2 = map rm_last_char l1 (* removing end line *)
  in
    (TextIO.closeIn file; l2)
  end


fun write_file file s = 
  let val oc = TextIO.openOut file in
    TextIO.output (oc,s); TextIO.closeOut oc
  end

fun erase_file file = write_file file "" handle _ => ()

fun writel file sl =
  let val oc = TextIO.openOut file in
    app (fn s => TextIO.output (oc, s ^ "\n")) sl;
    TextIO.closeOut oc
  end

fun append_file file s =
  let val oc = TextIO.openAppend file in
    TextIO.output (oc,s); TextIO.closeOut oc
  end
  
fun append_endline file s = append_file file (s ^ "\n")

(* --------------------------------------------------------------------------
   Profiling
   -------------------------------------------------------------------------- *)

fun add_time f x =
  let
    val rt = Timer.startRealTimer ()
    val r = f x
    val time = Timer.checkRealTimer rt
  in
    (r, Time.toReal time)
  end

fun total_time total f x =
  let val (r,t) = add_time f x in (total := (!total) + t; r) end
  
fun print_time s r = print (s ^ ": " ^ Real.toString r ^ "\n")

fun print_endline s = print (s ^ "\n")

(* --------------------------------------------------------------------------
   Debugging and exporting feature vectors
   -------------------------------------------------------------------------- *)

fun debug s = 
  append_endline (hhs_search_dir ^ "/debug/" ^ current_theory ()) s

fun debug_t s f x = 
  let 
    val _ = debug s
    val (r,t) = add_time f x
    val _ = debug ("  " ^ Real.toString t)
  in
    r
  end

fun debug_search s =
  append_endline (hhs_search_dir ^ "/search/" ^ current_theory ()) s

fun debug_proof s =
  append_endline (hhs_search_dir ^ "/proof/" ^ current_theory ()) s

fun debug_parse s =
  let val file = hhs_record_dir ^ "/" ^ current_theory () ^ "/parse_err" in
    append_endline file s
  end
  
fun debug_replay s =
  let val file = hhs_record_dir ^ "/" ^ current_theory () ^ "/replay_err" in
    append_endline file s
  end  

fun debug_record s =
  let val file = hhs_record_dir ^ "/" ^ current_theory () ^ "/record_err" in
    append_endline file s
  end  

(* --------------------------------------------------------------------------
   String
   -------------------------------------------------------------------------- *)

fun drop_sig s = 
  if last (explode s) = #"."
  then s
  else last (String.fields (fn x => x = #".") s)

fun rm_last_n_string n s =
  let 
    val l = explode s
    val m = length l
  in
    implode (first_n (m - n) l)
  end

fun filename_of s = last (String.tokens (fn x => x = #"/") s) 
  handle _ => raise ERR "filename_of" s

fun split_sl_aux s pl sl = case sl of
    []     => raise ERR "split_sl_aux" ""
  | a :: m => if a = s 
              then (rev pl, m) 
              else split_sl_aux s (a :: pl) m 

fun split_sl s sl = split_sl_aux s [] sl

fun rpt_split_sl s sl = 
  let val (a,b) = split_sl s sl handle _ => (sl,[]) 
  in
    if null b then [a] else a :: rpt_split_sl s b 
  end


fun split_level_aux i s pl sl = case sl of
    []     => raise ERR "split_level_aux" s
  | a :: m => if a = s andalso i <= 0
                then (rev pl, m) 
              else if mem a ["let","local","struct","(","[","{"]
                then split_level_aux (i + 1) s (a :: pl) m
              else if mem a ["end",")","]","}"]
                then split_level_aux (i - 1) s (a :: pl) m
              else split_level_aux i s (a :: pl) m
              
fun split_level s sl = split_level_aux 0 s [] sl

fun rpt_split_level s sl = 
  let val (a,b) = split_level s sl handle _ => (sl,[]) 
  in
    if null b then [a] else a :: rpt_split_level s b 
  end

fun split_charl acc buf csm l1 l2 = 
  if csm = [] then (rev acc, l2) else
  case l2 of
    []     => raise ERR "" ""
  | a :: m => if hd csm = a 
              then split_charl acc (a :: buf) (tl csm) l1 m
              else split_charl (a :: (buf @ acc)) [] l1 l1 m  
  
fun split_string s1 s2 = 
  let 
    val (l1,l2) = (explode s1, explode s2)
    val (rl1,rl2) = split_charl [] [] l1 l1 l2
  in
    (implode rl1, implode rl2)
  end

(* --------------------------------------------------------------------------
   Globals
   -------------------------------------------------------------------------- *)

val hhs_badstacl = ref []
val hhs_cthyfea  = ref []
val hhs_stacfea  = ref (dempty lbl_compare)
val hhs_ddict = ref (dempty goal_compare)
val hhs_ndict = ref (dempty String.compare)

fun update_ddict (lbl,fea) =
  let 
    val oldv = dfind (#3 lbl) (!hhs_ddict) handle _ => [] 
    val newv = (lbl,fea) :: oldv
  in
    hhs_ddict := dadd (#3 lbl) newv (!hhs_ddict)
  end

fun clean_feadata () =
  (
  hhs_stacfea := dempty lbl_compare;
  hhs_cthyfea := []; 
  hhs_ddict := dempty goal_compare;
  hhs_ndict := dempty String.compare
  )

fun init_stacfea_ddict feavl =
  (
  hhs_stacfea := dnew lbl_compare feavl;
  hhs_cthyfea := []; 
  hhs_ddict := dempty goal_compare;
  hhs_ndict := 
    count_dict (dempty String.compare) 
    (map (#1 o fst) (dlist (!hhs_stacfea)))
  ;
  dapp update_ddict (!hhs_stacfea)
  )

fun update_stacfea_ddict (feav as (lbl,fea)) =
  if dmem lbl (!hhs_stacfea) then () else
  let 
    val oldv = dfind (#3 lbl) (!hhs_ddict) handle _ => [] 
    val newv = feav :: oldv
  in
    hhs_stacfea := dadd lbl fea (!hhs_stacfea);
    hhs_cthyfea := feav :: (!hhs_cthyfea);
    hhs_ddict := dadd (#3 lbl) newv (!hhs_ddict);
    hhs_ndict := count_dict (!hhs_ndict) [(#1 lbl)]
  end

end (* struct *)
