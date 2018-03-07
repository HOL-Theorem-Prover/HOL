(* ========================================================================== *)
(* FILE          : tttTools.sml                                               *)
(* DESCRIPTION   : Library of useful functions for TacticToe                  *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure tttTools :> tttTools =
struct

open HolKernel boolLib Abbrev Dep tttRedirect

val ERR = mk_HOL_ERR "tttTools"

type lbl_t = (string * real * goal * goal list)
type fea_t = int list
type feav_t = (lbl_t * fea_t)

(* --------------------------------------------------------------------------
   Global parameters
   -------------------------------------------------------------------------- *)

val ttt_tactic_time = ref 0.0
val ttt_search_time = ref (Time.fromReal 0.0)

(* --------------------------------------------------------------------------
   Directories
   -------------------------------------------------------------------------- *)

val tactictoe_dir   = HOLDIR ^ "/src/tactictoe"

val ttt_tacfea_dir  = tactictoe_dir ^ "/fea_tactic"
val ttt_thmfea_dir  = tactictoe_dir ^ "/fea_theorem"
val ttt_glfea_dir   = tactictoe_dir ^ "/fea_goallist"

val ttt_code_dir    = tactictoe_dir ^ "/gen_code"
val ttt_open_dir    = tactictoe_dir ^ "/gen_open"

val ttt_search_dir  = tactictoe_dir ^ "/log_search"
val ttt_record_dir  = tactictoe_dir ^ "/log_record"
val ttt_unfold_dir = tactictoe_dir ^ "/log_unfold"

fun hide_out f x =
  hide_in_file (ttt_code_dir ^ "/" ^ current_theory () ^ "_hide_out") f x

(* --------------------------------------------------------------------------
   Commands
   -------------------------------------------------------------------------- *)

fun mkDir_err dir = OS.FileSys.mkDir dir handle _ => ()
fun rmDir_rec dir = ignore (OS.Process.system ("rm -r " ^ dir))
fun run_cmd cmd = ignore (OS.Process.system cmd)
fun cmd_in_dir dir cmd = run_cmd ("cd " ^ dir ^ "; " ^ cmd)

fun exists_file file = OS.FileSys.access (file, []);


(* --------------------------------------------------------------------------
    Dictionaries shortcuts
   -------------------------------------------------------------------------- *)

fun dfind k m  = Redblackmap.find (m,k)
fun dfind_err msg x dict = dfind x dict handle _ => raise ERR "dfind" msg

fun drem k m   = fst (Redblackmap.remove (m,k)) handle NotFound => m
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

fun findSome f l = case l of
    [] => NONE
  | a :: m =>
    let val r = f a in
      if isSome r then r else findSome f m
    end

fun first_n n l =
  if n <= 0 orelse null l
  then []
  else hd l :: first_n (n - 1) (tl l)

fun first_test_n test n l =
  if n <= 0 orelse null l
    then []
  else if test (hd l)
    then hd l :: first_test_n test (n - 1) (tl l)
  else first_test_n test n (tl l)

fun part_aux n acc l =
  if n <= 0 orelse null l
  then (rev acc,l)
  else part_aux (n - 1) (hd l :: acc) (tl l)

fun part_n n l = part_aux n [] l

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

fun sort_thyl thyl = topo_sort (map (fn x => (x, ancestry x)) thyl)


(* ---------------------------------------------------------------------------
   Reals
   -------------------------------------------------------------------------- *)

fun sum_real l = case l of [] => 0.0 | a :: m => a + sum_real m

fun list_rmax l = case l of
    [] => raise ERR "list_max" ""
  | [a] => a
  | a :: m => Real.max (a,list_rmax m)

fun sum_int l = case l of [] => 0 | a :: m => a + sum_int m

fun average_real l = sum_real l / Real.fromInt (length l)

(* --------------------------------------------------------------------------
   Goal
   -------------------------------------------------------------------------- *)

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

fun string_of_bool b = if b then "T" else "F"

(* --------------------------------------------------------------------------
   Comparisons
   -------------------------------------------------------------------------- *)

fun compare_rmax ((_,r2),(_,r1)) = Real.compare (r1,r2)
fun compare_rmin ((_,r1),(_,r2)) = Real.compare (r1,r2)

fun goal_compare ((asm1,w1), (asm2,w2)) =
  list_compare Term.compare (w1 :: asm1, w2 :: asm2)

fun cpl_compare cmp1 cmp2 ((a1,a2),(b1,b2)) =
  let val r = cmp1 (a1,b1) in
    if r = EQUAL then cmp2 (a2,b2) else r
  end

fun strict_term_compare (t1,t2) =
  if Portable.pointer_eq (t1,t2) then EQUAL
  else if is_var t1 andalso is_var t2 then Term.compare (t1,t2)
  else if is_var t1 then LESS
  else if is_var t2 then GREATER
  else if is_const t1 andalso is_const t2 then Term.compare (t1,t2)
  else if is_const t1 then LESS
  else if is_const t2 then GREATER
  else if is_comb t1 andalso is_comb t2 then
    cpl_compare strict_term_compare
      strict_term_compare (dest_comb t1, dest_comb t2)
  else if is_comb t1 then LESS
  else if is_comb t2 then GREATER
  else
    cpl_compare Term.compare strict_term_compare (dest_abs t1, dest_abs t2)

fun strict_goal_compare ((asm1,w1), (asm2,w2)) =
  list_compare strict_term_compare (w1 :: asm1, w2 :: asm2)

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

(* unfold_dir *)
val ttt_unfold_cthy = ref "scratch"

fun debug_unfold s =
  append_endline (ttt_unfold_dir ^ "/" ^ !ttt_unfold_cthy) s

(* search_dir *)
fun debug s = append_endline (ttt_search_dir ^ "/debug/" ^ current_theory ()) s

fun debug_err s = (debug s; raise ERR "debug_err" s)

fun debug_t s f x =
  let
    val _ = debug s
    val (r,t) = add_time f x
    val _ = debug (s ^ " " ^ Real.toString t)
  in
    r
  end

val debugsearch_flag = ref false

fun set_debugsearch b = debugsearch_flag := b

fun debug_search s =
  if !debugsearch_flag
  then append_endline (ttt_search_dir ^ "/search/" ^ current_theory ()) s
  else ()

fun debug_proof s =
  append_endline (ttt_search_dir ^ "/proof/" ^ current_theory ()) s

(* record_dir *)
fun debug_parse s =
  append_endline (ttt_record_dir ^ "/parse/" ^ current_theory ()) s

fun debug_replay s =
  append_endline (ttt_record_dir ^ "/replay/" ^ current_theory ()) s

fun debug_record s =
  append_endline (ttt_record_dir ^ "/record/" ^ current_theory ()) s

(* --------------------------------------------------------------------------
   Parsing
   -------------------------------------------------------------------------- *)

fun unquote_string s =
  if String.sub (s,0) = #"\"" andalso String.sub (s,String.size s - 1) = #"\""
  then String.substring (s, 1, String.size s - 2)
  else raise ERR "unquote_string" s

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
    []     => raise ERR "split_charl" ""
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
  handle _ => raise ERR "split_string" (s1 ^ " " ^ s2)

fun rm_prefix s2 s1 =
  let val (a,b) = split_string s1 s2 in
    if a = "" then b else raise ERR "rm_prefix" (s2 ^ " " ^ s1)
  end

fun rm_squote s =
  if String.sub (s,0) = #"\"" andalso String.sub (s,String.size s - 1) = #"\""
  then String.substring (s, 1, String.size s - 2)
  else raise ERR "rm_squote" s

fun rm_space_aux l = case l of
    [] => []
  | a :: m => if a = #" " then rm_space_aux m else l

fun rm_space s = implode (rm_space_aux (explode s))

(* --------------------------------------------------------------------------
   Tactics
   -------------------------------------------------------------------------- *)

val ttt_tacerr      = ref []
val ttt_tacfea      = ref (dempty lbl_compare)
val ttt_tacfea_cthy = ref (dempty lbl_compare)
val ttt_tacdep      = ref (dempty goal_compare)
val ttt_taccov      = ref (dempty String.compare)

(* --------------------------------------------------------------------------
   Theorems
   -------------------------------------------------------------------------- *)

val ttt_thmfea = ref (dempty goal_compare)

val namespace_tag = "namespace_tag"
(* Warning: causes a problem if you name your theory namespace_tag *)

fun dbfetch_of_string s =
  let val (a,b) = split_string "Theory." s in
    if a = current_theory ()
      then String.concatWith " " ["DB.fetch",mlquote a,mlquote b]
    else
      if a = namespace_tag then b else s
  end

fun mk_metis_call sl =
  "metisTools.METIS_TAC " ^
  "[" ^ String.concatWith " , " (map dbfetch_of_string sl) ^ "]"

(* --------------------------------------------------------------------------
   Lists of goals
   -------------------------------------------------------------------------- *)

val ttt_glfea = ref (dempty (list_compare Int.compare))
val ttt_glfea_cthy = ref (dempty (list_compare Int.compare))

(* --------------------------------------------------------------------------
   Cleaning tactictoe data (not necessary)
   -------------------------------------------------------------------------- *)

fun clean_tttdata () =
  (
  ttt_tacerr := [];
  ttt_tacfea := dempty lbl_compare;
  ttt_tacfea_cthy := dempty lbl_compare;
  ttt_tacdep := dempty goal_compare;
  ttt_taccov := dempty String.compare;
  ttt_thmfea := dempty goal_compare;
  ttt_glfea := dempty (list_compare Int.compare);
  ttt_glfea_cthy := dempty (list_compare Int.compare)
  )

end (* struct *)
