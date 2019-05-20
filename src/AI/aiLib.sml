(* ========================================================================= *)
(* FILE          : aiLib.sml                                                 *)
(* DESCRIPTION   : Library of useful functions                               *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure aiLib :> aiLib =
struct

open HolKernel Abbrev boolLib

val ERR = mk_HOL_ERR "aiLib"

(* ------------------------------------------------------------------------
   Misc
   ------------------------------------------------------------------------ *)

(* to remove ? *)
type fea = int list
type lbl = (string * real * goal * goal list)

fun vector_to_list v = Vector.foldr (op ::) [] v

fun number_fst start l = case l of
  []      => []
| a :: m  => (start,a) :: number_fst (start + 1) m

fun number_snd start l = case l of
  []      => []
| a :: m  => (a,start) :: number_snd (start + 1) m

fun print_endline s = print (s ^ "\n")

val hash_modulo =
  if valOf (Int.maxInt) > 2147483647
  then 79260655 * 10000000 + 5396977 (* assumes 64 bit *)
  else 1002487 (* assumes 32 bit *)

local open Char String in
  fun hash_string s =
    let
      fun hsh (i, A) s =
         hsh (i + 1, (A * 263 + ord (sub (s, i))) mod hash_modulo) s
         handle Subscript => A
    in
      hsh (0,0) s
    end
end

(* ------------------------------------------------------------------------
   Commands
   ------------------------------------------------------------------------ *)

fun exists_file file = OS.FileSys.access (file, []);

fun mkDir_err dir =
  if exists_file dir then () else OS.FileSys.mkDir dir

fun remove_file file =
  if exists_file file then ignore (OS.FileSys.remove file) else ()

fun run_cmd cmd = ignore (OS.Process.system cmd)

(* TODO: Use OS to change dir? *)
fun cmd_in_dir dir cmd = run_cmd ("cd " ^ dir ^ "; " ^ cmd)

(* -------------------------------------------------------------------------
   Comparisons
   ------------------------------------------------------------------------- *)

fun goal_compare ((asm1,w1), (asm2,w2)) =
  list_compare Term.compare (w1 :: asm1, w2 :: asm2)

fun cpl_compare cmp1 cmp2 ((a1,a2),(b1,b2)) =
  let val r = cmp1 (a1,b1) in
    if r = EQUAL then cmp2 (a2,b2) else r
  end

fun lbl_compare ((stac1,_,g1,_),(stac2,_,g2,_)) =
  cpl_compare String.compare goal_compare ((stac1,g1),(stac2,g2))

fun compare_imax ((_,r2),(_,r1)) = Int.compare (r1,r2)
fun compare_imin ((_,r1),(_,r2)) = Int.compare (r1,r2)

fun compare_rmax ((_,r2),(_,r1)) = Real.compare (r1,r2)
fun compare_rmin ((_,r1),(_,r2)) = Real.compare (r1,r2)

(* -------------------------------------------------------------------------
    Dictionaries
   ------------------------------------------------------------------------- *)

fun dfind k m  = Redblackmap.find (m,k)
fun drem k m   = fst (Redblackmap.remove (m,k)) handle NotFound => m
fun dmem k m   = Lib.can (dfind k) m
fun dadd k v m = Redblackmap.insert (m,k,v)
fun daddl kvl m = Redblackmap.insertList (m,kvl)
val dempty     = Redblackmap.mkDict
val dnew       = Redblackmap.fromList
val dlist      = Redblackmap.listItems
val dlength    = Redblackmap.numItems
val dapp       = Redblackmap.app
val dmap       = Redblackmap.map
val dfoldl     = Redblackmap.foldl
fun dkeys d    = map fst (dlist d)

fun inv_dict cmp d = dnew cmp (map (fn (a,b) => (b,a)) (dlist d))

(* list of values *)
fun dregroup cmp l =
  let
    val d = ref (dempty cmp)
    fun update (k,v) =
      let val oldl = dfind k (!d) handle NotFound => [] in
        d := dadd k (v :: oldl) (!d)
      end
  in
    app update l; !d
  end

fun distrib l = (* inverse of dregroup *)
  let fun f (a,al) = map (fn x => (a,x)) al in List.concat (map f l) end

fun dappend (k,v) d =
  let val oldl = dfind k d handle NotFound => [] in
    dadd k (v :: oldl) d
  end

fun dappendl kvl d = foldl (uncurry dappend) d kvl



fun dconcat cmp dictl =
  let
    val l0 = List.concat (map dlist dictl)
    val l1 = distrib l0
  in
    dappendl l1 (dempty cmp)
  end

(* sets *)
fun dset cmp l = dnew cmp (map (fn x => (x,())) l)
fun daddset l d = daddl (map (fn x => (x,())) l) d
fun union_dict cmp dl = dnew cmp (List.concat (map dlist dl))

(* multi sets *)
fun count_dict startdict l =
  let
    fun f (k,dict) =
      let val old_n = dfind k dict handle _ => 0 in
        dadd k (old_n + 1) dict
      end
  in
    foldl f startdict l
  end

(* -------------------------------------------------------------------------
   References
   ------------------------------------------------------------------------- *)

fun incr x = x := (!x) + 1
fun decr x = x := (!x) + 1

(* -------------------------------------------------------------------------
   List
   ------------------------------------------------------------------------- *)

fun only_hd x = case x of [a] => a | _ => raise ERR "only_hd" ""

fun one_in_n n start l = case l of
    [] => []
  | a :: m => if start mod n = 0
              then a :: one_in_n n (start + 1) m
              else one_in_n n (start + 1) m

fun map_snd f l   = map (fn (a,b) => (a, f b)) l
fun map_fst f l   = map (fn (a,b) => (f a, b)) l
fun map_assoc f l = map (fn a => (a, f a)) l

fun cartesian_product l1 l2 =
  List.concat (map (fn x => map (fn y => (x,y)) l2) l1)

fun quintuple_of_list l = case l of
    [a,b,c,d,e] => (a,b,c,d,e)
  | _ => raise ERR "quintuple_of_list" ""

fun cartesian_productl ll = case ll of 
     [] => [[]]
   | l :: m => 
     let 
       val l0 = cartesian_productl m
       val l1 = cartesian_product l l0
       fun f (a,b) = a :: b
     in
       map f l1
     end



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
fun mk_term_set l = mk_fast_set Term.compare l
fun mk_type_set l = mk_fast_set Type.compare l

fun fold_left f l orig = case l of
    [] => orig
  | a :: m => let val new_orig = f a orig in fold_left f m new_orig end

fun list_diff l1 l2 = filter (fn x => not (mem x l2)) l1

fun subset l1 l2 = all (fn x => mem x l2) l1

fun topo_sort cmp graph =
  let
    val (topl,downl) = List.partition (fn (x,xl) => null xl) graph
    fun list_diff l1 l2 =
        let
          open HOLset
        in
          listItems (difference (fromList cmp l1, fromList cmp l2))
        end
  in
    case (topl,downl) of
        ([],[]) => []
      | ([],_)  => raise ERR "topo_sort" "loop or missing nodes"
      | _       =>
        let
          val topl' = List.map fst topl
          val graph' = List.map (fn (x,xl) => (x,list_diff xl topl')) downl
        in
          topl' @ topo_sort cmp graph'
        end
  end

fun sort_thyl thyl =
    topo_sort String.compare (map (fn x => (x, ancestry x)) thyl)

(* keeps the order *)
fun mk_batch_aux size acc res l =
  if length acc >= size
  then mk_batch_aux size [] (rev acc :: res) l
  else case l of
     [] => (res,acc)
   | a :: m => mk_batch_aux size (a :: acc) res m

(* delete last elements *)
fun mk_batch size l = 
  let val (res,acc) = mk_batch_aux size [] [] l in
    rev res
  end

fun mk_batch_full size l = 
  let val (res,acc) = mk_batch_aux size [] [] l in
    rev (if null acc then res else rev acc :: res)
  end 

fun cut_n n l = 
  let 
    val n1 = length l 
    val bsize = if n1 mod n = 0 then n1 div n else (n1 div n) + 1 
  in 
    mk_batch_full bsize l
  end



fun number_partition m n =
  if m > n orelse m <= 0 then raise ERR "partition" "" else
  if m = 1 then [[n]] else
  let
    fun f x l = x :: l
    val sizel = List.tabulate (n-m+1, fn x => x+1)
    fun g size = map (f size) (number_partition (m-1) (n-size))
  in
    List.concat (map g sizel)
  end

fun duplicate n l =
  List.concat (map (fn x => List.tabulate (n, fn _ => x)) l)

fun indent n = implode (duplicate n [#" "])

fun list_combine ll = case ll of
    [] => []
  | [l] => map (fn x => [x]) l
  | l :: m => let val m' = list_combine m in
                map (fn (a,b) => a :: b) (combine (l,m'))
              end

fun split_triple l = case l of 
    [] => ([], [], [])
  | (a1,a2,a3) :: m => 
    let val (acc1, acc2, acc3) = split_triple m in
      (a1 :: acc1, a2 :: acc2, a3 :: acc3)
    end

fun combine_triple (l1,l2,l3) = case (l1,l2,l3) of
    ([],[],[]) => []
  | (a1 :: m1, a2 :: m2, a3 :: m3) => (a1,a2,a3) :: combine_triple (m1,m2,m3)
  | _ => raise ERR "combine_triple" "different lengths"



(* --------------------------------------------------------------------------
   Parsing
   ------------------------------------------------------------------------- *)

datatype lisp = Lterm of lisp list | Lstring of string

fun lisp_aux acc sl = case sl of
    []       => (rev acc, [])
  | "(" :: m =>
    let val (parsedl,contl) = lisp_aux [] m in
      lisp_aux (Lterm parsedl :: acc) contl
    end
  | ")" :: m => (rev acc, m)
  | a   :: m => lisp_aux (Lstring a :: acc) m

fun lisp_of sl = fst (lisp_aux [] sl)

fun lisp_lower_case s =
  if String.sub (s,0) = #"\""
  then s
  else String.translate (Char.toString o Char.toLower) s

fun strip_lisp x = case x of
    Lterm (Lstring x :: m) => (lisp_lower_case x, m)
  | Lstring x              => (lisp_lower_case x ,[])
  | _                      => raise ERR "strip_lisp" "operator is a comb"

fun rec_fun_type n ty =
  if n <= 1 then ty else mk_type ("fun",[ty,rec_fun_type (n-1) ty])

fun term_of_lisp x =
  let
    val (oper,argl) = strip_lisp x
    val opertm = mk_var (oper, rec_fun_type (length argl + 1) alpha)
  in
    list_mk_comb (opertm, map term_of_lisp argl)
  end

(* ---------------------------------------------------------------------------
   Reals
   -------------------------------------------------------------------------- *)

fun sum_real l = case l of [] => 0.0 | a :: m => a + sum_real m

fun list_rmax l = case l of
    [] => raise ERR "list_max" ""
  | [a] => a
  | a :: m => Real.max (a,list_rmax m)

fun list_imax l = case l of
    [] => raise ERR "list_imax" ""
  | [a] => a
  | a :: m => Int.max (a,list_imax m)

fun sum_int l = case l of [] => 0 | a :: m => a + sum_int m

fun average_real l = sum_real l / Real.fromInt (length l)

fun standard_deviation l =
  let
    val mean     = average_real l
    val variance = average_real (map (fn x => (x - mean) * (x - mean)) l)
  in
    Math.sqrt variance
  end

fun int_div n1 n2 =
   (if n2 = 0 then 0.0 else Real.fromInt n1 / Real.fromInt n2)

fun int_pow a b = 
  if b < 0 then raise ERR "int_pow" "" else 
  if b = 0 then 1 else a * int_pow a (b - 1) 

fun bin_rep nbit n = 
  let 
    fun bin_rep_aux nbit n = 
      if nbit > 0 
      then n mod 2 :: bin_rep_aux (nbit - 1) (n div 2)
      else []
  in
    map Real.fromInt (bin_rep_aux nbit n)
  end

fun pow (x:real) (n:int) =
  if n <= 0 then 1.0 else x * (pow x (n-1))


fun approx n r =
  let val mult = pow 10.0 n in
    Real.fromInt (Real.round (r * mult)) / mult
  end

fun pad n pads s =
  if pads = "" then raise ERR "pad_with" "" else
  if String.size s >= n then s else pad n pads (s ^ pads)

fun percent x = approx 2 (100.0 * x)

(* -------------------------------------------------------------------------
   Terms
   ------------------------------------------------------------------------- *)

fun rename_bvarl f tm =
  let
    val vi = ref 0
    fun rename_aux tm = case dest_term tm of
      VAR(Name,Ty)       => tm
    | CONST{Name,Thy,Ty} => tm
    | COMB(Rator,Rand)   => mk_comb (rename_aux Rator, rename_aux Rand)
    | LAMB(Var,Bod)      =>
      let
        val vs = f (fst (dest_var Var))
        val new_tm = rename_bvar ("V" ^ int_to_string (!vi) ^ vs) tm
        val (v,bod) = dest_abs new_tm
        val _ = incr vi
      in
        mk_abs (v, rename_aux bod)
      end
  in
    rename_aux tm
  end

fun rename_allvar tm =
  let
    val tm0 = list_mk_forall (free_vars_lr tm, tm)
    val tm1 = rename_bvarl (fn x => "") tm0;
    val tm2 = snd (strip_forall tm1)  
  in
    tm2
  end


fun all_bvar tm =
  mk_fast_set Term.compare (map (fst o dest_abs) (find_terms is_abs tm))

fun strip_type ty =
  if is_vartype ty then ([],ty) else
    case dest_type ty of
      ("fun",[a,b]) =>
      let val (tyl,im) = strip_type b in
        (a :: tyl, im)
      end
    | _             => ([],ty)

fun has_boolty x = type_of x = bool

fun only_concl x =
  let val (a,b) = dest_thm x in
    if null a then b else raise ERR "only_concl" ""
  end

fun string_of_goal (asm,w) =
  let
    val mem = !show_types
    val _   = show_types := false
    val s   =
      (if null asm
         then "[]"
         else "[``" ^ String.concatWith "``,``" (map term_to_string asm) ^
              "``]")
    val s1 = "(" ^ s ^ "," ^ "``" ^ (term_to_string w) ^ "``)"
  in
    show_types := mem;
    s1
  end

fun trace_tacl tacl g = case tacl of
    tac :: m => 
    (print_endline (string_of_goal g); trace_tacl m (hd (fst (tac g))))
  | [] => print_endline (string_of_goal g)

fun string_of_bool b = if b then "T" else "F"

fun only_concl x =
  let val (a,b) = dest_thm x in
    if null a then b else raise ERR "only_concl" ""
  end

fun tts tm = case dest_term tm of
    VAR(Name,Ty)       => Name
  | CONST{Name,Thy,Ty} => Name
  | COMB _ =>
    let val (oper,argl) = strip_comb tm in
      case argl of
        [a,b] => "(" ^ String.concatWith " " (map tts [a,oper,b]) ^ ")"
      | _ => "(" ^ String.concatWith " " (map tts (oper :: argl)) ^ ")"
    end
  | LAMB(Var,Bod)      => "(LAMB " ^ tts Var ^ "." ^ tts Bod ^ ")"

fun its i = int_to_string i
fun rts r = Real.toString r

(* -------------------------------------------------------------------------
   I/O
   ------------------------------------------------------------------------- *)

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

fun stream_to_string path f =
  let val oc = TextIO.openOut path in
    f oc; TextIO.closeOut oc; readl path
  end



fun erase_file file = write_file file "" handle _ => ()

fun writel file sl =
  let val oc = TextIO.openOut file in
    app (fn s => TextIO.output (oc, s ^ "\n")) sl;
    TextIO.closeOut oc
  end

fun ancestors_path path =
  let val dir = OS.Path.getParent path in
    if dir = "." orelse dir = "/"
    then []
    else dir :: ancestors_path dir
  end

fun mkPathDir dir path =
  let
    val l0 = rev (ancestors_path path)
    val l1 = map (fn x => (OS.Path.concat (dir,x))) l0
  in
    app mkDir_err l1
  end

fun writel_path dir path sl =
  (
  mkPathDir dir path;
  writel (OS.Path.concat (dir,path)) sl
  )

fun append_file file s =
  let val oc = TextIO.openAppend file in
    TextIO.output (oc,s); TextIO.closeOut oc
  end

fun append_endline file s = append_file file (s ^ "\n")

val debug_flag = ref false
fun debug_in_dir dir file s =
  if !debug_flag
  then (mkDir_err dir;
        append_endline (dir ^ "/" ^ current_theory () ^ "___" ^ file) s)
  else ()

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

(* -------------------------------------------------------------------------
   String
   ------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------
   Escape
   ------------------------------------------------------------------------- *)

fun escape_char c =
  if Char.isAlphaNum c then Char.toString c
  else if c = #"_" then "__"
  else
    let val hex = Int.fmt StringCvt.HEX (Char.ord c) in
      StringCvt.padLeft #"_" 3 hex
    end

fun escape s = String.translate escape_char s;

fun isCapitalHex c =
  Char.ord #"A" <= Char.ord c andalso Char.ord c <= Char.ord #"F"

fun charhex_to_int c =
  if Char.isDigit c
    then Char.ord c - Char.ord #"0"
  else if isCapitalHex c
    then Char.ord c - Char.ord #"A" + 10
  else raise ERR "charhex_to_int" ""

fun unescape_aux l = case l of
   [] => []
 | #"_" :: #"_" :: m => #"_" :: unescape_aux m
 | #"_" :: a :: b :: m =>
   Char.chr (16 * charhex_to_int a + charhex_to_int b) :: unescape_aux m
 | a :: m => a :: unescape_aux m

fun unescape s = implode (unescape_aux (explode s))

(* ------------------------------------------------------------------------
   Random
   ------------------------------------------------------------------------ *)

val new_real = Random.newgen ()

fun random_real () = Random.random new_real

fun shuffle l =
  let
    val l' = map (fn x => (x, random_real ())) l in
      map fst (dict_sort compare_rmin l')
  end

fun random_elem l = hd (shuffle l)
  handle Empty => raise ERR "random_elem" "empty"

fun random_int (a,b) =
  if a >= b then raise ERR "random_int" "" else
  let 
    val (ar,br) = (Real.fromInt a, Real.fromInt b)
    val c = Real.floor (ar + random_real () * (br - ar + 1.0))
  in
    if c >= b then b else c
  end

fun cumul_proba (tot:real) l = case l of
    [] => []
  | (mv,p) :: m => (mv, tot + p) :: cumul_proba (tot + p) m

fun find_cumul proba cumul = case cumul of
    []  => raise ERR "find_cumul" ""
  | [a] => fst a
  | (mv,p) :: m => if proba < (p:real) then mv else find_cumul proba m

fun select_in_distrib l =
  let
    val l' = cumul_proba 0.0 l
    val (_,tot) = last l'
  in
    find_cumul (random_real () * tot) l'
  end

fun random_percent percent l =
  part_n (Real.floor (percent * Real.fromInt (length l))) (shuffle l)

(* -------------------------------------------------------------------------
   Parallelism (currently slowing functions inside threads)
   ------------------------------------------------------------------------- *)

(* small overhead due to waiting safely for the thread to close *)
fun interruptkill worker =
   if not (Thread.isActive worker) then () else
     let
       val _ = Thread.interrupt worker handle Thread _ => ()
       fun loop n =
         if not (Thread.isActive worker) then () else
           if n > 0
           then (OS.Process.sleep (Time.fromReal 0.0001); loop (n-1))
           else (print_endline "Warning: thread killed"; Thread.kill worker)
     in
       loop 10
     end

(* -------------------------------------------------------------------------
   Neural network units
   ------------------------------------------------------------------------- *)

val oper_compare = cpl_compare Term.compare Int.compare

fun all_fosubtm tm =
  let val (oper,argl) = strip_comb tm in
    tm :: List.concat (map all_fosubtm argl)
  end

fun operl_of tm =
  let
    val tml = mk_fast_set Term.compare (all_fosubtm tm)
    fun f x = let val (oper,argl) = strip_comb x in (oper, length argl) end
  in
    mk_fast_set oper_compare (map f tml)
  end

(* -------------------------------------------------------------------------
   Position
   ------------------------------------------------------------------------- *)

type pos = int list

fun subst_pos (tm,pos) res =
  if null pos then res else
  let
    val (oper,argl) = strip_comb tm
    fun f i x = if i = hd pos then subst_pos (x,tl pos) res else x
    val newargl = mapi f argl
  in
    list_mk_comb (oper,newargl)
  end

fun find_subtm (tm,pos) =
  if null pos then tm else
  let val (oper,argl) = strip_comb tm in
    find_subtm (List.nth (argl,hd pos), tl pos)
  end

fun narg_ge n (tm,pos) =
  let val (_,argl) = strip_comb (find_subtm (tm,pos)) in length argl >= n end

fun all_pos tm = 
  let 
    val (oper,argl) = strip_comb tm 
    fun f i arg = map (fn x => i :: x) (all_pos arg)
  in
    [] :: List.concat (mapi f argl) 
  end

(* -------------------------------------------------------------------------
   Arithmetic
   ------------------------------------------------------------------------- *)

fun mk_suc x = mk_comb (``SUC``,x);
fun mk_add (a,b) = list_mk_comb (``$+``,[a,b]);
val zero = ``0:num``;
fun mk_sucn n = funpow n mk_suc zero;
fun mk_mult (a,b) = list_mk_comb (``$*``,[a,b]);

fun dest_suc x =
  let val (a,b) = dest_comb x in
    if not (term_eq  a ``SUC``) then raise ERR "" "" else b
  end

fun dest_add tm =
  let val (oper,argl) = strip_comb tm in
    if not (term_eq oper ``$+``) then raise ERR "" "" else pair_of_list argl
  end

fun is_suc_only tm = 
  if term_eq tm zero then true else
  (is_suc_only (dest_suc tm)  handle HOL_ERR _ => false)

(* -------------------------------------------------------------------------
   Equality
   ------------------------------------------------------------------------- *)

fun sym x = mk_eq (swap (dest_eq x))

fun unify a b = Unify.simp_unify_terms [] a b

fun paramod_ground eq (tm,pos) =
  let
    val (eql,eqr) = dest_eq eq
    val subtm = find_subtm (tm,pos)
    val sigma = unify eql subtm
    val eqrsig = subst sigma eqr
    val tmsig = subst sigma tm
    val result = subst_pos (tmsig,pos) eqrsig
  in
    if term_eq result tm orelse length (free_vars_lr result) > 0
    then NONE
    else SOME result
  end
  handle Interrupt => raise Interrupt | _ => NONE


end (* struct *)
