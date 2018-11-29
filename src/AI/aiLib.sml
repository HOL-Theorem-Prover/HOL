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

local open Char String in
  fun hash_string s =
    let
      fun hsh (i, A) s =
         hsh (i + 1, (A * 263 + ord (sub (s, i))) mod 792606555396977) s
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
    Dictionaries shortcuts
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

(* one to many transformations *)
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

fun distrib l = case l of
    [] => []
  | (a,al) :: m => map (fn x => (a,x)) al @ distrib m

(* sets *)
fun dset cmp l = dnew cmp (map (fn x => (x,())) l)
fun daddset l d = daddl (map (fn x => (x,())) l)

(* more *)
fun union_dict cmp dl = dnew cmp (List.concat (map dlist dl))

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


fun fold_left f l orig = case l of
    [] => orig
  | a :: m => let val new_orig = f a orig in fold_left f m new_orig end

fun list_diff l1 l2 = filter (fn x => not (mem x l2)) l1

fun subset l1 l2 = all (fn x => mem x l2) l1

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

(* keeps the order *)
fun mk_batch_aux size acc res l =
  if length acc >= size
  then mk_batch_aux size [] (rev acc :: res) l
  else case l of
     [] => rev res
   | a :: m => mk_batch_aux size (a :: acc) res m

fun mk_batch size l = mk_batch_aux size [] [] l

fun number_partition m n =
  if m > n then raise ERR "partition" "" else
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

(* ---------------------------------------------------------------------------
   Parsing
   -------------------------------------------------------------------------- *)

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

fun strip_lisp x = case x of
    Lterm (Lstring x :: m) => (x, m)
  | Lstring x              => (x ,[])
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

fun pow (x:real) (n:int) =
  if n <= 0 then 1.0 else x * (pow x (n-1))

fun approx n r =
  let val mult = pow 10.0 n in
    Real.fromInt (Real.round (r * mult)) / mult
  end

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

fun only_concl x =
  let val (a,b) = dest_thm x in
    if null a then b else raise ERR "only_concl" ""
  end


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

(* -------------------------------------------------------------------------
   Parallelism
   ------------------------------------------------------------------------- *)

datatype 'a result = Res of 'a | Exn of exn;

fun capture f x = Res (f x) handle e => Exn e

fun release (Res y) = y
  | release (Exn x) = raise x

fun is_res (Res y) = true
  | is_res (Exn x) = false

fun is_exn (Res y) = false
  | is_exn (Exn x) = true

fun interruptkill worker =
   if Thread.isActive worker
   then
     (
     Thread.interrupt worker handle Thread _ => ();
     if Thread.isActive worker
       then Thread.kill worker
       else ()
     )
   else ()

fun compare_imin (a,b) = Int.compare (snd a, snd b)

fun parmap_err ncores forg lorg =
  let
    (* input *)
    val sizeorg = length lorg
    val lin = List.tabulate (ncores,(fn x => (x, ref NONE)))
    val din = dnew Int.compare lin
    fun fi xi x = (x,xi)
    val queue = ref (mapi fi lorg)
    (* update process inputs *)
    fun update_from_queue lineref =
      if null (!queue) then ()
      else (lineref := SOME (hd (!queue)); queue := tl (!queue))
    fun is_refnone x = (not o isSome o ! o snd) x
    fun dispatcher () =
      app (update_from_queue o snd) (filter is_refnone lin)
    (* output *)
    val lout = List.tabulate (ncores,(fn x => (x, ref [])))
    val dout = dnew Int.compare lout
    val lcount = List.tabulate (ncores,(fn x => (x, ref 0)))
    val dcount = dnew Int.compare lcount
    (* process *)
    fun process pi =
      let val inref = dfind pi din in
        case !inref of
          NONE => process pi
        | SOME (x,xi) =>
          let
            val oldl = dfind pi dout
            val oldn = dfind pi dcount
            val y = capture forg x
          in
            oldl := (y,xi) :: (!oldl);
            incr oldn;
            inref := NONE;
            process pi
          end
      end
    fun fork_on pi = Thread.fork (fn () => process pi, [])
    val threadl = map fork_on (List.tabulate (ncores,I))
    fun loop () =
      (
      dispatcher ();
      if null (!queue) andalso sum_int (map (! o snd) lcount) >= sizeorg
      then app interruptkill threadl
      else loop ()
      )
  in
    loop ();
    map fst (dict_sort compare_imin (List.concat (map (! o snd) lout)))
  end

fun parmap ncores f l =
  map release (parmap_err ncores f l)

fun parapp ncores f l = ignore (parmap ncores f l)


end (* struct *)
