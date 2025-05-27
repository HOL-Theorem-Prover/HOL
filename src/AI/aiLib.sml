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

fun vector_to_list v = Vector.foldr (op ::) [] v
fun array_to_list v = Array.foldr (op ::) [] v

fun number_fst start l = case l of
  []      => []
| a :: m  => (start,a) :: number_fst (start + 1) m

fun number_snd start l = case l of
  []      => []
| a :: m  => (a,start) :: number_snd (start + 1) m

fun is_singleton l = case l of [a] => true | _ => false

fun print_endline s = print (s ^ "\n")

fun hash_string_mod modulo s =
  let
    fun hsh (i, A) s =
       hsh (i + 1, (A * 263 + Char.ord (String.sub (s, i))) mod modulo) s
       handle Subscript => A
  in
    hsh (0,0) s
  end

val hash_modulo =
    case Int.maxInt of
        NONE => 79260655 * 10000000 + 5396977
      | SOME i => if i > 2147483647
                  then 79260655 * 10000000 + 5396977 (* assumes 64 bit *)
                  else 1002487 (* assumes 32 bit *)

val hash_string = hash_string_mod hash_modulo

fun inter_increasing l1 l2 = case (l1,l2) of
    ([],_) => []
  | (_,[]) => []
  | (a1 :: m1, a2 :: m2) =>
    (
    case Int.compare (a1,a2) of
      LESS => inter_increasing m1 l2
    | GREATER => inter_increasing l1 m2
    | EQUAL => a1 :: inter_increasing m1 m2
    )

(* ------------------------------------------------------------------------
   Commands
   ------------------------------------------------------------------------ *)

fun exists_file file = HOLFileSys.access (file, []);

fun mkDir_err dir =
  if exists_file dir then () else HOLFileSys.mkDir dir

fun remove_file file =
  if exists_file file then ignore (OS.FileSys.remove file) else ()

fun run_cmd cmd = ignore (OS.Process.system cmd)

(* TODO: Use OS to change dir? *)
fun cmd_in_dir dir cmd = run_cmd ("cd " ^ dir ^ "; " ^ cmd)
fun clean_dir dir = (run_cmd ("rm -r " ^ dir); mkDir_err dir)

(* ------------------------------------------------------------------------
   Comparisons
   ------------------------------------------------------------------------ *)

fun cpl_compare cmp1 cmp2 ((a1,a2),(b1,b2)) =
  let val r = cmp1 (a1,b1) in
    if r = EQUAL then cmp2 (a2,b2) else r
  end

fun goal_compare ((asm1,w1), (asm2,w2)) =
  list_compare Term.compare (w1 :: asm1, w2 :: asm2)

fun triple_compare cmp1 cmp2 cmp3 ((a1,a2,a3),(b1,b2,b3)) =
  cpl_compare (cpl_compare cmp1 cmp2) cmp3 (((a1,a2),a3),((b1,b2),b3))

fun fst_compare cmp ((a,_),(b,_)) = cmp (a,b)
fun snd_compare cmp ((_,a),(_,b)) = cmp (a,b)

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

(* ------------------------------------------------------------------------
   References
   ------------------------------------------------------------------------ *)

fun incr x = x := (!x) + 1
fun decr x = x := (!x) - 1

(* ------------------------------------------------------------------------
   List
   ------------------------------------------------------------------------ *)

fun one_in_n n start l = case l of
    [] => []
  | a :: m => if start mod n = 0
              then a :: one_in_n n (start + 1) m
              else one_in_n n (start + 1) m

fun map_snd f l   = map (fn (a,b) => (a, f b)) l
fun map_fst f l   = map (fn (a,b) => (f a, b)) l
fun map_assoc f l = map (fn a => (a, f a)) l

fun range ((a,b),f) =
  if a > b then raise ERR "range" "" else
  List.tabulate (b-a+1,fn x => f (x+a))

fun cartesian_product l1 l2 =
  List.concat (map (fn x => map (fn y => (x,y)) l2) l1)

fun all_pairs l = case l of
    [] => []
  | [a] => []
  | a :: m => map (fn x => (a,x)) m @ all_pairs m

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

fun part_group groupl l = case groupl of
    [] => if null l then [] else raise ERR "part_group" ""
  | a :: m => let val (l1,l2) = part_n a l in
                l1 :: part_group m l2
              end

fun part_pct r l = part_n (Real.round (Real.fromInt (length l) * r)) l

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

fun tmsize_compare (a,b) =
  let val r = Int.compare (term_size a, term_size b) in
    if r = EQUAL then Term.compare (a,b) else r
  end

fun all_subterms tm =
  let
    val r = ref []
    fun traverse tm =
      let val (oper,argl) = strip_comb tm in
        r := oper :: (!r);
        app traverse argl
      end
  in
    traverse tm; !r
  end

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

fun interleave offset l1 l2 =
  let
    val l1' = map_snd (fn x => 2 * x) (number_snd 1 l1)
    val l2' = map_snd (fn x => offset * 2 * x + 1) (number_snd 1 l2)
  in
    map fst (dict_sort compare_imin (l1' @ l2'))
  end

(* ------------------------------------------------------------------------
   Efficient algorithm for finding the k largest values in a list.
   ------------------------------------------------------------------------ *)

fun swap_value (arr,a,b) =
  let
    val av = Array.sub (arr,a)
    val bv = Array.sub (arr,b)
  in
    Array.update (arr,a,bv);
    Array.update (arr,b,av)
  end

fun heapify cmp arr n i =
  let
    val largest = ref i
    val left = 2 * i + 1
    val right = 2 * i + 2
  in
    if left < n andalso
       cmp (Array.sub (arr,left),Array.sub (arr,!largest)) = LESS
    then largest := left
    else ();
    if right < n andalso
       cmp (Array.sub (arr,right),Array.sub (arr,!largest)) = LESS
    then largest := right
    else ();
    if !largest <> i
    then (swap_value (arr,i,!largest); heapify cmp arr n (!largest))
    else ()
  end

fun build_maxheap cmp arr =
  let
    val n = Array.length arr
    val i = n div 2 - 1
  in
    ignore (List.tabulate (i + 1, fn x => heapify cmp arr n (i - x)))
  end

fun delete_root cmp n arr =
  let
    val lastElement = Array.sub (arr,n-1)
  in
    Array.update (arr,0,lastElement);
    heapify cmp arr (n-1) 0
  end

fun best_n cmp k l =
  let
    val arr = Array.fromList l
    val n = Array.length arr
    val k' = Int.min (k,n)
    val _ = build_maxheap cmp arr
    fun f i =
      let val r = Array.sub (arr,0) in delete_root cmp (n-i) arr; r end
  in
    List.tabulate (k',f)
  end

fun best_n_rmaxu cmp k l =
  let
    val arr = Array.fromList l
    val n = Array.length arr
    val _ = build_maxheap compare_rmax arr
    fun loop i (d,l) =
      if dlength d >= k orelse n-i <= 0 then rev l else
      let val r = fst (Array.sub (arr,0)) in
        delete_root compare_rmax (n-i) arr;
        loop (i+1) (if dmem r d then (d,l) else (dadd r () d, r :: l))
      end
  in
    loop 0 (dempty cmp, [])
  end

(* ------------------------------------------------------------------------
   The functions from this section affects other in subtle ways.
   Please be careful to keep their "weird" semantics.
   ------------------------------------------------------------------------ *)

(* keeps the order *)
fun mk_batch_aux size (acc,accsize) res l =
  if accsize >= size
  then mk_batch_aux size ([],0) (rev acc :: res) l
  else case l of
     [] => (res,acc)
   | a :: m => mk_batch_aux size ((a :: acc),accsize + 1) res m

(* delete last elements *)
fun mk_batch size l =
  let val (res,acc) = mk_batch_aux size ([],0) [] l in
    rev res
  end

fun mk_batch_full size l =
  let val (res,acc) = mk_batch_aux size ([],0) [] l in
    rev (if null acc then res else rev acc :: res)
  end

fun cut_n n l =
  let
    val n1 = length l
    val bsize = if n1 mod n = 0 then n1 div n else (n1 div n) + 1
  in
    mk_batch_full bsize l
  end

fun cut_modulo n l =
  let
    val l1 = map_fst (fn x => x mod n) (number_fst 0 l)
    val d = dregroup Int.compare (rev l1)
  in
    map snd (dlist d)
  end

(* ------------------------------------------------------------------------
   List (continued)
   ------------------------------------------------------------------------ *)

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

(* -------------------------------------------------------------------------
   Parsing
   ------------------------------------------------------------------------ *)

fun hd_string s = String.sub (s,0)
fun tl_string s = String.substring (s, 1, String.size s - 1)

datatype lisp = Lterm of lisp list | Lstring of string

fun implo buf = if null buf then [] else [implode (rev buf)]

fun lisp_tokens acc buf charl = case charl of
    [] => rev acc
  | #"(" :: m => lisp_tokens ("(" :: implo buf @ acc) [] m
  | #")" :: m => lisp_tokens (")" :: implo buf @ acc) [] m
  | #" " :: m => lisp_tokens (implo buf @ acc) [] m
  | a :: m => lisp_tokens acc (a :: buf) m

fun lisp_lexer s = lisp_tokens [] [] (explode s)

fun lisp_parser_aux acc sl = case sl of
    []       => (rev acc, [])
  | "(" :: m =>
    let val (parsedl,contl) = lisp_parser_aux [] m in
      lisp_parser_aux (Lterm parsedl :: acc) contl
    end
  | ")" :: m => (rev acc, m)
  | a   :: m => lisp_parser_aux (Lstring a :: acc) m

fun lisp_parser s = fst (lisp_parser_aux [] (lisp_lexer s))

fun lisp_lower_case s =
  if String.sub (s,0) = #"\""
  then s
  else String.translate (Char.toString o Char.toLower) s

fun strip_lisp x = case x of
    Lterm (Lstring x :: m) => (lisp_lower_case x, m)
  | Lstring x              => (lisp_lower_case x ,[])
  | _                      => raise ERR "strip_lisp" "operator is a comb"

fun rpt_fun_type n ty =
  if n <= 1 then ty else mk_type ("fun",[ty,rpt_fun_type (n-1) ty])

fun term_of_lisp x =
  let
    val (oper,argl) = strip_lisp x
    val opertm = mk_var (oper, rpt_fun_type (length argl + 1) alpha)
  in
    list_mk_comb (opertm, map term_of_lisp argl)
  end

(* ------------------------------------------------------------------------
   Reals and integers
   ------------------------------------------------------------------------ *)

fun sum_real l = case l of [] => 0.0 | a :: m => a + sum_real m

fun list_rmax l = case l of
    [] => raise ERR "list_max" ""
  | [a] => a
  | a :: m => Real.max (a,list_rmax m)

fun list_imax l = case l of
    [] => raise ERR "list_imax" ""
  | [a] => a
  | a :: m => Int.max (a,list_imax m)


fun vector_max score v =
  let
    fun f (i,x,(maxi,maxsc)) =
      let val sc = score x in
        if sc > maxsc then (i,sc) else (maxi,maxsc)
      end
  in
    Vector.foldli f (0,Real.negInf) v
  end

fun vector_maxi score v = fst (vector_max score v)



fun vector_mini score v =
  let
    fun f (i,x,(mini,minsc)) =
      let val sc = score x in
        if sc < minsc then (i,sc) else (mini,minsc)
      end
  in
    fst (Vector.foldli f (0,Real.posInf) v)
  end


fun list_imin l = case l of
    [] => raise ERR "list_imin" ""
  | [a] => a
  | a :: m => Int.min (a,list_imin m)

fun div_equal n m =
  let val (q,r) = (n div m, n mod m) in
    List.tabulate (m, fn i => q + (if i < r then 1 else 0))
  end

fun sum_int l = case l of [] => 0 | a :: m => a + sum_int m

fun average_real l = sum_real l / Real.fromInt (length l)
fun average_int l = average_real (map Real.fromInt l)

fun standard_deviation l =
  let
    val mean     = average_real l
    val variance = average_real (map (fn x => (x - mean) * (x - mean)) l)
  in
    Math.sqrt variance
  end

fun absolute_deviation l =
  let val m = average_real l in
    average_real (map (fn x => Real.abs (x - m)) l)
  end

fun int_product nl = case nl of
    [] => 1
  | a :: m => a * int_product m

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

fun rts r = Real.toString r
fun rts_round n r = rts (approx n r)
fun pretty_real r = pad 8 "0" (rts_round 6 r)

fun interval (step:real) (a,b) =
  if a + (step / 2.0) > b then [b] else a :: interval step (a + step,b)

(* ------------------------------------------------------------------------
   Terms
   ------------------------------------------------------------------------ *)

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

fun strip_type_n n ty =
  if is_vartype ty orelse n = 0 then ([],ty) else
    case dest_type ty of
      ("fun",[a,b]) =>
      let val (tyl,im) = strip_type_n (n-1) b in
        (a :: tyl, im)
      end
    | _             => raise ERR "strip_type_n" ""

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

fun string_of_goal_noquote (asm,w) =
  let
    val mem = !show_types
    val _   = show_types := false
    val s   =
      (if null asm
         then "[]"
         else "[" ^ String.concatWith "," (map term_to_string asm) ^ "]")
    val s1 = "(" ^ s ^ "," ^ (term_to_string w) ^ ")"
  in
    show_types := mem;
    s1
  end

fun trace_tacl tacl g = case tacl of
    tac :: m =>
    (print_endline (string_of_goal g); trace_tacl m (hd (fst (tac g))))
  | [] => print_endline (string_of_goal g)

fun only_concl x =
  let val (a,b) = dest_thm x in
    if null a then b else raise ERR "only_concl" ""
  end

fun list_mk_binop binop l = case l of
    [] => raise ERR "list_mk_binop" "empty"
  | [a] => a
  | a :: m => list_mk_comb  (binop, [a, list_mk_binop binop m])

fun arity_of t = length (fst (strip_type (type_of t)))

fun strip_binop binop tm = case strip_comb tm of
    (oper,[a,b]) =>
    if term_eq oper binop
    then a :: strip_binop binop b
    else [tm]
  | _ => [tm]


local open HOLsexp SharingTables in

(* -------------------------------------------------------------------------
   Exporting terms
   ------------------------------------------------------------------------- *)

fun pp_tml tml =
  let
    val ed = {unnamed_terms = tml, named_terms = [], unnamed_types = [],
              named_types = [], theorems = []}
    val sdo = build_sharing_data ed
    val sexp = enc_sdata sdo
  in
    HOLsexp.printer sexp
  end

fun export_terml file tml =
  let
    val tml' = filter uptodate_term tml
    val _ = if length tml <> length tml'
            then raise ERR "" "out-of-date terms"
            else ()
    val ostrm = Portable.open_out file
  in
    (PP.prettyPrint (curry HOLFileSys.output ostrm, 75) (pp_tml tml');
     HOLFileSys.closeOut ostrm)
  end

fun export_goal file (goal as (asl,w)) =
  export_terml file (w :: asl)
  handle HOL_ERR _ =>
  print_endline "Warning: goal contained out-of-date terms (not exported it)"

(* -------------------------------------------------------------------------
   Importing terms
   ------------------------------------------------------------------------- *)

fun import_terml file =
  let
    val t = HOLsexp.fromFile file
  in
    case TheoryReader.core_decode t of
        NONE => raise Option
      | SOME {exports,tables} =>
        let
          val sdo = dec_sdata {before_types = fn _ => (),
                               before_terms = fn _ => (),
                               tables = tables,
                               exports = exports}
        in
          #unnamed_terms (export_from_sharing_data sdo)
        end
  end

fun import_goal file = let val l = import_terml file in (tl l, hd l) end

(* ------------------------------------------------------------------------
   S-expressions
   ------------------------------------------------------------------------ *)

(* basic encoding *)

val enc_real = String o Real.toString
val dec_real = Option.mapPartial Real.fromString o string_decode

(* data with terms *)
fun sharing_terms tml =
  let
    val ed = {named_terms = [], unnamed_terms = [], named_types = [],
              unnamed_types = [], theorems = []}
    val sdi1 = build_sharing_data ed
    val sdi2 = add_terms tml sdi1
    fun f sdi t = write_term sdi t handle NotFound =>
      (print_endline ("write_term: " ^ term_to_string t);
       raise ERR "write_term" (term_to_string t))
  in
    (String o f sdi2, sdi2)
  end

fun enc_tmdata (encf,tmlf) tmdata =
  let val (enc_tm,sdi) = sharing_terms (tmlf tmdata) in
    pair_encode (enc_sdata, encf enc_tm) (sdi,tmdata)
  end

fun dec_tmdata decf t =
  let
    val ({exports,tables}, tmdata) = valOf (pair_decode (TheoryReader.core_decode, SOME) t)
    val sdo = dec_sdata {exports = exports, tables = tables,
                         before_types = fn _ => (), before_terms = fn _ => ()}
    val dec_tm = Option.map (read_term sdo) o string_decode
  in
    decf dec_tm tmdata
  end

fun write_tmdata (encf,tmlf) file tmdata =
  let
    val ostrm = Portable.open_out file
    val sexp = enc_tmdata (encf,tmlf) tmdata
  in
    PP.prettyPrint (curry HOLFileSys.output ostrm, 75) (HOLsexp.printer sexp);
    HOLFileSys.closeOut ostrm
  end

fun read_tmdata decf file =
  valOf (dec_tmdata decf (HOLsexp.fromFile file))

(* data without terms *)
fun write_data encf file tmdata =
  let
    val ostrm = Portable.open_out file
    val sexp = encf tmdata
  in
    PP.prettyPrint (curry HOLFileSys.output ostrm, 75) (HOLsexp.printer sexp);
    HOLFileSys.closeOut ostrm
  end

fun read_data decf file = valOf (decf (HOLsexp.fromFile file))

end (* local *)

(* ------------------------------------------------------------------------
   I/O
   ------------------------------------------------------------------------ *)

fun bts b = if b then "true" else "false"
fun string_to_bool s =
  if s = "true" then true else if s = "false" then false
  else raise ERR "string_to_bool" ""

fun tts tm = case dest_term tm of
    VAR(Name,Ty)       => Name
  | CONST{Name,Thy,Ty} => Name
  | COMB _ =>
    let val (oper,argl) = strip_comb tm in
      "(" ^ String.concatWith " " (map tts (oper :: argl)) ^ ")"
    end
  | LAMB(Var,Bod)      => "(LAMB " ^ tts Var ^ "." ^ tts Bod ^ ")"

fun its i = int_to_string i

fun reall_to_string rl = String.concatWith " " (map rts rl)

fun realll_to_string rll =
  String.concatWith "," (map reall_to_string rll)

fun string_to_reall s =
  map (valOf o Real.fromString) (String.tokens Char.isSpace s)

fun string_to_realll s =
  let val sl = String.tokens (fn x => x = #",") s in
    map string_to_reall sl
  end

fun bare_readl path =
  let
    val file = HOLFileSys.openIn path
    fun loop file = case HOLFileSys.inputLine file of
        SOME line => line :: loop file
      | NONE => []
    val l = loop file
  in
    (HOLFileSys.closeIn file; l)
  end

fun readl path =
  let
    val file = HOLFileSys.openIn path
    fun loop file = case HOLFileSys.inputLine file of
        SOME line => line :: loop file
      | NONE => []
    val l1 = loop file
    fun rm_last_char s = String.substring (s,0,String.size s - 1)
    fun is_empty s = s = ""
    val l2 = map rm_last_char l1 (* removing end line *)
    val l3 = filter (not o is_empty) l2
  in
    (HOLFileSys.closeIn file; l3)
  end

fun readl_empty path =
  let
    val file = HOLFileSys.openIn path
    fun loop file = case HOLFileSys.inputLine file of
        SOME line => line :: loop file
      | NONE => []
    val l1 = loop file
    fun rm_last_char s = String.substring (s,0,String.size s - 1)
    val l2 = map rm_last_char l1 (* removing end line *)
  in
    (HOLFileSys.closeIn file; l2)
  end

fun write_file file s =
  let val oc = HOLFileSys.openOut file in
    HOLFileSys.output (oc,s); HOLFileSys.closeOut oc
  end

fun stream_to_string path f =
  let val oc = HOLFileSys.openOut path in
    f oc; HOLFileSys.closeOut oc; readl path
  end

fun erase_file file = write_file file "" handle _ => ()

fun writel file sl =
  let val oc = HOLFileSys.openOut file in
    app (fn s => HOLFileSys.output (oc, s ^ "\n")) sl;
    HOLFileSys.closeOut oc
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
  let val oc = HOLFileSys.openAppend file in
    HOLFileSys.output (oc,s); HOLFileSys.closeOut oc
  end

fun append_endline file s = append_file file (s ^ "\n")

val debug_flag = ref false
fun debug s = if !debug_flag then print_endline s else ()
fun debugf s f x = if !debug_flag then print_endline (s ^ (f x)) else ()

fun write_texgraph file (s1,s2) l =
  writel file ((s1 ^ " " ^ s2) :: map (fn (a,b) => its a ^ " " ^ its b) l);

fun writel_atomic file sl =
  (writel (file ^ "_temp") sl;
   OS.FileSys.rename {old = file ^ "_temp", new=file})

fun readl_rm file =
  let val sl = readl file in OS.FileSys.remove file; sl end

fun listDir_all dirName =
  let
    val dir = HOLFileSys.openDir dirName
    fun read files = case HOLFileSys.readDir dir of
        NONE => rev files
      | SOME file => read (file :: files)
    val r = read []
  in
    HOLFileSys.closeDir dir; r
  end

fun listDir dirName =
  filter (not o String.isPrefix ".") (listDir_all dirName)

(* ------------------------------------------------------------------------
   Profiling
   ------------------------------------------------------------------------ *)

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

(* ------------------------------------------------------------------------
   String
   ------------------------------------------------------------------------ *)

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

fun subst_sl (s1,s2) sl =
  let fun f x = if x = s1 then s2 else x in map f sl end

fun rpt_split_sl s sl =
  let val (a,b) = split_sl s sl handle _ => (sl,[])
  in
    if null b then [a] else a :: rpt_split_sl s b
  end

fun split_level_aux parl s pl sl = case sl of
    []     => raise ERR "split_level_aux"
      ("delim: " ^ s ^ ", parl: " ^ String.concatWith " " parl)
  | a :: m => if a = s andalso null parl
                then (rev pl, m)
              else if mem a ["let","local","struct","(","[","{"]
                then split_level_aux (a :: parl) s (a :: pl) m
              else if mem a ["end",")","]","}"]
                then split_level_aux (tl parl) s (a :: pl) m
              else split_level_aux parl s (a :: pl) m

fun split_level s sl = split_level_aux [] s [] sl

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

(* ------------------------------------------------------------------------
   Escape
   ------------------------------------------------------------------------ *)

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

fun random_int (a,b) =
  if a > b then raise ERR "random_int" "" else
  if a = b then a else
  let
    val (ar,br) = (Real.fromInt a, Real.fromInt b)
    val c = Real.floor (ar + random_real () * (br - ar + 1.0))
  in
    if c >= b then b else c
  end

fun random_elem l =
  if null l then raise ERR "random_elem" "empty" else
    List.nth (l, random_int (0, length l - 1))

fun random_subset n l = first_n n (shuffle l)

(* ------------------------------------------------------------------------
   Distribution
   ------------------------------------------------------------------------ *)

fun cumul_proba (tot:real) l = case l of
    [] => []
  | (mv,p) :: m => (mv, tot + p) :: cumul_proba (tot + p) m

fun find_cumul proba cumul = case cumul of
    []  => raise ERR "find_cumul" ""
  | [a] => fst a
  | (mv,p) :: m => if proba < (p:real) then mv else find_cumul proba m

fun mk_cumul l =
  let
    val l' = cumul_proba 0.0 l
    val (_,tot) = last l'
  in
    (l',tot)
  end

fun select_in_cumul (l,tot) =
  find_cumul (random_real () * tot) l

fun select_in_distrib l =
  let
    val l' = cumul_proba 0.0 l
    val (_,tot) = last l'
  in
    select_in_cumul (l',tot)
  end

fun select_in_distrib_seeded r l =
  let
    val l' = cumul_proba 0.0 l
    val (_,tot) = last l'
  in
    find_cumul (r * tot) l'
  end

fun best_in_distrib distrib =
  let fun cmp (a,b) = Real.compare (snd b,snd a) in
    fst (hd (dict_sort cmp distrib))
  end

val epsilon = 0.000000001

fun uniform_proba n = List.tabulate (n, fn _ => 1.0 / Real.fromInt n)

fun normalize_proba l =
  let val sum = sum_real l in
    if sum <= epsilon
    then uniform_proba (length l)
    else map (fn x => x / sum) l
  end

fun uniform_distrib l =
  let val sum = Real.fromInt (length l) in
    map_assoc (fn _ => 1.0 / sum) l
  end

fun normalize_distrib dis =
  let val sum = sum_real (map snd dis) in
    if sum <= epsilon
    then uniform_distrib (map fst dis)
    else map_snd (fn x => x / sum) dis
  end

(* --------------------------------------------------------------------------
   Dirichlet noise
   ------------------------------------------------------------------------- *)

val gammadict = dnew Real.compare
  [(0.01, 99.43258512),(0.02, 49.44221016),(0.03, 32.78499835),
   (0.04, 24.46095502),(0.05, 19.47008531),(0.06, 16.14572749),
   (0.07, 13.77360061),(0.08, 11.99656638),(0.09, 10.61621654),
   (0.1, 9.513507699),(0.2, 4.590843712),(0.3, 2.991568988),
   (0.4, 2.218159544),(0.5, 1.772453851),(0.6, 1.489192249),
   (0.7, 1.298055333),(0.8, 1.164229714),(0.9, 1.068628702)]

fun gamma_of alpha = dfind alpha gammadict
  handle NotFound => raise ERR "gamma_of" (rts alpha)

fun gamma_density alpha x =
  (Math.pow (x, alpha - 1.0) * Math.exp (~ x)) / gamma_of alpha

fun gamma_distrib alpha =
  map_assoc (gamma_density alpha) (interval 0.01 (0.01,10.0));

fun gamma_noise_gen alpha =
  let
    val distrib = gamma_distrib alpha
    val cumul = mk_cumul distrib
  in
    fn () => select_in_cumul cumul
  end



(* ------------------------------------------------------------------------
   Theories of the standard library (sigobj)
   ------------------------------------------------------------------------ *)

fun sigobj_theories () =
  let
    val ttt_code_dir = HOLDIR ^ "/src/tactictoe/code"
    val _    = mkDir_err ttt_code_dir
    val file = ttt_code_dir ^ "/theory_list"
    val sigdir = HOLDIR ^ "/sigobj"
    val cmd0 = "cd " ^ sigdir
    val cmd1 = "readlink -f $(find -regex \".*[^/]Theory.sig\") > " ^ file
  in
    ignore (OS.Process.system (cmd0 ^ "; " ^ cmd1 ^ "; "));
    readl file
  end

fun load_sigobj () =
  let
    fun barefile file = OS.Path.base (OS.Path.file file)
    val l0 = sigobj_theories ()
    val l1 = map barefile l0
  in
    app load l1
  end

fun link_sigobj file =
  let
    val base = OS.Path.base file
    val link = HOLDIR ^ "/sigobj/" ^ OS.Path.base (OS.Path.file file)
    fun f ext = "ln -sf " ^ base ^ "." ^ ext ^ " " ^ link ^ "." ^ ext ^ ";"
    val l = map f ["sig","uo","ui"]
    val cmd = String.concatWith " " l
  in
    ignore (OS.Process.system cmd)
  end


end (* struct *)
