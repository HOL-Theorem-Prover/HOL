structure hhsTools :> hhsTools =
struct

open HolKernel boolLib Abbrev

val ERR = mk_HOL_ERR "hhsTools"

val tactictoe_dir   = HOLDIR ^ "/src/tactictoe"
val hhs_code_dir    = tactictoe_dir ^ "/code"
val hhs_log_dir     = tactictoe_dir ^ "/log"
val hhs_predict_dir = tactictoe_dir ^ "/predict"
val hhs_record_dir  = tactictoe_dir ^ "/record"

(* ----------------------------------------------------------------------
    Dictionaries shortcuts
   ---------------------------------------------------------------------- *)

fun dfind k m  = Redblackmap.find (m,k) 
fun drem k m   = fst (Redblackmap.remove (m,k))
fun dmem k m   = Lib.can (dfind k) m
fun dadd i v m = Redblackmap.insert (m,i,v)
val dempty     = Redblackmap.mkDict

(* ----------------------------------------------------------------------
   List
   ---------------------------------------------------------------------- *)

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

(* preserve the order of equal elements *)
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

(* ----------------------------------------------------------------------
   Reals
   ---------------------------------------------------------------------- *)

fun sum_real l = case l of 
    [] => 0.0
  | a :: m => a + sum_real m

fun average_real l = sum_real l / Real.fromInt (length l)

(* ----------------------------------------------------------------------
   Goal
   ---------------------------------------------------------------------- *)

fun goal_compare ((asm1,w1), (asm2,w2)) =
  list_compare Term.compare (w1 :: asm1, w2 :: asm2)

fun replace_endline s =
  let fun f x = if x = #"\n" then #" " else x in
    implode (map f (explode s))
  end

fun string_of_goal g =
  "[" ^ String.concatWith ", " (map (replace_endline o term_to_string) (fst g)) 
  ^ "] |- " ^
  replace_endline (term_to_string (snd g))

(* ----------------------------------------------------------------------
   I/O
   ---------------------------------------------------------------------- *)

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



end (* struct *)
