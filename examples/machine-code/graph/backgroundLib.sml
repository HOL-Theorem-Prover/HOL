structure backgroundLib :> backgroundLib =
struct

open HolKernel boolLib bossLib Parse;
open helperLib;
open GraphLangTheory

val _ = set_echo 5;

fun the (SOME x) = x | the NONE = fail()

fun try_map f [] = []
  | try_map f (x::xs) = let val y = f x in y :: try_map f xs end
                        handle Interrupt => raise Interrupt
                             | _ => try_map f xs

fun max (x,y) = if x < y then y else x;

fun drop_until p [] = []
  | drop_until p (x::xs) = if p x then x::xs else drop_until p xs

fun take_until p [] = []
  | take_until p (x::xs) = if p x then [] else x::take_until p xs

fun every p [] = true
  | every p (x::xs) = p x andalso every p xs

fun subset xs ys = every (fn x => mem x ys) xs

fun diff xs ys = filter (fn x => not (mem x ys)) xs

fun append_lists [] = []
  | append_lists (x::xs) = x @ append_lists xs

fun take n [] = []
  | take n (x::xs) = if n = 0 then [] else x :: take (n-1) xs

fun drop n [] = []
  | drop n (x::xs) = if n = 0 then x::xs else drop (n-1) xs

val sum = foldl (op +) 0

fun lines_from_file filename = let
  val _ = echo 1 ("  Reading " ^ filename)
  val t = TextIO.openIn(filename)
  fun lines aux = case TextIO.inputLine(t) of
                    NONE => rev aux
                  | (SOME line) => lines (line::aux)
  val xs = lines []
  val _ = TextIO.closeIn(t)
  val _ = echo 1 ", done.\n"
  in xs end

fun measure_it name f x = let
  (* count inferences and record time *)
  val _ = Count.counting_thms true
  val _ = Count.reset_thm_count ()
  val start1 = Time.now()
  val y = f x
  val end1 = Time.now()
  val total1 = Count.thm_count ()
  val _ = Count.counting_thms false
  val time1 = Time.toReal ((op Time.-)(end1,start1))
  val _ = print "\n    (profiling) "
  val _ = print name
  val _ = print " "
  val _ = print (Real.toString time1)
  val _ = print " sec, "
  val _ = print (int_to_string (#total total1))
  val _ = print " prim. inf.\n"
  in y end;

fun dest_tuple tm =
  if aconv tm ``():unit`` then [] else
  let val (x,y) = pairSyntax.dest_pair tm in x :: dest_tuple y end
  handle HOL_ERR e => [tm];

fun REPLACE_CONV th tm = let
  val th = SPEC_ALL th
  val (i,j) = match_term ((fst o dest_eq o concl) th) tm
  in INST i (INST_TYPE j th) end

(* expands pairs ``(x,y,z) = f`` --> (x = FST f) /\ (y = FST (SND f)) /\ (z = ...) *)
fun expand_conv tm = let
  val cc = RAND_CONV (REPLACE_CONV (GSYM pairTheory.PAIR))
  val cc = cc THENC REPLACE_CONV pairTheory.PAIR_EQ
  val th = cc tm
  in CONV_RULE (RAND_CONV (RAND_CONV expand_conv)) th end
  handle HOL_ERR e => REFL tm

fun list_mk_pair xs = pairSyntax.list_mk_pair xs handle HOL_ERR e => ``()``
fun list_dest_pair tm = let val (x,y) = pairSyntax.dest_pair tm
 in list_dest_pair x @ list_dest_pair y end handle HOL_ERR e => [tm]

val BINOP1_CONV = RATOR_CONV o RAND_CONV

fun index_for x xs = let (* idea: el (index_for x xs) x = x *)
  fun aux k n [] = fail()
    | aux k n (x::xs) = if k = x then n else aux k (n+1) xs
  in aux x 1 xs end

(* implementation of skip_proofs *)

val skip_proofs = ref false;

fun print_error goal = let
  val _ = print "\n\nAuto proof of following failed.\n\n"
  val _ = print_term goal
  val _ = print "\n\n"
  in () end

fun auto_prove proof_name (goal,tac) =
  if !skip_proofs then prove(goal,cheat) else let
    val (rest,validation) = tac ([], goal)
    in if length rest = 0 then validation []
       else (print_error goal;
             failwith("auto_prove failed for " ^ proof_name)) end

fun auto_conv_prove proof_name goal conv =
  if !skip_proofs then prove(goal,cheat) else let
    val th = conv goal
    in if aconv (rand (concl th)) T then MATCH_MP GraphLangTheory.EQ_T th
       else (print_error goal;
             failwith("auto_conv_prove failed for " ^ proof_name)) end

(* debugging *)

fun modify_message f e =
  case e of
    HOL_ERR e => HOL_ERR (set_message (f (#message e)) e)
  | _ => e

fun report_error name e = let
  val _ = "\n\n" ^ name ^ " failed.\n\n"
  in raise (modify_message (fn s => s ^ " << " ^ name) e) end

val has_failures = ref false;

(* aconv *)

fun term_mem x [] = false
  | term_mem x (y::ys) = aconv x y orelse term_mem x ys

fun term_diff xs ys = filter (fn x => not (term_mem x ys)) xs;

fun term_intersect xs ys = filter (fn x => term_mem x ys) xs;

fun term_all_distinct [] = []
  | term_all_distinct (tm::tms) =
      tm :: filter (fn x => not (aconv tm x)) tms;

(* misc *)

fun is_inl tm = can (match_term sumSyntax.inl_tm o car) tm
fun is_inr tm = can (match_term sumSyntax.inr_tm o car) tm

fun dest_sum_type ty = let
  val (name,xs) = dest_type ty
  val _ = name = "sum" orelse fail()
  in (el 1 xs, el 2 xs) end

fun clean_name s = String.translate
  (fn c => if c = #"." then "_" else implode [c]) s

end
