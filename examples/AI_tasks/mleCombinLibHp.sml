(* ========================================================================= *)
(* FILE          : mleCombinLibHp.sml                                        *)
(* DESCRIPTION   : Tools for term synthesis on combinator datatype           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mleCombinLibHp :> mleCombinLibHp =
struct

open HolKernel Abbrev boolLib aiLib numTheory arithmeticTheory 
mleCombinLib hhExportFof

val ERR = mk_HOL_ERR "mleCombinLibHp"
val selfdir = HOLDIR ^ "/examples/AI_tasks"

(* -------------------------------------------------------------------------
   Position
   ------------------------------------------------------------------------- *)

datatype pose = Left | Right

fun pose_compare (a,b) = case (a,b) of
    (Left,Right) => LESS
  | (Right,Left) => GREATER
  | _ => EQUAL

fun pose_to_string pose = case pose of 
    Left => "L"
  | Right => "R"

fun string_to_pose s = 
  if s = "L" then Left else if s = "R" then Right else 
    raise ERR "string_to_pose" ""

fun pos_to_string pos = String.concatWith " " (map pose_to_string pos)
fun string_to_pos s = 
  map string_to_pose (String.tokens Char.isSpace s)

val pos_compare = list_compare pose_compare

(* -------------------------------------------------------------------------
   Combinators
   ------------------------------------------------------------------------- *)

datatype combin = V1 | V2 | V3 | S | K | A of combin * combin 

fun combin_size combin = case combin of
    A (c1,c2) => combin_size c1 + combin_size c2
  | _ => 1

(* -------------------------------------------------------------------------
   Printing combinators
   ------------------------------------------------------------------------- *)

fun strip_A_aux c = case c of
    A (c1,c2) => c2 :: strip_A_aux c1
  | _ => [c]
fun strip_A c = rev (strip_A_aux c)

fun list_mk_A_aux l = case l of
    [] => raise ERR "list_mk_A" ""
  | [c] => c
  | a :: m => A(list_mk_A_aux m,a)

fun list_mk_A l = list_mk_A_aux (rev l)

fun combin_to_string c = case c of 
    S => "S"
  | K => "K"
  | V1 => "V1"
  | V2 => "V2"
  | V3 => "V3"
  | A _ => "(" ^ String.concatWith " " (map combin_to_string (strip_A c)) ^ ")"

fun string_to_combin s = 
  let 
    val s' = if mem s ["S","K","V1","V2","V3"] then "(" ^ s ^ ")" else s
    val sexp = singleton_of_list (lisp_parser s')
    val assocl = map swap (map_assoc combin_to_string [S,K,V1,V2,V3])
    fun parse sexp = case sexp of
      Lterm l => list_mk_A (map parse l)
    | Lstring s => assoc s assocl
  in
    parse sexp
  end
 
fun combin_compare (c1,c2) = case (c1,c2) of
    (A x, A y) => cpl_compare combin_compare combin_compare (x,y)
  | (_, A _) => LESS
  | (A _,_) => GREATER
  | _ => String.compare (combin_to_string c1, combin_to_string c2)

(* -------------------------------------------------------------------------
   Rewriting combinators
   ------------------------------------------------------------------------- *)

fun next_pos_aux l = case l of
    [] => raise ERR "next_pos" ""
  | Left :: m => Right :: m
  | Right :: m => next_pos_aux m

fun next_pos l = rev (next_pos_aux (rev l))

exception Break

fun hp_nf c = case c of
    A(A(A(S,x),y),z) => false
  | A(A(K,x),y) => false
  | A(c1,c2) => hp_nf c1 andalso hp_nf c2
  | _ => true

fun hp_norm n mainc =
  let
    val i = ref 0
    fun incra c = (incr i; if (combin_size c > 100 orelse !i > n) 
                           then raise Break else ())   
    fun hp_norm_aux n c = 
      case c of
        A(A(A(S,x),y),z) => (incra c; hp_norm_aux n (A(A(x,z),A(y,z))) )  
      | A(A(K,x),y) => (incra c; hp_norm_aux n x)
      | A(c1,c2) => A(hp_norm_aux n c1, hp_norm_aux n c2)  
      | x => x
    fun loop c =
      if hp_nf c then SOME c else loop (hp_norm_aux n c)
  in
    loop mainc handle Break => NONE
  end

(* -------------------------------------------------------------------------
   Generating combinators
   ------------------------------------------------------------------------- *)

fun cterm_to_hp cterm = 
  if term_eq cterm cS then S 
  else if term_eq cterm cK then K
  else if term_eq cterm v1 then V1
  else if term_eq cterm v2 then V2
  else if term_eq cterm v3 then V3
  else let val (a,b) = dest_cA cterm in A (cterm_to_hp a, cterm_to_hp b) end

fun hp_to_cterm c = case c of 
   S => cS | K => cK | V1 => v1 | V2 => v2 | V3 => v3 |
   A (c1,c2) => mk_cA (hp_to_cterm c1, hp_to_cterm c2)

fun contains_sk c = case c of
    S => true
  | K => true
  | V1 => false
  | V2 => false
  | V3 => false
  | A (c1,c2) => contains_sk c1 orelse contains_sk c2

fun has_bigarity c =
  let val argl = tl (strip_A c) in
    length argl > 4 orelse exists has_bigarity argl
  end

fun compare_csize (a,b) = Int.compare (combin_size a, combin_size b)
fun smallest_csize l = hd (dict_sort compare_csize l)

fun gen_headnf_aux n nmax d =
  if dlength d >= nmax then (d,n) else
  let 
    val c = cterm_to_hp (random_nf (random_int (1,20)))
    val cnorm = valOf (hp_norm 100 (A(A(A(c,V1),V2),V3))) handle Option => K 
  in
    if contains_sk cnorm orelse 
       combin_size cnorm > 20 orelse 
       has_bigarity cnorm
    then gen_headnf_aux (n+1) nmax d 
    else if dmem cnorm d then
      let val oldc = dfind cnorm d in
        if compare_csize (c,oldc) = LESS 
        then gen_headnf_aux (n+1) nmax (dadd cnorm c d) 
        else gen_headnf_aux (n+1) nmax d
      end
    else 
      (print_endline (its (dlength d + 1)); 
       gen_headnf_aux (n+1) nmax (dadd cnorm c d))
  end

fun gen_headnf nmax d = gen_headnf_aux 0 nmax d

(* -------------------------------------------------------------------------
   Export
   ------------------------------------------------------------------------- *)

val targetdir = selfdir ^ "/combin_target"

fun distrib_il il = 
  let 
    val l = dlist (count_dict (dempty Int.compare) il)
    fun f (i,j) = its i ^ "-" ^ its j
  in
    String.concatWith " " (map f l)
  end

fun export_data (train,test) =
  let 
    val l = train @ test
    val _ = mkDir_err targetdir
    fun f1 (headnf,witness) = 
      "headnf: " ^ combin_to_string headnf ^
      "\ncombin: " ^ combin_to_string witness 
    val il1 = map (combin_size o fst) l
    val il2 = map (combin_size o snd) l
    val train_sorted = 
      dict_sort (cpl_compare combin_compare combin_compare) train
    val test_sorted = 
      dict_sort (cpl_compare combin_compare combin_compare) test
  in
    writel (targetdir ^ "/train_export") (map f1 train_sorted);
    writel (targetdir ^ "/test_export") (map f1 test_sorted);
    writel (targetdir ^ "/distrib-headnf") [distrib_il il1];
    writel (targetdir ^ "/distrib-witness") [distrib_il il2]
  end

fun import_data file =
  let 
    val sl = readl (targetdir ^ "/" ^ file)
    val l = map pair_of_list (mk_batch 2 sl) 
    fun f (a,b) = 
      (
      string_to_combin (snd (split_string "headnf: " a)), 
      string_to_combin (snd (split_string "combin: " b))
      )
  in
    map f l
  end

(* -------------------------------------------------------------------------
   TPTP Export
   ------------------------------------------------------------------------- *)

fun goal_of_headnf headnf =
  let 
    val vc = mk_var ("Vc",alpha)
    val tm =
    mk_exists (vc, (list_mk_forall ([v1,v2,v3], 
      mk_eq (list_mk_cA [vc,v1,v2,v3],hp_to_cterm headnf))))
  in
    (eq_axl,tm)
  end

fun export_goal dir (goal,n) =
  let 
    val tptp_dir = HOLDIR ^ "/examples/AI_tasks/TPTP"
    val _ = mkDir_err tptp_dir
    val file = tptp_dir ^ "/" ^ dir ^ "/i/" ^ its n ^ ".p"
    val _ = mkDir_err (tptp_dir ^ "/" ^ dir)
    val _ = mkDir_err (tptp_dir ^ "/" ^ dir ^ "/i")
    val _ = mkDir_err (tptp_dir ^ "/" ^ dir ^ "/eprover")
    val _ = mkDir_err (tptp_dir ^ "/" ^ dir ^ "/vampire")
    val _ = mkDir_err (tptp_dir ^ "/" ^ dir ^ "/eprover_schedule")
    val _ = mkDir_err (tptp_dir ^ "/" ^ dir ^ "/vampire_casc")
  in
    name_flag := false;
    type_flag := false;
    p_flag := false;
    fof_export_goal file goal
  end

(* 
load "aiLib"; open aiLib;
load "mleCombinLibHp"; open mleCombinLibHp;
val data = import_data "test_export";
val gl = map (goal_of_headnf o fst) data;
app (export_goal "combin_test") (number_snd 0 gl);

val data = import_data "train_export";
val gl = map (goal_of_headnf o fst) data;
app (export_goal "combin_train") (number_snd 0 gl);
*)



end (* struct *)

