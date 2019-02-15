structure PmatchHeuristics :> PmatchHeuristics =
struct

open HolKernel boolSyntax;


(*----------------------------------------------------------------------------
      Boilerplate stuff
 ----------------------------------------------------------------------------*)

type thry   = {Tyop : string, Thy : string} ->
              {case_const : term, constructors : term list} option

fun constructors_of {case_const : term, constructors : term list} = constructors

fun type_names ty =
  let val {Thy,Tyop,Args} = Type.dest_thy_type ty
  in {Thy=Thy,Tyop=Tyop}
  end;


(*----------------------------------------------------------------------------
      Various heuristics for pattern compilation
 ----------------------------------------------------------------------------*)

type pmatch_heuristic = {skip_rows : bool, collapse_cases : bool, col_fun : thry -> term list list -> int}

(* the old heuristic used by HOL 4 *)
val pheu_classic : pmatch_heuristic = { skip_rows = false, collapse_cases = false, col_fun = (fn _ => fn _ => 0) }

(* one that uses always the first column, but quits early and collapses *)
val pheu_first_col : pmatch_heuristic = { skip_rows = true, collapse_cases = true, col_fun = (fn _ => fn _ => 0) }

(* one that uses always the last column, but quits early and collapses *)
val pheu_last_col : pmatch_heuristic = { skip_rows = true, collapse_cases = true, col_fun = (fn _ => fn rowL =>
case rowL of [] => 0 | (r::_) => length r - 1) }

(* A heuristic based on ranking functions *)
fun pheu_rank (rankL : (thry -> term list -> int) list) = { skip_rows = true,
   collapse_cases = true,
   col_fun = (fn ty_info => fn rowL => let
   val colL = let
     (* assumption: rowL noteq [], and all rows have same length *)
     fun aux a rowL = if (length (hd rowL) = 0) then List.rev a else
             aux ((List.map hd rowL) :: a) (List.map tl rowL)
   in
     aux [] rowL
   end

   val ncolL = Lib.enumerate 0 colL
   fun step rank ncolL = let
     val ranked_cols = List.map (fn (i, pL) => ((i, pL), rank ty_info pL)) ncolL
     val max = List.foldl (fn ((_, r), m) => if r > m then r else m) (snd (hd ranked_cols)) (tl ranked_cols)
     val ranked_cols' = List.filter (fn (_, r) => r = max) ranked_cols
     val ncolL' = List.map fst ranked_cols'
   in
     ncolL'
   end
   fun steps [] ncolL = ncolL
     | steps _ [] = []
     | steps _ [e] = [e]
     | steps (rf :: rankL) ncolL = steps rankL (step rf ncolL)
   val ncolL' = steps rankL ncolL
in
   case ncolL' of
      [] => 0 (* something went wrong, should not happen *)
    | ((i, _) :: _) => i
end)} : pmatch_heuristic

(* ranking functions *)
fun prheu_first_row _ [] = 0
  | prheu_first_row _ (p :: _) = if (is_var p) then 0 else 1

fun prheu_first_row_constr tybase [] = 0
  | prheu_first_row_constr tybase (p :: _) = if (is_var p) then 0 else
    let val (_,ty) = strip_fun (type_of p) in
     case tybase (type_names ty) of NONE => 1 | SOME tyinfo =>
     (if (length (constructors_of tyinfo) = 1) then 0 else 1) end handle HOL_ERR _ => 0;

val prheu_constr_prefix : (thry -> term list -> int) =
  let fun aux n [] = n
        | aux n (p :: pL) = if (is_var p) then n else aux (n+1)  pL
  in (fn _ => aux 0) end

fun prheu_get_constr_set tybase pL =
  case pL of [] => NONE | p :: pL' =>
  let val (_,ty) = strip_fun (type_of p) in
  case tybase (type_names ty) of NONE => NONE | SOME tyinfo =>
  let
     val constrL = constructors_of tyinfo;
     val cL = List.map (fn p => fst (strip_comb p)) pL;
     val cL' = List.filter (fn c => op_mem same_const c constrL) cL;
     val cL'' = op_mk_set aconv cL';
  in
    SOME (cL'', constrL)
  end
  end handle HOL_ERR _ => NONE

fun prheu_get_nonvar_set pL =
  let
     val cL = List.map (fn p => fst (strip_comb p)) pL;
     val cL' = List.filter (fn c => not (is_var c)) cL;
     val cL'' = op_mk_set aconv cL';
  in
    cL''
  end

fun prheu_small_branching_factor ty_info pL =
  case prheu_get_constr_set ty_info pL of
      SOME (cL, full_constrL) =>
        (~(length cL + (if length cL = length full_constrL then 0 else 1)))
    | NONE => (~(length (prheu_get_nonvar_set pL) + 2))

fun prheu_arity ty_info pL =
  case prheu_get_constr_set ty_info pL of
     SOME (cL, full_constrL) =>
       List.foldl (fn (c, s) => s + length (fst (strip_fun (type_of c)))) 0 cL
   | NONE => 0


(* heuristics defined using ranking functions *)
val pheu_first_row = pheu_rank [prheu_first_row]
val pheu_constr_prefix = pheu_rank [prheu_constr_prefix]
val pheu_qba = pheu_rank [prheu_constr_prefix, prheu_small_branching_factor, prheu_arity]
val pheu_cqba = pheu_rank [prheu_first_row_constr, prheu_constr_prefix, prheu_small_branching_factor, prheu_arity]

(* A list of all the standard heuristics *)
val default_heuristic_list = [pheu_qba, pheu_cqba, pheu_first_row, pheu_last_col, pheu_first_col]


(*----------------------------------------------------------------------------
      Heuristic funs
 ----------------------------------------------------------------------------*)

(* run multiple heuristics and take the best result *)
type pmatch_heuristic_res_compare = (term list list * term) Lib.cmp
type pmatch_heuristic_fun = unit -> pmatch_heuristic_res_compare * (unit -> pmatch_heuristic option)


(*----------------------
  comparing the results
 -----------------------*)

fun average_tree_depth t =
let
  val (_, ts) = strip_comb t
  val ts' = tl ts
  val _ = if is_var (hd ts) andalso not (null ts') then () else fail()
  val ts'' = map (snd o strip_abs) ts'
  val ds = List.foldl (fn (t, s) => s + average_tree_depth t) 0.0 ts''
  val ds' = (ds / (real (length ts''))) + 1.0
in
  ds'
end handle Empty => 0.0
         | HOL_ERR _ => 0.0

fun lex_order (ord1 : 'a cmp) (ord2 : 'a cmp) xy =
  case ord1 xy of
     LESS => LESS
   | GREATER => GREATER
   | EQUAL => (ord2 xy handle Unordered => EQUAL)
  handle Unordered => (ord2 xy handle Unordered => EQUAL)

val pmatch_heuristic_cases_base_cmp : pmatch_heuristic_res_compare =
  fn ((patts1, case_tm1), (patts2, case_tm2)) => Int.compare (length patts1, length patts2)

fun pmatch_heuristic_size_base_cmp ((patts1, case_tm1), (patts2, case_tm2)) =
  Int.compare (term_size case_tm1, term_size case_tm2)

fun pmatch_heuristic_tree_base_cmp ((patts1, case_tm1), (patts2, case_tm2)) =
  Real.compare (average_tree_depth case_tm1, average_tree_depth case_tm2)

fun pmatch_heuristic_cases_cmp xy = lex_order pmatch_heuristic_cases_base_cmp
  (lex_order pmatch_heuristic_size_base_cmp pmatch_heuristic_tree_base_cmp) xy

fun pmatch_heuristic_size_cmp xy = lex_order pmatch_heuristic_size_base_cmp
  (lex_order pmatch_heuristic_tree_base_cmp pmatch_heuristic_cases_base_cmp) xy



(*-------------------------
  try a list of heuristics
 --------------------------*)

fun pmatch_heuristic_list min_fun l () : (pmatch_heuristic_res_compare * (unit -> pmatch_heuristic option)) = let
  val hL_ref = ref l
  fun aux () = case (!hL_ref) of
     [] => NONE
   | h::hL => (hL_ref := hL; SOME h)
in (min_fun, aux) end

val default_heuristic_fun = (pmatch_heuristic_list pmatch_heuristic_cases_cmp default_heuristic_list);
val classic_heuristic_fun = (pmatch_heuristic_list pmatch_heuristic_cases_cmp [pheu_classic]);


(*-----------------------------------
  an exhaustive search heuristic-fun
 ------------------------------------*)

fun exhaustive_heuristic_fun cmp =
let
  val heuristicL_ref = ref ([]:pmatch_heuristic list)
  fun add_heu heu = (heuristicL_ref := heu :: (!heuristicL_ref))

  fun heu (prefix : (bool * int * int) list) : pmatch_heuristic =
  let
    val current_prefix = ref prefix
    val remaining_prefix = ref prefix

    fun colfun_print thry rowL =
      case (!remaining_prefix) of
          (i :: is) => (remaining_prefix := is; i)
        | [] =>
            let
              fun all_vars n = List.all is_var (List.map
                 (fn r => List.nth (r, n)) rowL)
              fun col_fun n _ = if (all_vars n orelse
                   (List.null rowL) orelse
                   (List.length (List.hd rowL) < 2)) then
                SOME n else NONE
            in
               case (Lib.first_opt col_fun rowL) of
                 SOME r => let
                   val _ = current_prefix := (!current_prefix) @ [(false, r, 1)]
                 in
                   (false, r, 1)
                 end
               | NONE => let
                   val l = List.length (hd rowL)
                   val _ = Lib.appi (fn i => fn _ =>  add_heu (heu ((!current_prefix) @ [(true, i+1, l)]))) (tl (hd rowL))
                   val _ = current_prefix := (!current_prefix) @ [(true, 0, l)]
                 in
                   (true, 0, l)
                 end
            end

     fun colfun thry rowL = let
       val (do_it, r, l) = colfun_print thry rowL
       val _ = if do_it then (print (int_to_string (r+1)); print "/"; print (int_to_string l); print " ") else ()
     in
       r
     end
  in
    { skip_rows = true, collapse_cases = true, col_fun = colfun }
  end

  fun next_heu () =
    case (!heuristicL_ref) of
       [] => NONE
     | (h :: hs) => (print "\n"; heuristicL_ref := hs; SOME h)

  fun init () =
  let
    val _ = heuristicL_ref := [heu []]
    fun cmp' (r1, r2) = (
       print "\nCases in Result: ";
       print (int_to_string (length (fst r2)));
       print " (best so far ";
       print (int_to_string (length (fst r1)));
       print ")";
       cmp (r1, r2)
    )
  in
    (cmp', next_heu)
  end
in
  init
end

(* A manual one taking an explicit order *)
fun pheu_manual (res_input : int list) : pmatch_heuristic =
let
  fun pr ts = let
    val ts_sl = List.map (fn t => "``" ^ (Hol_pp.term_to_string t) ^ "``") ts
    val ts_s = String.concatWith ", " ts_sl
  in
    print ts_s;
    print "\n"
  end
  val res = ref res_input
  fun man_choice rowL =
    let
      val r = case (!res) of
          [] => 0
        | (i::is) =>
              let
                val _ = res := is
              in
                if (i < List.length (List.hd rowL)) then i else
                   (print ("Error, can't use "^(int_to_string i)^"\n");0)
              end
      val _ = List.map pr rowL
      val _ = print ("Using "^(int_to_string r)^"\n\n\n")
    in
      r
    end

  fun colfun thry rowL =
    if ((null rowL) orelse (length (hd rowL) < 2)) then 0 else
    let
      fun all_vars n = List.all is_var (List.map
          (fn r => List.nth (r, n)) rowL)
      fun col_fun n _ = if all_vars n then SOME n else NONE
    in
      case (Lib.first_opt col_fun rowL) of
          SOME r => r
        | NONE => man_choice rowL
    end
in
  { skip_rows = true, collapse_cases = true, col_fun = colfun }
end


(*----------------------------------------------------------------------------
      A reference to store the current heuristic_fun
 ----------------------------------------------------------------------------*)

val pmatch_heuristic = ref default_heuristic_fun
val classic = ref false
fun is_classic () = !classic

fun set_heuristic_fun heu_fun = (pmatch_heuristic := heu_fun)
fun set_heuristic_list_size heuL = set_heuristic_fun (pmatch_heuristic_list pmatch_heuristic_size_cmp heuL)
fun set_heuristic_list_cases heuL = set_heuristic_fun (pmatch_heuristic_list pmatch_heuristic_cases_cmp heuL)
fun set_heuristic heu = set_heuristic_list_cases [heu]

fun set_default_heuristic () =
   (classic := false; set_heuristic_fun default_heuristic_fun)

fun set_default_heuristic_size () =
   (classic := false; set_heuristic_list_size default_heuristic_list)

fun set_default_heuristic_cases () =
   (classic := false; set_heuristic_list_cases default_heuristic_list)

fun set_classic_heuristic () =
   (classic := true; set_heuristic_fun classic_heuristic_fun)

fun with_heuristic heu f =
   with_flag (classic, false)
      (with_flag (pmatch_heuristic,
                  pmatch_heuristic_list pmatch_heuristic_cases_cmp [heu]) f)

fun with_classic_heuristic f =
   with_flag (classic, true)
      (with_flag (pmatch_heuristic, classic_heuristic_fun) f)

fun with_manual_heuristic choices =
   with_heuristic (pheu_manual choices)

end;
