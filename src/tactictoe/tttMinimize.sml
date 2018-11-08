(* ========================================================================== *)
(* FILE          : tttMinimize.sml                                            *)
(* DESCRIPTION   : Minimize proof script including minimization               *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure tttMinimize :> tttMinimize =
struct

open HolKernel boolLib Abbrev tttTools tttExec tttLexer tttTimeout tttSetup

val ERR = mk_HOL_ERR "tttMinimize"

(* --------------------------------------------------------------------------
   Tests
   -------------------------------------------------------------------------- *)

fun same_effect tim stac1 stac2 g =
  let
    val gl1o = rec_stac tim stac1 g
    val gl2o = rec_stac tim stac2 g
  in
    gl1o <> NONE andalso gl2o <> NONE andalso gl1o = gl2o
  end

fun is_proof stac g = (rec_sproof stac g = SOME [])

fun is_effect tim stac g gl = (rec_stac tim stac g = SOME gl)

(*---------------------------------------------------------------------------
  Removing unnecessary parentheses
  ----------------------------------------------------------------------------*)

fun rm_par sl = case sl of
    [] => []
  | ["(",a,")"] => [a]
  | ["(","(",a,")",")"] => [a]
  | "(" :: a :: ")" :: m => a :: rm_par m
  | "(" :: "(" :: a :: ")" :: ")" :: m => a :: rm_par m
  | a :: m => a :: rm_par m

(*----------------------------------------------------------------------------
  Minimizing the space between parentheses
  ----------------------------------------------------------------------------*)

fun minspace_sl sl = case sl of
    [] =>  ""
  | [a] => a
  | a :: b :: m =>
    (
    if mem a ["[","("] orelse mem b ["]",")",",",";"]
      then a ^ minspace_sl (b :: m)
      else a ^ " " ^ minspace_sl (b :: m)
    )

(*----------------------------------------------------------------------------
  Remove infix guards
  ----------------------------------------------------------------------------*)

fun is_infix_open s =
  String.isPrefix "ttt_infix" s andalso
  String.isSuffix "open" s

fun is_infix_close s =
  String.isPrefix "ttt_infix" s andalso
  String.isSuffix "close" s

fun rm_infix sl = case sl of
    [] => []
  | a :: b :: c :: m =>
    if is_infix_open a andalso is_infix_close c
    then b :: rm_infix m
    else a :: rm_infix (b :: c :: m)
  | a :: m => a :: rm_infix m

(*----------------------------------------------------------------------------
  Removing module declaration
  ----------------------------------------------------------------------------*)

fun rm_prefix sl =
  let
    fun rm_one_prefix s =
      let
        val l = String.tokens (fn x => x = #".") s
        val s' = last l
      in
        if List.length l = 1 orelse not (is_pointer_eq s s')
        then s
        else s'
      end
  in
    map rm_one_prefix sl
  end

(*----------------------------------------------------------------------------
  Remove DB.fetch
  ----------------------------------------------------------------------------*)

fun rm_dbfetch sl = case sl of
    [] => []
  | ["DB.fetch",a,b] =>
    ((
    if unquote_string a = current_theory ()
    then ["DB.fetch",a,b]
    else [unquote_string a ^ "Theory." ^ unquote_string b]
    )
    handle _ => ["DB.fetch",a,b])
  | "DB.fetch" :: a :: b :: m =>
    ((
    if unquote_string a = current_theory ()
    then ["DB.fetch",a,b]
    else [unquote_string a ^ "Theory." ^ unquote_string b]
    )
    handle _ => ["DB.fetch",a,b])
    @
    rm_dbfetch m
  | a :: m => a :: rm_dbfetch m

(*----------------------------------------------------------------------------
  Prettification of a string tactic.
  ----------------------------------------------------------------------------*)

fun prettify1_stac stac =
  (minspace_sl o rm_infix o rm_prefix o rm_par o rm_dbfetch)
    (ttt_lex stac)

fun prettify2_stac stac =
  (minspace_sl o ttt_lex) stac

(*----------------------------------------------------------------------------
  Externalizing local declaration
  ----------------------------------------------------------------------------*)

fun find_local_aux loc_acc acc sl = case sl of
    [] => (rev loc_acc, rev acc)
  | "let" :: m =>
    let
      val (decl,cont0) = split_level "in" m
      val (body,cont1) = split_level "end" cont0
    in
      if length body <> 1
      then raise ERR "find_local" ""
      else find_local_aux (decl :: loc_acc) (hd body :: acc) cont1
    end
  | a :: m => find_local_aux loc_acc (a :: acc) m

fun find_local stac = find_local_aux [] [] (ttt_lex stac)

(*----------------------------------------------------------------------------
  Prettifying proofs
  ----------------------------------------------------------------------------*)

datatype Proof =
    Tactic of (string * goal)
  | Then   of (Proof * Proof)
  | Thenl  of (Proof * Proof list)

fun pretty_allstac tim proof = case proof of
    Tactic (s,g) =>
    let val (s1,s2) = (prettify1_stac s, prettify2_stac s) in
      if same_effect tim s s1 g then Tactic (s1,g) else Tactic (s2,g)
    end
  | Then (p1,p2) => Then (pretty_allstac tim p1, pretty_allstac tim p2)
  | Thenl (p,pl) => Thenl (pretty_allstac tim p, map (pretty_allstac tim) pl)

(*----------------------------------------------------------------------------
  Printing proofs and extracting local declarations
  ----------------------------------------------------------------------------*)

fun string_of_proof proof =
  let
    val decll_ref = ref []
    fun loop proof = case proof of
      Tactic (s,_) =>
        let val (decll,news) = find_local s in
          decll_ref := decll @ (!decll_ref);
          minspace_sl news
        end
    | Then (p1,p2) => loop p1 ^ " THEN\n  " ^ loop p2
    | Thenl (p,pl) =>
      let
        val sl = map loop pl
        val set = mk_fast_set String.compare sl
      in
        if length set = 1
        then loop p ^ " THEN\n  " ^ hd set
        else loop p ^ " THENL\n  [" ^ String.concatWith ",\n  " sl ^ "]"
      end
    val body = loop proof
    val decll = mk_fast_set (list_compare String.compare) (!decll_ref)
    val decls = map (String.concatWith " ") decll
  in
    if null decls
    then body
    else "let\n  " ^
         String.concatWith "\n  " decls ^ "\nin\n  " ^ body ^ "\nend"
  end

fun safestring_of_proof proof = case proof of
    Tactic (s,_) => "(" ^ s ^ ")"
  | Then (p1,p2) => string_of_proof p1 ^ " THEN " ^ string_of_proof p2
  | Thenl (p,pl) =>
    let
      val sl = map string_of_proof pl
      val set = mk_fast_set String.compare sl
    in
      if length set = 1
      then string_of_proof p ^ " THEN " ^ "(" ^ hd set ^ ")"
      else string_of_proof p ^ " THENL " ^
        "[" ^ String.concatWith ", " sl ^ "]"
    end

(*----------------------------------------------------------------------------
  Minimizing lists
  ----------------------------------------------------------------------------*)

fun decompose sl = case sl of
    [] => []
  | "[" :: m =>
    let
      val (body,cont) = split_level "]" m
      val l = map (String.concatWith " ") (rpt_split_level "," body)
    in
      (true, ([],l)) :: decompose cont
    end
  | a :: m => (false, ([],[a])) :: decompose m

fun list_to_string sl = "[ " ^ String.concatWith " , " sl ^ " ]"

fun group_to_string l =
  let fun to_string (b,(l1',l2')) =
    if b then list_to_string (l1' @ l2') else hd l2'
  in
    String.concatWith " " (map to_string l)
  end

fun mini_stac tim g gl pl l = case l of
    [] => group_to_string pl
  | (false,a) :: m => mini_stac tim g gl (pl @ [(false,a)]) m
  | (true,(l1,l2)) :: m =>
    if null l2
    then mini_stac tim g gl (pl @ [(true,(l1,l2))]) m
    else
      let val new_stac = group_to_string  (pl @ [(true, (l1, tl l2))] @ m) in
        if is_effect tim new_stac g gl
        then mini_stac tim g gl pl ((true, (l1, tl l2)) :: m)
        else mini_stac tim g gl pl ((true, (l1 @ [hd l2], tl l2)) :: m)
      end

fun mini_stac_g_gl tim stac g gl =
  mini_stac tim g gl [] (decompose (ttt_lex stac))

(*----------------------------------------------------------------------------
  Minimizing lists in all tactics of a proof
  ----------------------------------------------------------------------------*)

fun mini_proofstac stac g =
  let
    val gl = fst (tactic_of_sml stac g)
      handle _ => (debug "Error: minimize"; raise ERR "minimize" stac)
    val tim = Real.max (!ttt_tactic_time, !ttt_metis_time)
  in
    mini_stac tim g gl [] (decompose (ttt_lex stac))
  end

fun mini_allstac proof = case proof of
    Tactic (s,g) => Tactic (mini_proofstac s g,g)
  | Then (p1,p2) => Then (mini_allstac p1, mini_allstac p2)
  | Thenl (p,pl) => Thenl (mini_allstac p, map mini_allstac pl)

(*----------------------------------------------------------------------------
  Trivial proof minimization
  ----------------------------------------------------------------------------*)
(* could be replaced by minimization search,
   favorising breadth first, with a high exploration coefficient *)
fun mini_proof proof = case proof of
    Tactic _ => proof
  | Then (Tactic (_,g),p2) =>
    let val s = string_of_proof p2 in
      if is_proof s g then p2 else proof
    end
  | Then (p1,p2) => Then (mini_proof p1, mini_proof p2)
  | Thenl (p,pl) => Thenl (mini_proof p, map mini_proof pl)

fun mini_proof_wrap p =
  if !ttt_minimize_flag then
    let
      val _ = debug "Starting minimization"
      val newp = mini_proof (mini_allstac p)
      val _ ="End minimization"
    in
      newp
    end
  else p

(*----------------------------------------------------------------------------
  Combining minimization and prettification.
  ----------------------------------------------------------------------------*)

fun minimize_stac tim stac g gl = prettify1_stac (mini_stac_g_gl tim stac g gl)

fun pretty_proof_wrap p =
  if !ttt_prettify_flag then
    let
      val _ = debug "Starting prettification"
      val tim = Real.max (!ttt_tactic_time, !ttt_metis_time)
      val newp = pretty_allstac tim p
      val _ = debug "End prettification"
    in
      newp
    end
  else p

fun minimize_proof p = 
  (pretty_proof_wrap o mini_proof_wrap) p
  handle _ => 
    (debug "Error: prettification or minimization failed"; p)

(*----------------------------------------------------------------------------
  Reconstructing the proof.
  ----------------------------------------------------------------------------*)

fun proof_length proof = case proof of
  Tactic (s,g) => 1
| Then (p1,p2) => proof_length p1 + proof_length p2
| Thenl (p,pl) => proof_length p + sum_int (map proof_length pl)

fun reconstruct_aux g proof sproof =
  let
    val tim    = Time.toReal (!ttt_search_time)
    val tac    = tactic_of_sml sproof handle _ => NO_TAC
    val new_tim = snd (add_time (timeOut tim Tactical.TAC_PROOF) (g,tac))
      handle _ => (debug ("Warning: reconstruct: " ^ sproof); tim)
  in
    debug_proof ("proof length: " ^ int_to_string (proof_length proof));
    debug_proof ("proof time: " ^ Real.toString new_tim);
    sproof
  end

fun requote sl = case sl of
   [] => []
  | "[" :: "QUOTE" :: s :: "]" :: m =>
    if tttTools.is_string s
    then ("`" ^ rm_space (rm_comment (rm_squote s)) ^ "`") :: requote m
    else hd sl :: requote (tl sl)
  | "Term" :: "[" :: "QUOTE" :: s :: "]" :: m =>
    if tttTools.is_string s
    then ("``" ^ rm_space (rm_comment (rm_squote s)) ^ "``") :: requote m
    else hd sl :: requote (tl sl)
  | a :: m => a :: requote m

fun requote_sproof s = (minspace_sl o requote o ttt_lex) s

fun unsafe_reconstruct g proof =
  reconstruct_aux g proof (requote_sproof (string_of_proof proof))

fun safe_reconstruct g proof =
  reconstruct_aux g proof (safestring_of_proof proof)

fun reconstruct g proof =
  (
  if !ttt_prettify_flag
  then (unsafe_reconstruct g proof handle _ => safe_reconstruct g proof)
  else safe_reconstruct g proof
  )
  handle _ => 
    (debug ("Error: reconstruction failed" ^ string_of_proof proof);
     string_of_proof proof)
   
end (* struct *)
