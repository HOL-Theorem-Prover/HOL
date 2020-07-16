(* ========================================================================= *)
(* FILE          : psMinimize.sml                                            *)
(* DESCRIPTION   : Minimize and prettify tactical proofs                     *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure psMinimize :> psMinimize =
struct

open HolKernel Abbrev boolLib aiLib
  smlExecute smlLexer smlTimeout smlPrettify

val ERR = mk_HOL_ERR "psMinimize"

val mini_proof_time = ref 20.0
val mini_tactic_time = ref 0.2

(* -------------------------------------------------------------------------
   Tests
   ------------------------------------------------------------------------- *)

val glopt_eq = option_eq (list_eq goal_eq)

fun same_effect tim stac1 stac2 g =
  let
    val gl1o = app_stac tim stac1 g
    val gl2o = app_stac tim stac2 g
  in
    not (glopt_eq gl1o NONE) andalso not (glopt_eq gl2o NONE) andalso
    glopt_eq gl1o gl2o
  end

fun is_proof tim stac g = glopt_eq (app_stac stac tim g) (SOME [])
fun has_effect tim stac g gl = glopt_eq (app_stac tim stac g) (SOME gl)

(* -------------------------------------------------------------------------
   Pretty tactic string
   ------------------------------------------------------------------------- *)

fun unsafe_prettify_stac stac =
  (smart_space o elim_infix o elim_struct o elim_par o
   elim_dbfetch o partial_sml_lexer)
  stac

fun safe_prettify_stac stac = (smart_space o partial_sml_lexer) stac

(* -------------------------------------------------------------------------
   Pretty proof steps
   ------------------------------------------------------------------------- *)

datatype Proof =
    Tactic of (string * goal)
  | Then   of (Proof * Proof)
  | Thenl  of (Proof * Proof list)

fun pretty_allstac tim proof = case proof of
    Tactic (s,g) =>
    let val (s1,s2) = (unsafe_prettify_stac s, safe_prettify_stac s) in
      if same_effect tim s s1 g then Tactic (s1,g) else Tactic (s2,g)
    end
  | Then (p1,p2) => Then (pretty_allstac tim p1, pretty_allstac tim p2)
  | Thenl (p,pl) => Thenl (pretty_allstac tim p, map (pretty_allstac tim) pl)

(* -------------------------------------------------------------------------
   Externalizing local declaration
   ------------------------------------------------------------------------- *)

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

fun find_local stac = find_local_aux [] [] (partial_sml_lexer stac)

fun unsafe_prettify_proof proof =
  let
    val decll_ref = ref []
    fun loop proof = case proof of
      Tactic (s,_) =>
        let val (decll,news) = find_local s in
          decll_ref := decll @ (!decll_ref);
          smart_space news
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

fun safe_prettify_proof proof = case proof of
    Tactic (s,_) => "(" ^ s ^ ")"
  | Then (p1,p2) => safe_prettify_proof p1 ^ " THEN " ^ safe_prettify_proof p2
  | Thenl (p,pl) =>
    let
      val sl = map safe_prettify_proof pl
      val set = mk_fast_set String.compare sl
    in
      if length set = 1
      then safe_prettify_proof p ^ " THEN " ^ "(" ^ hd set ^ ")"
      else safe_prettify_proof p ^ " THENL " ^
        "[" ^ String.concatWith ", " sl ^ "]"
    end

(*---------------------------------------------------------------------------
  Minimizing lists in one tactic
  ---------------------------------------------------------------------------*)

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

fun mini_stac_aux tim g gl pl l = case l of
    [] => group_to_string pl
  | (false,a) :: m => mini_stac_aux tim g gl (pl @ [(false,a)]) m
  | (true,(l1,l2)) :: m =>
    if null l2
    then mini_stac_aux tim g gl (pl @ [(true,(l1,l2))]) m
    else
      let val new_stac = group_to_string  (pl @ [(true, (l1, tl l2))] @ m) in
        if has_effect tim new_stac g gl
        then mini_stac_aux tim g gl pl ((true, (l1, tl l2)) :: m)
        else mini_stac_aux tim g gl pl ((true, (l1 @ [hd l2], tl l2)) :: m)
      end

fun mini_stac stac g =
  let
    val gl = fst (tactic_of_sml (!mini_tactic_time) stac g)
      handle Interrupt => raise Interrupt
      | _ => (debug "Error: minimize"; raise ERR "minimize" stac)
    val l = decompose (partial_sml_lexer stac)
  in
    mini_stac_aux (!mini_tactic_time) g gl [] l
  end

(*---------------------------------------------------------------------------
  Minimizing lists in all tactics of a proof
  ---------------------------------------------------------------------------*)

fun mini_allstac proof = case proof of
    Tactic (s,g) => Tactic (mini_stac s g,g)
  | Then (p1,p2) => Then (mini_allstac p1, mini_allstac p2)
  | Thenl (p,pl) => Thenl (mini_allstac p, map mini_allstac pl)

(*---------------------------------------------------------------------------
  Trivial proof minimization
  ---------------------------------------------------------------------------*)

fun mini_proof proof = case proof of
    Tactic _ => proof
  | Then (Tactic (_,g),p2) =>
    let val s = safe_prettify_proof p2 in
      if is_proof s (!mini_proof_time) g then p2 else proof
    end
  | Then (p1,p2) => Then (mini_proof p1, mini_proof p2)
  | Thenl (p,pl) => Thenl (mini_proof p, map mini_proof pl)

(*---------------------------------------------------------------------------
  Combining minimization and prettification.
  ---------------------------------------------------------------------------*)

(* tactic (used by holyhammer) *)
fun minimize_stac tim stac g gl =
  let val newstac =
    mini_stac_aux tim g gl [] (decompose (partial_sml_lexer stac))
  in
    unsafe_prettify_stac newstac
  end

(* proof *)
fun minimize_proof p =
  (pretty_allstac (!mini_tactic_time) o mini_proof o mini_allstac) p
  handle Interrupt => raise Interrupt
   | _ => (debug "Error: prettification or minimization failed"; p)

(*---------------------------------------------------------------------------
  Reconstructing the proof.
  ---------------------------------------------------------------------------*)

fun proof_length proof = case proof of
    Tactic (s,g) => 1
  | Then (p1,p2) => proof_length p1 + proof_length p2
  | Thenl (p,pl) => proof_length p + sum_int (map proof_length pl)

fun reconstruct_aux g proof sproof =
  let
    val tac = tactic_of_sml (!mini_proof_time) sproof
      handle Interrupt => raise Interrupt | _ => NO_TAC
    val new_tim =
      snd (add_time (timeout (!mini_proof_time) Tactical.TAC_PROOF) (g,tac))
      handle Interrupt => raise Interrupt | _ => (!mini_proof_time)
  in
    debugf "proof length: " int_to_string (proof_length proof);
    debugf "proof time: " Real.toString new_tim;
    sproof
  end

fun requote_sproof s = (smart_space o requote o partial_sml_lexer) s

fun unsafe_reconstruct g proof =
  reconstruct_aux g proof (requote_sproof (unsafe_prettify_proof proof))

fun safe_reconstruct g proof =
  reconstruct_aux g proof (safe_prettify_proof proof)

fun reconstruct g proof =
  (
  unsafe_reconstruct g proof
  handle Interrupt => raise Interrupt | _ => safe_reconstruct g proof
  )
  handle Interrupt => raise Interrupt | _ => safe_prettify_proof proof


end (* struct *)
