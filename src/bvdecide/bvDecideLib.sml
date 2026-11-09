structure bvDecideLib :> bvDecideLib =
struct

open HolKernel boolLib bvBlastTheory bvDecideTheory

val ERR = mk_HOL_ERR "bvDecideLib"

(* ------------------------------------------------------------------------
   Reification: the goal becomes a DAG of nodes, hash-consed, with every
   subterm outside the supported operators as a variable node.
   ------------------------------------------------------------------------ *)

fun node_con s = prim_mk_const {Thy = "bvBlast", Name = s}
val node_ty = type_of (node_con "WVar")
fun mk_num i = numSyntax.term_of_int i
fun numeral_int t = Arbnum.toInt (numSyntax.dest_numeral t)

(* nodes in reverse order, the atoms' positions, and the memo table *)
type state = {nodes : term list, n : int, wvars : (int * term) list,
              bvars : (int * term) list, memo : (term, int) Redblackmap.dict}

fun reify wty t0 =
  let
    val st = ref {nodes = [], n = 0, wvars = [], bvars = [],
                  memo = Redblackmap.mkDict Term.compare} : state ref
    fun emit t nd =
      let val {nodes, n, wvars, bvars, memo} = !st
      in st := {nodes = nd :: nodes, n = n + 1, wvars = wvars, bvars = bvars,
                memo = Redblackmap.insert (memo, t, n)};
         n end
    fun atom isw t =
      let val i = emit t (node_con (if isw then "WVar" else "BVar"))
          val {nodes, n, wvars, bvars, memo} = !st
      in st := (if isw then {nodes = nodes, n = n, wvars = (i, t) :: wvars,
                             bvars = bvars, memo = memo}
                else {nodes = nodes, n = n, wvars = wvars,
                      bvars = (i, t) :: bvars, memo = memo});
         i end
    fun memo t = Redblackmap.peek (#memo (!st), t)
    fun un c f x t =
      let val a = f x in emit t (mk_comb (node_con c, mk_num a)) end
    fun bin c f (x, y) t =
      let val a = f x val b = f y
      in emit t (list_mk_comb (node_con c, [mk_num a, mk_num b])) end
    fun shift c (x, k) t =
      if numSyntax.is_numeral k then
        let val a = word x
        in emit t (list_mk_comb (node_con c, [mk_num a, k])) end
      else atom true t
    and word t =
      if type_of t <> wty then raise ERR "reify" "words of more than one width"
      else case memo t of SOME i => i | NONE =>
      if wordsSyntax.is_word_literal t then
        emit t (mk_comb (node_con "WConst",
                         numSyntax.mk_numeral
                           (wordsSyntax.dest_word_literal t)))
      else if wordsSyntax.is_word_1comp t then un "WNot" word
        (wordsSyntax.dest_word_1comp t) t
      else if wordsSyntax.is_word_2comp t then un "WNeg" word
        (wordsSyntax.dest_word_2comp t) t
      else if wordsSyntax.is_word_and t then bin "WAnd" word
        (wordsSyntax.dest_word_and t) t
      else if wordsSyntax.is_word_or t then bin "WOr" word
        (wordsSyntax.dest_word_or t) t
      else if wordsSyntax.is_word_xor t then bin "WXor" word
        (wordsSyntax.dest_word_xor t) t
      else if wordsSyntax.is_word_add t then bin "WAdd" word
        (wordsSyntax.dest_word_add t) t
      else if wordsSyntax.is_word_lsl t then shift "WShl"
        (wordsSyntax.dest_word_lsl t) t
      else if wordsSyntax.is_word_lsr t then shift "WLsr"
        (wordsSyntax.dest_word_lsr t) t
      else if wordsSyntax.is_word_asr t then shift "WAsr"
        (wordsSyntax.dest_word_asr t) t
      else atom true t
    fun boolean t =
      case memo t of SOME i => i | NONE =>
      if Teq t then emit t (mk_comb (node_con "BConst", T))
      else if Feq t then emit t (mk_comb (node_con "BConst", F))
      else if is_neg t then un "BNot" boolean (dest_neg t) t
      else if is_conj t then bin "BAnd" boolean (dest_conj t) t
      else if is_disj t then bin "BOr" boolean (dest_disj t) t
      else if is_imp_only t then bin "BImp" boolean (dest_imp t) t
      else if is_eq t then
        let val (x, y) = dest_eq t in
          if type_of x = bool then bin "BIff" boolean (x, y) t
          else if type_of x = wty then bin "BEq" word (x, y) t
          else atom false t
        end
      else if wordsSyntax.is_word_lo t then bin "BUlt" word
        (wordsSyntax.dest_word_lo t) t
      else if fcpSyntax.is_fcp_index t then
        let val (x, k) = fcpSyntax.dest_fcp_index t in
          if type_of x = wty andalso numSyntax.is_numeral k then
            let val a = word x
            in emit t (list_mk_comb (node_con "BBit", [mk_num a, k])) end
          else atom false t
        end
      else atom false t
    val _ = boolean t0
    val {nodes, n, wvars, bvars, ...} = !st
    fun env_list default vars =
      listSyntax.mk_list
        (List.tabulate (n, fn i => case Lib.assoc1 i vars of
                                       SOME (_, t) => t | NONE => default),
         type_of default)
    fun env default vars =
      let val l = env_list default vars
          val i = variant (free_vars l) (mk_var ("i", numSyntax.num))
      in mk_abs (i, listSyntax.mk_el (i, l)) end
  in
    (listSyntax.mk_list (rev nodes, node_ty),
     env (wordsSyntax.mk_n2w (mk_num 0, wordsSyntax.dest_word_type wty)) wvars,
     env F bvars)
  end

(* ⊢ eval_dag env benv dag ⇔ t', by a compset holding only the DAG's
   semantics, list lookup and num arithmetic, so word constants in the goal
   are left as they are. *)
val eval_cs =
  let val cs = computeLib.add_thms
        [eval_dag_def, eval_nodes_def, eval_node_def, wval_def, bval_def,
         listTheory.EL_restricted, listTheory.EL_simp_restricted, listTheory.HD,
         listTheory.TL, listTheory.LENGTH, listTheory.APPEND,
         listTheory.LAST_compute]
        reduceLib.num_compset
      fun dt ty = valOf (TypeBase.fetch ty)
  in computeLib.add_datatype_info
       (computeLib.add_datatype_info cs (dt node_ty))
       (dt (type_of (prim_mk_const {Thy = "bvBlast", Name = "Bool"})
            |> dom_rng |> snd))
  end

(* ------------------------------------------------------------------------
   The cv side: the DAG's cv image, its CNF, and the certificate check.
   ------------------------------------------------------------------------ *)

val from_cs =
  computeLib.add_thms [cv_typeTheory.from_list_def, from_bvBlast_node_def,
                       cvTheory.b2c_def]
    reduceLib.num_compset

val cv_blast_tm = prim_mk_const {Thy = "bvBlast", Name = "cv_blast_dag"}
val cv_check_tm = prim_mk_const {Thy = "bvBlast", Name = "cv_check_dag"}
val canon_tm = prim_mk_const {Thy = "lratCheck", Name = "cv_canon_steps"}
val canon_eqs =
  List.map (fn n => DB.fetch "lratCheck" n)
    ["cv_canon_steps_def", "cv_canon_ints_def", "cv_canon_nums_def",
     "cv_canon_int_def"]
val blast_eqs = cv_transLib.cv_eqs_for cv_blast_tm
val check_eqs = cv_transLib.cv_eqs_for cv_check_tm @ canon_eqs

fun cnum n = cvSyntax.mk_cv_num (numSyntax.term_of_int n)
fun clist f xs =
  List.foldr (fn (x, acc) => cvSyntax.mk_cv_pair (f x, acc)) (cnum 0) xs
fun cint i = if i < 0 then cvSyntax.mk_cv_pair (cnum (~i), cnum 0) else cnum i
fun csteps steps =
  clist (fn (n, c, hs) =>
           cvSyntax.mk_cv_pair
             (cnum n, cvSyntax.mk_cv_pair (clist cint c, clist cnum hs)))
        steps

fun dec_num t = numeral_int (cvSyntax.dest_cv_num t)
fun dec_int t =
  if cvSyntax.is_cv_pair t then ~ (dec_num (fst (cvSyntax.dest_cv_pair t)))
  else dec_num t
fun dec_list f t =
  if cvSyntax.is_cv_pair t then
    let val (h, r) = cvSyntax.dest_cv_pair t in f h :: dec_list f r end
  else []

(* ------------------------------------------------------------------------
   CaDiCaL
   ------------------------------------------------------------------------ *)

fun on_path name =
  case OS.Process.getEnv "PATH" of
      NONE => NONE
    | SOME p =>
        List.find (fn f => OS.FileSys.access (f, [OS.FileSys.A_EXEC]))
          (List.map (fn d => OS.Path.concat (d, name))
             (String.fields (fn c => c = #":") p))

val cadical_executable = ref ""

fun cadical () =
  if !cadical_executable <> "" then !cadical_executable else
  case OS.Process.getEnv "HOL_CADICAL" of
      SOME f => f
    | NONE => (case on_path "cadical" of SOME f => f
               | NONE => raise ERR "BV_DECIDE"
                   "CaDiCaL not found: set HOL_CADICAL or put cadical on PATH")

fun quote s = "'" ^ String.translate (fn #"'" => "'\\''" | c => str c) s ^ "'"

fun exit_code st =
  case Posix.Process.fromStatus st of
      Posix.Process.W_EXITED => 0
    | Posix.Process.W_EXITSTATUS w => Word8.toInt w
    | _ => ~1

fun write_dimacs file cnf =
  let fun maxvar (c, m) = List.foldl (fn (l, m) => Int.max (abs l, m)) m c
      val vars = List.foldl maxvar 0 cnf
      val out = TextIO.openOut file
      fun lit l = if l < 0 then "-" ^ Int.toString (~l) else Int.toString l
      fun clause c =
        TextIO.output (out, String.concatWith " " (List.map lit c @ ["0\n"]))
  in TextIO.output (out, "p cnf " ^ Int.toString vars ^ " " ^
                         Int.toString (length cnf) ^ "\n");
     List.app clause cnf;
     TextIO.closeOut out end

fun ints line =
  let fun sml_minus #"-" = #"~"
        | sml_minus c = c
  in List.map (fn s => valOf (Int.fromString (String.map sml_minus s)))
       (String.tokens Char.isSpace line)
  end
fun upto0 (0 :: rest) = ([], rest)
  | upto0 (x :: rest) = let val (a, b) = upto0 rest in (x :: a, b) end
  | upto0 [] = raise ERR "BV_DECIDE" "malformed LRAT line"
(* additions (id, clause, hints); deletions (0, [], ids) *)
fun parse_lrat file =
  let val ins = TextIO.openIn file
      fun line l =
        case String.tokens Char.isSpace l of
            [] => NONE
          | (_ :: "d" :: rest) =>
              SOME (0, [], #1 (upto0 (ints (String.concatWith " " rest))))
          | _ => (case ints l of
                      id :: rest => let val (c, rest') = upto0 rest
                                    in SOME (id, c, #1 (upto0 rest')) end
                    | [] => NONE)
      fun loop acc = case TextIO.inputLine ins of
                         NONE => rev acc
                       | SOME l => loop (case line l of
                                             SOME s => s :: acc
                                           | NONE => acc)
  in loop [] before TextIO.closeIn ins
     handle e => (TextIO.closeIn ins; raise e)
  end


(* CaDiCaL logs every clause it learns; keep only the additions the empty
   clause depends on, and deletions of clauses that are kept *)
fun trim ncnf steps =
  let
    fun upto_empty acc [] = rev acc
      | upto_empty acc ((s as (n, [], _)) :: rest) =
          if n = 0 then upto_empty (s :: acc) rest else rev (s :: acc)
      | upto_empty acc (s :: rest) = upto_empty (s :: acc) rest
    val steps = upto_empty [] steps
    fun top_id ((n, _, hs), m) = List.foldl Int.max (Int.max (n, m)) hs
    val top = List.foldl top_id ncnf steps
    val need = Array.array (top + 1, false)
    fun back ((s as (n, c, hs)), acc) =
      if n = 0 then s :: acc
      else if null c orelse Array.sub (need, n) then
        (List.app (fn h => Array.update (need, h, true)) hs; s :: acc)
      else acc
    fun kept i = i <= ncnf orelse Array.sub (need, i)
    fun del ((n, c, hs), acc) =
      if n <> 0 then (n, c, hs) :: acc
      else case List.filter kept hs of [] => acc | hs' => (0, [], hs') :: acc
  in List.foldr del [] (List.foldr back [] steps) end

(* the LRAT refutation of cnf, as addition and deletion steps.  CaDiCaL's
   "lucky" phase made w14's certificate 6x longer (55k hints, not 9.5k) *)
fun refute cnf =
  let val base = OS.FileSys.tmpName ()
      val (cnf_f, lrat_f) = (base ^ ".cnf", base ^ ".lrat")
      fun remove f = OS.FileSys.remove f handle _ => ()
      fun clean () = List.app remove [base, cnf_f, lrat_f]
      fun run () =
        let val _ = write_dimacs cnf_f cnf
            val cmd = String.concatWith " "
                        [quote (cadical ()), "-q", "--lrat", "--no-binary",
                         "--no-lucky", quote cnf_f, quote lrat_f,
                         ">/dev/null", "2>&1"]
            val code = exit_code (OS.Process.system cmd)
        in if code = 20 then parse_lrat lrat_f
           else raise ERR "BV_DECIDE"
                  (if code = 10 then "goal is false (CaDiCaL found a model)"
                   else "CaDiCaL failed with exit code " ^ Int.toString code)
        end
      val steps = run () handle e => (clean (); raise e)
  in clean (); trim (length cnf) steps end

(* ------------------------------------------------------------------------
   The procedure
   ------------------------------------------------------------------------ *)

fun word_type t =
  case Lib.total (find_term (wordsSyntax.is_word_type o type_of)) t of
      SOME s => type_of s
    | NONE =>
        wordsSyntax.mk_word_type (fcpSyntax.mk_numeric_type (Arbnum.fromInt 1))

(* ⊢ t for a quantifier-free t over words of one width *)
fun prove_body t =
  let
    val wty = word_type t
    val aty = wordsSyntax.dest_word_type wty
    val (dag, env, benv) = reify wty t
    (* both sides through the same compset, so that a computable subterm of
       an atom (2 ** 255, say) is reduced alike in both *)
    val eval_dag_tm = prim_mk_const {Thy = "bvBlast", Name = "eval_dag"}
                        |> inst [alpha |-> aty]
    val eval_th = computeLib.CBV_CONV eval_cs
                    (list_mk_comb (eval_dag_tm, [env, benv, dag]))
    val t_th = QCONV (computeLib.CBV_CONV eval_cs) t
    val _ = aconv (rhs (concl eval_th)) (rhs (concl t_th))
            orelse raise ERR "BV_DECIDE"
              "reification did not reproduce the goal"
    val eval_th = TRANS eval_th (SYM t_th)
    val from_th = computeLib.CBV_CONV from_cs
                    (mk_comb (cv_typeLib.from_term_for (type_of dag), dag))
    val dagc = rhs (concl from_th)
    val dim_th = wordsLib.SIZES_CONV (fcpSyntax.mk_dimindex aty)
    val wc = cvSyntax.mk_cv_num (rhs (concl dim_th))
    val cnf_th = cv_computeLib.cv_compute blast_eqs
                   (list_mk_comb (cv_blast_tm, [wc, dagc]))
    val cnf = dec_list (dec_list dec_int) (rhs (concl cnf_th))
    val steps = refute cnf
    val c = csteps steps
    val cv_th = cv_computeLib.cv_compute check_eqs
                  (list_mk_comb (cv_check_tm,
                                 [wc, dagc, mk_comb (canon_tm, c)]))
    val sound = check_dag_cv |> INST_TYPE [alpha |-> aty]
                             |> PURE_REWRITE_RULE [dim_th]
  in
    EQ_MP eval_th (SPECL [env, benv] (MATCH_MP sound (CONJ from_th cv_th)))
  end

fun BV_DECIDE_PROVE t =
  let val (vs, body) = strip_forall t
      val simp_th = QCONV (blastLib.WORD_SIMP_CONV THENC
                           PURE_REWRITE_CONV [word_not_alt]) body
      val body' = rhs (concl simp_th)
      val th' = if Teq body' then TRUTH else prove_body body'
  in GENL vs (EQ_MP (SYM simp_th) th') end

fun BV_DECIDE_CONV t = EQT_INTRO (BV_DECIDE_PROVE t)

fun BV_DECIDE_TAC (asl, g) = ACCEPT_TAC (BV_DECIDE_PROVE g) (asl, g)

end
