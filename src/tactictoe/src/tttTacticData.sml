(* ========================================================================== *)
(* FILE          : tttTacticData.sml                                                *)
(* DESCRIPTION   : Storing feature vectors                                    *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure tttTacticData :> tttTacticData =
struct

open HolKernel boolLib Abbrev tttTools tttTimeout tttExec tttLearn
tttThmData tttPredict SharingTables Portable tttSetup

val ERR = mk_HOL_ERR "tttTacticData"

(*---------------------------------------------------------------------------
 * Export
 *---------------------------------------------------------------------------*)

fun uptodate_goal (asl,w) = all uptodate_term (w :: asl)
fun uptodate_feav ((_,_,g,gl),_) = all uptodate_goal (g :: gl)

fun create_sharing_tables feavl =
  let
    fun f ((_,_,g,gl),_) = g :: gl
    val allgoals = List.concat (map f feavl)
    fun goal_terms ((asl,w), acc) =
      HOLset.union(acc, HOLset.fromList Term.compare (w :: asl))
    val allterms = List.foldl goal_terms empty_tmset allgoals
    fun leaves (t, acc) = Term.all_atomsl [t] acc
    val allleaves = HOLset.foldl leaves empty_tmset allterms
    fun doterms (t, tables) = #2 (make_shared_term t tables)
    val (idtable,tytable,tmtable) =
      HOLset.foldl doterms (empty_idtable, empty_tytable, empty_termtable)
      allleaves
    fun number start l = case l of
      []      => []
    | a :: m  => (a,start) :: number (start + 1) m
    val terml = HOLset.listItems allterms
    val termdict = dnew Term.compare (number 0 terml)
  in
    ((terml,termdict), (idtable,tytable,tmtable))
  end

infix >>
fun (f1 >> f2) pps = (f1 pps ; f2 pps)

fun block state brkdepth f pps = (HOLPP.begin_block pps state brkdepth ;
                                  f pps;
                                  HOLPP.end_block pps)

fun add_string s pps = HOLPP.add_string pps s
val add_newline = HOLPP.add_newline
fun jump () = add_newline >> add_newline
fun add_break ipr pps = HOLPP.add_break pps ipr
fun pr_list f g h obs pps = Portable.pr_list (fn x => f x pps)
                                             (fn () => g pps)
                                             (fn () => h pps)
                                             obs

val flush = HOLPP.flush_ppstream
fun nothing pps = ()

fun pp_feavl feavl =
  let
    val ((terml,termdict),(idtable,tytable,tmtable)) =
      create_sharing_tables feavl

    fun pp_sml_list pfun l =
      block INCONSISTENT 0
        (
        add_string "[" >> add_break (0,0) >>
        pr_list pfun (add_string ",") (add_break (1,0)) l >>
        add_break (0,0) >>
        add_string "]"
        )

    fun term_to_string term =
      quote ((Term.write_raw (fn t => Map.find(#termmap tmtable, t))) term)
    fun pp_tm tm = add_string ( (term_to_string tm))
    val pp_terml = pr_list pp_tm nothing add_newline terml

    fun pp_tmid tm = add_string (int_to_string (dfind tm termdict))
    fun pp_goal (asl,w) = pp_sml_list pp_tmid (w :: asl)
    fun pp_goal_list l =
      block INCONSISTENT 0
        (
        add_string "START" >> add_break (1,0) >>
        pr_list pp_goal nothing (add_break (1,0)) l >>
        add_break (1,0) >>
        add_string "END"
        )

    fun pp_fea n = add_string (int_to_string n)

    fun pr_feav ((stac,t,g,gl),fea) =
      block CONSISTENT 0
      (
      add_string (mlquote stac) >> add_newline >>
      add_string (Real.toString t) >> add_newline >>
      pp_goal g >> add_newline >>
      pp_goal_list gl >> add_newline >>
      pp_sml_list pp_fea fea
      )
    val pp_feav_all =
      block CONSISTENT 0
      (if null feavl then nothing
       else pr_list pr_feav nothing add_newline feavl)

  in
    block CONSISTENT 0
      (
      add_string "IDS" >> add_newline >>
      C theoryout_idtable idtable >> jump () >>
      add_string "TYPES" >> add_newline >>
      C theoryout_typetable tytable >> jump () >>
      add_string "TERMS" >> add_newline >>
      C theoryout_termtable tmtable >> jump () >>
      add_string "TERMS_START" >> add_newline >>
      pp_terml >> add_newline >>
      add_string "TERMS_END" >> jump () >>
      add_string "FEATURE_VECTORS_START" >> add_newline >>
      pp_feav_all >> add_newline >>
      add_string "FEATURE_VECTORS_END" >> jump ()
      ) >>
    flush
  end

fun feavl_out f ostrm =
 let val ppstrm = Portable.mk_ppstream
                    {consumer = Portable.outputc ostrm,
                     linewidth=75, flush = fn () => Portable.flush_out ostrm}
 in f ppstrm handle e => (Portable.close_out ostrm; raise e);
    Portable.flush_ppstream ppstrm;
    Portable.close_out ostrm
 end

fun export_tacdata thy =
  let
    val file = ttt_tacfea_dir ^ "/" ^ thy
    val ostrm = Portable.open_out file
    fun is_local s = mem "tttRecord.local_tag" (tttLexer.ttt_lex s)
    fun is_global feav = not (is_local (#1 (fst feav)))
    val feavl1 = filter is_global (dlist (!ttt_tacfea_cthy))
    val feavl2 = filter uptodate_feav feavl1
  in
    feavl_out (pp_feavl feavl2) ostrm
  end

(*----------------------------------------------------------------------------
 * Import
 *----------------------------------------------------------------------------*)

fun err_msg s l = raise ERR s (String.concatWith " " (first_n 10 l))

fun read_string s =
  let val n = String.size s in
    if String.sub (s,0) = #"\"" andalso String.sub (s,n - 1) = #"\""
    then
      valOf (String.fromString (String.extract (s,1,SOME (String.size s - 2))))
    else raise ERR "read_string" s
  end
  handle _ => raise ERR "read_string" s

fun read_list l =
  (
  case l of
   "[" :: m =>
    let
      val (body,cont) = split_sl "]" m
      val ll = rpt_split_sl "," body
    in
      if ll = [[]] then ([],cont) else (ll, cont)
    end
  | _ => err_msg "read_list" l
  )
  handle _ => err_msg "read_list" l

fun readcat_list l =
  let val (ll,cont) = read_list l in
    (List.concat ll, cont)
  end


fun read_id l = case l of
   [s1,s2] => {Thy = read_string s1, Other = read_string s2}
  | _ => err_msg "read_id" l

fun load_idvector l = case l of
   "IDS" :: m =>
    let
      val (ids,cont) = read_list m
      val idvector = Vector.fromList (map read_id ids)
    in
      (idvector,cont)
    end
  | _ => err_msg "load_idvector" l

fun read_ty l = case l of
    "TYOP" :: nl => TYOP (map string_to_int nl)
  | "TYV" :: [s] => TYV (read_string s)
  | _ => err_msg "read_ty" l

fun load_tyvector idvector l = case l of
   "TYPES" :: m =>
    let
      val (tys,cont) = read_list m
      val tyvector = build_type_vector idvector (map read_ty tys)
    in
      (tyvector,cont)
    end
  | _ => err_msg "load_tyvector" l

fun read_tm l =
  (
  case l of
    ["TMV",s,tyn] => TMV (read_string s, string_to_int tyn)
  | ["TMC",n1,n2] => TMC (string_to_int n1, string_to_int n2)
  | ["TMAp",n1,n2] => TMAp (string_to_int n1, string_to_int n2)
  | ["TMAbs",n1,n2] => TMAbs (string_to_int n1, string_to_int n2)
  | _ => err_msg "read_tm" l
  )
  handle _ => err_msg "read_tm" l

fun load_tmvector idvector tyvector l = case l of
   "TERMS" :: m =>
    let
      val (tms,cont) = read_list m
      val tmvector = build_term_vector idvector tyvector (map read_tm tms)
    in
      (tmvector,cont)
    end
  | _ => err_msg "load_tmvector" l

(* Terms *)
fun read_terml_loop tmvector acc l = case l of
   "TERMS_END" :: m => (Vector.fromList (rev acc), m)
  | s :: m =>
    let val tm = (Term.read_raw tmvector o read_string) s
      handle _ => err_msg "read_raw" [s]
    in
      read_terml_loop tmvector (tm :: acc) m
    end
  | _ => err_msg "read_terml_loop" l

fun read_terml tmvector l = case l of
   "TERMS_START" :: m => read_terml_loop tmvector [] m
  | _ => err_msg "read_terml" l

(* Goal *)
fun read_goal lookup l = case l of
    a :: m => (map lookup m, lookup a)
  | _      => err_msg "read_goal" l

(* Goal list *)
fun extract_gl_cont l = case l of
    "START" :: m => split_sl "END" m
  | _ => err_msg "extract_gl" l

fun extract_gl l = case l of
    [] => []
  | _  =>
  let val (l1,cont1) = readcat_list l in
    l1 :: extract_gl cont1
  end

(* Feature vector *)
fun read_feav lookup l = case l of
    a :: b :: m =>
    let
      val stac = read_string a
      val tim  = valOf (Real.fromString b)
      val (l0,cont0) = readcat_list m
      val g = read_goal lookup l0
      val (l1,cont1) = extract_gl_cont cont0
      val gl = map (read_goal lookup) (extract_gl l1)
      val (l2,cont2) = readcat_list cont1
      val fea = map string_to_int l2
    in
      (((stac,tim,g,gl),fea),cont2)
    end
  | _ => err_msg "read_feav" l

fun read_feavl_loop lookup acc l = case l of
   "FEATURE_VECTORS_END" :: m => (rev acc, m)
  | [] => err_msg "read_feavl_loop" l
  | _ =>
   let val (feav,cont) = read_feav lookup l in
     read_feavl_loop lookup (feav :: acc) cont
   end

fun read_feavl lookup l = case l of
   "FEATURE_VECTORS_START" :: m => read_feavl_loop lookup [] m
  | _ => err_msg "read_feavl" l

fun read_feavdatal thy =
  let
    val file = ttt_tacfea_dir ^ "/" ^ thy
    val l0 = tttLexer.ttt_lex (String.concatWith " " (readl file))
      handle _ => (print_endline (thy ^ " is missing"); debug thy; [])
  in
    if l0 = []
    then []
    else
      let
        val (idvector,l1) = load_idvector l0
        val (tyvector,l2) = load_tyvector idvector l1
        val (tmvector,l3) = load_tmvector idvector tyvector l2
        val (term_vector,l4) = read_terml tmvector l3
        fun lookup ns = Vector.sub (term_vector, string_to_int ns)
        val (feavl,_) = read_feavl lookup l4
      in
        feavl
      end
  end

fun read_feavdatal_no_min thy =
  if mem thy ["min","bool"] then [] else read_feavdatal thy

fun update_tacdep (lbl,_) =
  let
    val oldv = dfind (#3 lbl) (!ttt_tacdep) handle _ => []
    val newv = lbl :: oldv
  in
    ttt_tacdep := dadd (#3 lbl) newv (!ttt_tacdep)
  end

fun init_tacdata feavl =
  (
  ttt_tacfea := dnew lbl_compare feavl;
  ttt_tacfea_cthy := dempty lbl_compare;
  ttt_tacdep := dempty goal_compare;
  ttt_taccov :=
    count_dict (dempty String.compare)
    (map (#1 o fst) (dlist (!ttt_tacfea)))
  ;
  dapp update_tacdep (!ttt_tacfea)
  )

fun import_tacdata thyl =
  let val feavl = List.concat (map read_feavdatal_no_min thyl) in
    init_tacdata feavl
  end

(*----------------------------------------------------------------------------
 * Update
 *----------------------------------------------------------------------------*)

val feature_time = ref 0.0 (* statistics *)

fun update_tacdata_aux (lbl,fea) =
  if dmem lbl (!ttt_tacfea) then () else
    (
    ttt_tacfea := dadd lbl fea (!ttt_tacfea);
    ttt_tacfea_cthy := dadd lbl fea (!ttt_tacfea_cthy);
    update_tacdep (lbl,fea);
    ttt_taccov := count_dict (!ttt_taccov) [(#1 lbl)]
    )

fun update_tacdata (lbl0 as (stac0,t0,g0,gl0)) =
  if mem g0 gl0 then () else
    let
      val fea = total_time feature_time tttFeature.fea_of_goal g0
      val (lbl as (stac,t,g,gl)) =
        debug_t "orthogonalize" orthogonalize (lbl0,fea)
      val feav = (lbl,fea)
    in
      update_tacdata_aux feav
    end






end (* struct *)
