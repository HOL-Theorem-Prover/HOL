(* ========================================================================= *)
(* FILE          : mlTacticData.sml                                          *)
(* DESCRIPTION   : Storing data                                              *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)


structure mlTacticData :> mlTacticData =
struct

open HolKernel boolLib Abbrev SharingTables Portable aiLib smlLexer
  mlFeature

val ERR = mk_HOL_ERR "mlTacticData"
fun err_msg s l = raise ERR s (String.concatWith " " (first_n 10 l))

(* -------------------------------------------------------------------------
   Tactic data type
   ------------------------------------------------------------------------- *)

type tacdata =
  {
  tacfea : (lbl,fea) Redblackmap.dict,
  tacfea_cthy : (lbl,fea) Redblackmap.dict,
  taccov : (string, int) Redblackmap.dict,
  tacdep : (goal, lbl list) Redblackmap.dict
  }

val empty_tacdata =
  {
  tacfea = dempty lbl_compare,
  tacfea_cthy = dempty lbl_compare,
  taccov = dempty String.compare,
  tacdep = dempty goal_compare
  }

(* -------------------------------------------------------------------------
   Check if data is up-to-date before export
   ------------------------------------------------------------------------- *)

fun uptodate_goal (asl,w) = all uptodate_term (w :: asl)
fun uptodate_feav ((_,_,g,gl),_) = all uptodate_goal (g :: gl)

(* -------------------------------------------------------------------------
   Parsing raw input
   ------------------------------------------------------------------------- *)

fun read_string s =
  let val n = String.size s in
    if String.sub (s,0) = #"\"" andalso String.sub (s,n - 1) = #"\""
    then
      valOf (String.fromString (String.extract (s,1,SOME (String.size s - 2))))
    else raise ERR "read_string" s
  end
  handle Interrupt => raise Interrupt | _ => raise ERR "read_string" s

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
  handle Interrupt => raise Interrupt | _ => err_msg "read_list" l

fun readcat_list l =
  let val (ll,cont) = read_list l in (List.concat ll, cont) end

fun read_id l = case l of
   [s1,s2] => {Thy = read_string s1, Other = read_string s2}
  | _ => err_msg "read_id" l

(* -------------------------------------------------------------------------
   Loading sharing tables
   ------------------------------------------------------------------------- *)

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
  handle Interrupt => raise Interrupt | _ => err_msg "read_tm" l

fun load_tmvector idvector tyvector l = case l of
   "TERMS" :: m =>
    let
      val (tms,cont) = read_list m
      val tmvector = build_term_vector idvector tyvector (map read_tm tms)
    in
      (tmvector,cont)
    end
  | _ => err_msg "load_tmvector" l


(* -------------------------------------------------------------------------
   Reading terms from their raw representation
   ------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------
   Sharing tables from different sources of terms
   ------------------------------------------------------------------------- *)

fun create_sharing_tables_termset termset =
  let
    fun leaves (t, acc) = Term.all_atomsl [t] acc
    val allleaves = HOLset.foldl leaves empty_tmset termset
    fun doterms (t, tables) = #2 (make_shared_term t tables)
    val (idtable,tytable,tmtable) =
      HOLset.foldl doterms (empty_idtable, empty_tytable, empty_termtable)
      allleaves
    val terml = HOLset.listItems termset
    val termdict = dnew Term.compare (number_snd 0 terml)
  in
    ((terml,termdict), (idtable,tytable,tmtable))
  end

fun create_sharing_tables_feavl feavl =
  let
    fun f ((_,_,g,gl),_) = g :: gl
    val allgoals = List.concat (map f feavl)
    fun goal_terms ((asl,w), acc) =
      HOLset.union(acc, HOLset.fromList Term.compare (w :: asl))
    val termset = List.foldl goal_terms empty_tmset allgoals
  in
    create_sharing_tables_termset termset
  end

(* -------------------------------------------------------------------------
   Exporting terms
   ------------------------------------------------------------------------- *)

fun pp_tml tml =
  let
    val ((terml,termdict),(idtable,tytable,tmtable)) =
      create_sharing_tables_termset (HOLset.fromList Term.compare tml)
    fun pp_sml_list pfun l =
      PP.block INCONSISTENT 0 (
        [ PP.add_string "[", PP.add_break (0,0) ] @
        PP.pr_list pfun [PP.add_string ",", PP.add_break (1,0)] l @
        [ PP.add_break (0,0), PP.add_string "]" ]
      )
    fun raw_term_to_string term =
      quote ((Term.write_raw (fn t => Map.find(#termmap tmtable, t))) term)
    fun pp_tm tm = PP.add_string (raw_term_to_string tm)
    val pp_terml = PP.pr_list pp_tm [PP.add_newline] terml
  in
    PP.block CONSISTENT 0 (
      [
        PP.add_string "IDS", PP.add_newline,
        theoryout_idtable idtable,
        PP.add_newline, PP.add_newline,
        PP.add_string "TYPES", PP.add_newline,
        theoryout_typetable tytable,
        PP.add_newline, PP.add_newline,
        PP.add_string "TERMS", PP.add_newline,
        theoryout_termtable tmtable,
        PP.add_newline, PP.add_newline,
        PP.add_string "TERMS_START",
        PP.add_newline ] @ pp_terml @ [ PP.add_newline,
        PP.add_string "TERMS_END"
      ]
    )
  end

fun export_terml file tml =
  let
    val tml' = filter uptodate_term tml
    val _ = if length tml <> length tml'
            then print_endline "Warning: out-of-date terms are not exported"
            else ()
    val ostrm = Portable.open_out file
  in
    (PP.prettyPrint (curry TextIO.output ostrm, 75) (pp_tml tml');
     TextIO.closeOut ostrm)
  end

(* -------------------------------------------------------------------------
   Exporting tactic data
   ------------------------------------------------------------------------- *)

fun pp_feavl feavl =
  let
    val ((terml,termdict),(idtable,tytable,tmtable)) =
      create_sharing_tables_feavl feavl

    fun pp_sml_list pfun l =
      PP.block INCONSISTENT 0 (
        [ PP.add_string "[", PP.add_break (0,0) ] @
        PP.pr_list pfun [PP.add_string ",", PP.add_break (1,0)] l @
        [ PP.add_break (0,0), PP.add_string "]" ]
      )

    fun raw_term_to_string term =
      quote ((Term.write_raw (fn t => Map.find(#termmap tmtable, t))) term)
    fun pp_tm tm = PP.add_string (raw_term_to_string tm)
    val pp_terml = PP.pr_list pp_tm [PP.add_newline] terml

    fun pp_tmid tm = PP.add_string (int_to_string (dfind tm termdict))
    fun pp_goal (asl,w) = pp_sml_list pp_tmid (w :: asl)
    fun pp_goal_list l =
      PP.block INCONSISTENT 0 (
        [ PP.add_string "START", PP.add_break (1,0) ] @
        PP.pr_list pp_goal [PP.add_break (1,0)] l @
        [ PP.add_break (1,0), PP.add_string "END" ]
      )

    fun pp_fea n = PP.add_string (int_to_string n)

    fun pr_feav ((stac,t,g,gl),fea) =
      PP.block CONSISTENT 0
        [ PP.add_string (mlquote stac), PP.add_newline,
          PP.add_string (Real.toString t), PP.add_newline,
          pp_goal g, PP.add_newline,
          pp_goal_list gl, PP.add_newline,
          pp_sml_list pp_fea fea ]

    val pp_feav_all =
      PP.block CONSISTENT 0
      (if null feavl then []
       else PP.pr_list pr_feav [PP.add_newline] feavl)

  in
    PP.block CONSISTENT 0 (
      [
        PP.add_string"IDS", PP.add_newline,
        theoryout_idtable idtable,
        PP.add_newline, PP.add_newline,
        PP.add_string"TYPES", PP.add_newline,
        theoryout_typetable tytable,
        PP.add_newline, PP.add_newline,
        PP.add_string"TERMS", PP.add_newline,
        theoryout_termtable tmtable,
        PP.add_newline, PP.add_newline,
        PP.add_string "TERMS_START",
        PP.add_newline ] @ pp_terml @ [ PP.add_newline,
        PP.add_string "TERMS_END",
        PP.add_newline, PP.add_newline,
        PP.add_string "FEATURE_VECTORS_START",
        PP.add_newline, pp_feav_all, PP.add_newline,
        PP.add_string "FEATURE_VECTORS_END",
        PP.add_newline
      ]
    )
  end

fun export_tacfea file tacfea =
  let
    val ostrm = Portable.open_out file
    fun is_local s = mem "tttRecord.local_tag" (partial_sml_lexer s)
    fun is_global feav = not (is_local (#1 (fst feav)))
    val feavl1 = filter is_global (dlist tacfea)
    val feavl2 = filter uptodate_feav feavl1
  in
    (PP.prettyPrint (curry TextIO.output ostrm, 75) (pp_feavl feavl2);
     TextIO.closeOut ostrm)
  end

(* -------------------------------------------------------------------------
   Importing terms
   ------------------------------------------------------------------------- *)

fun import_terml file =
  let val l0 = partial_sml_lexer (String.concatWith " " (readl file)) in
    if l0 = [] then [] else
      let
        val (idvector,l1) = load_idvector l0
        val (tyvector,l2) = load_tyvector idvector l1
        val (tmvector,l3) = load_tmvector idvector tyvector l2
        val (term_vector,l4) = read_terml tmvector l3
      in
        vector_to_list term_vector
      end
  end

(* -------------------------------------------------------------------------
   Importing tactic data
   ------------------------------------------------------------------------- *)

fun read_goal lookup l = case l of
    a :: m => (map lookup m, lookup a)
  | _      => err_msg "read_goal" l

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


(*  val file = ttt_tacfea_dir ^ "/" ^ thy *)

fun import_tacfea file =
  let val l0 = partial_sml_lexer (String.concatWith " " (readl file)) in
    if null l0 then dempty lbl_compare else
    let
      val (idvector,l1) = load_idvector l0
      val (tyvector,l2) = load_tyvector idvector l1
      val (tmvector,l3) = load_tmvector idvector tyvector l2
      val (term_vector,l4) = read_terml tmvector l3
      fun lookup ns = Vector.sub (term_vector, string_to_int ns)
      val (feavl,_) = read_feavl lookup l4
    in
      dnew lbl_compare feavl
    end
  end

(*
fun read_tacfea_thy thy =
  if mem thy ["min","bool"] then [] else read_feavdatal thy
*)

(* -------------------------------------------------------------------------
   Tactic data is recovered from tacfea
   ------------------------------------------------------------------------- *)

fun init_taccov tacfea =
  count_dict (dempty String.compare) (map (#1 o fst) (dlist tacfea))

fun update_tacdep (lbl,tacdep) =
  let
    val oldv = dfind (#3 lbl) tacdep handle NotFound => []
    val newv = lbl :: oldv
  in
    dadd (#3 lbl) newv tacdep
  end

fun init_tacdep tacfea =
  foldl update_tacdep (dempty goal_compare) (dkeys tacfea)

fun init_tacdata tacfea =
  {
  tacfea      = tacfea,
  tacfea_cthy = dempty lbl_compare,
  tacdep      = init_tacdep tacfea,
  taccov      = init_taccov tacfea
  }

fun import_tacdata filel =
  let val tacfea = union_dict lbl_compare (map import_tacfea filel) in
    init_tacdata tacfea
  end

(* -------------------------------------------------------------------------
   Tactictoe database management
   ------------------------------------------------------------------------- *)

val ttt_tacdata_dir = HOLDIR ^ "/src/tactictoe/ttt_tacdata"

fun exists_tacdata_thy thy = exists_file (ttt_tacdata_dir ^ "/" ^ thy)

fun ttt_create_tacdata () =
  let
    val thyl = ancestry (current_theory ())
    fun f x = ttt_tacdata_dir ^ "/" ^ x
    val ethyl1 = filter (not o exists_tacdata_thy) thyl
    val ethyl2 = filter (fn x => not (mem x ["bool","min"])) ethyl1
    val _ =
      if null ethyl2 then () else
      print_endline
        ("Warning: missing tactic data for theories:" ^
        (String.concatWith " " ethyl2))
    val filel = filter exists_file (map f thyl)
    val tacdata = import_tacdata filel
    val is = int_to_string (dlength (#tacfea tacdata))
  in
    print_endline ("Loading " ^ is ^ " tactics");
    tacdata
  end

fun ttt_update_tacdata_aux {tacfea, tacfea_cthy, taccov, tacdep} (lbl,fea) =
  {
  tacfea      = dadd lbl fea tacfea,
  tacfea_cthy = dadd lbl fea tacfea_cthy,
  tacdep      = update_tacdep (lbl,tacdep),
  taccov      = count_dict taccov [#1 lbl]
  }

fun ttt_update_tacdata (lbl as (stac,t,g,gl), tacdata) =
  if op_mem goal_eq g gl orelse dmem lbl (#tacfea tacdata)
  then tacdata
  else ttt_update_tacdata_aux tacdata (lbl, feahash_of_goal g)

fun ttt_export_tacdata thy tacdata =
  let
    val _ = mkDir_err ttt_tacdata_dir
    val file = ttt_tacdata_dir ^ "/" ^ thy
  in
    print_endline file;
    export_tacfea file (#tacfea tacdata)
  end



end (* struct *)
