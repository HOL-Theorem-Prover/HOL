(* ========================================================================== *)
(* FILE          : tttTermData.sml                                            *)
(* DESCRIPTION   :                                                            *)
(*                                                                            *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure tttTermData :> tttTermData =
struct

open HolKernel boolLib Abbrev tttTools tttLexer SharingTables Portable

val ERR = mk_HOL_ERR "tttTermData"

(* --------------------------------------------------------------------------
   Exporting terms
   -------------------------------------------------------------------------- *)

fun create_sharing_tables_tml tml =
  let
    val allterms = HOLset.fromList Term.compare tml
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

fun pp_tml tml =
  let
    val ((terml,termdict),(idtable,tytable,tmtable)) =
      create_sharing_tables_tml tml

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

fun export_tml file tml =
  let val ostrm = Portable.open_out file in
    (PP.prettyPrint (curry TextIO.output ostrm, 75) (pp_tml tml);
     TextIO.closeOut ostrm)
  end

(* --------------------------------------------------------------------------
   Importing terms
   -------------------------------------------------------------------------- *)

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


fun vector_to_list v = Vector.foldr (op ::) [] v

fun import_tml file =
  let val l0 = tttLexer.ttt_lex (String.concatWith " " (readl file)) in
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


end (* struct *)
