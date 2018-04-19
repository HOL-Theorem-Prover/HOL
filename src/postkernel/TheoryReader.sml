(* ========================================================================== *)
(* FILE          : TheoryReader.sml                                           *)
(* DESCRIPTION   : Read theory data from disk                                 *)
(*                                                                            *)
(* AUTHOR        : Thibault Gauthier, University of Innsbruck                 *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure TheoryReader :> TheoryReader =
struct

type thm      = Thm.thm;
type term     = Term.term
type hol_type = Type.hol_type

open HolKernel SharingTables

val ERR = mk_HOL_ERR "TheoryReader"

fun first_n n l =
  if n <= 0 orelse null l then [] else hd l :: first_n (n - 1) (tl l)

fun err_msg s l = raise ERR s (String.concatWith " " (first_n 10 l))

fun split_sl_aux s pl sl = case sl of
    []     => raise ERR "split_sl_aux" s
  | a :: m => if a = s
              then (rev pl, m)
              else split_sl_aux s (a :: pl) m

fun split_sl s sl = split_sl_aux s [] sl

fun rpt_split_sl s sl =
  let val (a,b) = split_sl s sl handle HOL_ERR _ => (sl,[])
  in
    if null b then [a] else a :: rpt_split_sl s b
  end

fun read_string s =
  let val n = String.size s in
    if String.sub (s,0) = #"\"" andalso String.sub (s,n - 1) = #"\""
    then
      valOf (String.fromString (String.extract (s,1,SOME (String.size s - 2))))
    else raise ERR "read_string" s
  end
  handle HOL_ERR _ => raise ERR "read_string" s

fun read_list l =
  (
  case l of
   "[" :: m =>
    let
      val (body,cont) = split_sl "]" m
      val ll = rpt_split_sl "," body
    in
      if ll = [[]]
      then ([],cont)
      else (ll, cont)
    end
  | _ => err_msg "read_list" l
  )
  handle HOL_ERR _ => err_msg "read_list" l

fun read_thid l = case l of
   [s,n1,n2] =>
   (read_string s, Arbnum.fromString n1, Arbnum.fromString n2)
  | _ => err_msg "read_thid" l

fun read_thid_cont l = case l of
   s :: n1 :: n2 :: cont => (read_thid [s,n1,n2], cont)
  | _ => err_msg "read_thid" l

fun load_theory_and_parents l = case l of
    "THEORY_AND_PARENTS" :: m =>
    let
      val (thid,cont0) = read_thid_cont m
      val (parents,cont1) = read_list cont0
      val _ = Theory.link_parents thid (map read_thid parents)
    in
      cont1
    end
  | _ => err_msg "load_theory_and_parents" l

fun read_type l = case l of
    [s,n] => (read_string s, string_to_int n)
  | _ => err_msg "read_type" l

fun load_incorporate_types thyname l = case l of
   "INCORPORATE_TYPES" :: m =>
    let
      val (types,cont) = read_list m
      val _ = Theory.incorporate_types thyname (map read_type types)
    in
      cont
    end
  | _ => err_msg "load_incorporate_types" l

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

fun read_const l = case l of
    [s,n] => (read_string s, string_to_int n)
  | _ => err_msg "read_const" l

fun load_incorporate_consts thyname tyvector l = case l of
   "INCORPORATE_CONSTS" :: m =>
    let
      val (consts,cont) = read_list m
      val _ = Theory.incorporate_consts thyname tyvector (map read_const consts)
    in
      cont
    end
  | _ => err_msg "load_incorporate_consts" l

fun read_tm l =
  (
  case l of
    ["TMV",s,tyn] => TMV (read_string s, string_to_int tyn)
  | ["TMC",n1,n2] => TMC (string_to_int n1, string_to_int n2)
  | ["TMAp",n1,n2] => TMAp (string_to_int n1, string_to_int n2)
  | ["TMAbs",n1,n2] => TMAbs (string_to_int n1, string_to_int n2)
  | _ => err_msg "read_tm" l
  )
  handle HOL_ERR _ => err_msg "read_tm" l

fun load_tmvector idvector tyvector l = case l of
   "TERMS" :: m =>
    let
      val (tms,cont) = read_list m
      val tmvector = build_term_vector idvector tyvector (map read_tm tms)
    in
      (tmvector,cont)
    end
  | _ => err_msg "load_tmvector" l


fun wait_nonumber pl sl = case sl of
   [] => (rev pl,[])
 | a :: m => if Char.isDigit (String.sub (a,0))
             then wait_nonumber (a :: pl) m
             else (rev pl, sl)

fun read_dl l =
  if l = [] then [] else
  let val (nl,cont) = wait_nonumber [] (tl l) in
    (read_string (hd l), map string_to_int nl) :: read_dl cont
  end

fun read_dep l = case l of
    a :: b :: m => ((read_string a,string_to_int b),read_dl m)
  | _ => err_msg "read_dep" l


(* Relies on the CLASSES post to stop parsing theorems *)
fun read_thml_loop tmvector acc l = case l of
   "CLASSES" :: m => (rev acc,l)
  | s :: m =>
    let
      val thmname = read_string s
      val (dep,cont0) = read_list m
      val (ocl,cont1) = read_list cont0
      val (pretml,cont2) = read_list cont1
      val pretag = (read_dep (List.concat dep),
                    map read_string (List.concat ocl))
      val tml = map (Term.read_raw tmvector o read_string) (List.concat pretml)
                handle HOL_ERR _ => err_msg "read_raw" (List.concat pretml)
      val thm = Thm.disk_thm (pretag, tml)
    in
      read_thml_loop tmvector ((thmname,thm) :: acc) cont2
    end
  | _ => err_msg "read_thml_loop" l

fun read_thml tmvector l = case l of
   "THEOREMS" :: m => read_thml_loop tmvector [] m
  | _ => err_msg "read_thml" l

fun read_class thmdict l = case l of
    [s,"Axm"] =>
    let val name = read_string s in
      (name,Redblackmap.find (thmdict,name),DB.Axm)
    end
  | [s,"Def"] =>
    let val name = read_string s in
     (name,Redblackmap.find (thmdict,name),DB.Def)
    end
  | [s,"Thm"] =>
    let val name = read_string s in
      (name,Redblackmap.find (thmdict,name),DB.Thm)
    end
  | _ => err_msg "read_thml" l

fun load_classes thmdict thyname l = case l of
   "CLASSES" :: m =>
    let
      val (preclasses,cont) = read_list m
      val classes = map (read_class thmdict) preclasses
      val _ = DB.bindl thyname classes
    in
      cont
    end
  | _ => err_msg "load_classes" l

fun read_loadable_thydata l = case l of
    s0::rest => (read_string s0, String.concat (map read_string rest))
  | _ => err_msg "read_loadable_thydata" l

fun temp_encoded_update tmvector thyname (s0,s1) =
  Theory.LoadableThyData.temp_encoded_update {
     thy = thyname,
     thydataty = s0,
     read = Term.read_raw tmvector,
     data = s1
  }
  handle HOL_ERR _ => err_msg "temp_encoded_update" [s0,s1]

fun load_loadable_thydata tmvector thyname l = case l of
   "LOADABLE_THYDATA" :: m =>
    let
      val (l0,cont) = read_list m
      val l1 = map read_loadable_thydata l0
      val _ = app (temp_encoded_update tmvector thyname) l1
    in
      cont
    end
  | _ => err_msg "load_loadable_thydata" l

fun read_thydata path =
  let
    val file = TextIO.openIn path
    fun loop file = case TextIO.inputLine file of
        SOME line => TheoryLexer.lex_thydata line @ loop file
      | NONE => []
    val l = loop file
  in
    (TextIO.closeIn file; l)
  end

fun H nm f x =
  f x handle e =>
      raise ERR "load_thydata" (nm ^ ": " ^ General.exnMessage e)

fun load_thydata thyname path =
  let
    val l0 = H "read_thydata" read_thydata path
    val l1 = H "load_theory_and_parents" load_theory_and_parents l0
    val l2 = H "load_incorporate_types" (load_incorporate_types thyname) l1
    val (idvector,l3) = H "load_idvector" load_idvector l2
    val (tyvector,l4) = H "load_tyvector" (load_tyvector idvector) l3
    val l5 = H "load_incorporate_consts"
               (load_incorporate_consts thyname tyvector) l4
    val (tmvector,l6) = H "load_tmvector" (load_tmvector idvector tyvector) l5
    val (named_thms,l7) = H "read_thml" (read_thml tmvector) l6
    val thmdict = Redblackmap.fromList String.compare named_thms
    val l8 = H "load_classes" (load_classes thmdict thyname) l7
    val _ = H "load_loadable_thydata"
              (load_loadable_thydata tmvector thyname) l8
  in
    thmdict
  end

end;  (* TheoryReader *)
