(* ========================================================================== *)
(* FILE          : hhsExtract.sml                                             *)
(* DESCRIPTION   : Extract tactics from Poly/ML code                          *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsExtract :> hhsExtract =
struct

open HolKernel boolLib hhsExec hhsLexer hhsTools

val ERR = mk_HOL_ERR "hhsExtract"

val pointer_cache_glob = ref (dempty String.compare)

(*---------------------------------------------------------------------------
 * Extract tactics
 *---------------------------------------------------------------------------*)

fun hhs_propl_of s =
  let 
    val stream = TextIO.openString s
    val resultTrees : PolyML.parseTree list ref = ref []
    fun compilerResultFun (parsetree, codeOpt) =
      let
        val _ =
        case parsetree of
          SOME pt => resultTrees := !resultTrees @ [pt]
        | NONE => ()
      in
        fn () => raise ERR "hhs_propl_of" "NONE"
      end
    val _ = PolyML.compiler (fn () => 
          TextIO.input1 stream, 
         [PolyML.Compiler.CPCompilerResultFun compilerResultFun,
          PolyML.Compiler.CPNameSpace PolyML.globalNameSpace])
    in
      snd (hd (!resultTrees)) handle _ => raise ERR "hhs_propl_of" s
    end
 
fun hhs_prop_first p = case p of
    PolyML.PTfirstChild f  => SOME (snd (f ()))
  | _               => NONE

fun hhs_path_of s =
  let 
    val x = hd (hhs_propl_of s)
    val l = valOf (hhs_prop_first x)
    fun f y = case y of PolyML.PTdeclaredAt y => y 
                      | _ => raise ERR "hhs_path_of" ""
    val decll = mapfilter f l
    val path = #file (hd decll)
  in
    path
  end

fun string_of_pretty p =
  let
    val acc = ref []
    fun f s = acc := s :: !acc
  in
    PolyML.prettyPrint (f,80) p ;
    String.concatWith " " (rev (!acc))
  end

fun hhs_propl_all_of s =
  let
    val stream = TextIO.openString s
    val resultTrees : PolyML.parseTree list ref = ref []
    fun compilerResultFun (parsetree, codeOpt) =
      let
        val _ =
        case parsetree of
          SOME pt => resultTrees := !resultTrees @ [pt]
        | NONE => ()
      in
        fn () => raise Fail "not implemented"
      end
    val _ = PolyML.compiler (fn () =>
          TextIO.input1 stream,
         [PolyML.Compiler.CPCompilerResultFun compilerResultFun,
          PolyML.Compiler.CPNameSpace PolyML.globalNameSpace])
    in
      map snd (!resultTrees)
    end

fun is_print_prop prop = case prop of
   PolyML.PTprint _ => true
  | _ => false

fun dest_print_prop prop = case prop of
   PolyML.PTprint g => g
  | _ => raise ERR "dest_print" ""

fun is_first_prop prop = case prop of
   PolyML.PTfirstChild _ => true
  | _ => false

fun is_next_prop prop = case prop of
   PolyML.PTnextSibling _ => true
  | _ => false

fun dest_first_prop p = case p of
    PolyML.PTfirstChild g => snd (g ())
  | _ => raise ERR "dest_first_next" ""

fun dest_next_prop p = case p of
    PolyML.PTnextSibling g => snd (g ())
  | _ => raise ERR "dest_first_next" ""

datatype hhs_subtac =
    HHSTACL of string option * (hhs_subtac list)
  | HHSLEAF of string option

fun extract_subterms_aux propl =
  let val s =
    case List.find is_print_prop propl of
      SOME p => SOME (string_of_pretty ((dest_print_prop p) 80))
    | NONE   => NONE
    val l1 = List.filter is_first_prop propl
    val l2 = List.filter is_next_prop propl
  in
    case (l1,l2) of
      ([],[]) => [HHSLEAF s]
    | ([fprop],[]) =>
      let
        val ftreel = extract_subterms_aux (dest_first_prop fprop)
      in
        [HHSTACL (s,ftreel)]
      end
    | ([],[nprop]) =>
      let
        val ntreel = extract_subterms_aux (dest_next_prop nprop)
      in
        HHSLEAF s :: ntreel
      end
    | ([fprop],[nprop]) =>
      let
        val ftreel = extract_subterms_aux (dest_first_prop fprop)
        val ntreel = extract_subterms_aux (dest_next_prop nprop)
      in
        HHSTACL (s,ftreel) :: ntreel
      end
    | _ => raise ERR "extract_subterms_aux" ""
  end

fun extract_subterms s =
  let val propll = hhs_propl_all_of s in
    if List.length propll = 1
    then extract_subterms_aux (hd propll)
    else raise ERR "extract_subterms" s
  end

fun is_infix s = String.isPrefix "hhs_infix" (hd (hhs_lex s))

fun is_infix_tree tree = case tree of
   HHSTACL (s, treel) => is_infix (valOf s)
 | HHSLEAF s => is_infix (valOf s)

fun is_infix_treel treel = 
  List.length treel = 3 
  andalso 
  (is_infix_tree (List.nth (treel,1)) handle _ => false)

fun is_recordable1 sno sl treel =
  mem "hhsNumber.hhs_fst" sl andalso
  not (is_infix_treel treel) andalso
  is_tactic sno  

fun is_recordable2 sno sl =
  mem "hhsNumber.hhs_fst" sl andalso 
  is_tactic sno

(*  
  dfind s (!pointer_cache_glob) handle _ =>
  let val b =
    mem #"." (explode s) andalso
    (
    is_pointer_eq s "Tactical.THEN" orelse
    is_pointer_eq s "Tactical.ORELSE" orelse
    is_pointer_eq s "Tactical.THEN1" orelse
    is_pointer_eq s "Tactical.THENL" orelse
    is_pointer_eq s "Tactical.REVERSE" orelse
    is_pointer_eq s "Tactical.VALID" orelse
    is_pointer_eq s "BasicProvers.by" orelse
    is_pointer_eq s "BasicProvers.suffices_by" orelse
    is_pointer_eq s "Tactical.EVERY"
    )
 in
   pointer_cache_glob := dadd s b (!pointer_cache_glob);
   b
 end
*)
fun extract_tactics tree = case tree of
    HHSTACL (s, treel) =>
    if s = NONE then List.concat (map extract_tactics treel) else
      let val sno = valOf s 
          val sl = hhs_lex (valOf s)
      in
        if is_recordable1 sno sl treel
        then [sl]
        else List.concat (map extract_tactics treel)
      end
  | HHSLEAF s =>
    if s = NONE then [] else 
      let val sno = valOf s
          val sl = hhs_lex sno
      in
        if is_recordable2 sno sl then [sl] else []
      end

fun hhs_extract s =
  List.concat (map extract_tactics (extract_subterms s))

end (* struct *)
