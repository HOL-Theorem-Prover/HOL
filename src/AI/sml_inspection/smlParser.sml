(* ========================================================================= *)
(* FILE          : smlParser.sml                                             *)
(* DESCRIPTION   : Parse SML using the Poly/ML compiler                      *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure smlParser :> smlParser =
struct

open HolKernel boolLib aiLib smlLexer smlExecute

val ERR = mk_HOL_ERR "smlExtract"

(* -------------------------------------------------------------------------
   Calling the compiler
   ------------------------------------------------------------------------- *)

fun sml_propl_of s =
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
        fn () => raise ERR "sml_propl_of" "NONE"
      end
    val _ = PolyML.compiler (fn () =>
          TextIO.input1 stream,
         [PolyML.Compiler.CPCompilerResultFun compilerResultFun,
          PolyML.Compiler.CPNameSpace PolyML.globalNameSpace])
    in
      snd (hd (!resultTrees)) handle _ => raise ERR "sml_propl_of" s
    end

(* -------------------------------------------------------------------------
   Parsed tree
   ------------------------------------------------------------------------- *)

fun sml_prop_first p = case p of
    PolyML.PTfirstChild f  => SOME (snd (f ()))
  | _               => NONE

fun declaration_path s =
  let
    val x = hd (sml_propl_of s)
    val l = valOf (sml_prop_first x)
    fun f y = case y of PolyML.PTdeclaredAt y => y
                      | _ => raise ERR "sml_path_of" ""
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
    PolyML.prettyPrint (f,80) p;
    String.concatWith " " (rev (!acc))
  end


fun sml_propl_all_of s =
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

(* -------------------------------------------------------------------------
   Simplified parsed tree
   ------------------------------------------------------------------------- *)

datatype smlexp =
    SmlExp of string option * (smlexp list)
  | SmlUnit of string option

fun dest_smlexp e = case e of
    SmlExp (a,b) => (a,b)
  | _ => raise ERR "dest_smlexp" ""

fun constant_space stac = String.concatWith " " (partial_sml_lexer stac)

fun string_of_smlexp e = case e of
   SmlExp (SOME s,_) => constant_space s
 | SmlUnit (SOME s) => constant_space s
 | _ => raise ERR "string_of_smlexp" ""

fun reprint s =
  let val propll = sml_propl_all_of s in
    if List.length propll = 1 then
      case List.find is_print_prop
        (dest_first_prop (valOf (List.find is_first_prop (hd propll)))) of
      SOME p => SOME (string_of_pretty ((dest_print_prop p) 80))
    | NONE   => NONE
    else raise ERR "reprint" s
  end

fun extract_smlexp_aux propl =
  let val s =
    case List.find is_print_prop propl of
      SOME p => SOME (string_of_pretty ((dest_print_prop p) 80))
    | NONE   => NONE
    val l1 = List.filter is_first_prop propl
    val l2 = List.filter is_next_prop propl
  in
    case (l1,l2) of
      ([],[]) => [SmlUnit s]
    | ([fprop],[]) =>
      let val ftreel = extract_smlexp_aux (dest_first_prop fprop) in
        [SmlExp (s,ftreel)]
      end
    | ([],[nprop]) =>
      let val ntreel = extract_smlexp_aux (dest_next_prop nprop) in
        SmlUnit s :: ntreel
      end
    | ([fprop],[nprop]) =>
      let
        val ftreel = extract_smlexp_aux (dest_first_prop fprop)
        val ntreel = extract_smlexp_aux (dest_next_prop nprop)
      in
        SmlExp (s,ftreel) :: ntreel
      end
    | _ => raise ERR "extract_smlexp_aux" ""
  end

fun extract_smlexp s =
  let val propll = sml_propl_all_of s in
    if List.length propll = 1
    then extract_smlexp_aux (hd propll)
    else raise ERR "extract_smlexp" s
  end

(* -------------------------------------------------------------------------
   Tactic tree
   ------------------------------------------------------------------------- *)

datatype tacexp =
    SmlInfix of string * (tacexp * tacexp)
  | SmlTactical of string
  | SmlTactic of string

fun size_of_tacexp tacexp = case tacexp of
    SmlInfix (_,(e1,e2)) => size_of_tacexp e1 + size_of_tacexp e2
  | SmlTactical _ => 0
  | SmlTactic _ => 1

fun is_infixr s =
  let val sl = partial_sml_lexer s in
    String.isPrefix "sml_infixr" (singleton_of_list sl)
  end

fun is_infixl s =
  let val sl = partial_sml_lexer s in
    String.isPrefix "sml_infixl" (singleton_of_list sl)
  end

fun is_infix s =
  let val sl = partial_sml_lexer s in
    String.isPrefix "sml_infix" (singleton_of_list sl)
  end

fun dest_infix e = case e of
    SmlExp (_, el) =>
    if not (length el = 3 andalso is_infix
      (string_of_smlexp (List.nth (el,1))))
    then raise ERR "dest_infix" "unexpected"
    else triple_of_list el
   | SmlUnit _ => raise ERR "dest_infix" "unexpected"

fun extract_tacexp_aux smlexp = case smlexp of
    SmlExp (SOME s, el) =>
    (
    if length el = 3 andalso is_infixl (string_of_smlexp (List.nth (el,1)))
    then
    let
      val (a,inf,b) = triple_of_list el
      val (a0,ainf,a1) = dest_infix (List.nth (el,0))
      val infs = string_of_smlexp inf
      val ainfs = string_of_smlexp ainf
      val a1s = string_of_smlexp a1
    in
      SmlInfix (infs,
        (
        SmlInfix (ainfs, (extract_tacexp_aux a0, SmlTactical a1s)),
        extract_tacexp_aux b
        )
      )
    end
    else if length el = 3 andalso
      is_infixr (string_of_smlexp (List.nth (el,1)))
    then
       let
         val (a,inf,b) = triple_of_list el
         val (b0,binf,b1) = dest_infix (List.nth (el,2))
         val infs = string_of_smlexp inf
         val binfs = string_of_smlexp binf
         val b0s = string_of_smlexp b0
       in
         SmlInfix (infs,
           (
           extract_tacexp_aux a,
           SmlInfix (binfs, (SmlTactical b0s, extract_tacexp_aux b1))
           )
         )
       end
    else SmlTactic (constant_space s)
    )
  | SmlUnit (SOME s) => SmlTactic (constant_space s)
  | _ => raise ERR "extract_tacticl_aux" "option"

fun extract_tacexp s =
  if not (is_tactic s) then raise ERR "extract_tacexp" "not a tactic" else
  let
    val e1 = (singleton_of_list o extract_smlexp) s
    val e2 = (singleton_of_list o snd o dest_smlexp) e1
  in
    extract_tacexp_aux e2
  end

fun string_of_tacexp e = case e of
    SmlInfix (s,(e1,e2)) =>
    "( " ^ string_of_tacexp e1 ^ " " ^ s ^ " " ^ string_of_tacexp e2 ^ " )"
  | SmlTactic s => s
  | SmlTactical s => s

end (* struct *)
