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
   Property tests
   ------------------------------------------------------------------------- *)

fun is_print p = case p of PolyML.PTprint _ => true | _ => false
fun is_type p = case p of PolyML.PTtype _ => true | _ => false
fun is_firstchild p = case p of PolyML.PTfirstChild _ => true | _ => false
fun is_nextsibling p = case p of PolyML.PTnextSibling _ => true | _ => false

(* -------------------------------------------------------------------------
   Property destructors
   ------------------------------------------------------------------------- *)

fun dest_firstchild p = case p of
    PolyML.PTfirstChild f  => snd (f ())
  | _               => raise ERR "dest_firstchild" ""

fun dest_print p = case p of
    PolyML.PTprint f  => f
  | _               => raise ERR "dest_print" ""

fun dest_type p = case p of
   PolyML.PTtype ty => ty
  | _ => raise ERR "dest_type" ""

fun dest_firstchild p = case p of
    PolyML.PTfirstChild g => snd (g ())
  | _ => raise ERR "dest_firstchild" ""

fun dest_nextsibling p = case p of
    PolyML.PTnextSibling g => snd (g ())
  | _ => raise ERR "dest_nextsibling" ""

(* -------------------------------------------------------------------------
   Printing functions
   ------------------------------------------------------------------------- *)

fun respace s = String.concatWith " " (partial_sml_lexer s)

fun string_of_pretty pretty =
   let
    val acc = ref []
    fun f s = acc := s :: !acc
  in
    PolyML.prettyPrint (f,80) pretty;
    respace (String.concatWith " " (rev (!acc)))
  end 

fun string_of_print p = string_of_pretty ((dest_print p) 80)

fun string_of_type ty =
  let
    val pretty = PolyML.NameSpace.Values.printType 
      (ty, 80, SOME PolyML.globalNameSpace)
  in 
    respace (string_of_pretty pretty)
  end

fun string_of_propl pl = case List.find is_print pl of
    SOME p => SOME (string_of_print p)
  | NONE   => NONE

fun stype_of_propl pl = case List.find is_type pl of
    SOME (PolyML.PTtype ty) => SOME (string_of_type ty) 
  | _ => NONE

(* -------------------------------------------------------------------------
   Calling the PolyML compiler
   ------------------------------------------------------------------------- *)

fun parse s =
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
        fn () => raise ERR "parse" ""
      end
    val _ = PolyML.compiler (fn () =>
          TextIO.input1 stream,
         [PolyML.Compiler.CPCompilerResultFun compilerResultFun,
          PolyML.Compiler.CPNameSpace PolyML.globalNameSpace])
    in
      dest_firstchild 
        (singleton_of_list (snd (singleton_of_list (!resultTrees))))
    end

(* -------------------------------------------------------------------------
   Simplified parsed tree with type information
   ------------------------------------------------------------------------- *)

datatype smlexp =
    SmlExp of (string option * string option) * smlexp list
  | SmlUnit of (string option * string option)

fun dest_smlexp e = case e of
    SmlExp x => x
  | _ => raise ERR "dest_smlexp" ""

fun string_of_smlexp e = case e of
   SmlExp ((SOME s,_),_) => s
 | SmlUnit (SOME s,_) => s
 | _ => raise ERR "string_of_smlexp" ""

fun extract_smlexp_aux propl =
  let 
    val s = string_of_propl propl
    val sty = stype_of_propl propl
    val l1 = List.filter is_firstchild propl
    val l2 = List.filter is_nextsibling propl
  in
    case (l1,l2) of
      ([],[]) => [SmlUnit (s,sty)]
    | ([fprop],[]) =>
      let val ftreel = extract_smlexp_aux (dest_firstchild fprop) in
        [SmlExp ((s,sty),ftreel)]
      end
    | ([],[nprop]) =>
      let val ntreel = extract_smlexp_aux (dest_nextsibling nprop) in
        SmlUnit (s,sty) :: ntreel
      end
    | ([fprop],[nprop]) =>
      let
        val ftreel = extract_smlexp_aux (dest_firstchild fprop)
        val ntreel = extract_smlexp_aux (dest_nextsibling nprop)
      in
        SmlExp ((s,sty),ftreel) :: ntreel
      end
    | _ => raise ERR "extract_smlexp_aux" ""
  end

fun extract_smlexp s = singleton_of_list (extract_smlexp_aux (parse s))

(* -------------------------------------------------------------------------
   Proof tree separated into tactic units
   ------------------------------------------------------------------------- *)

datatype proofexp =
    ProofInfix of string * (proofexp * proofexp)
  | ProofTactical of string
  | ProofTactic of string
  | ProofOther of string

fun size_of_proofexp proofexp = case proofexp of
    ProofInfix (_,(e1,e2)) => size_of_proofexp e1 + size_of_proofexp e2
  | ProofTactical _ => 0
  | ProofTactic _ => 1
  | ProofOther _ => 0

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
    SmlExp (_,[a,b,c]) =>
    if not (is_infix (string_of_smlexp b))
    then raise ERR "dest_infix" "unexpected"
    else (a,b,c)
   | _ => raise ERR "dest_infix" "unexpected"

fun extract_proofexp_aux smlexp = case smlexp of
    SmlExp ((SOME s,_),[a,inf,b]) =>
    if is_infixl (string_of_smlexp inf) then
    let
      val (a0,ainf,a1) = dest_infix a
      val infs = string_of_smlexp inf
      val ainfs = string_of_smlexp ainf
      val a1s = string_of_smlexp a1
    in
      ProofInfix (infs,
        (
        ProofInfix (ainfs, (extract_proofexp_aux a0, ProofTactical a1s)),
        extract_proofexp_aux b
        )
      )
    end
    else if is_infixr (string_of_smlexp inf) then
       let
         val (b0,binf,b1) = dest_infix b
         val infs = string_of_smlexp inf
         val binfs = string_of_smlexp binf
         val b0s = string_of_smlexp b0
       in
         ProofInfix (infs,
           (
           extract_proofexp_aux a,
           ProofInfix (binfs, (ProofTactical b0s, extract_proofexp_aux b1))
           )
         )
       end
    else (if is_tactic s then ProofTactic s else ProofOther s)
  | SmlExp ((SOME s,_),_) => 
    if is_tactic s then ProofTactic s else ProofOther s
  | SmlUnit (SOME s,_) =>  
    if is_tactic s then ProofTactic s else ProofOther s
  | _ => raise ERR "extract_tacticl_aux" "option"

fun extract_proofexp s =
  if not (is_tactic s) 
  then raise ERR "extract_proofexp" "not a tactic" 
  else extract_proofexp_aux (extract_smlexp s)

fun safe_par s = 
  if mem #" " (explode s) 
  then String.concatWith " " ["(",s,")"]
  else s

fun string_of_proofexp e = case e of
    ProofInfix (s,(e1,e2)) => String.concatWith " " 
      ["(",string_of_proofexp e1,s,string_of_proofexp e2,")"]
  | ProofTactic s => safe_par s
  | ProofOther s => safe_par s
  | ProofTactical s => safe_par s

(* -------------------------------------------------------------------------
   Tactic sketch. Break a sml expression into applications.
   ------------------------------------------------------------------------- *)

fun drop_all_sig stac = 
  String.concatWith " " (map drop_sig (partial_sml_lexer stac));

datatype applyexp =
    ApplyExp of applyexp * applyexp
  | ApplyUnit of (string * string option)

fun is_app s (s1,s2) = 
  let 
    val s1par = "( " ^ s1 ^ " )"  
    val s2par = "( " ^ s2 ^ " )"
    val s1parpar = "( " ^ s1par ^ " )"  
    val s2parpar = "( " ^ s2par ^ " )"

    val l = cartesian_product [s1,s1par,s1parpar] [s2,s2par,s2parpar]
    fun f (a,b) = a ^ " " ^ b
  in
    mem s (map f l)
  end

fun mk_applyexp smlexp = case smlexp of
    SmlExp ((SOME a, SOME b),[e1,e2]) =>
      if is_app a (string_of_smlexp e1, string_of_smlexp e2)
      then ApplyExp (mk_applyexp e1, mk_applyexp e2)
      else ApplyUnit (a, SOME (drop_all_sig b))
  | SmlExp ((SOME a, b), _) => ApplyUnit (a, Option.map drop_all_sig b)
  | SmlUnit (SOME a, b) => ApplyUnit (a, Option.map drop_all_sig b)
  | _ => raise ERR "mk_applyexp" ""

(*

load "mlTacticData"; open mlTacticData;
load "smlLexer"; open smlLexer;
load "tttSetup"; open tttSetup;

fun fst_app applyexp = case applyexp of
    ApplyExp (a,b) => fst_app a
  | ApplyUnit (s,_) => s
;

fun all_x x applyexp = case applyexp of
    ApplyExp (a,b) => all_x x a @ all_x x b
  | ApplyUnit (s,sty) => if isSome sty andalso valOf sty = x then [s] else [] 
;

val (l,t) = add_time (map_snd (mk_applyexp o extract_smlexp)) gstacl;
val lapp = map_snd fst_app l;

fun count_string x = 
  dict_sort compare_imax (dlist (count_dict (dempty String.compare) x));
fun count_int x = 
  dict_sort compare_imax (dlist (count_dict (dempty Int.compare) x));


val testedl = map fst (first_n 10 (count_string (map snd lapp)));

val oh = List.tabulate (10, 
  fn i => List.tabulate (10, fn j => if i = j then 1.0 else 0.0));

val assocl = combine (testedl,oh);
val data1 = mapfilter (fn (a,b) => (a, assoc b assocl)) lapp;
val data2 = map_fst nntm_of_goal data1;
val data3 = map single data2;
val (train,test) = part_pct 0.9 data3;

val operl = mk_fast_set oper_compare
  (List.concat (map operl_of_term (map fst data2)));
val operdiml = map (fn x => (fst x, dim_std_arity (1,4) x)) operl;
val operdiml2 = 
  map (fn (a,b) => 
   if term_eq a ``head_goal:bool -> bool`` then (a,[4,10]) else (a,b)) operdiml;

val randtnn = random_tnn operdiml2;

val trainparam =
  {ncore = 1, verbose = true,
   learning_rate = 0.04, batch_size = 16, nepoch = 100};
val schedule = [trainparam];
val tnn = train_tnn schedule randtnn (train,test);

val l2 = 
  dict_sort compare_imax (map (fn (a,b) => ((a,f b),length b)) (dlist d));
val rl = f (List.concat (map (all_x "thm list -> tactic") l));
val rl = f (map fst_app l);


*)



end (* struct *)
