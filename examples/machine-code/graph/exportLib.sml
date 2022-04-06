structure exportLib :> exportLib =
struct

open HolKernel boolLib bossLib Parse;
open helperLib graph_specsLib backgroundLib writerLib file_readerLib;
open GraphLangTheory;


(* exporter state *)

val failed_ty_translations = ref ([]:hol_type list);
val failed_tm_translations = ref ([]:term list);


(* recording errors *)

local
  fun head_of t = fst (strip_comb t)
  fun print_ty_fail ty = let
    val _ = print "FAILED to translate type: "
    val _ = print_type ty
    val _ = print "\n"
    in () end;
  fun print_tm_fail tm = let
    val _ = print "FAILED to translate term: "
    val _ = print_term tm
    val _ = (print "\n\nwith head: "; print_term (head_of tm))
    val _ = (print "\nwith type: "; print_type (type_of tm); print "\n\n")
    in () end;
in
  fun add_ty_fail ty = let
    val _ = (failed_ty_translations := ty::(!failed_ty_translations))
    in print_ty_fail ty end
  fun add_tm_fail tm = let
    val _ = (failed_tm_translations := tm::(!failed_tm_translations))
    in print_tm_fail tm end
end


(* syntax functions *)

fun dest_graph tm =
  if can (match_term ``graph (xs:('a # 'b) list)``) tm then let
    val (x,y) = dest_comb tm
    fun f (x,y) = (numSyntax.int_of_term x, y)
    in listSyntax.dest_list y |> fst |> map (f o pairSyntax.dest_pair) end
    handle HOL_ERR _ => failwith "dest_graph"
  else failwith "dest_graph"

fun dest_str_graph tm =
  if can (match_term ``graph (xs:('a # 'b) list)``) tm then let
    val (x,y) = dest_comb tm
    fun f (x,y) = (stringSyntax.fromHOLstring x, y)
    in listSyntax.dest_list y |> fst |> map (f o pairSyntax.dest_pair) end
    handle HOL_ERR _ => failwith "dest_graph"
  else failwith "dest_graph"

fun dest_string_list tm = let
  val (xs,ty) = listSyntax.dest_list tm
  val _ = (ty = ``:string``) orelse fail()
  val ys = map stringSyntax.fromHOLstring xs
  in ys end handle HOL_ERR _ => failwith "dest_string_list"

local
  val pat = ``GraphFunction inps outps gg ep``
in
  fun dest_GraphFunction tm = let
    val _ = can (match_term pat) tm orelse fail()
    val ep = tm |> rand |> numSyntax.int_of_term
    val gs = tm |> rator |> rand |> dest_graph
    val ys = tm |> rator |> rator |> rand |> dest_string_list
    val xs = tm |> rator |> rator |> rator |> rand |> dest_string_list
    in (xs,ys,gs,ep) end
end

local
  val pat = ``Basic n xs``
in
  fun dest_Basic tm = let
    val _ = can (match_term pat) tm orelse fail()
    val next = tm |> rator |> rand
    val (xs,ty) = tm |> rand |> listSyntax.dest_list
    val _ = (ty = ``:string # (32 state -> 32 variable)``) orelse
            (ty = ``:string # (64 state -> 64 variable)``) orelse fail()
    val ys = xs |> map pairSyntax.dest_pair
                |> map (fn (x,y) => (stringSyntax.fromHOLstring x,y))
    in (next,ys) end
end

local
  val pat = ``Cond n1 n2 p``
in
  fun dest_Cond tm = let
    val _ = can (match_term pat) tm orelse fail()
    val next1 = tm |> rator |> rator |> rand
    val next2 = tm |> rator |> rand
    val tm = tm |> rand
    in (next1,next2,tm) end
end

local
  val pat = ``Call next name args strs``
in
  fun dest_Call tm = let
    val _ = can (match_term pat) tm orelse fail()
    val next = tm |> rator  |> rator  |> rator |> rand
    val (strs,ty) = tm |> rand |> listSyntax.dest_list
    val _ = (ty = ``:string``) orelse fail()
    val strs = strs |> map stringSyntax.fromHOLstring
    val name = tm |> rator |> rator |> rand |> stringSyntax.fromHOLstring
    val (args,ty) = tm |> rator |> rand |> listSyntax.dest_list
    val _ = (ty = ``:32 state -> 32 variable``) orelse
            (ty = ``:64 state -> 64 variable``) orelse
            fail()
    in (next,name,args,strs) end
end

local
  val pat = ``NextNode n``
in
  fun dest_NextNode tm = let
    val _ = can (match_term pat) tm orelse fail()
    val next = tm |> rand |> numSyntax.int_of_term
    in next end
end

local
  val pat = ``var_acc str``
in
  fun dest_var_acc tm = let
    val _ = can (match_term pat) tm orelse fail()
    in tm |> rand |> stringSyntax.fromHOLstring end
end

local
  val pat = ``SKIP_TAG str``
in
  fun dest_SKIP_TAG tm = let
    val _ = can (match_term pat) tm orelse fail()
    in tm |> rand |> stringSyntax.fromHOLstring end
end

local
  fun any_var_acc pat = fn tm => let
    val _ = can (match_term pat) tm orelse fail()
    val x1 = tm |> rator |> rand |> stringSyntax.fromHOLstring
    val x2 = tm |> rand
    in (x1,x2) end
in
  val dest_var_word = any_var_acc ``var_word str s``
  val dest_var_word8 = any_var_acc ``var_word8 str s``
  val dest_var_nat = any_var_acc ``var_nat str s``
  val dest_var_bool = any_var_acc ``var_bool str s``
  val dest_var_mem = any_var_acc ``var_mem str s``
  val dest_var_dom = any_var_acc ``var_dom str s``
end;


(* export to Graph's graph format *)

val patterns =
     [(``MemAcc8 m a``,"MemAcc"),
      (``MemAcc32 m a``,"MemAcc"),
      (``MemAcc64 m a``,"MemAcc"),
      (``MemUpdate8 m a w``,"MemUpdate"),
      (``MemUpdate32 m a w``,"MemUpdate"),
      (``MemUpdate64 m a w``,"MemUpdate"),
      (``x = (y:'a)``,"Equals"),
      (``T``,"True"),
      (``F``,"False"),
      (``~(b:bool)``,"Not"),
      (``word_1comp (x:'a word)``,"BWNot"),
      (``word_add (x:'a word) y``,"Plus"),
      (``word_sub (x:'a word) y``,"Minus"),
      (``word_mul (x:'a word) y``,"Times"),
      (``UnsignedDiv (x:'a word) y``,"UnsignedDiv"),
      (``SignedDiv (x:'a word) y``,"SignedDiv"),
      (``word_and (x:'a word) y``,"BWAnd"),
      (``word_or (x:'a word) y``,"BWOr"),
      (``word_xor (x:'a word) y``,"BWXOR"),
      (``word_ror (x:'a word) y``,"RotateRight"),
      (``ShiftLeft (x:'a word) y``,"ShiftLeft"),
      (``ShiftRight (x:'a word) y``,"ShiftRight"),
      (``SignedShiftRight (x:'a word) y``,"SignedShiftRight"),
      (``x ==> y:bool``,"Implies"),
      (``x /\ y:bool``,"And"),
      (``x \/ y:bool``,"Or"),
      (``(x:'a word) < y``,"SignedLess"),
      (``(x:'a word) <+ y``,"Less"),
      (``(x:'a word) <= y``,"SignedLessEquals"),
      (``(x:'a word) <=+ y``,"LessEquals"),
      (``(x:'a word) IN y``,"MemDom"),
      (``(w2w (x:'a word)):'b word``,"WordCast"),
      (``(sw2sw (x:'a word)):'b word``,"WordCastSigned"),
      (``(n:num) + m``,"Plus"),
      (``if b then x else y : 'a``,"IfThenElse"),
      (``word_reverse (x:'a word)``,"WordReverse"),
      (``count_leading_zero_bits (w:'a word)``,"CountLeadingZeroes")];

val last_fail_node_tm = ref T;

fun export_graph name rhs = let
  fun int_to_hex i =
    "0x" ^ Arbnumcore.toHexString (Arbnum.fromInt i)
  fun get_var_type "mem" = "Mem"
    | get_var_type "dom" = "Dom"
    | get_var_type "stack" = "Mem"
    | get_var_type "dom_stack" = "Dom"
    | get_var_type "n" = "Bool"
    | get_var_type "z" = "Bool"
    | get_var_type "c" = "Bool"
    | get_var_type "v" = "Bool"
    | get_var_type "clock" = "Word 64"
    | get_var_type _ = "Word " ^ substring(type_to_string(tysize()),1,2)
  fun arg s = "" ^ s ^ " " ^ get_var_type s
  fun commas [] = ""
    | commas [x] = x
    | commas (x::xs) = x ^ " " ^ commas xs
  fun export_list xs = int_to_string (length xs) ^ " " ^ commas xs
  fun export_type ty = case total dest_type ty of
    SOME ("cart", [_, idx]) => "Word "
        ^ Arbnum.toString (fcpLib.index_to_num idx)
  | _ => if ty = ``:word32->word8`` then "Mem" else
         if ty = ``:word32->bool`` then "Dom" else
         if ty = ``:word64->word8`` then "Mem" else
         if ty = ``:word64->bool`` then "Dom" else
         if ty = ``:bool`` then "Bool" else
         if ty = ``:num`` then "Word 64" else failwith("type")
  fun is_var_acc tm =
    can dest_var_word tm orelse
    can dest_var_word8 tm orelse
    can dest_var_nat tm orelse
    can dest_var_bool tm orelse
    can dest_var_mem tm orelse
    can dest_var_dom tm
  fun match_pattern tm [] = fail()
    | match_pattern tm ((pat,name)::xs) =
        if not (can (match_term pat) tm) then match_pattern tm xs else let
          val (s1,s2) = match_term pat tm
          val cs = filter is_var (list_dest dest_comb pat)
          in (name,map (subst s1 o inst s2) cs) end
  fun term tm =
    (* Num *)
    (if numSyntax.is_numeral tm then
      "Num " ^ int_to_string (tm |> numSyntax.int_of_term) ^ " Nat"
    else if wordsSyntax.is_n2w tm then
      let val i = tm |> rand |> numSyntax.dest_numeral
      in "Num " ^ Arbnum.toString i ^ " " ^ export_type (type_of tm) end
    (* Var *)
    else if is_var_acc tm then
      let val name = tm |> rator |> rand |> stringSyntax.fromHOLstring
      in "Var " ^ name ^ " " ^ export_type (type_of tm) end
    (* Op *)
    else let
      val (n,xs) = match_pattern tm patterns
      val ty = export_type (type_of tm)
      in "Op " ^ n ^ " " ^ ty ^ " " ^ export_list (map term xs) end
    ) handle HOL_ERR err => (print (exn_to_string (HOL_ERR err));
            add_tm_fail tm; fail())
  val types = [``VarNat :num -> 'a variable``,
               ``VarWord8 :word8 -> 'a variable``,
               ``VarWord :'a word -> 'a variable``,
               ``VarMem :('a word -> word8) -> 'a variable``,
               ``VarDom :('a word -> bool) -> 'a variable``,
               ``VarBool :bool -> 'a variable``]
  fun bool_exp tm =
    if can dest_var_acc tm then let
      val n = dest_var_acc tm
      in "Var " ^ n ^ " " ^ get_var_type n end
    else let
      val (s,e) = dest_abs tm
      val _ = type_of s = ``:32 state`` orelse
              type_of s = ``:64 state`` orelse failwith("bad exp")
      val _ = type_of e = ``:bool`` orelse failwith("bad exp")
      in term e end
  fun exp tm =
    if can dest_var_acc tm then let
      val n = dest_var_acc tm
      in "Var " ^ n ^ " " ^ get_var_type n end
    else let
      val (s,e) = dest_abs tm
      val _ = type_of s = ``:32 state`` orelse
              type_of s = ``:64 state`` orelse failwith("bad exp")
      val (t,tm) = dest_comb e
      val _ = term_mem t types
      in term tm end
  fun dest_abs_skip_tag test = let
    val (v,x) = dest_abs test
    val n = dest_SKIP_TAG x
    in n end
  fun assign_var (n,tm) =
    "" ^ n ^ " " ^ get_var_type n ^ " " ^ exp tm
  val ret_node = ``Ret``
  val err_node = ``Err``
  fun export_nextnode (tm:term) =
    if aconv tm ret_node then "Ret" else
    if aconv tm err_node then "Err" else let
      val i = dest_NextNode tm
      in int_to_hex i end
  fun export_node (n,tm) = let
    val (next,assign) = dest_Basic tm
    in commas [int_to_hex n,"Basic",export_nextnode next,
               export_list (map assign_var assign)] ^ "\n" end
    handle HOL_ERR _ => let
    val (next1,next2,test) = dest_Cond tm
    in if can dest_abs_skip_tag test then
         "# " ^ int_to_hex n ^ " node is " ^
         dest_abs_skip_tag test ^ "\n" ^
         commas [int_to_hex n,"Cond",
                 export_nextnode next1,
                 export_nextnode next2,
                 "Op UnspecifiedPrecond Bool 0"] ^ "\n"
       else
         commas [int_to_hex n,"Cond",
                 export_nextnode next1,
                 export_nextnode next2,
                 bool_exp test] ^ "\n" end
    handle HOL_ERR _ => let
    val (next,func_name,input,output) = dest_Call tm
    in commas [int_to_hex n,"Call",
               export_nextnode next,
               func_name,
               export_list (map exp input),
               export_list (map arg output)] ^ "\n" end
  val rhs = rhs |> QCONV (REWRITE_CONV [graph_format_preprocessing])
                |> concl |> rand
  val (input,output,nodes,entry) = dest_GraphFunction rhs
  val decl = "Function " ^ name ^ " " ^
                export_list (map arg input) ^ " " ^
                export_list (map arg output) ^ "\n"
  val _ = write_graph decl
  fun my_map f [] = []
    | my_map f (x::xs) =
    ((let val y = f x in y end
      handle Overflow => failwith "Overflow")
     handle HOL_ERR e =>
     let val _ = print "\n\nFailed to translate node: \n\n"
         val _ = print_term (snd x)
         val _ = print "\n\n"
         val _ = (last_fail_node_tm := snd x)
     in raise (HOL_ERR e) end) :: my_map f xs
  val _ = my_map (write_graph o export_node) nodes
  val last_line = "EntryPoint " ^ int_to_hex entry ^ "\n"
  val _ = if List.null nodes then () else write_graph last_line
  in () end

(*
val tm = !last_fail_node_tm
*)


(* export constant definition *)

fun export_func lemma = let
  val (lhs,rhs) = lemma |> concl |> dest_eq
  val name = lhs |> dest_const |> fst |> clean_name
  val _ = export_graph name rhs
  in "define_" ^ name end


(* print export report *)

fun print_export_report () = let
  val l = length (!failed_ty_translations) + length (!failed_tm_translations)
  in if l = 0 then write_line "No export failures." else let
       val _ = has_failures := true
       val xs = map (fn ty => "Failed to translate type: " ^ type_to_string ty)
                       (all_distinct (!failed_ty_translations)) @
                map (fn tm => "Failed to translate term: " ^ term_to_string tm)
                       (term_all_distinct (!failed_tm_translations))
       in (map write_line xs; ()) end end


(* conv used by func_decompiler *)

val prepare_for_export_conv = let
  fun unbeta_conv pat tm =
    if is_comb tm andalso can (match_term pat) (rand tm) then let
      val ty = rand tm |> type_of |> dest_type |> snd |> hd
      in (RAND_CONV (REWR_CONV (GSYM ETA_AX))) tm end else NO_CONV tm
  val foldback = (unbeta_conv ``var_bool str``) ORELSEC
                 (unbeta_conv ``var_word str``) ORELSEC
                 (unbeta_conv ``var_word8 str``) ORELSEC
                 (unbeta_conv ``var_nat str``) ORELSEC
                 (unbeta_conv ``var_mem str``) ORELSEC
                 (unbeta_conv ``var_dom str``)
  val c = PURE_REWRITE_CONV [decomp_simp1,all_names_def,
            ret_and_all_names_def,
            all_names_ignore_def, all_names_with_input_def] THENC
          PURE_REWRITE_CONV [decomp_simp2] THENC
          PURE_REWRITE_CONV [decomp_simp3] THENC
          PURE_REWRITE_CONV [GSYM wordsTheory.WORD_NOT_LOWER,v2w_sing,
                             wordsTheory.WORD_HIGHER_EQ,
                             wordsTheory.WORD_HIGHER,
                             wordsTheory.WORD_GREATER_EQ,
                             wordsTheory.WORD_GREATER] THENC
          DEPTH_CONV foldback
  in QCONV c end;

end
