structure type_grammar :> type_grammar =
struct

open HOLgrammars
open Lib
open type_grammar_dtype

fun typstruct_uptodate ts =
    case ts of
      PARAM _ => true
    | TYOP {Thy, Tyop, Args} => (
      case Type.op_arity {Thy = Thy, Tyop = Tyop} of
          SOME a => length Args = a andalso List.all typstruct_uptodate Args
        | _ => false
    )

type kernelname = KernelSig.kernelname

fun break_qident s =
  case String.fields (equal #"$") s of
      [ _ ] => (NONE, s)
    | [thy, nm] => (SOME thy, nm)
    | _ => raise GrammarError ("String \""^s^
                               "\" is not a valid type identifier")


datatype grammar = TYG of {
  rules : (int * grammar_rule) list,
  parse_str : (kernelname, type_structure) Binarymap.dict,
  str_print : (int * kernelname) TypeNet.typenet,
  bare_names : (string, string) Binarymap.dict,
  tstamp   : int
}

datatype ty_absyn =
         VTY of string
       | QTYOP of kernelname * ty_absyn list
(*

   Like term parsing, type parsing is handled in two phases:

   1. Concrete syntax (involving infixes and the special syntax for
      array-typeshere) is mapped to abstract syntax, the ty_absyn type
      above.  The infix rules are in the rules field.

      Along the way, bare names in the concrete syntax are mapped to
      "qualified" operators (the QTYOP constructor) using the
      bare_names map of the grammar.

   2. The parse_str field of the grammar is then used to turn QTYOPs
      into genuine type operators.

   Printing uses the str_print field to turn structures into syntactic
   structure names. If these are privileged, they get to print in bare
   form; otherwise they will be qualified.

   As with term overloads, more specific structure matches are
   preferred when turning underlying type operators into names, and
   the timestamp is used to break ties.

*)
open FunctionalRecordUpdate
fun tyg_mkUp z = makeUpdate5 z
fun update_G z = let
  fun from rules parse_str str_print bare_names tstamp =
    {rules = rules, parse_str = parse_str,
     str_print = str_print, bare_names = bare_names, tstamp = tstamp}
  (* fields in reverse order *)
  fun from' tstamp bare_names str_print parse_str rules =
    {rules = rules, parse_str = parse_str,
     str_print = str_print, bare_names = bare_names, tstamp = tstamp}
  (* first order *)
  fun to f {rules, parse_str, str_print, bare_names, tstamp} =
    f rules parse_str str_print bare_names tstamp
in
  tyg_mkUp (from, from', to)
end z

fun fupdate_rules f (TYG g) =
  TYG (update_G g (U #rules (f (#rules g))) $$)
fun fupdate_str_print f (TYG g) =
  TYG (update_G g (U #str_print (f (#str_print g))) $$)
fun fupdate_parse_str f (TYG g) =
  TYG (update_G g (U #parse_str (f (#parse_str g))) $$)
fun fupdate_tstamp f (TYG g) =
  TYG (update_G g (U #tstamp (f (#tstamp g))) $$)
fun fupdate_bare_names f (TYG g) =
  TYG (update_G g (U #bare_names (f (#bare_names g))) $$)

fun default_typrinter (G:grammar) (ty:Type.hol_type) =
  HOLPP.PrettyString "<a type>"

val type_printer = ref default_typrinter
val initialised_printer = ref false

fun initialise_typrinter f =
    if not (!initialised_printer) then
      (type_printer := f; initialised_printer := true)
    else
      raise Feedback.mk_HOL_ERR "type_grammar" "initialised_printer"
        "Printer function already initialised"

fun pp_type g ty = (!type_printer) g ty

fun structure_to_type st =
    case st of
      TYOP {Thy,Tyop,Args} =>
      Type.mk_thy_type {Thy = Thy, Tyop = Tyop,
                        Args = map structure_to_type Args}
    | PARAM n => Type.mk_vartype ("'"^str (chr (n + ord #"a")))

fun params0 acc (PARAM i) = HOLset.add(acc, i)
  | params0 acc (TYOP{Args,...}) = foldl (fn (t,set) => params0 set t) acc Args
val params = params0 (HOLset.empty Int.compare)

val num_params = HOLset.numItems o params

fun suffix_arity (abbrevs, privs) s =
  case Binarymap.peek (privs, s) of
      NONE => NONE
    | SOME thy =>
      let
      in
        case Binarymap.peek(abbrevs, {Thy = thy, Name = s}) of
            NONE => NONE (* shouldn't happen *)
          | SOME st => if typstruct_uptodate st then SOME (s, num_params st)
                       else NONE
      end

fun merge r1 r2 =
  case (r1, r2) of
    (INFIX(rlist1, a1), INFIX(rlist2, a2)) => let
    in
      if a1 = a2 then INFIX(Lib.union rlist1 rlist2, a1)
      else
        raise GrammarError
          "Attempt to merge two infix types with different associativities"
    end

fun insert_sorted (k, v) [] = [(k, v)]
  | insert_sorted kv1 (wholething as (kv2::rest)) = let
      val (k1, v1) = kv1
      val (k2, v2) = kv2
    in
      if (k1 < k2) then kv1::wholething
      else
        if k1 = k2 then  (k1, merge v1 v2) :: rest
        else
          kv2 :: insert_sorted kv1 rest
    end

fun new_binary_tyop g {precedence, infix_form = ix, opname, associativity = a} =
    let
      val rule = (precedence, INFIX([{parse_string = ix, opname = opname}], a))
    in
      g |> fupdate_rules (insert_sorted rule)
    end

fun remove_binary_tyop g s = let
  fun bad_irule {parse_string,...} = parse_string = s
  fun edit_rule (prec, r) =
      case r of
        INFIX (irules, assoc) => let
          val irules' = List.filter (not o bad_irule) irules
        in
          if null irules' then NONE
          else SOME (prec, INFIX (irules', assoc))
        end
in
  g |> fupdate_rules (List.mapPartial edit_rule)
end


fun new_qtyop (kid as {Name = name, Thy = thy}) g =
  let
    open Type Theory
  in
    case Type.op_arity {Tyop = name, Thy = thy} of
        NONE => raise GrammarError
                      (name ^ " is not the name of a type operator in theory "^
                       thy)
      | SOME i =>
        let
          val TYG {tstamp,...} = g
          val opstructure = TYOP {Thy = thy, Tyop = name,
                                  Args = List.tabulate(i, PARAM)}
          fun mk_vari i = mk_vartype ("'a" ^ Int.toString i)
          val ty =
              mk_thy_type {Tyop = name, Thy = thy,
                           Args = List.tabulate(i, mk_vari)}
        in
          g |> fupdate_str_print
                 (fn tynet => TypeNet.insert(tynet,ty,(tstamp,kid)))
            |> fupdate_parse_str (fn m => Binarymap.insert(m, kid, opstructure))
            |> fupdate_tstamp (fn i => i + 1)
            |> fupdate_bare_names (fn m => Binarymap.insert(m, name, thy))
        end
  end

fun hide_tyop s =
  fupdate_bare_names
    (fn m => #1 (Binarymap.remove(m,s)) handle Binarymap.NotFound => m)

val empty_grammar = TYG { rules = [],
                          parse_str = Binarymap.mkDict KernelSig.name_compare,
                          bare_names = Binarymap.mkDict String.compare,
                          str_print = TypeNet.empty,
                          tstamp = 0 }

fun keys m = Binarymap.foldr (fn (k,v,acc) => k :: acc) [] m

fun rules (TYG gr) = {infixes = #rules gr, suffixes = keys (#bare_names gr)}
fun parse_map (TYG gr) = #parse_str gr
fun print_map (TYG gr) = #str_print gr
fun privabbs (TYG gr) = #bare_names gr
val privileged_abbrevs = privabbs
fun tstamp (TYG gr) = #tstamp gr
fun bump_tstamp g = (tstamp g, fupdate_tstamp (fn n => n + 1) g)

fun check_structure st = let
  fun param_numbers (PARAM i, pset) = HOLset.add(pset, i)
    | param_numbers (TYOP{Args,...}, pset) = foldl param_numbers pset Args
  val pset = param_numbers (st, HOLset.empty Int.compare)
  val plist = HOLset.listItems pset
  fun check_for_gaps expecting [] = ()
    | check_for_gaps expecting (h::t) =
      if h <> expecting then
        raise GrammarError
                ("Expecting to find parameter #"^Int.toString expecting)
      else
        check_for_gaps (expecting + 1) t
in
  check_for_gaps 0 plist
end

fun remove_knm_abbreviation g knm = let
  val (dict, st) = Binarymap.remove(parse_map g, knm)
  fun doprint pmap0 = #1 (TypeNet.delete(pmap0, structure_to_type st))
                     handle Binarymap.NotFound => pmap0
  fun maybe_rmpriv d =
    case Binarymap.peek (d, #Name knm) of
        NONE => d
      | SOME thy' => if thy' = #Thy knm then #1 (Binarymap.remove(d, #Name knm))
                     else d
in
  g |> fupdate_parse_str (K dict)
    |> fupdate_str_print doprint
    |> fupdate_bare_names maybe_rmpriv
end

fun remove_abbreviation g s =
  let
    val (thyopt, nm) = break_qident s
    fun parsemap nmcheck (knm,st,acc) =
      if nmcheck knm then acc else Binarymap.insert(acc,knm,st)
    fun printmap nmcheck (ty,i as (_, knm),acc) =
        if nmcheck knm then acc else TypeNet.insert(acc,ty,i)
    fun thyprivrm thy m =
      case Binarymap.peek (m, nm) of
          NONE => m
        | SOME thy' => if thy' = thy then #1 (Binarymap.remove(m,nm))
                       else m
    val (check,privrm) =
        case thyopt of
            NONE => ((fn knm => #Name knm = nm),
                     (fn m => #1 (Binarymap.remove (m, nm))
                              handle Binarymap.NotFound => m))
          | SOME thy => (equal {Name = nm, Thy = thy}, thyprivrm thy)
  in
    g |> fupdate_bare_names privrm
      |> fupdate_str_print (TypeNet.fold (printmap check) TypeNet.empty)
      |> fupdate_parse_str
           (Binarymap.foldl (parsemap check)
                            (Binarymap.mkDict KernelSig.name_compare))
  end

fun type_to_structure ty =
  let
    open Type
    val params = Listsort.sort Type.compare (type_vars ty)
    val (num_vars, pset) =
        List.foldl (fn (ty,(i,pset)) => (i + 1, Binarymap.insert(pset,ty,i)))
                   (0, Binarymap.mkDict Type.compare) params
    fun mk_structure pset ty =
      if is_vartype ty then PARAM (Binarymap.find(pset, ty))
      else let
        val {Thy,Tyop,Args} = dest_thy_type ty
      in
        TYOP {Thy = Thy, Tyop = Tyop, Args = map (mk_structure pset) Args}
      end
  in
    mk_structure pset ty
  end


fun new_abbreviation {knm,print,ty} tyg = let
  open Portable
  val st = type_to_structure ty
  val {Name = s, Thy = thy} = knm
  val tyg = case Binarymap.peek(parse_map tyg, knm) of
                NONE => tyg
              | SOME st' =>
                if st = st' then tyg
                else
                  let
                    val tyg' = remove_knm_abbreviation tyg knm
                  in
                    Feedback.HOL_WARNING
                      "type_grammar"
                      "new_abbreviation"
                      ("Replacing old mapping from " ^ s ^ " to "^
                       PP.pp_to_string (!Globals.linewidth)
                                       (pp_type tyg')
                                       (structure_to_type st'));
                    tyg'
                  end
  val _ = case st of PARAM _ =>
                     raise GrammarError
                               "Abbreviation can't be to a type variable"
                   | _ => ()
  val (tstamp, tyg) = bump_tstamp tyg
  val result =
    tyg |> fupdate_parse_str (fn d => Binarymap.insert(d,knm,st))
        |> (print ?
            fupdate_str_print
             (fn pmap => TypeNet.insert(pmap,
                                        structure_to_type st,
                                        (tstamp, knm))))
        |> fupdate_bare_names(fn d => Binarymap.insert(d,s,thy))
in
  result
end


fun rev_append [] acc = acc
  | rev_append (x::xs) acc = rev_append xs (x::acc)

fun merge_abbrevs G (d1, d2) = let
  fun merge_dictinsert (k,v,newdict) =
      case Binarymap.peek(newdict,k) of
        NONE => Binarymap.insert(newdict,k,v)
      | SOME v0 =>
        if v0 <> v then
          (Feedback.HOL_WARNING "parse_type" "merge_grammars"
                                ("Conflicting entries for op/abbrev "^
                                 KernelSig.name_toString k ^
                                 "; arbitrarily keeping map to "^
                                 PP.pp_to_string (!Globals.linewidth)
                                                 (pp_type G)
                                                 (structure_to_type v0));
           newdict)
        else
          newdict
in
    Binarymap.foldr merge_dictinsert d1 d2
end

fun merge_pmaps (p1, p2) =
    TypeNet.fold (fn (ty,v,acc) => TypeNet.insert(acc,ty,v)) p1 p2

fun merge_privs (p1, p2) =
  Binarymap.foldl (fn (nm,thy,acc) => Binarymap.insert(acc,nm,thy)) p1 p2

fun merge_grammars (G1, G2) = let
  (* both grammars are sorted, with no adjacent suffixes *)
  val TYG { rules = grules1, parse_str = abbrevs1,
            str_print = pmap1, tstamp = t1, bare_names = priv1 } = G1
  val TYG { rules = grules2, parse_str = abbrevs2,
            str_print = pmap2, tstamp = t2, bare_names = priv2 } = G2
  fun merge_acc acc (gs as (g1, g2)) =
    case gs of
      ([], _) => rev_append acc g2
    | (_, []) => rev_append acc g1
    | ((g1rule as (g1k, g1v))::g1rest, (g2rule as (g2k, g2v))::g2rest) => let
      in
        case Int.compare (g1k, g2k) of
          LESS => merge_acc (g1rule::acc) (g1rest, g2)
        | GREATER => merge_acc (g2rule::acc) (g1, g2rest)
        | EQUAL => merge_acc ((g1k, merge g1v g2v)::acc) (g1rest, g2rest)
      end
in
  TYG { rules = merge_acc [] (grules1, grules2),
        parse_str = merge_abbrevs G2 (abbrevs1, abbrevs2),
        str_print = merge_pmaps (pmap1, pmap2),
        bare_names = merge_privs (priv1, priv2),
        tstamp = Int.max(t1,t2) + 1 }
end

fun can_print pmap kns ty =
  let
    val net_matches = TypeNet.match(pmap, ty)
    fun check_match (pat, (tstamp, nm)) =
      can (Type.match_type pat) ty andalso nm = kns
  in
    not (null (List.filter check_match net_matches))
  end

fun prettyprint_grammar G = let
  open Portable Lib HOLPP
  val TYG grm = G
  val {rules=g, parse_str=abbrevs, str_print=pmap, bare_names,... } = grm
  fun print_suffix (s,arity) = let
    fun print_ty_n_tuple n =
        case n of
          0 => []
        | 1 => [add_string "TY", add_break (1,0)]
        | n => [add_string "(",
                block INCONSISTENT 0
                      (tabulateWith (fn _ => add_string "TY")
                                    [add_string ",", add_break(1,0)]
                                    n),
                add_string ")", add_break(1,0)]
  in
    block CONSISTENT 2
          (print_ty_n_tuple arity @ [add_string s])
  end

  fun print_abbrev lwidth (kid, kidstr0, st) = let
    val kidstr = UTF8.padRight #" " (lwidth + 4) kidstr0
    val ty = structure_to_type st
    val printed = can_print pmap kid ty
    val ty_string = PP.pp_to_string 100
                      (Feedback.trace ("print_tyabbrevs", 0) (pp_type G))
                      ty
  in
    block INCONSISTENT 0 (
      add_string kidstr :: add_string "=" :: add_break(1,0) ::
      add_string (UTF8.padRight #" " (35 - lwidth) ty_string) ::
      (if not printed then
         [add_break(1,lwidth + 6), add_string "[not printed]"]
       else [])
    )
  end

  fun kid_string kid st =
    let
      val ispriv = case Binarymap.peek (bare_names, #Name kid) of
                       SOME thy => thy = #Thy kid
                     | NONE => false
      val kns = if ispriv then #Name kid else KernelSig.name_toString kid
      val paramstr = PP.pp_to_string 100 (pp_type G) o structure_to_type o PARAM
    in
      case num_params st of
          0 => kns
        | 1 => paramstr 0 ^ " " ^ kns
        | n => "(" ^ String.concatWith ", " (List.tabulate(n, paramstr)) ^
               ") " ^ kns
    end

  val print_abbrevs = let
    fun foldthis (k,st,acc as (mx,kstrs)) =
        if typstruct_uptodate st then
          let
            val kstr = kid_string k st
          in
            (Int.max(mx,size kstr), (k,kstr,st)::kstrs)
          end
        else acc
    val (lwidth, okabbrevs) = Binarymap.foldl foldthis (0, []) abbrevs
  in
    if length okabbrevs > 0 then [
      NL, add_string "Type abbreviations:",
      add_break(2,2),
      block CONSISTENT 0 (
        pr_list (print_abbrev lwidth) [NL] (List.rev okabbrevs)
      )
    ]
    else []
  end

  fun print_infix {opname,parse_string} =
    block INCONSISTENT 0 (
      [add_string "TY ",add_string parse_string,add_break(1,0),add_string "TY"]@
      (if opname <> parse_string then
         [add_break(1,0), add_string ("["^opname^"]")]
       else [])
    )

  fun print_suffixes slist = let
    val oksl = List.mapPartial (suffix_arity (abbrevs, bare_names)) slist
  in
    if null oksl then []
    else
      [
        block INCONSISTENT 0 [
          add_string "       TY  ::=  ",
          block INCONSISTENT 16 (
            pr_list print_suffix [add_string " |", add_break(1,0)] oksl
          )
        ]
      ]
  end

  fun print_rule0 r =
    case r of
      INFIX(oplist, assoc) => let
        val assocstring =
            case assoc of
              LEFT => "L-"
            | RIGHT => "R-"
            | NONASSOC => "non-"
      in
        [add_string "TY  ::=  ",
         block INCONSISTENT 0
               (pr_list print_infix [add_string " |", add_break(1,0)] oplist @
                [add_string (" ("^assocstring^"associative)")])]
      end
  fun print_rule (n, r) = let
    val precstr = StringCvt.padRight #" " 7 ("("^Int.toString n^")")
  in
    block CONSISTENT 0 (add_string precstr :: print_rule0 r)
  end
in
  block CONSISTENT 0 (
    block CONSISTENT 0 [
      add_string "Rules:",
      add_break (1,2),
      block CONSISTENT 0 (
        pr_list print_rule [NL] g @ [add_break(1,0)] @
        print_suffixes (keys bare_names) @
        [add_break(1,0), add_string "       TY  ::=  TY[TY] (array type)"]
      )
    ] :: print_abbrevs
  )
end;

val print_abbrevs = ref true
val _ = Feedback.register_btrace ("print_tyabbrevs", print_abbrevs)

fun tysize ty =
    if Type.is_vartype ty then 1
    else let
        val {Args,...} = Type.dest_thy_type ty
      in
        1 + List.foldl (fn (ty,acc) => tysize ty + acc) 0 Args
      end

fun dest_type' ty = let
  val {Thy, Tyop, Args} = Type.dest_thy_type ty
in
  {Thy = SOME Thy, Tyop = Tyop, Args = Args}
end

fun abb_dest_type0 (TYG{str_print = pmap, bare_names, ...}) ty = let
  open HolKernel
  val net_matches = TypeNet.match(pmap, ty)
  fun mymatch pat ty = let
    val (i, sames) = Type.raw_match_type pat ty ([], [])
  in
    i @ (map (fn ty => ty |-> ty) sames)
  end
  fun check_match (pat, (tstamp, nm)) =
      SOME(mymatch pat ty, nm, tstamp) handle HOL_ERR _ => NONE
  val checked_matches = List.mapPartial check_match net_matches
  fun instcmp ({redex = r1, ...}, {redex = r2, ...}) = Type.compare(r1, r2)
in
  case checked_matches of
    [] => dest_type' ty
  | _ => let
      fun instsize i =
          List.foldl (fn ({redex,residue},acc) => tysize residue + acc) 0 i
      fun match_info (i, _, tstamp) = (instsize i, tstamp)
      val matchcmp = inv_img_cmp match_info
                                 (pair_compare(Int.compare,
                                               Lib.flip_order o Int.compare))
      val allinsts = Listsort.sort matchcmp checked_matches
      val (inst,{Thy,Name},_) = hd allinsts
      val inst' = Listsort.sort instcmp inst
      val args = map #residue inst'
    in
      case Binarymap.peek (bare_names, Name) of
          NONE => {Thy = SOME Thy, Tyop = Name, Args = args}
        | SOME thy' => if Thy = thy' then {Thy = NONE, Tyop = Name, Args = args}
                       else {Thy = SOME Thy, Tyop = Name, Args = args}
    end
end

fun abb_dest_type G ty = if !print_abbrevs then abb_dest_type0 G ty
                         else dest_type' ty

fun disable_abbrev_printing s (g as TYG grm) = let
  val (thyopt, nm) = break_qident s
  fun rmprints namecheck g =
    let
      fun foldthis (ty, i as (_, knm), acc) =
        if namecheck knm then acc else TypeNet.insert(acc,ty,i)
      val pmap' = TypeNet.fold foldthis TypeNet.empty (print_map g)
    in
      fupdate_str_print (K pmap') g
    end
in
  case thyopt of
      NONE => rmprints (fn knm => #Name knm = nm) g
    | SOME thy => rmprints (fn knm => knm = {Name = nm, Thy = thy}) g
end

(* ----------------------------------------------------------------------
    min grammar

    Grammar that knows about types bool and ind, as well as the operator
    fun, which also has an infix -> presentation
   ---------------------------------------------------------------------- *)

fun nparams s n = TYOP {Thy = "min", Tyop = s,
                        Args = List.tabulate(n, PARAM)}
val funty = Type.-->(Type.alpha,Type.beta)
val indty = Type.mk_thy_type {Thy = "min", Tyop = "ind", Args = []}

fun insert_minop (s,arity,ty) g =
  let
    val kid = {Thy = "min", Name = s}
  in
    g |> fupdate_parse_str (fn m => Binarymap.insert(m,kid, nparams s arity))
      |> fupdate_str_print (fn n => TypeNet.insert(n,ty,(tstamp g, kid)))
      |> fupdate_bare_names (fn m => Binarymap.insert(m,s,"min"))
      |> fupdate_tstamp (fn i => i + 1)
  end


val fun_rule = (50,INFIX([{opname = "fun", parse_string = "->"}], RIGHT))

val min_grammar =
    empty_grammar
      |> fupdate_rules (K [fun_rule])
      |> insert_minop ("ind", 0, indty)
      |> insert_minop ("bool", 0, Type.bool)
      |> insert_minop ("fun", 2, funty)

fun apply_delta d g =
  case d of
      NEW_TYPE kid => new_qtyop kid g
    | NEW_INFIX {Name,ParseName,Assoc,Prec} =>
      new_binary_tyop g {precedence=Prec, infix_form = ParseName,
                         opname = Name, associativity = Assoc}
    | TYABBREV (kid,ty,prp) => new_abbreviation {knm=kid,ty=ty,print=prp} g
    | DISABLE_TYPRINT s => disable_abbrev_printing s g
    | RM_KNM_TYABBREV kid => remove_knm_abbreviation g kid
    | RM_TYABBREV s => remove_abbreviation g s


fun apply_deltas ds g =
  List.foldl (uncurry apply_delta) g ds

fun delta_toString d =
    case d of
        NEW_TYPE kid => "NEW_TYPE" ^ KernelSig.name_toString kid
      | NEW_INFIX {Name,ParseName,Assoc,Prec} =>
          "NEW_INFIX{Name=\"" ^ String.toString Name ^ "\",ParseName=\"" ^
          String.toString ParseName ^ "...}"
      | _ => ""

end
