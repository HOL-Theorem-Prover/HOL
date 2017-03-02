structure type_grammar :> type_grammar =
struct

open HOLgrammars
open Lib

datatype grammar_rule =
         INFIX of {opname : string, parse_string : string} list * associativity

datatype type_structure =
         TYOP of {Thy : string, Tyop : string, Args : type_structure list}
       | PARAM of int

fun typstruct_uptodate ts =
    case ts of
      PARAM _ => true
    | TYOP {Thy, Tyop, Args} => isSome (Type.op_arity {Thy = Thy, Tyop = Tyop})
                                andalso List.all typstruct_uptodate Args

type kernelname = KernelSig.kernelname

fun break_qident s =
  case String.fields (equal #"$") s of
      [ _ ] => (NONE, s)
    | [thy, nm] => (SOME thy, nm)
    | _ => raise GrammarError ("String \""^s^
                               "\" is not a valid type identifier")


datatype grammar = TYG of {
  rules : (int * grammar_rule) list,
  suffixes : string list,
  abbparse : (kernelname, type_structure) Binarymap.dict,
  abbprint : (int * kernelname) TypeNet.typenet,
  privabbs : (string, string) Binarymap.dict,
  tstamp   : int
}
(* Abbreviations are handled by four fields of the grammar record :

   abbparse: maps (Thy,Name) pairs to type structures, encoding the abbreviation
   abbprint: maps type-patterns (i.e., structures in effect) to kernel names,
             as well as a "time stamp".  In this way, more recent patterns
             take precedence over older ones (the "specific-ness" of the
             match is more important than this though).
   privabbs: records which bare strings/Names are "privileged", and get to
             be printed without being qualified by their theory.  The map is
             from Name to Theory, so that when parsing, if the algorithm sees
             bare Name nm, it then looks up in privabbs to see which theory
             this name is associated with, and then looks up the given
             (theory,name) pair to see what structure this abbreviation has.
   tstamp:   provides the timestamps for abbprint above
*)

fun fupdate_rules f (TYG{rules,suffixes,abbprint,abbparse,privabbs,tstamp}) =
  TYG{rules=f rules,suffixes=suffixes,abbprint=abbprint,abbparse=abbparse,
      privabbs = privabbs, tstamp = tstamp}
fun fupdate_suffixes f (TYG{rules,suffixes,abbprint,abbparse,privabbs,tstamp}) =
  TYG{rules=rules,suffixes=f suffixes,abbprint=abbprint,abbparse=abbparse,
      privabbs = privabbs, tstamp = tstamp}
fun fupdate_abbprint f (TYG{rules,suffixes,abbprint,abbparse,privabbs,tstamp}) =
  TYG{rules=rules,suffixes=suffixes,abbprint=f abbprint,abbparse=abbparse,
      privabbs = privabbs, tstamp = tstamp}
fun fupdate_abbparse f (TYG{rules,suffixes,abbprint,abbparse,privabbs,tstamp}) =
  TYG{rules=rules,suffixes=suffixes,abbprint=abbprint,abbparse=f abbparse,
      privabbs = privabbs, tstamp = tstamp}
fun fupdate_privabbs f (TYG{rules,suffixes,abbprint,abbparse,privabbs,tstamp}) =
  TYG{rules=rules,suffixes=suffixes,abbprint=abbprint,abbparse=abbparse,
      privabbs = f privabbs, tstamp = tstamp}
fun fupdate_tstamp f (TYG{rules,suffixes,abbprint,abbparse,privabbs,tstamp}) =
  TYG{rules=rules,suffixes=suffixes,abbprint=abbprint,abbparse=abbparse,
      privabbs = privabbs, tstamp = f tstamp}

fun default_typrinter (G:grammar) (pps:Portable.ppstream)
                      (ty:Type.hol_type) = PP.add_string pps "<a type>"

val type_printer = ref default_typrinter
val initialised_printer = ref false

fun initialise_typrinter f =
    if not (!initialised_printer) then
      (type_printer := f; initialised_printer := true)
    else
      raise Feedback.HOL_ERR {origin_structure = "type_grammar",
                              origin_function = "initialised_printer",
                              message = "Printer function already initialised"}

fun pp_type g pps ty = (!type_printer) g pps ty

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
      NONE =>
      let
      in
        case Type.decls s of
          [] => NONE
        | ty :: _ => Option.map (fn n => (s,n)) (Type.op_arity ty)
      end
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

fun new_binary_tyop g {precedence, infix_form, opname, associativity} =
    let
      val rule =
          if isSome infix_form then
            (precedence, INFIX([{parse_string = valOf infix_form,
                                 opname = opname}],
                               associativity))
          else (precedence, INFIX([{parse_string = opname, opname = opname}],
                                  associativity))
    in
      g |> fupdate_rules (insert_sorted rule)
        |> fupdate_suffixes (Lib.insert opname)
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


fun new_tyop g name = g |> fupdate_suffixes (cons name)

val empty_grammar = TYG { rules = [], suffixes = [],
                          abbparse = Binarymap.mkDict KernelSig.name_compare,
                          privabbs = Binarymap.mkDict String.compare,
                          abbprint = TypeNet.empty,
                          tstamp = 0 }

fun rules (TYG gr) = {infixes = #rules gr, suffixes = #suffixes gr}
fun abbreviations (TYG gr) = #abbparse gr
fun abbprintmap (TYG gr) = #abbprint gr
fun privabbs (TYG gr) = #privabbs gr
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
  val (dict, st) = Binarymap.remove(abbreviations g, knm)
  fun doprint pmap0 = #1 (TypeNet.delete(pmap0, structure_to_type st))
                     handle Binarymap.NotFound => pmap0
  fun maybe_rmpriv d =
    case Binarymap.peek (d, #Name knm) of
        NONE => d
      | SOME thy' => if thy' = #Thy knm then #1 (Binarymap.remove(d, #Name knm))
                     else d
in
  g |> fupdate_abbparse (K dict) |> fupdate_abbprint doprint
    |> fupdate_privabbs maybe_rmpriv
end

fun remove_abbreviation g s =
  let
    val (thyopt, nm) = break_qident s
    fun parsemap nmcheck (knm,st,acc) =
      if nmcheck knm then acc else Binarymap.insert(acc,knm,st)
    fun printmap nmcheck (ty,v as (tstamp,knm),acc) =
      if nmcheck knm then acc else TypeNet.insert(acc,ty,v)
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
    g |> fupdate_privabbs privrm
      |> fupdate_abbprint (TypeNet.fold (printmap check) TypeNet.empty)
      |> fupdate_abbparse
           (Binarymap.foldl (parsemap check)
                            (Binarymap.mkDict KernelSig.name_compare))
  end

fun new_abbreviation tyg (knm as {Name=s,Thy=thy}, st) = let
  val _ = check_structure st
  val tyg = case Binarymap.peek(abbreviations tyg, knm) of
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
    tyg |> fupdate_abbparse (fn d => Binarymap.insert(d,knm,st))
        |> fupdate_abbprint
             (fn pmap => TypeNet.insert(pmap, structure_to_type st,
                                        (tstamp, knm)))
        |> fupdate_privabbs (fn d => Binarymap.insert(d,s,thy))
        |> C new_tyop s
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
                                ("Conflicting entries for abbreviation "^
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
  val TYG { rules = grules1, suffixes = sfxs1, abbparse = abbrevs1,
            abbprint = pmap1, tstamp = t1, privabbs = priv1 } = G1
  val TYG { rules = grules2, suffixes = sfxs2, abbparse = abbrevs2,
            abbprint = pmap2, tstamp = t2, privabbs = priv2 } = G2
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
        suffixes = Lib.union sfxs1 sfxs2,
        abbparse = merge_abbrevs G2 (abbrevs1, abbrevs2),
        abbprint = merge_pmaps (pmap1, pmap2),
        privabbs = merge_privs (priv1, priv2),
        tstamp = Int.max(t1,t2) + 1 }
end

fun prettyprint_grammar pps G = let
  val TYG grm  = G
  val {rules=g, suffixes=sfxs, abbparse=abbrevs, abbprint=pmap, ... } = grm
  val privabbs = #privabbs grm
  open Portable Lib
  val {add_break,add_newline,add_string,begin_block,end_block,...} =
      with_ppstream pps
  fun print_suffix (s,arity) = let
    fun print_ty_n_tuple n =
        case n of
          0 => ()
        | 1 => add_string "TY "
        | n => (add_string "(";
                pr_list (fn () => add_string "TY") (fn () => add_string ", ")
                        (fn () => ()) (List.tabulate(n,K ()));
                add_string ")")
  in
    print_ty_n_tuple arity;
    add_string s
  end

  fun print_abbrev (s, st) = let
    val kns = KernelSig.name_toString s
    val ispriv = case Binarymap.peek (privabbs, #Name s) of
                     SOME thy => thy = #Thy s
                   | NONE => false
    fun print_lhs () =
      case num_params st of
        0 => add_string kns
      | 1 => (add_string "'a "; add_string kns)
      | n => (begin_block INCONSISTENT 0;
              add_string "(";
              pr_list (pp_type G pps o structure_to_type o PARAM)
                      (fn () => add_string ",")
                      (fn () => add_break(1,0))
                      (List.tabulate(n, I));
              add_string ") ";
              add_string kns)
    fun print_priv () = if ispriv then add_string " (*)" else ()
    val ty = structure_to_type st
    val printed = case TypeNet.peek (pmap, ty) of
                    NONE => false
                  | SOME (_, s') => s = s'
  in
    begin_block CONSISTENT 0;
    print_lhs ();
    add_string " =";
    add_break(1,2);
    Feedback.trace ("print_tyabbrevs", 0) (pp_type G pps) ty;
    if not printed orelse ispriv then
      (add_break(5,2); add_string "(";
       (if ispriv then add_string "preferred" else ());
       if printed then add_string ")"
       else if ispriv then add_string ", not printed)"
       else add_string "not printed)")
    else ();
    end_block()
  end

  fun print_abbrevs () = let
    fun foldthis (k,st,acc) =
        if typstruct_uptodate st then (k,st)::acc else acc
    val okabbrevs = List.rev (Binarymap.foldl foldthis [] abbrevs)
  in
    if length okabbrevs > 0 then let
      in
        add_newline();
        add_string "Type abbreviations:";
        add_break(2,2);
        begin_block CONSISTENT 0;
        pr_list print_abbrev (fn () => add_newline()) (fn () => ()) okabbrevs;
        end_block()
      end
    else ()
  end

  fun print_infix {opname,parse_string} = let
  in
    add_string "TY ";
    add_string parse_string;
    add_string " TY";
    if opname <> parse_string then
      add_string (" ["^opname^"]")
    else
      ()
  end

  fun print_suffixes slist = let
    val oksl = List.mapPartial (suffix_arity (abbrevs, privabbs)) slist
  in
    if null oksl then ()
    else let
      in
        add_string "       TY  ::=  ";
        begin_block INCONSISTENT 0;
        pr_list print_suffix (fn () => add_string " |")
                (fn () => add_break(1,0)) oksl;
        end_block ();
        add_newline()
      end
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
        add_string "TY  ::=  ";
        begin_block INCONSISTENT 0;
        pr_list print_infix (fn () => add_string " |")
                (fn () => add_break(1,0)) oplist;
        add_string (" ("^assocstring^"associative)");
        end_block()
      end;
  fun print_rule (n, r) = let
    val precstr = StringCvt.padRight #" " 7 ("("^Int.toString n^")")
  in
    add_string precstr;
    print_rule0 r;
    add_newline()
  end
in
  begin_block CONSISTENT 0;
    begin_block CONSISTENT 0;
      add_string "Rules:";
      add_break (1,2);
      begin_block CONSISTENT 0;
        app print_rule g;
        print_suffixes sfxs;
        add_string "       TY  ::=  TY[TY] (array type)";
      end_block ();
    end_block ();
    print_abbrevs();
  end_block()
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
  val (nm, args) = Type.dest_type ty
in
  {Thy = NONE, Tyop = nm, Args = args}
end

fun abb_dest_type0 (TYG{abbprint = pmap, privabbs, ...}) ty = let
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
      case Binarymap.peek (privabbs, Name) of
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
      val pmap' =
          TypeNet.fold (fn (ty, (tstamp, knm), acc) =>
                           if namecheck knm then acc
                           else TypeNet.insert(acc,ty, (tstamp, knm)))
                       TypeNet.empty
                       (abbprintmap g)
    in
      fupdate_abbprint (K pmap') g
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

val min_grammar =
    empty_grammar |> C new_tyop "bool"
                  |> C new_tyop "ind"
                  |> C new_binary_tyop {opname = "fun",
                                        associativity = RIGHT,
                                        infix_form = SOME "->",
                                        precedence = 50}


end
