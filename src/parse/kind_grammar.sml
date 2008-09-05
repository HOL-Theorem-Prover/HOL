structure kind_grammar :> kind_grammar =
struct

datatype grammar_rule
    = NONFIX
    | INFIX of {opname : string, parse_string : string} list *
                HOLgrammars.associativity
    | PREFIX of string list

datatype kind_structure
    = KINDOP of {Thy : string, Kindop : string, Args : kind_structure list}
    | KDVAR  of string

datatype grammar = KINDG of (int * grammar_rule) list (* *
                          (string, kind_structure) Binarymap.dict *
                          (int * string) TypeNet.typenet *)

open HOLgrammars Kind
infixr 3 ==>

fun KDG_ERR f m = Feedback.HOL_ERR {origin_structure = "kind_grammar",
                                    origin_function = f,
                                    message = m}

fun default_kindprinter (G:grammar) (pps:Portable.ppstream)
                        (kd:Kind.kind) = PP.add_string pps "<a kind>"

val kind_printer = ref default_kindprinter
val initialised_printer = ref false

fun initialise_kindprinter f =
    if not (!initialised_printer) then
      (kind_printer := f; initialised_printer := true)
    else
      raise KDG_ERR "initialised_printer"
                    "Printer function already initialised"

fun pp_kind g pps kind = (!kind_printer) g pps kind

fun structure_to_kind st =
    case st of
      KINDOP {Thy,Kindop,Args} =>
        let val args = map structure_to_kind Args
        in
           if Kindop = "ty"
           then if length args = 0
                then Kind.typ
                else raise KDG_ERR "structure_to_kind"
                           ("Wrong number of arguments ("
                            ^ Int.toString(length args)
                            ^ ") to kind operator\"" ^ Kindop ^ "\"")
           else if Kindop = "=>"
           then if length args = 2
                then hd args ==> hd(tl args)
                else raise KDG_ERR "structure_to_kind"
                           ("Wrong number of arguments ("
                            ^ Int.toString(length args)
                            ^ ") to kind operator\"" ^ Kindop ^ "\"")
           else raise KDG_ERR "structure_to_kind"
                             ("Unknown kind operator: " ^ Kindop)
            (* Kind.mk_thy_kind {Thy = Thy, Kindop = Kindop,
                                 Args = map structure_to_kind Args} *)
        end
    | KDVAR str => Kind.mk_varkind str

val std_prefix_precedence = 100



fun merge r1 r2 =
  case (r1, r2) of
    (NONFIX, NONFIX) => NONFIX
  | (PREFIX slist1, PREFIX slist2) => PREFIX (Lib.union slist1 slist2)
  | (INFIX(rlist1, a1), INFIX(rlist2, a2)) => let
    in
      if a1 = a2 then INFIX(Lib.union rlist1 rlist2, a1)
      else
        raise GrammarError
          "Attempt to merge two infix kinds with different associativities"
    end
  | _ => raise GrammarError "Attempt to merge prefix and infix kind"

fun insert_sorted0 (k, v) [] = [(k, v)]
  | insert_sorted0 kv1 (wholething as (kv2::rest)) = let
      val (k1, v1) = kv1
      val (k2, v2) = kv2
    in
      if (k1 < k2) then kv1::wholething
      else
        if k1 = k2 then  (k1, merge v1 v2) :: rest
        else
          kv2 :: insert_sorted0 kv1 rest
    end

fun insert_sorted (k, v) (G0 : (int * grammar_rule) list) = let
  val G1 = insert_sorted0 (k,v) G0
  fun merge_adj_prefixes [] = []
    | merge_adj_prefixes [x] = [x]
    | merge_adj_prefixes (x1::x2::xs) = let
      in
        case (x1, x2) of
          ((p1, PREFIX slist1), (p2, PREFIX slist2)) =>
            merge_adj_prefixes ((p1, PREFIX (Lib.union slist1 slist2))::xs)
        | _ => x1 :: merge_adj_prefixes (x2 :: xs)
      end
in
  merge_adj_prefixes G1
end



fun new_binary_kindop (KINDG(G (*,abbrevs,pmap*) ))
                    {precedence, infix_form, opname, associativity} =
    let
      val rule1 =
          if isSome infix_form then
            (precedence, INFIX([{parse_string = valOf infix_form,
                                 opname = opname}],
                               associativity))
          else (precedence, INFIX([{parse_string = opname, opname = opname}],
                                  associativity))
      (* val rule2 = (std_prefix_precedence, PREFIX[opname]) *)
    in
      (* KINDG (insert_sorted rule1 (insert_sorted rule2 G), abbrevs, pmap) *)
      KINDG (insert_sorted rule1 G (*, abbrevs, pmap*) )
    end

fun remove_binary_kindop (KINDG (G (*, abbrevs, pmap*))) s = let
  fun bad_irule {parse_string,...} = parse_string = s
  fun edit_rule (prec, r) =
      case r of
        INFIX (irules, assoc) => let
          val irules' = List.filter (not o bad_irule) irules
        in
          if null irules' then NONE
          else SOME (prec, INFIX (irules', assoc))
        end
      | _ => SOME (prec, r)
in
  KINDG(List.mapPartial edit_rule G (*, abbrevs, pmap*) )
end


fun new_kindop (KINDG(G (*,abbrevs,pmap*) )) name =
  KINDG (insert_sorted (std_prefix_precedence, PREFIX[name]) G (*, abbrevs, pmap*) )

val empty_grammar = new_binary_kindop
                    (KINDG ([(120, PREFIX ["ar"]),(700, NONFIX)] (*,
                          Binarymap.mkDict String.compare, 
                          TypeNet.empty *) ))
                    {precedence=70, infix_form=NONE, opname="=>",
                     associativity=HOLgrammars.RIGHT}

fun rules (KINDG (G (*, dict, pmap*) )) = G
(*
fun abbreviations (KINDG (G, dict, pmap)) = dict

val abb_tstamp = ref 0
fun new_abbreviation (KINDG(G, dict0, pmap)) (s, st) = let
  val G0 = KINDG(G, Binarymap.insert(dict0,s,st),
               TypeNet.insert(pmap, structure_to_kind st, (!abb_tstamp, s)))
  val _ = abb_tstamp := !abb_tstamp + 1
in
  new_kindop G0 s
end

fun remove_abbreviation(arg as KINDG(G, dict0, pmap0)) s = let
  val (dict,st) = Binarymap.remove(dict0,s)
  val pmap = #1 (TypeNet.delete(pmap0, structure_to_kind st))
      handle Binarymap.NotFound => pmap0
in
  KINDG(G, dict, pmap)
end handle Binarymap.NotFound => arg

fun merge_abbrevs G (d1, d2) = let
  fun merge_dictinsert (k,v,newdict) =
      case Binarymap.peek(newdict,k) of
        NONE => Binarymap.insert(newdict,k,v)
      | SOME v0 =>
        if v0 <> v then
          (Feedback.HOL_WARNING "parse_kind" "merge_grammars"
                                ("Conflicting entries for abbreviation "^k^
                                 "; arbitrarily keeping map to "^
                                 PP.pp_to_string (!Globals.linewidth)
                                                 (pp_kind G)
                                                 (structure_to_kind v0));
           newdict)
        else
          newdict
in
    Binarymap.foldr merge_dictinsert d1 d2
end

fun merge_pmaps (p1, p2) =
    TypeNet.fold (fn (kind,v,acc) => TypeNet.insert(acc,kind,v)) p1 p2
*)

fun rev_append [] acc = acc
  | rev_append (x::xs) acc = rev_append xs (x::acc)

fun merge_grammars (G1, G2) = let
  (* both grammars are sorted, with no adjacent prefixes *)
  val KINDG (grules1 (*, abbrevs1, pmap1*) ) = G1
  val KINDG (grules2 (*, abbrevs2, pmap2*) ) = G2
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
  KINDG (merge_acc [] (grules1, grules2) (*,
       merge_abbrevs G2 (abbrevs1, abbrevs2),
       merge_pmaps (pmap1, pmap2)*) )
end

fun prettyprint_grammar pps (G as KINDG (g (*,abbrevs,pmap*) )) = let
  open Portable Lib
  val {add_break,add_newline,add_string,begin_block,end_block,...} =
      with_ppstream pps
  fun print_prefix s = let
    fun oarity () = 0
(*
        case Binarymap.peek(abbrevs, s) of
          NONE => valOf (Kind.op_arity (hd (Kind.decls s)))
        | SOME st => num_params st
*)
    fun print_kind_n_tuple n =
        case n of
          0 => ()
        | 1 => add_string "KIND "
        | n => (add_string "(";
                pr_list (fn () => add_string "KIND") (fn () => add_string ", ")
                        (fn () => ()) (List.tabulate(n,K ()));
                add_string ")")
  in
    add_string s;
    add_string " ";
    if s = "ar" then add_string "NUMERAL"
    else print_kind_n_tuple (oarity())
  end

(*
  fun print_abbrev (s, st) = let
    fun print_lhs () =
      case num_params st of
        0 => add_string s
      | 1 => (add_string "'a "; add_string s)
      | n => (begin_block INCONSISTENT 0;
              add_string "(";
              pr_list (pp_kind G pps o structure_to_kind o PARAM)
                      (fn () => add_string ",")
                      (fn () => add_break(1,0))
                      (List.tabulate(n, I));
             add_string ") ";
             add_string s)
    val kind = structure_to_kind st
    val printed = case TypeNet.peek (pmap, kind) of
                    NONE => false
                  | SOME (_, s') => s = s'
  in
    begin_block CONSISTENT 0;
    print_lhs ();
    add_string " =";
    add_break(1,2);
    Feedback.trace ("print_kindabbrevs", 0) (pp_kind G pps) kind;
    if not printed then (add_break(5,2); add_string "(not printed)") else ();
    end_block()
  end

  fun print_abbrevs () =
      if Binarymap.numItems abbrevs > 0 then let
        in
          add_newline();
          add_string "Kind abbreviations:";
          add_break(2,0);
          begin_block CONSISTENT 0;
          pr_list print_abbrev (fn () => add_newline()) (fn () => ())
                  (Binarymap.listItems abbrevs);
          end_block()
        end
      else ()
*)

  fun print_infix {opname,parse_string} = let
  in
    add_string "KIND ";
    add_string parse_string;
    add_string " KIND";
    if opname <> parse_string then
      add_string (" ["^opname^"]")
    else
      ()
  end

  fun print_rule0 r =
    case r of
      PREFIX sl => let
      in
        add_string "KIND  ::=  ";
        begin_block INCONSISTENT 0;
        pr_list print_prefix (fn () => add_string " |")
                (fn () => add_break(1,0)) sl;
        end_block ()
      end
    | NONFIX => add_string "KIND  ::=  ty (type kind)"
    | INFIX(oplist, assoc) => let
        val assocstring =
            case assoc of
              LEFT => "L-"
            | RIGHT => "R-"
            | NONASSOC => "non-"
      in
        add_string "KIND  ::=  ";
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
  add_string "Rules:";
  add_newline();
  app print_rule g;
  (* print_abbrevs(); *)
  end_block()
end;

(*
val print_abbrevs = ref true
val _ = Feedback.register_btrace ("print_kind_abbrevs", print_abbrevs)

fun kindsize kind =
    if kind = Kind.typ then 1
    else let val (dom,rng) = Kind.kind_dom_rng kind
         in 1 + kindsize dom + kindsize rng
         end

fun abb_dest_kind0 (KINDG(_, _, pmap)) kind = let
  open HolKernel
  val net_matches = TypeNet.match(pmap, kind)
  fun mymatch pat kind = let
    val (i, sames) = Kind.raw_match_kind pat kind ([], [])
  in
    i @ (map (fn kind => kind |-> kind) sames)
  end
  fun check_match (pat, (tstamp, nm)) =
      SOME(mymatch pat kind, nm, tstamp) handle HOL_ERR _ => NONE
  val checked_matches = List.mapPartial check_match net_matches
  fun instcmp ({redex = r1, ...}, {redex = r2, ...}) = Kind.compare(r1, r2)
in
  case checked_matches of
    [] => Kind.dest_kind kind
  | _ => let
      fun instsize i =
          List.foldl (fn ({redex,residue},acc) => kindsize residue + acc) 0 i
      fun match_info (i, _, tstamp) = (instsize i, tstamp)
      val matchcmp = inv_img_cmp match_info
                                 (pair_compare(Int.compare,
                                               Lib.flip_order o Int.compare))
      val allinsts = Listsort.sort matchcmp checked_matches
      val (inst,nm,_) = hd allinsts
      val inst' = Listsort.sort instcmp inst
      val args = map #residue inst'
    in
      (nm, args)
    end
end

fun abb_dest_kind G kind = if !print_abbrevs then abb_dest_kind0 G kind
                         else Kind.dest_kind kind

fun disable_abbrev_printing s (arg as KINDG(G,abbs,pmap)) =
    case Binarymap.peek(abbs, s) of
      NONE => arg
    | SOME st => let
        val kind = structure_to_kind st
        val (pmap', (_,s')) = TypeNet.delete(pmap, kind)
      in
        if s = s' then KINDG(G, abbs, pmap')
        else arg
      end handle Binarymap.NotFound => arg
*)


end
