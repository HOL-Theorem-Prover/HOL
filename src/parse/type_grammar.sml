structure type_grammar :> type_grammar =
struct

datatype grammar_rule =
  CONSTANT of string list
| BINDER of string list list
| APPLICATION
| CAST
| ARRAY_SFX
| INFIX of {opname : string, parse_string : string} list *
           HOLgrammars.associativity

datatype type_structure =
         TYCON  of {Thy : string, Tyop : string, Kind : Kind.kind, Rank : int}
       | TYAPP  of type_structure * type_structure
       | TYUNIV of type_structure * type_structure
       | TYABST of type_structure * type_structure
       | TYVAR  of string * Kind.kind * int (* rank *)
       | PARAM  of int    * Kind.kind * int (* rank *)

fun typstruct_uptodate ts =
    case ts of
      PARAM _ => true
    | TYVAR (str,kd,rk) => true
    | TYCON {Thy, Tyop, Kind, Rank} => isSome (Type.op_kind {Thy = Thy, Tyop = Tyop})
    | TYAPP (opr,arg) => typstruct_uptodate opr andalso typstruct_uptodate arg
    | TYUNIV (bvar,body) => typstruct_uptodate body
    | TYABST (bvar,body) => typstruct_uptodate body
(*
    | TYOP {Thy, Tyop, Args} => isSome (Type.op_arity {Thy = Thy, Tyop = Tyop})
                                andalso List.all typstruct_uptodate Args
*)



type special_info = {lambda : string list,
                     forall : string list}

datatype grammar = TYG of (int * grammar_rule) list *
                          (string, type_structure) Binarymap.dict *
                          special_info *
                          (int * string) TypeNet.typenet

open HOLgrammars

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
      TYCON {Thy,Tyop,Kind,Rank} => Type.mk_thy_con_type {Thy=Thy, Tyop=Tyop, Kind=Kind, Rank=Rank}
    | TYAPP (opr,arg) => Type.mk_app_type(structure_to_type opr, structure_to_type arg)
    | TYUNIV (bvar,body) => Type.mk_univ_type(structure_to_type bvar, structure_to_type body)
    | TYABST (bvar,body) => Type.mk_abs_type(structure_to_type bvar, structure_to_type body)
    | TYVAR (str,kd,rk) => Type.mk_var_type(str,kd,rk)
(*
      TYOP {Thy,Tyop,Args} =>
      Type.mk_thy_type {Thy = Thy, Tyop = Tyop,
                        Args = map structure_to_type Args}
*)
    | PARAM (n,kd,rk) => Type.mk_var_type ("'"^str (chr (n + ord #"a")), kd, rk)

fun params0 acc (PARAM (i,kd,rk)) = HOLset.add(acc, i)
  | params0 acc (TYCON {Thy,Tyop,Kind,Rank}) = acc
  | params0 acc (TYVAR (str,kd,rk)) = acc
  | params0 acc (TYAPP (opr,arg)) = params0 (params0 acc opr) arg
  | params0 acc (TYUNIV (bvar,body)) = params0 (params0 acc bvar) body
  | params0 acc (TYABST (bvar,body)) = params0 (params0 acc bvar) body
(*
  | params0 acc (TYOP{Args,...}) = foldl (fn (t,set) => params0 set t) acc Args
*)
val params = params0 (HOLset.empty Int.compare)

val num_params = HOLset.numItems o params

fun suffix_kind abbrevs s =
    case Binarymap.peek (abbrevs, s) of
      NONE => let
      in
        case Type.decls s of
          [] => NONE
        | ty :: _ => Option.map (fn n => (s,n)) (Type.op_kind ty)
      end
    | SOME st => if typstruct_uptodate st then SOME (s, Kind.mk_arity (num_params st))
                 else NONE

val std_suffix_precedence = 100
val std_binder_precedence =  20



fun merge r1 r2 =
  case (r1, r2) of
    (ARRAY_SFX, ARRAY_SFX) => ARRAY_SFX
  | (CAST, CAST) => CAST
  | (APPLICATION, APPLICATION) => APPLICATION
  | (CONSTANT slist1, CONSTANT slist2) => CONSTANT(Lib.union slist1 slist2)
  | (BINDER slist1, BINDER slist2) => BINDER(Lib.union slist1 slist2)
  | (INFIX(rlist1, a1), INFIX(rlist2, a2)) => let
    in
      if a1 = a2 then INFIX(Lib.union rlist1 rlist2, a1)
      else
        raise GrammarError
          "Attempt to merge two infix types with different associativities"
    end
  | _ => raise GrammarError "Attempt to merge suffix and infix type"

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
  fun merge_adj_constants [] = []
    | merge_adj_constants [x] = [x]
    | merge_adj_constants (x1::x2::xs) = let
      in
        case (x1, x2) of
          ((p1, CONSTANT slist1), (p2, CONSTANT slist2)) =>
            merge_adj_constants ((p1, CONSTANT (Lib.union slist1 slist2))::xs)
        | ((p1, BINDER slist1), (p2, BINDER slist2)) =>
            merge_adj_constants ((p1, BINDER (Lib.union slist1 slist2))::xs)
        | _ => x1 :: merge_adj_constants (x2 :: xs)
      end
in
  merge_adj_constants G1
end



fun new_binary_tyop (TYG(G,abbrevs,specials,pmap))
                    {precedence, infix_form, opname, associativity} =
    let
      val rule1 =
          if isSome infix_form then
            (precedence, INFIX([{parse_string = valOf infix_form,
                                 opname = opname}],
                               associativity))
          else (precedence, INFIX([{parse_string = opname, opname = opname}],
                                  associativity))
      val rule2 = (std_suffix_precedence, CONSTANT[opname])
    in
      TYG (insert_sorted rule1 (insert_sorted rule2 G), abbrevs, specials, pmap)
    end

fun remove_binary_tyop (TYG (G, abbrevs, specials, pmap)) s = let
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
  TYG(List.mapPartial edit_rule G, abbrevs, specials, pmap)
end


fun new_tyop (TYG(G,abbrevs,specials,pmap)) name =
  TYG (insert_sorted (std_suffix_precedence, CONSTANT[name]) G, abbrevs, specials, pmap)

fun new_tybinder (TYG(G,abbrevs,specials,pmap)) names =
  TYG (insert_sorted (std_binder_precedence, BINDER[names]) G, abbrevs, specials, pmap)

val empty_grammar = TYG ([(std_binder_precedence, BINDER[]),
                          (80, APPLICATION),(90, CAST),(99, ARRAY_SFX)], 
                         Binarymap.mkDict String.compare,
                         {lambda = ["\\"], forall = ["!"]},
                         TypeNet.empty)

fun rules (TYG (G, dict, specials, pmap)) = G
fun abbreviations (TYG (G, dict, specials, pmap)) = dict
fun specials (TYG (G, dict, specials', pmap)) = specials'
fun abbr_print_map (TYG (G, dict, specials, pmap)) = pmap

fun fupdate_rules    f (TYG (G, dict, specials, pmap)) =
                        TYG (f G, dict, specials, pmap)
fun fupdate_specials f (TYG (G, dict, specials, pmap)) =
                        TYG (G, dict, f specials, pmap)

fun is_var_rule (_,CAST) = true
  | is_var_rule _        = false
fun var_grammar (TYG(G,abbrevs,specials,pmap)) = TYG(List.filter is_var_rule G,abbrevs,specials,pmap)

fun check_structure st = let
  fun param_numbers (PARAM (i,kd,rk), pset) = HOLset.add(pset, i)
    | param_numbers (TYCON _, pset) = pset
    | param_numbers (TYVAR _, pset) = pset
    | param_numbers (TYAPP(opr,arg), pset) = param_numbers (arg, param_numbers (opr,pset))
    | param_numbers (TYUNIV(bvar,body), pset) = param_numbers (body, param_numbers (bvar,pset))
    | param_numbers (TYABST(bvar,body), pset) = param_numbers (body, param_numbers (bvar,pset))
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

val abb_tstamp = ref 0
fun new_abbreviation (TYG(G, dict0, specials, pmap)) (s, st) = let
  val _ = check_structure st
  val _ = case st of PARAM _ =>
                     raise GrammarError
                               "Abbreviation can't be to a type variable"
                   | _ => ()
  val G0 = TYG(G, Binarymap.insert(dict0,s,st), specials,
               TypeNet.insert(pmap, structure_to_type st, (!abb_tstamp, s)))
  val _ = abb_tstamp := !abb_tstamp + 1
in
  new_tyop G0 s
end

fun remove_abbreviation(arg as TYG(G, dict0, specials, pmap0)) s = let
  val (dict,st) = Binarymap.remove(dict0,s)
  val pmap = #1 (TypeNet.delete(pmap0, structure_to_type st))
      handle Binarymap.NotFound => pmap0
in
  TYG(G, dict, specials, pmap)
end handle Binarymap.NotFound => arg

fun rev_append [] acc = acc
  | rev_append (x::xs) acc = rev_append xs (x::acc)

fun merge_abbrevs G (d1, d2) = let
  fun merge_dictinsert (k,v,newdict) =
      case Binarymap.peek(newdict,k) of
        NONE => Binarymap.insert(newdict,k,v)
      | SOME v0 =>
        if v0 <> v then
          (Feedback.HOL_WARNING "parse_type" "merge_grammars"
                                ("Conflicting entries for abbreviation "^k^
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

fun merge_specials (S1, S2) = let
  val {lambda = lam1, forall = fal1} = S1
  val {lambda = lam2, forall = fal2} = S2
in
  if lam1 = lam2 andalso fal1 = fal2
  then
    {lambda = lam1, forall = fal1}
  else
    raise GrammarError "Specials in two grammars don't agree"
end

fun merge_pmaps (p1, p2) =
    TypeNet.fold (fn (ty,v,acc) => TypeNet.insert(acc,ty,v)) p1 p2

fun merge_grammars (G1, G2) = let
  (* both grammars are sorted, with no adjacent suffixes *)
  val TYG (grules1, abbrevs1, specials1, pmap1) = G1
  val TYG (grules2, abbrevs2, specials2, pmap2) = G2
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
  TYG (merge_acc [] (grules1, grules2),
       merge_abbrevs G2 (abbrevs1, abbrevs2),
       merge_specials (specials1, specials2),
       merge_pmaps (pmap1, pmap2))
end

fun prettyprint_grammar pps (G as TYG (g,abbrevs,specials,pmap)) = let
  val {lambda,forall} = specials
  open Portable Lib
  val {add_break,add_newline,add_string,begin_block,end_block,...} =
      with_ppstream pps
  fun print_suffix (s,kind) = let
    fun print_ty_n_tuple n =
        case n of
          0 => ()
        | 1 => add_string "TY "
        | n => (add_string "(";
                pr_list (fn () => add_string "TY") (fn () => add_string ", ")
                        (fn () => ()) (List.tabulate(n,K ()));
                add_string ")")
    open Kind
    fun print_ty_kind kind =
      if kind = typ then add_string "TY"
      else if is_var_kind kind then add_string (dest_var_kind kind)
      else let val (kds,kd) = strip_arrow_kind kind
           in add_string "(";
              pr_list (fn kd => print_ty_kind kd) (fn () => add_string " => ")
                      (fn () => ()) (kds @ [kd]);
              add_string ")"
           end
  in
    if is_arity kind then print_ty_n_tuple (arity_of kind)
                     else print_ty_kind kind;
    add_string s
  end

  fun print_binder s = let
  in
    add_string ("\"" ^ hd s ^ "\" <..binders..> \".\" TY")
  end

fun triple_compare(cmp1,cmp2,cmp3)((a1,a2,a3),(b1,b2,b3)) =
    Lib.pair_compare(cmp1,Lib.pair_compare(cmp2,cmp3))((a1,(a2,a3)),(b1,(b2,b3)))

fun get_params0 acc (PARAM (i,kd,rk)) = HOLset.add(acc, (i,kd,rk))
  | get_params0 acc (TYCON {Thy,Tyop,Kind,Rank}) = acc
  | get_params0 acc (TYVAR (str,kd,rk)) = acc
  | get_params0 acc (TYAPP (opr,arg)) = get_params0 (get_params0 acc opr) arg
  | get_params0 acc (TYUNIV (bvar,body)) = get_params0 (get_params0 acc bvar) body
  | get_params0 acc (TYABST (bvar,body)) = get_params0 (get_params0 acc bvar) body
val get_params = get_params0 (HOLset.empty (triple_compare (Int.compare,Kind.kind_compare,Int.compare)))

  fun print_abbrev (s, st) = let
    val ps = HOLset.listItems (get_params st)
    fun print_lhs () =
      case (*num_params st*) length ps of
        0 => add_string s
      | 1 => (let val (p as (_,kd,rk)) = hd ps
                  val simple = kd = Kind.typ andalso rk = 0
              in if simple then () else add_string "(";
                 pp_type G pps (structure_to_type (PARAM p));
                 if simple then () else add_string ")";
                 add_string " ";
                 add_string s
              end)
      | n => (begin_block INCONSISTENT 0;
              add_string "(";
              pr_list (pp_type G pps o structure_to_type o PARAM)
                      (fn () => add_string ",")
                      (fn () => add_break(1,0))
                      ps;
             add_string ") ";
             add_string s)
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
    if not printed then (add_break(5,2); add_string "(not printed)") else ();
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

  fun print_rule0 r =
    case r of
      CONSTANT sl => let
        val oksl = List.mapPartial (suffix_kind abbrevs) sl
      in
        if null oksl then ()
        else let
          in
            add_string "TY  ::=  ";
            begin_block INCONSISTENT 0;
            pr_list print_suffix (fn () => add_string " |")
                    (fn () => add_break(1,0)) oksl;
            end_block ()
          end
      end
    | BINDER sl => let
      in
        add_string "TY  ::=  ";
        begin_block INCONSISTENT 0;
        pr_list print_binder (fn () => add_string " |")
                (fn () => add_break(1,0)) sl;
        end_block ()
      end
    | CAST => add_string "TY  ::=  TY : KIND | TY :<= RANK (kind or rank cast of type)"
    | APPLICATION => add_string "TY  ::=  TY TY (type application)"
    | ARRAY_SFX => add_string "TY  ::=  TY[TY] (array type)"
    | INFIX(oplist, assoc) => let
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

fun abb_dest_type0 (TYG(_, _, _, pmap)) ty = let
  open HolKernel
  val net_matches = TypeNet.match(pmap, ty)
  fun mymatch pat ty = let
    val pat = if is_abs_type pat then snd(strip_abs_type pat) else pat
    val ((i, sames), (k, kdsames), r) =
       Type.raw_kind_match_type pat ty (([], []), ([], []), 0)
  in
    (i @ (map (fn ty => ty |-> ty) sames),
     k @ (map (fn kd => kd |-> kd) kdsames),
     r)
  end
  fun check_match (pat, (tstamp, nm)) =
      SOME(mymatch pat ty, nm, tstamp) handle HOL_ERR _ => NONE
  val checked_matches = List.mapPartial check_match net_matches
  fun instcmp ({redex = r1, ...}, {redex = r2, ...}) = Type.compare(r1, r2)
in
  case checked_matches of
    [] => Type.dest_type ty
  | _ => let
      fun instsize (i,k,r) =
          List.foldl (fn ({redex,residue},acc) => tysize residue + acc) 0 i
      fun match_info (i, _, tstamp) = (instsize i, tstamp)
      val matchcmp = inv_img_cmp match_info
                                 (pair_compare(Int.compare,
                                               Lib.flip_order o Int.compare))
      val allinsts = Listsort.sort matchcmp checked_matches
      val (inst,nm,_) = hd allinsts
      val inst' = Listsort.sort instcmp (#1 inst)
      val args = map #residue inst'
    in
      (nm, args)
    end
end

fun abb_dest_type G ty = if !print_abbrevs then abb_dest_type0 G ty
                         else Type.dest_type ty

fun disable_abbrev_printing s (arg as TYG(G,abbs,specials,pmap)) =
    case Binarymap.peek(abbs, s) of
      NONE => arg
    | SOME st => let
        val ty = structure_to_type st
        val (pmap', (_,s')) = TypeNet.delete(pmap, ty)
      in
        if s = s' then TYG(G, abbs, specials, pmap')
        else arg
      end handle Binarymap.NotFound => arg
(* ----------------------------------------------------------------------
    min grammar

    Grammar that knows about types bool and ind, as well as the operator
    fun, which also has an infix -> presentation
   ---------------------------------------------------------------------- *)

open Lib
val min_grammar =
    empty_grammar |> C new_tyop "bool"
                  |> C new_tyop "ind"
                  |> C new_binary_tyop {opname = "fun",
                                        associativity = RIGHT,
                                        infix_form = SOME "->",
                                        precedence = 50}
                  |> C new_tybinder ["\\"]
                  |> C new_tybinder ["!"]


end
