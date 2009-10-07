structure type_pp :> type_pp =
struct

open Feedback Type Portable HOLgrammars type_grammar

datatype mygrav
   = Sfx of int
   | Lfx of int * string
   | Rfx of int * string
   | Top

datatype single_rule
   = SR
   | IR of associativity * string

val PP_ERR = mk_HOL_ERR "type_pp";

val ERR = mk_HOL_ERR "type_pp" "pp_type";

(*---------------------------------------------------------------------------
       Kind antiquotations (required in type parser)
 ---------------------------------------------------------------------------*)

fun kd_antiq kd = mk_var_type("'kd_antiq",kd,0)

fun dest_kd_antiq ty =
  case Lib.with_exn dest_var_type ty (PP_ERR "dest_kd_antiq" "not a kind antiquotation")
   of ("'kd_antiq",Kd,0) => Kd
    |  _ => raise PP_ERR "dest_kd_antiq" "not a kind antiquotation";

val is_kd_antiq = Lib.can dest_kd_antiq


val pp_num_types = ref true
val _ = register_btrace("pp_num_types", pp_num_types)

val pp_annotations = ref (!Globals.interactive)
val _ = register_btrace ("pp_annotations", pp_annotations)

fun dest_numtype ty = let
  open Arbnum
  val _ = (* respect pp_num_types flag *)
      !pp_num_types orelse raise mk_HOL_ERR "" "" ""
  val _ = (* exception: don't print :one as one *)
      let val {Thy,Tyop,Args} = dest_thy_type ty
      in
        if Thy = "one" andalso Tyop = "one" then raise mk_HOL_ERR "" "" ""
        else ()
      end
  fun recurse (base, acc) ty = let
    val {Thy,Tyop,Args} = dest_thy_type ty
  in
    case (Thy,Tyop) of
      ("one", "one") => acc + base
    | ("fcp", "bit1") => recurse (two * base, acc + base) (hd Args)
    | ("fcp", "bit0") => recurse (two * base, acc) (hd Args)
    | _ => raise mk_HOL_ERR "" "" ""
  end
in
  toString (recurse (one, zero) ty)
end

val greek4 = let
  open UnicodeChars
in
  [alpha, beta, gamma, delta]
end

fun strip_app_structure0 argl (TYAPP(opr,arg)) =
    strip_app_structure0 (arg::argl) opr
  | strip_app_structure0 argl st = (st,argl)

fun strip_app_structure st = strip_app_structure0 [] st

fun structure_to_string st = let
  open Kind
  fun recurse paren st =
      case st of
        TYCON {Thy,Tyop,Kind,Rank} => Thy ^ "$" ^ Tyop
      | TYVAR (str,kd,rk) =>
            str ^
            (if kd = typ then "" else " : "^kind_to_string kd) ^
            (if rk = 0   then "" else " :<= "^Int.toString rk)
      | TYAPP (TYAPP (TYCON {Thy="min",Tyop="fun",Kind,Rank}, x), y) =>
                       (if paren then "(" else "") ^
                       recurse true x ^ " -> " ^
                       recurse false y ^
                       (if paren then ")" else "")
      | TYAPP (opr,arg) =>
          let val (st0,args) = strip_app_structure st
          in if length args = 1 then recurse false arg ^ " " ^ structure_to_string opr
             else "(" ^ String.concatWith ", " (map (recurse false) args) ^
                  ") " ^ structure_to_string st0
          end
      | TYABST (bvar,body) =>
                       (if paren then "(" else "") ^ "\\" ^
                       recurse true bvar ^ ". " ^
                       recurse false body ^
                       (if paren then ")" else "")
      | TYUNIV (bvar,body) =>
                       (if paren then "(" else "") ^ "\\" ^
                       recurse true bvar ^ ". " ^
                       recurse false body ^
                       (if paren then ")" else "")
(*
        TYOP {Thy,Tyop,Args} => let
          val opstr = Thy ^ "$" ^ Tyop
        in
          case Args of
            [] => opstr
          | [x] => recurse false x ^ " " ^ opstr
          | [x,y] => if Thy = "min" andalso Tyop = "fun" then
                       (if paren then "(" else "") ^
                       recurse true x ^ " -> " ^
                       recurse false y ^
                       (if paren then ")" else "")
                     else
                       "(" ^ recurse false x ^ ", " ^ recurse false y ^ ") " ^
                       opstr
          | _ => "(" ^ String.concatWith ", " (map (recurse false) Args) ^
                 ") " ^ opstr
        end
*)
      | PARAM (i,kd,rk) => (if i < 4 then List.nth(greek4, i)
                            else "'" ^ str (Char.chr (Char.ord #"a" + i))) ^
                           (if kd = typ then "" else " : "^kind_to_string kd) ^
                           (if rk = 0   then "" else " :<= "^Int.toString rk)
in
  recurse false st
end

val pp_array_types = ref true
val _ = register_btrace ("pp_array_types", pp_array_types)

fun dest_arraytype ty = let
  val {Thy, Tyop, Args} = dest_thy_type ty
in
  if Thy = "fcp" andalso Tyop = "cart" then (hd Args, hd (tl Args))
  else raise ERR "dest_arraytype: not an array type"
end

(* This trace variable is now established in kind_pp.sml.
val show_kinds = ref 1
val _ = Feedback.register_trace("kinds", show_kinds, 2)
*)
val show_kinds = Feedback.get_tracefn "kinds"

val ftyvars_seen = ref ([] : hol_type list)
val btyvars_seen = ref ([] : hol_type list)

fun pp_type0 (G:grammar) backend = let
  val {lambda = lambda, forall = forall} = specials G
  fun lookup_tyop s = let
    fun recurse [] = NONE
      | recurse (x::xs) = let
        in
          case x of
            (p, CONSTANT slist) =>
              if Lib.mem s slist then SOME (p, SR) else recurse xs
          | (p, BINDER slist) => recurse xs
          | (p, APPLICATION) => recurse xs
          | (p, INFIX (slist, a)) => let
              val res = List.find (fn r => #opname r = s) slist
            in
              case res of
                NONE => recurse xs
              | SOME r => SOME(p, IR(a,#parse_string r))
            end
          | (p, CAST) => recurse xs
          | (p, ARRAY_SFX) => recurse xs
        end
  in
    recurse (rules G) : (int * single_rule) option
  end

  fun lookup_tybinder s = let
    fun recurse [] = NONE
      | recurse (x::xs) = let
        in
          case x of
            (p, BINDER slist) =>
              if Lib.exists (Lib.mem s) slist then SOME (p, SR) else recurse xs
          | (p, CONSTANT slist) => recurse xs
          | (p, APPLICATION) => recurse xs
          | (p, INFIX (slist, a)) => let
              val res = List.find (fn r => #opname r = s) slist
            in
              case res of
                NONE => recurse xs
              | SOME r => SOME(p, IR(a,#parse_string r))
            end
          | (p, CAST) => recurse xs
          | (p, ARRAY_SFX) => recurse xs
        end
  in
    recurse (rules G) : (int * single_rule) option
  end

  fun pr_ty binderp pps ty grav depth = let
    open PPBackEnd
    val {add_string, add_break, begin_block, end_block, add_ann_string,...} =
      with_ppstream backend pps
    fun pbegin b = if b then add_string "(" else ()
    fun pend b = if b then add_string ")" else ()
    fun uniconvert s =
        if get_tracefn "Greek tyvars" () = 1 andalso size s = 2 then let
            val i = Char.ord (String.sub(s, 1)) - Char.ord #"a" + 0x3B1
          in
            if 0x3B1 <= i andalso i <= 0x3C9 andalso i <> 0x3BB then UTF8.chr i
            else s
          end
        else s

    fun check_dest_type ty =
      let open Kind
          val (opr,args) = strip_app_type ty
          val {Thy,Tyop,Kind,Rank} = dest_thy_con_type opr
      in if is_arity Kind (*andalso length args = arity_of Kind*)
                          andalso Rank = 0
         then (Tyop,args)
         else raise ERR "check_dest_type: not a traditional type"
      end

    fun print_args grav0 args = let
      val parens_needed = case args of [_] => false | _ => true
      val grav = if parens_needed then Top else grav0
    in
      pbegin parens_needed;
      begin_block INCONSISTENT 0;
      pr_list (fn arg => pr_ty false pps arg grav (depth - 1))
              (fn () => add_string ",") (fn () => add_break (1, 0)) args;
      end_block();
      pend parens_needed
    end

    fun print_skr grav annot (s,k,r) =
        if (k <> Kind.typ orelse r <> 0) andalso show_kinds() = 1 orelse
           show_kinds() = 2
        then let
            val parens_needed =
                 case grav of Top => false | _ => true
          in
            pbegin parens_needed;
            add_ann_string (s, annot);
            if k <> Kind.typ orelse show_kinds() = 2 then let
                val p = r <> 0 andalso not (Kind.is_arity k)
              in
                add_string ": ";
                pbegin p;
                Kind.pp_kind pps k;
                pend p
              end
            else ();
            if r <> 0 orelse show_kinds() = 2 then
              (add_string " :<= "; add_string (Int.toString r))
            else ();
            pend parens_needed
          end
        else add_ann_string (s, annot)

    fun print_var new grav tyv =
      if not (!pp_annotations) then
        add_string (uniconvert (#1 (dest_var_type ty)))
      else
        let val (s,k,r) = dest_var_type tyv
            val s = uniconvert s
            val bound = Lib.mem tyv (!btyvars_seen)
            val kd_annot = (* if k = Kind.typ then "" else *)
                           ": " ^ Kind.kind_to_string k
            val annot = (if bound then TyBV else TyFV)
                        (k, r, s ^ kd_annot)
        in if new then print_skr grav annot (s,k,r)
                  else add_ann_string (s, annot)
        end

    fun print_const grav tyc =
        let val {Thy, Tyop, Kind, Rank} = dest_thy_con_type tyc
            val fullname = Thy ^ "$" ^ Tyop
            val kd_annot = if Kind = Kind.typ then ""
                           else ": " ^ Kind.kind_to_string Kind
            val annot = TyOp (fullname ^ kd_annot)
        in print_skr grav annot (fullname,Kind,Rank)
        end

  in
    if depth = 0 then add_string "..."
    else
      if is_var_type ty then
        let
          val new_freetyvar =
             not (Lib.mem ty (!ftyvars_seen)) andalso
             not (Lib.mem ty (!btyvars_seen))
          val new = new_freetyvar orelse binderp
        in
          if new_freetyvar then ftyvars_seen := ty :: (!ftyvars_seen) else ();
          print_var new grav ty
        end
      else let
          val s = dest_numtype ty
        in
          add_string s
        end handle HOL_ERR _ =>
        let
          val _ = !pp_array_types orelse
                  raise mk_HOL_ERR "" "" "" (* will be caught below *)
          val (bty, cty) = dest_arraytype ty
          (* ignore parenthesis requirements on sub-arguments on assumption that
             all suffixes, including array bracketting, are tightest binders in grammar
             and all at the same tightest level. *)
        in
          pr_ty binderp pps bty grav (depth - 1);
          add_string "[";
          pr_ty binderp pps cty Top (depth - 1);
          add_string "]"
        end handle HOL_ERR _ =>
        if Lib.can check_dest_type ty then
        let
          val (Tyop, Args) = type_grammar.abb_dest_type G ty
          val tooltip =
              if !pp_annotations then
                case Binarymap.peek (type_grammar.abbreviations G, Tyop) of
                  NONE => let
                    val {Thy,Tyop,...} = dest_thy_type ty
                  in
                    Thy ^ "$" ^ Tyop
                  end
                | SOME st => let
                    val numps = num_params st
                  in
                    if 0 < numps then let
                        val params =
                            if numps <= 4 then List.take(greek4, numps)
                            else let
                                fun tab i = str (Char.chr (Char.ord #"e" + i))
                              in
                                greek4 @ List.tabulate(numps - 4, tab)
                              end
                      in
                        UnicodeChars.lambda ^
                        String.concatWith " " params ^ ". " ^
                        structure_to_string st
                      end
                    else structure_to_string st
                  end
              else ""
          fun print_ghastly () = let
            val {Thy,Tyop,...} = dest_thy_type ty
          in
            add_string "(";
            begin_block INCONSISTENT 0;
            if not (null Args) then (print_args Top Args; add_break(1,0))
            else ();
            add_string (Thy ^ "$" ^ Tyop);
            end_block();
            add_string ")"
          end
          fun add_ann_string'(p as (s,ann)) =
              if !pp_annotations then add_ann_string p else add_string s
        in
          case Args of
            [] => let
            in
              case lookup_tyop Tyop of
                NONE => print_ghastly ()
              | _ => add_ann_string' (Tyop, TyOp tooltip)

            end
          | [arg1, arg2] => (let
              val (prec, rule) = valOf (lookup_tyop Tyop)
            in
              case rule of
                SR => let
                  val addparens =
                      case grav of
                        Rfx(n, _) => (n > prec)
                      | _ => false
                in
                  pbegin addparens;
                  begin_block INCONSISTENT 0;
                  (* knowing that there are two args, we know that they will
                     be printed with parentheses, so the gravity we pass in
                     here makes no difference. *)
                  print_args Top Args;
                  add_break(1,0);
                  add_ann_string' (Tyop, TyOp tooltip);
                  end_block();
                  pend addparens
                end
              | IR(assoc, printthis) => let
                  val parens_needed =
                      case grav of
                        Sfx n => (n > prec)
                      | Lfx (n, s) => if s = printthis then assoc <> LEFT
                                      else (n >= prec)
                      | Rfx (n, s) => if s = printthis then assoc <> RIGHT
                                      else (n >= prec)
                      | _ => false
                in
                  pbegin parens_needed;
                  begin_block INCONSISTENT 0;
                  pr_ty binderp pps arg1 (Lfx (prec, printthis)) (depth - 1);
                  add_break(1,0);
                  add_ann_string' (printthis, TySyn tooltip);
                  add_break(1,0);
                  pr_ty binderp pps arg2 (Rfx (prec, printthis)) (depth -1);
                  end_block();
                  pend parens_needed
                end
            end handle Option => print_ghastly())
          | _ => let
              val (prec, _) = valOf (lookup_tyop Tyop)
              val addparens =
                  case grav of
                    Rfx (n, _) => (n > prec)
                  | _ => false
            in
              pbegin addparens;
              begin_block INCONSISTENT 0;
              print_args (Sfx prec) Args;
              add_break(1,0);
              add_ann_string' (Tyop, TyOp tooltip);
              end_block();
              pend addparens
            end handle Option => print_ghastly()
        end
      else let
          (* not a normal "classic" type operator with arguments *)
          open TypeView
          fun add_ann_string'(p as (s,ann)) =
              if !pp_annotations then add_ann_string p else add_string s
        in
          case fromType ty of
            TyV_Const _ => let
              val {Thy,Tyop,Kind,Rank} = dest_thy_con_type ty
            in
              case lookup_tyop Tyop of
                NONE =>  print_const grav ty
              | _ => add_ann_string' (Tyop, TyOp (Thy ^ "$" ^ Tyop))
            end
          | TyV_App _ => let
              val (base, args) = strip_app_type ty
            in
              begin_block INCONSISTENT 0;
              print_args (Sfx 200) args;
              add_break(1,0);
              pr_ty binderp pps base (Sfx 200) (depth - 1);
              end_block ()
            end
          | TyV_Abs _ => let
              val (vars, body) = strip_abs_type ty
              val prev_btyvars_seen = !btyvars_seen
              val _ = btyvars_seen := vars @ prev_btyvars_seen
              val parens = case grav of
                             Top => false
                           | _ => true
                       (*    Lfx _ => true
                           | _ => false *)
            in
              pbegin parens;
              begin_block INCONSISTENT 0;
              add_string (hd lambda);
              pr_list (fn arg => pr_ty true pps arg grav (depth - 1))
                      (fn () => ())
                      (fn () => add_break (1, 0))
                      vars;
              add_string ".";
              add_break (1,0);
              pr_ty false pps body Top (depth - 1);
              end_block ();
              pend parens;
              btyvars_seen := prev_btyvars_seen
            end
          | TyV_All _ => let
              val (vars, body) = strip_univ_type ty
              val prev_btyvars_seen = !btyvars_seen
              val _ = btyvars_seen := vars @ prev_btyvars_seen
              val parens = case grav of
                             Top => false
                           | _ => true
                       (*    Lfx _ => true
                           | _ => false *)
            in
              pbegin parens;
              begin_block INCONSISTENT 0;
              add_string (hd forall);
              pr_list (fn arg => pr_ty true pps arg grav (depth - 1))
                      (fn () => ())
                      (fn () => add_break (1, 0))
                      vars;
              add_string ".";
              add_break (1,0);
              pr_ty false pps body Top (depth - 1);
              end_block ();
              pend parens;
              btyvars_seen := prev_btyvars_seen
            end
          | _ => raise Fail "type_pp: this can't happen"
        end
  end
in
  pr_ty
end

fun pp_type G backend = let
  val baseprinter = pp_type0 G backend
in
  (fn pps => fn ty => baseprinter false pps ty Top (!Globals.max_print_depth))
end

fun pp_type_with_depth G backend = let
  val baseprinter = pp_type0 G backend
in
  (fn pps => fn depth => fn ty => baseprinter false pps ty Top depth)
end

end; (* struct *)

(* testing

val G = parse_type.BaseHOLgrammar;
fun p ty =
  Portable.pp_to_string 75
   (fn pp => fn ty => type_pp.pp_type G pp ty type_pp.Top 100) ty;

new_type {Name = "fmap", Arity = 2};

val G' = [(0, parse_type.INFIX("->", "fun", parse_type.RIGHT)),
     (1, parse_type.INFIX("=>", "fmap", parse_type.NONASSOC)),
     (2, parse_type.INFIX("+", "sum", parse_type.LEFT)),
     (3, parse_type.INFIX("#", "prod", parse_type.RIGHT)),
     (100, parse_type.CONSTANT("list", true)),
     (101, parse_type.CONSTANT("fun", false)),
     (102, parse_type.CONSTANT("prod", false)),
     (103, parse_type.CONSTANT("sum", false))];
fun p ty =
  Portable.pp_to_string 75
   (fn pp => fn ty => type_pp.pp_type G' pp ty type_pp.Top 100) ty;

p (Type`:(bool,num)fmap`)

*)
