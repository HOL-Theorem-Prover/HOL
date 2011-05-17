structure type_pp :> type_pp =
struct

open Feedback Type Portable HOLgrammars type_grammar

datatype mygrav = Sfx
                | Lfx of int * string
                | Rfx of int * string
                | Top

datatype single_rule
   = SR
   | IR of int * associativity * string

val PP_ERR = mk_HOL_ERR "type_pp";

val ERR = mk_HOL_ERR "type_pp" "pp_type";

val pp_num_types = ref true
val _ = register_btrace("pp_num_types", pp_num_types)

val pp_annotations = ref (!Globals.interactive)
val _ = register_btrace ("pp_annotations", pp_annotations)

(* Modest reimplementation of kind printing, before Parse *)
val pp_kind = kind_pp.pp_kind kind_grammar.min_grammar PPBackEnd.raw_terminal;
val kind_to_string = Portable.pp_to_string (!Globals.linewidth) pp_kind

(*
fun dest_var_st (TYVAR triple) = triple
  | dest_var_st _ = raise GrammarError "dest_var_st: not a type variable"

fun is_abs_st (TYABST _) = true
  | is_abs_st _ = false;

fun dest_abs_st (TYABST p) = p
  | dest_abs_st _ = raise GrammarError "dest_abs_st: not a type abstraction"

fun strip_abs_st (TYABST (bvar,body)) =
  let val (bvars,body1) = strip_abs_st body
  in (bvar::bvars, body1)
  end
  | strip_abs_st ty = ([],ty)
*)
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
  open Rank Kind
  fun recurse paren st =
      case st of
        TYCON {Thy,Tyop,Kind} => Thy ^ "$" ^ Tyop
      | TYVAR (str,kd) =>
          let val paren = not (kd = typ rho) andalso not (is_var_kind kd)
          in
            (if paren then "(" else "") ^
            str ^
            (if kd = typ rho then "" else " : "^kind_to_string kd) ^
            (if paren then ")" else "")
          end
      | TYAPP (TYAPP (TYCON {Thy="min",Tyop="fun",Kind}, x), y) =>
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
      | PARAM (i,kd) => (if i < 4 then List.nth(greek4, i)
                         else "'" ^ str (Char.chr (Char.ord #"a" + i))) ^
                        (if kd = typ rho then "" else " : "^kind_to_string kd)
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

val show_kinds = Feedback.get_tracefn "kinds"

val ftyvars_seen = ref ([] : hol_type list)
val btyvars_seen = ref ([] : hol_type list)

fun pp_type0 (G:grammar) backend = let
  val {lambda = lambda, forall = forall, exists = exists} = specials G
  fun lookup_tyop s = let
    fun recurse [] = NONE
      | recurse (x::xs) = let
        in
          case x of
            (p, CONSTANT slist) =>
              if Lib.mem s slist then SOME SR else recurse xs
          | (p, BINDER slist) => recurse xs
          | (p, APPLICATION) => recurse xs
          | (p, INFIX (slist, a)) => let
              val res = List.find (fn r => #opname r = s) slist
            in
              case res of
                NONE => recurse xs
              | SOME r => SOME(IR(p, a,#parse_string r))
            end
          | (p, CAST) => recurse xs
        end
  in
    recurse (rules G) : single_rule option
  end

  fun lookup_tybinder s = let
    fun recurse [] = NONE
      | recurse (x::xs) = let
        in
          case x of
            (p, BINDER slist) =>
              if Lib.exists (Lib.mem s) slist then SOME SR else recurse xs
          | (p, CONSTANT slist) => recurse xs
          | (p, APPLICATION) => recurse xs
          | (p, INFIX (slist, a)) => let
              val res = List.find (fn r => #opname r = s) slist
            in
              case res of
                NONE => recurse xs
              | SOME r => SOME(IR(p, a,#parse_string r))
            end
          | (p, CAST) => recurse xs
        end
  in
    recurse (rules G) : single_rule option
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
          val {Thy,Tyop,Kind} = dest_thy_con_type opr
      in if is_arity Kind (*andalso length args = arity_of Kind*)
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

    fun add_ann_string'(p as (s,ann)) =
              (*if !pp_annotations then*) add_ann_string p (*else add_string s*)

    fun print_sk grav annot (s,k) =
      let open Rank Kind
      in
        if (k <> typ rho) andalso show_kinds() = 1
           orelse show_kinds() = 2
        then let
            val parens_needed =
                 case grav of Top => false | _ => true
          in
            pbegin parens_needed;
            add_ann_string' (s, annot);
            if k <> typ rho orelse show_kinds() = 2 then let
                val p = rank_of k <> rho andalso not (Kind.is_arity k)
              in
                add_string ": ";
                pbegin p;
                pp_kind pps k;
                pend p
              end
            else ();
            pend parens_needed
          end
        else add_ann_string' (s, annot)
      end

    fun print_var new grav tyv =
        let val (s,k) = dest_var_type tyv
            val s = uniconvert s
            val bound = binderp orelse Lib.mem tyv (!btyvars_seen)
            val kd_annot = (* if k = Kind.typ then "" else *)
                           ": " ^ kind_to_string k
            val annot = (if bound then TyBV else TyFV)
                        (k, fn () => s ^ kd_annot)
        in if new then print_sk grav annot (s,k)
                  else add_ann_string' (s, annot)
        end
    fun print_vars [] = ()
      | print_vars (v::vs) = (print_var true Top v; add_string ","; print_vars vs)

    fun print_const grav tyc =
        let val {Thy, Tyop, Kind} = dest_thy_con_type tyc
            val fullname = Thy ^ "$" ^ Tyop
            val kd_annot = if Kind = Kind.typ Rank.rho then ""
                           else ": " ^ kind_to_string Kind
            val annot_str = fullname ^ kd_annot
            val annot = TyOp (fn () => annot_str)
        in print_sk grav annot (fullname,Kind)
        end

  in
    if depth = 0 then add_string "..."
    else
      if is_var_type ty then
        let
          val new_freetyvar =
             not binderp andalso
             not (Lib.mem ty (!ftyvars_seen)) andalso
             not (Lib.mem ty (!btyvars_seen))
          val new = binderp orelse new_freetyvar
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
          (* ignore parenthesis requirements on sub-arguments knowing that
             all suffixes, including array bracketting, are tightest binders
             in grammar and all at the same tightest level. *)
        in
          pr_ty binderp pps bty Sfx (depth - 1);
          add_string "[";
          pr_ty binderp pps cty Top (depth - 1);
          add_string "]"
        end handle HOL_ERR _ =>
       (* if Lib.can check_dest_type ty then *)
        let
          val (Tyop, Args) = type_grammar.abb_dest_type G ty
          fun tooltip () =
              case Binarymap.peek (type_grammar.abbreviations G, Tyop) of
                NONE => let
                  val {Thy,Tyop,...} = dest_thy_type ty
                in
                    Thy ^ "$" ^ Tyop
                  end
              | SOME (st as TYABST _) => let
                  val st' = type_grammar.conform_structure_to_type (type_grammar.rules G) Tyop st ty
                in
                  structure_to_string st'
                end
              | SOME st => (* pre-HOL-Omega type structures *) let
                  (* val st = valOf (Binarymap.peek (type_grammar.abbreviations G, Tyop)) *) (* repeat? *)
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
        in
          case Args of
            [] => let
            in
              case lookup_tyop Tyop of
                NONE => print_ghastly ()
              | _ => add_ann_string (Tyop, TyOp tooltip)

            end
          | [arg1, arg2] => (let
              val rule = valOf (lookup_tyop Tyop)
            in
              case rule of
                SR => let
                in
                  begin_block INCONSISTENT 0;
                  (* knowing that there are two args, we know that they will
                     be printed with parentheses, so the gravity we pass in
                     here makes no difference. *)
                  print_args Top Args;
                  add_break(1,0);
                  add_ann_string (Tyop, TyOp tooltip);
                  end_block()
                end
              | IR(prec, assoc, printthis) => let
                  val parens_needed =
                      case grav of
                        Sfx => true
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
                  add_ann_string (printthis, TySyn tooltip);
                  if current_trace "kinds" < 2 then () else
                    let val rk = rank_of_type (#1 (strip_app_type ty))
                    in if rk = Rank.rho then () else
                        add_string (":" ^ Rank.rank_to_string rk)
                    end;
                  add_break(1,0);
                  pr_ty binderp pps arg2 (Rfx (prec, printthis)) (depth -1);
                  end_block();
                  pend parens_needed
                end
            end handle Option => print_ghastly())
          | _ => let
            in
              case lookup_tyop Tyop of
                NONE => print_ghastly()
              | SOME _ => let
                in
                  begin_block INCONSISTENT 0;
                  print_args Sfx Args;
                  add_break(1,0);
                  add_ann_string (Tyop, TyOp tooltip);
                  end_block()
                end
            end
        end
     (* else let *)
        handle HOL_ERR _ => let
          (* not a normal "classic" type operator with arguments *)
          open TypeView
          fun add_ann_string'(p as (s,ann)) =
              if !pp_annotations then add_ann_string p else add_string s
        in
          case fromType ty of
            TyV_Const _ => let
              val {Thy,Tyop,Kind} = dest_thy_con_type ty
            in
              case lookup_tyop Tyop of
                NONE =>  print_const grav ty
              | _ => add_ann_string' (Tyop, TyOp (fn () => Thy ^ "$" ^ Tyop))
            end
          | TyV_App _ => let
              val (base, args) = strip_app_type ty
            in
              begin_block INCONSISTENT 0;
              print_args Sfx args;
              add_break(1,0);
              pr_ty binderp pps base Sfx (depth - 1);
              end_block ()
            end
          | TyV_Abs _ => let
              val (vars, body) = strip_abs_type ty
              val prev_btyvars_seen = !btyvars_seen
              val parens = case grav of
                             Top => false
                           | _ => true
                       (*    Lfx _ => true
                           | _ => false *)
            in
              pbegin parens;
              begin_block CONSISTENT 2;
              add_string (hd lambda);
              begin_block INCONSISTENT 2;
              pr_list (fn arg => pr_ty true pps arg grav (depth - 1))
                      (fn () => ())
                      (fn () => add_break (1, 0))
                      vars;
              end_block ();
              add_string ".";
              btyvars_seen := vars @ prev_btyvars_seen;
              add_break (1,0);
              pr_ty false pps body Top (depth - 1);
              end_block ();
              pend parens;
              btyvars_seen := prev_btyvars_seen
            end
          | TyV_All _ => let
              val existential = HolKernel.is_exist_type ty
              val (vars, body) = (if existential then HolKernel.strip_exist_type
                                                 else strip_univ_type ) ty
              val prev_btyvars_seen = !btyvars_seen
              val parens = case grav of
                             Top => false
                           | _ => true
                       (*    Lfx _ => true
                           | _ => false *)
            in
              pbegin parens;
              begin_block CONSISTENT 2;
              add_string (hd (if existential then exists else forall));
              begin_block INCONSISTENT 2;
              pr_list (fn arg => pr_ty true pps arg grav (depth - 1))
                      (fn () => ())
                      (fn () => add_break (1, 0))
                      vars;
              end_block ();
              add_string ".";
              btyvars_seen := vars @ prev_btyvars_seen;
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

fun pp_type_cont G backend binderp = let
  val baseprinter = pp_type0 G backend binderp
in
  (fn pps => fn ty => baseprinter pps ty Top (!Globals.max_print_depth))
end

fun pp_type_with_depth_cont G backend binderp = let
  val baseprinter = pp_type0 G backend binderp
in
  (fn pps => fn depth => fn ty => baseprinter pps ty Top depth)
end

fun pp_type G backend = let
  val printer = pp_type_cont G backend
  val _ = ftyvars_seen := []
in
  printer
end

fun pp_type_with_depth G backend = let
  val printer = pp_type_with_depth_cont G backend
  val _ = ftyvars_seen := []
in
  printer
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
