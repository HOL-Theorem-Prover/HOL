structure kind_pp :> kind_pp =
struct

open Feedback Kind Portable HOLgrammars kind_grammar

datatype mygrav
   = Pfx of int
   | Lfx of int * string
   | Rfx of int * string
   | Top

datatype single_rule
   = SR
   | IR of associativity * string

val ERR = mk_HOL_ERR "kind_pp" "pp_kind";

val pp_arity_kinds = ref true
val _ = register_btrace("pp_arity_kinds", pp_arity_kinds)

fun dest_arity_kind kd = Kind.arity_of kd
       handle HOL_ERR _ => raise ERR "not an arity kind"

val show_kinds = ref 0
val _ = Feedback.register_trace("kinds", show_kinds, 2)

fun pp_kind0 (G:grammar) = let
  fun lookup_kindop s = let
    fun recurse [] = NONE
      | recurse (x::xs) = let
        in
          case x of
            (p, PREFIX slist) =>
              if Lib.mem s slist then SOME (p, SR) else recurse xs
          | (p, INFIX (slist, a)) => let
              val res = List.find (fn r => #opname r = s) slist
            in
              case res of
                NONE => recurse xs
              | SOME r => SOME(p, IR(a,#parse_string r))
            end
          | (p, NONFIX) => recurse xs
        end
  in
    recurse (rules G) : (int * single_rule) option
  end

  fun pr_kd pps kd grav depth = let
    val {add_string, add_break, begin_block, end_block,...} =
      with_ppstream pps
    fun pbegin b = if b then add_string "(" else ()
    fun pend b = if b then add_string ")" else ()

    fun print_args grav0 args = let
      val parens_needed = case args of [_] => false | _ => true
      val grav = if parens_needed then Top else grav0
    in
      pbegin parens_needed;
      begin_block INCONSISTENT 0;
      pr_list (fn arg => pr_kd pps arg grav (depth - 1))
              (fn () => add_string ",") (fn () => add_break (1, 0)) args;
      end_block();
      pend parens_needed
    end

  in
    if depth = 0 then add_string "..."
    else if kd = Kind.typ then add_string "ty"
    else
        let val _ = Lib.assert (Lib.equal true) (!pp_arity_kinds)
          val s = Int.toString (dest_arity_kind kd)
        in
          add_string ("ar "  ^ s)
        end handle HOL_ERR _ =>
        let val (dom,rng) = kind_dom_rng kd
            val Tyop = "=>"
            val Args = [dom,rng]
          in
            case Args of
              [arg1, arg2] =>
              (let
                 val (prec, rule) = valOf (lookup_kindop Tyop)
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
                     add_string Tyop;
                     end_block();
                     pend addparens
                   end
                 | IR(assoc, printthis) => let
                     val parens_needed =
                         case grav of
                           Pfx n => (n > prec)
                         | Lfx (n, s) => if s = printthis then assoc <> LEFT
                                         else (n >= prec)
                         | Rfx (n, s) => if s = printthis then assoc <> RIGHT
                                         else (n >= prec)
                         | _ => false
                   in
                     pbegin parens_needed;
                     begin_block INCONSISTENT 0;
                     pr_kd pps arg1 (Lfx (prec, printthis)) (depth - 1);
                     add_break(1,0);
                     add_string printthis;
                     add_break(1,0);
                     pr_kd pps arg2 (Rfx (prec, printthis)) (depth - 1);
                     end_block();
                     pend parens_needed
                   end
               end handle Option => raise ERR ("prettyprinting rule not found for kind operator "
                                               ^ "\"" ^ Tyop ^ "\""))
            | _ => let
                val (prec, _) = valOf (lookup_kindop Tyop)
                val addparens =
                    case grav of
                      Rfx (n, _) => (n > prec)
                    | _ => false
              in
                pbegin addparens;
                begin_block INCONSISTENT 0;
                print_args (Pfx prec) Args;
                add_break(1,0);
                add_string Tyop;
                end_block();
                pend addparens
              end handle Option => raise ERR ("prettyprinting rule not found for kind operator "
                                               ^ "\"" ^ Tyop ^ "\"")
          end
  end
in
  pr_kd
end

fun pp_kind G = let
  val baseprinter = pp_kind0 G
in
  (fn pps => fn kd => baseprinter pps kd Top (!Globals.max_print_depth))
end

fun pp_kind_with_depth G = let
  val baseprinter = pp_kind0 G
in
  (fn pps => fn depth => fn kd => baseprinter pps kd Top depth)
end

end; (* struct *)

(* testing

val G = parse_kind.BaseHOLgrammar;
fun p kd =
  Portable.pp_to_string 75
   (fn pp => fn kd => kind_pp.pp_kind G pp kd kind_pp.Top 100) kd;

new_kind {Name = "fmap", Arity = 2};

val G' = [(0, parse_kind.INFIX("->", "fun", parse_kind.RIGHT)),
     (1, parse_kind.INFIX("=>", "fmap", parse_kind.NONASSOC)),
     (2, parse_kind.INFIX("+", "sum", parse_kind.LEFT)),
     (3, parse_kind.INFIX("#", "prod", parse_kind.RIGHT)),
     (100, parse_kind.SUFFIX("list", true)),
     (101, parse_kind.SUFFIX("fun", false)),
     (102, parse_kind.SUFFIX("prod", false)),
     (103, parse_kind.SUFFIX("sum", false))];
fun p kd =
  Portable.pp_to_string 75
   (fn pp => fn kd => kind_pp.pp_kind G' pp kd kind_pp.Top 100) kd;

p (Kind`:(bool,num)fmap`)

*)
