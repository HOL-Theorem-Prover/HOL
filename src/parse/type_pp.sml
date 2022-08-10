structure type_pp :> type_pp =
struct

open Feedback Type Portable HOLgrammars type_grammar

datatype mygrav = Sfx
                | Lfx of int * string
                | Rfx of int * string
                | Top

datatype single_rule = IR of int * associativity * string

val ERR = mk_HOL_ERR "type_pp" "pp_type";

val avoid_unicode = ref (Systeml.OS = "winNT")
local
  open Globals
  fun ascii_delims () =
    (List.app (fn r => r := "``") [type_pp_prefix, type_pp_suffix,
                                   term_pp_prefix, term_pp_suffix];
     thm_pp_prefix := "|- ";
     thm_pp_suffix := "")
  fun unicode_delims () =
    (List.app (fn r => r := UnicodeChars.ldquo)
              [type_pp_prefix, term_pp_prefix];
     List.app (fn r => r := UnicodeChars.rdquo)
              [type_pp_suffix, term_pp_suffix];
     thm_pp_prefix := UnicodeChars.turnstile ^ " ";
     thm_pp_suffix := "")
  fun avoidset i = if i = 0 then (unicode_delims(); avoid_unicode := false)
                   else (ascii_delims(); avoid_unicode := true)
  fun avoidget () = if !avoid_unicode then 1 else 0
in

val _ = register_ftrace("PP.avoid_unicode", (avoidget, avoidset), 1)
val _ = register_ftrace("Unicode",
                        (fn () => 1 - avoidget(), fn n => avoidset (1 - n)),
                        1)
val _ = avoidset (avoidget())
end


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

fun structure_to_string st = let
  fun recurse paren st =
      case st of
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
      | PARAM i => if i < 4 then List.nth(greek4, i)
                   else "'" ^ str (Char.chr (Char.ord #"a" + i))
in
  recurse false st
end

val pp_array_types = ref true
val _ = register_btrace ("pp_array_types", pp_array_types)

fun pp_type0 (G:grammar) (backend: PPBackEnd.t) = let
  val {infixes,suffixes} = rules G
  fun lookup_tyop s = let
    fun recurse [] = NONE
      | recurse (x::xs) = let
        in
          case x of
            (p, INFIX (slist, a)) => let
              val res = List.find (fn r => #opname r = s) slist
            in
              case res of
                NONE => recurse xs
              | SOME r => SOME(IR(p, a,#parse_string r))
            end
        end
  in
    recurse infixes : single_rule option
  end
  fun pr_ty ty grav depth = let
    open HOLPP smpp PPBackEnd
    val {add_string, add_break, ublock, add_xstring,...} = backend
    fun add_ann_string (s,ann) = add_xstring {s=s,ann=SOME ann,sz=NONE}
    fun paren b p =
        if b then add_string "(" >> ublock INCONSISTENT 1 p >> add_string ")"
        else p
    fun uniconvert s =
        if not (!avoid_unicode) andalso get_tracefn "Greek tyvars" () = 1
           andalso size s = 2
        then
          let
            val i = Char.ord (String.sub(s, 1)) - Char.ord #"a" + 0x3B1
          in
            if 0x3B1 <= i andalso i <= 0x3C9 andalso i <> 0x3BB then UTF8.chr i
            else s
          end
        else s
  in
    if depth = 0 then add_string "..."
    else
      if is_vartype ty then
        add_ann_string (uniconvert (dest_vartype ty), TyV)
      else let
          val s = dest_numtype ty
        in
          add_string s
        end handle HOL_ERR _ =>
        let
          fun realtype ty = let val {Thy,Tyop,...} = dest_thy_type ty
                            in Thy ^ "$" ^ Tyop end
          val {Tyop = abop, Args = abargs, Thy = thyopt} =
              type_grammar.abb_dest_type G ty
          val abop_s =
              case thyopt of
                  NONE => abop
                | SOME thy => KernelSig.name_toString {Thy = thy, Name = abop}
          fun tooltip () =
            let
              val abbs = type_grammar.parse_map G
              fun doabbrev st =
                let
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
            in
              case thyopt of
                SOME thy => (* unprivileged abbrev *)
                let
                  val knm = {Thy = thy, Name = abop}
                in
                  case Binarymap.peek (abbs, knm) of
                      NONE => realtype ty (* probably shouldn't happen *)
                    | SOME st => doabbrev st
                end
              | NONE =>
                let
                  val privabbs = type_grammar.privileged_abbrevs G
                in
                  case Binarymap.peek (privabbs, abop) of
                      NONE => realtype ty
                    | SOME thy =>
                      let
                        val knm = {Thy = thy, Name = abop}
                      in
                        case Binarymap.peek (abbs, knm) of
                            NONE => raise Fail "Very confused tyabbrev"
                          | SOME st => doabbrev st
                      end
                end
            end
          fun print_args grav0 args = let
            val parens_needed = case args of [_] => false | _ => true
            val grav = if parens_needed then Top else grav0
          in
            paren parens_needed (
              ublock INCONSISTENT 0 (
                pr_list (fn arg => pr_ty arg grav (depth - 1))
                        (add_string "," >> add_break (1, 0)) args
              )
            )
          end
          val {Thy, Tyop = realTyop, Args = realArgs} = dest_thy_type ty
        in
          if abop = "cart" andalso length abargs = 2 andalso
             Thy = "fcp" andalso realTyop = "cart" andalso !pp_array_types
          then
            pr_ty (hd realArgs) Sfx (depth - 1) >>
            add_string "[" >>
            pr_ty (hd (tl realArgs)) Top (depth - 1) >>
            add_string "]"
          else
            case abargs of
              [] => add_ann_string (abop_s, TyOp tooltip)
            | [arg1, arg2] =>
              let
                fun print_suffix_style () =
                   ublock INCONSISTENT 0 (
                    (* knowing that there are two args, we know that they will
                       be printed with parentheses, so the gravity we pass in
                       here makes no difference. *)
                     print_args Top abargs >>
                     add_break(1,0) >>
                     add_ann_string (abop_s, TyOp tooltip)
                   )
              in
                if isSome thyopt then print_suffix_style()
                else
                  case lookup_tyop abop of
                      SOME (IR(prec, assoc, printthis)) =>
                      let
                        val parens_needed =
                            case grav of
                                Sfx => true
                              | Lfx (n, s) => if s = printthis then
                                                assoc <> LEFT
                                              else (n >= prec)
                              | Rfx (n, s) => if s = printthis then
                                                assoc <> RIGHT
                                              else (n >= prec)
                              | _ => false
                      in
                        paren parens_needed (
                          ublock INCONSISTENT 0 (
                            pr_ty arg1 (Lfx (prec, printthis)) (depth - 1) >>
                            add_break(1,0) >>
                            add_ann_string (printthis, TySyn tooltip) >>
                            add_break(1,0) >>
                            pr_ty arg2 (Rfx (prec, printthis)) (depth -1)
                          )
                        )
                      end
                    | NONE => print_suffix_style()
              end
            | _ =>
                ublock INCONSISTENT 0 (
                  print_args Sfx abargs >>
                  add_break(1,0) >>
                  add_ann_string (abop_s, TyOp tooltip)
                )
          end
  end
in
  pr_ty
end

fun pp_type G backend = let
  val baseprinter = pp_type0 G backend
in
  (fn ty => baseprinter ty Top (!Globals.max_print_depth))
end

fun pp_type_with_depth G backend = let
  val baseprinter = pp_type0 G backend
in
  (fn depth => fn ty => baseprinter ty Top depth)
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
     (100, parse_type.SUFFIX("list", true)),
     (101, parse_type.SUFFIX("fun", false)),
     (102, parse_type.SUFFIX("prod", false)),
     (103, parse_type.SUFFIX("sum", false))];
fun p ty =
  Portable.pp_to_string 75
   (fn pp => fn ty => type_pp.pp_type G' pp ty type_pp.Top 100) ty;

p (Type`:(bool,num)fmap`)

*)
