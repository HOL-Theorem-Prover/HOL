structure parse_type :> parse_type =
struct

open type_tokens type_grammar HOLgrammars monadic_parse optmonad

infix >- ++ >> >->

fun parse_type tyfns allow_unknown_suffixes G = let
  val G = rules G and abbrevs = abbreviations G
  val {vartype = pVartype, tyop = pType, antiq = pAQ, qtyop} = tyfns
  fun structure_to_value s args st =
      case st of
        TYOP {Args, Thy, Tyop} =>
        qtyop {Args = map (structure_to_value s args) Args,
               Thy = Thy, Tyop = Tyop}
      | PARAM n => List.nth(args, n)
        handle Subscript =>
               Feedback.Raise
                 (Feedback.mk_HOL_ERR
                    "Parse" "parse_type"
                    ("Insufficient arguments to abbreviated operator " ^
                     Lib.quote s))

  val lex = type_tokens.lex
  (* extra fails on next two definitions will effectively make the stream
     push back the unwanted token *)
  fun itemP P = (lex >- (fn t => if P t then return t else fail)) ++ fail

  (* can't use item for these, because this would require the token type
     to be an equality type, which is icky *)
  fun is_LParen t = case t of LParen => true | _ => false
  fun is_RParen t = case t of RParen => true | _ => false
  fun is_Comma t = case t of Comma => true | _ => false

  fun apply_tyop t args =
    case t of
      TypeIdent s => let
      in
        case Binarymap.peek(abbrevs, s) of
          NONE => pType(s,args)
        | SOME st => structure_to_value s args st
      end
    | QTypeIdent(thy,ty) => qtyop{Thy=thy,Tyop=ty,Args=args}
    | _ => raise Fail "parse_type.apply_tyop: can't happen"

  fun n_appls (ops, t) =
    case ops of
      [] => t
    | oph::opt => n_appls (opt, apply_tyop oph [t])
  fun n_appls_l ([], t) = raise Fail "parse_type.n_appls_l: can't happen"
    | n_appls_l (op1::ops, xs) = n_appls (ops, apply_tyop op1 xs)
  fun parse_base_level f =
    lex >-
    (fn t =>
     case t of
       TypeIdent s => return (apply_tyop t [])
     | QTypeIdent(thy,ty) => return (qtyop{Thy = thy, Tyop = ty, Args = []})
     | TypeVar s => return (pVartype s)
     | AQ x => return (pAQ x)
     | LParen => (f >-> itemP is_RParen)
     | _ => fail)

  fun parse_op slist =
    lex >-
    (fn t =>
     case t of
       TypeIdent s =>
         if allow_unknown_suffixes orelse Lib.mem s slist then return t
         else fail
     | QTypeIdent _ => return t
     | _ => fail)
  fun parse_binop stlist = let
    fun doit t =
      case List.find (fn r => (#parse_string r = token_string t)) stlist of
        NONE => fail
      | SOME r => return (TypeIdent (#opname r))
  in
    (itemP is_ident ++ itemP is_typesymbol) >-  doit
  end


  fun parse_term current strm =
    (case current of
       [] => parse_base_level (parse_term G)
     | (x::xs) => parse_rule x xs) strm
  and parse_rule (r as (level, rule)) rs strm = let
    val next_level = parse_term rs
    val same_level = parse_rule r rs
    val tuple_arg =
      itemP is_LParen >>
      chainl1
      (parse_term G >- (fn t => return [t]))
      (itemP is_Comma >> return (fn tl1 => fn tl2 => tl1 @ tl2)) >-
      (fn args => itemP is_RParen >> return args)
  in
    (case rule of
       INFIX (stlist, NONASSOC) =>
         next_level >-                         (fn t1 =>
         (parse_binop stlist >-                (fn opname =>
          next_level >-                        (fn t2 =>
          return (apply_tyop opname [t1, t2])))) ++
         (return t1))
     | INFIX (stlist, LEFT) =>
         chainl1 next_level
         (parse_binop stlist >-
          (fn opname => return (fn t1 => fn t2 => apply_tyop opname [t1, t2])))
     | INFIX (stlist, RIGHT) =>
         chainr1 next_level
         (parse_binop stlist >-
          (fn opname => return (fn t1 => fn t2 => apply_tyop opname [t1, t2])))
     | SUFFIX slist =>
         (next_level >-                             (fn t =>
          many (parse_op slist) >-                  (fn oplist =>
          return (n_appls (oplist, t))))) ++
         (tuple_arg >-                              (fn args =>
          many1 (parse_op slist) >-                 (fn oplist =>
          return (n_appls_l (oplist, args)))))) strm
  end
in
  parse_term G
end


end; (* struct *)
