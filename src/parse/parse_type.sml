structure parse_type :> parse_type =
struct

open type_tokens type_grammar HOLgrammars

open qbuf

exception InternalFailure

val ERR = Feedback.mk_HOL_ERR "parse_type"

fun totalify f x = SOME (f x) handle InternalFailure => NONE

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

  (* extra fails on next two definitions will effectively make the stream
     push back the unwanted token *)
  (* can't use item for these, because this would require the token type
     to be an equality type, which is icky *)
  fun is_LParen t = case t of LParen => true | _ => false
  fun is_RParen t = case t of RParen => true | _ => false
  fun is_Comma t = case t of Comma => true | _ => false
  fun itemP P fb = let
    val (adv, (t,locn)) = typetok_of fb (* TODO:KSW: use locn *)
  in
    if P t then adv() else raise InternalFailure
  end

  fun many f fb = let
    fun recurse acc =
        case totalify f fb of
          NONE => List.rev acc
        | SOME i => recurse (i::acc)
  in
    recurse []
  end

  fun many1 f fb = let
    val i1 = f fb
    fun recurse acc =
        case totalify f fb of
          NONE => List.rev acc
        | SOME i => recurse (i::acc)
  in
    recurse [i1]
  end

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



  fun parse_base_level f fb = let
    val (advance, (t,locn)) = typetok_of fb (* TODO:KSW: use locn *)
  in
    case t  of
      TypeVar s => (advance(); pVartype s)
    | TypeIdent s => (advance (); apply_tyop t [])
    | QTypeIdent(thy, ty) => (advance ();
                              qtyop{Thy = thy, Tyop = ty, Args = []})
    | AQ x => (advance (); pAQ x)
    | LParen => let
        val _ = advance ()
        val ty = f fb
        val _ = itemP is_RParen
      in
        ty
      end
    | _ => raise InternalFailure
  end

  fun parse_op slist fb = let
    val (adv, (t,locn)) = typetok_of fb (* TODO:KSW: use locn *)
  in
    case t of
      TypeIdent s => if allow_unknown_suffixes orelse Lib.mem s slist then
                       (adv(); t)
                     else raise InternalFailure
    | QTypeIdent _ => (adv(); t)
    | _ => raise InternalFailure
  end

  fun parse_binop stlist fb = let
    val (adv, (t,locn)) = typetok_of fb (* TODO:KSW: use locn *)
    fun doit t =
      case List.find (fn r => (#parse_string r = token_string t)) stlist of
        NONE => raise InternalFailure
      | SOME r => (adv(); TypeIdent (#opname r))
  in
    case t of
      TypeIdent s => doit t
    | TypeSymbol s => doit t
    | _ => raise InternalFailure
  end


  fun parse_tuple prse fb = let
    val _ = itemP is_LParen fb
    val ty1 = prse fb
    fun recurse acc = let
      val (adv,(t,locn)) = typetok_of fb (* TODO:KSW: use locn *)
    in
      case t of
        RParen => (adv(); List.rev acc)
      | Comma => (adv(); recurse (prse fb :: acc))
      | _ => raise InternalFailure
    end
  in
    recurse [ty1]
  end

  fun parse_term current strm =
      case current of
        [] => parse_base_level (parse_term G) strm
      | (x::xs) => parse_rule x xs strm
  and parse_rule (r as (level, rule)) rs strm = let
    val next_level = parse_term rs
    val same_level = parse_rule r rs
  in
    case rule of
      INFIX (stlist, NONASSOC) => let
        val ty1 = next_level strm
      in
        case totalify (parse_binop stlist) strm of
          NONE => ty1
        | SOME opn => apply_tyop opn [ty1, next_level strm]
      end
    | INFIX (stlist, LEFT) => let
        val ty1 = next_level strm
        fun recurse acc =
            case totalify (parse_binop stlist) strm of
              NONE => acc
            | SOME opn => recurse (apply_tyop opn [acc, next_level strm])
      in
        recurse ty1
      end
    | INFIX (stlist, RIGHT) => let
        val ty1 = next_level strm
      in
        case totalify (parse_binop stlist) strm of
          NONE => ty1
        | SOME opn => apply_tyop opn [ty1, same_level strm]
      end
    | SUFFIX slist => let
      in
        case totalify (parse_tuple (parse_term G)) strm of
          NONE => let
            val ty1 = next_level strm
            val ops = many (parse_op slist) strm
          in
            n_appls(ops, ty1)
          end
        | SOME tyl => let
          in
            case (many (parse_op slist) strm) of
              [] => if length tyl <> 1 then
                      raise ERR "parse_type" "tuple with no suffix"
                    else
                      hd tyl
            | oplist => n_appls_l (oplist, tyl)
          end
      end
  end
in
  fn qb => parse_term G qb
     handle InternalFailure =>
            raise ERR "parse_type"
                  ("Type parsing failure with remaining input: "^
                   qbuf.toString qb)
end


end; (* struct *)
