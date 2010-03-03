structure parse_kind :> parse_kind =
struct

open kind_tokens kind_grammar HOLgrammars

open qbuf

exception InternalFailure of locn.locn

type ('a,'b) kindconstructors =
     {varkind : string locn.located -> 'a,
      kindop : (string locn.located * 'a list) -> 'a,
      qkindop : {Thy:string, Kindop:string, Locn:locn.locn, Args: 'a list} -> 'a,
      arity : (string locn.located * int) -> 'a,
      antiq : 'b -> 'a}

val ERR = Feedback.mk_HOL_ERR "Parse" "parse_kind"

val ERRloc = Feedback.mk_HOL_ERRloc "Parse" "parse_kind"

(* antiquoting kinds into types *)
local
  val ERR2 = Feedback.mk_HOL_ERR "Parse" "dest_kd_antiq" "not a kind antiquotation"
in
fun kd_antiq kd = Type.mk_var_type("'kd_antiq",kd,0)

fun dest_kd_antiq ty =
  case Lib.with_exn Type.dest_var_type ty ERR2
   of ("'kd_antiq",Kd,0) => Kd
    |  _ => raise ERR2

val is_kd_antiq = Lib.can dest_kd_antiq
end

(* antiquoting types into terms *)
local
  open Term Type Kind
  infixr ==>
  val ERR2 = Feedback.mk_HOL_ERR "Parse" "dest_ty_antiq" "not a type antiquotation"
in
fun ty_antiq ty = let val kd = kind_of ty
                      val a = mk_var_type("'ty_antiq", kd ==> typ, 0)
                      val ty' = mk_app_type(a, ty)
                  in mk_var("ty_antiq",ty')
                  end

fun dest_ty_antiq tm =
  case Lib.with_exn dest_var tm ERR2
   of ("ty_antiq",ty) =>
        let val (a,ty') = Lib.with_exn dest_app_type ty ERR2
        in case Lib.with_exn dest_var_type a ERR2
            of ("'ty_antiq",_,0) => ty'
             | _ => raise ERR2
        end
    |  _ => raise ERR2

val is_ty_antiq = Lib.can dest_ty_antiq
end

(* antiquoting kinds into terms *)
val kd_ty_antiq = ty_antiq o kd_antiq;
val dest_kd_ty_antiq = dest_kd_antiq o dest_ty_antiq;
val is_kd_ty_antiq = Lib.can dest_kd_ty_antiq

fun totalify f x = SOME (f x) handle InternalFailure _ => NONE

fun parse_kind kdfns allow_unknown_prefixes G = let
  val G = rules G (*and abbrevs = abbreviations G*)
  val {varkind = pVarkind, kindop = pKind, antiq = pAQ, qkindop, arity} = kdfns
  fun structure_to_value (s,locn) args st =
      case st of
        KINDOP {Args, Thy, Kindop} =>
        qkindop {Args = map (structure_to_value (s,locn) args) Args,
                 Thy = Thy, Kindop = Kindop, Locn = locn}
      | KDVAR str => pVarkind (str,locn)

  (* extra fails on next two definitions will effectively make the stream
     push back the unwanted token *)
  (* can't use item for these, because this would require the token kind
     to be an equality kind, which is icky *)
  fun is_LParen t = case t of LParen => true | _ => false
  fun is_RParen t = case t of RParen => true | _ => false
  fun is_LBracket t = case t of LBracket => true | _ => false
  fun is_RBracket t = case t of RBracket => true | _ => false
  fun is_Comma t = case t of Comma => true | _ => false
  fun itemP P fb = let
    val (adv, (t,locn)) = kindtok_of fb (* TODO:KSW: use locn *)
  in
    if P t then (locn,adv()) else raise InternalFailure locn
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

  fun apply_kindop (t,locn) args =
    case t of
      KindIdent s => let
      in
        pKind((s,locn),args)
      end
    | _ => raise Fail "parse_kind.apply_kindop: can't happen"

  fun n_appls (ops, t) =
    case ops of
      [] => t
    | oph::opt => n_appls (opt, apply_kindop oph [t])
  fun n_appls_l ([], t) = raise Fail "parse_kind.n_appls_l: can't happen"
    | n_appls_l (op1::ops, xs) = n_appls (ops, apply_kindop op1 xs)

  fun n_array_sfxs locn (sfxs, ty) = let 
    fun build (sfx, base) = 
        qkindop{Thy = "fcp", Kindop = "cart",Locn=locn,Args = [base, sfx]}
  in
    List.foldl build ty sfxs
  end

  fun parse_op slist fb = let
    val (adv, (t,locn)) = kindtok_of fb
  in
    case t of
      KindIdent s => if allow_unknown_prefixes orelse Lib.mem s slist then
                       (adv(); (t,locn))
                     else raise InternalFailure locn
    | KindSymbol s => if allow_unknown_prefixes orelse Lib.mem s slist then
                       (adv(); (t,locn))
                     else raise InternalFailure locn
    | _ => raise InternalFailure locn
  end

  fun parse_binop (stlist:{parse_string:string,opname:string}list) fb = let
    val (adv, (t,locn)) = kindtok_of fb
    fun doit (t,locn) =
      case List.find (fn r => (#parse_string r = token_string t)) stlist of
        NONE => raise InternalFailure locn
      | SOME r => (adv(); (KindIdent (#opname r),locn))
  in
    case t of
      KindIdent s => doit (t,locn)
    | KindSymbol s => doit (t,locn)
    | _ => raise InternalFailure locn
  end

  fun parse_parens prse fb = let
    val (llocn,_) = itemP is_LParen fb
    val kd1 = prse fb
    val (rlocn,_) = itemP is_RParen fb
  in
    (kd1, locn.between llocn rlocn)
  end

  fun parse_num fb = let 
    val (adv, (t,locn)) = kindtok_of fb
  in
    case t of 
      KindNumeral n => (adv(); n)
    | _ => raise ERRloc locn
                 "arity kind operator with no numeric suffix"
  end

  fun parse_atom fb = let 
    val (adv, (t,locn)) = kindtok_of fb
  in
    case t of 
      KindVar s => (adv(); pVarkind (s, locn))
    | AQ x => (adv(); pAQ x)
    | KindIdent s => (adv(); apply_kindop(t,locn) [])
    | _ => raise InternalFailure locn
  end

  fun parse_term current strm =
      case current of
        [] => parse_atom strm 
      | (r::rs) => parse_rule r rs strm
  and parse_rule (r as (level, rule)) rs strm = let
    val next_level = parse_term rs
    val same_level = parse_rule r rs
  in
    case rule of
      INFIX (stlist, NONASSOC) => let
        val kd1 = next_level strm
      in
        case totalify (parse_binop stlist) strm of
          NONE => kd1
        | SOME opn => apply_kindop opn [kd1, next_level strm]
      end
    | INFIX (stlist, LEFT) => let
        val kd1 = next_level strm
        fun recurse acc =
            case totalify (parse_binop stlist) strm of
              NONE => acc
            | SOME opn => recurse (apply_kindop opn [acc, next_level strm])
      in
        recurse kd1
      end
    | INFIX (stlist, RIGHT) => let
        val kd1 = next_level strm
      in
        case totalify (parse_binop stlist) strm of
          NONE => kd1
        | SOME opn => apply_kindop opn [kd1, same_level strm]
      end
    | NONFIX => let
        val (adv, (t,locn)) = kindtok_of strm
      in
        case t of
          LParen => (case totalify (parse_parens (parse_term G)) strm of
                       NONE => next_level strm
                     | SOME (kd,locn) => kd)
        | _ => parse_atom strm
      end
    | PREFIX slist => let
        val (adv, (t,locn)) = kindtok_of strm
      in
        case t of
          KindArity => (adv(); arity (("ar",locn), parse_num strm))
        | _ => next_level strm
      end
  end
in
  fn qb => parse_term G qb
     handle InternalFailure locn =>
            raise ERRloc locn
                  ("Kind parsing failure with remaining input: "^
                   qbuf.toString qb)
end


end; (* struct *)
