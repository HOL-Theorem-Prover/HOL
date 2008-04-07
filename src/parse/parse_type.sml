structure parse_type :> parse_type =
struct

open type_tokens type_grammar HOLgrammars

open qbuf

exception InternalFailure of locn.locn

val ERR = Feedback.mk_HOL_ERR "Parse" "parse_type"
val ERRloc = Feedback.mk_HOL_ERRloc "Parse" "parse_type"

val debug = ref 0
val _ = Feedback.register_trace("debug_parse_type", debug, 1)
fun is_debug() = (!debug) > 0;

fun one _ [ty] = ty
  | one locn _ = raise ERRloc locn "tuple with no suffix"

fun totalify f x = SOME (f x) handle InternalFailure _ => NONE

fun parse_type (tyfns :
    {vartype : (string * Prekind.prekind * Prerank.prerank) locn.located -> 'a,
     tyop : (string locn.located * 'a list) -> 'a,
     qtyop : {Thy:string, Tyop:string, Locn:locn.locn, Args: 'a list} -> 'a,
     antiq : 'b -> 'a,
     kindcast : {Ty: 'a, Kind:Prekind.prekind, Locn:locn.locn} -> 'a,
     rankcast : {Ty: 'a, Rank:Prerank.prerank, Locn:locn.locn} -> 'a,
     tycon  : {Thy:string, Tyop:string, Locn:locn.locn} -> 'a,
     tyapp  : ('a * 'a) -> 'a,
     tyuniv : ('a * 'a) -> 'a,
     tyabs  : ('a * 'a) -> 'a,
     kindparser : 'b qbuf.qbuf -> Prekind.prekind})
               allow_unknown_suffixes G = let
  val G = rules G and abbrevs = abbreviations G
  val {vartype = pVartype, tyop = pType, antiq = pAQ, qtyop,
       kindcast, rankcast,
       tycon = pConType,
       tyapp = pAppType, tyuniv = pUnivType, tyabs = pAbstType,
       kindparser} = tyfns
  fun structure_num_args st =
    let val max = Int.max
        fun nargs (PARAM n) = n + 1
          | nargs (TYAPP  (opr, arg )) = max (nargs opr,  nargs arg)
          | nargs (TYUNIV (bvar,body)) = max (nargs bvar, nargs body)
          | nargs (TYABST (bvar,body)) = max (nargs bvar, nargs body)
          | nargs _ = 0
    in nargs st
    end
  fun structure_to_value (s,locn) args st =
    let val stv = structure_to_value (s,locn) args
    in
      case st of
        TYCON  {Thy, Tyop} => pConType {Thy = Thy, Tyop = Tyop, Locn = locn}
      | TYAPP  (opr,arg)   => pAppType (stv opr,  stv arg)
      | TYUNIV (bvar,body) => pUnivType(stv bvar, stv body)
      | TYABST (bvar,body) => pAbstType(stv bvar, stv body)
      | TYVAR  (str,kd,rk) => pVartype ((str, Prekind.fromKind kd, Prerank.fromRank rk), locn)
(*
        TYOP {Args, Thy, Tyop} =>
        qtyop {Args = map (structure_to_value (s,locn) args) Args,
               Thy = Thy, Tyop = Tyop, Locn = locn}
*)
      | PARAM n => List.nth(args, n)
        handle Subscript =>
               Feedback.Raise
                 (ERRloc locn ("Insufficient arguments to abbreviated operator " ^
                               Lib.quote s))
    end

  (* extra fails on next two definitions will effectively make the stream
     push back the unwanted token *)
  (* can't use item for these, because this would require the token type
     to be an equality type, which is icky *)
  fun is_LParen t = case t of LParen => true | _ => false
  fun is_RParen t = case t of RParen => true | _ => false
  fun is_LBracket t = case t of LBracket => true | _ => false
  fun is_RBracket t = case t of RBracket => true | _ => false
  fun is_Comma t = case t of Comma => true | _ => false
  fun is_Period t = case t of Period => true | _ => false
  fun is_KindCst t = case t of KindCst => true | _ => false
  fun is_RankCst t = case t of RankCst => true | _ => false
  fun itemP P fb = let
    val (adv, (t,locn)) = typetok_of fb (* TODO:KSW: use locn *)
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

  fun is_numeric s = let
    val lim = size s
    fun recurse n =
        n >= lim orelse (Char.isDigit (String.sub(s,n)) andalso
                         recurse (n + 1))
  in
    recurse 0
  end

  fun generate_fcpbit (s,locn) = let
    val n = Arbnum.fromString s
    val _ = n <> Arbnum.zero orelse
            raise ERRloc locn "Zero is not a valid number type"
    fun recurse acc m =
        if m = Arbnum.one then acc
        else let
            val (q,r) = Arbnum.divmod(m,Arbnum.two)
          in
            recurse ((r = Arbnum.one) :: acc) q
          end
    fun bit b arg = qtyop {Thy = "fcp", Tyop = if b then "bit1" else "bit0",
                           Locn = locn, Args = [arg]}
    fun build acc bits =
        case bits of
          [] => acc
        | b :: rest => build (bit b acc) rest
    val one = qtyop {Thy = "one", Tyop = "one", Locn = locn, Args = []}
  in
    build one (recurse [] n)
  end

  fun const_tyop (t,locn) =
let val res =
    case t of
      TypeIdent s => let
        val _ = if is_debug() then print ("const_tyop of " ^ s ^ "\n") else ()
      in
        if is_numeric s then generate_fcpbit(s,locn)
        else pType((s,locn),[])
             handle _ => raise InternalFailure locn (* if s not a known type name *)
      end
    | QTypeIdent(thy,ty) =>  let
        val _ = if is_debug() then print ("const_tyop of " ^ thy ^ "$" ^ ty ^ "\n") else ()
      in
        qtyop{Thy=thy,Tyop=ty,Locn=locn,Args=[]}
      end
    | _ => raise Fail "parse_type.const_tyop: can't happen"
in (if is_debug() then (print "Did const_tyop; got res "; print "\n") else (); res)
end

  fun list_pAppType(ty,[]) = ty
    | list_pAppType(ty,(ty1::tys)) = list_pAppType(pAppType(ty,ty1),tys)

  fun apply_tyop (ty,locn) args =
    list_pAppType(ty,args)
    handle e => (if is_debug() then print ("apply_tyop fails!\n") else (); Feedback.Raise e)

  fun apply_binop (t,locn) args =
    list_pAppType(const_tyop (t,locn),args)

  fun apply_kindcast (ty, kd, locn) =
    kindcast{Ty=ty, Kind=kd, Locn=locn}

  fun apply_rankcast (ty, rk, locn) =
    rankcast{Ty=ty, Rank=rk, Locn=locn}

  fun list_apply_binder(mk_ty, alphas, body) =
    List.foldr mk_ty body alphas

  fun apply_univ(alphas, body) =
    list_apply_binder(pUnivType, alphas, body)

  fun apply_abst(alphas, body) =
    list_apply_binder(pAbstType, alphas, body)

  fun n_appls (ops, t) =
    case ops of
      [] => t
    | oph::opt => n_appls (opt, apply_tyop oph [t])
  fun n_appls_l ([], t) = raise Fail "parse_type.n_appls_l: can't happen"
    | n_appls_l (op1::ops, xs) = n_appls (ops, apply_tyop op1 xs)

  fun n_array_sfxs locn (sfxs, ty) = let 
    fun build (sfx, base) = 
        qtyop{Thy = "fcp", Tyop = "cart",Locn=locn,Args = [base, sfx]}
  in
    List.foldl build ty sfxs
  end

  fun parse_abbrev args fb = let
    val (adv, (t,locn)) = typetok_of fb
  in
    case t of
      TypeIdent s =>
        if is_numeric s then raise InternalFailure locn
        else
         (case Binarymap.peek(abbrevs, s) of
             NONE => raise InternalFailure locn
           | SOME st => let val nargs = structure_num_args st
                            val (largs,rargs) = if nargs = 0 then ([],args) else (args,[])
                            val abr = structure_to_value (s,locn) largs st
                            val res = apply_tyop (abr,locn) rargs
                        in (adv(); (res, locn))
                        end)
    | _ => raise InternalFailure locn
  end

  fun parse_op slist fb = let
    val (adv, (t,locn)) = typetok_of fb
  in
    case t of
      TypeIdent s => if allow_unknown_suffixes orelse Lib.mem s slist then
                       (adv(); (t,locn))
                     else raise InternalFailure locn
    | QTypeIdent _ => (adv(); (t,locn))
    | _ => raise InternalFailure locn
  end

  fun parse_tuple prse fb = let
    val (llocn,_) = itemP is_LParen fb
    val ty1 = prse fb
    fun recurse acc = let
      val (adv,(t,locn)) = typetok_of fb
    in
      case t of
        RParen => (adv(); (List.rev acc,locn.between llocn locn))
      | Comma => (adv(); recurse (one locn (prse fb) :: acc))
      | _ => raise InternalFailure locn
    end
  in
    recurse ty1
  end

  fun parse_atom prse fb = let 
    val (adv, (t,locn)) = typetok_of fb
    val ts = type_tokens.token_string t handle _ => "<unknown>"
    val _ = if is_debug() then print ("=> parse_atom of " ^ ts ^ "\n") else ()
    fun try_const_tyop(t,locn) =
        let val ty = const_tyop(t,locn) (* may throw InternalFailure *)
        in (adv(); ty)                  (* if failure, don't adv()   *)
        end
  in
    case t of 
      LParen => let val (tys,locn) = parse_tuple prse fb
                in if is_debug() then print ("<= parse_tuple returned "
                         ^ Int.toString (length tys) ^ " types\n") else ();
                   tys
                end
             (* let val ty1 = (adv(); prse fb)
                    val (adv,(t,rlocn)) = typetok_of fb
                in
                  case t of
                    RParen => (adv(); ty1 (*,locn.between locn rlocn*) )
                  | _ => raise InternalFailure locn
                end *)
    | TypeVar s => (adv(); [pVartype ((s,Prekind.new_uvar(),Prerank.new_uvar()), locn)])
    | AQ x => (adv(); [pAQ x])
    | QTypeIdent (s0,s) => [try_const_tyop(t,locn)]
    | TypeIdent s => [try_const_tyop(t,locn)]
    | _ => raise InternalFailure locn
  end

  fun parse_num fb = let
    val (adv,(t,locn)) = typetok_of fb
  in
    case t of
      TypeIdent s => (adv(); case Int.fromString s of
                               SOME i => (i, locn)
                             | NONE => raise InternalFailure locn)
    | _ => raise InternalFailure locn
  end

  fun parse_kindcast fb = let
    val (llocn, _) = itemP is_KindCst fb 
    val kd = kindparser fb
    val (adv,(t,rlocn)) = typetok_of fb
  in
    (kd, locn.between llocn rlocn)
  end

  fun parse_rankcast fb = let
    val (llocn, _) = itemP is_RankCst fb
    val (rk,rlocn) = parse_num fb
    val prk = Prerank.fromRank rk
  in
    (prk, locn.between llocn rlocn)
  end

  fun parse_typevars parser strm = let
    fun add_casts acc =
        let val (adv, (t,locn)) = typetok_of strm
        in case t of
             KindCst =>
               (case totalify parse_kindcast strm of
                   SOME (kd,locn) => add_casts (apply_kindcast (acc, kd, locn))
                 | NONE => acc)
           | RankCst =>
               (case totalify parse_rankcast strm of
                   SOME (rk,locn) => add_casts (apply_rankcast (acc, rk, locn))
                 | NONE => acc)
           | _ => acc
        end
    fun recurse acc = let
      val (adv, (t,locn)) = typetok_of strm
    in case t of 
         Period => (adv(); List.rev acc)
(*
       | TypeVar s => (adv(); let val v = pVartype ((s,Prekind.new_uvar(),0), locn)
                                  val ty = add_casts v
                              in recurse (ty :: acc))
*)
       | _ => let val ty = one locn (parse_atom parser strm)
              in recurse (add_casts ty :: acc)
              end
    end
  in
    recurse []
  end

  fun parse_binder slist parser fb = let
    val (adv, (t,locn)) = typetok_of fb
    val _ =
    case t of
      TypeIdent s => if Lib.mem s slist then
                       (adv(); (t,locn))
                     else raise InternalFailure locn
    | QTypeIdent (_,s) => if Lib.mem s slist then
                       (adv(); (t,locn))
                     else raise InternalFailure locn
    | TypeSymbol s => if Lib.mem s slist then
                       (adv(); (t,locn))
                     else raise InternalFailure locn
    | _ => raise InternalFailure locn
    val alphas = parse_typevars parser fb
  in
    ((t,locn),alphas)
  end

  fun apply_binder ((t,locn),alphas,body) = let
  in
    case t of
      TypeIdent s  => if s = "\\" then apply_abst(alphas, body)
                      else if s = "!" then apply_univ(alphas, body)
                      else raise InternalFailure locn
    | QTypeIdent (_,s) => if s = "\\" then apply_abst(alphas, body)
                      else if s = "!" then apply_univ(alphas, body)
                      else raise InternalFailure locn
    | TypeSymbol s => if s = "\\" then apply_abst(alphas, body)
                      else if s = "!" then apply_univ(alphas, body)
                      else raise InternalFailure locn
    | _ => raise InternalFailure locn
  end

  fun parse_binop (stlist:{parse_string:string,opname:string}list) fb = let
    val (adv, (t,locn)) = typetok_of fb
    fun doit (t,locn) =
      case List.find (fn r => (#parse_string r = token_string t)) stlist of
        NONE => raise InternalFailure locn
      | SOME r => (adv(); (TypeIdent (#opname r),locn))
  in
    case t of
      TypeIdent s => doit (t,locn)
    | TypeSymbol s => doit (t,locn)
    | _ => raise InternalFailure locn
  end

  fun parse_asfx prse fb = let 
    val (llocn, _) = itemP is_LBracket fb 
    val ty = one llocn (prse fb)
    val (rlocn, _) = itemP is_RBracket fb
  in
    ty
  end

  fun parse_term current strm =
      case current of
        [] => parse_atom (parse_term G) strm
      | (r::rs) => parse_rule r rs strm
  and parse_rule (r as (level, rule)) rs strm = let
    val next_level = parse_term rs
    val same_level = parse_rule r rs
  in
    case rule of
      INFIX (stlist, NONASSOC) => let
        val (adv, (t,llocn)) = typetok_of strm
        val ty1 = next_level strm
        val (adv, (t,rlocn)) = typetok_of strm
      in
        case totalify (parse_binop stlist) strm of
          NONE => ty1
        | SOME opn => [apply_binop opn [one llocn ty1, one rlocn (next_level strm)]]
      end
    | INFIX (stlist, LEFT) => let
        val (adv, (t,llocn)) = typetok_of strm
        val ty1 = next_level strm
        fun recurse (acc,llocn) =
            case totalify (parse_binop stlist) strm of
              NONE => acc
            | SOME opn => let
                  val (adv, (t,rlocn)) = typetok_of strm
                in recurse ([apply_binop opn [one llocn acc, one rlocn (next_level strm)]],rlocn)
                end
      in
        recurse (ty1,llocn)
      end
    | INFIX (stlist, RIGHT) => let
        val _ = if is_debug() then print ">> INFIX (RIGHT)\n" else ()
        val (adv, (t,llocn)) = typetok_of strm
        val ty1 = next_level strm
      in
        case totalify (parse_binop stlist) strm of
          NONE => (if is_debug() then print "   INFIX (RIGHT) sees no infix\n" else (); ty1)
        | SOME opn => let
                        val (adv, (t,rlocn)) = typetok_of strm
                      in [(if is_debug() then print ("   INFIX (RIGHT) sees an infix " ^
                              type_tokens.token_string (#1 opn) ^ "\n") else ();
                           apply_binop opn [one llocn ty1, one rlocn (same_level strm)])]
                      end
      end
    | BINDER slist => let
      in case totalify (parse_binder slist (parse_term G)) strm of
            SOME ((t,locn),alphas) => let
                        val (adv, (_,rlocn)) = typetok_of strm
                      in [apply_binder((t,locn), alphas, one rlocn (same_level strm))]
                      end
          | NONE => next_level strm
      end
    | ARRAY_SFX => let 
        val llocn = #2 (current strm)
        val ty1 = next_level strm
      in
        if length ty1 <> 1 then ty1
        else let val asfxs = many (parse_asfx (parse_term G)) strm
             in [n_array_sfxs llocn (asfxs, one llocn ty1)]
             end
      end
    | CAST => let
        val _ = if is_debug() then print ">> CAST\n" else ()
        val ty1 = next_level strm
        fun recurse acc =
            let val (adv, (t,locn)) = typetok_of strm
            in case t of
                 KindCst =>
                   (case totalify parse_kindcast strm of
                       SOME (kd,locn) => recurse [apply_kindcast (one locn acc, kd, locn)]
                     | NONE => acc)
               | RankCst =>
                   (case totalify parse_rankcast strm of
                       SOME (rk,locn) => recurse [apply_rankcast (one locn acc, rk, locn)]
                     | NONE => acc)
               | _ => acc
            end
      in
        recurse ty1
      end
    | CONSTANT slist => let
        val _ = if is_debug() then print ">> CONSTANT\n" else ()
      in case totalify (parse_op slist) strm of
            SOME (op1,locn) => [const_tyop (op1,locn)]
          | NONE => next_level strm
      end
    | APPLICATION => let
        val _ = if is_debug() then print ">> APPLICATION\n" else ()
        val ty1 = case totalify (parse_abbrev []) strm of
                    SOME (ty2,locn) => (if is_debug() then print ("  APPLICATION did abbrev.\n") else ();
                                        [ty2])
                  | NONE => next_level strm
        val _ = if is_debug() then print ("  APPLICATION got arg.\n") else ()
        fun recurse acc = let
          in case totalify (parse_abbrev acc) strm of
                    SOME (ty2,locn) => (if is_debug() then print ("  APPLICATION did abbrev.\n") else ();
                                        recurse [ty2])
                  | NONE => let
                 val (adv, (t,locn1)) = typetok_of strm
                 val _ = if is_debug() then print ("  APPLICATION looking for operator;\n") else ()
             in
               case totalify next_level strm of
                 NONE => (if is_debug() then print "  APPLICATION returns.\n" else (); acc)
               | SOME ty2 => (if is_debug() then print "  APPLICATION found operator!\n" else ();
                              recurse [apply_tyop (one locn1 ty2,locn1) acc])
             end
          end
      in recurse ty1
      end
(*
    | TUPLE_APPL => let
        val _ = if is_debug() then print ">> TUPLE_APPL\n" else ()
      in
        case totalify (parse_tuple (parse_term G)) strm of
          NONE => next_level strm
        | SOME (tyl,locn) => let
          in
            case totalify (parse_abbrev tyl) strm of
               SOME (ty2,locn) => ty2
             | NONE => let
               val (adv, (t,locn1)) = typetok_of strm
             in
               case totalify same_level strm of
                 NONE => if length tyl <> 1 then
                           raise ERRloc locn "tuple with no suffix"
                         else
                           hd tyl
               | SOME ty2 => apply_tyop (ty2,locn1) tyl
             end
          end
      end
*)
  end
in
  fn (qb : 'b qbuf.qbuf) => let val (adv, (t,locn)) = typetok_of qb
                                val ty = one locn (parse_term G qb)
                            in if is_debug() then print ("Parsed type successfully!\n\n")
                                             else ();
                               ty
                            end
     handle InternalFailure locn =>
            raise ERRloc locn
                  ("Type parsing failure with remaining input: "^
                   qbuf.toString qb)
     handle e => Feedback.Raise e
end


end; (* struct *)
