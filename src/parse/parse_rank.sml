structure parse_rank :> parse_rank =
struct

open rank_tokens

open qbuf

exception InternalFailure of locn.locn

type ('a,'b) rankconstructors =
     {intrank : int -> 'a,
      antiq : 'b -> 'a}

val ERR = Feedback.mk_HOL_ERR "Parse" "parse_rank"

val ERRloc = Feedback.mk_HOL_ERRloc "Parse" "parse_rank"

(* antiquoting ranks into kinds *)
local
  val ERR2 = Feedback.mk_HOL_ERR "Parse" "dest_rk_antiq_kind" "not a rank antiquotation"
in
fun rk_antiq_kind rk = Kind.mk_var_kind("'rk_antiq",rk)

fun dest_rk_antiq_kind kd =
  case Lib.with_exn Kind.dest_var_kind kd ERR2
   of ("'rk_antiq",Rk) => Rk
    |  _ => raise ERR2

val is_rk_antiq_kind = Lib.can dest_rk_antiq_kind
end

(* antiquoting kinds into types *)
local
  val ERR2 = Feedback.mk_HOL_ERR "Parse" "dest_kd_antiq_type" "not a kind antiquotation"
in
fun kd_antiq_type kd = Type.mk_var_type("'kd_antiq",kd)

fun dest_kd_antiq_type ty =
  case Lib.with_exn Type.dest_var_type ty ERR2
   of ("'kd_antiq",Kd) => Kd
    |  _ => raise ERR2

val is_kd_antiq_type = Lib.can dest_kd_antiq_type
end

(* antiquoting types into terms *)
local
  open Term Type Kind Rank
  infixr ==>
  val ERR2 = Feedback.mk_HOL_ERR "Parse" "dest_ty_antiq" "not a type antiquotation"
in
fun ty_antiq ty = let val kd = kind_of ty
                      val a = mk_var_type("'ty_antiq", kd ==> typ rho)
                      val ty' = mk_app_type(a, ty)
                  in mk_var("ty_antiq",ty')
                  end

fun dest_ty_antiq tm =
  case Lib.with_exn dest_var tm ERR2
   of ("ty_antiq",ty) =>
        let val (a,ty') = Lib.with_exn dest_app_type ty ERR2
        in case Lib.with_exn dest_var_type a ERR2
            of ("'ty_antiq",_) => ty'
             | _ => raise ERR2
        end
    |  _ => raise ERR2

val is_ty_antiq = Lib.can dest_ty_antiq
end

(* antiquoting ranks into types *)
val rk_antiq_type = kd_antiq_type o rk_antiq_kind;
val dest_rk_antiq_type = dest_rk_antiq_kind o dest_kd_antiq_type;
val is_rk_antiq_type = Lib.can dest_rk_antiq_type

(* antiquoting ranks into terms *)
val rk_antiq = ty_antiq o kd_antiq_type o rk_antiq_kind;
val dest_rk_antiq = dest_rk_antiq_kind o dest_kd_antiq_type o dest_ty_antiq;
val is_rk_antiq = Lib.can dest_rk_antiq

fun totalify f x = SOME (f x) handle InternalFailure _ => NONE

fun parse_rank rkfns = let
  val {intrank, antiq = pAQ} = rkfns

  fun parse_atom fb = let 
    val (adv, (t,locn)) = ranktok_of fb
  in
    case t of
      RankNumeral s => (let val n = Arbnum.fromString s
                            val i = Arbnum.toInt n
                        in adv(); intrank i
                        end
                        handle Overflow => raise ERRloc locn
                               ("Excessively large rank: " ^ s)
                             | _ => raise ERRloc locn
                               ("Incomprehensible rank: " ^ s) )
    | AQ x => (adv(); pAQ x)
    | _ => raise InternalFailure locn
  end

  fun parse_term strm = parse_atom strm
in
  fn qb => parse_term qb
     handle InternalFailure locn =>
            raise ERRloc locn
                  ("Rank parsing failure with remaining input: "^
                   qbuf.toString qb)
end


end; (* struct *)
