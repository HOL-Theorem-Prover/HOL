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
  val ERR2 = Feedback.mk_HOL_ERR "Parse" "dest_rk_antiq" "not a rank antiquotation"
in
fun rk_antiq rk = Kind.mk_var_kind("'rk_antiq",rk)

fun dest_rk_antiq kd =
  case Lib.with_exn Kind.dest_var_kind kd ERR2
   of ("'rk_antiq",Rk) => Rk
    |  _ => raise ERR2

val is_rk_antiq = Lib.can dest_rk_antiq
end

(* antiquoting kinds into types *)
local
  val ERR2 = Feedback.mk_HOL_ERR "Parse" "dest_kd_antiq" "not a kind antiquotation"
in
fun kd_antiq kd = Type.mk_var_type("'kd_antiq",kd)

fun dest_kd_antiq ty =
  case Lib.with_exn Type.dest_var_type ty ERR2
   of ("'kd_antiq",Kd) => Kd
    |  _ => raise ERR2

val is_kd_antiq = Lib.can dest_kd_antiq
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
val rk_kd_antiq = kd_antiq o rk_antiq;
val dest_rk_kd_antiq = dest_rk_antiq o dest_kd_antiq;
val is_rk_kd_antiq = Lib.can dest_rk_kd_antiq

(* antiquoting ranks into terms *)
val rk_ty_antiq = ty_antiq o kd_antiq o rk_antiq;
val dest_rk_ty_antiq = dest_rk_antiq o dest_kd_antiq o dest_ty_antiq;
val is_rk_ty_antiq = Lib.can dest_rk_ty_antiq

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
