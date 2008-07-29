structure Prerank :> Prerank =
struct

open HolKernel optmonad;
infix >> >-;


val TCERR = mk_HOL_ERR "Prerank";

 datatype prerank
    = Zerorank
    | Sucrank of prerank
    | Maxrank of prerank * prerank
    | UVarrank of prerank option ref

fun eq (UVarrank (ref(SOME rk)))  rk'                         = eq rk rk'
  | eq rk                         (UVarrank (ref(SOME rk')))  = eq rk rk'
  | eq (Zerorank)                 (Zerorank)                  = true
  | eq (Sucrank rk)               (Sucrank rk')               = eq rk rk'
  | eq (Maxrank(rk1,rk2))         rk                          = eq rk1 rk orelse eq rk2 rk
  | eq rk                         (Maxrank(rk1,rk2))          = eq rk rk1 orelse eq rk rk2
(*| eq (Maxrank(rk1,rk2))         (Maxrank(rk1',rk2'))        = eq rk1 rk1' andalso eq rk2 rk2'*)
  | eq (UVarrank (r as ref NONE)) (UVarrank (r' as ref NONE)) = r=r'
  | eq _                          _                           = false

fun leq (UVarrank (ref(SOME rk)))  rk'                         = leq rk rk'
  | leq rk                         (UVarrank (ref(SOME rk')))  = leq rk rk'
  | leq (Zerorank)                 _                           = true
  | leq (Sucrank rk)               (Sucrank rk')               = leq rk rk'
  | leq (Maxrank(rk1,rk2))         rk                          = leq rk1 rk andalso leq rk2 rk
  | leq rk                         (Maxrank(rk1,rk2))          = leq rk rk1 orelse leq rk rk2
  | leq (UVarrank (r as ref NONE)) (UVarrank (r' as ref NONE)) = r=r'
  | leq _                          _                           = false

(* ----------------------------------------------------------------------
    A total ordering on preranks.
    UVarrank(NONE) < UVarrank(SOME) < Zerorank < Sucrank < Maxrank
   ---------------------------------------------------------------------- *)

fun prerank_compare (UVarrank (r1 as ref NONE), UVarrank (r2 as ref NONE)) = EQUAL
  | prerank_compare (UVarrank (ref NONE),       _)                         = LESS
  | prerank_compare (UVarrank (ref (SOME _)),   UVarrank (ref NONE))       = GREATER
  | prerank_compare (UVarrank (ref (SOME rk1)), UVarrank (ref (SOME rk2))) = prerank_compare(rk1,rk2)
  | prerank_compare (UVarrank (ref (SOME _)),   _)                         = LESS
  | prerank_compare (Zerorank,                  Zerorank)                  = EQUAL
  | prerank_compare (Zerorank,                  UVarrank _)                = GREATER
  | prerank_compare (Zerorank,                  _)                         = LESS
  | prerank_compare (Sucrank rk1,               Sucrank rk2)               = prerank_compare(rk1,rk2)
  | prerank_compare (Sucrank _,                 Maxrank _)                 = LESS
  | prerank_compare (Sucrank _,                 _)                         = GREATER
  | prerank_compare (Maxrank p1,                Maxrank p2)                =
                                             Lib.pair_compare(prerank_compare,prerank_compare)(p1,p2)
  | prerank_compare (Maxrank _,                 _)                         = GREATER

fun is_num_rank (Zerorank) = true
  | is_num_rank (Sucrank rk) = is_num_rank rk
  | is_num_rank _ = false

fun num_rank (Zerorank) = 0
  | num_rank (Sucrank rk) = num_rank rk + 1
  | num_rank _ = raise TCERR "num_rank" "not a simple numeric rank";

fun prerank_to_string0 (UVarrank (ref NONE)) = "?"
  | prerank_to_string0 (UVarrank (ref(SOME rk))) = prerank_to_string rk
  | prerank_to_string0 (Zerorank) = "0"
  | prerank_to_string0 (Sucrank rk) = prerank_to_string rk ^ "+1"
  | prerank_to_string0 (Maxrank (rk1,rk2)) = "max(" ^ prerank_to_string rk1 ^ ","
                                                   ^ prerank_to_string rk2 ^ ")"
and prerank_to_string rk =
    if is_num_rank rk then Int.toString(num_rank rk)
                      else prerank_to_string0 rk


fun fromRank 0 = Zerorank
  | fromRank i = if i < 0 then raise TCERR "fromRank" "negative rank"
                 else Sucrank (fromRank (i-1))

fun uvars_of rk =
    case rk of
      UVarrank r => [r]
    | Sucrank rk => uvars_of rk
    | _ => []

fun new_uvar () = UVarrank(ref NONE)

infix ref_occurs_in
fun r ref_occurs_in value =
  case value of
    Zerorank  => false
  | Sucrank rk => r ref_occurs_in rk
  | Maxrank (rk1,rk2) => r ref_occurs_in rk1 orelse r ref_occurs_in rk2
  | UVarrank (r' as ref NONE) => r = r'
  | UVarrank (r' as ref (SOME rk)) => r = r' orelse r ref_occurs_in rk

infix ref_equiv
fun r ref_equiv value =
  case value of
    UVarrank (r' as ref NONE) => r = r'
  | UVarrank (r' as ref (SOME rk)) => r = r' orelse r ref_equiv rk
  | _ => false

  fun has_free_uvar prk =
    case prk of
      UVarrank (ref NONE)      => true
    | UVarrank (ref (SOME rk)) => has_free_uvar rk
    | Zerorank                 => false
    | Sucrank rk               => has_free_uvar rk
    | Maxrank (rk1,rk2)        => has_free_uvar rk1 orelse has_free_uvar rk2


(* This unsafe_bind should not fail because of a SOME value, *)
(* but merge the two preranks using Maxrank.                 *)

fun unsafe_bind_greater f r value =
  if r ref_equiv value
  then ok
  else if r ref_occurs_in value
  then fail
  else (fn acc =>
         (((r, !r)::acc, SOME ())
          before r := SOME (case (!r) of
                              SOME value0 => Maxrank(value0,value)
                            | NONE => value)));

fun unsafe_bind_less f r value =
  if r ref_equiv value
  then ok
  else if r ref_occurs_in value
  then fail
  else case (!r) of
          SOME value0 => f value0 value
        | NONE => (fn acc => (((r, !r)::acc, SOME ()) before r := SOME value));
                         


(* first argument is a function which performs a binding between a
   pretype reference and another pretype, updating some sort of environment
   (the 'a), returning the new alpha and a unit option, SOME () for a
   success, and a NONE, if not.

   To further complicate things, the bind argument also gets a copy of
   gen_unify to call, if it should choose.
*)
(* this will need changing *)
(* eta-expansion *is* necessary *)

(* This rank unification is NOT SYMMETRIC!! *)
(* The first rank is made to be less than or equal to the second rank. *)
fun gen_unify bind_less bind_greater rk1 rk2 e = let
  val gen_unify = gen_unify bind_less bind_greater
in
  case (rk1, rk2) of
    (UVarrank r, _) => bind_less gen_unify r rk2
  | (_, UVarrank r) => bind_greater gen_unify r rk1
  | (Maxrank (r1,r2), _) => gen_unify r2 rk2 >> gen_unify r1 rk2 >> ok
  | (Zerorank, _) => ok
  | (Sucrank rk1, Sucrank rk2) => gen_unify rk1 rk2
  | (_, Maxrank (r1,r2)) => gen_unify rk1 r2 ++ gen_unify rk1 r1
  | _ => fail
end e;

val unsafe_unify = gen_unify unsafe_bind_less unsafe_bind_greater

fun unify rk1 rk2 =
  case (gen_unify unsafe_bind_less unsafe_bind_greater rk1 rk2 [])
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify" "unify failed";

fun can_unify rk1 rk2 = let
  val (bindings, result) = gen_unify unsafe_bind_less unsafe_bind_greater rk1 rk2 []
  val _ = app (fn (r, oldvalue) => r := oldvalue) bindings
in
  isSome result
end

local
  fun (r ref_equiv value) env =
       case value of
         UVarrank (r' as ref NONE) =>
              r = r' orelse
              let in
                case Lib.assoc1 r' env
                 of NONE => false
                  | SOME (_, v) => (r ref_equiv v) env
              end
         | UVarrank (ref (SOME k)) => (r ref_equiv k) env
         | _ => false

      fun (r ref_occurs_in value) env =
        case value
         of UVarrank (r' as ref NONE) =>
              r = r' orelse
              let in
                case Lib.assoc1 r' env
                 of NONE => false
                  | SOME (_, v) => (r ref_occurs_in v) env
              end
          | UVarrank (r' as ref (SOME rk)) => r=r' orelse (r ref_occurs_in rk) env
          | Sucrank rk => (r ref_occurs_in rk) env
          | Maxrank (rk1,rk2) => (r ref_occurs_in rk1) env orelse
                                 (r ref_occurs_in rk2) env
          | _ => false
in
fun safe_bind_less unify r value env =
  case Lib.assoc1 r env
   of SOME (_, v) => unify v value env
    | NONE =>
        if (r ref_equiv value) env then ok env else
        if (r ref_occurs_in value) env then fail env
        else ((r,value)::env, SOME ())

fun safe_bind_greater unify r value env =
  case Lib.assoc1 r env
   of SOME (_, v) => unify value v env
    | NONE =>
        if (r ref_equiv value) env then ok env else
        if (r ref_occurs_in value) env then fail env
        else ((r,value)::env, SOME ())
end


fun safe_unify t1 t2 = gen_unify safe_bind_less safe_bind_greater t1 t2

(* needs changing *)
fun apply_subst subst prk =
  case prk of
    Zerorank => prk
  | Sucrank rk => Sucrank (apply_subst subst rk)
  | Maxrank (rk1,rk2) => Maxrank (apply_subst subst rk1, apply_subst subst rk2)
  | UVarrank (ref (SOME rk)) => apply_subst subst rk
  | UVarrank (r as ref NONE) =>
      case (Lib.assoc1 r subst) of
        NONE => prk
      | SOME (_, value) => apply_subst subst value

fun remove_made_links rk =
  case rk of
    UVarrank(ref (SOME rk')) => remove_made_links rk'
  | Sucrank rk' => Sucrank(remove_made_links rk')
  | Maxrank (rk1,rk2) => Maxrank(remove_made_links rk1,
                                 remove_made_links rk2)
  | _ => rk

(* If rank inference did not define these ranks, *)
(* then set them to the default rank, Zerorank.  *)
fun set_null_to_default r (used_so_far:string list) =
  let val _ = r := SOME Zerorank
  in
    (used_so_far, SOME ())
  end

(* needs changing *)
(* eta-expansion (see "env" after end below) *is* necessary *)
fun replace_null_links rk env = let
in
  case rk of
    UVarrank (r as ref NONE) => set_null_to_default r
  | UVarrank (ref (SOME rk)) => replace_null_links rk
  | Zerorank => ok
  | Sucrank rk1 => replace_null_links rk1 >> ok
  | Maxrank (rk1,rk2) => replace_null_links rk1 >> replace_null_links rk2 >> ok
end env

fun clean rk =
  case rk of
    Zerorank => 0
  | Sucrank rk' => clean rk' + 1
  | Maxrank (rk1,rk2) => Int.max(clean rk1, clean rk2)
  | _ => raise Fail "Don't expect to see links remaining at this stage of rank inference"

fun toRank rk =
  let val _ = replace_null_links rk []
  in
    clean (remove_made_links rk)
  end

end;
