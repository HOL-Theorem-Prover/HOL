structure Prerank :> Prerank =
struct

open HolKernel optmonad;
infix >> >-;

val TCERR = mk_HOL_ERR "Prerank";

datatype prerank
    = Zerorank
    | Sucrank of prerank
    | Maxrank of prerank * prerank
    | UVarrank of (order * prerank) option ref

type oprerank = order * prerank

(* In UVarrank, if the order is EQUAL then the UVarrank is equal to the contained rank;
   if the bool is LESS then the UVarrank is less than or equal to the contained rank, or
   if the bool is GREATER then the UVarrank is greater than or equal to the contained rank. *)

fun leq (UVarrank (ref(SOME (_,rk))))  rk'                             = leq rk rk'
  | leq rk                             (UVarrank (ref(SOME (_,rk'))))  = leq rk rk'
  | leq (Zerorank)                     _                               = true
  | leq (Sucrank rk)                   (Sucrank rk')                   = leq rk rk'
  | leq (Maxrank(rk1,rk2))             rk                              = leq rk1 rk andalso leq rk2 rk
  | leq rk                             (Maxrank(rk1,rk2))              = leq rk rk1 orelse leq rk rk2
  | leq (UVarrank (r as ref NONE))     (UVarrank (r' as ref NONE))     = r=r'
  | leq _                              _                               = false

fun eq (UVarrank (ref(SOME (_,rk))))  rk'                             = eq rk rk'
  | eq rk                             (UVarrank (ref(SOME (_,rk'))))  = eq rk rk'
  | eq (Zerorank)                     (Zerorank)                      = true
  | eq (Sucrank rk)                   (Sucrank rk')                   = eq rk rk'
  | eq (rk as Maxrank(rk1,rk2))       rk'                             =
           leq rk rk' andalso (eq rk1 rk' orelse eq rk2 rk')
  | eq rk                             (rk' as Maxrank(rk1,rk2))       =
           leq rk' rk andalso (eq rk rk1 orelse eq rk rk2)
  | eq (UVarrank (r as ref NONE))     (UVarrank (r' as ref NONE))     = r=r'
  | eq _                              _                               = false

(* ----------------------------------------------------------------------
    A total ordering on preranks.
    UVarrank(NONE) < UVarrank(SOME) < Zerorank < Sucrank < Maxrank
   ---------------------------------------------------------------------- *)

fun bool_compare (false,false) = EQUAL
  | bool_compare (false,true ) = LESS
  | bool_compare (true ,false) = GREATER
  | bool_compare (true ,true ) = EQUAL

fun order_compare (LESS   ,LESS   ) = EQUAL
  | order_compare (LESS   , _     ) = LESS
  | order_compare (EQUAL  ,LESS   ) = GREATER
  | order_compare (EQUAL  ,EQUAL  ) = EQUAL
  | order_compare (EQUAL  , _     ) = LESS
  | order_compare (GREATER,GREATER) = EQUAL
  | order_compare (GREATER, _     ) = GREATER

fun refbool_compare (r1 as ref b1, r2 as ref b2) = bool_compare (b1,b2)

fun prerank_compare (UVarrank (r1 as ref NONE), UVarrank (r2 as ref NONE)) = EQUAL
  | prerank_compare (UVarrank (ref NONE),       _)                         = LESS
  | prerank_compare (UVarrank (ref (SOME _)),   UVarrank (ref NONE))       = GREATER
  | prerank_compare (UVarrank (ref (SOME p1)),  UVarrank (ref (SOME p2)))  =
                                             Lib.pair_compare(order_compare,prerank_compare)(p1,p2)
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

fun new_uvar () = UVarrank(ref NONE)

fun is_num_rank (Zerorank) = true
  | is_num_rank (Sucrank rk) = is_num_rank rk
  | is_num_rank _ = false

fun num_rank (Zerorank) = 0
  | num_rank (Sucrank rk) = num_rank rk + 1
  | num_rank _ = raise TCERR "num_rank" "not a simple numeric rank";

fun mk_Maxrank (rk1,rk2) =      if leq rk1 rk2 then rk2
                           else if leq rk2 rk1 then rk1
                           else Maxrank(rk1,rk2);

fun prerank_to_string0 (UVarrank (ref NONE)) = "?"
  | prerank_to_string0 (UVarrank (ref(SOME (ord,rk)))) =
         " " ^ (if ord = EQUAL then "=" else if ord = GREATER then ">=" else "<=") ^ prerank_to_string rk
  | prerank_to_string0 (Zerorank) = "0"
  | prerank_to_string0 (Sucrank rk) = prerank_to_string rk ^ "+1"
  | prerank_to_string0 (Maxrank (rk1,rk2)) = "max(" ^ prerank_to_string rk1 ^ ","
                                                    ^ prerank_to_string rk2 ^ ")"
and prerank_to_string rk =
    if is_num_rank rk then Int.toString(num_rank rk)
                      else prerank_to_string0 rk


(*------------------------------------------------------------------------------*
 * Passes over a rank, turning the (sole) rank variable into a fresh UVarrank.  *
 * If the parameter "new" is true, zero ranks remain unchanged.                 *
 * Since that variable is not modeled directly, all zeros are replaced instead. *
 *------------------------------------------------------------------------------*)

local (* fun replace_new env = (env, SOME (new_uvar())) *)
      fun replace_new env = (env, SOME (Zerorank  ))
      fun replace env =
        case env
         of [] =>
              let val r = new_uvar()
              in ([r], SOME r)
              end
          | [r] => (env, SOME r)
          | _ => raise TCERR "rename_rv" "extended rank environment"
      (* fun replace env = (env, SOME Zerorank) *)
in
fun rename_rv new rk =
  let val rename_rv = rename_rv new
      val replace = if new then replace_new else replace
  in
  case rk of
    Zerorank => replace
  | Sucrank (rk1) =>
      rename_rv rk1 >- (fn rk1' =>
      return (Sucrank (rk1')))
  | Maxrank (rk1,rk2) =>
      rename_rv rk1 >- (fn rk1' =>
      rename_rv rk2 >- (fn rk2' =>
      return (Maxrank (rk1',rk2'))))
  | _ => return rk
  end

fun rename_rankvars rk = valOf (#2 (rename_rv false rk []))
end

fun fromRank 0 = Zerorank
  | fromRank i = if i < 0 then raise TCERR "fromRank" "negative rank"
                 else Sucrank (fromRank (i-1))

fun uvars_of rk =
    case rk of
      UVarrank r => [r]
    | Sucrank rk => uvars_of rk
    | Maxrank (rk1,rk2) => Lib.union (uvars_of rk1) (uvars_of rk2)
    | _ => []

fun new_uvar () = UVarrank(ref NONE)

infix ref_occurs_in
fun r ref_occurs_in value =
  case value of
    Zerorank  => false
  | Sucrank rk => r ref_occurs_in rk
  | Maxrank (rk1,rk2) => r ref_occurs_in rk1 orelse r ref_occurs_in rk2
  | UVarrank (r' as ref NONE) => r = r'
  | UVarrank (r' as ref (SOME (_,rk))) => r = r' orelse r ref_occurs_in rk

(* ref_occurs_in_not_top only checks if the ref r appears below the top level,
   that is, below the values being max-ed together. *)
infix ref_occurs_in_not_top
fun r ref_occurs_in_not_top value =
  case value of
    Zerorank  => false
  | Sucrank rk => r ref_occurs_in rk
  | Maxrank (rk1,rk2) => r ref_occurs_in_not_top rk1 orelse r ref_occurs_in_not_top rk2
  | UVarrank (r' as ref NONE) => false
  | UVarrank (r' as ref (SOME (_,rk))) => r ref_occurs_in_not_top rk

infix ref_equiv
fun r ref_equiv value =
  case value of
    UVarrank (r' as ref NONE) => r = r'
  | UVarrank (r' as ref (SOME (_,rk))) => r = r' orelse r ref_equiv rk
  | Maxrank (rk1,rk2) => (r ref_equiv rk1 andalso leq rk2 rk1)
                  orelse (r ref_equiv rk2 andalso leq rk1 rk2)
  | _ => false

(* ref_remove deletes the uvar "r" from "value" and returns the resulting prerank. *)
(* UVarrank(SOME) links are followed and collapsed, forgetting the order. *)
(* No refs are assigned, so this has no side effects. *)
infix ref_remove
fun r ref_remove value =
  case value of
    UVarrank (r' as ref NONE) => if r = r' then NONE else SOME value
  | UVarrank (r' as ref (SOME (ord,rk))) => if r = r' then NONE else r ref_remove rk
  | Zerorank => SOME value
  | Sucrank rk => (*SOME value*)
                  let in case r ref_remove rk
                           of NONE => NONE
                            | SOME rk' => SOME (Sucrank rk') end
  | Maxrank (rk1,rk2) => case r ref_remove rk1
                           of NONE => r ref_remove rk2
                            | SOME rk1' => case r ref_remove rk2
                                             of NONE => SOME rk1'
                                              | SOME rk2' => SOME (mk_Maxrank(rk1',rk2'))

  fun has_free_uvar prk =
    case prk of
      UVarrank (ref NONE)           => true
    | UVarrank (ref (SOME (or,rk))) => has_free_uvar rk
    | Zerorank                      => false
    | Sucrank rk                    => has_free_uvar rk
    | Maxrank (rk1,rk2)             => has_free_uvar rk1 orelse has_free_uvar rk2


(* This unsafe_bind should not fail because of a SOME value, *)
(* but merge the two preranks using mk_Maxrank.              *)

(* For unsafe_bind_greater, f should be unify_le *)
fun unsafe_bind_greater f r value =
  if r ref_occurs_in_not_top value
  then fail
  else case r ref_remove value
        of NONE => ok
         | SOME value' =>
             case (!r) of
               SOME (EQUAL,value0) => f value' value0
             | SOME (GREATER,value0) => (* use the maximum of value0 and value' *)
                       (fn acc => ((r, !r)::acc, SOME ())
                                  before r := SOME (GREATER, mk_Maxrank(value0,value')))
             | SOME (LESS,value0) => (fn acc => (* Interval [value' .. value0], choose value' *)
                                  ((r, !r)::acc, SOME ())
                                  before r := SOME (EQUAL, value')) >> f value' value0
             | NONE => (fn acc => ((r, !r)::acc, SOME ())
                                  before r := SOME (GREATER, value'));

(* For unsafe_bind_less, f should be unify_le *)
fun unsafe_bind_less f r value =
  case r ref_remove value
   of NONE => ok
    | SOME value' =>
      case (!r) of
                SOME (EQUAL,value0) => f value0 value' (* the new value must be greater *)
              | SOME (GREATER,value0) => (fn acc => (* Interval [value0 .. value'], choose value0 *)
                                            ((r, !r)::acc, SOME ())
                                            before r := SOME (EQUAL, value0)) >> f value0 value'
              | SOME (LESS,value0) => (* use the minimum of value0 and value' *)
                                      if leq value0 value' then ok
                                      else if leq value' value0 then (fn acc =>
                                            ((r, !r)::acc, SOME ())
                                            before r := SOME (LESS,value'))
                                      else (* value0 and value' cannot be compared at present *)
                                           f value0 value' (* guess that the new value is greater *)
              | NONE => (fn acc => (((r, !r)::acc, SOME ())
                                    before r := SOME (LESS, value')));

(* For unsafe_bind_equal, f should be unify and fle should be unify_le*)
fun unsafe_bind_equal f fle r value =
  if r ref_occurs_in_not_top value
  then fail
  else case r ref_remove value
   of NONE => ok
    | SOME value' => (* no refs to r occur in value' *)
      case (!r) of
                SOME (EQUAL,value0) => f value0 value'
              | SOME (GREATER,value0) => (fn acc =>
                                ((r, !r)::acc, SOME ())
                                before r := SOME (EQUAL,value')) >> fle value0 value'
              | SOME (LESS,value0) => (fn acc =>
                                ((r, !r)::acc, SOME ())
                                before r := SOME (EQUAL,value')) >> fle value' value0
              | NONE => (fn acc => ((r, !r)::acc, SOME ())
                                   before r := SOME (EQUAL,value'));


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
fun gen_unify_le bind_less bind_greater rk1 rk2 e = let
  val gen_unify_le = gen_unify_le bind_less bind_greater
in
  case (rk1, rk2) of
    (_, UVarrank r) => bind_greater gen_unify_le r rk1
  | (UVarrank r, _) => bind_less gen_unify_le r rk2
  | (Maxrank (r1,r2), _) => gen_unify_le r2 rk2 >> gen_unify_le r1 rk2 >> ok
  | (Zerorank, _) => ok
  | (Sucrank rk1, Sucrank rk2) => gen_unify_le rk1 rk2
  | (_, Maxrank (r1,r2)) => gen_unify_le rk1 r2 ++ gen_unify_le rk1 r1
  | _ => fail
end e;

(* This rank unification is SYMMETRIC!! *)
(* The first rank is made to be equal to the second rank. *)
fun gen_unify bind_equal bind_less bind_greater rk1 rk2 e = let
  val gen_unify_le = gen_unify_le bind_less bind_greater
  val gen_unify = gen_unify bind_equal bind_less bind_greater
in
  case (rk1, rk2) of
    (_, UVarrank r) => bind_equal gen_unify gen_unify_le r rk1
  | (UVarrank r, _) => bind_equal gen_unify gen_unify_le r rk2
  | (Maxrank (r1,r2), _) => (gen_unify r2 rk2 >> gen_unify_le r1 rk2) ++
                            (gen_unify r1 rk2 >> gen_unify_le r2 rk2)
  | (Zerorank, Zerorank) => ok
  | (Sucrank rk1, Sucrank rk2) => gen_unify rk1 rk2
  | (_, Maxrank (r1,r2)) => (gen_unify rk1 r2 >> gen_unify_le r1 rk1) ++
                            (gen_unify rk1 r1 >> gen_unify_le r2 rk1)
  | _ => fail
end e;

val unsafe_unify = gen_unify unsafe_bind_equal unsafe_bind_less unsafe_bind_greater
val unsafe_unify_le = gen_unify_le unsafe_bind_less unsafe_bind_greater

fun unify rk1 rk2 =
  case (unsafe_unify rk1 rk2 [])
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify" "unify failed";

fun unify_le rk1 rk2 =
  case (unsafe_unify_le rk1 rk2 [])
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify_le" "unify failed";

fun can_unify rk1 rk2 = let
  val (bindings, result) = unsafe_unify rk1 rk2 []
  val _ = app (fn (r, oldvalue) => r := oldvalue) bindings
in
  isSome result
end

fun can_unify_le rk1 rk2 = let
  val (bindings, result) = unsafe_unify_le rk1 rk2 []
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
         | UVarrank (r' as ref (SOME (_,k))) => r=r' orelse (r ref_equiv k) env
         | Maxrank (rk1,rk2) => ((r ref_equiv rk1) env andalso leq rk2 rk1)
                         orelse ((r ref_equiv rk2) env andalso leq rk1 rk2)
         | _ => false

      fun (r ref_occurs_in value) env =
        case value
         of UVarrank (r' as ref NONE) =>
              r = r' orelse
              let in
                case Lib.assoc1 r' env
                 of NONE => false
                  | SOME (_, (_, v)) => (r ref_occurs_in v) env
              end
          | UVarrank (r' as ref (SOME (_,rk))) => r=r' orelse (r ref_occurs_in rk) env
          | Sucrank rk => (r ref_occurs_in rk) env
          | Maxrank (rk1,rk2) => (r ref_occurs_in rk1) env orelse
                                 (r ref_occurs_in rk2) env
          | _ => false

(* ref_occurs_in_not_top only checks if the ref r appears below the top level,
   that is, below the values being max-ed together. *)
      fun (r ref_occurs_in_not_top value) env =
        case value
         of UVarrank (r' as ref NONE) =>
              let in
                case Lib.assoc1 r' env
                 of NONE => false
                  | SOME (_, (_, v)) => (r ref_occurs_in_not_top v) env
              end
          | UVarrank (r' as ref (SOME (_,rk))) => (r ref_occurs_in_not_top rk) env
          | Sucrank rk => (r ref_occurs_in rk) env
          | Maxrank (rk1,rk2) => (r ref_occurs_in_not_top rk1) env orelse
                                 (r ref_occurs_in_not_top rk2) env
          | _ => false

(* ref_remove deletes the uvar "r" from "value". *)
      fun (r ref_remove value) env =
        case value of
          UVarrank (r' as ref NONE) =>
            if r = r' then NONE
            else
              let in
                case Lib.assoc1 r' env
                 of NONE => SOME value
                  | SOME (_, (_, v)) => (r ref_remove v) env
              end
        | UVarrank (r' as ref (SOME (_,rk))) => if r = r' then NONE else (r ref_remove rk) env
        | Zerorank => SOME value
        | Sucrank rk => (*SOME value*)
                  let in case (r ref_remove rk) env
                           of NONE => NONE
                            | SOME rk' => SOME (Sucrank rk') end
        | Maxrank (rk1,rk2) =>
                          case (r ref_remove rk1) env
                           of NONE => (r ref_remove rk2) env
                            | SOME rk1' => case (r ref_remove rk2) env
                                             of NONE => SOME rk1'
                                              | SOME rk2' => SOME (mk_Maxrank(rk1',rk2'))


in
fun safe_bind_equal unify unify_le r value env =
  if (r ref_occurs_in_not_top value) env
  then fail env
  else case (r ref_remove value) env
   of NONE => ok env
    | SOME value' =>
        case Lib.assoc1 r env
         of SOME (_, (EQUAL,   v)) => unify v value' env
          | SOME (_, (GREATER, v)) => unify_le v value' ((r,(EQUAL,value'))::env)
          | SOME (_, (LESS,    v)) => unify_le value' v ((r,(EQUAL,value'))::env)
          | NONE => ((r,(EQUAL,value'))::env, SOME ())

fun safe_bind_less unify_le r value env =
  case (r ref_remove value) env
   of NONE => ok env
    | SOME value' =>
        case Lib.assoc1 r env
         of SOME (_, (EQUAL,   v)) => unify_le v value' env (* the new value must be greater *)
          | SOME (_, (GREATER, v)) => (* Interval [v .. value'], choose v *)
                                      unify_le v value' ((r, (EQUAL, v))::env)
          | SOME (_, (LESS,    v)) => (* use the minimum of v and value' *)
                                      if leq v value' then ok env
                                      else if leq value' v then ok ((r, (LESS, value'))::env)
                                      else (* v and value cannot be compared at present *)
                                           unify_le v value' env (* guess that the new value is greater *)
          | NONE                   => ok ((r,(LESS,value'))::env)

fun safe_bind_greater unify_le r value env =
  if (r ref_occurs_in_not_top value) env
  then fail env
  else case (r ref_remove value) env
        of NONE => ok env
         | SOME value' =>
              case Lib.assoc1 r env
                 of SOME (_, (EQUAL,  v)) => unify_le value' v env
                  | SOME (_, (GREATER,v)) => (* use the maximum of v and value' *)
                                             ok ((r, (GREATER, mk_Maxrank(v,value')))::env)
                  | SOME (_, (LESS,   v)) => (* Interval [value' .. v], choose value' *)
                                             unify_le value' v ((r, (EQUAL, value'))::env)
                  | NONE                 => ok ((r, (GREATER, value'))::env)
end


fun safe_unify t1 t2 = gen_unify safe_bind_equal safe_bind_less safe_bind_greater t1 t2
fun safe_unify_le t1 t2 = gen_unify_le safe_bind_less safe_bind_greater t1 t2

(*
fun apply_subst subst prk =
  case prk of
    Zerorank => prk
  | Sucrank rk => Sucrank (apply_subst subst rk)
  | Maxrank (rk1,rk2) => Maxrank (apply_subst subst rk1, apply_subst subst rk2)
  | UVarrank (ref (SOME (_,rk))) => apply_subst subst rk
  | UVarrank (r as ref NONE) =>
      case (Lib.assoc1 r subst) of
        NONE => prk
      | SOME (_, (_,value)) => apply_subst subst value
*)

fun remove_made_links rk =
  case rk of
    UVarrank(ref (SOME (LESS,rk'))) => Zerorank
  | UVarrank(ref (SOME (_,rk'))) => remove_made_links rk'
  | Sucrank rk' => Sucrank(remove_made_links rk')
  | Maxrank (rk1,rk2) => Maxrank(remove_made_links rk1,
                                 remove_made_links rk2)
  | _ => rk

(* If rank inference did not define these ranks, *)
(* then set them to the default rank, Zerorank.  *)
fun set_null_to_default r (used_so_far:string list) =
  let val _ = r := SOME (EQUAL,Zerorank)
  in
    (used_so_far, SOME ())
  end

(* eta-expansion (see "env" after end below) *is* necessary *)
fun replace_null_links rk env = let
in
  case rk of
    UVarrank (r as ref NONE) => set_null_to_default r
  | UVarrank (ref (SOME (_,rk))) => replace_null_links rk
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
