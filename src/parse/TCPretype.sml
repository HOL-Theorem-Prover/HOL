
open Exception
fun TCERR f msg = HOL_ERR {origin_structure = "TCPretype",
                           origin_function = f, message = msg}

datatype pretype =
  Vartype of string | Tyop of (string * pretype list) |
  UVar of pretype option ref

fun tyvars t =
  case t of
    Vartype s => [s]
  | Tyop(s, args) =>
      List.foldl (fn (t, set) => Lib.union (tyvars t) set) [] args
  | UVar (ref NONE) => []
  | UVar (ref (SOME t')) => tyvars t'

open optmonad
infix >> >-

fun new_uvar () = UVar(ref NONE)

infix ref_occurs_in
fun r ref_occurs_in value =
  case value of
    Vartype _ => false
  | Tyop (s, ts) => List.exists (fn t => r ref_occurs_in t) ts
  | UVar (r' as ref NONE) => r = r'
  | UVar (r' as ref (SOME t)) => r = r' orelse r ref_occurs_in t
infix ref_equiv
fun r ref_equiv value =
  case value of
    Vartype _ => false
  | Tyop _ => false
  | UVar (r' as ref NONE) => r = r'
  | UVar (r' as ref (SOME t)) => r = r' orelse r ref_equiv t


fun bind r value =
  if r ref_equiv value then
    ok
  else
    if r ref_occurs_in value orelse isSome (!r) then
      fail
    else
      (fn acc => (((r, !r)::acc, SOME ()) before r := SOME value))

fun unify0 t1 t2 =
  case (t1, t2) of
    (UVar (r as ref NONE), t) => bind r t
  | (UVar (r as ref (SOME t1)), t2) => unify0 t1 t2
  | (t1, t2 as UVar _) => unify0 t2 t1
  | (Vartype s1, Vartype s2) => if s1 = s2 then ok else fail
  | (Tyop(op1, args1), Tyop(op2, args2)) =>
      if op1 <> op2 orelse length args1 <> length args2 then fail
      else
        mmap (fn (t1, t2) => unify0 t1 t2) (ListPair.zip(args1, args2)) >>
        return ()
  | _ => fail

fun unify t1 t2 =
  case (unify0 t1 t2 []) of
    (bindings, SOME ()) => ()
  | (_, NONE) => raise TCERR "unify" "unify failed"

(* passes over a type, turning all of the type variables into fresh
   UVars, but doing so consistently by using an env, which is an alist
   from variable names to type variable refs *)
local
  fun replace s env =
    case Lib.assoc1 s env of
      NONE => let
        val r = ref NONE
      in
        ((s, r)::env, SOME (UVar r))
      end
    | SOME (_, r) => (env, SOME (UVar r))
in
  fun rename_tv ty =
    case ty of
      Vartype s => replace s
    | Tyop(s, args) =>
        mmap rename_tv args >- (fn args' => return (Tyop(s, args')))
    | x => return x
  fun rename_typevars ty = valOf (#2 (rename_tv ty []))
end

fun fromType t =
  if Type.is_vartype t then Vartype (Type.dest_vartype t)
  else let
    val {Tyop = tyop, Args} = Type.dest_type t
  in
    Tyop(tyop, map fromType Args)
  end

  fun remove_made_links ty =
    case ty of
      UVar(ref (SOME ty')) => remove_made_links ty'
    | Tyop(s, args) => Tyop(s, map remove_made_links args)
    | _ => ty
  val a_code = Char.ord #"a"
  fun generate_new_name r used_so_far = let
    fun guess n = let
      val guess_str = String.implode [#"'", Char.chr n]
    in
      if Lib.mem guess_str used_so_far then guess (n + 1)
      else guess_str
    end
    val result = guess a_code
    val _ = r := SOME (Vartype result)
  in
    (result::used_so_far, SOME ())
  end

  fun replace_null_links ty =
    case ty of
      UVar (r as ref NONE) => generate_new_name r
    | UVar (ref (SOME ty)) => replace_null_links ty
    | Tyop (s, args) => mmap replace_null_links args >> ok
    | Vartype _ => ok

  fun clean ty =
    case ty of
      Vartype s => Type.mk_vartype s
    | Tyop(s, args) => Type.mk_type{Tyop = s, Args = map clean args}
    | _ => raise Fail "Don't expect to see links remaining at this stage"
  fun toType ty = let
    val _ = replace_null_links ty (tyvars ty)
  in
    clean (remove_made_links ty)
  end

fun chase (Tyop("fun", [_, ty])) = ty
  | chase (UVar(ref (SOME ty))) = chase ty
  | chase _ = raise Fail "chase applied to non-function type"