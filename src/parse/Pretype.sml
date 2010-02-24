structure Pretype :> Pretype =
struct

open HolKernel optmonad;
infix >> >-;


val TCERR = mk_HOL_ERR "Pretype";

datatype pretype
     = Vartype of string
     | Tyop of {Thy:string,Tyop:string, Args: pretype list}
     | UVar of pretype option ref

fun tyvars t =
  case t of
    Vartype s => [s]
  | Tyop{Args,...} =>
      List.foldl (fn (t, set) => Lib.union (tyvars t) set) [] Args
  | UVar (ref NONE) => []
  | UVar (ref (SOME t')) => tyvars t'

fun new_uvar () = UVar(ref NONE)

infix ref_occurs_in

fun r ref_occurs_in value =
  case value of
    Vartype _ => false
  | Tyop {Args = ts,...} => List.exists (fn t => r ref_occurs_in t) ts
  | UVar (r' as ref NONE) => r = r'
  | UVar (r' as ref (SOME t)) => r = r' orelse r ref_occurs_in t

infix ref_equiv
fun r ref_equiv value =
  case value of
    Vartype _ => false
  | Tyop _ => false
  | UVar (r' as ref NONE) => r = r'
  | UVar (r' as ref (SOME t)) => r = r' orelse r ref_equiv t

fun unsafe_bind f r value =
  if r ref_equiv value
  then ok
  else if r ref_occurs_in value orelse isSome (!r)
       then fail
    else (fn acc => (((r, !r)::acc, SOME ()) before r := SOME value))

fun gen_unify bind t1 t2 =
 let val gen_unify = gen_unify bind
 in
  case (t1, t2) of
    (UVar (r as ref NONE), t) => bind gen_unify r t
  | (UVar (r as ref (SOME t1)), t2) => gen_unify t1 t2
  | (t1, t2 as UVar _) => gen_unify t2 t1
  | (Vartype s1, Vartype s2) => if s1 = s2 then ok else fail
  | (Tyop{Tyop = op1, Thy = thy1, Args = args1},
     Tyop{Tyop = op2, Thy = thy2, Args = args2}) =>
      if op1 <> op2 orelse thy1 <> thy2 orelse
         length args1 <> length args2
      then
        fail
      else
        mmap (fn (t1, t2) => gen_unify t1 t2) (ListPair.zip(args1, args2)) >>
        return ()
  | _ => fail
 end

fun unify t1 t2 =
  case (gen_unify unsafe_bind t1 t2 [])
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify" "unify failed";

fun can_unify t1 t2 =
  let val (bindings, result) = gen_unify unsafe_bind t1 t2 []
      val _ = app (fn (r, oldvalue) => r := oldvalue) bindings
  in isSome result
  end

local fun (r ref_equiv value) env =
       case value
        of UVar (r' as ref NONE) =>
              r = r' orelse
              let in
                case Lib.assoc1 r' env
                 of NONE => false
                  | SOME (_, v) => (r ref_equiv v) env
              end
         | UVar (ref (SOME t)) => (r ref_equiv t) env
         | _ => false

      fun (r ref_occurs_in value) env =
        case value
         of UVar (r' as ref NONE) =>
              r = r' orelse
              let in
                case Lib.assoc1 r' env
                 of NONE => false
                  | SOME (_, v) => (r ref_occurs_in v) env
              end
          | UVar (ref (SOME t)) => (r ref_occurs_in t) env
          | Vartype _ => false
          | Tyop{Args=A,...} => List.exists (fn t => (r ref_occurs_in t) env) A
in
fun safe_bind unify r value env =
  case Lib.assoc1 r env
   of SOME (_, v) => unify v value env
    | NONE =>
        if (r ref_equiv value) env then ok env else
        if (r ref_occurs_in value) env then fail env
        else ((r,value)::env, SOME ())
end


fun safe_unify t1 t2 = gen_unify safe_bind t1 t2

fun apply_subst subst pty =
  case pty of
    Vartype _ => pty
  | Tyop{Tyop = s, Thy = t, Args = args} =>
      Tyop{Tyop = s, Thy = t, Args = map (apply_subst subst) args}
  | UVar (ref (SOME t)) => apply_subst subst t
  | UVar (r as ref NONE) =>
      case (Lib.assoc1 r subst) of
        NONE => UVar r
      | SOME (_, value) => apply_subst subst value

(* ----------------------------------------------------------------------
    Passes over a type, turning all of the type variables not in the
    avoids list into fresh UVars, but doing so consistently by using
    an env, which is an alist from variable names to type variable
    refs.
   ---------------------------------------------------------------------- *)

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
fun rename_tv avds ty =
  case ty of
    Vartype s => if mem s avds then return ty else replace s
  | Tyop{Tyop = s, Thy = thy, Args = args} =>
      mmap (rename_tv avds) args >-
      (fn args' => return (Tyop{Tyop = s, Thy = thy, Args = args'}))
  | x => return x

fun rename_typevars avds ty = valOf (#2 (rename_tv avds ty []))
end

fun fromType t =
  if Type.is_vartype t then Vartype (Type.dest_vartype t)
  else let val {Tyop = tyop, Args, Thy} = Type.dest_thy_type t
       in Tyop{Tyop = tyop, Args = map fromType Args, Thy = Thy}
       end

fun remove_made_links ty =
  case ty
   of UVar(ref (SOME ty')) => remove_made_links ty'
    | Tyop{Tyop = s, Thy, Args} => Tyop{Tyop = s, Thy = Thy,
                                        Args = map remove_made_links Args}
    | _ => ty

val tyvariant = Lexis.gen_variant Lexis.tyvar_vary

fun generate_new_name r used_so_far =
  let val result = tyvariant used_so_far "'a"
      val _ = r := SOME (Vartype result)
  in
    (result::used_so_far, SOME ())
  end

fun replace_null_links ty =
  case ty
   of UVar (r as ref NONE) => generate_new_name r
    | UVar (ref (SOME ty)) => replace_null_links ty
    | Tyop {Args,...} => mmap replace_null_links Args >> ok
    | Vartype _ => ok

fun clean ty =
  case ty of
    Vartype s => Type.mk_vartype s
  | Tyop{Tyop = s, Args, Thy} =>
      Type.mk_thy_type{Tyop = s, Thy = Thy, Args = map clean Args}
  | _ => raise Fail "Don't expect to see links remaining at this stage"

fun toType ty =
  let val _ = replace_null_links ty (tyvars ty)
  in
    clean (remove_made_links ty)
  end

fun chase (Tyop{Tyop = "fun", Thy = "min", Args = [_, ty]}) = ty
  | chase (UVar(ref (SOME ty))) = chase ty
  | chase _ = raise Fail "chase applied to non-function type"


datatype pp_pty_state = none | left | right | uvar

fun pp_pretype pps pty = let
  val checkref = Portable.ref_to_int
  fun pp_pty pps state pty = let
  in
    case pty of
      Vartype s => PP.add_string pps ("V("^s^")")
    | Tyop {Thy,Tyop = tyop,Args} => let
        fun qid pps = if Thy = "bool" orelse Thy = "min" then
                        PP.add_string pps tyop
                      else PP.add_string pps (Thy ^ "$" ^ tyop)
      in
        if Thy = "min" andalso tyop = "fun" then let
          in
            if state = none then PP.begin_block pps PP.INCONSISTENT 0 else ();
            if state = left orelse state = uvar then
              (PP.add_string pps "("; PP.begin_block pps PP.INCONSISTENT 0)
            else ();
            pp_pty pps left (hd Args);
            PP.add_string pps " ->";
            PP.add_break pps (1,0);
            pp_pty pps right (hd (tl Args));
            if state = left orelse state = uvar then
              (PP.end_block pps; PP.add_string pps ")")
            else ();
            if state = none then PP.end_block pps else ()
          end
        else
          case Args of
            [] => qid pps
          | _ => let
            in
              PP.add_string pps "(";
              PP.begin_block pps PP.INCONSISTENT 0;
              Portable.pr_list (fn a => (PP.begin_block pps PP.INCONSISTENT 0;
                                         pp_pty pps none a;
                                         PP.end_block pps))
                               (fn () => PP.add_string pps ",")
                               (fn () => ())
                               Args;
              PP.end_block pps ;
              PP.add_string pps ")";
              qid pps
            end
      end
    | UVar(r as ref NONE) => let
      in
        PP.add_string pps (Int.toString (checkref r) ^ ":*")
      end
    | UVar (r as ref (SOME pty')) => let
      in
        if state <> uvar then PP.begin_block pps PP.INCONSISTENT 0 else ();
        PP.add_string pps (Int.toString (checkref r) ^ ":");
        PP.add_break pps (1,2);
        pp_pty pps uvar pty';
        if state <> uvar then PP.end_block pps else ()
      end
  end
in
  pp_pty pps none pty
end

fun remove_ty_aq t =
  if parse_type.is_ty_antiq t then parse_type.dest_ty_antiq t
  else raise mk_HOL_ERR "Parse" "type parser" "antiquotation is not of a type"

fun tyop_to_qtyop ((tyop,locn), args) =
  case Type.decls tyop of
    [] => raise mk_HOL_ERRloc "Parse" "type parser" locn
                              (tyop^" not a known type operator")
  | {Thy,Tyop = tyop} :: _ => Tyop{Thy = Thy, Tyop = tyop, Args = args}

fun do_qtyop {Thy,Tyop=tyop,Locn,Args} = Tyop {Thy=Thy,Tyop=tyop,Args=Args}

val termantiq_constructors =
    {vartype = fn x => Vartype (fst x), qtyop = do_qtyop,
     tyop = tyop_to_qtyop,
     antiq = fn x => fromType (remove_ty_aq x)}

val typantiq_constructors =
    {vartype = fn x => Vartype (fst x), qtyop = do_qtyop,
     tyop = tyop_to_qtyop,
     antiq = fromType}

end;
