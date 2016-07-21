structure Pretype :> Pretype =
struct

open HolKernel optmonad Pretype_dtype;
infix >> >-;


val TCERR = mk_HOL_ERR "Pretype";

structure Env =
struct
  type t = ((int,pretype) Binarymap.dict * int)
  fun lookup (d,c) i = Binarymap.peek(d,i)
  fun update (i,pty) (d,c) = (Binarymap.insert(d,i,pty), c)
  val empty : t = (Binarymap.mkDict Int.compare, 0)
  fun new (d,c) = ((d,c+1), (c+1))
end

type 'a in_env = (Env.t,'a) optmonad.optmonad

fun boundcase i (n:'a in_env) (sf : pretype -> 'a in_env) : 'a in_env = fn e =>
  case Env.lookup e i of
      NONE => n e
    | SOME pty => sf pty e

fun tyvars t =
  case t of
    Vartype s => return [s]
  | Tyop{Args,...} =>
      List.foldl (fn (t, set) => lift2 Lib.union (tyvars t) set)
                 (return [])
                 Args
  | UVar i => boundcase i (return []) tyvars

fun mk_fun_ty (dom,rng) = Tyop{Thy="min", Tyop="fun", Args = [dom,rng]}

val new_uvar = lift UVar (SOME o Env.new)
fun update arg E =
  let
    val E' = Env.update arg E
  in
    SOME (E', ())
  end

infix ref_occurs_in

fun (r:int) ref_occurs_in (value:pretype) : bool in_env=
  case value of
    Vartype _ => return false
  | Tyop {Args = ts : pretype list,...} => refoccl r ts
  | UVar i => boundcase i (return (r = i)) (fn pty => r ref_occurs_in pty)
and refoccl r [] = return false
  | refoccl r ((t:pretype)::ts) =
      r ref_occurs_in t >- (fn b => if b then return b else refoccl r ts)


infix ref_equiv
fun r ref_equiv value =
  case value of
    Vartype _ => return false
  | Tyop _ => return false
  | UVar r' => boundcase r'
                         (return (r = r'))
                         (fn pty => if r = r' then return true
                                    else r ref_equiv pty)

fun bind i pty : unit in_env =
  (i ref_occurs_in pty) >-
  (fn b => if b then fail else update(i,pty))

fun unify t1 t2 =
  case (t1, t2) of
      (UVar r, _) =>
        boundcase r (bind r t2) (fn t1' => unify t1' t2)
    | (_, UVar r) => boundcase r (bind r t1) (fn t2' => unify t1 t2')
    | (Vartype v1, Vartype v2) => ok
    | (Vartype _, Tyop _) => fail
    | (Tyop _, Vartype _) => fail
    | (Tyop{Args=as1, Tyop=op1, Thy=thy1}, Tyop{Args=as2, Tyop=op2, Thy=thy2})=>
        if thy1 <> thy2 orelse op1 <> op2 then fail else unifyl as1 as2
and unifyl [] [] = ok
  | unifyl [] _ = fail
  | unifyl _ [] = fail
  | unifyl (t1::t1s) (t2::t2s) = unify t1 t2 >> unifyl t1s t2s

fun can_unify pty1 pty2 : bool in_env = fn e =>
  case unify pty1 pty2 e of
      NONE => SOME (e, false)
    | _ => SOME (e, true)

fun apply_subst E pty =
  case pty of
      Vartype _ => pty
    | Tyop{Tyop = s, Thy = t, Args = args} =>
      Tyop{Tyop = s, Thy = t, Args = map (apply_subst E) args}
    | UVar i => case Env.lookup E i of
                    NONE => pty
                  | SOME pty => apply_subst E pty

(* ----------------------------------------------------------------------
    Passes over a type, turning all of the type variables not in the
    avoids list into fresh UVars, but doing so consistently by using
    an env, which is an alist from variable names to type variable
    refs.
   ---------------------------------------------------------------------- *)

local
  fun replace s (env as (E, alist)) =
    case Lib.assoc1 s alist of
        NONE => (case new_uvar E of
                     SOME (E', pty) => SOME ((E',(s,pty) :: alist), pty)
                   | NONE => NONE)
      | SOME (_, pty) => SOME (env, pty)
in
fun rename_tv avds ty =
  case ty of
    Vartype s => if mem s avds then return ty else replace s
  | Tyop{Tyop = s, Thy = thy, Args = args} =>
      mmap (rename_tv avds) args >-
      (fn args' => return (Tyop{Tyop = s, Thy = thy, Args = args'}))
  | x => return x

fun rename_typevars avds ty : pretype in_env = fn e =>
  case rename_tv avds ty (e, []) of
      SOME ((e', _), pty) => SOME (e', pty)
    | _ => NONE

end

fun fromType t =
  if Type.is_vartype t then Vartype (Type.dest_vartype t)
  else let val {Tyop = tyop, Args, Thy} = Type.dest_thy_type t
       in Tyop{Tyop = tyop, Args = map fromType Args, Thy = Thy}
       end

fun remove_made_links ty =
  case ty of
      UVar i => boundcase i (return ty) remove_made_links
    | Tyop{Tyop = s, Thy, Args} =>
      lift (fn args => Tyop {Tyop = s, Thy = Thy, Args = args})
           (mmap remove_made_links Args)
    | _ => return ty

val tyvariant = Lexis.gen_variant Lexis.tyvar_vary

fun replace_null_links ty : (Env.t * string list, pretype) optmonad =
  case ty of
      UVar r => (fn (e,used) =>
                    case Env.lookup e r of
                        SOME pty => replace_null_links pty (e,used)
                      | NONE =>
                        let
                          val nm = tyvariant used "'a"
                          val res = Vartype nm
                        in
                          SOME ((Env.update (r,res) e, nm::used), res)
                        end)
    | Tyop {Args,Thy,Tyop=s} =>
        lift (fn args => Tyop{Tyop=s,Args=args,Thy=Thy})
             (mmap replace_null_links Args)
    | Vartype _ => return ty

fun clean ty =
  case ty of
    Vartype s => Type.mk_vartype s
  | Tyop{Tyop = s, Args, Thy} =>
      Type.mk_thy_type{Tyop = s, Thy = Thy, Args = map clean Args}
  | _ => raise Fail "Don't expect to see links remaining at this stage"

fun toTypeM ty : Type.hol_type in_env =
  remove_made_links ty >-
  (fn ty => tyvars ty >-
  (fn vs => lift (clean o #2) (addState vs (replace_null_links ty))))

fun toType pty =
  case toTypeM pty Env.empty of
      NONE => raise TCERR "toType" "monad failed"
    | SOME (_, ty) => ty

fun chase (Tyop{Tyop = "fun", Thy = "min", Args = [_, ty]}) = return ty
  | chase (UVar i) = boundcase i fail chase
  | chase _ = fail


datatype pp_pty_state = none | left | right | uvar

fun pp_pretype pps pty = let
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
    | UVar r => PP.add_string pps (Int.toString r)
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

fun has_unbound_uvar pty =
    case pty of
      Vartype _ => return false
    | UVar r => boundcase r (return true) has_unbound_uvar
    | Tyop{Args,...} => huul Args
and huul [] = return false
  | huul (ty1 :: tys) =
     has_unbound_uvar ty1 >- (fn b => if b then return true
                                      else huul tys)

end;
