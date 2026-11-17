structure Pretype :> Pretype =
struct

open HolKernel errormonad Pretype_dtype;
infix >> >-;


val TCERR = mk_HOL_ERR "Pretype";

(* Blame.  A pretype has no `locn' field, and cannot be given one: it
   is shared, substituted into and rebuilt constantly, and a type is
   not a piece of source text.  What *is* a piece of source text is the
   moment a unification variable was bound -- some subterm demanded
   that type of it -- and that is usually the thing a reader needs to
   be shown.  So the environment remembers, per unification variable,
   where it was bound; `unify' reports that position when two bound
   types clash, instead of the `Loc_Unknown' it used to have to use.

   Callers say what to blame with `with_blame', which scopes a locn
   over whatever bindings an action makes.  A caller that says nothing
   records nothing, so this costs the rest of the parser nothing and
   cannot move a position that was already being reported. *)
structure Env =
struct
  type t = {binds : pretype Inttab.table,
            (* uvar |-> (when it was bound, what to blame for it) *)
            prov : (int * locn.locn) Inttab.table,
            next : int, stamp : int, blame : locn.locn}
  fun lookup ({binds,...}:t) i = Inttab.lookup binds i
  (* `src' is the unification variable the type being bound was chased
     through, if any.  A type reached that way did not originate here:
     it originated wherever that variable got it, and inheriting the
     blame follows it back to the subterm that produced it instead of
     stopping at whatever happened to be unifying when the copy was
     made.  Without this the answer for `(value1 UNION value2, d2)' is
     the pair comma -- the last operator to handle the type -- rather
     than the `UNION' that made it a set. *)
  fun update_from src (i,pty) ({binds,prov,next,stamp,blame}:t) : t =
      let
        val inherited =
            case src of
                NONE => NONE
              | SOME j => (case Inttab.lookup prov j of
                               SOME (_, l) => SOME l
                             | NONE => NONE)
        val entry =
            case inherited of
                SOME l => SOME (stamp, l)
              | NONE =>
                (case blame of
                     locn.Loc_None => NONE
                   | locn.Loc_Unknown => NONE
                   | l => SOME (stamp, l))
      in
        {binds = Inttab.update (i,pty) binds,
         prov = (case entry of
                     NONE => prov
                   | SOME e => Inttab.update (i,e) prov),
         next = next, stamp = stamp + 1, blame = blame}
      end
  fun update arg E = update_from NONE arg E
  val empty : t = {binds = Inttab.empty, prov = Inttab.empty,
                   next = 0, stamp = 0, blame = locn.Loc_None}
  fun new ({binds,prov,next,stamp,blame}:t) =
      ({binds = binds, prov = prov, next = next + 1, stamp = stamp,
        blame = blame} : t, next)
  fun toList ({binds,next,...}:t) =
      List.tabulate(next, fn i => (i, Inttab.lookup binds i))
  fun provenance ({prov,...}:t) i = Inttab.lookup prov i
  fun blame_of ({blame,...}:t) = blame
  fun set_blame l ({binds,prov,next,stamp,...}:t) : t =
      {binds = binds, prov = prov, next = next, stamp = stamp, blame = l}
end

open typecheck_error
type 'a in_env = (Env.t,'a,error) errormonad.t

fun with_blame l (m : 'a in_env) : 'a in_env = fn e =>
  case m (Env.set_blame l e) of
      Error err => Error err
    | Some (e', v) => Some (Env.set_blame (Env.blame_of e) e', v)

fun fail s = error (Misc s, locn.Loc_Unknown)

(* Of the unification variables a failing `unify' was chased through,
   the position of the one bound *latest*: inference runs left to right
   through the source, so the most recent constraint is the newest
   information and the likeliest culprit.  No candidate was bound under
   a `with_blame', or none was chased at all, and there is nothing to
   say. *)
fun bestBlame (e : Env.t) cands = let
  fun better (NONE, acc) = acc
    | better (SOME i, acc) =
      (case Env.provenance e i of
           NONE => acc
         | SOME (s, l) =>
             case acc of
                 SOME (s', _) => if s > s' then SOME (s, l) else acc
               | NONE => SOME (s, l))
in
  case List.foldl better NONE cands of
      SOME (_, l) => l
    | NONE => locn.Loc_Unknown
end

fun failAt (c1, c2) s : 'a in_env =
    fn e => Error (Misc s, bestBlame e [c1, c2])

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

val new_uvar = lift UVar (Some o Env.new)
fun update_from src arg E = Some (Env.update_from src arg E, ())
fun update arg E = update_from NONE arg E

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

fun bind_from src i pty : unit in_env =
  case pty of
      UVar j => if i = j then ok
                else boundcase j (update_from src (i,pty))
                                 (fn pty' => bind_from (SOME j) i pty')
    | _ => (i ref_occurs_in pty) >-
           (fn b => if b then fail "Circular binding in unification"
                    else update_from src (i,pty))
fun bind i pty = bind_from NONE i pty

(* `cs' is the unification variable, if any, that each side has been
   chased through to reach the type now in hand.  Descending into a
   type operator's arguments keeps it: the argument was carried there
   by that same binding. *)
fun unify t1 t2 = unifyc (NONE, NONE) t1 t2
and unifyc (cs as (c1,c2)) t1 t2 =
  case (t1, t2) of
      (UVar r, _) =>
        boundcase r (bind r t2) (fn t1' => unifyc (SOME r, c2) t1' t2)
    | (_, UVar r) =>
        boundcase r (bind r t1) (fn t2' => unifyc (c1, SOME r) t1 t2')
    | (Vartype v1, Vartype v2) =>
        if v1 = v2 then ok
        else failAt cs ("Attempt to unify fixed variable types "^v1^" and " ^ v2)
    | (Vartype v, Tyop {Thy,Tyop=s,...}) =>
      failAt cs ("Attempt to unify fixed variable type "^v^" with operator "^
                 Thy^"$"^s)
    | (Tyop {Thy,Tyop=s,...}, Vartype v) =>
      failAt cs ("Attempt to unify fixed variable type "^v^" with operator "^
                 Thy^"$"^s)
    | (Tyop{Args=as1, Tyop=op1, Thy=thy1}, Tyop{Args=as2, Tyop=op2, Thy=thy2})=>
        if thy1 <> thy2 orelse op1 <> op2 then
          failAt cs ("Attempt to unify different type operators: " ^
                     thy1 ^ "$" ^ op1^ " and " ^ thy2 ^ "$" ^ op2)
        else unifycl cs as1 as2
and unifycl _ [] [] = ok
  | unifycl cs [] _ = failAt cs "Same tyop with different # of arguments?"
  | unifycl cs _ [] = failAt cs "Same tyop with different # of arguments?"
  | unifycl cs (t1::t1s) (t2::t2s) = unifyc cs t1 t2 >> unifycl cs t1s t2s

fun can_unify pty1 pty2 : bool in_env = fn e =>
  case unify pty1 pty2 e of
      Error _ => Some (e, false)
    | _ => Some (e, true)

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
                     Some (E', pty) => Some ((E',(s,pty) :: alist), pty)
                   | Error e => Error e (* should never happen *))
      | SOME (_, pty) => Some (env, pty)
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
      Some ((e', _), pty) => Some (e', pty)
    | Error e => Error e

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

fun replace_null_links ty : (Env.t * string list, pretype, error) t =
  case ty of
      UVar r => (fn (e,used) =>
                    case Env.lookup e r of
                        SOME pty => replace_null_links pty (e,used)
                      | NONE =>
                        let
                          val nm = tyvariant used "'a"
                          val res = Vartype nm
                        in
                          Some ((Env.update (r,res) e, nm::used), res)
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

val typecheck_listener = ref (fn _:pretype => fn _:Env.t => ());

fun toTypeM ty : Type.hol_type in_env =
  remove_made_links ty >-
  (fn ty => tyvars ty >-
  (fn vs => addState vs (replace_null_links ty) >-
  (fn (_, pty) => fn e => (
    !typecheck_listener pty e;
    return (clean pty) e))))

fun toType pty =
  case toTypeM pty Env.empty of
      Error e => raise mkExn e
    | Some (_, ty) => ty

fun chase (Tyop{Tyop = "fun", Thy = "min", Args = [_, ty]}) = return ty
  | chase (UVar i) =
      boundcase i (fail ("chase: uvar "^Int.toString i^" unbound")) chase
  | chase (Vartype s) = fail ("chase: can't chase variable type "^s)
  | chase (Tyop{Tyop=s, Thy, ...}) =
      fail ("chase: can't chase through "^Thy^"$"^s)


datatype pp_pty_state = none | left | right | uvar

fun pp_pretype pty = let
  open HOLPP
  fun pp_pty state pty = let
  in
    case pty of
      Vartype s => [add_string ("V("^s^")")]
    | Tyop {Thy,Tyop = tyop,Args} =>
      let
        val qid = if Thy = "bool" orelse Thy = "min" then add_string tyop
                  else add_string (Thy ^ "$" ^ tyop)
      in
        if Thy = "min" andalso tyop = "fun" then
          let
            val wrap =
                case state of
                    none => (fn ps => [block INCONSISTENT 0 ps])
                  | right => I
                  | _ (* left or uvar *) =>
                    fn ps => [add_string "(", block INCONSISTENT 0 ps,
                              add_string ")"]
            val core =
                pp_pty left (hd Args) @
                [add_string " ", add_string "->", add_break (1,0)] @
                pp_pty right (hd (tl Args))
          in
            wrap core
          end
        else
          case Args of
            [] => [qid]
          | _ => [
              add_string "(",
              block INCONSISTENT 0 (
                pr_list (block INCONSISTENT 0 o pp_pty none) [add_string ","]
                        Args
              ),
              add_string ")",
              qid
          ]
      end
    | UVar r => [add_string ("U("^Int.toString r^")")]
  end
in
  block INCONSISTENT 0 (pp_pty none pty)
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
