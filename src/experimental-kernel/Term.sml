structure Term :> Term =
struct

(*
In *scratch*, type
(hol-set-executable sml-executable)
or
(hol-set-executable (concat hol-home "/bin/hol.bare"))
and type Ctrl-j.

loadPath := "/Users/palantir/hol/hol-omega/sigobj" :: !loadPath;

loadPath := "/Users/pvhomei/hol/hol-omega/sigobj" :: !loadPath;

app load ["Feedback","Lib","Type","KernelSig","Lexis",
          "Redblackmap","Binarymap","Profile"];
*)

open Feedback Lib Type Kind Rank

infixr --> |->
infix :>=:

val ERR = mk_HOL_ERR "Term"
val WARN = HOL_WARNING "Term"

val ==> = Kind.==>;   infixr 3 ==>;

(* used internally to avoid term rebuilding during substitution and
   type instantiation *)
exception Unchanged = Type.Unchanged

fun qcomb2 con (f, g) (x, y) =
  let val fx = f x
  in
    let val gy = g y
    in
      con (fx, gy)
    end handle Unchanged => con (fx, y)
  end handle Unchanged => let val gy = g y in con (x, gy) end

(* apply a function f under "constructor" con, handling Unchanged *)
fun qcomb con f = qcomb2 con (f, f)

type tyvar = string * kind
type const_key = KernelSig.kernelname
type const_info = (KernelSig.kernelid * hol_type)
type 'a set = 'a HOLset.set

val compare_key = KernelSig.name_compare
val compare_cinfo = KernelSig.id_compare

val c2string = KernelSig.id_toString
val id2string  = KernelSig.name_toString

val const_table = KernelSig.new_table()

fun prim_delete_const kn = ignore (KernelSig.retire_name(const_table, kn))

fun inST s = not (null (KernelSig.listName const_table s))

datatype term = Var of string * hol_type
              | Const of const_info
              | App  of term * term
              | TApp of term * hol_type
              | Abs  of term * term
              | TAbs of hol_type * term

fun prim_new_const (k as {Thy,Name}) ty = let
  val _ = if is_type_kind (kind_of ty) then () else raise ERR "prim_new_const" "type does not have base kind"
  val id = KernelSig.insert(const_table, k, ty)
in
  Const(id, ty)
end

fun uptodate_term tm = let
  fun recurse tmlist =
      case tmlist of
        [] => true
      | tm :: rest => let
        in
          case tm of
            Var(s, ty) => uptodate_type ty andalso recurse rest
          | Const(info, ty) => KernelSig.uptodate_id info andalso
                               uptodate_type ty andalso
                               recurse rest
          | App(f, x) => recurse (f::x::rest)
          | Abs(v, body) => recurse (v::body::rest)
          | TApp(f, a) => recurse (f::rest)
          | TAbs(a, body) => recurse (body::rest)
        end
in
  recurse [tm]
end

fun thy_consts s = let
  fun f (k, info, acc) =
      if #Thy k = s then Const info :: acc
      else acc
in
  KernelSig.foldl f [] const_table
end

fun del_segment s = KernelSig.del_segment(const_table, s)

fun prim_decls s = KernelSig.listName const_table s

fun decls s = let
  fun foldthis (k,v,acc) =
      if #Name k = s then Const v::acc else acc
in
  KernelSig.foldl foldthis  [] const_table
end

fun all_consts () = let
  fun foldthis (_,v,acc) = Const v :: acc
in
  KernelSig.foldl foldthis [] const_table
end

(*---------------------------------------------------------------------------*
 *                  Equality of terms                                        *
 *     This does NOT include alpha-equivalence, but                          *
 *     DOES include deep beta and eta conversion of types.                   *
 *     This discriminates between unequal but alpha-equivalent terms.        *
 *---------------------------------------------------------------------------*)

val prim_eq = equal : term -> term -> bool

local val EQ = Portable.pointer_eq
in
fun eq t1 t2 = EQ(t1,t2) orelse
 case(t1,t2)
  of (Var(M,a),  Var(N,b))   => M=N andalso eq_ty a b
   | (Const(M,a),Const(N,b)) => M=N andalso eq_ty a b
   | (App(M,N),  App(P,Q))   => eq N Q andalso eq M P
   | (Abs(u,M),  Abs(v,N))   => eq u v andalso eq M N
   | (TApp(M,a), TApp(N,b))  => eq_ty a b andalso eq M N
   | (TAbs(a,M), TAbs(b,N))  => a=b andalso eq M N
   | otherwise => false
end


fun type_of t = let
  fun ty_of t k =
      case t of
        Var(_, ty) => k ty
      | Const(_, ty) => k ty
      | App(t1, t2) => ty_of t1 (fn ty => k (#2 (dom_rng ty)))
      | Abs(Var(_, ty1), t) => ty_of t (fn ty2 => k (ty1 --> ty2))
      | TApp(tm, ty) => ty_of tm (fn univ =>
                          let val (a,body) = Type.dest_univ_type univ
                          in k (Type.pure_type_subst[a |-> ty] body)
                          end)
      | TAbs(a, tm) => ty_of tm (fn ty => k (Type.mk_univ_type(a,ty)))
      | _ => raise Fail "Catastrophic invariant failure"
in
  ty_of t Lib.I
end

fun rank_of_term t = let
  fun rk_of t k =
      case t of
        App(t1, t2) => rk_of t1 (fn r1 => rk_of t2 (fn r2 => k (Rank.max(r1,r2))))
      | TApp(tm, ty) => rk_of tm (fn rk => k (Rank.max(rk,rank_of_type ty)))
      | Abs(Var(_, ty), t) => rk_of t (fn rk => k (Rank.max(rank_of_type ty,rk)))
      | _ => k (rank_of_type (type_of t))
in
  rk_of t Lib.I
end



(*-----------------------------------------------------------------------------*
 * The kind variables of a lambda term. Tail recursive (from Ken Larsen).      *
 *-----------------------------------------------------------------------------*)

local val ty_kdV = Type.kind_vars
      fun kdV (Var(_,Ty)) k        = k (ty_kdV Ty)
        | kdV (Const(_,Ty)) k      = k (ty_kdV Ty)
        | kdV (App(Rator,Rand)) k  = kdV Rand (fn q1 =>
                                     kdV Rator(fn q2 => k (union q2 q1)))
        | kdV (Abs(Bvar,Body)) k   = kdV Body (fn q1 =>
                                     kdV Bvar (fn q2 => k (union q2 q1)))
        | kdV (TApp(Rator,Ty)) k   = kdV Rator (fn q  =>
                                         k (union q (ty_kdV Ty)))
        | kdV (TAbs(Btvar,Body)) k = kdV Body (fn q =>
                                         k (union q (ty_kdV Btvar)))
      fun kdVs (t::ts) k           = kdV t (fn q1 =>
                                     kdVs ts (fn q2 => k (union q2 q1)))
        | kdVs [] k                = k []
in
fun kind_vars_in_term tm = kdV tm Lib.I
fun kind_vars_in_terml tms = kdVs tms Lib.I
end

(*---------------------------------------------------------------------------*
 *                  Equality of terms                                        *
 *     This does NOT include alpha-equivalence, but                          *
 *     DOES include deep beta and eta conversion of types.                   *
 *     This discriminates between unequal but alpha-equivalent terms.        *
 *---------------------------------------------------------------------------*)

local val EQ = Portable.pointer_eq
in
fun eq t1 t2 = EQ(t1,t2) orelse
 case(t1,t2)
  of (Var(M,a),Var(N,b)) => M=N andalso eq_ty a b
   | (Const(M,a),Const(N,b)) => M=N andalso eq_ty a b
   | (App(M,N),App(P,Q)) => eq N Q andalso eq M P
   | (TApp(M,a),TApp(N,b)) => eq_ty a b andalso eq M N
   | (Abs(u,M),Abs(v,N)) => eq u v andalso eq M N
   | (TAbs(a1,M),TAbs(a2,N)) => a1 = a2 andalso eq M N
   | _ => false
end;

(* free variable calculations *)

local
fun FV (v as Var _) A k = k (Lib.op_insert eq v A)
  | FV (Const _) A k = k A
  | FV (App(f, x)) A k = FV f A (fn q => FV x q k)
  | FV (Abs(v, bdy)) A k =
    if Lib.op_mem eq v A then FV bdy A k
    else FV bdy A (fn q => k (Lib.op_set_diff eq q [v]))
  | FV (TApp(f, _)) A k = FV f A k
  | FV (TAbs(_, bdy)) A k = FV bdy A k
in
fun free_vars tm = FV tm [] Lib.I
end

(* val free_vars = Profile.profile "free_vars" free_vars *)

fun free_vars_lr tm = let
  fun FV (v as Var _) A = Lib.op_insert eq v A
    | FV (Const _) A = A
    | FV (App(f, x)) A = FV x (FV f A)
    | FV (Abs(v, body)) A = Lib.op_set_diff eq (FV body A) [v]
    | FV (TApp(f, _)) A = FV f A
    | FV (TAbs(_, body)) A = FV body A
in
  List.rev (FV tm [])
end


fun safe_delete(s, i) = HOLset.delete(s, i) handle HOLset.NotFound => s

datatype FVaction = FVTM of term | DELvar of term

fun FVL0 tlist acc =
    case tlist of
      [] => acc
    | (FVTM t::ts) => let
      in
        case t of
          (v as Var _) => FVL0 ts (HOLset.add(acc, v))
        | Const _ => FVL0 ts acc
        | App(f, x) => FVL0 (FVTM f :: FVTM x :: ts) acc
        | Abs(v, bdy) =>
          if HOLset.member(acc, v) then FVL0 (FVTM bdy :: ts) acc
          else FVL0 (FVTM bdy :: DELvar v :: ts) acc
        | TApp(f, _) => FVL0 (FVTM f :: ts) acc
        | TAbs(_, bdy) => FVL0 (FVTM bdy :: ts) acc
      end
    | DELvar v :: ts => FVL0 ts (safe_delete(acc, v))

fun FVL tlist = FVL0 (map FVTM tlist)


local
  fun vars (v as Var _) A = Lib.op_insert eq v A
    | vars (Const _) A = A
    | vars (App(f, x)) A = vars x (vars f A)
    | vars (Abs(v, bdy)) A = vars bdy (vars v A)
    | vars (TApp(f, _)) A = vars f A
    | vars (TAbs(_, bdy)) A = vars bdy A
in
fun all_vars tm = vars tm []
end

fun free_varsl tm_list = itlist (op_union eq o free_vars) tm_list []
fun all_varsl tm_list = itlist (op_union eq o all_vars) tm_list []


(* discriminators *)
fun is_var (Var _) = true | is_var _ = false
fun is_const (Const _) = true | is_const _ = false
fun is_abs (Abs _) = true | is_abs _ = false
fun is_comb (App _) = true | is_comb _ = false
fun is_tyabs (TAbs _) = true | is_tyabs _ = false
fun is_tycomb (TApp _) = true | is_tycomb _ = false

fun same_const t1 t2 =
    case (t1, t2) of
      (Const(r1, _), Const(r2, _)) => r1 = r2
    | _ => false

(* constructors - variables *)
fun mk_var (n,ty) = if is_type_kind (kind_of ty) then Var(n,ty)
                    else raise ERR "mk_var" "type does not have base kind"
fun mk_primed_var (Name,Ty) =
  let val next = Lexis.nameStrm Name
      fun spin s = if inST s then spin (next()) else s
  in mk_var(spin Name, Ty)
  end;

local val genvar_prefix = "%%genvar%%"
      fun num2name i = genvar_prefix^Lib.int_to_string i
      val nameStrm = Lib.mk_istream (fn x => x+1) 0 num2name
in
fun genvar ty = if is_type_kind (kind_of ty) then Var(state(next nameStrm), ty)
                else raise ERR "genvar" "type does not have base kind"

fun genvars ty =
 let fun gen acc n = if n <= 0 then rev acc else gen (genvar ty::acc) (n-1)
 in gen []
 end

fun is_genvar (Var(Name,_)) = String.isPrefix genvar_prefix Name
  | is_genvar _ = false;
end;

fun first_decl fname Name =
  case prim_decls Name
   of []              => raise ERR fname ("No constant with name "^Name)
    | [(_, const)]    => const
    | (_, const) :: _ =>
        (WARN fname (Name^": more than one possibility");
         const)

(* constructors - constants *)
fun mk_const(s, ty) =
  let val const as (id,basety) = first_decl "mk_const" s
  in
    let val Theta as (tyS,kdS,rkS) = Type.kind_match_type basety ty
        val reduce = if null tyS then I else Type.deep_beta_eta_ty
    in case (tyS,kdS,rkS)
        of ([],[],0) => Const const
         | (S,_,_) => Const(id, reduce (Type.inst_rk_kd_ty Theta basety))
    end handle HOL_ERR _ => raise (ERR "mk_const"
             (String.concat["Not a type instance: ", KernelSig.id_toString id,
                              "\nof primitive type\n", type_to_string basety,
                              " cannot have type\n", type_to_string ty]))
  end

fun prim_mk_const (k as {Thy, Name}) =
    case KernelSig.peek(const_table, k) of
      NONE => raise ERR "prim_mk_const" ("No such constant: "^id2string k)
    | SOME x => Const x

fun mk_thy_const {Thy,Name,Ty} = let
  val k = {Thy = Thy, Name = Name}
in
  case KernelSig.peek(const_table, k) of
    NONE => raise ERR "mk_thy_const" ("No such constant: "^id2string k)
  | SOME (id,basety) => let val Theta as (tyS,kdS,rkS) = Type.kind_match_type basety Ty
                            val reduce = if null tyS then I else Type.deep_beta_eta_ty
                            val Ty' = reduce (Type.inst_rk_kd_ty Theta basety)
                        in Const(id, Ty')
                        end handle HOL_ERR_ =>
                            raise ERR "mk_thy_const"
                                       ("Not a type instance: "^id2string k)
end

(* constructors - applications *)
local val INCOMPAT_TYPES  = Lib.C ERR "incompatible types"
      fun lmk_comb err =
        let fun loop (A,_) [] = A
              | loop (A,typ) (tm::rst) =
                 let val (ty1,ty2) = with_exn Type.dom_rng typ err
                 in if ge_ty ty1 (type_of tm)
                    then loop(App(A,tm),ty2) rst
                    else raise err
                 end
        in fn (f,L) => loop(f, deep_beta_eta_ty (type_of f)) L
        end
      val lmk_comb = (fn err => (**) Profile.profile "lmk_comb" (**)(lmk_comb err))
      val mk_comb0 = lmk_comb (INCOMPAT_TYPES "mk_comb")
in

fun mk_comb(r as (Abs(Var(_,Ty),_), Rand)) =
      if ge_ty Ty (type_of Rand) then App r else raise INCOMPAT_TYPES "mk_comb"
  | mk_comb(Rator,Rand) = mk_comb0 (Rator,[Rand])

val list_mk_comb = lmk_comb (INCOMPAT_TYPES "list_mk_comb")
end;


(* constructors - abstractions *)
fun mk_abs(v, body) =
    if is_var v then Abs(v, body)
    else raise ERR "mk_abs" "Arg 1 not a variable"

(* constructors - type applications *)
local val INCOMPAT_TYPES  = Lib.C ERR "term applied to type does not have universal type"
      val INCOMPAT_KINDS  = Lib.C ERR "type application argument has different kind than expected"
      val INCOMPAT_RANKS  = Lib.C ERR "type application argument has rank exceeding that expected"
      fun lmk_tycomb err errK errR =
        let fun loop (A,_) [] = A
              | loop (A,typ) (ty::rst) =
                 let val (btyv,ty2) = with_exn Type.dest_univ_type typ err
                     val kd = kind_of ty
                     val bkd = kind_of btyv
                 in if rank_of kd > rank_of bkd then raise errR
                    else if not (bkd :>=: kd) then raise errK
                    else let val tm = TApp(A,ty)
                         in loop(tm, type_of tm) rst
                         end
                 end
        in fn (f,L) => loop(f, type_of f) L
        end
   (* val lmk_tycomb = (fn err => fn errK => fn errR => (* Profile.profile "lmk_comb" *)(lmk_tycomb err errK errR)) *)
      val mk_tycomb0 = lmk_tycomb (INCOMPAT_TYPES "mk_tycomb")
                                  (INCOMPAT_KINDS "mk_tycomb")
                                  (INCOMPAT_RANKS "mk_tycomb")
in

fun mk_tycomb(r as (TAbs(a,_), Rand)) =
    let val (_,Kd) = dest_var_type a
        val Rand_Kd = kind_of Rand
    in
      if rank_of Rand_Kd > rank_of Kd then raise INCOMPAT_RANKS "mk_tycomb"
      else if not (Kd :>=: Rand_Kd) then raise INCOMPAT_KINDS "mk_tycomb"
      else TApp r
    end
  | mk_tycomb(Rator,Rand) = mk_tycomb0 (Rator,[Rand])

val list_mk_tycomb = lmk_tycomb (INCOMPAT_TYPES "list_mk_tycomb")
                                (INCOMPAT_KINDS "list_mk_tycomb")
                                (INCOMPAT_RANKS "list_mk_tycomb")
end;

fun type_var_string tyv =
    let val (s,kd) = dest_var_type tyv
                        handle HOL_ERR _ =>
                        raise ERR "type_var_string" "not a type variable"
    in
      s ^ (if kd = typ rho then "" else " : "^kind_to_string kd)
    end;

(* constructors - type abstractions *)
fun mk_tyabs(tyv, body) =
    let val fvs = free_vars body
    in
      if mem tyv (type_varsl (map type_of fvs))
      then let val fv = first (fn v => mem tyv (type_vars (type_of v))) fvs
               val fv_name = case fv of Var (fv_name,_) => fv_name
                                      | _ => raise ERR "mk_tyabs" "impossible"
           in raise ERR "mk_tyabs"
              ("bound type variable (" ^ type_var_string tyv ^
               ") occurs free in the type of a free variable of the body ("^fv_name^")")
           end
      else if is_var_type tyv then TAbs(tyv, body)
      else raise ERR "mk_tyabs" "first argument not a type variable"
    end


(* destructors *)

fun dest_var (Var p) = p
  | dest_var _ = raise ERR "dest_var" "Term not a variable"

fun dest_const(Const(r, ty)) = (KernelSig.name_of r, ty)
  | dest_const _ = raise ERR "dest_const" "Term not a constant"

fun dest_thy_const t = let
  open KernelSig
in
  case t of
    Const(r, ty) => {Thy = seg_of r, Name = name_of r, Ty = ty}
  | _ => raise ERR "dest_thy_const" "Term not a constant"
end

fun dest_comb(App p) = p
  | dest_comb _ = raise ERR "dest_comb" "Term not a comb"

val rator = #1 o dest_comb
val rand = #2 o dest_comb

val strip_comb =
 let val destc = total dest_comb
     fun strip rands M =
      case destc M
       of NONE => (M, rands)
        | SOME(Rator,Rand) => strip (Rand::rands) Rator
 in strip []
 end

fun dest_abs(Abs p) = p
  | dest_abs _ = raise ERR "dest_abs" "Term not an abstraction"
val bvar = #1 o dest_abs
val body = #2 o dest_abs

fun strip_binder binder = let
  val f = case binder of
            NONE => (fn t => if is_abs t then SOME t else NONE)
          | SOME c => (fn t => let
                            val (rator, rand) = dest_comb t
                          in
                            if same_const rator c andalso is_abs rand then
                              SOME rand
                            else NONE
                          end handle HOL_ERR _ => NONE)
  fun recurse acc t =
      case f t of
        NONE => (List.rev acc, t)
      | SOME abs => let
          val (v, body) = dest_abs abs
        in
          recurse (v::acc) body
        end
in
  recurse []
end

val strip_abs = strip_binder NONE

fun dest_tycomb(TApp p) = p
  | dest_tycomb _ = raise ERR "dest_tycomb" "Term not a type application"

val tyrator = #1 o dest_tycomb
val tyrand = #2 o dest_tycomb

val strip_tycomb =
 let val destc = total dest_tycomb
     fun strip rands M =
      case destc M
       of NONE => (M, rands)
        | SOME(Rator,Rand) => strip (Rand::rands) Rator
 in strip []
 end

fun dest_tyabs(TAbs p) = p
  | dest_tyabs _ = raise ERR "dest_tyabs" "Term not a type abstraction"
val btyvar = #1 o dest_tyabs
val tybody = #2 o dest_tyabs

fun strip_tybinder binder = let
  val f = case binder of
            NONE => (fn t => if is_tyabs t then SOME t else NONE)
          | SOME c => (fn t => let
                            val (rator, rand) = dest_comb t
                          in
                            if same_const rator c andalso is_tyabs rand then
                              SOME rand
                            else NONE
                          end handle HOL_ERR _ => NONE)
  fun recurse acc t =
      case f t of
        NONE => (List.rev acc, t)
      | SOME tyabs => let
          val (v, body) = dest_tyabs tyabs
        in
          recurse (v::acc) body
        end
in
  recurse []
end

val strip_tyabs = strip_tybinder NONE


(* free variable calculations *)

fun var_compare0 m (tyenv1, tyenv2) p =
    case p of
      (Var(s1, ty1), Var(s2, ty2)) => let
      in
        case String.compare(s1, s2) of
          EQUAL => Type.compare0 m (tyenv1, tyenv2) (ty1, ty2)
        | x => x
      end
    | _ => raise ERR "var_compare0" "variables required"

fun var_compare p =
    case p of
      (Var(s1, ty1), Var(s2, ty2)) => let
      in
        case String.compare(s1, s2) of
          EQUAL => Type.compare(ty1, ty2)
        | x => x
      end
    | _ => raise ERR "var_compare" "variables required"

val empty_tyvarset = HOLset.empty Type.raw_compare
val empty_varset = HOLset.empty var_compare


(* term comparison *)
structure Map = Binarymap
val empty_tyenv = Map.mkDict Type.compare
val empty_env = Map.mkDict var_compare

fun compare p = let
  open Map
  fun cmp (D as (m,n)) (E as (tyenv1, tyenv2, env1, env2)) p =
      if m = 0 andalso n = 0 andalso Portable.pointer_eq p then EQUAL
      else
        case p of
          (v1 as Var _, v2 as Var _) => let
          in
            case (peek(env1, v1), peek(env2, v2)) of
              (NONE, NONE) => var_compare0 m (tyenv1, tyenv2) (v1, v2)
            | (SOME _, NONE) => GREATER
            | (NONE, SOME _) => LESS
            | (SOME i, SOME j) => Int.compare(j, i)
              (* flipping i & j deliberate; mimics deBruijn implementation's
                 behaviour, which would number variables in reverse order
                 from that done here *)
          end
        | (Var _, _) => LESS
        | (_, Var _) => GREATER
        | (Const(cid1, ty1), Const(cid2, ty2)) => let
          in
            case compare_cinfo(cid1, cid2) of
              EQUAL => Type.compare0 m (tyenv1, tyenv2) (ty1, ty2)
            | x => x
          end
        | (Const _, _) => LESS
        | (_, Const _) => GREATER
        | (App(M, N), App(P, Q)) => let
          in
            case cmp D E (M, P) of
              EQUAL => cmp D E (N, Q)
            | x => x
          end
        | (App _, _) => LESS
        | (_, App _) => GREATER
        | (Abs(v1, bdy1), Abs(v2, bdy2)) => let
          in
            case Type.compare0 m (tyenv1, tyenv2) (type_of v1, type_of v2) of
              EQUAL => cmp (m, n + 1) (tyenv1, tyenv2, insert(env1, v1, n), insert(env2, v2, n))
                           (bdy1, bdy2)
            | x => x
          end
        | (Abs _, _) => LESS
        | (_, Abs _) => GREATER
        | (TApp(M, S), TApp(P, T)) => let
          in
            case cmp D E (M, P) of
              EQUAL => Type.compare0 m (tyenv1, tyenv2) (S, T)
            | x => x
          end
        | (TApp _, _) => LESS
        | (_, TApp _) => GREATER
        | (TAbs(a1, bdy1), TAbs(a2, bdy2)) => let
             val (_,kd1) = dest_var_type a1
             val (_,kd2) = dest_var_type a2
          in
            case Kind.kind_compare(kd1, kd2) of
              EQUAL => cmp (m + 1, n) (insert(tyenv1, a1, n), insert(tyenv2, a2, n), env1, env2)
                           (bdy1, bdy2)
            | x => x
          end
in
  cmp (0,0) (empty_tyenv, empty_tyenv, empty_env, empty_env) p
end

val empty_tmset = HOLset.empty compare

fun aconv t1 t2 = compare(t1, t2) = EQUAL

val term_eq = aconv

fun has_var_rankl ((tm:term)::tms) = true
  | has_var_rankl [] = false

fun free_in M N = let
  val Mfvs = FVL [M] empty_varset
  fun recurse t =
      if compare(M, t) = EQUAL then true
      else
        case t of
          Var _ => false
        | Const _ => false
        | App(f, x) => recurse f orelse recurse x
        | Abs(v, bdy) => not (HOLset.member(Mfvs, v)) andalso
                         recurse bdy
        | TApp(f, a) => recurse f
        | TAbs(a, bdy) => recurse bdy
in
  recurse N
end

fun type_var_occurs aty =
  let val tyocc = if is_var_type aty then type_var_in aty else raise ERR "" ""
      fun occ (Var(_,ty))         = tyocc ty
        | occ (Const(_,ty))       = tyocc ty
        | occ (App(Rator,Rand))   = occ Rand  orelse occ Rator
        | occ (Abs(Bvar,Body))    = occ Bvar  orelse occ Body
        | occ (TApp(Rator,Ty))    = occ Rator orelse tyocc Ty
        | occ (TAbs(Btyvar,Body)) = aty <> Btyvar andalso occ Body
   in occ end
   handle HOL_ERR _ => raise ERR "type_var_occurs" "not a type variable";

fun var_occurs M = let
  val v as (_,ty) = case M of
                      Var v => v
                    | _ => raise ERR "var_occurs" "Term not a variable"
  fun occ (Var u) = (v = u)
    | occ (Const _) = false
    | occ (App(f, x)) = occ f orelse occ x
    | occ (Abs(Var u, body)) = u <> v andalso occ body
    | occ (Abs _) = raise Fail "catastrophic invariant failure"
    | occ (TApp(f, a)) = occ f
    | occ (TAbs(a, body)) = not (type_var_in a ty) andalso occ body
in
  occ
end

(*
fun type_vars_in_term t = let
  fun tyv t k =
      case t of
        Var(_, ty) => k (Type.type_vars ty)
      | Const(_, ty) => k (Type.type_vars ty)
      | App(f, x) => tyv f (fn fq => tyv x (fn xq => k (union fq xq)))
      | Abs(x, b) => tyv x (fn xq => tyv b (fn bq => k (union xq bq)))
      | TApp(f, a) => tyv f (fn fq => k (union fq (Type.type_vars a)))
      | TAbs(a, b) => tyv b (fn bq => k (set_diff bq [a]))
in
  tyv t Lib.I
end
*)

(*-----------------------------------------------------------------------------*
 * The free type variables of a lambda term. Tail recursive (from Ken Larsen). *
 *-----------------------------------------------------------------------------*)

local val ty_tyV = Type.type_vars
      fun tyV (Var(_,Ty)) k        = k (ty_tyV Ty)
        | tyV (Const(_,Ty)) k      = k (ty_tyV Ty)
        | tyV (App(Rator,Rand)) k  = tyV Rand (fn q1 =>
                                     tyV Rator(fn q2 => k (union q2 q1)))
        | tyV (Abs(Bvar,Body)) k   = tyV Body (fn q1 =>
                                     tyV Bvar (fn q2 => k (union q2 q1)))
        | tyV (TApp(Rator,Ty)) k   = tyV Rator (fn q  =>
                                         k (union q (ty_tyV Ty)))
        | tyV (TAbs(a,Body)) k     = tyV Body (fn bq => k (set_diff bq [a]))
      fun tyVs (t::ts) k           = tyV t (fn q1 =>
                                     tyVs ts (fn q2 => k (union q2 q1)))
        | tyVs [] k                = k []
in
fun type_vars_in_term tm = tyV tm Lib.I
fun type_vars_in_terml tms = tyVs tms Lib.I
end;

(* two different substs; monomorphism restriction bites again; later code
   gives these different types *)
val emptyvsubst = Map.mkDict compare
val emptysubst = Map.mkDict compare

val empty_stringset = HOLset.empty String.compare

(* it's hard to calculate free names simply by traversing a term because
   of the situation where \x:ty1. body has x:ty1 and x:ty2 as free variables
   in body.  So, though it may be slightly less efficient, my solution here
   is to just calculate the free variables and then calculate the image of
   this set under name extraction *)
val free_names = let
  fun fold_name (v, acc) = HOLset.add(acc, #1 (dest_var v))
in
  (fn t => HOLset.foldl fold_name empty_stringset (FVL [t] empty_varset))
end
fun free_type_names t = List.foldr (fn (v,acc) => HOLset.add(acc,#1(dest_var_type v)))
                                   empty_stringset (type_vars_in_term t)

(* jrh's caml light HOL Light code
let vsubst =
  let mk_qcomb = qcomb(fun (x,y) -> Comb(x,y)) in
  let rec vsubst theta tm =
    match tm with
      Var(_,_)  -> (try snd(op_rev_assoc eq tm theta)
                    with Failure _ -> raise Unchanged)
    | Const(_,_) -> raise Unchanged
    | Comb(f,x) -> mk_qcomb (vsubst theta) (f,x)
    | Abs(_,_) -> fst(vasubst theta tm)
  and vasubst theta tm =
    match tm with
      Var(_,_)  -> (try snd(op_rev_assoc eq tm theta),[tm]
                  with Failure _ -> raise Unchanged)
    | Const(_,_) -> raise Unchanged
    | Comb(l,r) -> (try let l',vs = vasubst theta l in
                        try let r',vt = vasubst theta r in
                            Comb(l',r'),op_union eq vs vt
                        with Unchanged -> Comb(l',r),vs
                    with Unchanged ->
                        let r',vt = vasubst theta r in Comb(l,r'),vt)
    | Abs(v,bod) -> let theta' = filter (not(eq prefix v) o snd) theta in
                    if theta' = [] then raise Unchanged else
                    let bod',vs = vasubst theta' bod in
                    let tms = map
                      (eval o fst o C op_rev_assoc eq theta') vs in
                    if exists (op_mem eq v) tms then
                      let fvs = itlist (op_union eq) tms (op_subtract eq (frees bod) vs) in
                      let v' = variant fvs v in
                      let bod',vars' = vasubst
                        (((eager [v'],v'),v)::theta') bod in
                      Abs(v',bod'),op_subtract eq vars' [v]
                    else
                      Abs(v,bod'),vs in
  fun theta ->
    if null theta then (fun tm -> tm) else
    let atheta = map
      (fun (t,x) -> if eq_ty (type_of t) (snd(dest_var x))
                    then (lazy frees t,t),x
                    else failwith "vsubst: Bad substitution list") theta in
    qtry(vsubst atheta);;
*)

fun set_name_variant nmset n = let
  val next = Lexis.nameStrm n
  fun loop n = if HOLset.member(nmset, n) then loop (next())
               else n
in
  loop n
end

fun set_type_name_variant nmset n = let
  val next = Lexis.tyvar_vary
  fun loop n = if HOLset.member(nmset, n) then loop (next n)
               else n
in
  loop n
end

(* -------------------------------------- *)
(* Proper substitution of terms for terms *)
(* -------------------------------------- *)

local
  open Map

  exception NeedToRename of term
  val empty_tyvsubst = mkDict Type.raw_compare
  val empty_ctxt = mkDict compare
  fun type_vars ty = Type.type_vars_set raw_empty_tyset raw_empty_tyset [ty]

  datatype fvinfo = FVI of { currentty : hol_type HOLset.set,
                             current : term HOLset.set,
                             is_full : bool,
                             left : fvinfo option, (* also used for Abs (inabs) *)
                             right : fvinfo option } (* also used for (absv) *)
  fun leaf (tys,tms,b) =
    FVI {currentty = tys, current = tms, is_full = b, left = NONE, right = NONE}
  fun current (FVI r) = #current r
  fun currentty (FVI r) = #currentty r
  fun is_full (FVI r) = #is_full r
  fun left (FVI r) = valOf (#left r)
  fun right (FVI r) = valOf (#right r)
  fun pureleft (FVI r) = #left r
  fun pureright (FVI r) = #right r
  (* computes a tree with information about the set of free variables in tm,
     returns early when all redexes in tytheta and theta have become bound *)
  fun calculate_fvinfo_ty theta_opt ty =
      leaf (type_vars ty, empty_tmset, true)
  fun calculate_fvinfo theta_opt tm =
      case tm of
        Var (_,ty) => leaf (type_vars ty, HOLset.singleton var_compare tm, true)
      | Const (_,ty) => leaf (type_vars ty, empty_varset, true)
      | App (f, x) =>
        let
          val fvs = calculate_fvinfo theta_opt f
          val xvs = calculate_fvinfo theta_opt x
        in
          FVI {currentty = HOLset.union (currentty fvs, currentty xvs),
               current = HOLset.union (current fvs, current xvs),
               is_full = is_full fvs andalso is_full xvs,
               left = SOME fvs, right = SOME xvs}
        end
      | Abs (v, body) =>
        let
          val theta'_opt = Option.map
            (fn theta => #1 (remove (theta, v)) handle NotFound => theta)
            theta_opt
        in
          if isSome theta'_opt andalso numItems (valOf theta'_opt) = 0 then
            (* return early *)
            leaf (empty_tyvarset, empty_varset, false)
          else
            let
              val vvs = calculate_fvinfo theta'_opt v
              val bodyvs = calculate_fvinfo theta'_opt body
            in
              FVI {currentty = HOLset.union(currentty vvs, currentty bodyvs),
                   current = safe_delete(current bodyvs, v),
                   is_full = is_full bodyvs andalso is_full vvs,
                   left = SOME bodyvs, right = SOME vvs}
            end
        end
      | TApp (f, t) =>
        let
          val fvs = calculate_fvinfo theta_opt f
          val tvs = leaf (type_vars t, empty_varset, true)
        in
          FVI {currentty = HOLset.union(currentty fvs, currentty tvs),
               current = current fvs,
               is_full = is_full fvs andalso is_full tvs,
               left = SOME fvs, right = SOME tvs}
        end
      | TAbs (a, body) =>
        let
          val avs = leaf (HOLset.singleton Type.raw_compare a, empty_tmset, true)
          val bodyvs = calculate_fvinfo theta_opt body
        in
          FVI {currentty = safe_delete(currentty bodyvs, a),
               current = current bodyvs,
               is_full = is_full bodyvs andalso is_full avs,
               left = SOME bodyvs, right = SOME avs}
        end
  (* expands a (possibly partial) tree with information about the set of free
     variables in tm into a tree with full information *)
(*
  fun expand_partial_fvinfo_ty ty fvi =
        FVI {currentty = HOLset.union (currentty fvi, type_vars ty),
             current = current fvi,
             is_full = true,
             left = pureleft fvi, right = pureright fvi}
*)
  fun expand_partial_fvinfo_ty ty fvi = leaf (type_vars ty, empty_varset, true)
  fun expand_partial_fvinfo tm fvi =
    if is_full fvi then
      raise Unchanged
    else
      case tm of
        App (f, x) =>
          qcomb2 (fn (fvs, xvs) =>
              FVI {currentty = HOLset.union (currentty fvs, currentty xvs),
                   current = HOLset.union (current fvs, current xvs),
                   is_full = true,
                   left = SOME fvs, right = SOME xvs})
            (expand_partial_fvinfo f, expand_partial_fvinfo x)
            (left fvi, right fvi)
      | Abs (v, body) =>
          let
            val vvs = right fvi
              handle Option => calculate_fvinfo NONE v
            val bodyvs = expand_partial_fvinfo body (left fvi)
              handle Option => calculate_fvinfo NONE body
          in
            FVI {currentty = HOLset.union (currentty vvs, currentty bodyvs),
                 current = safe_delete (current bodyvs, v),
                 is_full = true,
                 left = SOME bodyvs, right = SOME vvs}
          end
      | TApp (f, t) =>
          qcomb2 (fn (fvs, tvs) =>
              FVI {currentty = HOLset.union (currentty fvs, currentty tvs),
                   current = HOLset.union (current fvs, current tvs),
                   is_full = true,
                   left = SOME fvs, right = SOME tvs})
            (expand_partial_fvinfo f, expand_partial_fvinfo_ty t)
            (left fvi, right fvi)
      | TAbs (a, body) =>
          let
            val avs = right fvi
              handle Option => calculate_fvinfo_ty NONE a
            val bodyvs = expand_partial_fvinfo body (left fvi)
              handle Option => calculate_fvinfo NONE body
          in
            FVI {currentty = safe_delete (currentty bodyvs, a),
                 current = current bodyvs,
                 is_full = true,
                 left = SOME bodyvs, right = SOME avs}
          end
      | _ => raise Fail "expand_partial_fvinfo: catastrophic invariant failure"

  fun ty_vsubst tytheta ty = if numItems tytheta = 0 then raise Unchanged
                             else Type.vsubst tytheta ty

  fun type_vsubst tytheta ty = if numItems tytheta = 0 then ty
                             else Type.vsubst tytheta ty handle Unchanged => ty

  fun filtertheta theta fvset = let
    (* Removes entries in theta for things not in fvset.  theta likely to
       be much smaller than fvset, so fold over that rather than the
       other *)
    fun foldthis (k,v,acc) = if HOLset.member(fvset, k) then insert(acc, k, v)
                             else acc
  in
    foldl foldthis emptyvsubst theta
  end

  fun tyset_vsubst tytheta tyset =
    if numItems tytheta = 0 then tyset
    else HOLset.foldl (fn (ftyv,acc) =>
                         HOLset.add(acc, Type.vsubst tytheta ftyv
                                         handle Unchanged => ftyv))
                      empty_tyvarset tyset

  fun varset_vsubst tytheta varset =
    if numItems tytheta = 0 then varset
    else HOLset.foldl (fn (v,acc) =>
                         let val (n,ty) = dest_var v
                         in HOLset.add(acc, Var(n, Type.vsubst tytheta ty)
                                            handle Unchanged => v)
                         end)
                      empty_tmset varset

  fun augvsubst tytheta theta fvi tm =
      case tm of
        (v as Var (s,ty)) => let
          val (tychanged, ty') = (true, ty_vsubst tytheta ty)
                                 handle Unchanged => (false, ty)
          val v' = Var (s,ty')
          val (changed, nv) = case peek (theta, v') of
                                NONE => (tychanged, v')
                              | SOME (_, _, t) => (true, t)
        in
          if changed then nv
          else raise Unchanged
        end
      | Const (id,ty) => Const (id, ty_vsubst tytheta ty)
      | App p => qcomb2 App
          (augvsubst tytheta theta (left fvi), augvsubst tytheta theta (right fvi)) p
      | Abs (v, body) => let
          val (vname, vty) = dest_var v
          val (changed, vty') = (true, ty_vsubst tytheta vty)
                                handle Unchanged => (false, vty)
          val v' = mk_var (vname, vty')
          val theta' = #1 (remove (theta, v)) handle NotFound => theta
          val _ = if numItems theta' = 0 andalso numItems tytheta = 0 then raise Unchanged else ()
          val currentfvs = varset_vsubst tytheta (current fvi)
          val v_fvi = right fvi
          val body_fvi = left fvi
          (* first calculate the new names we are about to introduce into
             the term *)
          fun foldthis (k, v, acc) =
              if HOLset.member (currentfvs, k) then
                HOLset.union (acc, Susp.force (#2 v))
              else acc
          val newnames = foldl foldthis empty_stringset theta'
        in
          (* The bound variable must be renamed if either
               a. its name is the same as a new name being introduced into the term, or
               b. its image under tytheta is the same as the image of a free variable of the term *)
          if HOLset.member(newnames, vname) orelse HOLset.member(currentfvs, v') then
            let
              (* now need to vary v, avoiding both newnames, and also the
                 existing free-names of the whole term. *)
              val v_fvi = expand_partial_fvinfo v v_fvi
                handle Unchanged => v_fvi
              val body_fvi = expand_partial_fvinfo body body_fvi
                handle Unchanged => body_fvi
              val bodyfvs = current body_fvi
              fun foldthis (fv, acc) = HOLset.add (acc, #1 (dest_var fv))
              fun addtyname (ftyv, acc) = HOLset.add(acc, #1 (dest_var_type ftyv))
              val allfreenames = HOLset.foldl foldthis newnames bodyfvs
              val new_vname = set_name_variant allfreenames vname
              val new_v = mk_var (new_vname, vty')
              val new_theta =
                  if HOLset.member(varset_vsubst tytheta bodyfvs, v')
                  (* NOT the same as HOLset.member(bodyfvs, v) *)
                  then let
                      val tynameset = HOLset.foldl addtyname empty_stringset
                                                   (tyset_vsubst tytheta (currentty v_fvi))
                                      (*Type.free_names vty'*)
                      val singleton = HOLset.singleton String.compare new_vname
                    in
                      insert(theta', v', (Susp.delay (fn () => tynameset),
                                          Susp.delay (fn () => singleton),
                                          new_v))
                    end
                  else theta'
            in
              Abs (new_v, augvsubst tytheta new_theta body_fvi body
                          handle Unchanged => body)
            end
          else
            Abs (v', augvsubst tytheta theta' body_fvi body
                     handle Unchanged => if changed then body else raise Unchanged)
        end
      | TApp p => qcomb2 TApp
          (augvsubst tytheta theta (left fvi), ty_vsubst tytheta) p
(*
      | TApp (f, a) => let
          val afvi = right fvi
        in
          let
            val ffvi = left fvi
            val f' = augvsubst tytheta theta ffvi f
          in
            let val a' = ty_vsubst tytheta a
            in
              TApp (f', a')
            end handle Unchanged => TApp (f', a)
          end handle Unchanged => let val a' = ty_vsubst tytheta a
                                  in
                                    TApp (f, a')
                                  end
        end
*)
      | TAbs (a, body) => let
          fun removewitha (k,v,acc) =
              if HOLset.member(type_vars (type_of k), a) then acc
              else insert(acc, k, v)
          val theta' = foldl removewitha emptyvsubst theta
          val tytheta' = #1 (remove(tytheta, a)) handle NotFound => tytheta
          val _ = if numItems theta' = 0 andalso numItems tytheta' = 0 then raise Unchanged else ()
          val (aname, akd) = dest_var_type a
          val currentftyvs = currentty fvi
          val currentfvs = varset_vsubst tytheta' (current fvi)
          val a_fvi = right fvi
          val body_fvi = left fvi
          (* first calculate the new type names we are about to introduce into
             the term *)
          fun foldthisty (k,v,acc) =
              if HOLset.member(currentftyvs, k) then
                HOLset.union(acc, Susp.force (#1 v))
              else acc
          val newnames0 = foldl foldthisty empty_stringset tytheta'
          fun foldthis (k,v,acc) =
              if HOLset.member(currentfvs, k) then
                HOLset.union(acc, Susp.force (#1 v))
              else acc
          val newnames = foldl foldthis newnames0 theta'
        in
          if HOLset.member(newnames, aname) then let
              (* now need to vary a, avoiding both newnames, and also the
                 existing free-type-names of the whole term. *)
              val body_fvi = expand_partial_fvinfo body body_fvi
                handle Unchanged => body_fvi
              val bodyftyvs = currentty body_fvi
              fun foldthis (fv, acc) = HOLset.add(acc, #1 (dest_var_type fv))
              val allfreenames = HOLset.foldl foldthis newnames currentftyvs
              val new_aname = set_type_name_variant allfreenames aname
              val new_a = mk_var_type(new_aname, akd)
              val new_tytheta =
                  if HOLset.member(tyset_vsubst tytheta' bodyftyvs, a)
                  (* NOT the same as HOLset.member(bodyftyvs, a) *)
                  (* Note that a is unchanged by tytheta' because of remove above *)
                  then let
                      val singleton = HOLset.singleton String.compare new_aname
                    in
                      insert(tytheta', a, (Susp.delay (fn () => singleton),
                                           new_a))
                    end
                  else tytheta'
            in
              TAbs (new_a, augvsubst new_tytheta theta' body_fvi body
                           handle Unchanged => body)
            end
          else
            TAbs (a, augvsubst tytheta' theta' body_fvi body)
        end

  fun vsubst theta tm =
      case tm of
        Var _ => (case peek(theta, tm) of NONE => raise Unchanged
                                        | SOME (_, _, t) => t)
      | Const _ => raise Unchanged
      | App p  => qcomb App (vsubst theta) p
      | TApp (t,a) => TApp (vsubst theta t, a)
      | _ => (* either Abs or TAbs *)
        let
          val fvi = calculate_fvinfo (SOME theta) tm
          val theta' = filtertheta theta (current fvi)
        in
          if numItems theta' = 0 then raise Unchanged
          else augvsubst empty_tyvsubst theta' fvi tm
        end

  fun ssubst theta t =
      (* only used to substitute in fresh variables (genvars), so no
         capture check -- potentially incorrect (because there is no
         guarantee that genvars are actually fresh).
         The free type vars of the type of the genvar
         will be a subset of the free type vars of the redex. *)
      if numItems theta = 0 then raise Unchanged
      else
        case peek(theta, t) of
          SOME v => v
        | NONE => let
          in
            case t of
              App p => qcomb App (ssubst theta) p
            | Abs(v, body) => let
                fun modify_theta (k,value,newtheta) =
                    if free_in v k then newtheta
                    else insert(newtheta, k, value)
                val newtheta = foldl modify_theta emptysubst theta
              in
                Abs(v, ssubst newtheta body)
              end
            | TApp (tm,ty) => TApp(ssubst theta tm, ty)
            | TAbs (a,body) => let
                fun modify_theta (k,value,newtheta) =
                    if mem a (type_vars_in_term k) then newtheta
                    else insert(newtheta, k, value)
                val newtheta = foldl modify_theta emptysubst theta
              in
                TAbs(a, ssubst newtheta body)
              end
            | _ => raise Unchanged
          end

  fun vsubst_insert (map, k, v) =
      insert (map, k, (Susp.delay (fn () => free_type_names v),
                       Susp.delay (fn () => free_names v),
                       v))
(*
  fun tyvsubst_insert(map, k, v) =
      insert (map, k, (Susp.delay (fn () => Type.free_names v), v))
*)
in

(* Due to the missing capture check in ssubst, subst can produce wrong results
   (with accidental variable capture) unless all redexes in theta are
   variables.

   Therefore, all calls to subst that occur in Thm must ensure this
   precondition. *)

fun subst theta =
    if null theta then I
    else if List.all (is_var o #redex) theta then let
        fun foldthis ({redex, residue}, acc) = let
          val _ = eq_ty (type_of redex) (type_of residue)
                  orelse raise ERR "vsubst" "Bad substitution list"
        in
          if eq redex residue then acc
          else vsubst_insert (acc, redex, residue)
        end
        val atheta = List.foldl foldthis emptyvsubst theta
      in
        if numItems atheta = 0 then I
        else (fn tm => vsubst atheta tm handle Unchanged => tm)
      end
    else let
        fun foldthis ({redex,residue}, (theta1, theta2)) = let
          val _ = eq_ty (type_of redex) (type_of residue)
                  orelse raise ERR "vsubst" "Bad substitution list"
          val gv = genvar (type_of redex)
        in
          (insert (theta1, redex, gv), vsubst_insert (theta2, gv, residue))
        end
        val (theta1, theta2) =
            List.foldl foldthis (emptysubst, emptyvsubst) theta
      in
        (fn tm => vsubst theta2 (ssubst theta1 tm)
                  handle Unchanged => tm)
      end

end (* local *)


(*---------------------------------------------------------------------------*
 *     Instantiate type variables in a term                                  *
 *---------------------------------------------------------------------------*)

local
  exception NeedToRename of term
  structure Map = struct open Redblackmap end
  val empty_ctxt = Map.mkDict compare : (term, hol_type) Map.dict
  fun type_vars ty = Type.type_vars_set raw_empty_tyset raw_empty_tyset [ty]
  fun inst1 theta ctxt t =
      case t of
        (c as Const(r, ty)) => (case pure_ty_sub theta ty of
                                  SAME => raise Unchanged
                                | DIFF ty => Const(r, ty))
      | (v as Var(name,ty0)) => let
          val (changed, nv) = case pure_ty_sub theta ty0 of
                                SAME => (false, v)
                              | DIFF ty => (true, Var(name, ty))
        in
          case Map.peek (ctxt, nv) of
            SOME oldtype => if eq_ty oldtype ty0 then ()
                            else raise NeedToRename nv
          | NONE => ();
          if changed then nv
          else raise Unchanged
        end
      | App p => qcomb App (inst1 theta ctxt) p
      | Abs (v as Var(n, ty), body) => let
          val (changed, v') = case pure_ty_sub theta ty of
                                SAME => (false, v)
                              | DIFF ty' => (true, Var(n, ty'))
        in
          let
            val body' = SOME (inst1 theta (Map.insert(ctxt,v',ty)) body)
                        handle Unchanged => NONE
          in
            case (body', changed) of
              (SOME t, _) => Abs(v', t)
            | (NONE, true) => Abs(v', body)
            | (NONE, false) => raise Unchanged
          end handle e as NeedToRename v'' =>
                     if eq v' v'' then let
                         val free_names = free_names t
                         val new_name = set_name_variant free_names n
                         val newv = Var(new_name, ty)
                       in
                         inst1 theta ctxt (Abs(newv, subst [v |-> newv] body))
                       end
                     else raise e
        end
      | TApp (tm,ty) => let in
                          case pure_ty_sub theta ty of
                            SAME => TApp (inst1 theta ctxt tm, ty)
                          | DIFF ty' => let val tm' = inst1 theta ctxt tm
                                        in TApp (tm', ty')
                                        end
                                        handle Unchanged => TApp (tm, ty')
                        end
      | TAbs (a, body) => let
          val (name, kd) = dest_var_type a
              handle HOL_ERR _ => raise Fail "inst1: catastrophic invariant failure!"
          fun remove(theta,key) = Lib.filter (fn p => key <> #redex p) theta
          val theta = remove(theta,a)
          (* first calculate the new type names we are about to introduce into
             the term *)
          val body_tyvs = HOLset.addList(raw_empty_tyset, type_vars_in_term body)
          val free_tyvs = HOLset.delete(body_tyvs, a) handle NotFound => body_tyvs
          fun foldthis ({redex,residue}, acc) =
            if HOLset.member(free_tyvs, redex) then HOLset.union(type_vars residue, acc)
                                               else acc
          val newtyvs = List.foldl foldthis raw_empty_tyset theta
          fun foldthis1 (tyv,acc) = HOLset.add(acc, #1 (dest_var_type tyv))
          val newnames = HOLset.foldl foldthis1 empty_stringset newtyvs
        in
          if HOLset.member(newnames, name) then let
              (* now need to vary a, avoiding both newnames, and also the
                 existing free-type-names of the whole term. *)
              val allfreenames = HOLset.foldl foldthis1 newnames free_tyvs
              val new_name = set_type_name_variant allfreenames name
              val new_a = mk_var_type(new_name, kd)
              val new_theta = if HOLset.member(body_tyvs, a) then (a |-> new_a)::theta
                                                             else theta
            in
              TAbs(new_a, inst1 new_theta ctxt body)
            end
          else
            TAbs (a, inst1 theta ctxt body)
        end
      | _ => raise Fail "inst1: catastrophic invariant failure!"

  fun inst2 theta tm = inst1 theta empty_ctxt tm handle Unchanged => tm

  val instty = Type.ssubst
(*
  fun instty theta ty = let val ty' = Type.ssubst theta ty
                        in if Type.type_eq ty ty' then raise Unchanged
                                                  else ty'
                        end
*)

  open Binarymap
  val empty_tyvsubst = mkDict Type.raw_compare

  fun sinst theta t =
      (* only used to substitute in fresh variables (gentyvars), so no
         capture check.  *)
      if numItems theta = 0 then raise Unchanged
      else  case t of
              Var (n,ty) => Var (n, instty theta ty)
            | Const (id,ty) => Const (id, instty theta ty)
            | App p => qcomb App (sinst theta) p
            | Abs p => qcomb Abs (sinst theta) p
            | TApp (tm,ty) => (let
                val tm' = sinst theta tm
              in
                let val ty' = instty theta ty
                in
                  TApp(tm', ty')
                end handle Unchanged => TApp(tm', ty)
              end handle Unchanged => let val ty' = instty theta ty
                                      in
                                        TApp(tm, ty')
                                      end)
            | TAbs(a, body) => let
                fun modify_theta (k,value,newtheta) =
                    if type_var_in a k then newtheta
                    else insert(newtheta, k, value)
                val newtheta = foldl modify_theta empty_tyvsubst theta
              in
                TAbs(a, sinst newtheta body)
              end

(* inst properly ingores redexes which are not variables, for backwards compatibility. *)
fun inst1 [] = I
  | inst1 theta = inst2 (filter (is_var_type o #redex) theta)
(*
       if List.all (is_var_type o #redex) theta
       then inst2 theta
       else let
              fun foldthis ({redex,residue}, (theta1, theta2)) = let
                val gtyv = gen_var_type (kind_of redex)
              in
                (insert(theta1, redex, gtyv), (gtyv |-> residue)::theta2)
              end
              val (theta1, theta2) =
                  List.foldl foldthis (empty_tyvsubst, []) theta
            in
              (fn tm => inst2 theta2 (sinst theta1 tm)
                        handle Unchanged => tm)
            end
*)

(*
fun map_redex f = List.map (fn {redex,residue} => {redex=f redex, residue=residue})
*)

fun check_subst [] = ()
  | check_subst ({redex,residue} :: s) =
        if not (kind_of redex :>=: kind_of residue)
        then raise ERR "pure_inst" "kind of redex does not contain kind of residue"
        else check_subst s

in

val pure_inst : (hol_type, hol_type) Lib.subst -> term -> term =
  (fn theta => (check_subst theta;
                inst1 theta))
end


(*---------------------------------------------------------------------------*
 * Increasing the rank of all types in a term.                               *
 *---------------------------------------------------------------------------*)

fun inst_rank 0 = Lib.I
  | inst_rank rkS =
  if rkS < 0 then raise ERR "inst_rank" "increment is negative"
  else
  let val inst_ty = Type.inst_rank rkS
      fun inst (Var(s,ty))            = Var(s, inst_ty ty)
        | inst (Const(s,ty))          = Const(s, inst_ty ty)
        | inst (App(Rator,Rand))      = App(inst Rator, inst Rand)
        | inst (TApp(tm, ty))         = TApp(inst tm, inst_ty ty)
        | inst (Abs(Var(nm,ty),body)) = Abs(Var(nm, inst_ty ty), inst body)
        | inst (TAbs(a,body))         = TAbs(inst_ty a, inst body)
        | inst _ = raise ERR "inst_rank" "term construction"
  in inst
  end;

(*---------------------------------------------------------------------------*
 * Applying both a rank and a kind substitution to all types in a term.      *
 *---------------------------------------------------------------------------*)

local
  open Map
  exception NeedToRename of term

  (* inst_rank_kind1 may throw Unchanged(=Type.Unchanged), NeedToRename, or Type.NeedToRename *)

  fun inst_rank_kind1 (rk:int) theta tyctxt ctxt =
    let val inst_ty = Type.inst_rank_kind1 rk theta tyctxt
                      (* may throw Type.Unchanged, Type.NeedToRename *)
        fun inst (v as Var(Name,Ty)) = let
                val (changed, nv) = let val nTy = inst_ty Ty
                                    in if eq_ty nTy Ty then raise Unchanged
                                       else (true, Var(Name,nTy))
                                    end handle Unchanged => (false, v)
              in
                case peek (ctxt, nv) of
                  SOME oldty => if eq_ty oldty Ty then ()
                                else raise NeedToRename nv
                | NONE => ();
                if changed then nv
                else raise Unchanged
              end
          | inst (Const(r,Ty))      = Const(r, inst_ty Ty)
          | inst (App(Rator,Rand))  = qcomb App inst (Rator,Rand)
          | inst (tm as Abs(v as Var(Name,Ty), Body)) = let
                val (changed, v') = let val nTy = inst_ty Ty
                                    in if eq_ty nTy Ty then raise Unchanged
                                       else (true, Var(Name,nTy))
                                    end handle Unchanged => (false, v)
              in let
                   val Body' = SOME (inst_rank_kind1 rk theta tyctxt
                                                     (Map.insert(ctxt, v', Ty)) Body)
                               handle Unchanged => NONE
                 in
                   case (Body', changed) of
                     (SOME t, _) => Abs(v', t)
                   | (NONE, true) => Abs(v', Body)
                   | (NONE, false) => raise Unchanged
                 end handle e as NeedToRename v'' =>
                     if eq v' v'' then let
                         val free_names = free_names tm
                         val new_name = set_name_variant free_names Name
                         val newv = Var(new_name, Ty)
                       in
                         inst (Abs(newv, subst [v |-> newv] Body))
                       end
                     else raise e
              end
          | inst (TApp(Rator,Ty))   = let
              in let
                val Rator' = inst Rator
              in
                let val Ty' = inst_ty Ty
                in
                  TApp(Rator', Ty')
                end handle Unchanged => TApp(Rator', Ty)
              end handle Unchanged => let val Ty' = inst_ty Ty
                                      in
                                        TApp(Rator, Ty')
                                      end
              end
          | inst (tm as TAbs(v, Body)) = let
                val tyv as (Name,Kind) = dest_var_type v
                val (changed, tyv') = (true, (Name, Kind.inst_rank_kind (theta,rk) Kind))
                                      handle Unchanged => (false, tyv)
                val v' = mk_var_type tyv'
              in let
                   val Body' = SOME (inst_rank_kind1 rk theta
                                       (insert(tyctxt, tyv', Kind))
                                       ctxt Body)
                               handle Unchanged => NONE
                 in
                   case (Body', changed) of
                     (SOME t, _) => TAbs(v', t)
                   | (NONE, true) => TAbs(v', Body)
                   | (NONE, false) => raise Unchanged
                 end handle e as Type.NeedToRename tyv'' =>
                     if tyv' = tyv'' then let
                         val free_names = free_type_names tm
                         val new_name = set_type_name_variant free_names Name
                         val newv = mk_var_type(new_name, Kind)
                       in
                         inst (TAbs(newv, pure_inst [v |-> newv] Body))
                       end
                     else raise e
              end
          | inst _ = raise ERR "inst_rank_kind1" "catastrophic failure"
    in
      inst
    end

in

fun inst_rank_kind (   [],rk) = (inst_rank rk
                                 handle HOL_ERR {message=m, ...} => raise ERR "inst_rank_kind" m)
  | inst_rank_kind (theta,rk) =
      if rk < 0 then raise ERR "inst_rank_kind" "increment is negative"
      else let
        fun foldthis1  (r as {redex,residue}, acc) = let
          val _ = rank_of redex >= rank_of residue
                  orelse raise ERR "inst_rank_kind" "Bad kind substitution list"
        in
          if redex = residue then acc
          else r::acc
        end
        val atheta = List.foldr foldthis1 [] theta
      in
        fn tm =>
        inst_rank_kind1 rk atheta (Map.mkDict tyvar_compare) (Map.mkDict compare) tm
                    handle Unchanged => tm
                         | HOL_ERR {message=m, ...} => raise ERR "inst_rank_kind" m
      end

end (* local *);

(*---------------------------------------------------------------------------*
 * Applying a rank, kind, and type substitution to all types in a term.      *
 *---------------------------------------------------------------------------*)

local
  open Map
  exception NeedToRename of term

  (* inst_rk_kd_ty1 may throw Unchanged(=Type.Unchanged), NeedToRename, or Type.NeedToRename *)

  fun inst_rk_kd_ty1 (tytheta, kdtheta, rk:int) tyctxt ctxt =
    let val inst_ty = Type.inst_rk_kd_ty1 rk kdtheta tytheta tyctxt
                      (* may throw Type.Unchanged, Type.NeedToRename *)
        val inst_kd = Kind.vsubst_rk_kd rk kdtheta
                      (* may throw Kind.Unchanged=Type.Unchanged *)
        val kdinst_ty = Type.inst_rank_kind (kdtheta,rk)
        fun inst (v as Var(Name,Ty)) = let
                val (changed, nv) = let val nTy = inst_ty Ty
                                    in if eq_ty nTy Ty then raise Unchanged
                                       else (true, Var(Name,nTy))
                                    end handle Unchanged => (false, v)
              in
                case peek (ctxt, nv) of
                  SOME oldty => if eq_ty oldty Ty then ()
                                else raise NeedToRename nv
                | NONE => ();
                if changed then nv
                else raise Unchanged
              end
          | inst (Const(r,Ty))      = Const(r, inst_ty Ty)
          | inst (App(Rator,Rand))  = qcomb App inst (Rator,Rand)
          | inst (tm as Abs(v as Var(Name,Ty), Body)) = let
                val (changed, v') = let val nTy = inst_ty Ty
                                    in if eq_ty nTy Ty then raise Unchanged
                                       else (true, Var(Name,nTy))
                                    end handle Unchanged => (false, v)
              in let
                   val Body' = SOME (inst_rk_kd_ty1 (tytheta,kdtheta,rk) tyctxt
                                                    (Map.insert(ctxt, v', Ty)) Body)
                               handle Unchanged => NONE
                 in
                   case (Body', changed) of
                     (SOME t, _) => Abs(v', t)
                   | (NONE, true) => Abs(v', Body)
                   | (NONE, false) => raise Unchanged
                 end handle e as NeedToRename v'' =>
                     if eq v' v'' then let
                         val free_names = free_names tm
                         val new_name = set_name_variant free_names Name
                         val newv = Var(new_name, Ty)
                       in
                         inst (Abs(newv, subst [v |-> newv] Body))
                       end
                     else raise e
              end
          | inst (TApp(Rator,Ty))   = let
              in let
                val Rator' = inst Rator
              in
                let val Ty' = inst_ty Ty
                in
                  TApp(Rator', Ty')
                end handle Unchanged => TApp(Rator', Ty)
              end handle Unchanged => let val Ty' = inst_ty Ty
                                      in
                                        TApp(Rator, Ty')
                                      end
              end
          | inst (tm as TAbs(v, Body)) = let
                val tyv as (Name,Kind) = dest_var_type v
                val (changed, tyv') = (true, (Name, inst_kd Kind))
                                      handle Unchanged => (false, tyv)
                val v' = mk_var_type tyv'
                val tytheta = #1 (remove(tytheta, v)) handle NotFound => tytheta
                val currentfvs = HOLset.addList(empty_tyset, List.map kdinst_ty (type_vars_in_term tm))
                (* first calculate the new names we are about to introduce into
                   the type *)
                fun foldthis (k,v,acc) =
                    if HOLset.member(currentfvs, k) then
                      HOLset.union(acc, Susp.force (#1 v))
                    else acc
                val newnames = foldl foldthis empty_stringset tytheta
              in 
                 let
                   val _ = if HOLset.member(newnames, Name)
                           then raise Type.NeedToRename tyv'
                           else ()
                   val new_tyctxt = insert(tyctxt, tyv', Kind)
                   val Body' = SOME (inst_rk_kd_ty1 (tytheta,kdtheta,rk)
                                       new_tyctxt ctxt Body) (* may throw Type.NeedToRename *)
                               handle Unchanged => NONE
                 in
                   case (Body', changed) of
                     (SOME t, _) => TAbs(v', t)
                   | (NONE, true) => TAbs(v', Body)
                   | (NONE, false) => raise Unchanged
                 end handle e as Type.NeedToRename tyv'' =>
                     (* now need to vary v, avoiding both newnames, and also the
                        existing free-type-names of the whole term. *)
                     if tyv' = tyv'' then let
                         fun foldthis (fv, acc) = HOLset.add(acc, #1 (dest_var_type fv))
                         val allfreenames = HOLset.foldl foldthis newnames currentfvs
                         val new_name = set_type_name_variant allfreenames Name
                         val newv = mk_var_type(new_name, Kind)
                       in
                         inst (TAbs(newv, pure_inst [v |-> newv] Body))
                       end
                     else raise e
              end
          | inst _ = raise ERR "inst_rk_kd_ty1" "catastrophic failure"
    in
      inst
    end

in

fun inst_rk_kd_ty ([],kdtheta,rk) = (inst_rank_kind (kdtheta,rk)
                                     handle HOL_ERR {message=m, ...}
                                       => raise ERR "inst_rk_kd_ty" m)
  | inst_rk_kd_ty (tytheta,kdtheta,rk) =
      if rk < 0 then raise ERR "inst_rk_kd_ty" "increment is negative"
      else let
        fun foldthis1  (r as {redex,residue}, acc) = let
          val _ = rank_of redex >= rank_of residue
                  orelse raise ERR "inst_rk_kd_ty" "Bad kind substitution list"
        in
          if redex = residue then acc
          else r::acc
        end
        val akdtheta = List.foldr foldthis1 [] kdtheta
        fun foldthis2  (r as {redex,residue}, acc) = let
          val _ = kind_of redex :>=: kind_of residue
                  orelse raise ERR "inst_rk_kd_ty" "Bad type substitution list"
        in
          if eq_ty redex residue then acc
          else Type.vsub_insert(acc, redex, residue)
        end
        val atytheta = List.foldr foldthis2 Type.emptyvsubst (filter (is_var_type o #redex) tytheta)
      in
        fn tm =>
        inst_rk_kd_ty1 (atytheta,akdtheta,rk) (Map.mkDict tyvar_compare) (Map.mkDict compare) tm
                    handle Unchanged => tm
                         | HOL_ERR {message=m, ...} => raise ERR "inst_rk_kd_ty" m
      end

end (* local *);

val inst_kind = fn theta => inst_rank_kind (theta,0)

fun align_inst_kind []  = I
  | align_inst_kind kdS =
  let val Theta = align_kinds kdS
  in inst_rank_kind Theta
  end
  handle HOL_ERR {message, ...} => raise ERR "align_inst_kind" message

(*---------------------------------------------------------------------------*
 * Applying rank, kind, and type substitutions to all types in a term.       *
 *---------------------------------------------------------------------------*)

fun align_inst [] = I
  | align_inst theta =
  let val Theta = align_types theta
  in inst_rk_kd_ty Theta
  end

val inst = align_inst

fun inst_all (tmS,tyS,kdS,rkS) = (subst tmS o inst_rk_kd_ty (tyS,kdS,rkS))
                                 handle HOL_ERR{message=m,...} => raise ERR "inst_all" m;

local
fun align_terms0 (tyS,kdS,rkS) [] = (tyS,kdS,rkS)
  | align_terms0 (tyS,kdS,rkS) ({redex,residue} :: s) = let
        val (tyS',kdS',rkS') =
            Type.raw_kind_match_type (type_of redex) (type_of residue) (tyS,kdS,rkS)
      in
        align_terms0 (tyS',kdS',rkS') s
      end
in
fun align_terms theta = let
        val ((tyS,_),(kdS,_),(rkS,_)) = align_terms0 (([],[]),([],[]),(0,false)) theta
        fun inst_redex [] = []
          | inst_redex ({redex,residue} :: s) = let
                val redex' = inst_rk_kd_ty (tyS,kdS,rkS) redex (*pure_inst tyS (inst_rank_kind (kdS,rkS) redex)*)
              in
                if aconv redex' residue then inst_redex s
                else (redex' |-> residue) :: inst_redex s
              end
      in
        (if rkS = 0 andalso null kdS andalso null tyS
           then theta
           else inst_redex theta,
         tyS, kdS, rkS)
      end
end


local
  val FORMAT = ERR "list_mk_binder"
   "expected first arg to be a constant of type :(<ty>_1 -> <ty>_2) -> <ty>_3"
  fun check_opt NONE = Lib.I
    | check_opt (SOME c) =
      if not(is_const c) then raise FORMAT
      else case total ((*fst o Type.dom_rng o*) fst o Type.dom_rng o type_of) c of
             NONE => raise FORMAT
           | SOME ty => (fn abs =>
                         (* let val dom = fst(Type.dom_rng(type_of abs))
                            in mk_comb (align_inst[ty |-> dom] c, abs)
                            end *)
                            let val (tytheta,kdtheta,rk) = kind_match_type ty (type_of abs)
                            in mk_comb (inst_rk_kd_ty (tytheta,kdtheta,rk) c, abs)
                            end)
in
fun list_mk_binder binder = let
  val f = check_opt binder
  (* As of Mosml2.00, List.foldr is clearly not tail recursive, and you can
     blow the stack with big lists here.  Thus, the reversing of the list and
     the use of foldl instead, relying on the fact that it's hard to imagine
     not writing foldl tail-recursively *)
in
  fn (vlist, tm) =>
    if not (all is_var vlist) then raise ERR "list_mk_binder" "bound variable arg not a variable"
    else List.foldl (f o mk_abs) tm (List.rev vlist)
end
end (* local *)

val list_mk_abs = list_mk_binder NONE

local
  val FORMAT = ERR "list_mk_tybinder"
   "expected first arg to be a constant of type :(!<tyvar>. <ty>_2) -> <ty>_3"
  fun check_opt NONE = Lib.I
    | check_opt (SOME c) =
      if not(is_const c) then raise FORMAT
      else case total ((*fst o Type.dest_univ_type o*) fst o Type.dom_rng o type_of) c of
             NONE => raise FORMAT
           | SOME ty => (fn univ =>
                         (* let val dom = kind_of(fst(Type.dest_univ_type(type_of univ)))
                                val kdv = kind_of ty
                            in mk_comb (align_inst_kind [kdv |-> dom] c, univ)
                            end *) 
                            let val (tytheta,kdtheta,rk) = kind_match_type ty (type_of univ)
                            in mk_comb (inst_rk_kd_ty (tytheta,kdtheta,rk) c, univ)
                            end)
in
fun list_mk_tybinder binder = let
  val f = check_opt binder
  (* As of Mosml2.00, List.foldr is clearly not tail recursive, and you can
     blow the stack with big lists here.  Thus, the reversing of the list and
     the use of foldl instead, relying on the fact that it's hard to imagine
     not writing foldl tail-recursively *)
in
  fn (vlist, tm) => List.foldl (f o mk_tyabs) tm (List.rev vlist)
end
end (* local *)

val list_mk_tyabs = list_mk_tybinder NONE


fun beta_conv (App (Abs (v, body), x)) =
  if eq x v then body else subst [v |-> x] body
  | beta_conv (App _) =
  raise ERR "beta_conv" "LHS not an abstraction"
  | beta_conv _ =
  raise ERR "beta_conv" "Term not an application"

val lazy_beta_conv = beta_conv

fun eta_conv (Abs (x, App (f, x'))) =
  if eq x x' andalso not (free_in x f)
     andalso rank_of_term x = rank_of_type (fst (dom_rng (type_of f)))
  then f
  else raise ERR "eta_conv" "Term not an eta-redex"
  | eta_conv _ =
  raise ERR "eta_conv" "Term not an eta-redex"


fun ty_beta_conv (TApp (TAbs (a, body), ty)) =
  if ty = a then body else pure_inst [a |-> ty] body
  | ty_beta_conv (TApp _) =
  raise ERR "ty_beta_conv" "LHS not a type abstraction"
  | ty_beta_conv _ =
  raise ERR "ty_beta_conv" "Term not a type application"

fun ty_eta_conv (TAbs(a, TApp(f, a'))) =
  if a = a' andalso not (mem a (type_vars_in_term f))
     andalso kind_of a = kind_of (fst (dest_univ_type (type_of f)))
  then f
  else raise ERR "ty_eta_conv" "Term not a type eta-redex"
  | ty_eta_conv (TAbs _) =
  raise ERR "ty_eta_conv" "Term not a type eta-redex"
  | ty_eta_conv _ =
  raise ERR "ty_eta_conv" "Term not a type eta-redex"


(*---------------------------------------------------------------------------*
 *       Beta-conversion of all types within a term.                         *
 *---------------------------------------------------------------------------*)

val beta_conv_ty_in_term =
     let fun bconv(Var(s,ty))        = Var(s,deep_beta_ty ty)
           | bconv(Const(Name,Ty))   = Const(Name,deep_beta_ty Ty)
           | bconv(App(Rator,Rand))  = App(bconv Rator,bconv Rand)
           | bconv(Abs(v,Body))      = Abs(bconv v,bconv Body)
           | bconv(TApp(Rator,Ty))   = TApp(bconv Rator,deep_beta_ty Ty)
           | bconv(TAbs(a,Body))     = TAbs(a,bconv Body)
     in
       bconv
     end;

(*---------------------------------------------------------------------------*
 *       Eta-conversion of all types within a term.                          *
 *---------------------------------------------------------------------------*)

val eta_conv_ty_in_term =
     let fun econv(Var(s,ty))        = Var(s,deep_eta_ty ty)
           | econv(Const(Name,Ty))   = Const(Name,deep_eta_ty Ty)
           | econv(App(Rator,Rand))  = App(econv Rator,econv Rand)
           | econv(Abs(v,Body))      = Abs(econv v,econv Body)
           | econv(TApp(Rator,Ty))   = TApp(econv Rator,deep_eta_ty Ty)
           | econv(TAbs(a,Body))     = TAbs(a,econv Body)
     in
       econv
     end;

(*---------------------------------------------------------------------------*
 *       Beta-eta-conversion of all types within a term.                     *
 *---------------------------------------------------------------------------*)

val beta_eta_conv_ty_in_term =
     let fun beconv(Var(s,ty))        = Var(s,deep_beta_eta_ty ty)
           | beconv(Const(Name,Ty))   = Const(Name,deep_beta_eta_ty Ty)
           | beconv(App(Rator,Rand))  = App(beconv Rator,beconv Rand)
           | beconv(Abs(v,Body))      = Abs(beconv v,beconv Body)
           | beconv(TApp(Rator,Ty))   = TApp(beconv Rator,deep_beta_eta_ty Ty)
           | beconv(TAbs(a,Body))     = TAbs(a,beconv Body)
     in
       beconv
     end;


(*---------------------------------------------------------------------------*
 * Given a variable and a list of variables, if the variable does not exist  *
 * on the list, then return the variable. Otherwise, rename the variable and *
 * try again. Note well that the variant uses only the name of the variable  *
 * as a basis for testing equality. Experience has shown that basing the     *
 * comparison on both the name and the type of the variable resulted in      *
 * needlessly confusing formulas occasionally being displayed in interactive *
 * sessions.                                                                 *
 *---------------------------------------------------------------------------*)

fun gen_variant P caller =
  let fun var_name _ (Var(Name,_)) = Name
        | var_name caller _ = raise ERR caller "not a variable"
      fun vary vlist (Var(Name,Ty)) =
          let val next = Lexis.nameStrm Name
              val L = map (var_name caller) vlist
              fun away s = if mem s L then away (next()) else s
              fun loop name =
                 let val s = away name
                 in if P s then loop (next()) else s
                 end
          in mk_var(loop Name, Ty)
          end
        | vary _ _ = raise ERR caller "2nd argument should be a variable"
  in vary
  end;

val variant      = gen_variant inST "variant"
val prim_variant = gen_variant (K false) "prim_variant";

local val tyis_omega = Type.is_omega
in
  fun is_omega (Var(_,ty))       = tyis_omega ty
    | is_omega (Const (_,ty))    = tyis_omega ty
    | is_omega (App(Rator,Rand)) = is_omega Rand orelse is_omega Rator
    | is_omega (Abs(Bvar,Body))  = is_omega Bvar orelse is_omega Body
    | is_omega (TApp(Rator,Ty))  = true
    | is_omega (TAbs(Ty,Body))   = true
end


(* In the name-carrying implementation this operation is no longer constant
   time *)
fun rename_bvar newname t =
    case t of
      Abs(v, body) => let
        val (nm, ty) = dest_var v
        val newvar0 = mk_var(newname, ty)
        val newvar = variant (free_vars t) newvar0
      in
        Abs(newvar, subst [v |-> newvar] body)
      end
    | _ => raise ERR "rename_bvar" "Term not an abstraction"

fun rename_btyvar newname t =
    case t of
      TAbs(v, body) => let
        val (nm, kd) = dest_var_type v
        val newvar0 = mk_var_type(newname, kd)
        val newvar = variant_type (type_vars_in_term t) newvar0
      in
        TAbs(newvar, pure_inst [v |-> newvar] body)
      end
    | _ => raise ERR "rename_btyvar" "Term not a type abstraction"



(* ----------------------------------------------------------------------
    Matching
   ---------------------------------------------------------------------- *)

fun lookup x ids = let
  fun look [] = if HOLset.member(ids, x) then SOME x else NONE
    | look ({redex,residue}::t) = if eq x redex then SOME residue else look t
in
  look
end

fun bvar_free (bvmap, tm) = let
  (* return true if none of the free variables occur as keys in bvmap *)
  fun recurse bs t =
      case t of
        v as Var _ => HOLset.member(bs, v) orelse
                      not (isSome (Map.peek(bvmap, v)))
      | Const _ => true
      | App(f,x) => recurse bs f andalso recurse bs x
      | Abs(v, body) => recurse (HOLset.add(bs, v)) body
      | TApp(f,a) => recurse bs f
      | TAbs(a, body) => recurse bs body
in
  Map.numItems bvmap = 0 orelse recurse empty_varset tm
end

fun MERR s = raise ERR "raw_match_term" s

fun add_id v {ids, patbvars, obbvars, theta, n} =
    {ids = HOLset.add(ids, v), patbvars = patbvars, obbvars = obbvars, n = n,
     theta = theta}
fun add_binding v tm {ids, patbvars, obbvars, theta, n} =
    {ids = ids, patbvars = patbvars, obbvars = obbvars, n = n,
     theta = (v |-> tm) :: theta}

type tminfo = {ids : term HOLset.set, n : int,
               patbvars : (term,int)Map.dict,
               obbvars :  (term,int)Map.dict,
               theta : (term,term) Lib.subst}

datatype tmpair = TMP of term * term
                | BVrestore of {patbvars : (term,int)Map.dict,
                                obbvars : (term,int)Map.dict,
                                n : int}

val kdmatch = Kind.raw_match_kind
(*val tymatch = Type.raw_kind_match_type *)
fun tymatch pat ob ((lctys,env,insts_homs),kdS,rkS) =
        let val insts_homs' = Type.type_pmatch lctys env pat ob insts_homs
            val (kdS',rkS') = Type.get_rank_kind_insts [] env (fst insts_homs') (kdS,rkS)
        in ((lctys,env,insts_homs'),kdS',rkS')
        end
fun add_env mp (lctys,env,insts_homs) = (lctys,mp::env,insts_homs)
fun drop_env (tminfo,((lctys,env,insts_homs),kdS,rkS)) = (tminfo,((lctys,tl env,insts_homs),kdS,rkS))

fun RM patobs (theta0 as (tminfo, S as (tyS,kdS,rkS))) =
    case patobs of
      [] => theta0
    | TMP po::rest => let
      in
        case po of
          (v as Var(_, ty), tm) => let
          in
            case Map.peek(#patbvars tminfo, v) of
              NONE => (* var on left not bound *) let
              in
                if bvar_free (#obbvars tminfo, tm) then
                  RM rest ((case lookup v (#ids tminfo) (#theta tminfo) of
                              NONE => if eq v tm then add_id v tminfo
                                      else add_binding v tm tminfo
                            | SOME tm' => if aconv tm' tm then tminfo
                                          else MERR "double bind"),
                           tymatch ty (type_of tm) S)
                else
                  MERR "Attempt to capture bound variable"
              end
            | SOME i => if is_var tm andalso
                           Map.peek(#obbvars tminfo, tm) = SOME i
                        then
                          RM rest theta0
                        else MERR "Bound var doesn't match"
          end
        | (Const(c1, ty1), Const(c2, ty2)) =>
          if c1 <> c2 then MERR ("Different constants: "^c2string c1^" and "^
				 c2string c2)
          else RM rest (tminfo, tymatch ty1 ty2 S)
        | (App(f1, x1), App(f2, x2)) =>
          RM (TMP (f1, f2) :: TMP (x1, x2) :: rest) theta0
        | (Abs(x1, bdy1), Abs(x2, bdy2)) => let
            val S' = tymatch (type_of x1) (type_of x2) S
            val {ids, patbvars, obbvars, n, theta} = tminfo
          in
            RM (TMP (bdy1, bdy2) ::
                BVrestore {patbvars = patbvars, obbvars = obbvars, n = n} ::
                rest)
               ({ids = #ids tminfo, n = n + 1, theta = theta,
                 patbvars = Map.insert(patbvars, x1, n),
                 obbvars = Map.insert(obbvars, x2, n)}, S')
          end
        | (TApp(tm1, ty1), TApp(tm2, ty2)) => let
            val S' = tymatch ty1 ty2 S
          in
            RM (TMP (tm1, tm2) :: rest) (tminfo, S')
          end
        | (TAbs(a1, bdy1), TAbs(a2, bdy2)) => let
            val (_,kd1) = dest_var_type a1
            val (_,kd2) = dest_var_type a2
            val (kdS',rkS') = kdmatch kd1 kd2 (kdS,rkS)
            val tyS' = add_env (a1 |-> a2) tyS
            val S' = (tyS',kdS',rkS')
          in
            drop_env (RM (TMP (bdy1, bdy2) :: rest) (tminfo, S'))
          end
        | _ => MERR "Incompatible term types"
      end
    | BVrestore{patbvars, obbvars, n} :: rest => let
        val {ids, theta, ...} = tminfo
      in
        RM rest ({ids = ids, theta = theta, patbvars = patbvars,
                  obbvars = obbvars, n = n}, S)
      end

(* tyfixed: list of type variables that mustn't be instantiated
   tmfixed: set of term variables that mustn't be instantiated
   pat    : term "pattern" to match
   theta0 : an existing matching
*)

val empty_intsubst = Map.mkDict compare

fun raw_kind_match rkfixed kdfixed tyfixed tmfixed pat ob (tmS,tyS,kdS,rkS)
   = let val tyfixed_set = HOLset.addList(raw_empty_tyset, tyfixed)
         val (tmtheta,((_,_,pinsts_homs),kdS1,rkS1)) =
            RM [TMP (pat, ob)] ({ids = tmfixed, n = 0, theta = tmS,
                                 patbvars = empty_intsubst,
                                 obbvars = empty_intsubst},
                                ((tyfixed_set,[],(tyS,[])), (kdS,kdfixed), (rkS,rkfixed)))
         val tmS' = (#theta tmtheta, #ids tmtheta)
         val tyinsts = Type.type_homatch kdfixed tyfixed_set rkS1 kdS1 pinsts_homs
         val (_,tyS',kdS',rkS') = Type.separate_insts_ty false rkS1 kdfixed kdS1 [] tyinsts
         val tyId' = Lib.subtract (Lib.union (type_vars_in_term pat) tyfixed) (map #redex tyS')
     in (tmS',(tyS',tyId'),kdS',rkS')
     end;

fun raw_match tyfixed tmfixed pat ob (tmS,tyS)
   = let val (tmSId,tySId,(kdS,kdIds),(rkS,_)) = raw_kind_match false [] tyfixed tmfixed pat ob (tmS,tyS,[],0)
     in if null kdS andalso null kdIds andalso rkS = 0 then (tmSId,tySId)
        else raise ERR "raw_match" "kind and/or rank instantiation needed: use raw_kind_match instead"
     end;

(* val raw_match0 = raw_match
fun raw_match tyf tmf pat ob =
    Profile.profile "raw_match" (raw_match0 tyf tmf pat ob) *)

fun norm_subst ((tmS,_),(tyS,_)) =
 let val Theta = align_inst tyS
     fun del A [] = A
       | del A ({redex,residue}::rst) =
         del (let val redex' = Theta(redex)
              in if aconv residue redex' then A else (redex' |-> residue)::A
              end) rst
 in (del [] tmS,tyS)
 end

fun kind_norm_subst0 ((tmS,_),(tyS,_),(kdS,_),(rkS,_)) =
 let val Theta = pure_inst tyS
     fun del A [] = A
       | del A ({redex,residue}::rst) =
         del (let val redex' = Theta(redex)
              in if aconv residue redex' then A else (redex' |-> residue)::A
              end) rst
 in (del [] tmS, tyS, kdS, rkS)
 end

local
  val op :>=: = Kind.:>=:
  val op :=: = Kind.:=:
  infix :>=: :=:
in
fun kind_norm_subst (S as (_,_,([],_),(0,_))) = kind_norm_subst0 S
  | kind_norm_subst ((tmS,_),(tyS,_),(kdS,_),rk as (rkS,_)) =
 let val ((kdS',_),_) = Kind.norm_subst ((kdS,[]),rk)
     val kTheta = Type.inst_rank_kind (kdS',rkS)
     fun delty A [] = A
       | delty A ({redex,residue}::rst) =
         delty (let val redex' = kTheta(redex)
              in if residue = redex' then A
                 else (redex' |-> residue)::A
              end) rst
     val tyS' = delty [] tyS
     val Theta = inst_rk_kd_ty (tyS',kdS',rkS) (* pure_inst tyS' o inst_kind kdS' o inst_rank rkS *)
     fun del A [] = A
       | del A ({redex,residue}::rst) =
         del (let val redex' = Theta(redex)
              in if aconv residue redex' then A
                 else (redex' |-> residue)::A
              end) rst
 in (del [] tmS, tyS', kdS', rkS)
 end
end (* local *)

fun kind_match_terml rkfixed kdfixed tyfixed tmfixed pat ob =
 kind_norm_subst (raw_kind_match rkfixed kdfixed tyfixed tmfixed pat ob ([],[],[],0))

fun match_terml tyfixed tmfixed pat ob =
 let val (tmS,tyS,kdS,rkS) = kind_match_terml false [] tyfixed tmfixed pat ob
 in if null kdS andalso rkS = 0 then (tmS,tyS)
    else raise ERR "match_terml" "kind and/or rank instantiation needed: use kind_match_terml instead"
 end

val kind_match_term = kind_match_terml false [] [] empty_varset

fun match_term pat ob =
 let val (tmS,tyS,kdS,rkS) = kind_match_term pat ob
 in if null kdS andalso rkS = 0 then (tmS,tyS)
    else raise ERR "match_term" "kind and/or rank instantiation needed: use kind_match_term instead"
 end;

(*---------------------------------------------------------------------------
       Assistance for higher order matching of types within
       higher order matching of terms - most routines inside Kernel
 ---------------------------------------------------------------------------*)

local
fun tymatch pat ob ((lctys,env,insts_homs),kdS,rkS) =
        let val insts_homs' = Type.type_pmatch lctys env pat ob insts_homs
            val (kdS',rkS') = Type.get_rank_kind_insts [] env (fst insts_homs') (kdS,rkS)
        in ((lctys,env,insts_homs'),kdS',rkS')
        end
in
fun get_type_kind_rank_insts kdavoids tyavoids L ((tyS,tyId),(kdS,kdId),rk as (rkS,rkfixed)) =
  let val tyfixed = HOLset.addList(HOLset.addList(raw_empty_tyset, tyavoids), tyId)
      val kdfixed = union kdavoids kdId
      val ((_,_,pinsts_homs),kdS1,rkS1) =
          itlist (fn {redex,residue} => tymatch (snd(dest_var redex)) (type_of residue))
                 L ((tyfixed,[],(tyS,[])),(kdS,kdfixed),rk)
      val tyinsts = Type.type_homatch kdfixed tyfixed rkS1 kdS1 pinsts_homs
      val (_,tyS',kdS',rkS') = Type.separate_insts_ty false rkS1 kdfixed kdS1 [] tyinsts
  in ((tyS',tyId),kdS',rkS')
  end
end


fun size acc tlist =
    case tlist of
      [] => acc
    | t :: ts => let
      in
        case t of
          Var _ => size (1 + acc) ts
        | Const _ => size (1 + acc) ts
        | App(t1, t2) => size (1 + acc) (t1 :: t2 :: ts)
        | Abs(_, b) => size (1 + acc) (b :: ts)
        | TApp(t, _) => size (1 + acc) (t :: ts)
        | TAbs(_, b) => size (1 + acc) (b :: ts)
      end

fun term_size t = size 0 [t]




val imp = let
  val k = {Name = "==>", Thy = "min"}
in
  prim_new_const k (bool --> bool --> bool)
end

val equality = let
  val k = {Name = "=", Thy = "min"}
in
  prim_new_const k (alpha --> alpha --> bool)
end

val select = let
  val k = {Name = "@", Thy = "min"}
in
  prim_new_const k ((alpha --> bool) --> alpha)
end

local
  (* for HOL-Omega, PACK and UNPACK: *)
  val rty = mk_var_type("'r", typ 1)
  val aty = mk_var_type("'a", kappa ==> typ 1)
  val xty = mk_var_type("'x", kappa)
  val axty = mk_app_type(aty,xty)
  val ety = mk_exist_type(xty, axty)
  val pack_ty = mk_univ_type(xty, axty --> ety)
  val unpack_ty = mk_univ_type(xty, axty --> rty) --> ety --> rty
in

  val pack = let
    val k = {Name = "PACK", Thy = "min"}
  in
    prim_new_const k pack_ty
  end

  val unpack = let
    val k = {Name = "UNPACK", Thy = "min"}
  in
    prim_new_const k unpack_ty
  end

end (* local *)

fun dest_eq_ty t = let
  val (fx, y) = dest_comb t
  val (f, x) = dest_comb fx
in
  if same_const f equality then (x, y, type_of x)
  else raise ERR "dest_eq_ty" "Term not an equality"
end

fun prim_mk_eq ty t1 t2 =
  let val rk = rank_of_type ty
      val equality' =
            if rk = 0 then pure_inst [alpha |-> ty] equality
            else inst_rk_kd_ty ([Type.inst_rank rk alpha |-> ty], [], rk) equality
  in App(App(equality', t1), t2)
  end

(*val prim_mk_eq =
    (fn ty => fn t1 => Profile.profile "prim_mk_eq" (prim_mk_eq ty t1)) *)

fun prim_mk_imp t1 t2 = App(App(imp, t1), t2)

(* val prim_mk_imp = (fn t1 => Profile.profile "prim_mk_imp" (prim_mk_imp t1))*)


(*---------------------------------------------------------------------------*
 *  Raw syntax prettyprinter for terms.                                      *
 *---------------------------------------------------------------------------*)

val dot     = "."
val percent = "%";

fun pp_raw_term index pps tm =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     fun pp (Abs(Bvar,Body)) =
          ( add_string "\\\\(";
            pp Bvar; add_string ","; add_break(1,0);
            pp Body; add_string ")" )
      | pp (App(Rator,Rand)) =
         ( add_string "("; pp Rator; add_break(1,0);
                           add_string "& ";
                           pp Rand; add_string ")")
      | pp a      = add_string (percent^Lib.int_to_string (index a))
 in
   begin_block INCONSISTENT 0;
   pp tm;
   end_block()
 end;


local
datatype tok = bslash | fslash | colon | id of int | lparen | rparen
open StringCvt

fun readtok (c : (char, cs) reader) cs0 = let
  val cs = skipWS c cs0
  val intread = Int.scan DEC c
in
  case c cs of
    NONE => NONE
  | SOME (#"|",cs') => SOME (bslash,cs')
  | SOME (#"/",cs') => SOME (fslash,cs')
  | SOME (#":",cs') => SOME ( colon,cs')
  | SOME (#"(",cs') => SOME (lparen,cs')
  | SOME (#")",cs') => SOME (rparen,cs')
  | SOME c => (case intread cs of
                 NONE => NONE
               | SOME (i,cs') => SOME(id i, cs'))
end

(* SLR parser for grammar

     T   ::= tm $
     tm  ::= '|' [id] tm    -- abstraction
     tm  ::= '/' [id] tm    -- type abstraction
     tm  ::= ':' [id] tm    -- type combination ([id] refers to type which is the argument)
     tm  ::= tmc
     tmc ::= tmc tmb
     tmc ::= tmb
     tmb ::= [id]
     tmb ::= '(' tm ')'
*)

datatype stk_item = TYLAM of hol_type | TYC of hol_type | LAM of term | C of term | BK | Start

fun parse tyv tmv c cs0 = let
  fun adv cs = case readtok c cs of NONE => (NONE, cs)
                                  | SOME (t, cs') => (SOME t, cs')
  fun new_bv i stk = LAM (Vector.sub(tmv,i)) :: stk
  fun new_btyv i stk = TYLAM (Vector.sub(tyv,i)) :: stk
  fun new_tyarg i stk = TYC (Vector.sub(tyv,i)) :: stk
  fun parse_term stk cur =
      case cur of
        (NONE,_) => NONE
      | (SOME bslash, cs') => let
        in
          case readtok c cs' of
            NONE => NONE
          | SOME (id i, cs'') => parse_term (new_bv i stk) (adv cs'')
          | _ => NONE
        end
      | (SOME fslash, cs') => let
        in
          case readtok c cs' of
            NONE => NONE
          | SOME (id i, cs'') => parse_term (new_btyv i stk) (adv cs'')
          | _ => NONE
        end
      | (SOME colon, cs') => let
        in
          case readtok c cs' of
            NONE => NONE
          | SOME (id i, cs'') => parse_term (new_tyarg i stk) (adv cs'')
          | _ => NONE
        end
      | (SOME lparen, cs') => parse_term (BK :: stk) (adv cs')
      | (SOME (id i), cs') => reduce_tmb stk (Vector.sub(tmv,i)) (adv cs')
      | _ => raise Fail "parse failure 1 in RawParse.parse"
  and reduce_tmb stk tm cur =
      case stk of
        [] => NONE
      | C t :: rest => parse_tmc (C (mk_comb(t,tm)) :: rest) cur
      | TYC ty :: rest => parse_tmc (C (mk_tycomb(tm,ty)) :: rest) cur
      | _ => parse_tmc (C tm :: stk) cur
  and parse_tmc stk cur =
      case cur of
        (NONE, _) => reduce_tm stk cur
      | (SOME(id i), cs') => reduce_tmb stk (Vector.sub(tmv,i)) (adv cs')
      | (SOME lparen, cs') => parse_term (BK :: stk) (adv cs')
      | (SOME rparen, cs') => reduce_tm stk (adv cs')
      | _ => raise Fail "parse failure 2 in RawParse.parse"
  and reduce_tm stk cur =
      case stk of
        C t :: BK :: rest => reduce_tmb rest t cur
      | C t :: Start :: rest => SOME (t, #2 cur)
      | C t :: LAM bv :: rest => reduce_tm (C (mk_abs(bv,t)) :: rest) cur
      | C t :: TYLAM bv :: rest => reduce_tm (C (mk_tyabs(bv,t)) :: rest) cur
      | _ => raise Fail "parse failure 3 (reduce) in RawParse.parse"
in
  parse_term [Start] (adv cs0)
end


datatype grav = Top | CombL | CombR
datatype ppaction = Brk | Tm of term * grav | Ty of hol_type * grav | Stg of string

in

fun read_raw tyv tmv s = valOf (scanString (parse tyv tmv) s)
fun write_raw tymap map t = let
  fun doit acc actlist =
      case actlist of
        [] => String.concat (List.rev acc)
      | Brk :: rest => doit (" "::acc) rest
      | Stg s :: rest => doit (s::acc) rest
      | Ty (t,g) :: rest => let
        in
          doit (Int.toString (tymap t)::acc) rest
        end
      | Tm (t,g) :: rest => let
        in
          if is_var t orelse is_const t then
             doit (Int.toString (map t)::acc) rest
          else if is_comb t then let
              val (Rator,Rand) = dest_comb t
            in
              if g = CombR then
                doit acc
                     (Stg "(" :: Tm(Rator,CombL) :: Brk :: Tm(Rand,CombR) ::
                      Stg ")" :: rest)
              else
                doit acc (Tm(Rator,CombL) :: Brk :: Tm(Rand,CombR) :: rest)
            end
          else if is_abs t then let
              val (bv, body) = dest_abs t
              val core = [Stg "|", Tm(bv, Top), Brk, Tm(body, Top)]
            in
              if g <> Top then
                doit acc ((Stg "(" :: core) @ (Stg ")" :: rest))
              else
                doit acc (core @ rest)
            end
          else if is_tycomb t then let
              val (Rator,Rand) = dest_tycomb t
              val core = [Stg ":", Ty(Rand,CombL), Brk, Tm(Rator,CombR)]
            in
              if g = CombR then
                doit acc ((Stg "(" :: core) @ (Stg ")" :: rest))
              else
                doit acc (core @ rest)
            end
          else if is_tyabs t then let
              val (bv, body) = dest_tyabs t
              val core = [Stg "/", Ty(bv, Top), Brk, Tm(body, Top)]
            in
              if g <> Top then
                doit acc ((Stg "(" :: core) @ (Stg ")" :: rest))
              else
                doit acc (core @ rest)
            end
          else raise ERR "pp_raw_term" "unrecognized term"
        end
in
  doit [] [Tm(t,Top)]
end

end (* local *)


(*---------------------------------------------------------------------------
       Higher order matching (from jrh via Michael Norrish - June 2001)
       Modified to include kind variables by Peter Homeier - June 2009
 ---------------------------------------------------------------------------*)

local
  exception NOT_FOUND
  fun find_residue red [] = raise NOT_FOUND
    | find_residue red ({redex,residue}::rest) = if red = redex then residue
                                                 else find_residue red rest
  fun find_residue_ty red [] = raise NOT_FOUND
    | find_residue_ty red ({redex,residue}::rest) = if eq_ty red redex then residue
                                                    else find_residue_ty red rest
  fun find_residue_tm red [] = raise NOT_FOUND
    | find_residue_tm red ({redex,residue}::rest) = if aconv red redex then residue
                                                    else find_residue_tm red rest
  fun in_dom x [] = false
    | in_dom x ({redex,residue}::rest) = (x = redex) orelse in_dom x rest
  fun in_dom_ty x [] = false
    | in_dom_ty x ({redex,residue}::rest) = eq_ty x redex orelse in_dom_ty x rest
  fun in_dom_tm x [] = false
    | in_dom_tm x ({redex,residue}::rest) = aconv x redex orelse in_dom_tm x rest
  fun safe_insert (n as {redex,residue}) l = let
    val z = find_residue redex l
  in
    if residue = z then l
    else raise ERR "safe_insert" "match"
  end handle NOT_FOUND => n::l  (* binding not there *)
  (* safe_inserta is like safe_insert but specially for terms *)
  fun safe_inserta (n as {redex,residue}) l = let
    val z = find_residue_tm redex l
  in
    if aconv residue z then l
    else raise ERR "safe_inserta" "match"
  end handle NOT_FOUND => n::l
  (* safe_insertb is like safe_insert but specially for betacounts *)
  fun safe_insertb (n as {redex,residue}) l = let
    val z = find_residue_tm redex l
  in
    if residue = z then l
    else raise ERR "safe_insertb" "match"
  end handle NOT_FOUND => n::l
  (* safe_insert_ty is like safe_insert but specially for types *)
  fun safe_insert_ty (n as {redex,residue}) l = let
    val z = find_residue_ty redex l
  in
    if eq_ty residue z then l
    else raise ERR "safe_insert_ty" "match"
  end handle NOT_FOUND => n::l
  local
    val name = fst(dest_var(genvar Type.alpha))
    val tyname = #1(dest_var_type(gen_var_type(typ rho)))
  in
    fun mk_new_dummy ty =
       let val a = trace ("Vartype Format Complaint",0)
                             mk_var_type(tyname, kind_of ty)
           val ty' = mk_app_type(mk_abs_type(a, bool), ty)
       in mk_var(name, ty')
       end
    fun mk_dummy2 {redex,residue} =
       if is_type_kind (kind_of redex)
          (* keep as similar as possible to HOL4 dummies *)
       then (mk_var(name, redex) |-> mk_var(name, residue))
       else (mk_new_dummy redex  |-> mk_new_dummy residue )
    fun dest_dummy tm =
       let val (n,ty) = dest_var tm
           val _ = if name = n then () else raise ERR "dest_dummy" ""
       in let val (opr,arg) = dest_app_type ty
              val (a,body) = dest_abs_type opr
              val (s,kd) = dest_var_type a
              val _ = if tyname = s then () else raise ERR "dest_dummy" ""
          in arg
          end (* but if not the new kind of dummy, it's the old sort *)
          handle HOL_ERR _ => ty
       end handle HOL_ERR _ => raise ERR "dest_dummy" "not a dummy"
  end
  val mk_dummy_ty = let
    val name = dest_vartype(gen_tyvar())
  in fn kd => trace ("Vartype Format Complaint",0) mk_var_type(name, kd)
  end

  fun find_residue_dum red [] = raise NOT_FOUND
    | find_residue_dum red ({redex,residue}::rest) =
        (if eq_ty red (dest_dummy redex) then dest_dummy residue
         else find_residue_dum red rest)
        handle HOL_ERR _ => find_residue_dum red rest
  (* safe_insert_dummy is like safe_insert but specially for dummy terms *)
  fun safe_insert_dummy (n as {redex,residue}) l =
    let val z = find_residue_dum redex l
    in if eq_ty residue z then l
       else raise ERR "safe_insert_dummy" "match"
    end handle NOT_FOUND => mk_dummy2 n :: l


  fun term_pmatch lconsts tyenv env vtm ctm (sofar as (insts,homs)) =
    if is_var vtm then let
        val ctm' = find_residue_tm vtm env
      in
        if aconv ctm' ctm then sofar else raise ERR "term_pmatch" "variable double bind"
      end handle NOT_FOUND =>
                 if HOLset.member(lconsts, vtm) then
                   if aconv ctm vtm then sofar
                   else raise ERR "term_pmatch" "can't instantiate local constant"
                 else (safe_inserta (vtm |-> ctm) insts, homs)
    else if is_const vtm then let
        val {Thy = vthy, Name = vname, Ty = vty} = dest_thy_const vtm
        val {Thy = cthy, Name = cname, Ty = cty} = dest_thy_const ctm
      in
        if vname = cname andalso vthy = cthy then
          if eq_ty cty vty then sofar
          else (safe_insert_dummy (vty |-> cty) insts, homs)
        else raise ERR "term_pmatch" "constant mismatch"
      end
    else if is_abs vtm then let
        val (vv,vbod) = dest_abs vtm
        val (cv,cbod) = dest_abs ctm
        val (_, vty) = dest_var vv
        val (_, cty) = dest_var cv
        val sofar' = (safe_insert_dummy (vty |-> cty) insts, homs)
      in
        term_pmatch lconsts tyenv ((vv |-> cv)::env) vbod cbod sofar'
      end
    else if is_tyabs vtm then let
        val (vty,vbod) = dest_tyabs vtm
        val (cty,cbod) = dest_tyabs ctm
        val (_, vkd) = dest_var_type vty
        val (_, ckd) = dest_var_type cty
        val vdty = mk_dummy_ty vkd
        val cdty = mk_dummy_ty ckd
        val sofar' = (safe_insert_dummy (vdty |-> cdty) insts, homs)
      in
        term_pmatch lconsts ((vty |-> cty)::tyenv) env vbod cbod sofar'
      end
    else if is_comb vtm then let
        val vhop = repeat tyrator (repeat rator vtm)
      in
        if is_var vhop andalso not (HOLset.member(lconsts, vhop)) andalso
           not (in_dom_tm vhop env)
        then let
            val vty = type_of vtm
            val cty = type_of ctm
            val insts' = if eq_ty vty cty then insts
                         else safe_insert_dummy (vty |-> cty) insts
          in
            (insts', (tyenv,env,ctm,vtm)::homs)
          end
        else let
            val (lv,rv) = dest_comb vtm
            val (lc,rc) = dest_comb ctm
            val sofar' = term_pmatch lconsts tyenv env lv lc sofar
          in
            term_pmatch lconsts tyenv env rv rc sofar'
          end
      end
    else if is_tycomb vtm then let
        val vhop = repeat tyrator vtm
      in
        if is_var vhop andalso not (HOLset.member(lconsts, vhop)) andalso
           not (in_dom_tm vhop env)
        then let
            val vty = type_of vtm
            val cty = type_of ctm
            val insts' = if eq_ty vty cty then insts
                         else safe_insert_dummy (vty |-> cty) insts
          in
            (insts', (tyenv,env,ctm,vtm)::homs)
          end
        else let
            val (lv,rvty) = dest_tycomb vtm
            val (lc,rcty) = dest_tycomb ctm
            val sofar' = (safe_insert_dummy (rvty |-> rcty) insts, homs)
          in
            term_pmatch lconsts tyenv env lv lc sofar'
          end
      end
    else raise ERR "term_pmatch" "unrecognizable term"

(*
fun get_type_kind_rank_insts kdavoids tyavoids L ((tyS,tyId),(kdS,kdId),rkS) =
 itlist (fn {redex,residue} => fn Theta =>
          Type.prim_kind_match_type (snd(dest_var redex)) (type_of residue) Theta)
       L ((tyS,union tyavoids tyId),(kdS,union kdavoids kdId),rkS)
*)

fun separate_insts kdavoids tyavoids rkS kdS tyS insts = let
  val (realinsts, patterns) = partition (is_var o #redex) insts
  val betacounts =
      if null patterns then []
      else
        itlist (fn {redex = p,...} =>
                   fn sof => let
                        val (hop,args) = strip_comb p
                      in
                        safe_insertb (hop |-> length args) sof
                      end handle _ =>
                                 (HOL_WARNING "" ""
                                  "Inconsistent patterning in h.o. match";
                                  sof))
        patterns []
  val (tyins,kdins,rkin) = get_type_kind_rank_insts kdavoids tyavoids realinsts (tyS,kdS,rkS)
  val kdins' as (kdS',_) = fst (Kind.norm_subst (kdins,rkin))
  val inst_rk_kd = Type.inst_rank_kind (kdS', fst rkin)
  val tyinsts = mapfilter (fn {redex = x, residue = t} => let
                   val x' = inst_rk_kd x
                 in
                   if t = x' then raise ERR "separate_insts" ""
                             else {redex = x', residue = t}
                 end) (fst tyins)
  val tyins' = (tyinsts,snd tyins)
  val inst_rk_kd_ty = Type.inst_rk_kd_ty (tyinsts, kdS', fst rkin)
  val tminsts = mapfilter (fn {redex = x, residue = t} => let
                   val x' = let val (xn,xty) = dest_var x
                            in
                              mk_var(xn, inst_rk_kd_ty xty)
                            end
                 in
                   if aconv t x' then raise ERR "separate_insts" ""
                   else {redex = x', residue = t}
                 end) realinsts
  val _ = map (fn {redex = x, residue = t} =>
                   if eq_ty (type_of x) (type_of t) then ()
                   else raise ERR "separate_insts" "bad term subst: type mismatch" (* This covers an error in normal HOL *)
              ) tminsts
in
  (betacounts, tminsts, tyins', kdins', rkin)
end

fun tyenv_in_dom x (env, idlist) = op_mem eq_ty x idlist orelse in_dom_ty x env
fun tyenv_find_residue x (env, idlist) = if op_mem eq_ty x idlist then x
                                         else find_residue x env
fun tyenv_safe_insert (t as {redex,residue}) (E as (env, idlist)) = let
  val existing = tyenv_find_residue redex E
in
  if eq_ty existing residue then E else raise ERR "tyenv_safe_insert" "Type bindings clash"
end handle NOT_FOUND => if eq_ty redex residue then (env, redex::idlist)
                        else (t::env, idlist)

fun beta_normalise0 t = let
  val bn0 = beta_normalise0
  fun bn1 t = case bn0 t of NONE => SOME t | x => x
in
  case t of
    App(t1,t2) => let
(*case dest_term t of
    COMB(t1,t2) => let *)
    in
      case Lib.total beta_conv t of
        NONE => let
        in
          case bn0 t1 of
            NONE => Option.map (fn t2' => mk_comb(t1,t2')) (bn0 t2)
          | SOME t1' => bn1 (mk_comb(t1',t2))
        end
      | SOME t' => bn1 t'
    end
(*
  | TYCOMB(tm,ty) => Option.map (fn tm' => mk_tycomb(tm',ty)) (bn0 tm)
  | LAMB(v,t) => Option.map (fn t' => mk_abs(v,t')) (bn0 t)
  | TYLAM(a,t) => Option.map (fn t' => mk_tyabs(a,t')) (bn0 t)
*)
  | TApp(t,ty) => Option.map (fn t' => TApp(t',ty)) (bn0 t)
  | Abs _ => let
      val (v,t) = dest_abs t
    in
      Option.map (fn t' => mk_abs(v,t')) (bn0 t)
    end
  | TAbs _ => let
      val (a,t) = dest_tyabs t
    in
      Option.map (fn t' => mk_tyabs(a,t')) (bn0 t)
    end
  | x => NONE
end

fun beta_normalise t = case beta_normalise0 t of NONE => t | SOME x => x

fun all_abconv [] [] = true
  | all_abconv [] _ = false
  | all_abconv _ [] = false
  | all_abconv (h1::t1) (h2::t2) =
     aconv (beta_normalise h1) (beta_normalise h2) andalso all_abconv t1 t2

fun all_eq_ty [] [] = true
  | all_eq_ty [] _ = false
  | all_eq_ty _ [] = false
  | all_eq_ty (h1::t1) (h2::t2) = eq_ty h1 h2 andalso all_eq_ty t1 t2

fun determ {redex,residue} =
      if not (is_var redex) orelse not (is_var residue) then NONE
      else let val (nm1,ty1) = dest_var redex
               val (nm2,ty2) = dest_var residue
           in if nm1 <> nm2 then NONE
              else if is_vartype ty1
                   then SOME (ty1 |-> ty2)
                   else NONE
           end


fun term_homatch kdavoids tyavoids lconsts rkin kdins tyins (insts, homs) = let
  (* local constants of both terms and types never change *)
  val term_homatch = term_homatch kdavoids tyavoids lconsts
in
  if null homs then insts
  else let
      val (tyenv,env,ctm,vtm) = hd homs
    in
      if is_var vtm then
        if aconv ctm vtm then term_homatch rkin kdins tyins (insts, tl homs)
        else let
            (* val (newtyins,newkdins,newrkin) =
                Type.prim_kind_match_type (snd (dest_var vtm)) (type_of ctm) (tyins,kdins,rkin) *)
            val newtyins =
                tyenv_safe_insert (snd (dest_var vtm) |-> type_of ctm) tyins
            val newinsts = (vtm |-> ctm)::insts
          in
            term_homatch rkin kdins newtyins (newinsts, tl homs)
          end
      else if is_comb vtm then let
          val (vtm0, vargs) = strip_comb vtm
          val (vhop, vtyargs) = strip_tycomb vtm0
          val afvs = free_varsl vargs
          val aftyvs = type_varsl vtyargs
          val ((kdins',_),(rkin',_)) = Kind.norm_subst(kdins,rkin)
          val tyins' = map (fn {redex,residue} => Type.inst_rank_kind (kdins',rkin') redex |-> residue)
                           (fst tyins)
          val inst_fn = inst_rk_kd_ty (tyins',kdins',rkin')
          val ty_inst_fn = Type.inst_rk_kd_ty (tyins',kdins',rkin')
          val ty_insts = List.mapPartial determ insts
        in
          (let
             val tyins1 =
                 map (fn a =>
                         (ty_inst_fn a |->
                                  (find_residue_ty a tyenv
                                   handle _ =>
                                          find_residue_ty a (fst tyins)
                                   handle _ =>
                                          find_residue_ty a ty_insts
                                   handle _ =>
                                          if mem a tyavoids orelse mem a (snd tyins)
                                          then a
                                          else raise ERR "term_homatch" ""))) aftyvs
             val tmins =
                 map (fn a =>
                         (inst_fn a |->
                                  (find_residue_tm a env
                                   handle _ =>
                                          find_residue_tm a insts
                                   handle _ =>
                                          if HOLset.member(lconsts, a)
                                          then a
                                          else raise ERR "term_homatch" ""))) afvs
             val typats0 = map ty_inst_fn vtyargs
             val typats = map (Type.pure_type_subst tyins1) typats0
             val pats0 = map inst_fn vargs
             val pats = map (subst tmins) pats0
             val vhop' = inst_fn vhop
             val ictm = list_mk_comb(list_mk_tycomb(vhop', typats), pats)
             val ni = let
               val (ctm0,cargs) = strip_comb ctm
               val (chop,ctyargs) = if null typats then (ctm0,[]) else strip_tycomb ctm0
             in
               if all_eq_ty ctyargs typats andalso all_abconv cargs pats then
                 if aconv chop vhop then insts
                 else safe_inserta (vhop |-> chop) insts
               else let
                   val gtyinsts = map (fn p => (p |->
                                                  (if is_vartype p then p
                                                   else gen_var_type(kind_of p))))
                                      typats
                   val ginsts   = map (fn p => (p |->
                                                  (if is_var p then p
                                                   else genvar(type_of p))))
                                      pats
                   val ctm' = pure_inst gtyinsts (subst ginsts ctm)
                   val gtyvs = map #residue gtyinsts
                   val gvs = map #residue ginsts
                   val abstm = list_mk_tyabs(gtyvs,list_mk_abs(gvs,ctm'))
                   val vinsts = safe_inserta (vhop |-> abstm) insts
                   val icpair = (list_mk_comb(list_mk_tycomb(vhop',gtyvs),gvs) |-> ctm')
                 in
                   icpair::vinsts
                 end
             end
           in
             term_homatch rkin kdins tyins (ni,tl homs)
           end) handle _ => let
                         val (lc,rc) = dest_comb ctm
                         val (lv,rv) = dest_comb vtm
                         val pinsts_homs' =
                             term_pmatch lconsts tyenv env rv rc
                                         (insts, (tyenv,env,lc,lv)::(tl homs))
                         val (tyins',kdins',rkin') =
                             get_type_kind_rank_insts kdavoids tyavoids
                                                 (fst pinsts_homs')
                                                 (([], []), ([], []), (0, false))
                       in
                         term_homatch rkin' kdins' tyins' pinsts_homs'
                       end
        end
      else (* if is_tycomb vtm then *) let
          val (vhop, vtyargs) = strip_tycomb vtm
          val aftyvs = type_varsl vtyargs
          val ((kdins',_),(rkin',_)) = Kind.norm_subst(kdins,rkin)
          val tyins' = map (fn {redex,residue} => Type.inst_rank_kind (kdins',rkin') redex |-> residue)
                           (fst tyins)
          val inst_fn = inst_rk_kd_ty (tyins',kdins',rkin')
          val ty_inst_fn = Type.inst_rk_kd_ty (tyins',kdins',rkin')
          val ty_insts = List.mapPartial determ insts
        in
          (let
             val tyins1 =
                 map (fn a =>
                         (ty_inst_fn a |->
                                  (find_residue_ty a tyenv
                                   handle _ =>
                                          find_residue_ty a (fst tyins)
                                   handle _ =>
                                          find_residue_ty a ty_insts
                                   handle _ =>
                                          if mem a tyavoids orelse mem a (snd tyins)
                                          then a
                                          else raise ERR "term_homatch" ""))) aftyvs
             val typats0 = map ty_inst_fn vtyargs
             val typats = map (Type.pure_type_subst tyins1) typats0
             val vhop' = inst_fn vhop
             val ictm = list_mk_tycomb(vhop', typats)
             val ni = let
               val (chop,ctyargs) = strip_tycomb ctm
             in
               if all_eq_ty ctyargs typats then
                 if aconv chop vhop then insts
                 else safe_inserta (vhop |-> chop) insts
               else let
                   val gtyinsts = map (fn p => (p |->
                                                  (if is_vartype p then p
                                                   else gen_var_type(kind_of p))))
                                      typats
                   val ctm' = pure_inst gtyinsts ctm
                   val gtyvs = map #residue gtyinsts
                   val tyabstm = list_mk_tyabs(gtyvs,ctm')
                   val vinsts = safe_inserta (vhop |-> tyabstm) insts
                   val icpair = (list_mk_tycomb(vhop',gtyvs) |-> ctm')
                 in
                   icpair::vinsts
                 end
             end
           in
             term_homatch rkin kdins tyins (ni,tl homs)
           end) handle _ => let
                         val (lc,rcty) = dest_tycomb ctm
                         val (lv,rvty) = dest_tycomb vtm
                         val insts' = safe_insert_dummy (rvty |-> rcty) insts
                         val pinsts_homs' =
                             term_pmatch lconsts tyenv env lv lc (insts', tl homs)
                         val (tyins',kdins',rkin') =
                             get_type_kind_rank_insts kdavoids tyavoids
                                                 (fst pinsts_homs')
                                                 (([], []), ([], []), (0, false))
                       in
                         term_homatch rkin' kdins' tyins' pinsts_homs'
                       end
        end
    end
end

in

fun ho_kind_match_term0 kdavoids tyavoids lconsts vtm ctm = let
  val pinsts_homs = term_pmatch lconsts [] [] vtm ctm ([], [])
  val (tyins,kdins,rkin) = get_type_kind_rank_insts kdavoids tyavoids (fst pinsts_homs) (([],[]),([],[]),(0,false))
  val insts = term_homatch kdavoids tyavoids lconsts rkin kdins tyins pinsts_homs
in
  separate_insts kdavoids tyavoids rkin kdins tyins insts
end

fun ho_match_term0 tyavoids lconsts vtm ctm = let
  val pinsts_homs = term_pmatch lconsts [] [] vtm ctm ([], [])
  val (tyins,kdins,rkin) = get_type_kind_rank_insts [] tyavoids (fst pinsts_homs) (([],[]),([],[]),(0,false))
  val insts = term_homatch [] tyavoids lconsts rkin kdins tyins pinsts_homs
  val (bcs,tmins,tyins,kdins,rkin) = separate_insts [] tyavoids rkin kdins tyins insts
in
  (bcs,tmins,tyins)
end

fun ho_kind_match_term kdavoids tyavoids lconsts vtm ctm = let
  val (bcs, tmins, tyins, kdins, rkin) = ho_kind_match_term0 kdavoids tyavoids lconsts vtm ctm
in
  (tmins, #1 tyins, #1 kdins, #1 rkin)
end handle e => raise (wrap_exn "HolKernel" "ho_kind_match_term" e)

fun ho_match_term tyavoids lconsts vtm ctm = let
  val (bcs, tmins, tyins) = ho_match_term0 tyavoids lconsts vtm ctm
in
  (tmins, #1 tyins)
end handle e => raise (wrap_exn "HolKernel" "ho_match_term" e)

end (* local *)

end (* struct *)
