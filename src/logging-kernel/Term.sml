structure Term :> Term =
struct

open Feedback Lib Type

infixr --> |->

val ERR = mk_HOL_ERR "Term"
val WARN = HOL_WARNING "Term"

(* used internally to avoid term rebuilding during substitution and
   type instantiation *)
exception Unchanged

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
              | App of term * term
              | Const of const_info
              | Abs of term * term

fun prim_new_const (k as {Thy,Name}) ty = let
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


fun type_of t = let
  fun ty_of t k =
      case t of
        Var(_, ty) => k ty
      | App(t1, t2) => ty_of t1 (fn ty => k (#2 (dom_rng ty)))
      | Const(_, ty) => k ty
      | Abs(Var(_, ty1), t) => ty_of t (fn tty => k (ty1 --> tty))
      | _ => raise Fail "Catastrophic invariant failure"
in
  ty_of t Lib.I
end


(* discriminators *)
fun is_var (Var _) = true | is_var _ = false
fun is_const (Const _) = true | is_const _ = false
fun is_abs (Abs _) = true | is_abs _ = false
fun is_comb (App _) = true | is_comb _ = false

fun same_const t1 t2 =
    case (t1, t2) of
      (Const(r1, _), Const(r2, _)) => r1 = r2
    | _ => false

(* constructors - variables *)
val mk_var = Var
fun mk_primed_var (Name,Ty) =
  let val next = Lexis.nameStrm Name
      fun spin s = if inST s then spin (next()) else s
  in mk_var(spin Name, Ty)
  end;

local val genvar_prefix = "%%genvar%%"
      fun num2name i = genvar_prefix^Lib.int_to_string i
      val nameStrm = Lib.mk_istream (fn x => x+1) 0 num2name
in
fun genvar ty = Var(state(next nameStrm), ty)

fun genvars ty =
 let fun gen acc n = if n <= 0 then rev acc else gen (genvar ty::acc) (n-1)
 in gen []
 end

fun is_genvar (Var(Name,_)) = String.isPrefix genvar_prefix Name
  | is_genvar _ = false;
end;

(* constructors - constants *)
fun mk_const(s, ty) =
    case prim_decls s of
      [] => raise ERR "mk_const" ("No constant with name "^s)
    | [(_, (id,basety))] => if can (match_type basety) ty then
                         Const (id, ty)
                       else raise ERR "mk_const"
                                      ("Not a type instance: "^c2string id)
    | (_, (id,basety))::_ =>
         if can (match_type basety) ty then
           (WARN "mk_const" (s^": more than one possibility"); Const (id,ty))
         else raise ERR "mk_const" ("Not a type instance: "^ c2string id)

fun prim_mk_const (k as {Thy, Name}) =
    case KernelSig.peek(const_table, k) of
      NONE => raise ERR "prim_mk_const" ("No such constant: "^id2string k)
    | SOME x => Const x

fun mk_thy_const {Thy,Name,Ty} = let
  val k = {Thy = Thy, Name = Name}
in
  case KernelSig.peek(const_table, k) of
    NONE => raise ERR "mk_thy_const" ("No such constant: "^id2string k)
  | SOME (id,basety) => if can (match_type basety) Ty then
                          Const(id, Ty)
                        else raise ERR "mk_thy_const"
                                       ("Not a type instance: "^id2string k)
end

(* constructors - applications *)
local val INCOMPAT_TYPES  = Lib.C ERR "incompatible types"
      fun lmk_comb err =
        let fun loop (A,_) [] = A
              | loop (A,typ) (tm::rst) =
                 let val (ty1,ty2) = with_exn Type.dom_rng typ err
                 in if type_of tm = ty1
                    then loop(App(A,tm),ty2) rst
                    else raise err
                 end
        in fn (f,L) => loop(f, type_of f) L
        end
      val lmk_comb = (fn err => (* Profile.profile "lmk_comb" *)(lmk_comb err))
      val mk_comb0 = lmk_comb (INCOMPAT_TYPES "mk_comb")
in

fun mk_comb(r as (Abs(Var(_,Ty),_), Rand)) =
      if type_of Rand = Ty then App r else raise INCOMPAT_TYPES "mk_comb"
  | mk_comb(Rator,Rand) = mk_comb0 (Rator,[Rand])

val list_mk_comb = lmk_comb (INCOMPAT_TYPES "list_mk_comb")
end;


(* constructors - abstractions *)
fun mk_abs(v, body) =
    if is_var v then Abs(v, body)
    else raise ERR "mk_abs" "Arg 1 not a variable"


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

(* free variable calculations *)

fun var_compare p =
    case p of
      (Var(s1, ty1), Var(s2, ty2)) => let
      in
        case String.compare(s1, s2) of
          EQUAL => Type.compare(ty1, ty2)
        | x => x
      end
    | _ => raise ERR "var_compare" "variables required"

val empty_varset = HOLset.empty var_compare

local
fun FV (v as Var _) A k = k (Lib.insert v A)
  | FV (App(f, x)) A k = FV f A (fn q => FV x q k)
  | FV (Abs(v, bdy)) A k =
    if mem v A then FV bdy A k
    else FV bdy A (fn q => k (Lib.set_diff q [v]))
  | FV _ A k = k A
in
fun free_vars tm = FV tm [] Lib.I
end

fun free_vars_lr tm = let
  fun FV (v as Var _) A = Lib.insert v A
    | FV (App(f, x)) A = FV x (FV f A)
    | FV (Abs(v, body)) A = if Lib.mem v A
                            then FV body A
                            else Lib.set_diff (FV body A) [v]
    | FV _ A = A
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
      end
    | DELvar v :: ts => FVL0 ts (safe_delete(acc, v))

fun FVL tlist = FVL0 (map FVTM tlist)


local
  fun vars (v as Var _) A = Lib.insert v A
    | vars (App(f, x)) A = vars x (vars f A)
    | vars (Abs(v, bdy)) A = vars bdy (vars v A)
    | vars _ A = A
in
fun all_vars tm = vars tm []
end

fun free_varsl tm_list = itlist (union o free_vars) tm_list []
fun all_varsl tm_list = itlist (union o all_vars) tm_list []

(* term comparison *)
structure Map = Binarymap
val empty_env = Map.mkDict var_compare
fun compare p = let
  open Map
  fun cmp n (E as (env1, env2)) p =
      if n = 0 andalso Portable.pointer_eq p then EQUAL
      else
        case p of
          (v1 as Var _, v2 as Var _) => let
          in
            case (peek(env1, v1), peek(env2, v2)) of
              (NONE, NONE) => var_compare(v1, v2)
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
              EQUAL => Type.compare(ty1, ty2)
            | x => x
          end
        | (Const _, _) => LESS
        | (_, Const _) => GREATER
        | (App(M, N), App(P, Q)) => let
          in
            case cmp n E (M, P) of
              EQUAL => cmp n E (N, Q)
            | x => x
          end
        | (App _, Abs _) => LESS
        | (Abs _, App _) => GREATER
        | (Abs(v1, bdy1), Abs(v2, bdy2)) => let
          in
            case Type.compare(type_of v1, type_of v2) of
              EQUAL => cmp (n + 1) (insert(env1, v1, n), insert(env2, v2, n))
                           (bdy1, bdy2)
            | x => x
          end
in
  cmp 0 (empty_env, empty_env) p
end

val empty_tmset = HOLset.empty compare

(* ----------------------------------------------------------------------
    All "atoms" (variables (bound or free) and constants).

    Does not respect alpha-equivalence
   ---------------------------------------------------------------------- *)

fun all_atomsl tlist A =
    case tlist of
        [] => A
      | t::ts =>
        let
        in
          case t of
              Var _ => all_atomsl ts (HOLset.add(A,t))
            | Const _ => all_atomsl ts (HOLset.add(A,t))
            | App(Rator,Rand) => all_atomsl (Rator::Rand::ts) A
            | Abs(v,body) => all_atomsl (body::ts) (HOLset.add(A,v))
        end

fun all_atoms t = all_atomsl [t] empty_tmset


fun aconv t1 t2 = compare(t1, t2) = EQUAL

val term_eq = aconv

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
in
  recurse N
end

fun var_occurs M = let
  val v = case M of
            Var v => v
          | _ => raise ERR "var_occurs" "Term not a variable"
  fun occ (Var u) = (v = u)
    | occ (Const _) = false
    | occ (App(f, x)) = occ f orelse occ x
    | occ (Abs(Var u, body)) = u <> v andalso occ body
    | occ (Abs _) = raise Fail "catastrophic invariant failure"
in
  occ
end

fun type_vars_in_term t = let
  fun tyv t k =
      case t of
        Var(_, ty) => k (Type.type_vars ty)
      | Const(_, ty) => k (Type.type_vars ty)
      | App(f, x) => tyv f (fn fq => tyv x (fn xq => k (union fq xq)))
      | Abs(x, b) => tyv x (fn xq => tyv b (fn bq => k (union xq bq)))
in
  tyv t Lib.I
end

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

(* jrh's caml light HOL Light code
let vsubst =
  let mk_qcomb = qcomb(fun (x,y) -> Comb(x,y)) in
  let rec vsubst theta tm =
    match tm with
      Var(_,_)  -> (try snd(rev_assoc tm theta)
                    with Failure _ -> raise Unchanged)
    | Const(_,_) -> raise Unchanged
    | Comb(f,x) -> mk_qcomb (vsubst theta) (f,x)
    | Abs(_,_) -> fst(vasubst theta tm)
  and vasubst theta tm =
    match tm with
      Var(_,_)  -> (try snd(rev_assoc tm theta),[tm]
                  with Failure _ -> raise Unchanged)
    | Const(_,_) -> raise Unchanged
    | Comb(l,r) -> (try let l',vs = vasubst theta l in
                        try let r',vt = vasubst theta r in
                            Comb(l',r'),union vs vt
                        with Unchanged -> Comb(l',r),vs
                    with Unchanged ->
                        let r',vt = vasubst theta r in Comb(l,r'),vt)
    | Abs(v,bod) -> let theta' = filter (prefix<> v o snd) theta in
                    if theta' = [] then raise Unchanged else
                    let bod',vs = vasubst theta' bod in
                    let tms = map
                      (eval o fst o C rev_assoc theta') vs in
                    if exists (mem v) tms then
                      let fvs = itlist union tms (subtract (frees bod) vs) in
                      let v' = variant fvs v in
                      let bod',vars' = vasubst
                        (((eager [v'],v'),v)::theta') bod in
                      Abs(v',bod'),subtract vars' [v]
                    else
                      Abs(v,bod'),vs in
  fun theta ->
    if theta = [] then (fun tm -> tm) else
    let atheta = map
      (fun (t,x) -> if type_of t = snd(dest_var x)
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


local
  open Map

  datatype fvinfo = FVI of { current : term HOLset.set,
                             is_full : bool,
                             left : fvinfo option, (* also used for Abs *)
                             right : fvinfo option }
  fun leaf (s, b) =
    FVI {current = s, is_full = b, left = NONE, right = NONE}
  fun current (FVI r) = #current r
  fun is_full (FVI r) = #is_full r
  fun left (FVI r) = valOf (#left r)
  fun right (FVI r) = valOf (#right r)
  (* computes a tree with information about the set of free variables in tm,
     returns early when all redexes in theta have become bound *)
  fun calculate_fvinfo theta_opt tm =
      case tm of
        Var _ => leaf (HOLset.singleton var_compare tm, true)
      | Const _ => leaf (empty_varset, true)
      | App (f, x) =>
        let
          val fvs = calculate_fvinfo theta_opt f
          val xvs = calculate_fvinfo theta_opt x
        in
          FVI {current = HOLset.union (current fvs, current xvs),
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
            leaf (empty_varset, false)
          else
            let
              val bodyvs = calculate_fvinfo theta'_opt body
            in
              FVI {current = safe_delete (current bodyvs, v),
                   is_full = is_full bodyvs,
                   left = SOME bodyvs, right = NONE}
            end
        end
  (* expands a (possibly partial) tree with information about the set of free
     variables in tm into a tree with full information *)
  fun expand_partial_fvinfo tm fvi =
    if is_full fvi then
      raise Unchanged
    else
      case tm of
        App (f, x) =>
          qcomb2 (fn (fvs, xvs) =>
              FVI {current = HOLset.union (current fvs, current xvs),
                   is_full = true,
                   left = SOME fvs, right = SOME xvs})
            (expand_partial_fvinfo f, expand_partial_fvinfo x)
            (left fvi, right fvi)
      | Abs (v, body) =>
          let
            val bodyvs = expand_partial_fvinfo body (left fvi)
              handle Option => calculate_fvinfo NONE body
          in
            FVI {current = safe_delete (current bodyvs, v),
                 is_full = true,
                 left = SOME bodyvs, right = NONE}
          end
      | _ => raise Fail "expand_partial_fvinfo: catastrophic invariant failure"

  fun filtertheta theta fvset = let
    (* Removes entries in theta for things not in fvset.  theta likely to
       be much smaller than fvset, so fold over that rather than the
       other *)
    fun foldthis (k,v,acc) = if HOLset.member(fvset, k) then insert(acc, k, v)
                             else acc
  in
    foldl foldthis emptyvsubst theta
  end

  fun augvsubst theta fvi tm =
      case tm of
        Var _ => (case peek (theta, tm) of NONE => raise Unchanged
                                         | SOME (_, t) => t)
      | Const _ => raise Unchanged
      | App p => qcomb2 App
          (augvsubst theta (left fvi), augvsubst theta (right fvi)) p
      | Abs (v, body) => let
          val theta' = #1 (remove (theta, v)) handle NotFound => theta
          val _ = if numItems theta' = 0 then raise Unchanged else ()
          val (vname, vty) = dest_var v
          val currentfvs = current fvi
          val body_fvi = left fvi
          (* first calculate the new names we are about to introduce into
             the term *)
          fun foldthis (k, v, acc) =
              if HOLset.member (currentfvs, k) then
                HOLset.union (acc, Susp.force (#1 v))
              else acc
          val newnames = foldl foldthis empty_stringset theta'
        in
          if HOLset.member (newnames, vname) then
            let
              (* now need to vary v, avoiding both newnames, and also the
                 existing free-names of the whole term. *)
              val body_fvi = expand_partial_fvinfo body body_fvi
                handle Unchanged => body_fvi
              val bodyfvs = current body_fvi
              fun foldthis (fv, acc) = HOLset.add (acc, #1 (dest_var fv))
              val allfreenames = HOLset.foldl foldthis newnames bodyfvs
              val new_vname = set_name_variant allfreenames vname
              val new_v = mk_var (new_vname, vty)
              val new_theta =
                if HOLset.member (bodyfvs, v) then
                  let
                    val singleton = HOLset.singleton String.compare new_vname
                  in
                    insert (theta', v,
                      (Susp.delay (fn () => singleton), new_v))
                  end
                else theta'
            in
              Abs (new_v, augvsubst new_theta body_fvi body)
            end
          else
            Abs (v, augvsubst theta' body_fvi body)
        end

  fun vsubst theta tm =
      case tm of
        Var _ => (case peek(theta, tm) of NONE => raise Unchanged
                                        | SOME (_, t) => t)
      | Const _ => raise Unchanged
      | App p  => qcomb App (vsubst theta) p
      | Abs _ => let
          val fvi = calculate_fvinfo (SOME theta) tm
          val theta' = filtertheta theta (current fvi)
        in
          if numItems theta' = 0 then raise Unchanged
          else augvsubst theta' fvi tm
        end

  fun ssubst theta t =
      (* only used to substitute in fresh variables (genvars), so no
         capture check -- potentially incorrect (because there is no
         guarantee that genvars are actually fresh) *)
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
            | _ => raise Unchanged
          end

  fun vsubst_insert (map, k, v) =
      insert (map, k, (Susp.delay (fn () => free_names v), v))
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
          val _ = type_of redex = type_of residue
                  orelse raise ERR "vsubst" "Bad substitution list"
        in
          if redex = residue then acc
          else vsubst_insert (acc, redex, residue)
        end
        val atheta = List.foldl foldthis emptyvsubst theta
      in
        if numItems atheta = 0 then I
        else (fn tm => vsubst atheta tm handle Unchanged => tm)
      end
    else let
        fun foldthis ({redex,residue}, (theta1, theta2)) = let
          val _ = type_of redex = type_of residue
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
  fun inst1 theta ctxt t =
      case t of
        (c as Const(r, ty)) => (case ty_sub theta ty of
                                  SAME => raise Unchanged
                                | DIFF ty => Const(r, ty))
      | (v as Var(name,ty0)) => let
          val (changed, nv) = case ty_sub theta ty0 of
                                  SAME => (false, v)
                                | DIFF ty => (true, Var(name, ty))
        in
          case Map.peek (ctxt, nv) of
                SOME oldtype => if oldtype = ty0 then ()
                                else raise NeedToRename nv
              | NONE => ();
          if changed then nv
          else raise Unchanged
        end
      | App p => qcomb App (inst1 theta ctxt) p
      | Abs (v as Var(n, ty), body) => let
        in
          let
            val (changed, v') = case ty_sub theta ty of
                                  SAME => (false, v)
                                | DIFF ty' => (true, Var(n, ty'))
          in let
               val body' = SOME (inst1 theta (Map.insert(ctxt,v',ty)) body)
                           handle Unchanged => NONE
             in
               case (body', changed) of
                 (SOME t, _) => Abs(v', t)
               | (NONE, true) => Abs(v', body)
               | (NONE, false) => raise Unchanged
             end handle e as NeedToRename v'' =>
                     if v' = v'' then let
                         val free_names = free_names t
                         val new_name = set_name_variant free_names n
                         val newv = Var(new_name, ty)
                       in
                         inst1 theta ctxt (Abs(newv, subst [v |-> newv] body))
                       end
                     else raise e
          end
        end
      | Abs _ => raise Fail "inst1: catastrophic invariant failure!"
in

fun inst [] tm = tm
  | inst theta tm = inst1 theta (Map.mkDict compare) tm handle Unchanged => tm
end

val inst : (hol_type, hol_type) Lib.subst -> term -> term = inst


local
  val FORMAT = ERR "list_mk_binder"
   "expected first arg to be a constant of type :(<ty>_1 -> <ty>_2) -> <ty>_3"
  fun check_opt NONE = Lib.I
    | check_opt (SOME c) =
      if not(is_const c) then raise FORMAT
      else case total (fst o Type.dom_rng o fst o Type.dom_rng o type_of) c of
             NONE => raise FORMAT
           | SOME ty => (fn abs =>
                            let val dom = fst(Type.dom_rng(type_of abs))
                            in mk_comb (inst[ty |-> dom] c, abs)
                            end)
in
fun list_mk_binder binder = let
  val f = check_opt binder
  (* As of Mosml2.00, List.foldr is clearly not tail recursive, and you can
     blow the stack with big lists here.  Thus, the reversing of the list and
     the use of foldl instead, relying on the fact that it's hard to imagine
     not writing foldl tail-recursively *)
in
  fn (vlist, tm) => List.foldl (f o mk_abs) tm (List.rev vlist)
end
end (* local *)

val list_mk_abs = list_mk_binder NONE


fun beta_conv (App (Abs (v, body), x)) =
  if x = v then body else subst [v |-> x] body
  | beta_conv (App _) =
  raise ERR "beta_conv" "LHS not an abstraction"
  | beta_conv _ =
  raise ERR "beta_conv" "Term not an application"

val lazy_beta_conv = beta_conv

fun eta_conv (Abs (x, App (f, x'))) =
  if x = x' andalso not (free_in x f) then
    f
  else raise ERR "eta_conv" "Term not an eta-redex"
  | eta_conv _ =
  raise ERR "eta_conv" "Term not an eta-redex"


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



(* ----------------------------------------------------------------------
    Matching
   ---------------------------------------------------------------------- *)

fun lookup x ids = let
  fun look [] = if HOLset.member(ids, x) then SOME x else NONE
    | look ({redex,residue}::t) = if x = redex then SOME residue else look t
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

fun RM patobs (theta0 as (tminfo, tyS)) =
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
                              NONE => if v = tm then add_id v tminfo
                                      else add_binding v tm tminfo
                            | SOME tm' => if aconv tm' tm then tminfo
                                          else MERR "double bind"),
                           Type.raw_match_type ty (type_of tm) tyS)
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
          else RM rest (tminfo, Type.raw_match_type ty1 ty2 tyS)
        | (App(f1, x1), App(f2, x2)) =>
          RM (TMP (f1, f2) :: TMP (x1, x2) :: rest) theta0
        | (Abs(x1, bdy1), Abs(x2, bdy2)) => let
            val tyS' = Type.raw_match_type (type_of x1) (type_of x2) tyS
            val {ids, patbvars, obbvars, n, theta} = tminfo
          in
            RM (TMP (bdy1, bdy2) ::
                BVrestore {patbvars = patbvars, obbvars = obbvars, n = n} ::
                rest)
               ({ids = #ids tminfo, n = n + 1, theta = theta,
                 patbvars = Map.insert(patbvars, x1, n),
                 obbvars = Map.insert(obbvars, x2, n)}, tyS')
          end
        | _ => MERR "Incompatible term types"
      end
    | BVrestore{patbvars, obbvars, n} :: rest => let
        val {ids, theta, ...} = tminfo
      in
        RM rest ({ids = ids, theta = theta, patbvars = patbvars,
                  obbvars = obbvars, n = n}, tyS)
      end

(* tyfixed: list of type variables that mustn't be instantiated
   tmfixed: set of term variables that mustn't be instantiated
   pat    : term "pattern" to match
   theta0 : an existing matching
*)

fun postRM (tmtheta : tminfo, tyS) = ((#theta tmtheta, #ids tmtheta), tyS)

val empty_intsubst = Map.mkDict compare

fun raw_match tyfixed tmfixed pat ob (tmS, tyS) =
    postRM (RM [TMP (pat, ob)] ({ids = tmfixed, n = 0, theta = tmS,
                                 patbvars = empty_intsubst,
                                 obbvars = empty_intsubst},
                                (tyS, tyfixed)))

(* val raw_match0 = raw_match
fun raw_match tyf tmf pat ob =
    Profile.profile "raw_match" (raw_match0 tyf tmf pat ob) *)

fun norm_subst ((tmS,_),(tyS,_)) =
 let val Theta = inst tyS
     fun del A [] = A
       | del A ({redex,residue}::rst) =
         del (let val redex' = Theta(redex)
              in if residue=redex' then A else (redex' |-> residue)::A
              end) rst
 in (del [] tmS,tyS)
 end

fun match_terml tyfixed tmfixed pat ob =
 norm_subst (raw_match tyfixed tmfixed pat ob ([],[]))

val match_term = match_terml [] empty_varset;

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

fun dest_eq_ty t = let
  val (fx, y) = dest_comb t
  val (f, x) = dest_comb fx
in
  if same_const f equality then (x, y, type_of x)
  else raise ERR "dest_eq_ty" "Term not an equality"
end

fun prim_mk_eq ty t1 t2 =
    App(App(inst [alpha |-> ty] equality, t1), t2)

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
datatype tok = bslash | id of int | lparen | rparen
open StringCvt

fun readtok (c : (char, cs) reader) cs0 = let
  val cs = skipWS c cs0
  val intread = Int.scan DEC c
in
  case c cs of
    NONE => NONE
  | SOME (#"|",cs') => SOME (bslash,cs')
  | SOME (#"(",cs') => SOME (lparen,cs')
  | SOME (#")",cs') => SOME (rparen,cs')
  | SOME c => (case intread cs of
                 NONE => NONE
               | SOME (i,cs') => SOME(id i, cs'))
end

(* SLR parser for grammar

     T   ::= tm $
     tm  ::= '|' [id] tm
     tm  ::= tmc
     tmc ::= tmc tmb
     tmc ::= tmb
     tmb ::= [id]
     tmb ::= '(' tm ')'
*)

datatype stk_item = LAM of term | C of term | BK | Start

fun parse tmv c cs0 = let
  fun adv cs = case readtok c cs of NONE => (NONE, cs)
                                  | SOME (t, cs') => (SOME t, cs')
  fun new_bv i stk = LAM (Vector.sub(tmv,i)) :: stk
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
      | (SOME lparen, cs') => parse_term (BK :: stk) (adv cs')
      | (SOME (id i), cs') => reduce_tmb stk (Vector.sub(tmv,i)) (adv cs')
      | _ => raise Fail "parse failure 1 in RawParse.parse"
  and reduce_tmb stk tm cur =
      case stk of
        [] => NONE
      | C t :: rest => parse_tmc (C (mk_comb(t,tm)) :: rest) cur
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
      | _ => raise Fail "parse failure 3 (reduce) in RawParse.parse"
in
  parse_term [Start] (adv cs0)
end


datatype grav = Top | CombL | CombR
datatype ppaction = Brk | Tm of term * grav | Stg of string

in

fun read_raw tmv s = valOf (scanString (parse tmv) s)
fun write_raw map t = let
  fun doit acc actlist =
      case actlist of
        [] => String.concat (List.rev acc)
      | Brk :: rest => doit (" "::acc) rest
      | Stg s :: rest => doit (s::acc) rest
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
          else let
              val (bv, body) = dest_abs t
              val core = [Stg "|", Tm(bv, Top), Brk, Tm(body, Top)]
            in
              if g <> Top then
                doit acc ((Stg "(" :: core) @ (Stg ")" :: rest))
              else
                doit acc (core @ rest)
            end
        end
in
  doit [] [Tm(t,Top)]
end

end (* local *)

end (* struct *)
