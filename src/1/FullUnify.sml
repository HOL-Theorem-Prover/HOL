structure FullUnify :> FullUnify =
struct

open HolKernel boolSyntax
structure Env =
struct

  (* It would be nice to have a simple invariant such as
       term maps always preserve type
     But this can't work because you might want to unify

       x:'a    with    SUC

     this requires :'a to map to :num -> num.  So the invariant has to be
     something like

       term-variable v maps to term t  ==>
       type_of (sigma v) = type_of (sigma t)

     where sigma is the type instantiation given by the map
  *)
  type t = (string, hol_type) Binarymap.dict * (term, term) Binarymap.dict
  fun triTY ((d,_):t) = d
  fun triTM ((_, d):t) = d
  type 'a EM = (t, 'a) optmonad.optmonad
  val empty : t =
        (Binarymap.mkDict String.compare, Binarymap.mkDict Term.compare)

  fun lookup_ty0 tym ty =
      if is_vartype ty then
        case Binarymap.peek(tym, dest_vartype ty) of
            NONE => ty
          | SOME ty' => lookup_ty0 tym ty'
      else ty
  fun lookup_ty (E:t) ty = lookup_ty0 (#1 E) ty
  fun instE (E:t) tm =
      let val tyvs = type_vars_in_term tm
          val sigma =
              map (fn ty => {redex = ty, residue = lookup_ty0 (#1 E) ty}) tyvs
      in
        Term.inst sigma tm
      end
  fun lookup_tm E tm0 =
      let
        val tm = instE E tm0
      in
        case dest_term tm of
          VAR _ => (case Binarymap.peek(#2 E, tm) of
                        NONE => tm
                      | SOME tm' => lookup_tm E tm')
        | _ => tm
      end



  fun add_tybind (s,ty) : unit EM = fn (tym,tmm)  =>
      case Binarymap.peek(tym, s) of
          NONE => SOME ((Binarymap.insert(tym,s,ty), tmm), ())
        | SOME _ => NONE

  fun add_tmbind (v, tm) : unit EM = fn (tym,tmm) =>
      case Binarymap.peek(tmm, v) of
          NONE => SOME((tym, Binarymap.insert(tmm,v,tm)), ())
        | SOME _ => NONE

  fun fromEmpty (m : 'a EM) = Option.map #2 (m empty)
end (* Env struct *)

fun getty ty E = SOME(E, Env.lookup_ty E ty)
fun gettm tm : term Env.EM = fn E => SOME(E, Env.lookup_tm E tm)

infix >*
fun (m1 >* m2) = optmonad.lift2 (fn x => fn y => (x,y)) m1 m2

fun unify_types ctys (ty1, ty2) : unit Env.EM =
  let
    open optmonad
    val op>>- = op>-
    fun recurse (ty1_0, ty2_0) =
        let
          fun k (ty1, ty2) =
              if is_vartype ty1 then
                if ty1 = ty2 then return ()
                else if Lib.mem ty1 (type_vars ty2) then fail
                else if Lib.mem ty1 ctys then fail
                else Env.add_tybind (dest_vartype ty1, ty2)
              else if is_vartype ty2 then fail
              else
                let
                  val {Args=a1,Tyop=op1,Thy=thy1} = dest_thy_type ty1
                  val {Args=a2,Tyop=op2,Thy=thy2} = dest_thy_type ty2
                in
                  if thy1 <> thy2 orelse op1 <> op2 then fail
                  else
                    mmap recurse (ListPair.zip(a1,a2)) >> return ()
                end
          fun flip (p as (ty1, ty2)) =
              if is_vartype ty1 andalso not (Lib.mem ty1 ctys) then p
              else (ty2, ty1)
        in
          lift flip (getty ty1_0 >* getty ty2_0) >>- k
        end
  in
    recurse(ty1,ty2)
  end

fun unify ctys ctms (t1, t2) : unit Env.EM =
  let
    open optmonad
    val op>>- = op>-
    fun recurse bvs (tm10, tm20) : unit Env.EM =
        let
          fun k (tm1, tm2) =
              case (dest_term tm1, dest_term tm2) of
                  (VAR _, VAR _) => if tm1 ~~ tm2 then return ()
                                    else if tmem tm1 bvs orelse tmem tm2 bvs
                                    then
                                      fail
                                    else if tmem tm1 ctms then
                                      if tmem tm2 ctms then fail
                                      else Env.add_tmbind (tm2, tm1)
                                    else Env.add_tmbind (tm1, tm2)
                | (VAR _, _) => if free_in tm1 tm2 orelse tmem tm1 ctms orelse
                                   tmem tm1 bvs
                                then
                                  fail
                                else Env.add_tmbind (tm1, tm2)
                | (CONST _, CONST _) => if tm1 ~~ tm2 then return () else fail
                | (COMB(f1,x1), COMB(f2,x2)) =>
                    unify_types ctys (type_of x1, type_of x2) >>
                    recurse bvs (f1,f2) >> recurse bvs (x1,x2)
                | (LAMB(bv1,bod1), LAMB(bv2,bod2)) =>
                  let
                    val gv = genvar (type_of bv1)
                  in
                    recurse (gv::bvs)
                            (subst [bv1 |-> gv] bod1, subst [bv2 |-> gv] bod2)
                  end
                | _ => fail
          fun flip (p as (t1, t2)) =
              if is_var t1 then p else if is_var t2 then (t2,t1) else p
        in
          lift flip (gettm tm10 >* gettm tm20) >>- k
        end
  in
    unify_types ctys (type_of t1, type_of t2) >>
    recurse [] (t1, t2)
  end

fun collapse_map (freeset,empty,dosub) subst =
    let
      fun find_used_leaf subst =
          let
            val with_frees = map (fn i as {redex,residue} => (i,freeset residue))
                                 subst
            val (used_vars, keys) =
                List.foldl (fn (({redex,residue},fvs), (uvA, kA)) =>
                               (HOLset.union(uvA, fvs), HOLset.add(kA, redex)))
                           (empty, empty)
                           with_frees
            fun used_leaf (i as {redex,residue},fvs) =
                if HOLset.member(used_vars, redex) andalso
                   HOLset.isEmpty(HOLset.intersection(fvs,keys))
                then SOME i
                else NONE

          in
            case trypluck' used_leaf with_frees of
                (SOME i, rest) => SOME(i, map #1 rest)
              | (NONE, _) => NONE
          end

      fun recurse subst =
            case find_used_leaf subst of
                NONE => subst
              | SOME (i as {redex,residue}, rest) =>
                let
                  val rest' = map (fn {redex,residue} =>
                                      {redex=redex, residue = dosub [i] residue})
                                  rest
                in
                  i :: recurse rest'
                end
    in
      recurse subst
    end

fun collapse0 E =
    let
      val mk_vartype = trace ("Vartype Format Complaint", 0) mk_vartype
      fun EtoSUBST i E =
          Binarymap.foldl
            (fn (k,v,A) => {redex = i k, residue = v} :: A)
            []
            E
      val tymap =
          collapse_map (HOLset.fromList Type.compare o Type.type_vars,
                      HOLset.empty Type.compare,
                      Type.type_subst)
                     (EtoSUBST mk_vartype (Env.triTY E))
      val tmmap0 = map (fn {residue,redex} =>
                           {residue = Term.inst tymap residue,
                            redex = Term.inst tymap redex})
                       (EtoSUBST (fn x => x) (Env.triTM E))
    in
      (tymap,
       collapse_map (fn t => FVL [t] empty_tmset, empty_tmset, Term.subst) tmmap0
      )
    end

fun collapse E = SOME(E, collapse0 E)


end
