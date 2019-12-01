structure FullUnify :> FullUnify =
struct

open Abbrev
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
  type 'a EM = (t, 'a) optmonad.optmonad
  val empty : t =
        (Binarymap.mkDict String.compare, Binarymap.mkDict Term.compare)

  fun lookup_ty0 tym ty =
      if is_vartype ty then
        case Binarymap.peek(tym, dest_vartype ty) of
            NONE => ty
          | SOME ty' => lookup_ty0 tym ty'
      else
        let val {Thy,Tyop,Args} = dest_thy_type ty
            val Args' = map (lookup_ty0 tym) Args
        in
          mk_thy_type {Thy=Thy, Tyop=Tyop, Args=Args'}
        end
  fun lookup_ty (E:t) ty = lookup_ty0 (#1 E) ty
  fun instE (E:t) tm =
      let val tyvs = type_vars_in_term tm
          val sigma =
              map (fn ty => {redex = ty, residue = lookup_ty0 (#1 E) ty}) tyvs
      in
        Term.inst sigma tm
      end
  fun lookup_tm E tm =
      case dest_term tm of
          VAR _ => (case Binarymap.peek(#2 E, tm) of
                       NONE => instE E tm
                     | SOME tm' => lookup_tm E tm')
        | CONST _ => instE E tm
        | COMB(f,x) => mk_comb(lookup_tm E f, lookup_tm E x)
        | LAMB(v,bod) =>
          let
            val tm' =
                #1 (Binarymap.remove(#2 E, v)) handle Binarymap.NotFound => #2 E
          in
            mk_abs(instE E v, lookup_tm (#1 E, tm') bod)
          end



  fun add_tybind (s,ty) : unit EM = fn (tym,tmm)  =>
      case Binarymap.peek(tym, s) of
          NONE => SOME ((Binarymap.insert(tym,s,ty), tmm), ())
        | SOME _ => NONE

  fun add_tmbind (v, tm) : unit EM = fn (tym,tmm) =>
      case Binarymap.peek(tmm, v) of
          NONE => SOME((tym, Binarymap.insert(tmm,v,tm)), ())
        | SOME _ => NONE
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
                else if Lib.mem ty1 (type_vars ty2) orelse Lib.mem ty1 ctys then
                  fail
                else Env.add_tybind (dest_vartype ty1, ty2)
              else if is_vartype ty2 then
                if Lib.mem ty2 (type_vars ty1) orelse Lib.mem ty2 ctys then fail
                else Env.add_tybind (dest_vartype ty2, ty1)
              else
                let
                  val {Args=a1,Tyop=op1,Thy=thy1} = dest_thy_type ty1
                  val {Args=a2,Tyop=op2,Thy=thy2} = dest_thy_type ty2
                in
                  if thy1 <> thy2 orelse op1 <> op2 then fail
                  else
                    mmap recurse (ListPair.zip(a1,a2)) >> return ()
                end
        in
          (getty ty1_0 >* getty ty2_0) >>- k
        end
  in
    recurse(ty1,ty2)
  end

fun unify ctys ctms (t1, t2) : unit Env.EM =
  let
    open optmonad
    val op>>- = op>-
    fun recurse ctms (tm10, tm20) : unit Env.EM =
        let
          fun k (tm1, tm2) =
              if type_of tm1 <> type_of tm2 then fail
              else
                case (dest_term tm1, dest_term tm2) of
                    (VAR _, VAR _) => if tm1 ~~ tm2 then return ()
                                      else if tmem tm1 ctms then
                                        if tmem tm2 ctms then fail
                                        else Env.add_tmbind (tm2, tm1)
                                      else Env.add_tmbind (tm1, tm2)
                  | (VAR _, _) => if free_in tm1 tm2 orelse tmem tm1 ctms
                                  then
                                    fail
                                  else Env.add_tmbind (tm1, tm2)
                  | (_, VAR _) => if free_in tm2 tm1 orelse tmem tm2 ctms
                                  then
                                    fail
                                  else Env.add_tmbind (tm2, tm1)
                | (CONST _, CONST _) => if tm1 ~~ tm2 then return () else fail
                | (COMB(f1,x1), COMB(f2,x2)) =>
                  recurse ctms (f1,f2) >> recurse ctms (x1,x2)
                | (LAMB(bv1,bod1), LAMB(bv2,bod2)) =>
                  let
                    val gv = genvar (type_of bv1)
                  in
                    recurse (gv::ctms)
                            (subst [bv1 |-> gv] bod1, subst [bv2 |-> gv] bod2)
                  end
                | _ => fail
        in
          unify_types ctys (type_of tm10, type_of tm20) >>
          (gettm tm10 >* gettm tm20) >>- k
        end
  in
    recurse ctms (t1, t2)
  end





end
