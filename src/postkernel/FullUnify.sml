structure FullUnify :> FullUnify =
struct

open HolKernel

type tyenv = (string, hol_type) Binarymap.dict
val empty_tyenv : tyenv = Binarymap.mkDict String.compare

exception UNIF_ERROR of string

datatype tyrep = UVar of string
               | Tyvar of string
               | Tyop of {Thy:string, Name:string, Args : hol_type list}

datatype tmrep = tmUVar of string * tyrep
               | tmVar of string * tyrep
               | uConst of {Thy : string, Name : string, Ty : tyrep}
               | uCOMB of term * term
               | uLAMB of term * term

fun dest_type P ty =
  let
    val nm = dest_vartype ty
  in
    if P nm then UVar nm else Tyvar nm
  end handle HOL_ERR _ =>
             let val {Thy,Tyop=nm,Args} = dest_thy_type ty
             in
               Tyop{Thy = Thy, Name = nm, Args = Args}
             end

fun mkty (UVar s) = mk_vartype s
  | mkty (Tyvar s) = mk_vartype s
  | mkty (Tyop{Thy,Name,Args}) =
      mk_thy_type {Thy = Thy, Tyop = Name, Args = Args}

fun dest_term {tmP, tyP} tm =
  case HolKernel.dest_term tm of
      VAR (nm, ty) => if tmP nm then tmUVar(nm, dest_type tyP ty)
                      else tmVar(nm, dest_type tyP ty)
    | CONST{Thy,Name,Ty} => uConst {Thy = Thy, Name = Name,
                                    Ty = dest_type tyP Ty}
    | LAMB p => uLAMB p
    | COMB p => uCOMB p

fun mktm (tmUVar p) = mk_var ((I ## mkty) p)
  | mktm (tmVar p) = mk_var  ((I ## mkty) p)
  | mktm (uCOMB p) = mk_comb p
  | mktm (uLAMB p) = mk_abs p
  | mktm (uConst {Name,Thy,Ty}) = mk_thy_const {Name=Name,Thy=Thy,Ty=mkty Ty}

fun tyvwalk P e s =
  case Binarymap.peek(e, s) of
      SOME ty => (case dest_type P ty of
                      UVar vnm => tyvwalk P e vnm
                    | tyr => tyr)
    | NONE => UVar s

fun tywalk P E tyr =
  case tyr of
      UVar vnm => tyvwalk P E vnm
    | _ => tyr

fun tyoc P E tyrep v =
  case tywalk P E tyrep of
      UVar v' => v' = v
    | Tyvar _ => false
    | Tyop{Args,...} => List.exists (fn ty => tyoc P E (dest_type P ty) v) Args

fun tyunify0 P E (tyr1, tyr2) =
  case (tywalk P E tyr1, tywalk P E tyr2) of
      (UVar v1, UVar v2) => SOME (if v1 = v2 then E
                                  else Binarymap.insert(E,v1,mk_vartype v2))
    | (UVar v1, t2) => if tyoc P E t2 v1 then NONE
                       else SOME (Binarymap.insert(E,v1,mkty t2))
    | (t1, UVar v2) => if tyoc P E t1 v2 then NONE
                       else SOME (Binarymap.insert(E,v2,mkty t1))
    | (Tyvar s1, Tyvar s2) => if s1 = s2 then SOME E else NONE
    | (Tyop{Thy=thy1,Name=name1,Args = a1},
       Tyop{Thy=thy2,Name=name2,Args = a2}) =>
      if thy1 = thy2 andalso name1 = name2 then
        tyunifyl P E (a1,a2)
      else NONE
    | _ => NONE
and tyunifyl P E ([],[]) = SOME E
  | tyunifyl P E (ty1::ty1s, ty2::ty2s) =
    (case tyunify0 P E (dest_type P ty1, dest_type P ty2) of
         NONE => NONE
       | SOME E' => tyunifyl P E' (ty1s, ty2s))
  | tyunifyl P E _ = NONE

fun qtyrep ty = dest_type (K true) ty
fun unified tyE (tyr1, tyr2) =
  case (tywalk (K true) tyE tyr1, tywalk (K true) tyE tyr2) of
      (Tyop{Thy=thy1,Name=n1,Args=a1}, Tyop{Thy=thy2,Name=n2,Args=a2}) =>
        thy1 = thy2 andalso n1 = n2 andalso
        ListPair.all (fn (ty1,ty2) => unified tyE (qtyrep ty1, qtyrep ty2))
                     (a1,a2)
    | (tyr1', tyr2') => tyr1' = tyr2'

fun tmvwalk (P as {tyP, tmP}) (E as {tyE, tmE}) (p as (s,tyr)) =
  let
    val tyr' = tywalk tyP tyE tyr
  in
    case Binarymap.peek (tmE, s) of
        SOME (ty,tm) =>
        if unified tyE (dest_type tyP ty, tyr') then
          case dest_term P tm of
              tmUVar p => tmvwalk P E p
            | tmr => tmr
        else raise UNIF_ERROR ("Variable "^s^" has two distinct types")
      | NONE => tmUVar p
  end

fun tmwalk (P as {tyP, tmP}) (E as {tyE, tmE}) tmr =
  case tmr of
      tmUVar p => tmvwalk P E p
    | _ => tmr

fun tmoc P E v tmrep =
  case tmwalk P E tmrep of
      tmUVar (v',_) => v = v'
    | tmVar _ => false
    | uConst _ => false
    | uCOMB(t1,t2) => tmoc P E v (dest_term P t1) orelse
                      tmoc P E v (dest_term P t2)
    | uLAMB(bv,body) => tmoc P E v (dest_term P body)

fun utype_of {tyP,tmP} E tmr =
  dest_type tyP (type_of (mktm tmr))

val insert = Binarymap.insert

fun tmunify P (E0 as {tyE,tmE}) (tmr1, tmr2) =
  case tyunify0 (#tyP P) (#tyE E0) (utype_of P E0 tmr1, utype_of P E0 tmr2) of
      NONE => NONE
    | SOME tyE =>
      let
        val E as {tyE,tmE} = {tyE = tyE, tmE = #tmE E0}
      in
        case (tmwalk P E tmr1, tmwalk P E tmr2) of
            (tmUVar (s1, tyr1), tmUVar (s2, tyr2)) =>
              if s1 = s2 then SOME E
              else
                SOME{tyE = tyE,
                     tmE = insert(tmE, s1, (mkty tyr1, mk_var(s2, mkty tyr1)))}
          | (tmUVar (s1, tyr1), tmr2) =>
              if tmoc P E s1 tmr2 then NONE
              else SOME{tyE=tyE, tmE = insert(tmE, s1, (mkty tyr1, mktm tmr2))}
          | (tmr1, tmUVar (s2, tyr2)) =>
              if tmoc P E s2 tmr1 then NONE
              else SOME{tyE=tyE, tmE = insert(tmE, s2, (mkty tyr2, mktm tmr1))}
          | (tmVar (s1,_), tmVar (s2,_)) => if s1 = s2 then SOME E else NONE
          | (uConst{Name=n1,Thy=thy1,...}, uConst{Name=n2,Thy=thy2,...}) =>
              if n1 = n2 andalso thy1 = thy2 then SOME E else NONE
          | (uCOMB(t1,t2), uCOMB(u1,u2)) =>
            (case tmunify P E (dest_term P t1, dest_term P u1) of
                 NONE => NONE
               | SOME E' => tmunify P E' (dest_term P t2, dest_term P u2))
          | (uLAMB(p1 as (bv1,bod1)), uLAMB(p2 as (bv2,bod2))) =>
            let
              fun fo() =
                let val gv = genvar (type_of bv1)
                    val bod1' = subst [bv1 |-> gv] bod1
                    val bod2' = subst [bv2 |-> gv] bod2
                in
                  tmunify P E (dest_term P bod1', dest_term P bod2')
                end
              fun test ((bv1,bod1), (bv2,bod2)) k =
                case dest_term P bod1 of
                    uCOMB(f,x) =>
                    if aconv x bv1 then
                      case tmwalk P E (dest_term P f) of
                          tmUVar(s1,tyr1) =>
                            if tmoc P E s1 (dest_term P bod2) then NONE
                            else
                              SOME{tyE = tyE,
                                   tmE = insert(tmE, s1,
                                                (type_of bv1 --> type_of bod1,
                                                 mk_abs(bv2,bod2)))}
                        | _ => k()
                    else k()
                  | _ => k()
            in
              test (p1, p2) (fn () => test (p2, p1) fo)
            end
          | _ => NONE
      end

fun tyunify P E0 (ty1, ty2) =
  tyunify0 P E0 (dest_type P ty1, dest_type P ty2)

fun tywalkstar P E tyr =
  case tywalk P E tyr of
      Tyop{Thy,Name,Args} =>
      Tyop{Thy = Thy, Name = Name,
           Args = map (mkty o tywalkstar P E o dest_type P) Args}
    | x => x

fun tmwalkstar P E tmr =
  let
    val tyws = tywalkstar (#tyP P) (#tyE E)
    val tmws = mktm o tmwalkstar P E o dest_term P
  in
    case tmwalk P E tmr of
        tmUVar(s, tyr) => tmUVar(s, tyws tyr)
      | tmVar(s, tyr) => tmVar(s, tyws tyr)
      | uCOMB(t1,t2) => uCOMB(tmws t1, tmws t2)
      | uLAMB (bv, bod) => uLAMB (tmws bv, tmws bod)
      | uConst {Name,Thy,Ty} => uConst{Name = Name, Thy = Thy, Ty = tyws Ty}
  end

fun tycollapse P E =
  Binarymap.map (fn (vnm,_) => mkty (tywalkstar P E (UVar vnm))) E

fun tmcollapse (P as {tyP,...}) (E as {tyE,tmE}) =
  let
    val tyE' = tycollapse tyP tyE
  in
    {tyE = tyE',
     tmE = Binarymap.map
             (fn (vnm, (ty,_)) =>
                 mktm (tmwalkstar P E (tmUVar(vnm,dest_type tyP ty))))
             tmE}
  end

(* test

(* types *)

val uvar_v = String.isPrefix "'v"
fun tf ty1 ty2 =
  Option.map (Binarymap.listItems o tycollapse uvar_v)
             (tyunify uvar_v empty_tyenv (ty1, ty2))

val  r1 = tf ``:'a list`` ``:'v``
val  r2 = tf ``:'v1 list`` ``:'v2``
val  r3 = tf ``:'v1 # ('v2 list)`` ``:'v3 # 'v3``
val  r4 = tf ``:'v1 # ('v2 list)`` ``:'v3 # 'v1``
val  r5 = tf ``:'v1 list`` ``:'v3 # 'v1``
val  r6 = tf ``:'v1 list`` ``:'v1``
val  r7 = tf ``:'v4 # ('v5 list)`` ``:'v3 # 'v4``
val  r8 = tf ``:'v4 # ('a -> 'v4)`` ``:'v3 # 'v3``
val  r9 = tf ``:'v4 list`` ``:('a -> 'v5) list``
val r10 = tf ``:('a -> 'v5) list`` ``:'v4``
val r11 = tf ``:'a`` ``:'v1``
val r12 = tf ``:'a`` ``:'v1 list``
val r13 = tf ``:'a -> bool`` ``:'a -> 'v``

val tmvar = String.isPrefix "uv"
val P = {tmP = tmvar, tyP = uvar_v}
type 'a dict = (string,'a) Binarymap.dict
val E0 = {tyE = Binarymap.mkDict String.compare : hol_type dict,
          tmE = Binarymap.mkDict String.compare : (hol_type * term) dict}

fun tmf f (tm1,tm2) =
  Option.map
    ((fn {tmE, tyE} => (Binarymap.listItems tyE, Binarymap.listItems tmE)) o f)
    (tmunify P E0 (dest_term P tm1, dest_term P tm2))

val t1 = tmf (tmcollapse P) (``f:'a->'v1``, ``uv:'a->bool``)
val t2 = tmf I (``(f:'v1->'v2) uv2``, ``(uv:'a -> bool) x``)
val t3 = tmf (``(f:'v1->bool) uv2``, ``(uv:'a -> 'v2) x``)
val t4 = tmf (``(uvf:'v1->'v2) uv2``, ``CONS (h:'a) t``)
val t5 = tmf (``?x. x /\ T``, ``?y:'v1. uv y``)
val t6 = tmf (``?y:'v1. uv y``, ``?x:bool. x /\ T``)
val t7 = tmf (``uv1 (x:'v1) (uv:'v2) : 'v3``, ``x /\ x``)
val t8 = tmf (``uv1 (uv:'v1) (uv:'v1) : 'v3``, ``x /\ y``) (* NONE *)

*)


end
