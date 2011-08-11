structure Prekind :> Prekind =
struct

open HolKernel optmonad;
infix >> >-;
infixr 3 ==>;

  type prerank = Prerank.prerank
  type oprerank = Prerank.oprerank

val Zerorank = Prerank.Zerorank

fun is_debug() = current_trace "debug_type_inference" >= 4;

val show_kinds = ref 1
val _ = Feedback.register_trace("kinds", show_kinds, 2)

val TCERR = mk_HOL_ERR "Prekind";
val ERRloc = mk_HOL_ERRloc "Prekind"

fun rcheck_say s = if Feedback.current_trace "show_typecheck_errors" > 0 handle _ => true
                   then Lib.say s else ()

datatype rcheck_error =
         KdRankConstrFail of kind * rank
       | KdRankLEConstrFail of kind * rank

val last_rcerror : (rcheck_error * locn.locn) option ref = ref NONE

 datatype prekind0
    = Varkind of string * prerank
    | Typekind of prerank
    | Arrowkind of prekind * prekind
    | KdRankConstr of {Kd : prekind, Rank : prerank}
    | UVarkind of uvarkind ref
 and uvarkind
    = SOMEK of prekind
    | NONEK of prerank
 and prekind = PK of prekind0 locn.located

fun isSomeK (SOMEK _) = true
  | isSomeK (NONEK _) = false

fun THEK (SOMEK v) = v
  | THEK (NONEK _) = raise TCERR "THEK" "uvarkind not a SOMEK";

fun eq0 (UVarkind (ref(SOMEK (PK(kd,l)))))    kd'              = eq0 kd kd'
  | eq0 kd                (UVarkind (ref(SOMEK (PK(kd',l)))) ) = eq0 kd kd'
  | eq0 (Varkind(s,rk))            (Varkind(s',rk'))           = s=s' andalso Prerank.eq rk rk'
  | eq0 (Typekind rk)              (Typekind rk')              = Prerank.eq rk rk'
  | eq0 (Arrowkind(kd1,kd2))       (Arrowkind(kd1',kd2'))      = eq kd1 kd1' andalso eq kd2 kd2'
  | eq0 (KdRankConstr{Kd=kd, Rank=rk}) (KdRankConstr{Kd=kd', Rank=rk'})
                                                               = eq kd kd' andalso Prerank.eq rk rk'
  | eq0 (UVarkind (r as ref (NONEK _))) (UVarkind (r' as ref (NONEK _))) = r=r'
  | eq0 _                          _                           = false
and eq  (PK (value,locn))          (PK (value',locn'))         = eq0 value value'

fun ge0 (UVarkind (ref(SOMEK (PK(kd,l)))))    kd'              = ge0 kd kd'
  | ge0 kd                (UVarkind (ref(SOMEK (PK(kd',l)))) ) = ge0 kd kd'
  | ge0 (Varkind(s,rk))            (Varkind(s',rk'))           = s=s' andalso Prerank.eq rk rk'
  | ge0 (Typekind rk)              (Typekind rk')              = Prerank.leq rk' rk
  | ge0 (Arrowkind(kd1,kd2))       (Arrowkind(kd1',kd2'))      = eq kd1 kd1' andalso ge kd2 kd2'
  | ge0 (KdRankConstr{Kd=kd, Rank=rk}) (KdRankConstr{Kd=kd', Rank=rk'})
                                                               = ge kd kd' andalso Prerank.leq rk' rk
  | ge0 (UVarkind (r as ref (NONEK _))) (UVarkind (r' as ref (NONEK _))) = r=r'
  | ge0 _                          _                           = false
and ge  (PK (value,locn))          (PK (value',locn'))         = ge0 value value'

(* eqr is needed because during type inference, some ranks may not yet have been unified,
   so disregard them for this comparison. *)
fun eqr0 (UVarkind (ref(SOMEK (PK(kd,_)))))    kd'              = eqr0 kd kd'
  | eqr0 kd                (UVarkind (ref(SOMEK (PK(kd',_)))) ) = eqr0 kd kd'
  | eqr0 (Varkind(s,rk))            (Varkind(s',rk'))           = s=s' (* NOT andalso Prerank.eq rk rk' *)
  | eqr0 (Typekind rk)              (Typekind rk')              = true (* NOT Prerank.eq rk rk' *)
  | eqr0 (Arrowkind(kd1,kd2))       (Arrowkind(kd1',kd2'))      = eqr kd1 kd1' andalso eqr kd2 kd2'
  | eqr0 (KdRankConstr{Kd=kd, Rank=rk}) (KdRankConstr{Kd=kd', Rank=rk'})
                                                                = eqr kd kd' (* NOT andalso Prerank.eq rk rk' *)
  | eqr0 (UVarkind (r as ref (NONEK _))) (UVarkind (r' as ref (NONEK _))) = r=r'
  | eqr0 _                          _                           = false
and eqr  (PK (value,locn))          (PK (value',locn'))         = eqr0 value value'

val op :>=: = ge
infix 3 :>=:

fun typ rk = PK (Typekind rk, locn.Loc_None)

fun is_type_kind (PK (Typekind _, _)) = true
  | is_type_kind _ = false

fun dest_type_kind (PK (Typekind rk, _)) = rk
  | dest_type_kind _ = raise TCERR "dest_type_kind" "not a type kind"

fun is_var_kind (PK (Varkind _, _)) = true
  | is_var_kind _ = false

fun dest_var_kind (PK (Varkind p, _)) = p
  | dest_var_kind _ = raise TCERR "dest_var_kind" "not a kind variable"

fun ((kd1 as PK(_,loc1)) ==> (kd2 as PK(_,loc2))) =
    PK(Arrowkind(kd1,kd2),
       locn.between loc1 loc2)

fun mk_arrow_kind(kd1, kd2) = kd1 ==> kd2

fun dest_arrow_kind (PK (Arrowkind p, _)) = p
  | dest_arrow_kind _ = raise TCERR "dest_arrow_kind" "not an arrow kind"

fun dom_rng (PK (Arrowkind p, _)) = p
  | dom_rng (PK (KdRankConstr{Kd,...}, _)) = dom_rng Kd
  | dom_rng (PK (UVarkind (ref(SOMEK kd)), _)) = dom_rng kd
  | dom_rng _ = raise TCERR "dom_rng" "not an arrow kind"

val is_arrow_kind = can dom_rng

fun list_mk_arrow_kind([], kd0) = kd0
  | list_mk_arrow_kind(kd::kds, kd0) = kd ==> list_mk_arrow_kind(kds, kd0)

fun mk_arity 0 = typ Zerorank
  | mk_arity n = if n > 0 then typ Zerorank ==> mk_arity (n - 1)
                 else raise TCERR "mk_arity" "negative arity"

fun is_arity (PK(kd0,_)) =
  case kd0 of
    UVarkind(ref (SOMEK kd')) => is_arity kd'
  | Typekind Zerorank => true
  | Arrowkind(PK(Typekind Zerorank,_),kd2) => is_arity kd2
  | _ => false

and is_type_kind (PK(kd0,_)) =
  case kd0 of
    UVarkind(ref (SOMEK kd')) => is_type_kind kd'
  | Typekind _ => true
  | KdRankConstr{Kd=kd, Rank=rk} => is_type_kind kd
  | _ => false

and arity_of (PK(kd0,locn)) =
  case kd0 of
    UVarkind(ref (SOMEK kd')) => arity_of kd'
  | Typekind Zerorank => 0
  | Arrowkind(PK(Typekind Zerorank,_),kd2) => 1 + arity_of kd2
  | Arrowkind(PK(UVarkind(ref (SOMEK kd1')),_),kd2) => arity_of(PK(Arrowkind(kd1',kd2),locn))
  | KdRankConstr{Kd=kd, Rank=Zerorank} => arity_of kd
  | _ => raise TCERR "arity_of" "not an arity kind"

fun prekind_to_string (kd as PK(kd0,locn)) =
  case kd0 of
    UVarkind(r as ref (SOMEK kd')) => Int.toString(Portable.ref_to_int r) ^ "= " ^
                                      prekind_to_string kd'
  | UVarkind(r as ref (NONEK rk)) => "?" ^ Int.toString(Portable.ref_to_int r) ^
                                     (if rk = Zerorank then "" else ": " ^ Prerank.prerank_to_string rk)
  | Varkind (s,rk) => s ^ (if rk = Zerorank then "" else ":" ^ Prerank.prerank_to_string rk)
  | Typekind rk => "ty" ^ (if rk = Zerorank then "" else ":" ^ Prerank.prerank_to_string rk)
  | Arrowkind(kd1, kd2) => "(" ^ prekind_to_string kd1 ^ " => " ^ prekind_to_string kd2 ^ ")"
  | KdRankConstr{Kd=kd, Rank=rk} => "(" ^ prekind_to_string kd ^
                                   " : " ^ Prerank.prerank_to_string rk ^ ")"

fun default_rank Prerank.Zerorank = true
  | default_rank _ = false
fun pp_if_prerank add_string pp_prerank rk =
      if current_trace "ranks" < 2 orelse default_rank rk then ()
      else (add_string ":";
            pp_prerank rk)

fun pp_prekind pps kd =
 let open Portable Prerank
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val pp_prerank = Prerank.pp_prerank pps
     val pp_if_prerank = pp_if_prerank add_string pp_prerank
     fun pp2 paren (Typekind rk) =
                        (add_string "ty";
                         if rk=Zerorank then () else
                           (add_string ":";
                            add_break(0,0);
                            pp_prerank rk))
       | pp2 paren (Varkind (s,rk)) =
                        (add_string s;
                         if rk=Zerorank then () else
                           (add_string ":";
                            add_break(0,0);
                            pp_prerank rk))
       | pp2 paren (UVarkind (r as ref (SOMEK kd))) =
                        (add_string (Int.toString(Portable.ref_to_int r) ^ "=");
                         add_break(1,0);
                         pp1 paren kd)
       | pp2 paren (UVarkind (r as ref (NONEK rk))) =
                        (add_string ("?" ^ Int.toString(Portable.ref_to_int r));
                         if rk=Zerorank then () else
                           (add_string ":";
                            add_break(1,0);
                            pp_prerank rk))
       | pp2 paren (KdRankConstr {Kd,Rank}) =
                        ( pp1 true Kd;
                          add_string " :";
                          add_break(1,0);
                          pp_prerank Rank )
       | pp2 paren (Arrowkind(Rator,Rand)) =
          ( if paren then (add_string "("; begin_block INCONSISTENT 0) else ();
            pp true Rator; add_string " =>"; add_break(1,0); pp false Rand;
            if paren then (end_block(); add_string ")") else () )
     and pp1 paren (PK(kd,_)) = pp2 paren kd
     and pp0 paren (Typekind rk) =
                        (add_string "ty";
                         if rk=Zerorank then () else
                           (add_string ":";
                            add_break(0,0);
                            pp_prerank rk))
       | pp0 paren (Varkind (s,rk)) =
                        (add_string s;
                         if rk=Zerorank then () else
                           (add_string ":";
                            add_break(0,0);
                            pp_prerank rk))
       | pp0 paren (UVarkind (r as ref (SOMEK kd))) =
                        (add_string (Int.toString(Portable.ref_to_int r) ^ "=");
                         add_break(1,0);
                         pp paren kd)
       | pp0 paren (UVarkind (r as ref (NONEK rk))) =
                        (add_string ("?" ^ Int.toString(Portable.ref_to_int r));
                         if rk=Zerorank then () else
                           (add_string ":";
                            add_break(1,0);
                            pp_prerank rk))
       | pp0 paren (KdRankConstr {Kd,Rank}) =
                        ( pp true Kd;
                          add_string " :";
                          add_break(1,0);
                          pp_prerank Rank )
       | pp0 paren kd = if current_trace "pp_arity_kinds" = 0 then pp2 paren kd
                        else let val kd1 = PK(kd,locn.Loc_None)
                             in if is_arity kd1
                                  then add_string ("ar " ^ Lib.int_to_string (arity_of kd1))
                                  else pp2 paren kd
                             end
    and pp paren (PK(kd,_)) = pp0 paren kd
 in
   begin_block INCONSISTENT 0;
   pp false kd;
   end_block()
 end;

val prekind_to_string = Portable.pp_to_string 80 pp_prekind
fun print_prekind ty = Portable.output(Portable.std_out, prekind_to_string ty);

(*---------------------------------------------------------------------------*
 * Calculate the prerank of a prekind.                                       *
 *---------------------------------------------------------------------------*)

local
val max  = Prerank.mk_Maxrank
in
fun prank_of0 (Varkind(s,rk)) = rk
  | prank_of0 (Typekind rk)   = rk
  | prank_of0 (Arrowkind(dom,rng)) = max( prank_of dom, prank_of rng )
  | prank_of0 (KdRankConstr{Kd,Rank}) = Rank
  | prank_of0 (UVarkind (ref (NONEK rk))) = rk
  | prank_of0 (UVarkind (ref (SOMEK kd))) = prank_of kd
and prank_of (PK(kd,locn)) = prank_of0 kd
end;


(* ----------------------------------------------------------------------
    A total ordering on prekinds.
    UVarkind(NONE) < UVarkind(SOME) < Varkind < Typekind < Arrowkind < KdRankConstr
   ---------------------------------------------------------------------- *)

val prerank_compare = Prerank.prerank_compare

fun prekind_compare0 (UVarkind (ref (NONEK rk1)), UVarkind (ref (NONEK rk2))) = prerank_compare(rk1,rk2)
  | prekind_compare0 (UVarkind (ref (NONEK _)),  _)                         = LESS
  | prekind_compare0 (UVarkind (ref (SOMEK _)),  UVarkind (ref (NONEK _)))  = GREATER
  | prekind_compare0 (UVarkind (ref (SOMEK k1)), UVarkind (ref (SOMEK k2))) = prekind_compare(k1,k2)
  | prekind_compare0 (UVarkind (ref (SOMEK _)),  _)                         = LESS
  | prekind_compare0 (Varkind _,                 UVarkind _)                = GREATER
  | prekind_compare0 (Varkind p1,                Varkind p2)                =
        Lib.pair_compare(String.compare,prerank_compare)(p1,p2)
  | prekind_compare0 (Varkind _,                 _)                         = LESS
  | prekind_compare0 (Typekind rk1,              Typekind rk2)              = prerank_compare(rk1,rk2)
  | prekind_compare0 (Typekind _,                Arrowkind _)               = LESS
  | prekind_compare0 (Typekind _,                KdRankConstr _)            = LESS
  | prekind_compare0 (Typekind _,                _)                         = GREATER
  | prekind_compare0 (Arrowkind p1,              Arrowkind p2)              =
        Lib.pair_compare(prekind_compare,prekind_compare)(p1,p2)
  | prekind_compare0 (Arrowkind _,               KdRankConstr _)            = LESS
  | prekind_compare0 (Arrowkind _,               _)                         = GREATER
  | prekind_compare0 (KdRankConstr{Kd=k1,Rank=r1}, KdRankConstr{Kd=k2,Rank=r2}) =
        Lib.pair_compare(prekind_compare,prerank_compare)((k1,r1),(k2,r2))
  | prekind_compare0 (KdRankConstr _,            _)                         = GREATER
and prekind_compare (PK (value1,locn1), PK (value2,locn2)) = prekind_compare0 (value1,value2);

fun kindvars (PK (kd, loc)) =
  case kd of
    Varkind (s,rk) => [s]
  | Typekind _ => []
  | Arrowkind (kd1, kd2) => Lib.union (kindvars kd1) (kindvars kd2)
  | KdRankConstr{Kd=kd,...} => kindvars kd
  | UVarkind (ref (NONEK _)) => []
  | UVarkind (ref (SOMEK k')) => kindvars k'

fun uvars_of (PK(ty, loc)) =
    case ty of
      UVarkind r => [r]
    | Arrowkind (kd1, kd2) => Lib.union (uvars_of kd1) (uvars_of kd2)
    | KdRankConstr{Kd=kd,...} => uvars_of kd
    | _ => []

fun new_uvar rk = PK (UVarkind(ref (NONEK rk)), locn.Loc_None)

fun all_new_uvar () = new_uvar (Prerank.new_uvar())
(*fun new_var_uvar () = new_uvar (Prerank.new_var_uvar())*)

local
val reset_rk = Prerank.reset_rank_uvars
in
fun reset_rank_uvars0 (UVarkind (ref(NONEK rk))) = reset_rk rk
  | reset_rank_uvars0 (UVarkind (ref(SOMEK kd))) = reset_rank_uvars kd
  | reset_rank_uvars0 (Varkind(s,rk)) = reset_rk rk
  | reset_rank_uvars0 (Typekind rk) =  reset_rk rk
  | reset_rank_uvars0 (Arrowkind(kd1,kd2)) = (reset_rank_uvars kd1; reset_rank_uvars kd2)
  | reset_rank_uvars0 (KdRankConstr{Kd,Rank}) = (reset_rk Rank; reset_rank_uvars Kd)
and reset_rank_uvars (PK(kd0,_)) = reset_rank_uvars0 kd0
end

infix ref_occurs_in

fun r ref_occurs_in (PK(value, locn)) =
  case value of
    Varkind _ => false
  | Typekind _ => false
  | Arrowkind(kd1, kd2) => r ref_occurs_in kd1 orelse r ref_occurs_in kd2
  | KdRankConstr{Kd=kd,Rank=rk} => r ref_occurs_in kd
  | UVarkind (r' as ref (NONEK _)) => r = r'
  | UVarkind (r' as ref (SOMEK k)) => r = r' orelse r ref_occurs_in k

infix ref_equiv
fun r ref_equiv (PK(value, locn)) =
  case value of
    UVarkind (r' as ref (NONEK _)) => r = r'
  | UVarkind (r' as ref (SOMEK k)) => r = r' orelse r ref_equiv k
  | _ => false

  fun has_free_uvar (PK(pkd,_)) =
    case pkd of
      UVarkind (ref (NONEK _))    => true
    | UVarkind (ref (SOMEK pkd')) => has_free_uvar pkd'
    | Varkind _                   => false
    | Typekind _                  => false
    | Arrowkind(kd1, kd2)         => has_free_uvar kd1 orelse has_free_uvar kd2
    | KdRankConstr{Kd=kd,...}     => has_free_uvar kd

fun rank_unify n r1 r2 (rk_env,kd_env) =
  let val (rk_env', result) = Prerank.unsafe_unify n r1 r2 rk_env
  in if not (is_debug()) then () else
     case result of SOME _ => () | NONE =>
         (print "\nrank_unify failed:\n";
          print (Prerank.prerank_to_string r1 ^ " compared to\n" ^
                 Prerank.prerank_to_string r2 ^ "\n"));
     ((rk_env',kd_env), result)
  end

fun rank_unify_le n r1 r2 (rk_env,kd_env) =
  let val (rk_env', result) = Prerank.unsafe_unify_le n r1 r2 rk_env
  in if not (is_debug()) then () else
     case result of SOME _ => () | NONE =>
         (print "\nrank_unify_le failed:\n";
          print (Prerank.prerank_to_string r1 ^ " compared to\n" ^
                 Prerank.prerank_to_string r2 ^ "\n"));
     ((rk_env',kd_env), result)
  end

fun no_rank_unify n r1 r2 (rk_env,kd_env) = ((rk_env,kd_env), SOME())


fun report s cmp n kd1 kd2 m e =
  let fun spaces n = if n = 0 then "" else ("  " ^ spaces(n-1))
      val _ = if not (is_debug()) then () else
          print ("\n" ^ spaces n ^ s ^ ": " ^ prekind_to_string kd1 ^ "\n" ^
                 spaces n ^ "to be  " ^ cmp ^ "   to: " ^ prekind_to_string kd2 ^ "\n")
      val (e',result) = m e
      val resstr = "\n" ^ spaces n ^ s ^ ": " ^ prekind_to_string kd1 ^ "\n" ^
                 spaces n ^ "to be  " ^ cmp ^ "   to: " ^ prekind_to_string kd2 ^ "\n"
  in case result
       of NONE => if not (is_debug()) then () else (print (resstr ^ spaces n ^ "failed\n"))
      | SOME() => if not (is_debug()) then () else (print (resstr ^ spaces n ^ "succeeded\n"));
(*
       of NONE => if not (is_debug()) then () else print (resstr ^ spaces n "failed\n")
                  (print ("\n" ^ spaces n ^ s ^ " failed for\n" ^ spaces n);
                   print (prekind_to_string kd1 ^ " compared to " ^ cmp ^ "\n" ^ spaces n);
                   print (prekind_to_string kd2 ^ "\n"))
      | SOME() => if not (is_debug()) then () else
                  (print ("\n" ^ spaces n ^ s ^ " succeeded for\n" ^ spaces n);
                   print (prekind_to_string kd1 ^ " compared to " ^ cmp ^ "\n" ^ spaces n);
                   print (prekind_to_string kd2 ^ "\n"));
*)
      (e',result)
  end


fun unsafe_bind n f r value =
  if r ref_equiv value
  then ok
  else if r ref_occurs_in value orelse isSomeK (!r)
       then fail
    else
      report "Bind kind uvar" "= " n (PK(UVarkind r, locn.Loc_None)) value
         (fn (rk_env,kd_env) =>
             (((rk_env,(r, !r)::kd_env), SOME ()) before r := SOMEK value))


(* first argument "bind" is a function which performs a binding between a
   pretype reference and another pretype, updating some sort of environment
   (the 'a), returning the new alpha and a unit option, SOME () for a
   success, and a NONE, if not.

   To further complicate things, the bind argument also gets a copy of
   gen_unify to call, if it should choose.
*)
(* this will need changing *)
(* eta-expansion *is* necessary *)
fun gen_unify (rank_unify   :int -> prerank -> prerank -> ('a -> 'a * unit option))
              (rank_unify_le:int -> prerank -> prerank -> ('a -> 'a * unit option))
              (rank_unify_eq:int -> prerank -> prerank -> ('a -> 'a * unit option))
              (bind : int -> (prekind -> prekind -> ('a -> 'a * unit option)) ->
                      (uvarkind ref -> (prekind -> ('a -> 'a * unit option))))
              s n (kd1 as PK(k1,locn1)) (kd2 as PK(k2,locn2)) e = let
  val gen_unify_eq = gen_unify rank_unify rank_unify_eq rank_unify_eq bind " =" (n+1)
  val gen_unify    = gen_unify rank_unify rank_unify_le rank_unify_eq bind s (n+1)
  val rank_unify = rank_unify (n+1)
  val rank_unify_le = rank_unify_le (n+1)
  val bind = bind (n+1)
in
report "Unifying kinds" s n kd1 kd2 (
  case (k1, k2) of
(* Believe that rank_unify_le should be rank_unify (forcing equality),
   when binding a prekind UVarkind NONE to a value
   NO: this fails when type constant c:(tuv1:r1 => tuv2:r1) => ty:r1
       is applied to type value v:('k:r => 'l:0);
       tuv2 is bound to 'l:0, so r1 is bound to be equal to 0,
       but then tuv1 is bound to 'k:r, so r1(=0) must  be >= r. !!!
   Correction: for the fifth line below, it must be rank_unify, not rank_unify_le,
               so that the rank of the kind uvar (r) does not decrease
   Correction: for the second case below, it must be rank_unify, not rank_unify_le,
               so that the rank of the kind uvar (r) is equal to that of kd1
   2011-01-31: added first and fifth cases for less determined inferencing; experimental  *)
    (Typekind rk1, UVarkind (r as ref (NONEK rk))) =>
       rank_unify_le rk1 rk >> bind gen_unify r (PK((Typekind rk),locn2)) (* experimental *)
  | (Arrowkind(kd11, kd12), UVarkind (r as ref (NONEK rk))) =>
       let (*val kd21 = all_new_uvar()
           and kd22 = all_new_uvar()
           val kd2' = PK(Arrowkind(kd21,kd22),locn2)*)
           val kd2' = PK(Arrowkind(all_new_uvar(),all_new_uvar()),locn2)
       in rank_unify (prank_of kd2') rk >> bind gen_unify r kd2' >> gen_unify kd1 kd2'
       (*in rank_unify_le (prank_of kd2') rk >>
          gen_unify_eq kd11 kd21 >> gen_unify kd12 kd22 >> bind gen_unify r kd2'*)
       end
  (*| (_, UVarkind (r as ref (NONEK rk))) => rank_unify(*_le*) (prank_of kd1) rk >> bind gen_unify r kd1*)
  | (_, UVarkind (r as ref (NONEK rk))) => rank_unify_le (prank_of kd1) rk >> bind gen_unify r kd1
  | (k1, UVarkind (r as ref (SOMEK k2))) => gen_unify kd1 k2
  | (UVarkind (r as ref (NONEK rk)), Typekind rk2) =>
       rank_unify_le rk rk2 >> bind gen_unify r (PK((Typekind rk),locn1)) (* experimental *)
  | (UVarkind (r as ref (NONEK rk)), Arrowkind(kd21, kd22)) =>
       let (*val kd11 = all_new_uvar()
           and kd12 = all_new_uvar()
           val kd1' = PK(Arrowkind(kd11,kd12),locn2)*)
           val kd1' = PK(Arrowkind(all_new_uvar(),all_new_uvar()),locn2)
       in rank_unify rk (prank_of kd1') >> bind gen_unify r kd1' >> gen_unify kd1' kd2
       (*in rank_unify rk (prank_of kd1') >>
          gen_unify_eq kd11 kd21 >> gen_unify kd12 kd22 >> bind gen_unify r kd1'*)
       end
  (*| (UVarkind (r as ref (NONEK rk)), _) => rank_unify(*_le*) rk (prank_of kd2) >> bind gen_unify r kd2*)
  | (UVarkind (r as ref (NONEK rk)), _) => rank_unify_le rk (prank_of kd2) >> bind gen_unify r kd2
  | (UVarkind (r as ref (SOMEK k1)), k2) => gen_unify k1 kd2
  | (Varkind (s1,rk1), Varkind (s2,rk2)) => (fn e => (if s1 = s2 then ok else fail) e)
                                            >> rank_unify rk1 rk2
  | (Typekind rk1, Typekind rk2) => rank_unify_le rk1 rk2
  | (Arrowkind(kd11, kd12), Arrowkind(kd21, kd22)) =>
       gen_unify_eq kd11 kd21 >> gen_unify kd12 kd22
  | (KdRankConstr{Kd=kd1',Rank=rk1}, _) =>
       rank_unify (prank_of kd1') rk1 >> gen_unify kd1' kd2
  | (_, KdRankConstr{Kd=kd2',Rank=rk2}) =>
       rank_unify (prank_of kd2') rk2 >> gen_unify kd1 kd2'
  | _ => fail
)
 end e

val unsafe_unify = gen_unify rank_unify rank_unify rank_unify unsafe_bind "= "
val unsafe_unify_le = gen_unify rank_unify rank_unify_le rank_unify unsafe_bind "<="
val unsafe_conty_unify = gen_unify rank_unify no_rank_unify no_rank_unify unsafe_bind "=?"

fun unify k1 k2 =
  case (gen_unify rank_unify rank_unify rank_unify unsafe_bind "= " 0 k1 k2 ([],[]))
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify" "unify failed";

fun unify_le k1 k2 =
  case (gen_unify rank_unify rank_unify_le rank_unify unsafe_bind "<=" 0 k1 k2 ([],[]))
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify_le" "unify failed";

fun can_unify k1 k2 = let
  val ((rank_bindings,kind_bindings), result) =
        gen_unify rank_unify rank_unify rank_unify unsafe_bind "= " 0 k1 k2 ([],[])
  val _ = app (fn (r, oldvalue) => r := oldvalue) rank_bindings
  val _ = app (fn (r, oldvalue) => r := oldvalue) kind_bindings
in
  isSome result
end

fun can_unify_le k1 k2 = let
  val ((rank_bindings,kind_bindings), result) =
        gen_unify rank_unify rank_unify_le rank_unify unsafe_bind "<=" 0 k1 k2 ([],[])
  val _ = app (fn (r, oldvalue) => r := oldvalue) rank_bindings
  val _ = app (fn (r, oldvalue) => r := oldvalue) kind_bindings
in
  isSome result
end

fun print_safe_env n env =
  if not (is_debug()) then (env, SOME ()) else
  let 
    fun spaces n = if n = 0 then "" else ("  " ^ spaces(n-1))
    fun print1 (r, kd) =
      print (Int.toString(Portable.ref_to_int r) ^ " |-> "
               ^ prekind_to_string (THEK kd))
    fun printn (r_kd::r_kds) =
        let in
          print ("\n  " ^ spaces n);
          print1 r_kd;
          printn r_kds
        end
      | printn [] = print " "
  in
    print (spaces n^"[ ");
    if null env then ()
    else (print1 (hd env);
          printn (tl env));
    print "]\n";
    (env, SOME ())
  end

local
  fun (r ref_equiv (PK(value, locn))) (env as (renv,kenv)) =
       case value of
         UVarkind (r' as ref (NONEK _)) =>
              r = r' orelse
              let in
                case Lib.assoc1 r' kenv
                 of NONE => false
                  | SOME (_, v) => (r ref_equiv (THEK v)) env
              end
         | UVarkind (r' as ref (SOMEK k)) => (* r = r' orelse *) (r ref_equiv k) env
           (* equality test unnecessary since r must point to a UVarkind(NONEK _) *)
         | _ => false

      fun (r ref_occurs_in (PK(value, locn))) (env as (renv,kenv)) =
        case value
         of UVarkind (r' as ref (NONEK _)) =>
              r = r' orelse
              let in
                case Lib.assoc1 r' kenv
                 of NONE => false
                  | SOME (_, v) => (r ref_occurs_in (THEK v)) env
              end
          | UVarkind (r' as ref (SOMEK k)) => (* r = r' orelse *) (r ref_occurs_in k) env
           (* equality test unnecessary since r must point to a UVarkind(NONEK _) *)
          | Arrowkind(kd1,kd2) => (r ref_occurs_in kd1) env orelse
                                  (r ref_occurs_in kd2) env
          | KdRankConstr{Kd,...} => (r ref_occurs_in Kd) env
          | _ => false

      fun rank_unify n r1 r2 (env as (renv,kenv)) =
        let val (renv', result) = Prerank.safe_unify n r1 r2 renv
        in ((renv',kenv), result)
        end

      fun rank_unify_le n r1 r2 (env as (renv,kenv)) =
        let val (renv', result) = Prerank.safe_unify_le n r1 r2 renv
        in ((renv',kenv), result)
        end

      fun no_rank_unify n r1 r2 (env as (renv,kenv)) = ((renv,kenv), SOME())

in
fun safe_bind n unify r value (env as (renv,kenv)) =
report "Binding safely = kind" "= " n (PK(UVarkind r, locn.Loc_None)) value (fn (env as (renv,kenv)) =>
(print_safe_env n kenv;
  case Lib.assoc1 r kenv
   of SOME (_, v) => unify (THEK v) value env
    | NONE =>
        if (r ref_equiv value) env then ok env else
        if (r ref_occurs_in value) env orelse isSomeK (!r) then fail env
        else ((renv,(r, SOMEK value)::kenv), SOME ())
)) env

val safe_unify = gen_unify rank_unify rank_unify rank_unify safe_bind "= "
val safe_unify_le = gen_unify rank_unify rank_unify_le rank_unify safe_bind "<="
val safe_conty_unify = gen_unify rank_unify no_rank_unify no_rank_unify safe_bind "=?"
end

(* needs changing *)
fun apply_subst subst (pk as PK (pkd, locn)) =
  case pkd of
    Varkind _ => pk
  | Typekind _ => pk
  | Arrowkind(kd1, kd2) => PK (Arrowkind(apply_subst subst kd1, apply_subst subst kd2), locn)
  | KdRankConstr{Kd=kd,Rank=rk} => PK (KdRankConstr{Kd=apply_subst subst kd,Rank=rk}, locn)
  | UVarkind (ref (SOMEK k)) => apply_subst subst k
  | UVarkind (r as ref (NONEK _)) =>
      case (Lib.assoc1 r subst) of
        NONE => pk
      | SOME (_, value) => apply_subst subst value

(*---------------------------------------------------------------------------*
 * Passes over a kind, turning all of the kind variables into fresh          *
 * UVarkinds, but doing so consistently by using an env, which is an alist   *
 * from variable names to kind variable refs.                                *
 *---------------------------------------------------------------------------*)

(* in (m1 >>- f), m1 is a monad on rank environments,
    while f is a function that takes a rank and produces
    a monad on a pair of (rank environment, kind environment).
*)
infix >>-
fun (m1 >>- f) (env as (rkenv,kdenv)) = let
  val (rkenv0, res0) = m1 rkenv
in
  case res0 of
    NONE => ((rkenv0,kdenv), NONE)
  | SOME res => f res (rkenv0,kdenv)
end

local
  val rename_rv = Prerank.rename_rv
  fun rename_rv_new rk rkenv =
    let val (_, result) = rename_rv rk []
    in (rkenv, result)
    end
  fun replace (s,rk) (env as (rkenv,kdenv)) =
        case Lib.assoc1 s kdenv
         of NONE =>
              let val (rkenv', srk') = rename_rv_new rk rkenv
                  val rk' = case srk' of SOME rk' => rk' | NONE => rk
                  val r = new_uvar rk'
              in ((rkenv,(s, r)::kdenv), SOME r)
              end
          | SOME (_, r) => (env, SOME r)
in
fun rename_kv avds (kd as PK(kd0, locn)) =
  case kd0 of
    Typekind rk =>
       rename_rv rk >>- (fn rk' =>
       return (PK(Typekind rk', locn)))
  | Varkind (s,rk) =>
       if mem s avds then (rename_rv rk >>- (fn rk' => return (PK(Varkind(s,rk'), locn))))
       else replace (s,rk)
(*
       rename_rv rk >>- (fn rk' =>
       if mem s avds then return (PK(Varkind(s,rk'), locn)) else replace (s,rk'))
*)
  | Arrowkind (kd1, kd2) =>
      rename_kv avds kd1 >- (fn kd1' =>
      rename_kv avds kd2 >- (fn kd2' =>
      return (PK(Arrowkind(kd1', kd2'), locn))))
  | KdRankConstr{Kd=kd,Rank=rk} =>
      rename_rv rk >>- (fn rk' =>
      rename_kv avds kd >- (fn kd' =>
      return (PK(KdRankConstr{Kd=kd',Rank=rk'}, locn))))
  | UVarkind (r as ref (SOMEK kd)) =>
      rename_kv avds kd >- (fn kd' =>
      (r := SOMEK kd'; return (PK(UVarkind r, locn))))
  | UVarkind (r as ref (NONEK rk)) =>
      rename_rv rk >>- (fn rk' =>
      (r := NONEK rk'; return (PK(UVarkind r, locn))))
(* | _ => return kd *)

fun rename_kindvars avds kd = valOf (#2 (rename_kv avds kd ([],[])))
end

fun fromKind k =
  if Kind.is_var_kind k then let
      val (s,rk) = Kind.dest_var_kind k
    in
      PK(Varkind (s,Prerank.fromRank rk), locn.Loc_None)
    end
  else if Kind.is_type_kind k then
    PK(Typekind (Prerank.fromRank (Kind.dest_type_kind k)), locn.Loc_None)
  else (* if Kind.is_opr_kind k then *) let
      val (kd1, kd2) = Kind.kind_dom_rng k
    in
      PK(Arrowkind(fromKind kd1, fromKind kd2), locn.Loc_None)
    end
  (* else raise TCERR "fromKind" "Unexpected sort of kind" *)

fun remove_made_links (kd as PK(kd0,locn)) =
  case kd0 of
    UVarkind(ref (SOMEK kd')) => remove_made_links kd'
  | UVarkind(ref (NONEK rk)) => PK(UVarkind(ref (NONEK (Prerank.remove_made_links rk))), locn)
  | Typekind rk => PK(Typekind (Prerank.remove_made_links rk), locn)
  | Varkind(s,rk) => PK(Varkind(s,Prerank.remove_made_links rk), locn)
  | Arrowkind(kd1, kd2) => PK(Arrowkind(remove_made_links kd1, remove_made_links kd2), locn)
  | KdRankConstr{Kd=kd',Rank=rk} => PK(KdRankConstr{Kd=remove_made_links kd',
                                                    Rank=Prerank.remove_made_links rk}, locn)

val kindvariant = Lexis.gen_variant Lexis.tyvar_vary

(* needs changing *)
fun generate_new_name r rk (renv,used_so_far) =
  let val result = kindvariant used_so_far "'a"
      val _ = r := SOMEK (PK(Varkind (result,rk), locn.Loc_None))
  in
    ((renv,result::used_so_far), SOME ())
  end

(* If kind inference did not define these kinds, *)
(* then set them to the default kind, ty:rk.     *)
fun set_null_to_default r rk env =
  let val _ = r := SOMEK (typ rk)
  in
    (env, SOME ())
  end

fun rank_replace_null_links rk (renv,kenv) =
    let val (renv', result) = Prerank.replace_null_links rk renv
    in ((renv',kenv), result)
    end

fun var_rank_replace_null_links rk (renv,kenv) =
    let val (renv', result) = Prerank.var_replace_null_links rk renv
    in ((renv',kenv), result)
    end

(* eta-expansion (see "env" after end below) *is* necessary *)
fun replace_null_links (PK(kd,_)) env = let
in
  case kd of
    UVarkind (r as ref (NONEK rk)) => rank_replace_null_links rk >>
                                      (* generate_new_name r rk *) set_null_to_default r rk
  | UVarkind (ref (SOMEK kd)) => replace_null_links kd
  | Arrowkind (kd1,kd2) => replace_null_links kd1 >> replace_null_links kd2 >> ok
  | Varkind (s,rk) => rank_replace_null_links rk >> ok
  | Typekind rk => rank_replace_null_links rk >> ok
  | KdRankConstr {Kd,Rank} => replace_null_links Kd >> rank_replace_null_links Rank >> ok
end env

(* eta-expansion (see "env" after end below) *is* necessary *)
fun var_replace_null_links (PK(kd,_)) env = let
in
  case kd of
    UVarkind (r as ref (NONEK rk)) => var_rank_replace_null_links rk >>
                                      (* generate_new_name r rk *) set_null_to_default r rk
  | UVarkind (ref (SOMEK kd)) => var_replace_null_links kd
  | Arrowkind (kd1,kd2) => var_replace_null_links kd1 >> var_replace_null_links kd2 >> ok
  | Varkind (s,rk) => var_rank_replace_null_links rk >> ok
  | Typekind rk => var_rank_replace_null_links rk >> ok
  | KdRankConstr {Kd,Rank} => var_replace_null_links Kd >> var_rank_replace_null_links Rank >> ok
end env

fun clean (PK(ty, locn)) =
  case ty of
    Varkind (s,rk) => Kind.mk_var_kind (s,Prerank.clean rk)
  | Typekind rk => Kind.typ (Prerank.clean rk)
  | Arrowkind(kd1,kd2) => Kind.==>(clean kd1, clean kd2)
  | KdRankConstr {Kd,Rank} => clean Kd
  | _ => raise Fail "Don't expect to see links remaining at this stage of kind inference"

fun toKind kd =
  let val _ = replace_null_links kd ((),kindvars kd)
  in
    clean (remove_made_links kd)
  end

fun chase (PK(Arrowkind(_, kd), _)) = kd
  | chase (PK(UVarkind(ref (SOMEK kd)), _)) = chase kd
  | chase (PK(KdRankConstr{Kd,Rank}, _)) = chase Kd
  | chase _ = raise Fail "chase applied to non-arrow kind"



(*---------------------------------------------------------------------------
 * Kind inference for HOL types. Looks ugly because of error messages, but is
 * actually very simple, given side-effecting unification.
 *---------------------------------------------------------------------------*)

fun is_atom0 (Varkind _) = true
  | is_atom0 (Typekind _) = true
  | is_atom0 (KdRankConstr{Kd,...}) = is_atom Kd
  | is_atom0 (UVarkind (r as ref (NONEK _))) = false
  | is_atom0 (UVarkind (r as ref (SOMEK kd))) = is_atom kd
  | is_atom0 kd = false
and is_atom (PK(pkd,locn)) = is_atom0 pkd



local
  fun default_kdprinter x = "<kind>"
  fun Locn (PK(_,locn)) = locn
  fun throw_non_unify (e as Feedback.HOL_ERR{origin_structure,origin_function,message}) =
         if origin_structure = "Prerank" andalso
            mem origin_function ["unify","unify_le"] then ()
         else raise e
    | throw_non_unify e = raise e
in
fun RC printers = let
  val prk = Rank.rank_to_string
  val pkd =
      case printers
       of SOME z => z
        | NONE => default_kdprinter
  fun check (PK(Arrowkind(kd1,kd2),locn)) = (check kd1; check kd2)
    | check (PK(KdRankConstr{Kd,Rank},locn)) =
       (check Kd; Prerank.unify (prank_of Kd) Rank
       handle (e as Feedback.HOL_ERR{origin_structure,origin_function,message})
       => let val _ = throw_non_unify e
              val real_kind = toKind Kd
              val kd_locn = Locn Kd
              val real_rank = Prerank.toRank Rank
              val message =
                  String.concat
                      [
                       "\nRank inference failure: the kind\n\n",
                       pkd real_kind,
                       "\n\n"^locn.toString kd_locn^"\n\n",
                       if (is_atom Kd) then ""
                       else ("which has rank " ^
                             prk(Kind.rank_of real_kind) ^ "\n\n"),

                       "can not be constrained to be of rank ",
                       prk real_rank,
                       "\n\n",

                       "rank unification failure message: ", message, "\n"]
          in
            rcheck_say message;
            last_rcerror := SOME ( (if origin_function = "unify" then KdRankConstrFail
                                                                 else KdRankLEConstrFail)
                                   (real_kind, real_rank), kd_locn);
            raise ERRloc "rankcheck" locn "failed"
          end)
    | check _ = ()
in check
end end;

val checkrank = RC

fun rankcheck pfns pkd = let
  val _ = RC pfns pkd
in
  toKind pkd
end


fun remove_kd_aq t =
  if parse_kind.is_kd_antiq t then parse_kind.dest_kd_antiq t
  else raise mk_HOL_ERR "Parse" "kind parser" "antiquotation is not of a kind"

fun remove_kd_ty_aq t =
  if parse_kind.is_kd_ty_antiq t then parse_kind.dest_kd_ty_antiq t
  else raise mk_HOL_ERR "Parse" "kind parser" "antiquotation is not of a kind"

(* "qkindop" refers to "qualified" kind operator, i.e., qualified by theory name. *)

fun kindop_to_qkindop ((kindop,locn), args) =
  if kindop = "ty" then
    if null args then PK(Typekind (Prerank.new_uvar()),locn)
    else raise mk_HOL_ERRloc "Parse" "kind parser" locn
                             (kindop ^ " is given arguments")
  else if kindop = "=>" then
    if length args = 2 then PK(Arrowkind(hd args, hd(tl args)), locn)
    else raise mk_HOL_ERRloc "Parse" "kind parser" locn
                             (kindop ^ " is not given exactly two arguments")
  else raise mk_HOL_ERRloc "Parse" "kind parser" locn
                           (kindop ^ " not a known kind operator")

fun do_qkindop {Thy:string, Kindop, Locn:locn.locn, Args} =
    kindop_to_qkindop ((Kindop,Locn), Args)

fun arity ((s, locn), n) = mk_arity n

fun mk_basevarkd((s,rk),locn) = PK(Varkind (s, rk), locn)

fun mk_basetypekd(rk,locn) = PK(Typekind rk, locn)

fun kd_rankcast {Kd,Rank,Locn} =
  PK(KdRankConstr {Kd=Kd,Rank=Rank}, Locn)

(* val kind_p0_rec *)
val termantiq_constructors =
    {varkind = mk_basevarkd, typekind = mk_basetypekd,
     qkindop = do_qkindop, kindop = kindop_to_qkindop,
     arity = arity, rankcast = kd_rankcast,
     antiq = fn x => fromKind (remove_kd_ty_aq x)}

(* kind_p1_rec *)
val typeantiq_constructors =
    {varkind = mk_basevarkd, typekind = mk_basetypekd,
     qkindop = do_qkindop, kindop = kindop_to_qkindop,
     arity = arity, rankcast = kd_rankcast,
     antiq = fn x => fromKind (remove_kd_aq x)}

(* kind_p2_rec *)
val kindantiq_constructors =
    {varkind = mk_basevarkd, typekind = mk_basetypekd,
     qkindop = do_qkindop, kindop = kindop_to_qkindop,
     arity = arity, rankcast = kd_rankcast,
     antiq = fromKind}

end;
