structure Prerank :> Prerank =
struct

open HolKernel List optmonad;
infix >> >-;

val debug = ref 0
val _ = Feedback.register_trace("debug_type_inference", debug, 5)
fun is_debug() = (!debug) >= 4;

(* must be between 0 and 4, inclusive;
     0 - no tracing of type inference
     1 - trace checking of preterms
     2 - also trace checking of pretypes and type inference
     3 - also trace checking of prekinds and kind inference
     4 - also trace checking of preranks and rank inference
   Replaces "debug_preterm", "debug_pretype, "debug_prekind", and "debug_prerank".
*)

val TCERR = mk_HOL_ERR "Prerank";

datatype prerank
    = Zerorank
    | Sucrank of prerank
    | Maxrank of prerank list
    | UVarrank of (order * prerank) option ref

type oprerank = order * prerank

(* In UVarrank, if the order is EQUAL then the UVarrank is equal to the contained rank;
   if the order is LESS then the UVarrank is less than or equal to the contained rank, or
   if the order is GREATER then the UVarrank is greater than or equal to the contained rank. *)

fun leq rk rk' = Portable.pointer_eq(rk,rk') orelse leq0 rk rk'
and leq0 rk                       (UVarrank (ref(SOME (EQUAL,rk'))))    = leq rk rk'
  | leq0 (UVarrank (ref(SOME (EQUAL,rk))))  rk'                         = leq rk rk'
(*| leq0 (UVarrank (ref(SOME (LESS, rk))))  rk'                         = leq rk rk'*)
  | leq0 (Zerorank)                     _                               = true
  | leq0 (Sucrank rk)                   (Sucrank rk')                   = leq rk rk'
  | leq0 (Maxrank rks)                  rk                              = all (geq rk) rks
  | leq0 rk                             (Maxrank rks)                   = exists (leq rk) rks
  | leq0 (rk as UVarrank (r as ref _))  (UVarrank (r' as ref(SOME (GREATER,rk')))) = r=r' orelse leq rk rk' (* ? *)
  | leq0 (UVarrank (r as ref _))        (UVarrank (r' as ref _))        = r=r'
  | leq0 rk                       (UVarrank (ref(SOME (GREATER,rk'))))  = leq rk rk' (* ? *)
(*| leq0 rk                       (UVarrank (ref(SOME (LESS,rk'))))     = leq rk Zerorank *)
(*| leq0 (UVarrank (ref(SOME (GREATER,rk))))  rk'                       = false *)
  | leq0 rk                             (Sucrank rk')                   = leq rk rk' (* a hope *)
  | leq0 _                              _                               = false

and geq rk rk' = leq rk' rk

fun eq rk rk' = Portable.pointer_eq(rk,rk') orelse eq0 rk rk'
and eq0 (UVarrank (ref(SOME (EQUAL,rk))))  rk'                         = eq rk rk'
  | eq0 rk                         (UVarrank (ref(SOME (EQUAL,rk'))))  = eq rk rk'
  | eq0 (Zerorank)                     (Zerorank)                      = true
  | eq0 (Sucrank rk)                   (Sucrank rk')                   = eq rk rk'
  | eq0 (rk as Maxrank rks)            rk'                             =
           leq rk rk' andalso (exists (eq rk') rks)
  | eq0 rk                             (rk' as Maxrank rks)       =
           leq rk' rk andalso (exists (eq rk') rks)
  | eq0 (UVarrank (r as ref _))        (UVarrank (r' as ref _))        = r=r'
(*| eq0 (UVarrank (ref(SOME (_,rk))))  rk'                             = false *)
(*| eq0 rk                          (UVarrank (ref(SOME (_,rk'))))     = false *)
  | eq0 _                              _                               = false

(* ----------------------------------------------------------------------
    A total ordering on preranks.
    UVarrank(NONE) < UVarrank(SOME) < Zerorank < Sucrank < Maxrank
   ---------------------------------------------------------------------- *)

fun order_compare (LESS   ,LESS   ) = EQUAL
  | order_compare (LESS   , _     ) = LESS
  | order_compare (EQUAL  ,LESS   ) = GREATER
  | order_compare (EQUAL  ,EQUAL  ) = EQUAL
  | order_compare (EQUAL  , _     ) = LESS
  | order_compare (GREATER,GREATER) = EQUAL
  | order_compare (GREATER, _     ) = GREATER

(* fun refbool_compare (r1 as ref b1, r2 as ref b2) = bool_compare (b1,b2) *)

local
val r2i = Portable.ref_to_int
in
fun prerank_compare (UVarrank (r1 as ref NONE), UVarrank (r2 as ref NONE)) = Int.compare(r2i r1, r2i r2)
  | prerank_compare (UVarrank (ref NONE),       _)                         = LESS
  | prerank_compare (UVarrank (ref (SOME _)),   UVarrank (ref NONE))       = GREATER
  | prerank_compare (UVarrank (r1 as ref (SOME _)),  UVarrank (r2 as ref (SOME _))) = Int.compare(r2i r1, r2i r2)
(*| prerank_compare (UVarrank (ref (SOME p1)),  UVarrank (ref (SOME p2)))  =
                                             Lib.pair_compare(order_compare,prerank_compare)(p1,p2) *)
  | prerank_compare (UVarrank (ref (SOME _)),   _)                         = LESS
  | prerank_compare (Zerorank,                  Zerorank)                  = EQUAL
  | prerank_compare (Zerorank,                  UVarrank _)                = GREATER
  | prerank_compare (Zerorank,                  _)                         = LESS
  | prerank_compare (Sucrank rk1,               Sucrank rk2)               = prerank_compare(rk1,rk2)
  | prerank_compare (Sucrank _,                 Maxrank _)                 = LESS
  | prerank_compare (Sucrank _,                 _)                         = GREATER
  | prerank_compare (Maxrank l1,                Maxrank l2)                =
                                             Lib.list_compare(prerank_compare)(l1,l2)
  | prerank_compare (Maxrank _,                 _)                         = GREATER
end

fun new_uvar () = UVarrank(ref NONE)

(*fun new_var_uvar () = UVarrank(ref (SOME (GREATER, TheVarrank)))*)
(*fun new_var_uvar () = UVarrank(ref NONE)*)

fun reset_rank_uvars (UVarrank (r as ref(SOME _))) = (r := NONE)
  | reset_rank_uvars (Sucrank rk) = reset_rank_uvars rk
  | reset_rank_uvars (Maxrank rks) = List.app reset_rank_uvars rks
  | reset_rank_uvars _ = ()

fun is_con_rank (Zerorank) = true
  | is_con_rank (Sucrank rk) = is_con_rank rk
  | is_con_rank _ = false

fun is_undef_uvar (UVarrank (ref NONE)) = true
  | is_undef_uvar (UVarrank (ref (SOME (EQUAL, rk)))) = is_undef_uvar rk
  | is_undef_uvar _ = false

fun is_uvar (UVarrank _) = true
  | is_uvar _ = false

fun con_rank (Zerorank) = 0
  | con_rank (Sucrank rk) = con_rank rk + 1
  | con_rank _ = raise TCERR "con_rank" "not a simple constant rank";

fun flatten_ge_rank (Maxrank rks) = flatten_ge_rank_list rks
  | flatten_ge_rank (UVarrank (ref (SOME (EQUAL, rk)))) = flatten_ge_rank rk (* experimental *)
  | flatten_ge_rank (UVarrank (ref (SOME (GREATER, rk)))) = flatten_ge_rank rk (* experimental *)
  | flatten_ge_rank rk = [rk]

and flatten_ge_rank_list (rk::rks) = flatten_ge_rank rk @ flatten_ge_rank_list rks
  | flatten_ge_rank_list [] = []

fun shrink_ge_list [] = []
  | shrink_ge_list (rk::rks) =
      let val rk' = shrink_ge_rank rk
          val rks' = shrink_ge_list rks
      in if exists (leq rk') rks' then rks'
         else rk' :: filter (not o geq rk') rks'
      end

and shrink_ge_rank (Maxrank rks) =
      let
      in
        case shrink_ge_list (flatten_ge_rank_list rks) of
           [] => Zerorank
         | [rk] => rk
         | rks' => Maxrank rks'
      end
  | shrink_ge_rank (Sucrank rk) = Sucrank (shrink_ge_rank rk)
  | shrink_ge_rank (UVarrank (ref (SOME (EQUAL, rk)))) = shrink_ge_rank rk (* experimental *)
  | shrink_ge_rank (UVarrank (ref (SOME (GREATER, rk)))) = shrink_ge_rank rk (* experimental *)
  | shrink_ge_rank rk = rk

fun flatten_rank (Maxrank rks) = flatten_rank_list rks
  | flatten_rank (UVarrank (ref (SOME (EQUAL, rk)))) = flatten_rank rk (* experimental *)
  | flatten_rank rk = [rk]

and flatten_rank_list (rk::rks) = flatten_rank rk @ flatten_rank_list rks
  | flatten_rank_list [] = []

fun shrink_list [] = []
  | shrink_list (rk::rks) =
      let val rk' = shrink_rank rk
          val rks' = shrink_list rks
      in if exists (leq rk') rks' then rks'
         else rk' :: filter (not o geq rk') rks'
      end

and shrink_rank (Maxrank rks) =
      let
      in
        case shrink_list (flatten_rank_list rks) of
           [] => Zerorank
         | [rk] => rk
         | rks' => Maxrank rks'
      end
  | shrink_rank (Sucrank rk) = Sucrank (shrink_rank rk)
  | shrink_rank (UVarrank (ref (SOME (EQUAL, rk)))) = shrink_rank rk (* experimental *)
(*
  | shrink_rank (rk as UVarrank (ref (SOME (GREATER, rk1)))) =
      let val rk1' = shrink_ge_rank rk1
      in (*if eq rk1' rk1 then rk
         else*) UVarrank (ref (SOME (GREATER, rk1'))) (* makes a new variable; safer than := ? *)
      end
*)
  | shrink_rank rk = rk

fun mk_Maxrank (rk1,rk2) = shrink_rank (Maxrank [rk1,rk2]);

(*val shrink_ge_rank = shrink_rank*)
fun mk_ge_Maxrank (rk1,rk2) = shrink_ge_rank (Maxrank [rk1,rk2]);

fun delete_rank rks rk =
  case (op_subtract eq rks [rk]) of
     [] => Zerorank
   | [rk] => rk
   | rks => Maxrank rks

fun prerank_to_string0 rs (UVarrank (r as ref NONE)) =
      "?" ^ Int.toString(Portable.ref_to_int r)
  | prerank_to_string0 rs (UVarrank (r as ref(SOME (ord,rk)))) =
      Int.toString(Portable.ref_to_int r) ^
      (if mem r rs then ":*" else
         (": " ^ (if ord = EQUAL then "=" else if ord = GREATER then ">=" else "<=")
               ^ prerank_to_string0 (r::rs) rk))
  | prerank_to_string0 rs (Zerorank) = "0"
  | prerank_to_string0 rs (Sucrank rk) = prerank_to_string0 rs rk ^ "+1"
  | prerank_to_string0 rs (Maxrank rks) = "max(" ^ preranks_to_string0 rs rks ^ ")"

and preranks_to_string0 rs [] = ""
  | preranks_to_string0 rs (rk::rks) = prerank_to_string0 rs rk ^ ", "
                                       ^ preranks_to_string0 rs rks

and prerank_to_string rk =
         if is_con_rank rk then Int.toString(con_rank rk)
                           else prerank_to_string0 [] rk


(*------------------------------------------------------------------------------*
 * Passes over a rank, turning the (sole) rank variable into a fresh UVarrank.  *
 * That variable is modeled by Zerorank.                                        *
 *------------------------------------------------------------------------------*)

local fun replace env =
        case env
         of [] =>
              let val r = new_uvar()
              in ([r], SOME r)
              end
(*
          | (r :: _) => (env, SOME r)
*)
          | [r] => (env, SOME r)
          | _ => raise TCERR "rename_rv" "extended rank environment"
in
fun rename_rv rk =
  case rk of
    Zerorank => replace
  | Sucrank (rk1) =>
      rename_rv rk1 >- (fn rk1' =>
      return (Sucrank (rk1')))
  | Maxrank rks =>
      mmap rename_rv rks >- (fn rks' =>
      return (Maxrank rks'))
  | _ => return rk

fun rename_rankvars rk = valOf (#2 (rename_rv rk []))
end

local open Kind
  fun mk_Suc 0 rk = rk
    | mk_Suc i rk = mk_Suc (i-1) (Sucrank rk)
in
fun fromRank rk = mk_Suc rk Zerorank
end

fun uvars_of rk =
    case rk of
      UVarrank (ref (SOME (EQUAL,rk'))) => uvars_of rk'
    | UVarrank r => [r]
    | Sucrank rk => uvars_of rk
    | Maxrank rks => foldr (fn (rk,s) => Lib.union(uvars_of rk)s) [] rks
(* or, Lib.itlist (fn rk => fn s => Lib.union(uvars_of rk,s)) rks [] *)
    | _ => []

fun refstring r = Int.toString (Portable.ref_to_int r)

(* ref_occurs_in does not look under LESS *)
fun ref_occurs_in0 rs r value =
  case value of
    Zerorank   => false
  | Sucrank rk => ref_occurs_in0 rs r rk
  | Maxrank rks => exists (ref_occurs_in0 rs r) rks
  | UVarrank (r' as ref NONE) => r = r'
  | UVarrank (r' as ref (SOME (EQUAL,rk))) => r = r' orelse
                       ( not (mem r' rs) andalso ref_occurs_in0 (r'::rs) r rk )
  | UVarrank (r' as ref (SOME (GREATER,rk))) => r = r' orelse
                       ( not (mem r' rs) andalso ref_occurs_in0 (r'::rs) r rk )
  | UVarrank (r' as ref (SOME (_,rk))) => r = r'

infix ref_occurs_in
fun r ref_occurs_in value = ref_occurs_in0 [] r value

(* ref_occurs_in_all looks everywhere, including under LESS *)
infix ref_occurs_in_all
fun ref_occurs_in_all0 rs r value =
  case value of
    Zerorank   => false
  | Sucrank rk => ref_occurs_in_all0 rs r rk
  | Maxrank rks => exists (ref_occurs_in_all0 rs r) rks
  | UVarrank (r' as ref NONE) => r = r'
  | UVarrank (r' as ref (SOME (_,rk))) => r = r' orelse
                       ( not (mem r' rs) andalso ref_occurs_in_all0 (r'::rs) r rk )
fun r ref_occurs_in_all value = ref_occurs_in_all0 [] r value

(* ref_occurs_in_not_top only checks if the ref r appears below the top level,
   that is, below the values being max-ed together.
   If it occurs in a link under the GREATER sign, it may be more, treat as Sucrank
   Does NOT check under LESS *)
fun ref_occurs_in_not_top0 rs r value =
  case value of
    Zerorank   => false
  | Sucrank rk => r ref_occurs_in rk
  | Maxrank rks => exists (ref_occurs_in_not_top0 rs r) rks
  | UVarrank (r' as ref NONE) => false
  | UVarrank (r' as ref (SOME (EQUAL,rk))) =>
                       ( not (mem r' rs) andalso ref_occurs_in_not_top0 (r'::rs) r rk )
  | UVarrank (r' as ref (SOME (GREATER,rk))) =>
                       ( not (mem r' rs) andalso ref_occurs_in_not_top0 (r'::rs) r rk )
  | UVarrank (r' as ref (SOME (_,rk))) => false

infix ref_occurs_in_not_top
fun r ref_occurs_in_not_top value = ref_occurs_in_not_top0 [] r value

(* ref_occurs_in_top only checks if the ref r appears at the top level,
   that is, one of the values being max-ed together, but NOT under LESS. *)
infix ref_occurs_in_top
fun r ref_occurs_in_top value =
  case value of
    Zerorank   => false
  | Sucrank rk => false
  | Maxrank rks => exists (fn rk => r ref_occurs_in_top rk) rks
  | UVarrank (r' as ref NONE) => r = r'
  | UVarrank (r' as ref (SOME (EQUAL,rk))) => r = r' orelse r ref_occurs_in_top rk
  | UVarrank (r' as ref (SOME (_,rk))) => r = r'

(* same as ref_occurs_in:
(* ref_occurs_in_not_less checks if the ref r appears anywhere except under a LESS. *)
infix ref_occurs_in_not_less
fun r ref_occurs_in_not_less value =
  case value of
    Zerorank   => false
  | Sucrank rk => r ref_occurs_in rk
  | Maxrank rks => exists (fn rk => r ref_occurs_in_not_less rk) rks
  | UVarrank (r' as ref NONE) => r = r'
  | UVarrank (r' as ref (SOME (EQUAL,rk))) => r = r' orelse r ref_occurs_in_not_less rk
  | UVarrank (r' as ref (SOME (_,rk))) => r = r'
*)

fun print_circular_rank rs r value =
  ( print "\n!!! Circular rank: ";
    print (prerank_to_string value ^ "\n") )

(* ref_occurs_in_less checks if the ref r appears under a LESS (but not a GREATER. *)
fun ref_occurs_in_less0 rs r value =
  case value of
    Zerorank   => false
  | Sucrank rk => false
  | Maxrank rks => exists (ref_occurs_in_less0 rs r) rks
  | UVarrank (r' as ref NONE) => false
  | UVarrank (r' as ref (SOME (EQUAL,rk))) =>
                       ( if mem r' rs then (print_circular_rank rs r value; false)
                                      else ref_occurs_in_less0 rs r rk )
                       (* ( not (mem r' rs) andalso ref_occurs_in_less0 rs r rk ) *)
  | UVarrank (r' as ref (SOME (LESS, rk))) =>
                       ( if mem r' rs then (print_circular_rank rs r value; false)
                                      else r ref_occurs_in_all rk )
                       (* ( not (mem r' rs) andalso r ref_occurs_in_all rk ) *)
  | UVarrank (r' as ref (SOME (_,rk))) => false

infix ref_occurs_in_less
fun r ref_occurs_in_less value = ref_occurs_in_less0 [] r value


infix ref_equiv
fun r ref_equiv value =
  case value of
    UVarrank (r' as ref NONE) => r = r'
  | UVarrank (r' as ref (SOME (EQUAL,rk))) => r = r' orelse r ref_equiv rk
  | UVarrank (r' as ref (SOME (_,rk))) => r = r'
(* | Maxrank rks => exists (fn rk => r ref_equiv rk andalso all (geq rk) rks) rks *)
  | Maxrank rks => exists (fn rk => r ref_equiv rk andalso leq (delete_rank rks rk) rk) rks
  | _ => false

(* -------------------------------------------------------------------------------------
   ref_remove deletes the uvar "r" from "value" and returns the resulting prerank.
   UVarrank(SOME) links are followed and collapsed, forgetting the order.
   No refs are assigned, so this has no side effects.
   ------------------------------------------------------------------------------------- *)
(* classic:
infix ref_remove
fun r ref_remove value =
  case value of
    UVarrank (r' as ref NONE) => if r = r' then NONE else SOME value
  | UVarrank (r' as ref (SOME (_,rk))) => if r = r' then NONE else r ref_remove rk
  | Zerorank => SOME value
  | Sucrank rk => (*SOME value*)
                  let in case r ref_remove rk
                           of NONE => NONE
                            | SOME rk' => SOME (Sucrank rk') end
  | Maxrank rks => case mapPartial (fn rk => r ref_remove rk) rks of
                      [] => NONE
                    | [rk] => SOME rk
                    | rks' => SOME (shrink_rank (Maxrank rks'))
*)

fun ref_remove0 rs r value = (* experimental; diverges? *)
  case value of
    UVarrank (r' as ref NONE) => if r = r' then NONE else SOME value
  | UVarrank (r' as ref (SOME (EQUAL,rk))) => if r = r' then NONE
                                              else if mem r' rs then SOME value (* end descent *)
                                                   else ref_remove0 (r'::rs) r rk
  | UVarrank (r' as ref (SOME (GREATER,rk))) => if r = r' then NONE
                                              else if mem r' rs then SOME value (* end descent *)
                                                   else ref_remove0 (r'::rs) r rk
  | UVarrank (r' as ref (SOME (_,rk))) => if r = r' then NONE
                                          else SOME value        (* experimental *)
  | Zerorank => SOME value
  | Sucrank rk => (*SOME value*)
                  let in case ref_remove0 rs r rk
                           of NONE => NONE
                            | SOME rk' => SOME (Sucrank rk') end
  | Maxrank rks => case mapPartial (ref_remove0 rs r) rks of
                      [] => NONE
                    | [rk] => SOME rk
                    | rks' => SOME (shrink_rank (Maxrank rks'))

infix ref_remove
fun r ref_remove value = ref_remove0 [] r value

fun ref_remove_all0 rs r value = (* experimental; shouldn't diverge *)
 (if true (*length rs < 8*) (*current_trace "kinds" < 2*) then () else
   (print ("**ref_remove_all["^Int.toString(length rs)^": ");
    () (*print (prerank_to_string value ^ "\n")*) );
  let val res =
  case value of
    UVarrank (r' as ref NONE) => if r = r' then (true, NONE) else (false, SOME value)
  | UVarrank (r' as ref (SOME (EQUAL,rk))) => if r = r' then (true, NONE)
                                              else if mem r' rs then (false, SOME value)
                                              else (true, snd (ref_remove_all0 (r'::rs) r rk))
  | UVarrank (r' as ref (SOME (GREATER,rk))) => if r = r' then (true, NONE)
                                          else if mem r' rs then (false, SOME value)
                                          else let in
                                            case ref_remove_all0 (r'::rs) r rk
                                                 of (_,NONE) => (true, NONE)
                                                  | (chgd, SOME rk') =>
                                                    (chgd, SOME (if chgd
                                                        (* then UVarrank(ref(SOME(GREATER,rk'))) *)
                                                           then rk'
                                                           else value))
                                          end (* experimental *)
  | UVarrank (r' as ref (SOME (LESS,rk))) => if r = r' then (true, NONE)
                                          else if mem r' rs then (false, SOME value)
                                          else let in
                                            case ref_remove_all0 (r'::rs) r rk
                                                 of (_,NONE) => (true, NONE)
                                                  | (chgd, SOME rk') =>
                                                    (chgd, if chgd
                                                        (* then SOME (UVarrank(ref NONE)) *)
                                                           then NONE
                                                           else SOME value)
                                          end (* experimental *)
  | Zerorank   => (false, SOME value)
  | Sucrank rk => let in case ref_remove_all0 rs r rk
                           of (_,NONE) => (true, NONE)
                            | (chgd,SOME rk') => (chgd, SOME (Sucrank rk')) end
  | Maxrank rks => let val (chgd,rks') =
                           foldl (fn (rk,(chgd,rks')) =>
                                    let val (chgd1,ork) = ref_remove_all0 rs r rk
                                    in case ork of
                                          NONE => (true, rks')
                                        | SOME rk' => (chgd orelse chgd1, rk'::rks')
                                    end
                                 ) (false,[]) rks
                   in (chgd, SOME (shrink_rank (Maxrank (rev rks'))))
                   end
  in if true (*length rs < 8*) (*current_trace "kinds" < 2*) then () else
       (print ("]\n"));
     res
  end
 )

infix ref_remove_all
fun r ref_remove_all value = snd (ref_remove_all0 [] r value)


  fun has_free_uvar prk =
    case prk of
      UVarrank (ref NONE)              => true
    | UVarrank (ref (SOME (EQUAL,rk))) => has_free_uvar rk
    | UVarrank (ref (SOME (_,rk)))     => true
    | Zerorank                         => false
    | Sucrank rk                       => has_free_uvar rk
    | Maxrank rks                      => exists has_free_uvar rks


fun reportd d s cmp n rk1 rk2 m e =
  let fun spaces n = if n = 0 then "" else ("  " ^ spaces(n-1))
      (* fun is_debug () = (!debug) >= d *)
      val _ = if not (is_debug()) then () else
          print ("\n" ^ spaces n ^ "(" ^ s ^ ": " ^ prerank_to_string rk1 ^ "\n" ^
                 spaces n ^ "to be " ^ cmp ^ "     vs: " ^ prerank_to_string rk2 ^ "\n")
      val (e',result) = m e
  in if not (is_debug()) then () else
          print ("\n" ^ spaces n ^ ")" ^ s ^ ": " ^ prerank_to_string rk1 ^ "\n" ^
                 spaces n ^ "to be " ^ cmp ^ "     vs: " ^ prerank_to_string rk2 ^ "\n" ^
                 spaces n ^ (case result
                               of NONE => "failed"
                                | SOME() => "succeeded") ^ "\n");
(*
     case result
       of NONE => if not (is_debug()) then () else
                  (print ("\n" ^ spaces n ^ ")" ^ s ^ " failed for\n" ^ spaces n);
                   print (prerank_to_string rk1 ^ " compared to " ^ cmp ^ "\n" ^ spaces n);
                   print (prerank_to_string rk2 ^ "\n"))
      | SOME() => if not (is_debug()) then () else
                  (print ("\n" ^ spaces n ^ ")" ^ s ^ " succeeded for\n" ^ spaces n);
                   print (prerank_to_string rk1 ^ " compared to " ^ cmp ^ "\n" ^ spaces n);
                   print (prerank_to_string rk2 ^ "\n"));
*)
      (e',result)
  end

fun report  s cmp n rk1 rk2 m e = reportd 1 s cmp n rk1 rk2 m e
fun report2 s cmp n rk1 rk2 m e = trace ("debug_type_inference",3) (reportd 2 s cmp n rk1 rk2 m) e


(* For unsafe_bind_top_not_equal_to_equal, f should be unify and fle should be unify_le*)
fun unsafe_bind_top_not_equal_to_equal f fle n r value =
  let val unsafe_bind_top_not_equal_to_equal = unsafe_bind_top_not_equal_to_equal f fle (n+1)
  in
report2 "Binding top <> to = " "<>2=" n (UVarrank r) value (
  case value of
    Maxrank rks => mmap (unsafe_bind_top_not_equal_to_equal r) rks >> ok
  | UVarrank (r' as ref (SOME (EQUAL,rk))) => if r' = r then ok
                                              else unsafe_bind_top_not_equal_to_equal r rk
  | UVarrank (r' as ref (SOME (GREATER,rk))) =>
                     if r' = r then ok else
                     if r ref_occurs_in_not_top rk then fail else
                     if r ref_occurs_in rk then
                         unsafe_bind_equal f fle (n+1) r' rk
(*
                         (fn acc =>
                                ((r', !r')::acc, SOME ())
                                before r' := SOME (EQUAL,rk))
*)
                         >> unsafe_bind_top_not_equal_to_equal r rk
                     else ok
  | _ => ok
)
  end

(* For unsafe_bind_equal, f should be unify and fle should be unify_le*)
and unsafe_bind_equal f fle n r value =
  let val unsafe_bind_top_not_equal_to_equal = unsafe_bind_top_not_equal_to_equal f fle (n+1)
      val f = f (n+1) and fle = fle (n+1)
  in
report "Binding = rank" "= " n (UVarrank r) value (
  if r ref_occurs_in_not_top value
  then fail
  else
  unsafe_bind_top_not_equal_to_equal r value >>
  (fn env =>
  (if r ref_occurs_in_all value
   then
     (case r ref_remove_all (*?_all?*) value
       of NONE => ok
        | SOME value' => (* no refs to r occur in value' *)
          case (!r) (* wish to ensure that remaining value' is <= r *)
             of SOME (EQUAL,value0) => fle value' value0
              | SOME (GREATER,value0) => fle value' value0
              | SOME (LESS,value0) => (fn acc =>
                                ((r, !r)::acc, SOME ())
                                before r := SOME (EQUAL,value')) >> fle value' value0
              | NONE => (fn acc => ((r, !r)::acc, SOME ())
                                   before r := SOME (GREATER,shrink_ge_rank value')))
   else (* r does not occur in value *)
     (case (!r) of (* wish to ensure that r = value *)
                SOME (EQUAL,value0) => f value0 value
              | SOME (GREATER,value0) => (fn acc =>
                                ((r, !r)::acc, SOME ())
                                before r := SOME (EQUAL,value)) >> fle value0 value
              | SOME (LESS,value0) => (fn acc =>
                                ((r, !r)::acc, SOME ())
                                before r := SOME (EQUAL,value)) >> fle value value0
              | NONE => (fn acc => ((r, !r)::acc, SOME ())
                                   before r := SOME (EQUAL,value)))
  ) env)
)
  end;


fun unsafe_bind_top_greater_to_equal f fle n r value =
  let val unsafe_bind_top_greater_to_equal = unsafe_bind_top_greater_to_equal f fle (n+1)
  in
report2 "Binding top > to = " ">2=" n (UVarrank r) value (
  case value of
    Maxrank rks => mmap (unsafe_bind_top_greater_to_equal r) rks >> ok
  | UVarrank (r' as ref (SOME (EQUAL,rk))) => if r' = r then ok
                                              else unsafe_bind_top_greater_to_equal r rk
  | UVarrank (r' as ref (SOME (GREATER,rk))) =>
                     if r' = r then ok else
                     if r ref_occurs_in rk then
                         unsafe_bind_equal f fle (n+1) r' rk
(*
                         (fn acc =>
                                ((r', !r')::acc, SOME ())
                                before r' := SOME (EQUAL,rk))
*)
                         >> unsafe_bind_top_greater_to_equal r rk
                     else ok
  | _ => ok
)
  end

(* For unsafe_bind_greater, f should be unify and fle should be unify_le *)
fun unsafe_bind_greater f fle n r value =
  let val unsafe_bind_top_greater_to_equal = unsafe_bind_top_greater_to_equal f fle (n+1)
      val f = f (n+1) and fle = fle (n+1)
  in
report "Binding > rank" ">=" n (UVarrank r) value (
  if r ref_occurs_in_not_top value
   then fail
   else
     unsafe_bind_top_greater_to_equal r value >>
     (fn env =>
     (if r ref_occurs_in_not_top value
      then fail
      else
      (case r ref_remove_all value
        of NONE => ok
         | SOME value' =>
             case (!r) of
               SOME (EQUAL,value0) => fle value' value0
             | SOME (GREATER,value0) => (* use the maximum of value0 and value' *)
                       (fn acc => ((r, !r)::acc, SOME ())
                                  before r := SOME (GREATER, mk_ge_Maxrank(value0,value')))
             | SOME (LESS,value0) => if eq value' Zerorank then ok else
                      ((fn acc => (* Interval [value' .. value0], choose value' unless 0 *)
                                  ((r, !r)::acc, SOME ())
                                  before r := SOME (EQUAL, value'))
                                >> fle value' value0)
             | NONE => (fn acc => ((r, !r)::acc, SOME ())
                                  before r := SOME (GREATER, shrink_ge_rank value'))) ) env)
)
  end;

(* For unsafe_bind_less, f should be unify_le *)
fun unsafe_bind_less f n r value =
  let val f = f (n+1)
  in
report "Binding < rank" "<=" n (UVarrank r) value (
  if r ref_occurs_in_all (*?_all*) value
  then ok
  else (* no refs to r occur in value *)
      case (!r) of
                SOME (EQUAL,value0) => f value0 value (* the new value must be greater *)
              | SOME (GREATER,value0) => (* Interval [value0 .. value], choose value0 unless = 0 *)
                                       if eq value0 Zerorank then (fn acc => (* forget value0 *)
                                            (((r, !r)::acc, SOME ())
                                            before r := SOME (LESS, value)))
                                       else (fn acc =>
                                            ((r, !r)::acc, SOME ())
                                            before r := SOME (EQUAL, value0)) >> f value0 value
              | SOME (LESS,value0) => (* use the minimum of value0 and value *)
                                      if leq value0 value then ok
                                      else if leq value value0 then (fn acc =>
                                            ((r, !r)::acc, SOME ())
                                            before r := SOME (LESS, value))
                                      else (* value0 and value cannot be compared at present *)
                                           f value0 value (* guess and check that the new value is greater *)
              | NONE => (fn acc => if eq value Zerorank then
                                   (((r, !r)::acc, SOME ())
                                    before r := SOME (EQUAL, value))
                                   else
                                   (((r, !r)::acc, SOME ())
                                    before r := SOME (LESS, value)))
)
  end;


(* first argument is a function which performs a binding between a
   pretype reference and another pretype, updating some sort of environment
   (the 'a), returning the new alpha and a unit option, SOME () for a
   success, and a NONE, if not.

   To further complicate things, the bind argument also gets a copy of
   gen_unify to call, if it should choose.
*)
(* this will need changing *)
(* eta-expansion *is* necessary *)

(* This rank unification is NOT SYMMETRIC!! *)
(* The first rank is made to be less than or equal to the second rank. *)
fun gen_unify_le bind_equal bind_less bind_greater n rk1 rk2 (e:'a) = let
  val gen_unify_le   = gen_unify_le bind_equal bind_less bind_greater
  val gen_unify      = gen_unify bind_equal bind_less bind_greater
  val gen_unify_le_1 = gen_unify_le (n+1)
  val gen_unify_1    = gen_unify (n+1)
in
report "Unifying ranks" "<=" n rk1 rk2 (
  if not (eq rk1 Zerorank) andalso leq rk1 rk2 then ok
  else
  case (rk1, rk2) of
    (UVarrank r1, UVarrank r2) =>
          if r2 ref_occurs_in_less rk1
            then bind_less gen_unify_le (n+1) r1 rk2
            else bind_greater gen_unify gen_unify_le (n+1) r2 rk1
  | (_, UVarrank r) => bind_greater gen_unify gen_unify_le (n+1) r rk1
  | (UVarrank r, _) => bind_less gen_unify_le (n+1) r rk2
  | (Maxrank rs, _) => mmap (C gen_unify_le_1 rk2) (rev rs) >> ok
  | (Zerorank, _) => ok
  | (Sucrank rk1, Sucrank rk2) => gen_unify_le_1 rk1 rk2
  | (_, Maxrank rs) => tryall (gen_unify_le_1 rk1) (rev (shrink_list rs))
  | _ => fail
)
end e

(* This rank unification is SYMMETRIC!! *)
(* The first rank is made to be equal to the second rank. *)
(* Note that gen_unify and gen_unify_le are mutually recursive. *)
and gen_unify bind_equal bind_less bind_greater n rk1 rk2 e = let
  val gen_unify_le   = gen_unify_le bind_equal bind_less bind_greater
  val gen_unify      = gen_unify bind_equal bind_less bind_greater
  val gen_unify_le_1 = gen_unify_le (n+1)
  val gen_unify_1    = gen_unify (n+1)
in
report "Unifying ranks" "= " n rk1 rk2 (
  if not (is_undef_uvar rk1 orelse is_undef_uvar rk2)
     andalso eq rk1 rk2 then ok
  else
  case (rk1, rk2) of
    (UVarrank r1, UVarrank r2) =>
          if r2 ref_occurs_in_less rk1
            then bind_equal gen_unify gen_unify_le (n+1) r1 rk2
            else bind_equal gen_unify gen_unify_le (n+1) r2 rk1
  | (_, UVarrank r) => bind_equal gen_unify gen_unify_le (n+1) r rk1
  | (UVarrank r, _) => bind_equal gen_unify gen_unify_le (n+1) r rk2
  | (Maxrank rs, _) => (case shrink_list rs of
                          [] => gen_unify_1 Zerorank rk2
                        | [rk] => gen_unify_1 rk rk2
                        | rks => let
                            in
                              case find (geq rk2) rks of
                                 SOME rk => let val r2 = delete_rank rks rk
                                            in if eq rk rk2 then gen_unify_le_1 r2 rk2
                                                            else gen_unify_1 r2 rk2
                                            end
                               | NONE => tryall (fn r1 =>
                                                 gen_unify_1 r1 rk2 >> (fn env =>
                                                   gen_unify_le_1 (delete_rank rks r1) rk2 env))
                                                (rev rks)
                            end)
(*
                        | (r1::rs1) =>
                            let val r2 = if length rs1 = 1 then hd rs1 else Maxrank rs1
                            in
                                 if leq r1 rk2 then
                                    if eq r1 rk2 then gen_unify_le_1 r2 rk2
                                                 else gen_unify_1 r2 rk2
                            else if leq r2 rk2 then
                                    if eq r2 rk2 then gen_unify_le_1 r1 rk2
                                                 else gen_unify_1 r1 rk2
                            else ((gen_unify_1 r2 rk2 >> gen_unify_le_1 r1 rk2) ++
                                  (gen_unify_1 r1 rk2 >> gen_unify_le_1 r2 rk2))
                            end
*)
  | (Zerorank, Zerorank) => ok
  | (Sucrank rk1, Sucrank rk2) => gen_unify_1 rk1 rk2
  | (_, Maxrank rs) => (case shrink_list rs of
                          [] => gen_unify_1 rk1 Zerorank
                        | [rk] => gen_unify_1 rk1 rk
                        | rks => let
                            in
                              case find (geq rk1) rks of
                                 SOME rk => let val r2 = delete_rank rks rk
                                            in if eq rk rk1 then gen_unify_le_1 r2 rk1
                                                            else gen_unify_1 r2 rk1
                                            end
                               | NONE => tryall (fn r1 =>
                                                 gen_unify_1 r1 rk1 >> (fn env =>
                                                   gen_unify_le_1 (delete_rank rks r1) rk1 env))
                                                (rev rks)
                            end)
(*
                        | (r1::rs1) =>
                            let val r2 = if length rs1 = 1 then hd rs1 else Maxrank rs1
                            in
                                 if leq r1 rk1 then
                                    if eq r1 rk1 then gen_unify_le_1 r2 rk1
                                                 else gen_unify_1 r2 rk1
                            else if leq r2 rk1 then
                                    if eq r2 rk1 then gen_unify_le_1 r1 rk1
                                                 else gen_unify_1 r1 rk1
                            else ((gen_unify_1 rk1 r2 >> gen_unify_le_1 r1 rk1) ++
                                  (gen_unify_1 rk1 r1 >> gen_unify_le_1 r2 rk1))
                            end
*)
  | _ => fail
)
end e;

val unsafe_unify = gen_unify unsafe_bind_equal unsafe_bind_less unsafe_bind_greater
val unsafe_unify_le = gen_unify_le unsafe_bind_equal unsafe_bind_less unsafe_bind_greater

fun unify rk1 rk2 =
  case (unsafe_unify 0 rk1 rk2 [])
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify" "unify failed";

fun unify_le rk1 rk2 =
  case (unsafe_unify_le 0 rk1 rk2 [])
   of (bindings, SOME ()) => ()
    | (_, NONE) => raise TCERR "unify_le" "unify failed";

fun can_unify rk1 rk2 = let
  val (bindings, result) = unsafe_unify 0 rk1 rk2 []
  val _ = app (fn (r, oldvalue) => r := oldvalue) bindings
in
  isSome result
end

fun can_unify_le rk1 rk2 = let
  val (bindings, result) = unsafe_unify_le 0 rk1 rk2 []
  val _ = app (fn (r, oldvalue) => r := oldvalue) bindings
in
  isSome result
end

fun print_safe_env n env =
  if not (is_debug()) then (env, SOME ()) else
  let 
    (*fun clean rs ((r, ord_value)::rest) =
      if mem r rs then clean rs rest
                  else (r, ord_value)::clean (r::rs) rest
      | clean _ [] = []
    val env = clean [] env*)
    fun spaces n = if n = 0 then "" else ("  " ^ spaces(n-1))
    fun print1 (r, (ord, rk)) =
      print (Int.toString(Portable.ref_to_int r) ^ " |-> "
               ^ (case ord
                   of EQUAL   => " ="
                    | GREATER => ">="
                    | LESS    => "<=")
               ^ " " ^ prerank_to_string rk)
    fun printn (r_rk::r_rks) =
        let in
          print ("\n  " ^ spaces n);
          print1 r_rk;
          printn r_rks
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
  fun deref r env =
    case Lib.assoc1 r env
     of SOME (_, p) => SOME p
      | NONE => !r
  exception UNCHANGED
  fun add (r, value) env =
    let fun rem ((p as (r', _))::rest) =
              if r=r' then rest
              else p::rem rest
          | rem [] = raise UNCHANGED
     in (r,value) :: (rem env handle UNCHANGED => env)
     end
  fun uvar_eq f r r' env =
              r = r' orelse
              let in
                case deref r' env
                 of SOME (EQUAL,v) => f (r,v) env
                  | _ => false
              end
  fun (r ref_equiv value) env =
       case value of
         UVarrank r' => uvar_eq (op ref_equiv) r r' env
(*
         UVarrank (r' as ref NONE) => (*uvar_eq (op ref_equiv) r r' env*)
              r = r' orelse
              let in
                case Lib.assoc1 r' env
                 of NONE => false
                  | SOME (_, v) => (r ref_equiv v) env
              end
         | UVarrank (r' as ref (SOME (EQUAL,k))) => (*uvar_eq (op ref_equiv) r r' env orelse*) (r ref_equiv k) env
         | UVarrank (r' as ref (SOME (_,k))) => (*uvar_eq (op ref_equiv) r r' env*)
              r = r' orelse
              let in
                case Lib.assoc1 r' env
                 of NONE => false
                  | SOME (_, v) => (r ref_equiv v) env
              end
*)
         | Maxrank rks => exists (fn rk => (r ref_equiv rk) env andalso leq (delete_rank rks rk) rk) rks
         | _ => false

      fun (r ref_occurs_in value) env =
        case value
         of UVarrank r' => uvar_eq (op ref_occurs_in) r r' env
(*
         of UVarrank (r' as ref NONE) => (*uvar_eq (op ref_occurs_in) r r' env*)
              r = r' orelse
              let in
                case Lib.assoc1 r' env
                 of NONE => false
                  | SOME (_, (_, v)) => (r ref_occurs_in v) env
              end
          | UVarrank (r' as ref (SOME (EQUAL,  rk))) => (*uvar_eq (op ref_occurs_in) r r' env orelse*)
                                                        r=r' orelse (r ref_occurs_in rk) env
(*
          | UVarrank (r' as ref (SOME (GREATER,rk))) => (*uvar_eq (op ref_occurs_in) r r' env orelse*)
                                                        r=r' orelse (r ref_occurs_in rk) env
          | UVarrank (r' as ref (SOME (_,rk))) => (*uvar_eq (op ref_occurs_in) r r' env*) false
*)
          | UVarrank (r' as ref (SOME (_,rk))) => (*uvar_eq (op ref_occurs_in) r r' env*) (*false*)
              r = r' orelse
              let in
                case Lib.assoc1 r' env
                 of NONE => false
                  | SOME (_, (_, v)) => (r ref_occurs_in v) env
              end
*)
          | Sucrank rk => (r ref_occurs_in rk) env
          | Maxrank rks => exists (fn rk => (r ref_occurs_in rk) env) rks
          | _ => false

      fun (r ref_occurs_in_all value) env =
        case value
         of UVarrank r' =>
             r=r' orelse
             let in
               case deref r' env
                 of SOME (_,rk) => (r ref_occurs_in_all rk) env
                  | NONE => false
             end
          | Sucrank rk => (r ref_occurs_in_all rk) env
          | Maxrank rks => exists (fn rk => (r ref_occurs_in_all rk) env) rks
          | _ => false

(* ref_occurs_in_not_top only checks if the ref r appears below the top level,
   that is, below the values being max-ed together.
   If it occurs in a link under the GREATER sign, it may be more, treat as Sucrank
   Does NOT check under LESS *)
      fun (r ref_occurs_in_not_top value) env =
        case value
         of UVarrank r' =>
              let in
                case deref r' env
                 of SOME (EQUAL,   v) => (r ref_occurs_in_not_top v) env
                  | SOME (GREATER, v) => (r ref_occurs_in_not_top v) env
                  | _ => false
              end
          | Sucrank rk => (r ref_occurs_in rk) env
          | Maxrank rks => exists (fn rk => (r ref_occurs_in_not_top rk) env) rks
          | _ => false

      fun (r ref_occurs_in_top value) env =
        case value
         of UVarrank r' => uvar_eq (op ref_occurs_in_top) r r' env
          | Maxrank rks => exists (fn rk => (r ref_occurs_in_top rk) env) rks
          | _ => false

      fun (r ref_occurs_in_less value) env =
        case value
         of UVarrank r' =>
              let in
                case deref r' env
                 of SOME (EQUAL,rk) => (r ref_occurs_in_less rk) env
                  | SOME (LESS, rk) => (r ref_occurs_in_all rk) env
                  | _ => false
              end
          | Maxrank rks => exists (fn rk => (r ref_occurs_in_less rk) env) rks
          | _ => false

(* ref_remove deletes the uvar "r" from "value". *)
      fun (r ref_remove value) env =
        case value of
          UVarrank r' =>
            if r = r' then NONE
            else
              let in
                case deref r' env
                 of NONE => SOME value
                  | SOME (EQUAL, v) => (r ref_remove v) env
                  | SOME (GREATER, v) => (r ref_remove v) env
                  | SOME (LESS, v) => SOME value
              end
(*
          UVarrank (r' as ref NONE) =>
            if r = r' then NONE
            else
              let in
                case Lib.assoc1 r' env
                 of NONE => SOME value
                  | SOME (_, (EQUAL, v)) => (r ref_remove v) env
                  | SOME (_, (GREATER, v)) => (r ref_remove v) env
                  | SOME (_, (_, v)) => SOME value
              end
        | UVarrank (r' as ref (SOME (EQUAL,rk))) => if r = r' then NONE else (r ref_remove rk) env
        | UVarrank (r' as ref (SOME (ord,rk))) =>
            if r = r' then NONE
            else
              let in
                case Lib.assoc1 r' env
                 of NONE => (case ord of LESS => SOME value | _ => (r ref_remove rk) env)
                  | SOME (_, (EQUAL, v)) => (r ref_remove v) env
                  | SOME (_, (GREATER, v)) => (r ref_remove v) env
                  | SOME (_, (_, v)) => SOME value
              end
*)
        | Zerorank => SOME value
        | Sucrank rk =>
                  let in case (r ref_remove rk) env
                           of NONE => NONE
                            | SOME rk' => SOME (Sucrank rk') end
        | Maxrank rks =>
                  case mapPartial (fn rk => (r ref_remove rk) env) rks of
                      [] => NONE
                    | [rk] => SOME rk
                    | rks' => SOME (shrink_rank (Maxrank rks'))

infix ref_remove_all0
(* ref_remove_all0 deletes the uvar "r" from "value" even harder. *)
      fun (r ref_remove_all0 value) rs env =
        case value of
          UVarrank r' =>
            if r = r' then (true, NONE)
            else if mem r' rs then (print "ref_remove_all: LOOP ERROR\n"; (false, SOME value))
            else
              let in
                case deref r' env
                 of NONE => (false, SOME value)
                  | SOME (EQUAL, v) => (true, snd((r ref_remove_all0 v) (r'::rs) env))
                  | SOME (GREATER, v) =>
                      let in
                        case (r ref_remove_all0 v) (r'::rs) env
                         of (_, NONE) => (true, NONE)
                          | (chgd, SOME rk') =>
                            (chgd, SOME (if chgd then rk' else value))
                      end
                  | SOME (LESS, v) =>
                      let in
                        case (r ref_remove_all0 v) (r'::rs) env
                         of (_, NONE) => (true, NONE)
                          | (chgd, SOME rk') =>
                            (chgd, if chgd then NONE else SOME value)
                      end
              end
(*
          UVarrank (r' as ref NONE) =>
            if r = r' then (true, NONE)
            else if mem r' rs then (print "ref_remove_all: LOOP ERROR\n"; (false, SOME value))
            else
              let in
                case Lib.assoc1 r' env
                 of NONE => (false, SOME value)
                  | SOME (_, (EQUAL, v)) => (true, snd((r ref_remove_all0 v) (r'::rs) env))
                  | SOME (_, (GREATER, v)) =>
                      let in
                        case (r ref_remove_all0 v) (r'::rs) env
                         of (_, NONE) => (true, NONE)
                          | (chgd, SOME rk') =>
                            (chgd, SOME (if chgd then rk' else value))
                      end
                  | SOME (_, (LESS, v)) =>
                      let in
                        case (r ref_remove_all0 v) (r'::rs) env
                         of (_, NONE) => (true, NONE)
                          | (chgd, SOME rk') =>
                            (chgd, if chgd then NONE else SOME value)
                      end
              end
    (*  | UVarrank (r' as ref (SOME (EQUAL,rk))) =>
            if r = r' then (true, NONE) else (r ref_remove_all0 rk) (r'::rs) env *)
        | UVarrank (r' as ref (SOME (ord,rk))) =>
            if r = r' then (true, NONE)
            else if mem r' rs then (print "ref_remove_all: LOOP ERROR\n"; (false, SOME value))
            else
              let in
                case Lib.assoc1 r' env
                 of NONE => let in
                            case ord
                              of EQUAL => (true, snd((r ref_remove_all0 rk) (r'::rs) env))
                               | GREATER =>
                                let in
                                  case (r ref_remove_all0 rk) (r'::rs) env
                                   of (_, NONE) => (true, NONE)
                                    | (chgd, SOME rk') =>
                                      (chgd, SOME (if chgd then rk' else value))
                                end
                               | LESS =>
                                let in
                                  case (r ref_remove_all0 rk) (r'::rs) env
                                   of (_, NONE) => (true, NONE)
                                    | (chgd, SOME rk') =>
                                      (chgd, if chgd then NONE else SOME value)
                                end
                            end
                  | SOME (_, (EQUAL, v)) => (true, snd((r ref_remove_all0 v) (r'::rs) env))
                  | SOME (_, (GREATER, v)) =>
                                let in
                                  case (r ref_remove_all0 v) (r'::rs) env
                                   of (_, NONE) => (true, NONE)
                                    | (chgd, SOME rk') =>
                                      (chgd, SOME (if chgd then rk' else value))
                                end
                  | SOME (_, (LESS, v)) =>
                                let in
                                  case (r ref_remove_all0 v) (r'::rs) env
                                   of (_, NONE) => (true, NONE)
                                    | (chgd, SOME rk') =>
                                      (chgd, if chgd then NONE else SOME value)
                                end
              end
*)
        | Zerorank => (false, SOME value)
        | Sucrank rk =>
                  let in case (r ref_remove_all0 rk) rs env
                           of (_, NONE) => (true, NONE)
                            | (chgd, SOME rk') => (chgd, SOME (Sucrank rk')) end
        | Maxrank rks =>
                  let val (chgd,rks') =
                           foldl (fn (rk,(chgd,rks')) =>
                                    let val (chgd1,ork) = (r ref_remove_all0 rk) rs env
                                    in case ork of
                                          NONE => (true, rks')
                                        | SOME rk' => (chgd orelse chgd1, rk'::rks')
                                    end
                                 ) (false,[]) rks
                  in (chgd, SOME (shrink_rank (Maxrank (rev rks'))))
                  end

and (r ref_remove_all value) env = snd ((r ref_remove_all0 value) [] env)

in

fun safe_bind_top_not_equal_to_equal unify unify_le n r value env =
  let val safe_bind_top_not_equal_to_equal = safe_bind_top_not_equal_to_equal unify unify_le (n+1)
      val safe_bind_equal = safe_bind_equal unify unify_le (n+1)
      val unify = unify (n+1) and unify_le = unify_le (n+1)
  in
    case value of
      Maxrank rks => (mmap (safe_bind_top_not_equal_to_equal r) rks >> ok) env
    | UVarrank (r' as ref (SOME (EQUAL,rk))) => if r' = r then ok env
                                                else safe_bind_top_not_equal_to_equal r rk env
    | UVarrank (r' as ref (SOME (GREATER,rk))) =>
                     if r' = r then ok env else
                     if (r ref_occurs_in_not_top rk) env then fail env else
                     if (r ref_occurs_in rk) env then
                         (safe_bind_equal r' rk
                          >> safe_bind_top_not_equal_to_equal r rk) env
                     else ok env
    | _ => ok env
  end

and safe_bind_equal unify unify_le n r value env =
  let val safe_bind_top_not_equal_to_equal = safe_bind_top_not_equal_to_equal unify unify_le (n+1)
      val unify = unify (n+1) and unify_le = unify_le (n+1)
  in
(report "Binding safely = rank" "= " n (UVarrank r) value (fn env =>
(print_safe_env n env;
  if (r ref_occurs_in_not_top value) env
  then fail env
  else
  (safe_bind_top_not_equal_to_equal r value >>
    (fn env =>
      (if (r ref_occurs_in_all value) env
       then
         case (r ref_remove_all value) env
            of NONE => ok env
             | SOME value' =>  (* wish to ensure that remaining value' is <= r *)
                 case deref r env (* (!r) *)
                  of SOME (EQUAL,   v) => unify_le value' v env
                   | SOME (GREATER, v) => unify_le value' v env
                   | SOME (LESS,    v) => unify_le value' v (add (r, (EQUAL,value')) env)
                   | NONE => (add (r,(GREATER, shrink_ge_rank value')) env, SOME ())
       else (* r does not occur in value *)
            (* wish to ensure that value = r *)
                 case deref r env (* (!r) *)
                  of SOME (EQUAL,   v) => unify v value env
                   | SOME (GREATER, v) => unify_le v value (add (r, (EQUAL,value)) env)
                   | SOME (LESS,    v) => unify_le value v (add (r, (EQUAL,value)) env)
                   | NONE => (add (r, (EQUAL,value)) env, SOME ())
      ))) env
)) >> print_safe_env n) env
  end

fun safe_bind_less unify_le n r value env =
  let val unify_le = unify_le (n+1)
  in
report "Binding safely <= rank" "<=" n (UVarrank r) value (fn env =>
(print_safe_env n env;
(*
  case Lib.assoc1 r env
    of SOME (_, (EQUAL,   v)) => unify_le v value env
     | SOME (_, (GREATER, v)) => (* guess and set r to the low end of the range v..value, unless v=0 *)
                                 if eq v Zerorank then ok (add (r, (LESS,value)) env)
                                 else unify_le v value (add (r, (EQUAL,v)) env)
     | SOME (_, (LESS,    v)) => if leq v value then ok env
                                 else if leq value v
                                      then ok (add (r, (LESS,value)) env)
                                      else (* v and value cannot be compared at present *)
                                           (* guess and check that the new value is greater *)
                                           unify_le v value env
     | NONE =>
*)
  if (r ref_occurs_in_all value) env
  then ok env
  else (* no refs to r occur in value *)
        case deref r env (* (!r) *)
         of SOME (EQUAL,   v) => unify_le v value env (* the new value must be greater *)
          | SOME (GREATER, v) => (* Interval [v .. value], choose v unless = 0 *)
                                 if eq v Zerorank then ok (add (r, (LESS,value)) env)
                                 else unify_le v value (add (r, (EQUAL,v)) env)
          | SOME (LESS,    v) => (* use the minimum of v and value *)
                                 if leq v value then ok env
                                 else if leq value v
                                      then ok (add (r, (LESS,value)) env)
                                      else (* v and value cannot be compared at present *)
                                           (* guess that the new value is greater *)
                                           unify_le v value env
          | NONE              => if eq value Zerorank then ok (add (r, (EQUAL,value)) env)
                                                      else ok (add (r, (LESS, value)) env)
)) env
  end

fun safe_bind_top_greater_to_equal unify unify_le n r value env =
  let val safe_bind_top_greater_to_equal = safe_bind_top_greater_to_equal unify unify_le (n+1)
      val safe_bind_equal = safe_bind_equal unify unify_le (n+1)
  in
  case value of
    Maxrank rks => (mmap (safe_bind_top_greater_to_equal r) rks >> ok) env
  | UVarrank (r' as ref (SOME (EQUAL,rk))) => if r' = r then ok env
                                              else safe_bind_top_greater_to_equal r rk env
  | UVarrank (r' as ref (SOME (GREATER,rk))) =>
                     if r' = r then ok env else
                     if (r ref_occurs_in rk) env then
                         (safe_bind_equal r' rk
                          >> safe_bind_top_greater_to_equal r rk) env
                     else ok env
  | _ => ok env
  end

fun safe_bind_greater unify unify_le n r value env =
  let val safe_bind_top_greater_to_equal = safe_bind_top_greater_to_equal unify unify_le (n+1)
      val unify    = unify (n+1)
      val unify_le = unify_le (n+1)
  in
report "Binding safely >= rank" ">=" n (UVarrank r) value (fn env =>
(print_safe_env n env;
  if (r ref_occurs_in_not_top value) env
  then fail env
  else
    (safe_bind_top_greater_to_equal r value >>
      (fn env =>
        (if (r ref_occurs_in_not_top value) env
         then fail env
         else case (r ref_remove_all value) env
               of NONE => ok env
                | SOME value' =>
                     case deref r env
                        of SOME (EQUAL,  v) => unify_le value' v env
                         | SOME (GREATER,v) => (* use the maximum of v and value' *)
                                               ok (add (r, (GREATER, mk_ge_Maxrank(v,value'))) env)
                         | SOME (LESS,   v) => (* Interval [value' .. v], choose value' unless = 0 *)
                                               if eq value' Zerorank then ok env
                                               else unify_le value' v (add (r, (EQUAL,value')) env)
                         | NONE             => ok (add (r, (GREATER,shrink_ge_rank value')) env)
        ))) env
)) env
  end

end (*local*)


val safe_unify = gen_unify safe_bind_equal safe_bind_less safe_bind_greater
val safe_unify_le = gen_unify_le safe_bind_equal safe_bind_less safe_bind_greater

(*
fun apply_subst subst prk =
  case prk of
    Zerorank => prk
  | Sucrank rk => Sucrank (apply_subst subst rk)
  | Maxrank rks => Maxrank (map (apply_subst subst) rks)
  | UVarrank (ref (SOME (_,rk))) => apply_subst subst rk
  | UVarrank (r as ref NONE) =>
      case (Lib.assoc1 r subst) of
        NONE => prk
      | SOME (_, (_,value)) => apply_subst subst value
*)

fun remove_made_links0 refs rk =
  case rk of
    UVarrank(ref (SOME (EQUAL,rk'))) => remove_made_links0 refs rk'
  | UVarrank(r as ref (SOME (LESS,rk'))) => Zerorank (* less-than defaults to 0 *)
  | UVarrank(r as ref (SOME (_,rk'))) => (* otherwise defaults to = bound *)
        if mem r refs then Zerorank
                      else remove_made_links0 (r::refs) rk'
  | Sucrank rk' => Sucrank(remove_made_links0 refs rk')
  | Maxrank rks => Maxrank(map (remove_made_links0 refs) rks)
  | _ => rk
val remove_made_links = remove_made_links0 []

(* If rank inference did not define these ranks, *)
(* then set them to the default rank, Zerorank.  *)
(* The environment "env:unit" is not actually used. *)
fun set_null_to_default r (env:unit) =
  let val _ = r := SOME (EQUAL, Zerorank)
  in
    (env, SOME ())
  end

fun set_some_to_default (r as ref (SOME (ord,rk))) (env:unit) =
  let val _ = r := SOME (EQUAL, Zerorank)
  in
    (env, SOME ())
  end
  | set_some_to_default _ _ = raise Fail "set_some_to_default: not a SOME ref"

(* eta-expansion (see "env" after end below) *is* necessary *)
(* The environment "env" is not actually used. *)
(* The "refs" argument is a list of SOME references already seen, to prevent divergence. *)
fun replace_null_links0 refs rk env = let
in
  case rk of
    UVarrank (r as ref NONE) => set_null_to_default r
  | UVarrank (r as ref (SOME (_,rk))) =>
        if mem r refs then ok (* r depends on itself; punt! *)
                      else replace_null_links0 (r::refs) rk
  | Zerorank => ok
  | Sucrank rk1 => replace_null_links0 refs rk1
  | Maxrank rks => mmap (replace_null_links0 refs) rks >> ok
end env
val replace_null_links = replace_null_links0 []

(* eta-expansion (see "env" after end below) *is* necessary *)
(* The environment "env" is not actually used. *)
(* The "refs" argument is a list of SOME references already seen, to prevent divergence. *)
fun var_replace_null_links0 refs rk env = let
in
  case rk of
    UVarrank (r as ref NONE) => set_null_to_default r
  | UVarrank (r as ref (SOME (_,rk))) =>
        if mem r refs then ok (* r depends on itself; punt! *)
                      else var_replace_null_links0 (r::refs) rk
  | Zerorank => ok
  | Sucrank rk1 => var_replace_null_links0 refs rk1
  | Maxrank rks => mmap (var_replace_null_links0 refs) rks >> ok
end env
val var_replace_null_links = var_replace_null_links0 []

fun clean rk =
  let open Rank in
    case rk of
      Zerorank => rho
    | Sucrank rk' => suc (clean rk')
    | Maxrank rks => itlist (fn prk => fn rk => max(rk, clean prk)) rks 0
    | _ => raise Fail "Don't expect to see links remaining at this stage of rank inference"
  end

fun toRank rk =
  let val _ = replace_null_links rk ()
  in
    clean (remove_made_links rk)
  end

fun pp_prerank pps rk =
 let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val checkref = Portable.ref_to_int
     fun pp rs (Zerorank) = add_string "0"
       | pp rs (Sucrank rk) = (pp rs rk; add_string "+1")
       | pp rs (UVarrank (r as ref (SOME (order,rk)))) =
          ( add_string ((if order=LESS then "<"
                         else if order = GREATER then ">"
                         else "") ^ "= ");
            if mem r rs then add_string ("*" ^ Int.toString (checkref r))
                        else pp (r::rs) rk )
       | pp rs (UVarrank (r as ref NONE)) =
            add_string ("?" ^ Int.toString (checkref r))
       | pp rs (Maxrank rks) =
          ( add_string "max("; begin_block INCONSISTENT 0;
            pr_list (pp rs) (fn () => add_string ",") (fn () => add_break(1,0)) rks;
            end_block(); add_string ")" )
 in
   begin_block INCONSISTENT 0;
   pp [] rk;
   end_block()
 end;


fun remove_rk_aq t =
  if parse_rank.is_rk_antiq t then parse_rank.dest_rk_antiq t
  else raise mk_HOL_ERR "Parse" "rank parser" "antiquotation is not of a rank"

fun remove_rk_kd_aq t =
  if parse_rank.is_rk_kd_antiq t then parse_rank.dest_rk_kd_antiq t
  else raise mk_HOL_ERR "Parse" "rank parser" "antiquotation is not of a rank"

fun remove_rk_ty_aq t =
  if parse_rank.is_rk_ty_antiq t then parse_rank.dest_rk_ty_antiq t
  else raise mk_HOL_ERR "Parse" "rank parser" "antiquotation is not of a rank"

val mk_rank = fromRank

(* rank_p0_rec *)
val termantiq_constructors =
    {intrank = mk_rank,
     antiq = fn x => fromRank (remove_rk_ty_aq x)}

(* rank_p1_rec *)
val typeantiq_constructors =
    {intrank = mk_rank,
     antiq = fn x => fromRank (remove_rk_kd_aq x)}

(* rank_p2_rec *)
val kindantiq_constructors =
    {intrank = mk_rank,
     antiq = fn x => fromRank (remove_rk_aq x)}

(* rank_p3_rec *)
val rankantiq_constructors =
    {intrank = mk_rank,
     antiq = fromRank}

end;
