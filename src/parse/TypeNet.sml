structure TypeNet :> TypeNet =
struct

open HolKernel

fun print_type ty = Thm.debug_type ty

fun print_types [] = print "[]"
  | print_types [ty] = (print "["; print_type ty; print "]")
  | print_types (ty::tys) = (print "["; print_type ty; print_types0 tys; print "]")
and print_types0 (ty::tys) = (print ","; print_type ty; print_types0 tys)
  | print_types0 [] = ()

(*
fun to_skind kd = if is_arrow_kind kd then let
                      val (kd1,kd2) = dest_arrow_kind kd
                    in mk_arrow_kind(to_skind kd1, to_skind kd2)
                    end
                  else typ (* for both the base kind and kind variables *)
*)

datatype label = TV of int | TOP of {Thy : string, Tyop : string} | TAB | TUN

(* fun label_to_string (TV kd) = "<tyvar>" ^ (if kd=Kind.typ then "" else ":"^kind_to_string kd) *)
fun label_to_string (TV n) = "<tyvar>" ^ (if n=0 then "" else ":"^Int.toString n)
  | label_to_string (TOP{Thy,Tyop}) = Thy^"$"^Tyop
  | label_to_string TAB = "<tyabs>"
  | label_to_string TUN = "<tyuniv>"

fun labcmp p =
    case p of
      (TV n1, TV n2) => Int.compare(n1,n2)
    | (TV _, _) => LESS
    | (TOP{Thy = thy1, Tyop = op1}, TOP{Thy = thy2, Tyop = op2}) =>
        pair_compare (String.compare, String.compare) ((op1,thy1), (op2,thy2))
    | (TOP _, TV _) => GREATER
    | (TOP _, _) => LESS
    | (TAB, TUN) => LESS
    | (TAB, TAB) => EQUAL
    | (TAB, _) => GREATER
    | (TUN, TUN) => EQUAL
    | (TUN, _) => GREATER

datatype 'a N = LF of (hol_type,'a) Binarymap.dict
              | ND of (label,'a N) Binarymap.dict * (hol_type,'a) Binarymap.dict
              | EMPTY
(* redundant EMPTY constructor is used to get around value polymorphism problem
   when creating a single value for empty below *)

type 'a typenet = 'a N * int

val empty = (EMPTY, 0)

fun mkempty () = ND (Binarymap.mkDict labcmp, Binarymap.mkDict Type.compare)

fun ndest_type ty =
    if is_vartype ty then (TV (length (snd (strip_app_type ty))), [])
    else if is_con_type ty then let
        val {Thy,Tyop,Kind,Rank} = dest_thy_con_type ty
      in
        (TOP{Thy=Thy,Tyop=Tyop}, [])
      end
    else if is_app_type ty then let
        val (Opr,Args) = strip_app_type ty
        val (lab,rest) = ndest_type Opr
      in
        (lab, rest @ Args)
      end
    else if is_abs_type ty then let
        val (Bvar,Body) = dest_abs_type ty
      in
        (TAB, [Body])
      end
    else if is_univ_type ty then let
        val (Bvar,Body) = dest_univ_type ty
      in
        (TUN, [Body])
      end
    else raise Fail "TypeNet.ndest_type: unrecognized type"

fun insert ((net,sz), ty, item) = let
  val ty' = deep_beta_eta_ty ty
(*val _ = (print "\nTypeNet.insert ("; print_type ty'; print ")\n") *)
  fun newnode tys =
      case tys of
        [] => LF (Binarymap.mkDict Type.compare)
      | _ => mkempty()
  fun trav (net, tys) =
      case (net, tys) of
        (LF d, []) => ( (* print "TypeNet.insert: LF d |-"; print_type ty'; print "-> =|\n"; *)
                       LF (Binarymap.insert(d,ty',item)))
      | (LF d, tys) => trav (ND (Binarymap.mkDict labcmp, d), tys)
      | (ND (d,d0), []) => ( (* print "TypeNet.insert: ND d |-"; print_type ty'; print "-> =|\n"; *)
                            ND (d,Binarymap.insert(d0,ty',item)))
      | (ND (d,d0), ty::tys0) => let
          val (lab, rest) = ndest_type ty
       (* val _ = (print "TypeNet.insert: ND d |-"; print (label_to_string lab); print "-> ") *)
          val tys = rest @ tys0
          val n' =
             (case Binarymap.peek(d,lab) of
                NONE => ( (* print ("new node("^Int.toString (length tys)^")\n"); *) trav(newnode tys, tys))
              | SOME n => ( (* print "some node\n"; *) trav(n, tys))
             ) handle Fail s => Raise (wrap_exn "TypeNet.insert" (label_to_string lab) (Fail s))
          val d' = Binarymap.insert(d, lab, n')
        in
          ND (d',d0)
        end
      | (EMPTY, tys) => trav(mkempty(), tys)
   (* | _ => raise Fail "TypeNet.insert: catastrophic invariant failure" *)
in
  (trav(net,[ty']), sz + 1)
end

fun listItems (net, sz) = let
  fun cons'(k,v,acc) = (k,v)::acc
  fun trav (net, acc) =
      case net of
        LF d => Binarymap.foldl cons' acc d
      | ND (d,d0) => let
          fun foldthis (k,v,acc) = trav(v,acc)
        in
          Binarymap.foldl foldthis (Binarymap.foldl cons' acc d0) d
        end
      | EMPTY => []
in
  trav(net, [])
end

fun numItems (net, sz) = sz

fun peek ((net,sz), ty) = let
  val ty' = deep_beta_eta_ty ty
(*val _ = (print "\nTypeNet.peek ("; print_type ty'; print ")\n") *)
  fun trav (net, tys) =
      case (net, tys) of
        (LF d, []) => ( (* print "TypeNet.peek: LF d |-"; print_type ty'; print "-> =|\n"; *) Binarymap.peek(d, ty'))
      | (LF d, tys) => ( (* print "TypeNet.peek: LF d tys |-"; print_type ty'; print "-> =|\n"; *) Binarymap.peek(d, ty'))
      | (ND (d,d0), []) => ( (* print "TypeNet.peek: ND d |-"; print_type ty'; print "-> =|\n"; *) Binarymap.peek(d0, ty'))
      | (ND (d,d0), ty::tys) => let
          val acc = Binarymap.peek(d0, ty')
          val (lab, rest) = ndest_type ty
       (* val _ = (print "TypeNet.peek: ND d |-"; print (label_to_string lab); print "-> ") *)
        in
         (case acc of
            SOME a => SOME a
          | NONE =>
         (case Binarymap.peek(d, lab) of
            NONE => ( (*print "NONE\n";*) NONE)
          | SOME n => ( (*print "SOME n\n";*) trav(n, rest @ tys))
         ) handle Fail s => raise (wrap_exn "TypeNet.peek" (label_to_string lab) (Fail s)))
        end
      | (EMPTY, _) => NONE
   (* | _ => raise Fail "TypeNet.peek: catastrophic invariant failure" *)
in
  trav(net, [ty'])
end

fun find (n, ty) =
    valOf (peek (n, ty)) handle Option => raise Binarymap.NotFound

fun match ((net,sz), ty) = let
  val ty' = deep_beta_eta_ty ty
  val _ = if current_trace "debug_parse_type" = 0 then () else
            (print "TypeNet.match("; print_type ty'; print ")\n")
  fun trav acc (net, tyl) =
      case (net, tyl) of
        (EMPTY, _) => []
      | (LF d, []) => Binarymap.listItems d @ acc
      | (LF d, tys) => acc
      | (ND (d,d0), []) => Binarymap.listItems d0 @ acc
      | (ND (d,d0), ty::tys) => let
          val _ = if current_trace "debug_parse_type" = 0 then ()
                  else (print "ND d on\n  "; print_types (ty::tys); print "\n")
          val acc0 = Binarymap.listItems d0
          val _ = if current_trace "debug_parse_type" = 0 then () else
                    (print "  d0 here has "; print_types (map fst acc0); print "\n")
          val acc' = Binarymap.listItems d0 @ acc
          val (Opr,Args) = strip_app_type ty
          val n = length Args
          val varresult = case Binarymap.peek(d, TV 0) of
                            NONE => acc'
                          | SOME n => trav acc' (n, tys)
          val _ = if current_trace "debug_parse_type" = 0 then () else
                    (print "varresult = "; print_types (map fst varresult); print "\n")
          val (lab, rest) = ndest_type ty
          val _ = if current_trace "debug_parse_type" = 0 then () else
                    (print "lab = "; print (label_to_string lab); print "\n  "; print_types rest; print "\n")
          val varhead_result =
            if n = 0 then varresult 
            else
              case Binarymap.peek (d, TV n) of 
                NONE => varresult
              | SOME n => trav varresult (n, rest @ tys)
          val _ = if current_trace "debug_parse_type" = 0 then () else
                    (print "varhead_result = "; print_types (map fst varhead_result); print "\n")
        in
          (case lab of
            TV n => (if current_trace "debug_parse_type" = 0 then () else
                       (print "  n = "; print (Int.toString n); print "\n";
                        print "    yielding "; print_types (map fst varhead_result); print "\n");
                     varhead_result)
          | _ => let
            in
              case Binarymap.peek (d, lab) of
                NONE => varhead_result
              | SOME n => trav varhead_result (n, rest @ tys)
            end) handle Fail s => raise (wrap_exn "TypeNet.match" (label_to_string lab) (Fail s))
        end
   (* | _ => raise Fail "TypeNet.match: catastrophic invariant failure" *)
in
  trav [] (net, [ty'])
end

fun delete ((net,sz), ty) = let
  val ty' = deep_beta_eta_ty ty
  fun trav (p as (net, tyl)) =
      case p of
        (EMPTY, _) => raise Binarymap.NotFound
      | (LF d, []) => let
          val (d',removed) = Binarymap.remove(d, ty')
        in
          if Binarymap.numItems d' = 0 then (NONE, removed)
          else (SOME (LF d'), removed)
        end
      | (ND (d,d0), []) => let
        in
          case trav (LF d0, []) of
            (NONE, removed) => (SOME (ND (d,Binarymap.mkDict Type.compare)), removed)
          | (SOME (LF d0'), removed) => (SOME (ND (d,d0')), removed)
          | _ => raise Fail "TypeNet.delete: impossible"
        end
      | (ND (d,d0), ty::tys) => let
          val (lab, rest) = ndest_type ty
        in
          case Binarymap.peek(d, lab) of
            NONE => raise Binarymap.NotFound
          | SOME n => let
            in
              case trav (n, rest @ tys) of
                (NONE, removed) => let
                  val (d',_) = Binarymap.remove(d, lab)
                in
                  if Binarymap.numItems d' = 0 andalso Binarymap.numItems d0 = 0 then (NONE, removed)
                  else (SOME (ND (d',d0)), removed)
                end
              | (SOME n', removed) => (SOME (ND (Binarymap.insert(d,lab,n'),d0)),
                                       removed)
            end
        end
      | _ => raise Fail "TypeNet.delete: catastrophic invariant failure"
in
  case trav (net, [ty']) of
    (NONE, removed) => (empty, removed)
  | (SOME n, removed) =>  ((n,sz-1), removed)
end

fun app f (net, sz) = let
  fun trav n =
      case n of
        LF d => Binarymap.app f d
      | ND (d,d0) => (trav (LF d0); Binarymap.app (fn (lab, n) => trav n) d)
      | EMPTY => ()
in
  trav net
end

fun fold f acc (net, sz) = let
  fun trav acc n =
      case n of
        LF d => Binarymap.foldl f acc d
      | ND (d,d0) => Binarymap.foldl (fn (lab,n',acc) => trav acc n') (trav acc (LF d0)) d
      | EMPTY => acc
in
  trav acc net
end

fun map f (net, sz) = let
  fun trav n =
      case n of
        LF d => LF (Binarymap.map f d)
      | ND (d,d0) => ND (Binarymap.transform trav d, Binarymap.map f d0)
      | EMPTY => EMPTY
in
  (trav net, sz)
end

fun transform f = map (fn (k,v) => f v)


end (* struct *)
