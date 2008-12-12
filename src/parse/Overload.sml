structure Overload :> Overload =
struct

open HolKernel Lexis
infix ##

(* invariant on the type overloaded_op_info;
     base_type is the anti-unification of all the types in the actual_ops
     list
   invariant on the overload_info list:
     all members of the list have non-empty actual_ops lists
*)

type nthy_rec = {Name : string, Thy : string}

fun lose_constrec_ty {Name,Ty,Thy} = {Name = Name, Thy = Thy}

(* though term's are stored, the Ty component is there just to
   tell us what the generic type of a term is, it will never be a
   specialisation of a polymorphic type *)

type overloaded_op_info = {base_type : Type.hol_type, actual_ops : term list,
                           tyavoids : Type.hol_type list}

(* the overload info is thus a pair:
   * first component is for the "parsing direction"; it's a map from
     identifier name to an overloaded_op_info record.
   * second component is for the "printing direction"; it takes constant
     specifications {Name,Thy} records, and returns the preferred
     identifier. If no entry exists, the constant should be printed in
     thy$constant name form.
*)


type printmap_data = term * string * real
  (* the term is the lambda abstraction provided by the user, the
     string is the name that it is to be used in the printing process, and
     the real is the timestamp *)
fun tstamp () : real = Time.toReal (Time.now())

type overload_info = ((string,overloaded_op_info) Binarymap.dict *
                      printmap_data LVTermNet.lvtermnet)

structure PrintMap = LVTermNet

fun nthy_rec_cmp ({Name = n1, Thy = thy1}, {Name = n2, Thy = thy2}) =
    pair_compare (String.compare, String.compare) ((thy1, n1), (thy2, n2))

val null_oinfo : overload_info =
  (Binarymap.mkDict String.compare, PrintMap.empty)

fun oinfo_ops (oi,_) = Binarymap.listItems oi
fun print_map (_, pm) = let
  fun foldthis (_,(t,nm,_),acc) =
      if Theory.uptodate_term t then
        (lose_constrec_ty (dest_thy_const t),nm) :: acc
        handle HOL_ERR _ => acc
      else acc
in
  PrintMap.fold foldthis [] pm
end

fun update_assoc k v [] = [(k,v)]
  | update_assoc k v ((k',v')::kvs) = if k = k' then (k,v)::kvs
                                      else (k',v')::update_assoc k v kvs

exception OVERLOAD_ERR of string

fun tmlist_kdvs tlist =
  List.foldl (fn (t,acc) => Lib.union (kind_vars_in_term t) acc) [] tlist

fun tmlist_tyvs tlist =
  List.foldl (fn (t,acc) => Lib.union (type_vars_in_term t) acc) [] tlist

local
  open stmonad Lib Type
  infix >- >>
  fun lookup n (env,avds) =
    case assoc1 n env of
      NONE => ((env,avds), NONE)
    | SOME (_,v) => ((env,avds), SOME v)
  fun extend x (env,avds) = ((x::env,avds), ())
  (* invariant on type generation part of state:
       not (next_var MEM sofar)
  *)
  fun newtyvar (kd,rk) (env, (next_var, sofar)) = let
    val new_sofar = next_var::sofar
    val new_next = gen_variant tyvar_vary sofar (tyvar_vary next_var)
    (* new_next can't be in new_sofar because gen_variant ensures that
       it won't be in sofar, and tyvar_vary ensures it won't be equal to
       next_var *)
  in
    ((env, (new_next, new_sofar)), mk_vartype_opr(next_var,kd,rk))
  end

(* ---------------------------------------------------------------------- *)
(* The au routine is the core of the anti-unification algorithm.          *)
(* The result is the type which is the anti-unification of the arguments. *)
(* ---------------------------------------------------------------------- *)

  fun au0 cntx (ty1, ty2) =
    if null cntx andalso abconv_ty ty1 ty2 then return ty1
    else
      lookup (ty1, ty2) >-
      (fn result =>
       case result of
         NONE =>
           if (is_vartype ty1) andalso (is_vartype ty2) then
             case Lib.assoc1 ty1 cntx
              of SOME (ty1',ty2') =>
                   if ty2' = ty2
                   then return ty1
                   else
                     newtyvar (kind_of ty1,rank_of ty1) >- (fn new_ty => extend ((ty1, ty2), new_ty) >>
                                                            return new_ty)
               | NONE =>
                   let
                     val (s1, kd1, rk1) = dest_vartype_opr ty1
                     val (s2, kd2, rk2) = dest_vartype_opr ty2
                   in
                     if s1 = s2 andalso kd1 = kd2 andalso rk1 = rk2 then
                       return ty1
                     else
                       newtyvar (kd1,rk1) >- (fn new_ty => extend ((ty1, ty2), new_ty) >>
                                              return new_ty)
                   end
           else
           if (is_con_type ty1) andalso (is_con_type ty2) then let
               val {Thy = thy1, Tyop = tyop1, Kind = kd1, Rank = rk1} = dest_thy_con_type ty1
               val {Thy = thy2, Tyop = tyop2, Kind = kd2, Rank = rk2} = dest_thy_con_type ty2
             in
               if tyop1 = tyop2 andalso thy1 = thy2 then
                 return (mk_thy_con_type{Thy = thy1, Tyop = tyop1})
               else
                 newtyvar (kd1,rk1) >- (fn new_ty => extend ((ty1, ty2), new_ty) >>
                                        return new_ty)
             end
           else
           if (is_app_type ty1) andalso (is_app_type ty2) then
(*
             (* this next case is for backwards compatibility *)
             if (is_type ty1) andalso (is_type ty2) then let
               val {Thy = thy1, Tyop = tyop1, Args = args1} = dest_thy_type ty1
               val {Thy = thy2, Tyop = tyop2, Args = args2} = dest_thy_type ty2
             in
               if tyop1 = tyop2 andalso thy1 = thy2 then
                 mmap (au0 cntx) (ListPair.zip (args1, args2)) >-
                 (fn tylist =>
                   return (mk_thy_type{Thy = thy1, Tyop = tyop1,
                                       Args = tylist}))
               else
                 newtyvar (kind_of ty1,rank_of ty1) >- (fn new_ty => extend ((ty1, ty2), new_ty) >>
                                                        return new_ty)
             end
             else
*)
             let
               val (ty1f,ty1a) = dest_app_type ty1
               val (ty2f,ty2a) = dest_app_type ty2
             in
               if kind_of ty1f = kind_of ty2f andalso kind_of ty1a = kind_of ty2a
               then
                 mmap (au0 cntx) (ListPair.zip ([ty1f,ty1a], [ty2f,ty2a])) >-
                   (fn [tyf,tya] =>
                     return (mk_app_type(tyf, tya)
                             handle e => (print ("au failed at mk_app_type on " ^ type_to_string tya
                                                 ^ " " ^ type_to_string tyf ^ "\n");
                                          Raise e)
                            ))
               else
                 newtyvar (kind_of ty1,rank_of ty1) >- (fn new_ty => extend ((ty1, ty2), new_ty) >>
                                                        return new_ty)
             end
           else
           if (is_abs_type ty1) andalso (is_abs_type ty2) then let
               val (bty1,body1) = dest_abs_type ty1
               val (bty2,body2) = dest_abs_type ty2
             in
               au0 ((bty1,bty2)::cntx) (body1, body2) >-
                   (fn body =>
                     return (mk_abs_type(bty1, body)))
             end
           else
           if (is_univ_type ty1) andalso (is_univ_type ty2) then let
               val (bty1,body1) = dest_univ_type ty1
               val (bty2,body2) = dest_univ_type ty2
             in
               au0 ((bty1,bty2)::cntx) (body1, body2) >-
                   (fn body =>
                     return (mk_univ_type(bty1, body)))
             end
(*
           else
           if not (is_vartype ty1) andalso not (is_vartype ty2) then let
               val {Thy = thy1, Tyop = tyop1, Args = args1} = dest_thy_type ty1
               val {Thy = thy2, Tyop = tyop2, Args = args2} = dest_thy_type ty2
             in
               if tyop1 = tyop2 andalso thy1 = thy2 then
                 mmap au0 (ListPair.zip (args1, args2)) >-
                 (fn tylist =>
                   return (mk_thy_type{Thy = thy1, Tyop = tyop1,
                                       Args = tylist}))
               else
                 newtyvar >- (fn new_ty => extend ((ty1, ty2), new_ty) >>
                              return new_ty)
             end
*)
           else
             newtyvar (kind_of ty1, rank_of ty1) >-
                         (fn new_ty =>
                          extend ((ty1, ty2), new_ty) >>
                          return new_ty)
        | SOME v => return v)

  val au = au0 []

  fun initial_state (ty1, ty2) = let
    val avoids = map (#1 o dest_vartype_opr) (type_varsl [ty1, ty2])
    val first_var = gen_variant tyvar_vary avoids "'a"
  in
    ([], (first_var, avoids))
  end
  fun generate_iterates n f x =
    if n <= 0 then []
    else x::generate_iterates (n - 1) f (f x)

  fun canonicalise ty = let
    val tyvars = type_vars ty
    val replacements =
      map2 (fn tyv => fn s => let val (_,kd,rk) = dest_vartype_opr tyv
                              in mk_vartype_opr(s,kd,rk) end)
           tyvars (generate_iterates (length tyvars) tyvar_vary "'a")
    val subst =
      ListPair.map (fn (ty1, ty2) => Lib.|->(ty1, ty2)) (tyvars, replacements)
  in
    type_subst subst ty
  end
in
  fun anti_unify ty1 ty2 = let
    val (_, result) = au (ty1, ty2) (initial_state (ty1, ty2))
  in
    canonicalise result
  end
end

(* find anti-unification for list of types *)
fun aul tyl =
    case tyl of
      [] => raise Fail "Overload.aul applied to empty list - shouldn't happen"
    | (h::t) => foldl (uncurry anti_unify) h t

fun au_tml tml =
    case tml of
      [] => raise Fail "Overload.au_tml applied to empty list: shouldn't happen"
    | tm :: tms => foldl (fn (t,acc) => anti_unify (type_of t) acc)
                         (type_of tm)
                         tms

fun fupd_actual_ops f {base_type, actual_ops, tyavoids} =
  {base_type = base_type, actual_ops = f actual_ops, tyavoids = tyavoids}

fun fupd_base_type f {base_type, actual_ops, tyavoids} =
  {base_type = f base_type, actual_ops = actual_ops, tyavoids = tyavoids}

fun fupd_tyavoids f {base_type, actual_ops, tyavoids} =
    {base_type = base_type, actual_ops = actual_ops, tyavoids = f tyavoids}

fun fupd_dict_at_key k f dict = let
  val (newdict, kitem) = Binarymap.remove(dict,k)
in
  Binarymap.insert(newdict,k,f kitem)
end

fun info_for_name (overloads:overload_info) s =
  Binarymap.peek (#1 overloads, s)
fun is_overloaded (overloads:overload_info) s =
  isSome (info_for_name overloads s)

fun type_compare (ty1, ty2) = let
  val ty1_gte_ty2 = Lib.can (Type.kind_match_type ty1) ty2
  val ty2_gte_ty1 = Lib.can (Type.kind_match_type ty2) ty1
in
  case (ty1_gte_ty2, ty2_gte_ty1) of
    (true, true) => SOME EQUAL
  | (true, false) => SOME GREATER
  | (false, true) => SOME LESS
  | (false, false) => NONE
end

fun remove_overloaded_form s (oinfo:overload_info) = let
  val (op2cnst, cnst2op) = oinfo
  val (okopc, badopc0) = (I ## #actual_ops) (Binarymap.remove(op2cnst, s))
    handle Binarymap.NotFound => (op2cnst, [])
  val badopc = List.filter Theory.uptodate_term badopc0
  (* will keep okopc, but should now remove from cnst2op all pairs of the form
       (c, s)
     where s is the s above *)
  fun foldthis (k,fullv as (t,v,_),acc as (map,removed)) =
      if not (Theory.uptodate_term t) then (map, removed)
      else if v = s then (map, t ::removed)
      else (PrintMap.insert(map, k, fullv), removed)

  val (okcop, badcop) = PrintMap.fold foldthis (PrintMap.empty,[]) cnst2op
in
  ((okopc, okcop), (badopc, badcop))
end

fun raw_map_insert s (new_op2cs, new_c2ops) (op2c_map, c2op_map) = let
  fun install_ty (r as {Name,Thy}) =
    Term.prim_mk_const r
    handle HOL_ERR _ =>
      raise OVERLOAD_ERR ("No such constant: "^Thy^"$"^Name)
  val withtypes = map install_ty new_op2cs

  val new_c2op_map = let
    val withtypes = map install_ty new_c2ops
  in
    List.foldl (fn (t,acc) => PrintMap.insert(acc, ([],t), (t,s,tstamp())))
               c2op_map
               withtypes
  end
in
  case withtypes of
    [] => (op2c_map, new_c2op_map)
  | (r::rs) => let
      val au = foldl (fn (r1, t) => anti_unify (type_of r1) t) (type_of r) rs
    in
      (Binarymap.insert
         (op2c_map, s,
          {base_type = au, actual_ops = withtypes,
           tyavoids = tmlist_tyvs (HOLset.listItems
                                     (FVL withtypes empty_tmset))}),
       new_c2op_map)
    end
end

(* a predicate on pairs of operations and types that returns true if
   they're equal, given that two types are equal if they can match
   each other *)
fun ntys_equal {Ty = ty1,Name = n1, Thy = thy1}
               {Ty = ty2, Name = n2, Thy = thy2} =
  type_compare (ty1, ty2) = SOME EQUAL andalso n1 = n2 andalso thy1 = thy2


(* put a new overloading resolution into the database.  If it's already
   there for a given operator, don't mind.  In either case, make sure that
   it's at the head of the list, meaning that it will be the first choice
   in ambigous resolutions. *)
fun add_overloading (opname, term) oinfo = let
  val _ = Theory.uptodate_term term orelse
          raise OVERLOAD_ERR "Term is out-of-date"
  val (opc0, cop0) = oinfo
  val opc =
      case info_for_name oinfo opname of
        SOME {base_type, actual_ops = a0, tyavoids} => let
          (* this name is already overloaded *)
          val actual_ops = List.filter Theory.uptodate_term a0
          val changed = length actual_ops <> length a0
        in
          case Lib.total (Lib.pluck (aconv term)) actual_ops of
            SOME (_, rest) => let
              (* this term was already in the map *)
              (* must replace it *)
              val (avoids, base_type) =
                  if changed then
                    (tmlist_tyvs (free_varsl actual_ops), au_tml actual_ops)
                  else (tyavoids, base_type)
            in
              Binarymap.insert(opc0, opname,
                               {actual_ops = term::rest,
                                base_type = base_type,
                                tyavoids = avoids})
            end
          | NONE => let
              (* Wasn't in the map, so can just cons its record in *)
              val (newbase, new_avoids) =
                  if changed then
                    (au_tml (term::actual_ops),
                     tmlist_tyvs (free_varsl (term::actual_ops)))
                  else
                    (anti_unify base_type (type_of term),
                     Lib.union (tmlist_tyvs (free_vars term)) tyavoids)
            in
              Binarymap.insert(opc0, opname,
                               {actual_ops = term :: actual_ops,
                                base_type = newbase,
                                tyavoids = new_avoids})
            end
        end
      | NONE =>
        (* this name not overloaded at all *)
        Binarymap.insert(opc0, opname,
                         {actual_ops = [term], base_type = type_of term,
                          tyavoids = tmlist_tyvs (free_vars term)})
  val cop = let
    val fvs = free_vars term
    val (_, pat) = strip_abs term
  in
    PrintMap.insert(cop0,(fvs,pat),(term,opname,tstamp()))
  end
in
  (opc, cop)
end


fun add_actual_overloading {opname, realname, realthy} oinfo = let
  val cnst = prim_mk_const{Name = realname, Thy = realthy}
      handle HOL_ERR _ =>
             raise OVERLOAD_ERR ("No such constant: "^realthy^"$"^realname)
in
  add_overloading (opname, cnst) oinfo
end

local
  fun foverloading f {opname, realname, realthy} oinfo = let
    val nthy_rec = {Name = realname, Thy = realthy}
    val cnst = prim_mk_const nthy_rec
      handle HOL_ERR _ =>
        raise OVERLOAD_ERR ("No such constant: "^realthy^"$"^realname)
    val (opc0, cop0) = oinfo
    val opc =
        case info_for_name oinfo opname of
          SOME {base_type, actual_ops, tyavoids} => let
            (* this name is overloaded *)
          in
            case List.find (aconv cnst) actual_ops of
              SOME x => (* the constant is in the map *)
                Binarymap.insert(opc0, opname,
                  {actual_ops = f (aconv cnst) actual_ops,
                   base_type = base_type,
                   tyavoids = tyavoids})
            | NONE => raise OVERLOAD_ERR
                        ("Constant not overloaded: "^realthy^"$"^realname)
          end
        | NONE => raise OVERLOAD_ERR
                    ("No overloading for Operator: "^opname)
  in
    (opc, cop0)
  end

  fun send_to_back P l = let val (m,r) = Lib.pluck P l in r @ [m] end
  fun bring_to_front P l = let val (m,r) = Lib.pluck P l in m::r end
in
  fun send_to_back_overloading x oinfo = foverloading send_to_back x oinfo
  fun bring_to_front_overloading x oinfo = foverloading bring_to_front x oinfo
end;


fun myfind f [] = NONE
  | myfind f (x::xs) = case f x of (v as SOME _) => v | NONE => myfind f xs

fun isize0 acc f [] = acc
  | isize0 acc f ({redex,residue} :: rest) = isize0 (acc + f residue) f rest
fun isize f x = isize0 0 f x

fun strip_comb ((_, prmap): overload_info) t = let
  val matches = PrintMap.match(prmap, t)
  val cmp0 = pair_compare (Int.compare,
                           pair_compare (measure_cmp (isize kind_size),
                           pair_compare (measure_cmp (isize type_size),
                           pair_compare (measure_cmp (isize term_size),
                                         flip_order o Real.compare))))
  val cmp = inv_img_cmp (fn (r,k,a,b,c,d) => (r,(k,(a,(b,c))))) cmp0

  fun test ((fvs, pat), (orig, nm, tstamp)) = let
    val kdvs = tmlist_kdvs fvs
    val tyvs = tmlist_tyvs fvs
    val tmset = HOLset.addList(empty_tmset, fvs)
    val ((tmi0,tmeq),(tyi0,tyeq),(kdi0,kdeq),rki) = raw_kind_match kdvs tyvs tmset pat t ([],[],[],0)
    val tmi = HOLset.foldl (fn (t,acc) => if HOLset.member(tmset,t) then acc
                                          else (t |-> t) :: acc)
                           tmi0
                           tmeq
    val tyi = List.foldl (fn (ty,acc) => if mem ty tyvs then acc
                                         else (ty |-> ty) :: acc)
                         tyi0
                         tyeq
    val kdi = List.foldl (fn (kd,acc) => if mem kd kdvs then acc
                                         else (kd |-> kd) :: acc)
                         kdi0
                         kdeq
  in
    SOME (rki, kdi, tyi, tmi, tstamp, (orig, nm))
  end handle HOL_ERR _ => NONE

  val inst_data = List.mapPartial test matches
  val sorted = Listsort.sort cmp inst_data
  fun rearrange (_, _, _, tmi, _, (orig, nm)) = let
    val (bvs,_) = strip_abs orig
    fun findarg v =
        case List.find (fn {redex,residue} => eq residue v) tmi of
          NONE => mk_const("ARB", type_of v)
        | SOME i => #residue i
  in
    (mk_var(GrammarSpecials.fakeconst_special ^ nm, alpha), map findarg bvs)
  end
in
  case sorted of
    [] => NONE
  | m :: _ => SOME (rearrange m)
end
fun oi_strip_comb oinfo t = let
  fun recurse acc t =
      case strip_comb oinfo t of
        NONE => let
        in
          case Lib.total dest_comb t of
            NONE => NONE
          | SOME (f,x) => recurse (x::acc) f
        end
      | SOME (f,args) => SOME(f, args @ acc)
  val realf = repeat rator t
in
  if is_var realf andalso
     String.isPrefix GrammarSpecials.fakeconst_special (#1 (dest_var realf))
  then
    NONE
  else recurse [] t
end


fun overloading_of_term (oinfo as (_, prmap) : overload_info) t =
    case strip_comb oinfo t of
      SOME (f, []) => SOME (unprefix GrammarSpecials.fakeconst_special
                                     (#1 (dest_var f)))
    | _ => NONE

fun overloading_of_nametype (oinfo:overload_info) r =
    case Lib.total prim_mk_const r of
      NONE => NONE
    | SOME c => overloading_of_term oinfo c

fun rev_append [] rest = rest
  | rev_append (x::xs) rest = rev_append xs (x::rest)

val show_alias_resolution = ref true
val _ = Feedback.register_btrace ("show_alias_printing_choices",
                                  show_alias_resolution)

fun merge_oinfos (O1:overload_info) (O2:overload_info) : overload_info = let
  val O1ops_sorted = Binarymap.listItems (#1 O1)
  val O2ops_sorted = Binarymap.listItems (#1 O2)
  fun merge acc op1s op2s =
    case (op1s, op2s) of
      ([], x) => rev_append acc x
    | (x, []) => rev_append acc x
    | ((k1,op1)::op1s', (k2,op2)::op2s') => let
      in
        case String.compare (k1, k2) of
          LESS => merge ((k1,op1)::acc) op1s' op2s
        | EQUAL => let
            val name = k1
            val ty1 = #base_type op1
            val ty2 = #base_type op2
            val newty = anti_unify ty1 ty2
            val newopinfo =
              (name,
               {base_type = newty,
                actual_ops =
                Lib.op_union aconv (#actual_ops op1) (#actual_ops op2),
                tyavoids = Lib.union (#tyavoids op1) (#tyavoids op2)})
          in
            merge (newopinfo::acc) op1s' op2s'
          end
        | GREATER => merge ((k2, op2)::acc) op1s op2s'
      end
    infix ##
    fun foldthis (k,v as (t,_,_),acc) =
        if Theory.uptodate_term t then PrintMap.insert(acc,k,v)
        else acc
    val new_prmap = PrintMap.fold foldthis (#2 O2) (#2 O1)
in
  (List.foldr (fn ((k,v),dict) => Binarymap.insert(dict,k,v))
              (Binarymap.mkDict String.compare)
              (merge [] O1ops_sorted O2ops_sorted),
   new_prmap)
end

fun keys dict = Binarymap.foldr (fn (k,v,l) => k::l) [] dict

fun known_constants (oi:overload_info) = keys (#1 oi)

fun remove_omapping crec str opdict = let
  val (dictlessk, kitem) = Binarymap.remove(opdict, str)
  val cnst = prim_mk_const crec
  fun ok_actual t = not (aconv t cnst)
  val new_rec = fupd_actual_ops (List.filter ok_actual) kitem
in
  if (null (#actual_ops new_rec)) then dictlessk
  else Binarymap.insert(dictlessk, str, new_rec)
end handle Binarymap.NotFound => opdict


fun remove_mapping str crec ((opc, cop) : overload_info) = let
  val t = prim_mk_const crec
in
  (remove_omapping crec str opc,
   case PrintMap.peek (cop, ([], t)) of
     NONE => cop
   | SOME (_,s,_) => if s = str then #1 (PrintMap.delete(cop, ([], t)))
                     else cop)
end

end (* Overload *)
