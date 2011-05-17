structure Overload :> Overload =
struct

open HolKernel Lexis
infix ##
infixr 3 ==>

(* invariant on the type overloaded_op_info;
     base_type is the anti-unification of all the types in the actual_ops
     list
   invariant on the overload_info list:
     all members of the list have non-empty actual_ops lists
*)

type nthy_rec = {Name : string, Thy : string}

fun lose_constrec_ty {Name,Ty,Thy} = {Name = Name, Thy = Thy}

type overloaded_op_info = {base_type : Type.hol_type, actual_ops : term list,
                           kdavoids : kind list, tyavoids : Type.hol_type list}

(* the overload info is thus a pair:
   * first component is for the "parsing direction"; it's a map from
     identifier name to an overloaded_op_info record.
   * second component is for the "printing direction"; it takes constant
     specifications {Name,Thy} records, and returns the preferred
     identifier. If no entry exists, the constant should be printed in
     thy$constant name form.
*)


type printmap_data = term * string * int
  (* the term is the lambda abstraction provided by the user, the
     string is the name that it is to be used in the printing process, and
     the int is the 'timestamp' *)
val pos_tstamp : bool -> int = let
  val neg = ref 0
  val cnt = ref 1
in
  fn true => (!cnt before (cnt := !cnt + 1))
   | false => (!neg before (neg := !neg - 1))
end
fun tstamp () = pos_tstamp true

type overload_info = ((string,overloaded_op_info) Binarymap.dict *
                      printmap_data LVTermNet.lvtermnet)

fun raw_print_map ((x,y):overload_info) = y
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
  fun kd_lookup n (kdinfo as (kdenv,_),tyinfo) =
    case assoc1 n kdenv of
      NONE => ((kdinfo,tyinfo), NONE)
    | SOME (_,v) => ((kdinfo,tyinfo), SOME v)
  fun lookup n (kdinfo,(env,avds)) =
    case assoc1 n env of
      NONE => ((kdinfo,(env,avds)), NONE)
    | SOME (_,v) => ((kdinfo,(env,avds)), SOME v)
  fun kd_extend x ((kdenv,kdavds),tyinfo) = (((x::kdenv,kdavds),tyinfo), ())
  fun extend x (kdinfo,(env,avds)) = ((kdinfo,(x::env,avds)), ())
  (* invariant on type generation part of state:
       not (next_var MEM sofar)
  *)
  fun newkdvar rk ((env, (next_var, sofar)), tyinfo) = let
    val new_sofar = next_var::sofar
    val new_next = gen_variant tyvar_vary sofar (tyvar_vary next_var)
    (* new_next can't be in new_sofar because gen_variant ensures that
       it won't be in sofar, and tyvar_vary ensures it won't be equal to
       next_var *)
  in
    (((env, (new_next, new_sofar)), tyinfo), mk_var_kind(next_var,rk))
  end
  fun newtyvar kd (kdinfo, (env, (next_var, sofar))) = let
    val new_sofar = next_var::sofar
    val new_next = gen_variant tyvar_vary sofar (tyvar_vary next_var)
    (* new_next can't be in new_sofar because gen_variant ensures that
       it won't be in sofar, and tyvar_vary ensures it won't be equal to
       next_var *)
  in
    ((kdinfo, (env, (new_next, new_sofar))), mk_var_type(next_var,kd))
  end

(* ---------------------------------------------------------------------- *)
(* The au routine is the core of the anti-unification algorithm.          *)
(* The result is the type which is the anti-unification of the arguments. *)
(* ---------------------------------------------------------------------- *)

  fun au_rk (rk1, rk2) =
    return (if ge_rk(rk1,rk2) then rk2 else rk1)

  fun au_kd (kd1, kd2) =
    if kd1 = kd2 then return kd1
    else
      kd_lookup (kd1, kd2) >-
      (fn result =>
       case result of
         NONE =>
           if (is_arrow_kind kd1) andalso (is_arrow_kind kd2) then let
               val (kd1f,kd1a) = dest_arrow_kind kd1
               val (kd2f,kd2a) = dest_arrow_kind kd2
             in
                 mmap au_kd (ListPair.zip ([kd1f,kd1a], [kd2f,kd2a])) >-
                   (fn [kdf,kda] =>
                     return (kdf ==> kda)
                     | _ => raise Fail "Overload.au_kd: impossible argument")
             end
           else if (is_type_kind kd1) andalso (is_type_kind kd2) then let
               val rk1 = dest_type_kind kd1
               val rk2 = dest_type_kind kd2
             in
               au_rk (rk1,rk2) >- (fn rk => return (typ rk))
             end
           else
             au_rk (rank_of kd1, rank_of kd2) >- (fn rk =>
             newkdvar rk >- (fn new_kd => kd_extend ((kd1, kd2), new_kd) >>
                                          return new_kd))
        | SOME v => return v)

  fun au0 cntx (ty1, ty2) =
    if null cntx andalso eq_ty ty1 ty2 then return ty1
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
                     au_kd (kind_of ty1, kind_of ty2) >- (fn kd =>
                     newtyvar kd >- (fn new_ty => extend ((ty1, ty2), new_ty) >>
                                                  return new_ty))
               | NONE =>
                   let
                     val (s1, kd1) = dest_var_type ty1
                     val (s2, kd2) = dest_var_type ty2
                   in
                     if s1 = s2 then
                       if kd1 = kd2 then
                         return ty1
                       else
                         au_kd (kd1,kd2) >- (fn kd => return (mk_var_type(s1,kd)))
                     else
                       au_kd (kd1,kd2) >- (fn kd =>
                       newtyvar kd >- (fn new_ty => extend ((ty1, ty2), new_ty) >>
                                                    return new_ty))
                   end
           else
           if (is_con_type ty1) andalso (is_con_type ty2) then let
               val {Thy = thy1, Tyop = tyop1, Kind = kd1} = dest_thy_con_type ty1
               val {Thy = thy2, Tyop = tyop2, Kind = kd2} = dest_thy_con_type ty2
             in
               au_kd (kd1,kd2) >- (fn kd =>
               if tyop1 = tyop2 andalso thy1 = thy2 then
                 return (mk_thy_con_type{Thy = thy1, Tyop = tyop1, Kind = kd})
               else
                 newtyvar kd >- (fn new_ty => extend ((ty1, ty2), new_ty) >>
                                              return new_ty))
             end
           else
           if (is_app_type ty1) andalso (is_app_type ty2) then
(**)
             (* this next case is for backwards compatibility *)
             (* needed, e.g., for decode_opcode_def in examples/ARM/v4/arm_evalScript.sml *)
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
                 au_kd (kind_of ty1, kind_of ty2) >- (fn kd =>
                 newtyvar kd >- (fn new_ty => extend ((ty1, ty2), new_ty) >>
                                              return new_ty))
             end
             else
(**)
             let
               val (ty1f,ty1a) = dest_app_type ty1
               val (ty2f,ty2a) = dest_app_type ty2
             in
               if kind_of ty1f = kind_of ty2f andalso kind_of ty1a = kind_of ty2a
               then
                 mmap (au0 cntx) (ListPair.zip ([ty1f,ty1a], [ty2f,ty2a])) >-
                   (fn [tyf,tya] =>
                     return (mk_app_type(tyf, tya)
                             handle e => ((*print ("au failed at mk_app_type on " ^ type_to_string tya
                                                 ^ " " ^ type_to_string tyf ^ "\n");*)
                                          Raise e)
                            )
                     | _ => raise Fail "Overload.au0: impossible argument")
               else
                 au_kd (kind_of ty1, kind_of ty2) >- (fn kd =>
                 newtyvar kd >- (fn new_ty => extend ((ty1, ty2), new_ty) >>
                                              return new_ty))
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
                 au_kd (kind_of ty1, kind_of ty2) >- (fn kd =>
                 newtyvar kd >- (fn new_ty => extend ((ty1, ty2), new_ty) >>
                                 return new_ty))
             end
*)
           else
             au_kd (kind_of ty1, kind_of ty2) >- (fn kd =>
             newtyvar kd >- (fn new_ty =>
                             extend ((ty1, ty2), new_ty) >>
                             return new_ty))
        | SOME v => return v)

  val au = au0 []

  fun initial_state (ty1, ty2) = let
    val avoids = List.map (#1 o dest_var_type) (Type.type_varsl [ty1, ty2])
    val kdavoids = List.map (#1 o dest_var_kind) (Type.kind_varsl [ty1, ty2])
    val first_var = gen_variant tyvar_vary avoids "'a"
    val first_kdvar = gen_variant tyvar_vary kdavoids "'a"
  in
    (([], (first_kdvar, kdavoids)),([], (first_var, avoids)))
  end
  fun generate_iterates n f x =
    if n <= 0 then []
    else x::generate_iterates (n - 1) f (f x)

  fun canonicalise ty = let
    val tyvars = type_vars ty
    val replacements =
      map2 (fn tyv => fn s => let val (_,kd) = dest_var_type tyv
                              in mk_var_type(s,kd) end)
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

fun fupd_actual_ops f {base_type, actual_ops, kdavoids, tyavoids} =
  {base_type = base_type, actual_ops = f actual_ops, kdavoids = kdavoids, tyavoids = tyavoids}

fun fupd_base_type f {base_type, actual_ops, kdavoids, tyavoids} =
  {base_type = f base_type, actual_ops = actual_ops, kdavoids = kdavoids, tyavoids = tyavoids}

fun fupd_kdavoids f {base_type, actual_ops, kdavoids, tyavoids} =
    {base_type = base_type, actual_ops = actual_ops, kdavoids = f kdavoids, tyavoids = tyavoids}

fun fupd_tyavoids f {base_type, actual_ops, kdavoids, tyavoids} =
    {base_type = base_type, actual_ops = actual_ops, kdavoids = kdavoids, tyavoids = f tyavoids}

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
      val fvs = HOLset.listItems (FVL withtypes empty_tmset)
    in
      (Binarymap.insert
         (op2c_map, s,
          {base_type = au, actual_ops = withtypes,
           kdavoids = tmlist_kdvs fvs, tyavoids = tmlist_tyvs fvs}),
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
   in ambigous resolutions.
   update: abstracted the inserter to allow adding at the
           end of the list for inferior resolutions.  *)
fun add_overloading_with_inserter inserter tstamp (opname, term) oinfo = let
  val _ = Theory.uptodate_term term orelse
          raise OVERLOAD_ERR "Term is out-of-date"
  val (opc0, cop0) = oinfo
  val opc =
      case info_for_name oinfo opname of
        SOME {base_type, actual_ops = a0, kdavoids, tyavoids} => let
          (* this name is already overloaded *)
          val actual_ops = List.filter Theory.uptodate_term a0
          val changed = length actual_ops <> length a0
        in
          case Lib.total (Lib.pluck (aconv term)) actual_ops of
            SOME (_, rest) => let
              (* this term was already in the map *)
              (* must replace it *)
              val (kavoids, avoids, base_type) =
                  if changed then
                    let val fvs = free_varsl actual_ops
                    in (tmlist_kdvs fvs, tmlist_tyvs fvs, au_tml actual_ops)
                    end
                  else (kdavoids, tyavoids, base_type)
            in
              Binarymap.insert(opc0, opname,
                               {actual_ops = inserter(term,rest),
                                base_type = base_type,
                                kdavoids = kavoids,
                                tyavoids = avoids})
            end
          | NONE => let
              (* Wasn't in the map, so can just cons its record in *)
              val (newbase, new_kdavoids, new_avoids) =
                  if changed then
                    let val fvs = free_varsl (term::actual_ops)
                    in
                      (au_tml (term::actual_ops),
                       tmlist_kdvs fvs,
                       tmlist_tyvs fvs)
                    end
                  else
                    let val fvs = free_vars term
                    in
                      (anti_unify base_type (type_of term),
                       Lib.union (tmlist_kdvs fvs) kdavoids,
                       Lib.union (tmlist_tyvs fvs) tyavoids)
                    end
            in
              Binarymap.insert(opc0, opname,
                               {actual_ops = inserter(term,actual_ops),
                                base_type = newbase,
                                kdavoids = new_kdavoids,
                                tyavoids = new_avoids})
            end
        end
      | NONE =>
        (* this name not overloaded at all *)
        let val fvs = free_vars term
        in
          Binarymap.insert(opc0, opname,
                           {actual_ops = [term], base_type = type_of term,
                            kdavoids = tmlist_kdvs fvs,
                            tyavoids = tmlist_tyvs fvs})
        end
  val cop = let
    val fvs = free_vars term
    val (_, pat) = strip_abs term
  in
    PrintMap.insert(cop0,(fvs,pat),(term,opname,tstamp()))
  end
in
  (opc, cop)
end

val add_overloading = add_overloading_with_inserter (op ::) (fn () => pos_tstamp true)
val add_inferior_overloading = add_overloading_with_inserter (fn (a,l) => l @ [a]) (fn() => pos_tstamp false)

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
          SOME {base_type, actual_ops, kdavoids, tyavoids} => let
            (* this name is overloaded *)
          in
            case List.find (aconv cnst) actual_ops of
              SOME x => (* the constant is in the map *)
                Binarymap.insert(opc0, opname,
                  {actual_ops = f (aconv cnst) actual_ops,
                   base_type = base_type,
                   kdavoids = kdavoids,
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
  | isize0 acc f ({redex,residue} :: rest) = isize0 (acc + f residue + 1) f rest
fun isize f x = isize0 0 f x

(*
fun rsize0 acc f [] = acc
  | rsize0 acc f (r :: rs) = rsize0 (acc + f r) f rs
fun rsize f x = rsize0 0 f x
*)
fun rsize f x = f x

  val cmp0 = pair_compare (measure_cmp (isize term_size),
                           pair_compare (measure_cmp (isize type_size),
                           pair_compare (measure_cmp (isize kind_size),
                           pair_compare (measure_cmp (rsize rank_size),
                                         flip_order o Int.compare))))
  val cmp = inv_img_cmp (fn (a,b,k,r,c,d) => (a,(b,(k,(r,c))))) cmp0

fun strip_comb ((_, prmap): overload_info) t = let
  val (t',tyargs) = strip_tycomb t
  val matches = PrintMap.match(prmap, t')

  fun test ((fvs, pat), (orig, nm, tstamp)) = let
    val rkvs = not (null fvs)
    val kdvs = tmlist_kdvs fvs
    val tyvs = tmlist_tyvs fvs
    val tmset = HOLset.addList(empty_tmset, fvs)
    val ((tmi0,tmeq),(tyi0,tyeq),(kdi0,kdeq),(rki,rkfx)) = raw_kind_match rkvs kdvs tyvs tmset pat t' ([],[],[],0)
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
    SOME (tmi, tyi, kdi, rki, tstamp, (orig, nm))
  end handle HOL_ERR _ => NONE

  val inst_data = List.mapPartial test matches
  val sorted = Listsort.sort cmp inst_data
  fun rearrange (tmi, _, _, _, _, (orig, nm)) = let
    val (bvs,_) = strip_abs orig
    fun findarg v =
        case List.find (fn {redex,residue} => eq redex v) tmi of
          NONE => mk_const("ARB", type_of v)
        | SOME i => #residue i
    val args = map findarg bvs
    val fconst_ty = List.foldr (fn (arg,acc) => type_of arg --> acc)
                               (type_of t')
                               args
    val fake_var = mk_var(GrammarSpecials.fakeconst_special ^ nm, fconst_ty)
  in
    (list_mk_tycomb(fake_var, tyargs), args)
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
  val realf = repeat tyrator (repeat rator t)
in
  if is_var realf andalso
     String.isPrefix GrammarSpecials.fakeconst_special (#1 (dest_var realf))
  then
    NONE
  else recurse [] t
end

fun dest_all_comb tm =
  case Lib.total dest_comb tm of
     SOME (Rator,Rand) => (Rator, inR Rand)
   | NONE => case Lib.total dest_tycomb tm of
                SOME (Rator,Rand) => (Rator, inL Rand)
              | NONE => raise OVERLOAD_ERR "neither a comb or a type comb"
fun all_rator tm = rator tm handle HOL_ERR _ => tyrator tm
fun oi_strip_all_comb oinfo t = let
  fun recurse acc t =
      case strip_comb oinfo t of
        NONE => let
        in
          case Lib.total dest_all_comb t of
            NONE => NONE
          | SOME (f,x) => recurse (x::acc) f
        end
      | SOME (f,args) =>
          let val (f',tyargs) = strip_tycomb f
          in SOME(f', map inL tyargs @ map inR args @ acc)
          end
  val realf = repeat all_rator t
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
                kdavoids = Lib.union (#kdavoids op1) (#kdavoids op2),
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

fun remove_omapping t str opdict = let
  val (dictlessk, kitem) = Binarymap.remove(opdict, str)
  fun ok_actual t' = not (aconv t' t)
  val new_rec = fupd_actual_ops (List.filter ok_actual) kitem
in
  if (null (#actual_ops new_rec)) then dictlessk
  else Binarymap.insert(dictlessk, str, new_rec)
end handle Binarymap.NotFound => opdict

fun gen_remove_mapping str t ((opc, cop) : overload_info) = let
  val cop' = let
    val ds = PrintMap.peek (cop, ([], t))
    val ds' = List.filter (fn (_, s, _) => s <> str) ds
  in
    if length ds' = length ds then cop
    else let
        val (pm',_) = PrintMap.delete(cop, ([], t))
      in
        List.foldl (fn (d,acc) => PrintMap.insert(acc,([],t),d))
                   pm'
                   ds'
      end
  end
in
  (remove_omapping t str opc, cop')
end
fun remove_mapping str crec = gen_remove_mapping str (prim_mk_const crec)

end (* Overload *)
