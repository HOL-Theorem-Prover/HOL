structure listSyntax :> listSyntax =
struct

 open HolKernel Abbrev
 local open listTheory in end;

val ERR = mk_HOL_ERR "listSyntax";


(*---------------------------------------------------------------------------
     Constructors and destructors for the type of lists
 ---------------------------------------------------------------------------*)

fun mk_list_type ty = mk_thy_type {Tyop="list", Thy="list",  Args=[ty]};

fun dest_list_type ty =
   case total dest_thy_type ty
    of SOME {Tyop="list", Thy="list", Args=[ty]} => ty
     | other => raise ERR "dest_list_type" ""

val is_list_type = can dest_list_type;

(*---------------------------------------------------------------------------
    Constants ... SUM really belongs elsewhere.
 ---------------------------------------------------------------------------*)

val nil_tm       = prim_mk_const {Name = "NIL",     Thy = "list"}
val cons_tm      = prim_mk_const {Name = "CONS",    Thy = "list"}
val snoc_tm      = prim_mk_const {Name = "SNOC",    Thy = "list"}
val drop_tm      = prim_mk_const {Name = "DROP",    Thy = "list"}
val take_tm      = prim_mk_const {Name = "TAKE",    Thy = "list"}
val isprefix_tm  = prim_mk_const {Name = "isPREFIX",Thy = "list"}
val null_tm      = prim_mk_const {Name = "NULL",    Thy = "list"}
val hd_tm        = prim_mk_const {Name = "HD",      Thy = "list"}
val tl_tm        = prim_mk_const {Name = "TL",      Thy = "list"}
val append_tm    = prim_mk_const {Name = "APPEND",  Thy = "list"}
val flat_tm      = prim_mk_const {Name = "FLAT",    Thy = "list"}
val length_tm    = prim_mk_const {Name = "LENGTH",  Thy = "list"}
val map_tm       = prim_mk_const {Name = "MAP",     Thy = "list"}
val map2_tm      = prim_mk_const {Name = "MAP2",    Thy = "list"}
val filter_tm    = prim_mk_const {Name = "FILTER",  Thy = "list"}
val foldr_tm     = prim_mk_const {Name = "FOLDR",   Thy = "list"}
val foldl_tm     = prim_mk_const {Name = "FOLDL",   Thy = "list"}
val every_tm     = prim_mk_const {Name = "EVERY",   Thy = "list"}
val exists_tm    = prim_mk_const {Name = "EXISTS",  Thy = "list"}
val el_tm        = prim_mk_const {Name = "EL",      Thy = "list"}
val zip_tm       = prim_mk_const {Name = "ZIP",     Thy = "list"}
val unzip_tm     = prim_mk_const {Name = "UNZIP",   Thy = "list"}
val sum_tm       = prim_mk_const {Name = "SUM",     Thy = "list"}
val reverse_tm   = prim_mk_const {Name = "REVERSE", Thy = "list"}
val list_case_tm = prim_mk_const {Name = "list_CASE", Thy = "list"}
val last_tm      = prim_mk_const {Name = "LAST",    Thy = "list"}
val front_tm     = prim_mk_const {Name = "FRONT",   Thy = "list"}
val nub_tm       = prim_mk_const {Name = "nub",     Thy = "list"}
val all_distinct_tm = prim_mk_const {Name = "ALL_DISTINCT", Thy = "list"}
val list_to_set_tm  = prim_mk_const {Name = "LIST_TO_SET",  Thy = "list"}
val genlist_tm    = prim_mk_const {Name = "GENLIST", Thy = "list"}

fun eltype l = dest_list_type (type_of l);

(*---------------------------------------------------------------------------
         Constructor functions ... should add bespoke error
         message to each of these ...
 ---------------------------------------------------------------------------*)

fun mk_nil ty    = inst [alpha |-> ty] nil_tm
fun mk_cons(h,t) = list_mk_comb(inst [alpha |-> type_of h] cons_tm, [h,t])
fun mk_snoc(h,t) = list_mk_comb(inst [alpha |-> type_of h] snoc_tm, [h,t])
fun mk_drop(n,l) = list_mk_comb(inst [alpha |-> eltype l] drop_tm, [n,l])
fun mk_take(n,l) = list_mk_comb(inst [alpha |-> eltype l] take_tm, [n,l])
fun mk_isprefix(l1,l2) =
  list_mk_comb(inst [alpha |-> eltype l1] isprefix_tm, [l1,l2])
fun mk_null l    = mk_comb(inst[alpha |-> eltype l] null_tm,l)
fun mk_hd l      = mk_comb(inst[alpha |-> eltype l] hd_tm,l)
fun mk_tl l      = mk_comb(inst[alpha |-> eltype l] tl_tm,l)
fun mk_append(l1,l2) = list_mk_comb(inst[alpha |-> eltype l1]append_tm,[l1,l2])
fun mk_flat l    = mk_comb(inst[alpha |-> dest_list_type(eltype l)] flat_tm,l)
fun mk_length l  = mk_comb(inst[alpha |-> eltype l] length_tm,l)
fun mk_map (f,l) =
  list_mk_comb(inst[alpha |-> eltype l,
                    beta  |-> snd(dom_rng (type_of f))] map_tm, [f,l])
fun mk_map2(f,l1,l2) =
  list_mk_comb(inst[alpha |-> eltype l1,
                    beta  |-> eltype l2,
                    gamma |-> snd(strip_fun(type_of f))] map2_tm, [f,l1,l2])

fun mk_filter(P,l)  = list_mk_comb(inst[alpha |-> eltype l] filter_tm,[P,l])
fun mk_foldr(f,b,l) = list_mk_comb(inst[alpha |-> eltype l,
                                        beta  |-> type_of b] foldr_tm,[f,b,l])
fun mk_foldl(f,b,l) = list_mk_comb(inst[alpha |-> eltype l,
                                        beta  |-> type_of b] foldl_tm,[f,b,l])
fun mk_every(P,l)   = list_mk_comb(inst[alpha |-> eltype l] every_tm,[P,l])
fun mk_exists(P,l)  = list_mk_comb(inst[alpha |-> eltype l] exists_tm,[P,l])
fun mk_el(n,l)      = list_mk_comb(inst[alpha |-> eltype l] el_tm,[n,l])
fun mk_zip(l1,l2)   = mk_comb(inst[alpha |-> eltype l1,
                                   beta  |-> eltype l2] zip_tm,
                              pairSyntax.mk_pair(l1,l2))
fun mk_unzip l =
  let val (ty1,ty2) = pairSyntax.dest_prod (eltype l)
  in mk_comb(inst[alpha |-> ty1, beta |-> ty2] unzip_tm, l)
  end

fun mk_sum l = mk_comb(sum_tm,l);
fun mk_reverse l = mk_comb(inst[alpha |-> eltype l] reverse_tm,l);
fun mk_last l = mk_comb(inst[alpha |-> eltype l] last_tm,l);
fun mk_front l = mk_comb(inst[alpha |-> eltype l] front_tm,l);
fun mk_all_distinct l = mk_comb(inst[alpha |-> eltype l] all_distinct_tm,l);
fun mk_list_to_set l = mk_comb(inst[alpha |-> eltype l] list_to_set_tm,l);
fun mk_mem(x,l)     = pred_setSyntax.mk_in(x,mk_list_to_set l)

fun mk_nub l = mk_comb(inst[alpha |-> eltype l] nub_tm,l)

fun mk_genlist (f,n) =
  list_mk_comb (inst [alpha |-> (f |> Term.type_of
                                   |> Type.dom_rng
                                   |> snd)] genlist_tm, [f,n])
  handle HOL_ERR _ => raise ERR "mk_genlist" ""

fun mk_list_case (n,c,l) =
 case total dest_list_type (type_of l)
  of SOME ty =>
       list_mk_comb
          (inst [alpha |-> ty, beta |-> type_of n]list_case_tm, [l,n,c])
   | NONE => raise ERR "mk_list_case" "";


(*---------------------------------------------------------------------------
         Destructors
 ---------------------------------------------------------------------------*)

fun dest_nil tm =
 if same_const nil_tm tm
   then dest_list_type (type_of tm)
   else raise ERR "dest_nil" "";

val dest_cons     = dest_binop cons_tm     (ERR "dest_cons"     "not CONS")
val dest_snoc     = dest_binop snoc_tm     (ERR "dest_snoc"     "not SNOC")
val dest_drop     = dest_binop drop_tm     (ERR "dest_drop"     "not DROP")
val dest_take     = dest_binop take_tm     (ERR "dest_take"     "not TAKE")
val dest_isprefix = dest_binop isprefix_tm (ERR "dest_isprefix" "not isPREFIX")
val dest_null     = dest_monop null_tm     (ERR "dest_null"     "not NULL")
val dest_hd       = dest_monop hd_tm       (ERR "dest_hd"       "not HD")
val dest_tl       = dest_monop tl_tm       (ERR "dest_tl"       "not TL")
val dest_append   = dest_binop append_tm   (ERR "dest_append"   "not APPEND")
val dest_flat     = dest_monop flat_tm     (ERR "dest_flat"     "not FLAT")
val dest_length   = dest_monop length_tm   (ERR "dest_length"   "not LENGTH")
val dest_map      = dest_binop map_tm      (ERR "dest_map"      "not MAP")
val dest_map2     = dest_triop map2_tm     (ERR "dest_map2"     "not MAP2")
val dest_filter   = dest_binop filter_tm   (ERR "dest_filter"   "not FILTER")
val dest_foldr    = dest_triop foldr_tm    (ERR "dest_foldr"    "not FOLDR")
val dest_foldl    = dest_triop foldl_tm    (ERR "dest_foldl"    "not FOLDL")
val dest_every    = dest_binop every_tm    (ERR "dest_every"    "not EVERY")
val dest_exists   = dest_binop exists_tm   (ERR "dest_exists"   "not EXISTS")
val dest_el       = dest_binop el_tm       (ERR "dest_el"       "not EL")
val dest_zip      = pairSyntax.dest_pair
                    o dest_monop zip_tm    (ERR "dest_zip"      "not ZIP")
val dest_unzip    = dest_monop unzip_tm    (ERR "dest_unzip"    "not UNZIP")
val dest_sum      = dest_monop sum_tm      (ERR "dest_sum"      "not SUM")
val dest_reverse  = dest_monop reverse_tm  (ERR "dest_reverse"  "not REVERSE")
val dest_last     = dest_monop last_tm     (ERR "dest_last"     "not LAST")
val dest_front    = dest_monop front_tm    (ERR "dest_front"    "not FRONT")
val dest_nub      = dest_monop nub_tm      (ERR "dest_nub"      "not nub")
val dest_all_distinct = dest_monop all_distinct_tm
                          (ERR "dest_all_distinct" "not ALL_DISTINCT")
val dest_list_to_set = dest_monop list_to_set_tm
                          (ERR "dest_list_to_set" "not LIST_TO_SET")
val dest_genlist  = dest_binop genlist_tm  (ERR "dest_genlist"  "not GENLIST")

fun dest_list_case t = let
  val (l,n,c) = dest_triop list_case_tm
                           (ERR "dest_list_case" "not list_case") t
in
  (n,c,l)
end

fun dest_mem t = let
  val (x,setl) = pred_setSyntax.dest_in t
in
  (x, dest_list_to_set setl)
end
handle HOL_ERR herr => raise ERR "dest_mem" (message_of herr)


(*---------------------------------------------------------------------------
         Queries
 ---------------------------------------------------------------------------*)

val is_nil          = can dest_nil
val is_cons         = can dest_cons
val is_snoc         = can dest_snoc
val is_drop         = can dest_drop
val is_take         = can dest_take
val is_isprefix     = can dest_isprefix
val is_null         = can dest_null
val is_hd           = can dest_hd
val is_tl           = can dest_tl
val is_append       = can dest_append
val is_flat         = can dest_flat
val is_length       = can dest_length
val is_map          = can dest_map
val is_map2         = can dest_map2
val is_mem          = can dest_mem
val is_filter       = can dest_filter
val is_foldr        = can dest_foldr
val is_foldl        = can dest_foldl
val is_every        = can dest_every
val is_exists       = can dest_exists
val is_el           = can dest_el
val is_zip          = can dest_zip
val is_unzip        = can dest_unzip
val is_sum          = can dest_sum
val is_last         = can dest_last
val is_front        = can dest_front
val is_all_distinct = can dest_all_distinct
val is_list_to_set  = can dest_list_to_set
val is_reverse      = can dest_reverse
val is_list_case    = can dest_list_case
val is_genlist      = can dest_genlist
val is_nub          = can dest_nub

val s3 = HolKernel.syntax_fns3 "list"

val (pad_left_tm, mk_pad_left, dest_pad_left, is_pad_left) = s3 "PAD_LEFT"
val (pad_right_tm, mk_pad_right, dest_pad_right, is_pad_right) = s3 "PAD_RIGHT"

fun mk_list (l,ty) = itlist (curry mk_cons) l (mk_nil ty);

fun dest_list M =
 let fun dest M =
       case total dest_cons M
       of NONE => if is_nil M then []
                  else raise ERR "dest_list" "not terminated with nil"
        | SOME(h,t) => h::dest t
 in (dest M, dest_list_type (type_of M))
 end;

val is_list = can dest_list;

(*---------------------------------------------------------------------------*)
(* Strips leading occurences of cons                                         *)
(* Added 17 July 2009 by Thomas Tuerk                                        *)
(*---------------------------------------------------------------------------*)
val strip_cons =
  let fun strip A M =
        case total dest_cons M
         of NONE => (List.rev A, M)
          | SOME(h,tl) => strip (h::A) tl
  in strip []
  end;

(*---------------------------------------------------------------------------*)
(* Strips leading occurences of SNOC                                         *)
(*                                                                           *)
(*  strip_snoc “SNOC x l”          = (``l``, [``x``])                        *)
(*  strip_snoc “SNOC y (SNOC x l)” = (``l``, [``x``, ``y``])                 *)
(*  strip_snoc “l :'a list”        = (``l``, [])                             *)
(*---------------------------------------------------------------------------*)
val strip_snoc =
  let fun strip A M =
        case total dest_snoc M
         of NONE => (M, A)
          | SOME(t,hl) => strip (t::A) hl
  in strip []
  end;

(*---------------------------------------------------------------------------*)
(* Strips occurences of append                                               *)
(* Added 03 December 2009 by Thomas Tuerk                                    *)
(*---------------------------------------------------------------------------*)
val strip_append =
  let fun strip A M =
        case total dest_append M
         of NONE => (M::A)
          | SOME(l1,l2) => strip (l2::A) l1
  in strip []
  end;

(*---------------------------------------------------------------------------*)
(* Strips leading occurences of SNOC, outputs compatible with strip_append   *)
(* NOTE: The name "strip_snoc_to_lists" is suggested by Konrad Slind.        *)
(*                                                                           *)
(*  strip_snoc_to_lists “SNOC x l”          = [``l``, ``[x]``]               *)
(*  strip_snoc_to_lists “SNOC y (SNOC x l)” = [``l``, ``[x]``, ``[y]``]      *)
(*  strip_snoc_to_lists “l :'a list”        = [``l``]                        *)
(*---------------------------------------------------------------------------*)
val strip_snoc_to_lists =
  let fun strip A M =
        case total dest_snoc M
         of NONE => (M::A)
          | SOME(t,hl) => strip (mk_list([t],type_of t)::A) hl
  in strip []
  end;

(*---------------------------------------------------------------------------*)
(* Added 03 December 2009 by Thomas Tuerk                                    *)
(*---------------------------------------------------------------------------*)
fun list_mk_append [] = raise ERR "list_mk_append" "empty append list"
  | list_mk_append [l] = l
  | list_mk_append (l1::l2::ls) =
       list_mk_append ((mk_append (l1,l2))::ls)

(*---------------------------------------------------------------------------*)
(* Lift ML lists to HOL lists                                                *)
(*---------------------------------------------------------------------------*)

fun lift_list ty =
  let open TypeBasePure
      val Nil = cinst ty nil_tm
      val Cons = cinst ty cons_tm
      fun lift f [] = Nil
        | lift f (h::t) = list_mk_comb(Cons,[f h,lift f t])
  in lift
  end

end
