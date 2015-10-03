structure Type :> Type =
struct

open Feedback Lib

infix |->
infixr -->

val WARN = HOL_WARNING "Type";
fun ERR f msg = HOL_ERR {origin_structure = "Type",
                         origin_function = f,
                         message = msg}

type type_key = {Thy : string, Tyop : string }
type type_info = KernelSig.kernelid * int

val operator_table = KernelSig.new_table()

fun prim_delete_type (k as {Thy, Tyop}) =
    ignore (KernelSig.retire_name(operator_table, {Thy = Thy, Name = Tyop}))

fun prim_new_type {Thy,Tyop} n = let
  val _ = n >= 0 orelse failwith "invalid arity"
in
  ignore (KernelSig.insert(operator_table,{Thy=Thy,Name=Tyop},n))
end

fun thy_types s = let
  fun foldthis (kn,(_,arity),acc) =
      if #Thy kn = s then (#Name kn, arity) :: acc
      else acc
in
  KernelSig.foldl foldthis [] operator_table
end

fun del_segment s = KernelSig.del_segment(operator_table, s)

fun minseg s = {Thy = "min", Tyop = s}
val _ = prim_new_type (minseg "fun") 2
val _ = prim_new_type (minseg "bool") 0
val _ = prim_new_type (minseg "ind") 0

val funref = #1 (KernelSig.find(operator_table, {Thy="min", Name = "fun"}))

type 'a weakref = 'a option ref

fun wr_compare cmp (ref wr1, ref wr2) = option_compare cmp (wr1, wr2)

type 'a hconsed = { node: 'a, tag : int, hkey : word } ref

local
  val tag = ref 0
in
fun next_tag () = (!tag before tag := !tag + 1)
end

fun hccompare cmp (ref {node=n1,tag=t1,hkey=_},ref {node=n2,tag=t2,hkey=_}) =
  if t1 = t2 then EQUAL else cmp (n1, n2)

datatype hol_type_node =
         Tyv of string
       | Tyapp of KernelSig.kernelid * hol_type_node hconsed list

type hol_type = hol_type_node hconsed

fun node (ref {node,...} : hol_type) = node
fun tag (ref {tag,...} : hol_type) = tag
fun hkey (ref {hkey,...} : hol_type) = hkey

fun htn_compare (ty1,ty2) =
  case (ty1, ty2) of
      (Tyv s1, Tyv s2) => String.compare(s1,s2)
    | (Tyv _, Tyapp _) => LESS
    | (Tyapp _, Tyv _) => GREATER
    | (Tyapp p1, Tyapp p2) =>
      pair_compare (KernelSig.id_compare, list_compare (hccompare htn_compare))
                   (p1, p2)

val typetable = ref (PIntMap.empty : hol_type weakref HOLset.set PIntMap.t)

val hashstring = CharVector.foldl (fn (c,h) => Word.fromInt(Char.ord c) + h * 0w31) 0w0

fun hashkid kid =
  let
    val {Thy,Name} = KernelSig.name_of_id kid
  in
    Word.xorb(hashstring Thy,hashstring Name)
  end

fun hashopn (kid,args) =
  List.foldl (Word.xorb o (Lib.##(hkey,I))) (hashkid kid) args

fun mk_hashconsed cmp table hash cons args =
  let
    val hk = hash args
    fun mk_new() =
      let
        val nr = ref {hkey = hk, tag = next_tag(), node = cons args}
        val wr = Weak.weak (SOME nr)
      in
        (wr,nr)
      end
    fun not_there() =
      let
        val (wr,nr) = mk_new()
      in
        (HOLset.singleton (wr_compare (hccompare cmp)) wr, nr)
      end
    fun is_there set =
      let
        fun findP (ref (SOME (ref hc))) = #node hc = cons args
          | findP _ = false
      in
        case HOLset.find findP set of
          NONE =>
            let
              val (wr,nr) = mk_new()
              val set' = HOLset.add(set,wr)
            in
              (set',nr)
            end
        | SOME (ref (SOME nr)) => (set,nr)
        | SOME (ref NONE) => raise Fail "Weak reference disappeared during pattern match"
      end
    val (t, r) = PIntMap.addfu is_there (Word.toInt hk) not_there (!table)
  in
    table := t; r
  end

fun mk_hctype x = mk_hashconsed htn_compare typetable x

fun uptodate_type ty =
  case node ty of
      Tyv _ => true
    | Tyapp(info, args) => KernelSig.uptodate_id info andalso
                           List.all uptodate_type args

fun dest_vartype ty =
  case node ty of
      Tyv s => s
    | _ => raise ERR "dest_vartype" "Type not a vartype"

fun is_vartype ty =
  case node ty of
      Tyv _ => true
    | _ => false

fun pfind k pm =
  SOME (PIntMap.find k pm) handle PIntMap.NotFound=> NONE

val mk_Tyv = mk_hctype hashstring Tyv
val mk_Tyapp = mk_hctype hashopn Tyapp

val alpha  = mk_Tyv "'a"
val beta   = mk_Tyv "'b";
val gamma  = mk_Tyv "'c"
val delta  = mk_Tyv "'d"
val etyvar = mk_Tyv "'e"
val ftyvar = mk_Tyv "'f"


val varcomplain = ref true
val _ = register_btrace ("Vartype Format Complaint", varcomplain)


fun mk_vartype s =
  (if not (Lexis.allowed_user_type_var s) andalso !varcomplain then
     WARN "mk_vartype" "non-standard syntax"
   else ();
   mk_Tyv s)

val gen_tyvar_prefix = "%%gen_tyvar%%"

fun num2name i = gen_tyvar_prefix ^ Lib.int_to_string i
val nameStrm = Lib.mk_istream (fn x => x + 1) 0 num2name

fun gen_tyvar () = mk_Tyv (state(next nameStrm))

fun is_gen_tyvar ty =
  case node ty of
      Tyv name => String.isPrefix gen_tyvar_prefix name
    | _ => false;

fun first_decl caller s = let
  val possibilities = KernelSig.listName operator_table s
in
  case possibilities of
    [] => raise ERR caller ("No such type: "^s)
  | [x] => #2 x
  | x::xs => (WARN caller ("More than one possibility for "^s); #2 x)
end

fun mk_type (opname, args) = let
  val (id,aty) = first_decl "mk_type" opname
in
  if length args = aty then mk_Tyapp (id,args)
  else
    raise ERR "mk_type"
              ("Expecting "^Int.toString aty^" arguments for "^opname)
end

fun mk_thy_type {Thy, Tyop, Args} =
  case KernelSig.peek(operator_table, {Thy = Thy, Name = Tyop}) of
      NONE => raise ERR "mk_thy_type" ("No such type: "^Thy ^ "$" ^ Tyop)
    | SOME (id,arity) =>
      if arity = length Args then mk_Tyapp (id,Args)
      else raise ERR "mk_thy_type" ("Expecting "^Int.toString arity^
                                    " arguments for "^Tyop)

val bool = mk_type("bool", [])
val ind = mk_type("ind", [])

fun dest_type ty =
  case node ty of
      Tyv _ => raise ERR "dest_type" "Type a variable"
    | Tyapp(id, args) =>
      let
        val {Thy, Name} = KernelSig.name_of_id id
      in
        (Name, args)
      end

fun is_type ty = not (is_vartype ty)

fun dest_thy_type ty =
  case node ty of
      Tyv _ => raise ERR "dest_thy_type" "Type a variable"
    | Tyapp(id, args) =>
      {Thy = KernelSig.seg_of id, Tyop = KernelSig.name_of id, Args = args}

fun decls s = let
  fun foldthis ({Thy,Name},v,acc) = if Name = s then {Thy=Thy,Tyop=Name}::acc
                                    else acc
in
  KernelSig.foldl foldthis [] operator_table
end

fun op_arity {Thy,Tyop} =
    Option.map (#2) (KernelSig.peek(operator_table, {Thy=Thy,Name=Tyop}))

fun type_vars_set acc tylist =
  case tylist of
      [] => acc
    | ty::tys =>
      case node ty of
          Tyv _ => type_vars_set (HOLset.add(acc, ty)) tys
        | Tyapp (_, args) => type_vars_set acc (args @ tys)

val compare = hccompare htn_compare

val empty_tyset = HOLset.empty compare

fun type_vars ty = HOLset.listItems (type_vars_set empty_tyset [ty])

val type_varsl = HOLset.listItems o type_vars_set empty_tyset

fun exists_tyvar P = let
  fun occ ty =
    case node ty of
        Tyv _ => P ty
      | Tyapp(_, Args) => List.exists occ Args
in
  occ
end

fun type_var_in v =
  if is_vartype v then exists_tyvar (equal v)
                  else raise ERR "type_var_in" "not a type variable"

val polymorphic = exists_tyvar (fn _ => true)

fun (ty1 --> ty2) = mk_Tyapp (funref,[ty1, ty2])

fun dom_rng ty =
  case node ty of
      Tyv _  => raise ERR "dom_rng" "Type a variable"
    | Tyapp(i, args) => if i = funref then (hd args, hd (tl args))
                        else raise ERR "dom_rng"
                                   "Type not a function type"

fun ty_sub [] _ = SAME
  | ty_sub theta ty =
    case node ty of
        Tyapp(tyc,Args) => (case delta_map (ty_sub theta) Args of
                                SAME => SAME
                              | DIFF Args' => DIFF (mk_Tyapp (tyc,Args')))
      | _ => case Lib.subst_assoc (equal ty) theta of
                 NONE    => SAME
               | SOME ty => DIFF ty

fun type_subst theta = delta_apply (ty_sub theta)

(* val type_subst0 = type_subst
fun type_subst theta = Profile.profile "type_subst" (type_subst0 theta) *)


local
  fun MERR s = raise ERR "raw_match_type" s
  fun lookup x ids =
   let fun look [] = if Lib.mem x ids then SOME x else NONE
         | look ({redex,residue}::t) = if x=redex then SOME residue else look t
   in look end
in
fun tymatch [] [] Sids = Sids
  | tymatch (v::ps) (ty::obs) (Sids as (S,ids)) =
    (case (node v, node ty) of
        (Tyv _,_) =>
        tymatch ps obs
          (case lookup v ids S of
               NONE => if v=ty then (S,v::ids) else ((v |-> ty)::S,ids)
             | SOME ty1 => if ty1=ty then Sids else MERR "double bind")
      | (Tyapp(c1,A1), Tyapp(c2,A2)) =>
        if c1=c2 then tymatch (A1@ps) (A2@obs) Sids
        else MERR "different tyops"
      | (_, _) => MERR "different constructors")
    | tymatch any other thing = MERR "different constructors"
end
(*
fun raw_match_type (v as Tyv _) ty (Sids as (S,ids)) =
       (case lookup v ids S
         of NONE => if v=ty then (S,v::ids) else ((v |-> ty)::S,ids)
          | SOME ty1 => if ty1=ty then Sids else MERR "double bind")
  | raw_match_type (Tyapp(c1,A1)) (Tyapp(c2,A2)) Sids =
       if c1=c2 then rev_itlist2 raw_match_type A1 A2 Sids
                else MERR "different tyops"
  | raw_match_type _ _ _ = MERR "different constructors"
*)
fun raw_match_type pat ob Sids = tymatch [pat] [ob] Sids

fun match_type_restr fixed pat ob  = fst (raw_match_type pat ob ([],fixed))
fun match_type_in_context pat ob S = fst (raw_match_type pat ob (S,[]))

fun match_type pat ob = match_type_in_context pat ob []


fun size acc tylist =
    case tylist of
      [] => acc
    | [] :: tys => size acc tys
    | (ty::tys1) :: tys2 => let
      in
        case node ty of
          Tyv _ => size (1 + acc) (tys1 :: tys2)
        | Tyapp(_, args) => size (1 + acc) (args :: tys1 :: tys2)
      end

fun type_size ty = size 0 [[ty]]

end (* struct *)
