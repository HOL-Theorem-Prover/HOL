structure DefnBaseCore :> DefnBaseCore =
struct

(* ----------------------------------------------------------------------
    storage of definitions
   ---------------------------------------------------------------------- *)
open HolKernel boolSyntax Drule

type kname = KernelSig.kernelname
type defnstore = (string * kname, string * thm) Binarymap.dict
datatype defn_thm = STDEQNS of thm | OTHER of thm
fun thm_of (STDEQNS th) = th | thm_of (OTHER th) = th
type defn_presentation = {const: term, thmname: kname, thm : defn_thm}


val empty_dstore =
    Binarymap.mkDict(pair_compare(String.compare, KernelSig.name_compare))

fun list_insert m k v =
    case Binarymap.peek(m,k) of
        NONE => Binarymap.insert(m,k,[v])
      | SOME vs => Binarymap.insert(m,k,v::vs)

fun to_kid {Thy,Name,Ty} = {Thy = Thy, Name = Name}
val prim_dest_const = to_kid o dest_thy_const

(* _p versions are pure/functional *)
fun register_nonstd_p tag (thname as {Thy,...} :kname) thm dstore =
    let
      fun test t =
          let val cinfo as {Thy = tthy,...} = prim_dest_const t
          in
            tthy = Thy andalso (
            case Binarymap.peek(dstore, (tag, cinfo)) of
                NONE => true
              | SOME (_, defth) => not (uptodate_thm $ thm_of defth)
            )
          end handle HOL_ERR _ => false
      val cs = find_terms test (concl thm)
      val cinfS = List.foldl (fn (c,A) => Binaryset.add(A,prim_dest_const c))
                             (Binaryset.empty KernelSig.name_compare)
                             cs
      fun fold (cinfo, A) =
          Binarymap.insert(A, (tag, cinfo), (thname, OTHER thm))
    in
      Binaryset.foldl fold dstore cinfS
    end

exception nonstdform
fun defn_eqns th =
    let
      val ths = th |> CONJUNCTS
    in
      map
        (fn th =>
            (th |> concl |> strip_forall |> #2 |> lhs |> strip_comb |> #1
                |> dest_thy_const |> to_kid,
             th))
        ths handle HOL_ERR _ => raise nonstdform
    end
val constants_of_defn = mk_set o map #1 o defn_eqns

fun register_defn_p tag (thname, thm) dstore =
    let
      val m = List.foldr (fn ((t,th),A) => list_insert A t th)
                         (Binarymap.mkDict KernelSig.name_compare)
                         (defn_eqns thm)
      open Binarymap
    in
      foldl
        (fn (k,cs,A) => insert(A,(tag,k),(thname, STDEQNS $ LIST_CONJ cs)))
        dstore
        m
    end handle nonstdform => register_nonstd_p tag thname thm dstore

fun add_thy thyname dstore =
    let val defs = DB.definitions thyname
    in
      List.foldl
        (fn ((n,th), A) =>
            register_defn_p "user" ({Thy = thyname, Name = n}, th) A)
        dstore
        defs
    end

fun addboolth nm A =
    register_defn_p "user" ({Thy = "bool", Name = nm}, DB.fetch "bool" nm) A

val initial_dstore =
    empty_dstore
      |> rev_itlist add_thy ["relation", "combin", "bool"]


fun remove_def s dstore =
    Binarymap.foldl (fn (k,v as (nm, th), A) =>
                        if s <> nm then Binarymap.insert(A,k,v) else A)
                    empty_dstore
                    dstore

fun udef_apply (ThmSetData.ADD v) dstore = register_defn_p "user" v dstore
  | udef_apply (ThmSetData.REMOVE s) dstore =
      remove_def (ThmSetData.toKName s) dstore
val userdefs_db as
    {get_global_value = get_userdefs_db, get_deltas = thy_userdefs0,...} =
    ThmSetData.export_with_ancestry {
      settype = "userdef",
      delta_ops = {apply_to_global = udef_apply, thy_finaliser = NONE,
                   uptodate_delta = K true, initial_value = initial_dstore,
                   apply_delta = udef_apply}
    }

fun register_defn {tag, thmname} =
    let
      val add = ThmSetData.mk_add thmname
      val p = case add of ThmSetData.ADD p => p | _ => raise Fail "Impossible"
    in
      if tag <> "user" then
        HOL_WARNING "DefnBase" "register_defn"
                    "Non-'user' definitions are only stored transiently"
      else
        #record_delta userdefs_db add;
      #update_global_value userdefs_db (register_defn_p tag p)
    end


fun presentation (tag,kid) (thmnm, th) =
    {const = prim_mk_const kid,thmname = thmnm,thm = th}
fun lookup_userdef_p dstore c =
    let
      val {Name,Thy,...} =
          dest_thy_const c
          handle HOL_ERR _ => raise mk_HOL_ERR "DefnBase"
                                    "lookup_userdef" "Not a constant"
      val k = ("user", {Name=Name,Thy=Thy})
    in
      Option.map (presentation k) $ Binarymap.peek(dstore, k)
    end
fun lookup_userdef c = lookup_userdef_p (get_userdefs_db()) c

fun current_userdefs () =
    let fun foldthis (k as (tag,kid), v, A) =
            if tag = "user" then presentation k v::A else A
    in
      Binarymap.foldl foldthis [] $ get_userdefs_db()
    end

fun thy_userdefs {thyname} =
    let
      fun foldthis (k as (tag, kid), v, A) =
          if tag = "user" andalso #Thy kid = thyname then
            presentation k v :: A
          else A
    in
      Binarymap.foldl foldthis [] $ get_userdefs_db()
    end


(* ----------------------------------------------------------------------
    Handling induction principles.

    These are awkward because you can't tell by examining the induction
    principle what constants they are supposed to be used with.  This
    means that the register-function needs to pass those constants in
    with the theorem, and those constants need to be stored on disk as
    well.  Of course, being constants only, the kname can be used as a
    substitute for the term value.
   ---------------------------------------------------------------------- *)


type indnstore = (KernelSig.kernelname, thm * kname list) Binarymap.dict
val empty_istore = Binarymap.mkDict KernelSig.name_compare

(* the 'delta' is a thm * term list, with each term a constant *)
local open ThyDataSexp
      fun mmap f [] = SOME []
        | mmap f (h::t) = case f h of
                              NONE => NONE
                            | SOME fh => Option.map (cons fh) $ mmap f t
in
fun encode (th, knms) = List (Thm th :: map (Term o prim_mk_const) knms)
fun decode sexp =
    case sexp of
        List (Thm th :: rest) =>
        Option.map (pair th) $
          mmap (Option.map prim_dest_const o term_decode) rest
      | _ => NONE
end

fun isprefix l1 l2 =
    case (l1,l2) of
        ([], _) => true
      | (_, []) => false
      | (h1::t1, h2::t2) => h1 = h2 andalso isprefix t1 t2

fun issubseq l1 l2 =
    case (l1,l2) of
        ([] , _) => true
      | (h1::t1, []) => false
      | (h1::t1, h2::t2) => h1 = h2 andalso isprefix t1 t2 orelse
                            issubseq (h1::t1) t2
(* Boyer-Moore or similar could be used here, but we only expect these lists
   to be order <= 10 elements long, and even 10 would be super-surprising. *)

fun register_indn_p (ind, knms) istore =
    let
      val cs = map prim_mk_const knms
      val _ = not (null cs) orelse
              raise mk_HOL_ERR "DefnBase" "register_indn"
                    "Must have non-empty list of constants"
      val c = concl ind
      val (Ps, body) = strip_forall c
      fun check (P, c) =
          let
            val (Pdoms, _) = strip_fun (type_of P)
            val (cdoms, _) = strip_fun (type_of c)
          in
            (* might have to ignore suffix types because of possibility
               of returning higher order value (e.g., a set);
               might have to ignore  prefix types because of schematic
               variables
            *)
            issubseq Pdoms cdoms orelse
            raise mk_HOL_ERR "DefnBase" "register_indn"
                    ("Induction variable type of ivar "^ #1 (dest_var P) ^
                     " doesn't match that of constant " ^ #1 (dest_const c))
          end
      val _ = ListPair.all check (Ps, cs)
    in
      List.foldl (fn (c, A) =>
                     Binarymap.insert(A, c |> dest_thy_const |> to_kid,
                                      (ind,knms)))
                 istore
                 cs
    end

val adinfo = {tag = "DefnBase.indn",
              initial_values = [("min", empty_istore)],
              apply_delta = register_indn_p} :
             (thm * KernelSig.kernelname list, indnstore)
               AncestryData.adata_info

val globinfo = {apply_to_global = register_indn_p,
                thy_finaliser = NONE,
                initial_value = empty_istore}

val AData as {get_global_value = the_istore,
              record_delta = record_istore_delta,
              update_global_value = istore_fupd, ...} =
    AncestryData.fullmake {adinfo = adinfo,
                           uptodate_delta = K true,
                           sexps = {dec = decode, enc = encode},
                           globinfo = globinfo}

fun lookup_indn_p istore c =
    let
      val knm = prim_dest_const c
                handle HOL_ERR _ => raise mk_HOL_ERR "DefnBase"
                                          "lookup_indn" "Not a constant"
    in
      Binarymap.peek (istore, knm)
    end
fun lookup_indn c = lookup_indn_p (the_istore()) c

fun register_indn delta (* (thm, knms) *) = (
  record_istore_delta delta;
  istore_fupd (register_indn_p delta)
)

end (* struct *)
