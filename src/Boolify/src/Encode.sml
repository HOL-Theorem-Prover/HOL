(* ========================================================================= *)
(* AUTOMATIC GENERATION OF ENCODING FUNCTIONS FOR DATATYPES.                 *)
(* Created by Joe Hurd, July 2002                                            *)
(* Derived from Konrad Slind's code to generate size functions               *)
(* ========================================================================= *)

structure Encode :> Encode =
struct

open HolKernel boolLib Parse pairSyntax numSyntax listSyntax
  combinSyntax arithmeticTheory boolSimps
  optionTheory listSyntax EncodeTheory PreListEncode;

infix 0 THEN |->;
infixr 1 -->;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

val ERR = mk_HOL_ERR "Encode";

val head = Lib.repeat rator;
fun pair_string(s1,s2) = s1^"$"^s2;

val bool_list = mk_list_type bool;
val bool_nil = inst [alpha |-> bool] listSyntax.nil_tm;
val bool_cons = inst [alpha |-> bool] listSyntax.cons_tm;
val bool_append = inst [alpha |-> bool] listSyntax.append_tm;

fun mk_bool_cons (x,y) = list_mk_comb (bool_cons, [x,y]);
fun mk_bool_append (x,y) = list_mk_comb (bool_append, [x,y]);

fun bool_lists n =
  let
    val ConsT = curry mk_bool_cons T
    val ConsF = curry mk_bool_cons F
    fun booll 0 = [bool_nil]
      | booll n = let val l = booll (n div 2) in map ConsT l @ map ConsF l end
  in
    List.take (booll (n - 1), n)
  end;


local open Portable
      fun num_variant vlist v =
        let val counter = ref 0
            val names = map (fst o dest_var) vlist
            val (Name,Ty) = dest_var v
            fun pass str =
               if mem str names
               then (inc counter; pass (Name^Lib.int_to_string(!counter)))
               else str
        in mk_var(pass Name,  Ty)
        end
in
fun mk_tyvar_encode vty (V,away) =
  let val v = num_variant away (mk_var("f", vty --> bool_list))
  in (v::V, v::away)
  end
end;

fun tyencode_env db =
     Option.map fst o
     Option.composePartial (TypeBasePure.encode_of, TypeBasePure.prim_get db)

(*---------------------------------------------------------------------------*)
(* Term encoding, as a function of types. The function gamma maps type       *)
(* operator "ty" to term "ty_encode". Encountering a type not registered in  *)
(* means failure. The function theta maps a type variable (say 'a) to a term *)
(* variable "f" of type 'a -> bool list.                                     *)
(*                                                                           *)
(* The omega map is used to deal with pre-existing type operators that are   *)
(* nested under.                                                             *)
(*                                                                           *)
(* When actually building an encoder, the behaviour of theta is changed to   *)
(* be such that it maps type variables to failure.                           *)
(*---------------------------------------------------------------------------*)

local fun drop [] ty = fst(dom_rng ty)
        | drop (_::t) ty = drop t (snd(dom_rng ty));
      fun undef ty = raise ERR "tyencode" "undef"
                    (* mk_abs (mk_var ("v", ty), bool_nil) *)
      fun OK f ty M =
         let val (Rator,Rand) = dest_comb M
         in (Rator=f) andalso is_var Rand andalso (type_of Rand = ty)
         end
in
fun tyencode (theta,omega,gamma) clause ty =
 case theta ty
  of SOME fvar => fvar
   | NONE =>
      case omega ty
       of SOME (_,[]) => raise ERR "tyencode" "bug: no assoc for nested"
        | SOME (_,[(f,szfn)]) => szfn
        | SOME (_,alist) => snd
             (first (fn (f,sz) => Lib.can (find_term(OK f ty)) (rhs clause))
                  alist)
        | NONE =>
           let val {Thy,Tyop,Args} = dest_thy_type ty
           in case gamma (Thy,Tyop)
               of SOME f =>
                   let val vty = drop Args (type_of f)
                       val sigma = Type.match_type vty ty
                    in list_mk_comb(inst sigma f,
                            map (tyencode (theta,omega,gamma) clause) Args)
                    end
                | NONE => undef ty
           end
end;

fun dupls [] (C,D) = (rev C, rev D)
  | dupls (h::t) (C,D) = dupls t (if mem h t then (C,h::D) else (h::C,D));

fun crunch [] = []
  | crunch ((x,y)::t) =
    let val key = #1(dom_rng(type_of x))
        val (yes,no) = partition (fn(x,_) => (#1(dom_rng(type_of x))=key)) t
    in (key, (x,y)::yes)::crunch no
    end;

fun unflatten f =
 let fun h (x, s) =
      let val k = f x
      in case List.partition (equal k o fst) s
          of ([(_,l)], r) => (k, x :: l) :: r
           | otherwise    => (k, [x]) :: s
      end
  in
    rev o map (rev o snd) o foldl h []
  end;

fun tyconst_names ty =
  let val {Thy,Tyop,Args} = dest_thy_type ty
  in (Thy,Tyop)
  end;

fun define_encode ax db =
 let val dtys = Prim_rec.doms_of_tyaxiom ax  (* primary types in axiom *)
     val tyvars = Lib.U (map (snd o dest_type) dtys)
     val (_, abody) = strip_forall(concl ax)
     val (exvs, ebody) = strip_exists abody
     (* list of all constructors with arguments *)
     val conjl = strip_conj ebody
     val bare_conjl = map (snd o strip_forall) conjl
     val capplist = map (rand o lhs) bare_conjl
     val def_name = fst(dest_type(type_of(hd capplist)))
     (* 'a -> bool list variables : encode functions for type variables *)
     val fparams = rev(fst(rev_itlist mk_tyvar_encode tyvars
                             ([],free_varsl capplist)))
     val fparams_tyl = map type_of fparams
     fun proto_const n ty =
         mk_var(n, itlist (curry op-->) fparams_tyl (ty --> bool_list))
     fun tyop_binding ty =
       let val {Tyop=root_tyop,Thy=root_thy,...} = dest_thy_type ty
       in ((root_thy,root_tyop), (ty, proto_const("encode_" ^ root_tyop) ty))
       end
     val tyvar_map = zip tyvars fparams
     val tyop_map = map tyop_binding dtys
     fun theta tyv =
          case assoc1 tyv tyvar_map
           of SOME(_,f) => SOME f
            | NONE => NONE
     val type_encode_env = tyencode_env db
     fun gamma str =
          case assoc1 str tyop_map
           of NONE  => type_encode_env str
            | SOME(_,(_, v)) => SOME v
     (* now the ugly nested map *)
     val head_of_clause = head o lhs o snd o strip_forall
     fun is_dty M = mem(#1(dom_rng(type_of(head_of_clause M)))) dtys
     val (dty_clauses,non_dty_clauses) = partition is_dty bare_conjl
     val dty_fns = fst(dupls (map head_of_clause dty_clauses) ([],[]))
     fun dty_encode ty =
        let val (d,r) = dom_rng ty
        in list_mk_comb(proto_const("encode_"^fst(dest_type d)) d,fparams)
        end
     val dty_map = zip dty_fns (map (dty_encode o type_of) dty_fns)
     val non_dty_fns = fst(dupls (map head_of_clause non_dty_clauses) ([],[]))
     fun nested_binding (n,f) =
        let val name = String.concat["encode_",def_name,Lib.int_to_string n]
            val (d,r) = dom_rng (type_of f)
            val proto_const = proto_const name d
        in (f, list_mk_comb (proto_const,fparams))
       end
     val nested_map0 = map nested_binding (enumerate 1 non_dty_fns)
     val nested_map1 = crunch nested_map0
     fun omega ty = assoc1 ty nested_map1
     val encoder = tyencode(theta,omega,gamma)
     fun mk_app cl v = mk_comb(encoder cl (type_of v), v)
     val fn_i_map = dty_map @ nested_map0
     fun clause (bl, cl) =
         let val (fn_i, capp) = dest_comb (lhs cl)
         in
         mk_eq(mk_comb(assoc fn_i fn_i_map, capp),
               end_itlist (curry mk_bool_append)
               (bl :: map (mk_app cl) (snd(strip_comb capp))))
         end
     val bare_conjls = unflatten (rator o lhs) bare_conjl
     val annot_conjs =
       flatten (map (fn l => zip (bool_lists (length l)) l) bare_conjls)
     val pre_defn0 = list_mk_conj (map clause annot_conjs)
     val nil_rws =
       [CONJUNCT1 (DB.fetch "list" "APPEND"), DB.fetch "list" "APPEND_NIL"]
     val pre_defn1 = rhs(concl   (* remove zero additions *)
                      ((DEPTH_CONV BETA_CONV THENC
                        Rewrite.PURE_REWRITE_CONV nil_rws) pre_defn0))
                     handle UNCHANGED => pre_defn0
     val defn = new_recursive_definition
                 {name="encode_"^def_name^"_def",
                  rec_axiom=ax, def=pre_defn1}
     val cty = (I##(type_of o last)) o strip_comb o lhs o snd o strip_forall
     val ctyl = Lib.mk_set (map cty (strip_conj (concl defn)))
     val const_tyl = gather (fn (c,ty) => mem ty dtys) ctyl
     val const_tyopl = map (fn (c,ty) => (c,tyconst_names ty)) const_tyl
 in
    SOME {def=defn,const_tyopl=const_tyopl}
 end
 handle HOL_ERR _ => NONE;

(*---------------------------------------------------------------------------
      Writing all the boolification information to the typebase.
 ---------------------------------------------------------------------------*)

fun insert_encode {def, const_tyopl} tyinfol =
 case tyinfol
  of [] => raise ERR "build_tyinfos" "empty tyinfo list"
   | tyinfo::rst =>
     let val first_tyname = TypeBasePure.ty_name_of tyinfo
         fun ins_encode info encode_eqs =
          let val tyname = TypeBasePure.ty_name_of info
          in case assoc2 tyname const_tyopl
              of SOME(c,tyop) => TypeBasePure.put_encode(c,encode_eqs) info
               | NONE => (HOL_MESG ("Can't find encode constant for"
                                 ^Lib.quote(pair_string tyname));
                         raise ERR "build_tyinfos" "")
          end
     in
       ins_encode tyinfo (TypeBasePure.ORIG def) ::
       map (C ins_encode (TypeBasePure.COPY (first_tyname,def))) rst
     end
     handle HOL_ERR _ => tyinfol;

fun add_encode tyinfol =
  if List.exists (Option.isSome o TypeBasePure.encode_of0) tyinfol
   then tyinfol
   else let
      val db = TypeBase.theTypeBase ()
      val recursion = TypeBasePure.axiom_of (hd tyinfol)
      val tyname = TypeBasePure.ty_name_of (hd tyinfol)
    in
      case define_encode recursion db
       of SOME s => insert_encode s tyinfol
        | NONE => (HOL_MESG("Couldn't define encode function for type "
                            ^Lib.quote (pair_string tyname))
                   ; tyinfol)
    end;

val () = TypeBase.register_update_fn add_encode;

end
