structure DataSize :> DataSize =
struct

open HolKernel Parse boolLib Prim_rec arithmeticTheory;
val ERR = mk_HOL_ERR "DataSize";

val num = numSyntax.num

val Zero  = numSyntax.zero_tm
val One   = numSyntax.term_of_int 1

fun Kzero ty = mk_abs(mk_var("v",ty), numSyntax.zero_tm)

val defn_const =
  #1 o strip_comb o lhs o #2 o strip_forall o hd o strip_conj o concl;

val head = Lib.repeat rator;

fun tyconst_names ty =
  let val {Thy,Tyop,Args} = dest_thy_type ty
  in (Thy,Tyop)
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
fun mk_tyvar_size vty (V,away) =
  let val fty = vty --> num
      val v = num_variant away (mk_var("f", fty))
  in (v::V, v::away)
  end
end;

(* Setting up the "theta" parameter to TypeBasePure.type_size_pre,
   which provides pre-set sizes for some types, given the various
   cases here (type parameters, sizes of the new types, and auxiliary
   sizes needed for intermediate types). *)
local
  fun OK f ty M =
         let val (Rator,Rand) = dest_comb M
         in aconv Rator f andalso is_var Rand andalso (type_of Rand = ty)
         end
  fun theta2 (theta,omega) clause ty = case theta ty
  of SOME fvar => SOME fvar
   | NONE =>
      case omega ty
       of SOME (_,[]) => raise ERR "tysize theta2" "bug: no assoc for nested"
        | SOME (_,[(f,szfn)]) => SOME szfn
        | SOME (_,alist) => SOME (snd
             (first (fn (f,sz) => Lib.can (find_term(OK f ty)) (rhs clause))
                  alist))
        | NONE => NONE
in
fun tysize (theta,omega) db clause ty = TypeBasePure.type_size_pre
    (theta2 (theta,omega) clause) db ty
end;

fun dupls [] (C,D) = (rev C, rev D)
  | dupls (h::t) (C,D) = dupls t (if tmem h t then (C,h::D) else (h::C,D));

fun crunch [] = []
  | crunch ((x,y)::t) =
    let val key = #1(dom_rng(type_of x))
        val (yes,no) = partition (fn(x,_) => (#1(dom_rng(type_of x))=key)) t
    in (key, (x,y)::yes)::crunch no
    end;

val zero_rws = [Rewrite.ONCE_REWRITE_RULE [ADD_SYM] ADD_0, ADD_0]

fun define_size_rec ax db =
 let val dtys = Prim_rec.doms_of_tyaxiom ax  (* primary types in axiom *)
     val tyvars = Lib.U (map (snd o dest_type) dtys)
     val (_, abody) = strip_forall(concl ax)
     val (exvs, ebody) = strip_exists abody
     (* list of all constructors with arguments *)
     val conjl = strip_conj ebody
     val bare_conjl = map (snd o strip_forall) conjl
     val capplist = map (rand o lhs) bare_conjl
     val def_name = fst(dest_type(type_of(hd capplist)))
     (* 'a -> num variables : size functions for type variables *)
     val fparams = rev(fst(rev_itlist mk_tyvar_size tyvars
                             ([],free_varsl capplist)))
     val fparams_tyl = map type_of fparams
     val tyvar_map = zip tyvars fparams
     val tyvar_map2 = map (fn (ty, sz) => (ty --> num, sz)) tyvar_map
     fun app_tyvar_szs tm = case assoc1 (fst (dom_rng (type_of tm))) tyvar_map2 of
         NONE => tm
       | SOME (_, sz) => app_tyvar_szs (mk_comb (tm, sz))
     fun proto_const n ty =
         mk_var(n, itlist (curry op-->) fparams_tyl (ty --> num))
     fun mk_ty_size ty =
       let val {Tyop=root_tyop,Thy=root_thy,...} = dest_thy_type ty
       in (ty, app_tyvar_szs (proto_const(root_tyop^"_size") ty)) end
     val ty_sz_map = tyvar_map @ map mk_ty_size dtys
     fun theta tyv = Option.map snd (assoc1 tyv ty_sz_map)
     (* now the ugly nested map *)
     val head_of_clause = head o lhs o snd o strip_forall
     fun is_dty M = mem(#1(dom_rng(type_of(head_of_clause M)))) dtys
     val (dty_clauses,non_dty_clauses) = partition is_dty bare_conjl
     val dty_fns = fst(dupls (map head_of_clause dty_clauses) ([],[]))
     fun dty_size ty =
        let val (d,r) = dom_rng ty
        in list_mk_comb(proto_const(fst(dest_type d)^"_size") d,fparams)
        end
     val dty_map = zip dty_fns (map (dty_size o type_of) dty_fns)
     val non_dty_fns = fst(dupls (map head_of_clause non_dty_clauses) ([],[]))
     fun nested_binding (n,f) =
        let val name = String.concat[def_name,Lib.int_to_string n,"_size"]
            val (d,r) = dom_rng (type_of f)
            val proto_const = proto_const name d
        in (f, list_mk_comb (proto_const,fparams))
       end
     val nested_map0 = map nested_binding (enumerate 1 non_dty_fns)
     val nested_map1 = crunch nested_map0
     fun omega ty = assoc1 ty nested_map1
     val sizer = tysize (theta,omega) db
     fun mk_app cl v = mk_comb(sizer cl (type_of v), v)
     val fn_i_map = dty_map @ nested_map0
     fun clause cl =
         let val (fn_i, capp) = dest_comb (lhs cl)
         in
         mk_eq(mk_comb(op_assoc aconv fn_i fn_i_map, capp),
               case snd(strip_comb capp)
                of [] => Zero
                 | L  => end_itlist (curry numSyntax.mk_plus)
                                    (One::map (mk_app cl) L))
         end
     val pre_defn0 = list_mk_conj (map clause bare_conjl)
     val pre_defn1 = rhs(concl   (* remove zero additions *)
                      ((DEPTH_CONV BETA_CONV THENC
                        Rewrite.PURE_REWRITE_CONV zero_rws) pre_defn0))
                     handle UNCHANGED => pre_defn0
     val defn = new_recursive_definition
                 {name=def_name^"_size_def",
                  rec_axiom=ax, def=pre_defn1}
     val cty = (I##(type_of o last)) o strip_comb o lhs o snd o strip_forall
     val ctyl = op_mk_set tmx_eq (map cty (strip_conj (concl defn)))
     val const_tyl = filter (fn (c,ty) => mem ty dtys) ctyl
     val const_tyopl = map (fn (c,ty) => (c,tyconst_names ty)) const_tyl
 in
    SOME {def=defn,const_tyopl=const_tyopl}
 end
 handle HOL_ERR _ => NONE;

val thm_compare = inv_img_cmp concl Term.compare

val useful_ths = List.take(CONJUNCTS arithmeticTheory.ADD_CLAUSES, 2)


fun size_def_to_comb (db : TypeBasePure.typeBase) opt_ind size_def =
  let
    val eq_rator = rator o lhs o snd o strip_forall
    val size_rators = size_def |> concl |> strip_conj |> map eq_rator
        |> HOLset.fromList Term.compare |> HOLset.listItems
    val aux_measures = map (snd o strip_comb) size_rators |> List.concat
    val measures = size_rators @ aux_measures
        |> HOLset.fromList Term.compare |> HOLset.listItems
    fun def_measure ty =
        hd (filter (fn m => fst (dom_rng (type_of m)) = ty) measures)
    fun fix_measure t =
        if is_abs t then
          hd (filter (fn m => type_of m = type_of t) measures @ [t])
        else if is_comb t then
          mk_comb (fix_measure (rator t), fix_measure (rand t))
        else t
    fun measure sz = TypeBasePure.type_size db (fst (dom_rng (type_of sz)))
        |> fix_measure
    val hd_ty = size_def |> concl |> strip_conj |> hd |> eq_rator
        |> type_of |> dom_rng |> fst
    val ind = case opt_ind of SOME ind => ind
        | _ => TypeBasePure.fetch db hd_ty |> valOf |> TypeBasePure.induction_of
    val ind_tys =
        concl ind |> strip_forall |> snd |> strip_imp |> snd |> strip_conj
              |> map (type_of o fst o dest_forall)
    fun remdups (x :: y :: zs) = if term_eq x y then remdups (y :: zs)
                                 else x :: remdups (y :: zs)
      | remdups xs = xs
    val szs = size_def |> concl |> strip_conj |> map eq_rator |> remdups
    fun sz_all_eq sz = let
        val m = measure sz
        val x = mk_var ("x", fst (dom_rng (type_of m)))
        val eq = mk_eq (mk_comb (sz, x), mk_comb (m, x))
      in mk_forall (x, eq) end
    val eqs = map sz_all_eq szs |> list_mk_conj
    val others = filter (fn sz => not (term_eq (measure sz) sz)) size_rators
    fun size_rule ty = TypeBasePure.fetch db ty |> valOf |> TypeBasePure.size_of
            |> valOf |> snd
    val size_rules = others |> map (fst o dom_rng o type_of) |> map size_rule
    val size_eqs = size_rules |> HOLset.fromList thm_compare |> HOLset.listItems
        |> map (size_def_to_comb db NONE)
    val size_def' = REWRITE_RULE [boolTheory.ITSELF_EQN_RWT] size_def
  in
    if null others then TRUTH
    else prove (eqs,
                ho_match_mp_tac ind
                \\ REWRITE_TAC (size_def' :: size_eqs @ size_rules @ useful_ths)
                \\ rpt strip_tac
                \\ BETA_TAC
                \\ ASSUM_LIST REWRITE_TAC)
               |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ
               |> REWRITE_RULE [GSYM FUN_EQ_THM]
  end

val prove_size_eqs = ref true

fun define_size {induction, recursion} db = case define_size_rec recursion db of
    NONE => NONE
  | SOME r => if ! prove_size_eqs then let
    val comb_eqs = size_def_to_comb db (SOME induction) (#def r)
      handle HOL_ERR err =>
        let in
        print "Error proving size_eqs, consider DataSize.prove_size_eqs := false\n\n";
        raise (HOL_ERR err) end
    val dtys = Prim_rec.doms_of_tyaxiom recursion
    val def_name = fst(dest_type(hd dtys))
    val _ = save_thm (def_name ^ "_size_eq", comb_eqs)
  in SOME r end
  else SOME r

end
