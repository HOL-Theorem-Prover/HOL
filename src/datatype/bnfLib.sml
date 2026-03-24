structure bnfLib :> bnfLib =
struct

open HolKernel bnfBase stmonad

val ERR = mk_HOL_ERR "bnfLib"

type convert_state = {
  tyvars : hol_type Symtab.table * int,
  mutrecvars : hol_type Symtab.table * int
}
fun updtyvars f {tyvars,mutrecvars} =
    {tyvars = f tyvars, mutrecvars = mutrecvars}
fun updmvs f {tyvars,mutrecvars} =
    {tyvars = tyvars, mutrecvars = f mutrecvars}
fun updtab p (tab,c) = (Symtab.update p tab, c + 1)

fun cs_tylookup s (cst:convert_state) =
    (cst, Symtab.lookup (#1 (#tyvars cst)) s)
fun cs_mvlookup s (cst:convert_state) =
    (cst, Symtab.lookup (#1 (#mutrecvars cst)) s)

fun newty k (cst:convert_state) =
    let val new = mk_vartype ("'b" ^ Int.toString (#2 (#tyvars cst)))
    in
      (updtyvars (updtab (k,new)) cst, new)
    end
fun newmv k (cst:convert_state) =
    let val new = mk_vartype("'a" ^ Int.toString (#2 (#mutrecvars cst)))
    in
      (updmvs (updtab (k, new)) cst, new)
    end

val empty_cstate = {tyvars = (Symtab.empty, 1), mutrecvars = (Symtab.empty, 1)}

fun convertTy ty =
    if is_vartype ty then
      let val oldnm = dest_vartype ty
      in
        cs_tylookup oldnm >-
        (fn opt =>
          case opt of
             NONE => newty oldnm
           | SOME ty' => return ty')
      end
    else
      let val {Thy,Tyop,Args} = dest_thy_type ty
      in
        mmap convertTy Args >-
        (fn args' =>
          return (mk_thy_type{Args = args',Tyop=Tyop,Thy=Thy}))
      end

(* assume that ftor is used only when at least one of the arguments does
   contain an instance of the_arg or a mutrec_var *)
fun specToFunctor0 s =
    case s of
        ftor (knm, args) =>
        mmap specToFunctor0 args >-
        (fn args' =>
            return $ mk_thy_type{
              Args = args', Thy = #Thy knm, Tyop = #Name knm})
      | the_arg => return alpha
      | constty ty => convertTy ty
      | mutrec_var s =>
        cs_mvlookup s >-
        (fn opt =>
            case opt of
                NONE => newmv s
              | SOME ty => return ty)
      | previous_op s => raise Fail "previous_op encountered in specToFunctor0"

fun specToFunctor s = #2 (specToFunctor0 s empty_cstate)

fun is_maparg ty =
    let val (d,r) = dom_rng ty
        val dnm = dest_vartype d
        val rnm = dest_vartype r
        val dsfx = String.extract(dnm, 2, NONE)
        val rsfx = String.extract(rnm, 2, NONE)
    in
      String.isPrefix "'a" dnm andalso String.isPrefix "'c" rnm andalso
      dsfx = rsfx andalso CharVector.all Char.isDigit dsfx
    end handle Subscript => false | HOL_ERR _ => false

fun strip_mapargs ty =
    let val (d,r) = dom_rng ty
    in
      if is_maparg d then
        let val (rest, base) = strip_mapargs r
        in
          (d::rest, base)
        end
      else ([], (d,r))
    end

fun is_alphanum_tyv ty =
    let val s = dest_vartype ty
    in
      String.isPrefix "'a" s andalso size s > 2 andalso
      CharVector.all Char.isDigit (String.extract(s, 2, NONE))
    end

val map_f = mk_var("f", alpha --> beta)
val equal_alpha = boolSyntax.equality
val empty_alpha = pred_setSyntax.mk_empty alpha
fun K0 ty =
    mk_comb(
      Term.inst[alpha |-> (alpha --> bool), beta |-> ty] combinSyntax.K_tm,
      empty_alpha
    )

val aset_ty = alpha --> bool
val bset_ty = beta --> bool
val BIMG = let (* (o) BIGUNION o IMAGE ; generating an α set; other var is β *)
  val imgtm = mk_thy_const{
        Thy = "pred_set", Name = "IMAGE",
        Ty = (beta --> aset_ty) --> bset_ty --> (aset_ty --> bool)}
  val bu_tm = pred_setSyntax.bigunion_tm
  val o1_tm = mk_thy_const{
        Thy = "combin", Name = "o",
        Ty = type_of bu_tm --> (bset_ty --> (aset_ty --> bool)) -->
             (bset_ty --> aset_ty)}
  val obu = mk_comb(o1_tm, bu_tm)
in
  combinSyntax.mk_o(obu, imgtm)
end

val o_tm = mk_thy_const{
      Thy = "combin", Name = "o",
      Ty = (beta --> gamma) --> ((alpha --> beta) --> (alpha --> gamma))
    }
val UNION_tm = mk_thy_const{
      Thy = "pred_set", Name = "UNION",
      Ty = aset_ty --> (aset_ty --> aset_ty)}

fun mk_lifted_union (f1,f2) =
    (* f1 and f2 have same type, schematically some-β → α set;
       i.e., range type is literally α, domain can vary
       generate S((UNION) o f1)f2
     *)
    let
      val (b,_) = dom_rng (type_of f1)
      val Uof1 = combinSyntax.mk_o(UNION_tm, f1)
      val Stm = mk_thy_const{Thy = "combin", Name = "S",
                             Ty = (b --> (aset_ty --> aset_ty)) -->
                                  ((b --> aset_ty) --> (b --> aset_ty))}
    in
      list_mk_comb(Stm, [Uof1, f2])
    end

fun biCompare (bI info1, bI info2) = Type.compare(#canontype info1, #canontype info2)
val empty_biset : thm info set = HOLset.empty biCompare

fun functorToMapAndSet (bnfDB:bnfBase.t) ty =
    if ty = alpha then (map_f, equal_alpha, empty_biset)
    else if not $ mem alpha $ type_vars ty then
      (Term.inst [alpha |-> ty] combinSyntax.I_tm, K0 ty, empty_biset)
    else let
      val {Tyop,Thy,Args} = dest_thy_type ty
    in
      case pure_lookup bnfDB {Name=Tyop,Thy=Thy} of
          NONE => raise ERR "functorToMap" (Thy^"$"^Tyop ^ " is not a BNF")
        | SOME (bI info) =>
          let val map_t = #map info
              val set_tms = #set info
              val (args, (d,r)) = strip_mapargs (type_of map_t)
              (* d of form (..,..,..) tyop, where an arg is 'aₙ if functorial
                 recursion is possible there *)
              val functor_params = #Args (dest_thy_type d)
              fun foldthis (actual,parameter,(i,mapA : term list,setA : term list,bisA)) =
                  case (is_alphanum_tyv parameter, mem alpha $ type_vars actual) of
                      (true, true) =>
                      let
                        val (submap, subset, bis) = functorToMapAndSet bnfDB actual
                      in
                        (i + 1, submap :: mapA, subset :: setA, HOLset.union(bisA,bis))
                      end
                    | (true, false) =>
                      let
                        val nullmap = Term.inst [alpha |-> actual] combinSyntax.I_tm
                        val nullset = mk_comb(
                              Term.inst [alpha |-> alpha --> bool, beta |-> actual]
                                        combinSyntax.K_tm,
                              pred_setSyntax.empty_tm
                            )
                      in
                        (i + 1,  nullmap :: mapA, nullset :: setA, bisA)
                      end
                    | (false, false) => (i + 1, mapA, setA, bisA)
                    | (false, true) =>
                      raise ERR "functorToMapAndSet"
                            (Thy^"$"^Tyop^ " is not functorial in argument " ^
                             Int.toString i)
              val (_, submaps, subsets, bis) =
                  ListPair.foldlEq foldthis
                                   (0,[],[], HOLset.singleton biCompare (bI info))
                                   (Args,functor_params)
              fun liftset (f,set) =
                  (* returns BIMG f o set *)
                  let val (fd, fr) = dom_rng (type_of f)
                      val BIMGf = mk_comb(inst [beta |-> fd] BIMG, f)
                      val set_theta = match_type (type_of set) (ty --> (fd --> bool))
                  in
                    combinSyntax.mk_o(BIMGf, inst set_theta set)
                  end
              val lifted_sets = ListPair.mapEq liftset (List.rev subsets, set_tms)
              val Usets = List.foldl (fn (t,A) => mk_lifted_union(A,t))
                                     (hd lifted_sets)
                                     (tl lifted_sets)
          in
            (list_mk_icomb map_t (List.rev submaps),Usets, bis)
          end
    end

(*
fun mk_option_ftor ft = ftor({Thy="option", Name = "option"}, [ft])

val f = ftor(
  {Thy="sum", Name = "sum"}, [
    ftor({Thy="option", Name = "option"}, [
      ftor({Thy="pair", Name = "prod"}, [constty ``:'c``, the_arg])
    ]),
    mk_option_ftor $
     ftor({Thy = "min", Name = "fun"}, [
       constty “:num”,
       the_arg
     ])
  ])

val fty = specToFunctor f
val (fmap, fset) = functorToMapAndSet (fullDB()) fty

Overload "∪ₗ" = “λf1 f2. S ($UNION o f1) f2”
Overload BIMG = “(o) BIGUNION o IMAGE”

*)





end
