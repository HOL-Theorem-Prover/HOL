structure binderSyntax :> binderSyntax =
struct

open HolKernel boolLib nomsetTheory

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars nomsetTheory.nomset_grammars
end
open Parse

val mk_prod = pairSyntax.mk_prod
val atom_ty = mk_thy_type{Thy="basic_swap",Args=[],Tyop="atom"}
val mk_list_type = listSyntax.mk_list_type

val cperm_ty = mk_list_type (mk_prod(atom_ty, atom_ty))

fun mk_perm_type ty = cperm_ty --> (ty --> ty)
fun dest_perm_type ty = let
  val (d,r) = dom_rng ty
in
  if Type.compare(d, cperm_ty) = EQUAL then let
      val (r1, r2) = dom_rng ty
    in
      if Type.compare(r1, r2) = EQUAL then r1
      else failwith ""
    end
  else failwith ""
end handle HOL_ERR _ => raise mk_HOL_ERR "binderSyntax" "dest_perm_type"
                                         "Type not a permutation type"
val is_perm_type = can dest_perm_type


val is_perm_t = mk_thy_const {Thy = "nomset", Name = "is_perm",
                              Ty = mk_perm_type alpha --> bool}

val fnpm_t = mk_thy_const {Thy = "nomset", Name = "fnpm",
                           Ty = mk_perm_type alpha --> mk_perm_type beta -->
                                mk_perm_type (alpha --> beta)}
val pairpm_t = mk_thy_const {Thy = "pairpm", Name = "pairpm",
                             Ty = mk_perm_type alpha --> mk_perm_type beta -->
                                  mk_perm_type (mk_prod(alpha, beta))}
val listpm_t = mk_thy_const {Thy = "listpm", Name = "listpm",
                             Ty = mk_perm_type alpha -->
                                  mk_perm_type (mk_list_type alpha)}
val atompm_t = mk_thy_const {Thy = "basic_swap", Name = "lswap",
                               Ty = mk_perm_type atom_ty}
val nullpm_t = combinSyntax.mk_K_1 (combinSyntax.I_tm, cperm_ty)

fun mk_fnpm (dp, rp) = let
  val dty = dest_perm_type (type_of dp)
  val rty = dest_perm_type (type_of rp)
  val fnpm = Term.inst [alpha |-> dty, beta |-> rty] fnpm_t
in
  list_mk_comb(fnpm, [dp, rp])
end



(* storage of permutation information *)

val table_data =
    [(("min", "fun"), (fnpm_t, fnpm_is_perm)),
     (("pair", "prod"), (pairpm_t, pairpm_is_perm)),
     (("list", "list"), (listpm_t, listpm_is_perm)),
     (("string", "string"), (``lswapstr``, perm_of_is_perm))]
val permtable =
    ref (List.foldl (fn ((k,v), t) => Binarymap.insert(t,k,v))
                    (Binarymap.mkDict
                       (pair_compare(String.compare, String.compare)))
                    table_data)

fun type_perm ty = let
  val {Tyop,Thy,Args} = dest_thy_type ty
  val (con,thm) = Binarymap.find (!permtable, (Thy,Tyop))
      handle Binarymap.NotFound =>
             (``K I : ^(ty_antiq ty) pm``,
              INST_TYPE [alpha |-> ty] discrete_is_perm)
  val (arg_cons, arg_ths) = ListPair.unzip (map type_perm Args)
in
  if null arg_cons then (con, thm)
  else let
      val arg_th = LIST_CONJ arg_ths
    in
      (list_mk_icomb(con, arg_cons),
       MP (PART_MATCH (rand o rator) thm (concl arg_th)) arg_th)
    end
end handle HOL_ERR _ => let
             val s = String.extract(dest_vartype ty, 1, NONE)
             val v = mk_var(s ^ "pm", ``:^ty pm``)
           in
             (v, ASSUME (mk_icomb(is_perm_t, v)))
           end

(* this still needs tidying up *)
val ok_perms = [``pairpm``, ``fnpm``, ``listpm``, ``cpmpm``, ``setpm``,
                ``lswapstr``]

fun is_perm_comb t = let
  val (f, arg) = dest_comb t
  val (pmfn, pi) = dest_comb f
in
  (type_of pi = ``:(string # string) list`` andalso
   (is_var pmfn orelse
    isSome (List.find (same_const (#1 (strip_comb pmfn))) ok_perms)) andalso
   (type_of t = type_of arg)) orelse
  same_const ``basic_swap$swapstr`` (rator pmfn)
end handle HOL_ERR _ => false

fun pm_comb_CONV t = let
  val _ = is_perm_comb t orelse failwith "Term not a perm"
  val (f, arg) = dest_comb t
  val _ = is_comb arg orelse failwith "arg is not a comb"
  val (pmfn, pi) = dest_comb f
  val (hdpm, _) = strip_comb pmfn
  val _ = isSome (List.find (same_const hdpm) ok_perms) orelse is_var hdpm
          orelse failwith "not a perm"
  val _ = not (is_perm_comb arg) orelse failwith "Arg is a perm itself"
  val (dpm, dth) = type_perm (type_of (rand arg))
  val rwt0 = ISPECL [dpm, pmfn, pi, rator arg,
                     list_mk_comb(dpm, [pi, rand arg])] fnpm_def
  val inverse = CONJUNCT2 (MATCH_MP (Q.GEN `f` is_perm_inverse) dth)
  val rwt = CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV (REWR_CONV inverse))))
                      rwt0
in
  SYM rwt
end

val fnpm_lam = prove(
  ``fnpm dpm rpm pi f = \x. rpm pi (f (dpm (REVERSE pi) x))``,
  REWRITE_TAC [FUN_EQ_THM, fnpm_def]);

fun pm_abs_CONV t = let
  val (f, args) = strip_comb t
  val _ = same_const fnpm_t f orelse raise failwith "Not a fnpm"
  val _ = length args = 4 orelse
          raise failwith "Not a fnpm with right # of args"
  val [dpm, rpm, pi, abs] = args
  val _ = is_abs abs orelse raise failwith "Not applied to an abstraction"
in
  (REWR_CONV fnpm_lam THENC ABS_CONV (RAND_CONV BETA_CONV) THENC
   RENAME_VARS_CONV [#1 (dest_var (#1 (dest_abs abs)))]) t
end

end (* struct *)
