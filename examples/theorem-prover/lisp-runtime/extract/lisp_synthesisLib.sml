structure lisp_synthesisLib :> lisp_synthesisLib =
struct

open HolKernel boolLib bossLib;
open lisp_extractTheory lisp_extractLib;
open lisp_compilerTheory;

open stringTheory finite_mapTheory pred_setTheory listTheory sumTheory;
open optionTheory arithmeticTheory relationTheory;
open stringLib pairSyntax;


(* we define lisp_Define and lisp_tDefine which record definitions
   that are to be exported to verified deep embeddings *)

local
  val defs_inds = ref (tl [("",TRUTH,TRUTH)])
in
  fun add_def def = let
    val name = def |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
                   |> dest_const |> fst
    val ind_name = name ^ "_ind"
    val ind = fetch "-" ind_name handle HOL_ERR _ => TRUTH
    val xs = filter (fn (n,def,ind) => not (n = name)) (!defs_inds)
    val _ = defs_inds := xs @ [(name,def,ind)]
    in def end
  fun get_defs_inds () = !defs_inds
end

fun lisp_Define t = add_def (Define t);
fun lisp_tDefine name t tac = add_def (tDefine name t tac);


(* the main synthesis function: shallow -> deep *)

fun synthesise_deep_embeddings () = let
  val defs_inds = map (fn (name,def,ind) => (def,ind)) (get_defs_inds())
  val base_name = "deep_embedding"
  val (deep,certs) = deep_embeddings base_name defs_inds
  val deep_simp = SIMP_RULE std_ss [GSYM CONJ_ASSOC,fns_assum_def,EVERY_DEF] deep
  (* printing in Lisp syntax *)
  val xs = deep |> SPEC_ALL |> concl |> rand |> rand
  val tm = EVAL ``verified_string ^xs`` |> concl |> rand
  val _ = if can (match_term ``NONE:'a option``) tm then () else let
            val str = stringSyntax.fromHOLstring (rand tm)
            in print ("\n\nDeep embedding in Lisp syntax:\n\n" ^ str ^ "\n\n") end
  in LIST_CONJ (deep_simp::certs) end


end
