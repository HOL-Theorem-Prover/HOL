structure abstraction :> abstraction =
struct

open HolKernel Parse boolLib;
infix o |->;

fun ABS_ERR function message =
    HOL_ERR{origin_structure = "abs_tools",
		      origin_function = function,
		      message = message};

val curr_assums = ref ([]:term list);
val fv_ass = ref ([]:term list);


fun add_parameter v =
  let val _ = dest_var v in
  fv_ass := v :: !fv_ass
  end;

fun get_assums () = !curr_assums;

fun set_assums asl =
  (curr_assums := asl;
   fv_ass := free_varsl asl)
;

fun add_assums asl =
  (curr_assums := rev asl @ !curr_assums;
   fv_ass := subtract (free_varsl asl) (!fv_ass) @ !fv_ass)
;


fun select_disch (h,th) =
  if HOLset.member(hypset th, h) then DISCH h th
  else th;

(* Only the variables appearing in the discharged hypothese should
 * be generalized.
 *)
fun gen_assums thm =
  GENL (!fv_ass) (foldr select_disch thm (!curr_assums));



val impl_param_cstr = ref ([]:(string * term list) list);
fun add_impl_param x p =
  impl_param_cstr := (x,p)::(!impl_param_cstr);
fun impl_of x =
  map Absyn.mk_AQ (assoc x (!impl_param_cstr)) handle HOL_ERR _ => []



fun head tm =
  let val a = fst(strip_comb(lhs
                 (snd(strip_forall(Lib.trye hd (strip_conj tm))))))
  in
    fst(dest_var a handle HOL_ERR _ => dest_const a)
  end;

fun param_eq eqs0 =
 let val nm = head eqs0
     val eqs = map (snd o strip_forall) (strip_conj eqs0)
     val fvrhs = subtract (free_varsl (map rhs eqs)) (free_varsl (map lhs eqs))
     val pv = filter (C mem fvrhs) (!fv_ass)
     val ty = type_of(fst(strip_comb(lhs(hd eqs))))
     val old_var = mk_var(nm, ty)
     val newvar = mk_var(nm, foldr (op -->) ty (map type_of pv))
     val _ = if null pv then () else add_impl_param nm pv
 in subst [old_var |-> list_mk_comb(newvar,pv)] eqs0
 end;

fun new_param_definition (x,tm) = new_definition(x, param_eq tm);



(* Instantiating variables such that general constants can be replaced by
 * the local constants.
 * Could be improved (both in efficiency and soundness!).
 *)

fun is_defd sub v = exists (fn {redex,residue} => v=redex) sub;

fun except_assoc x [] = raise ABS_ERR "except_assoc" ""
  | except_assoc x ((s as {redex,residue})::l) =
      if x=redex then (residue,l)
      else
	let val (v,nsub) = except_assoc x l in
	(v,s::nsub)
	end
;

fun majo NONE o2 = o2
  | majo o1 NONE = o1
  | majo (SOME x1) (SOME x2) =
      if x1=x2 then (SOME x1)
      else raise ABS_ERR "under_conj"
	  "vars were instantiated differently in conjuncts"
;

fun under_conj f th =
  case (f (CONJUNCT1 th), f (CONJUNCT2 th)) of
    ((NONE, _),(NONE, _)) => (NONE, th)
  | ((o1,th1),(o2,th2)) => (majo o1 o2, CONJ th1 th2)
;


fun under_forall f th =
  let val qvars = fst(strip_forall(concl th))
      val thm = SPECL qvars th
      val (ovars,rthm) = f thm in
  case ovars of
    SOME (ivars,ti) =>
      let val (rsub,thm) =
	foldr (fn (x,(sub,th)) =>
	  let val (v,nsub) = except_assoc (inst ti x) sub in
	  (nsub,SPEC v (GEN (inst ti x) th))
	  end
	  handle HOL_ERR _ => (sub,GEN (inst ti x) th)) (ivars,rthm) qvars
      in (SOME (rsub,ti), thm)
      end
  | NONE => (NONE,th)
  end
;

fun under_all f th =
  if is_forall (concl th) then under_forall (under_all f) th
  else if is_conj (concl th) then under_conj (under_all f) th
  else f th
;


fun first_match env mfun [] = raise ABS_ERR "first_match" "no match"
  | first_match env mfun (x::l) =
      (let val (vi,ti) = mfun x in
      if exists (fn {redex,residue} => mem redex env) vi then
	raise ABS_ERR "" ""
      else (vi,ti)
      end
      handle HOL_ERR _ => first_match env mfun l)
;


fun inst_csts inst env tm =
  case dest_term tm of
    LAMB(Bvar,Body) => inst_csts inst (Bvar::env) Body
  | COMB(Rator,Rand) =>
      (SOME (first_match env (match_term tm) inst)
       handle HOL_ERR _ =>
	 (case inst_csts inst env Rand of
	   SOME i => SOME i
	 | NONE => inst_csts inst env Rator))
  | _ => NONE
;


fun inst_thm inst thm =
  case inst_csts inst [] (concl thm) of
    NONE => (NONE,thm)
  | SOME(vi,ti) => (SOME (vi,ti), INST_TYPE ti thm)
;

fun inst_all ctab thm =
  let val (osub,thm) = under_all (inst_thm ctab) thm in
  case osub of
    SOME (sub,ti) =>
      foldl (fn ({redex,residue},th) => SPEC residue (GEN redex th))
	thm sub
  | NONE => thm
  end
  handle HOL_ERR _ => thm;

(* example:
   inst_all [--`0+0`--,--`0-0`--]
      (GEN_ALL(CONJ(GEN (--`y:num`--) (REFL(--` x+y = x-y `--)))
                 (REFL(--`z`--))))
    ;
*)


fun inst_hyp (h,thm) =
  MATCH_MP thm h
  handle HOL_ERR _ => thm
;

fun import_fun inst thm =
  foldl inst_hyp thm inst
;


(*----------------*)

type inst_infos =
    { Vals : term list,
      Inst : thm list,
      Rule : thm -> thm,
      Rename : string -> string option };

type cinst_infos =
    { Inst : thm list, Rule : thm -> thm, Csts : term list, Defs : thm list };


fun compute_inst_infos ctab ({Rename,Inst,Rule,...}:inst_infos) =
  let fun mk_def tm =
        case Rename(#Name(dest_thy_const(fst(strip_comb tm)))) of
	  SOME name => SOME(name^"_def", mk_eq(mk_var(name,type_of tm),tm))
	| NONE => NONE
      val defs = List.mapPartial mk_def ctab
      val thms = map (GSYM o new_param_definition) defs
  in { Csts=ctab, Defs=thms, Inst=Inst, Rule=Rule }
  end;

fun inst_thm_fun { Inst=inst, Rule=f, Csts=ctab, Defs=thms } =
    f o REWRITE_RULE thms o inst_all ctab o import_fun inst
;


(* --> abs_tools ? *)

fun pr_list_sep f sep l = Portable.pr_list f sep (fn () => ()) l;

val S = PP.add_string;
val NL = PP.add_newline;
fun N strm = PP.add_string strm o int_to_string;



fun functor_header strm =
  (S strm "fun IMPORT P =";  NL strm)
;

fun compute_cst_arg_map (fv,impargs) strm =
  let val thcsts = map (#Name o dest_thy_const) (constants(current_theory()))
      fun is_param_cst (x,iargs) =
        mem x thcsts andalso all (C mem fv) iargs
      val ptab = filter is_param_cst impargs
      val pr_var = S strm o fst o dest_var
      fun sep() = (S strm ","; NL strm; S strm "          ")
  in
  S strm "  let open Parse abstraction";                  NL strm;
  S strm "      fun sing [x] = x | sing _ = raise Match"; NL strm;
  S strm "      val ";
    pr_list_sep pr_var (fn() => S strm ",") (!fv_ass);
    S strm " = sing (#Vals P)"; NL strm;
  S strm "      val ctab =";    NL strm;
  S strm "        [ ";
  pr_list_sep (fn (x,iargs) =>
      (S strm ("Term`"^x^" ");
       pr_list_sep (fn v => (S strm "^"; pr_var v)) (fn()=>S strm " ") iargs;
       S strm "`"))
    sep ptab;
  S strm " ]";   NL strm;
  S strm "      val inst_fun = inst_thm_fun (compute_inst_infos ctab P) in";
    NL strm
  end
;

fun export_param_theory () = let
  val _ = Theory.scrub()
  val defs = rev (map fst (definitions"-"))
  val thms = rev (map fst (theorems"-"))
  fun struct_line ppstrm thn =
      (S ppstrm thn; S ppstrm " = inst_fun "; S ppstrm thn)
  fun sig_line ppstrm thn =
      (S ppstrm thn; S ppstrm " : thm")
  fun sep ppstrm () =
      (S ppstrm ",";
       NL ppstrm;
       S ppstrm "    ")
  val adj = {
    sig_ps =
      SOME (fn ppstrm =>
    	       (S ppstrm "val IMPORT : abstraction.inst_infos ->"; NL ppstrm;
	        S ppstrm "  { ";
	        pr_list_sep (sig_line ppstrm) (sep ppstrm) (defs@thms);
	        S ppstrm " }"; NL ppstrm)),
    struct_ps =
      SOME (fn ppstrm =>
	       (functor_header ppstrm;
	        compute_cst_arg_map (!fv_ass, !impl_param_cstr) ppstrm;
	        S ppstrm "  { ";
	        pr_list_sep (struct_line ppstrm) (sep ppstrm) (defs@thms);
	        S ppstrm " }"; NL ppstrm;
	        S ppstrm "  end"; NL ppstrm ))}
in
  adjoin_to_theory adj;
  export_theory()
end;


end;
