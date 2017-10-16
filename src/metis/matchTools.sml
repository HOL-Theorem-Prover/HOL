(* ========================================================================= *)
(* ADDITIONS TO HOL TERM AND TYPE MATCHING.                                  *)
(* Created by Joe Hurd, June 2002.                                           *)
(* ========================================================================= *)

(*
*)
structure matchTools :> matchTools =
struct

open HolKernel Parse boolLib;

infix THENR ## |->;

type tySubst = (hol_type, hol_type) subst;
type Subst   = (term, term) subst * tySubst;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

local
  open mlibUseful;
  val module = "matchTools";
in
  val () = traces := {module = module, alignment = I} :: !traces;
  fun chatting l = tracing {module = module, level = l};
  fun chat s = (trace s; true)
  val ERR = mk_HOL_ERR module;
  fun BUG f m = Bug (f ^ ": " ^ m);
end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun assert b e = if b then () else raise e;

fun zipwith f =
  let
    fun z l [] [] = l
      | z l (x :: xs) (y :: ys) = z (f x y :: l) xs ys
      | z _ _ _ = raise ERR "zipwith" "lists different lengths";
  in
    fn xs => fn ys => rev (z [] xs ys)
  end;

fun chain [] = []
  | chain [_] = []
  | chain (x :: (xs as y :: _)) = (x, y) :: chain xs;

fun check_redexes p = List.all (fn {redex, residue} => p redex);

fun residue_map f = map (fn {redex, residue} => redex |-> f residue);

(* ------------------------------------------------------------------------- *)
(* Basic operations on substitutions.                                        *)
(* Public health warning: don't use cyclic substitutions!                    *)
(* ------------------------------------------------------------------------- *)

fun inst_ty (_, tyS) tm = inst tyS tm;

fun pinst (tmS, tyS) tm = subst tmS (inst tyS tm);

local
  fun fake_asm_op r th =
    let val h = rev (hyp th)
    in (funpow (length h) UNDISCH o r o C (foldl (uncurry DISCH)) h) th
    end
in
  val INST_TY = fake_asm_op o INST_TYPE;
  val PINST   = fake_asm_op o INST_TY_TERM;
end;

fun type_refine_subst [] tyS' : (hol_type, hol_type) subst = tyS'
  | type_refine_subst tyS [] = tyS
  | type_refine_subst tyS tyS' =
  tyS' @ (map (fn {redex, residue} => redex |-> type_subst tyS' residue) tyS);

fun refine_subst ([], []) sub' = sub'
  | refine_subst sub ([], []) = sub
  | refine_subst (tmS, tyS) (tmS', tyS') =
  let fun f {redex, residue} = inst tyS' redex |-> pinst (tmS', tyS') residue
  in (tmS' @ map f tmS, type_refine_subst tyS tyS')
  end;

(* ------------------------------------------------------------------------- *)
(* Raw matching.                                                             *)
(* ------------------------------------------------------------------------- *)

type raw_subst =
  ((term,term)subst * term set) * ((hol_type,hol_type)subst * hol_type list);

val empty_raw_subst : raw_subst = (([], empty_tmset), ([], []));

fun raw_match_term ((tmS, tmIds), (tyS, tyIds)) tm1 tm2 =
  raw_match tyIds tmIds tm1 tm2 (tmS, tyS);

local
  fun mk_tm ty =
    mk_thy_const {Thy = "combin", Name = "K", Ty = bool --> ty --> bool};
in
  fun raw_match_ty sub ty1 ty2 = raw_match_term sub (mk_tm ty1) (mk_tm ty2);
end;

val finalize_subst = norm_subst;

(* ------------------------------------------------------------------------- *)
(* Operations on types containing "locally constant" variables.              *)
(* ------------------------------------------------------------------------- *)

type tyVars = hol_type -> bool;

fun vmatch_type tyvarP ty ty' =
  let
    val tyS = match_type ty ty'
    val () = assert (check_redexes tyvarP tyS) (ERR "vmatch_type" "")
  in
    tyS
  end;

fun vunifyl_type tyvarP =
  let
    fun unify sub [] = sub
      | unify sub ((ty, ty') :: work) =
      unify' sub work (type_subst sub ty) (type_subst sub ty')
    and unify' sub work ty ty' =
      if ty = ty' then unify sub work
      else if tyvarP ty then
        if type_var_in ty ty' then raise ERR "unify_type" "occurs"
        else unify (type_refine_subst sub [ty |-> ty']) work
      else if tyvarP ty' then unify' sub work ty' ty
      else if is_vartype ty orelse is_vartype ty' then
        raise ERR "unify_type" "locally constant variable"
      else
        let
          val (f , args ) = dest_type ty
          val (f', args') = dest_type ty'
        in
          if f = f' andalso length args = length args' then
            unify sub (zip args args' @ work)
          else raise ERR "unify_type" "different type constructors"
        end
  in
    unify
  end;

fun vunify_type tyvarP = vunifyl_type tyvarP [] o chain;

(* ------------------------------------------------------------------------- *)
(* Operations on terms containing "locally constant" variables.              *)
(* ------------------------------------------------------------------------- *)

type tmVars = term -> bool;
type Vars   = tmVars * tyVars;

fun vfree_names tmvarP tm =
  let
    val names = map (fst o dest_var) (filter tmvarP (free_vars tm))
    open Binaryset
  in
    listItems (addList (empty String.compare, names))
  end;

fun vfree_vars (tmvarP, tyvarP) tm =
  (filter tmvarP (free_vars tm), filter tyvarP (type_vars_in_term tm));

fun vmatch (tmvarP, tyvarP) tm tm' =
  let
    val sub = match_term tm tm'
    val (tmS, tyS) = sub
    val () = assert (check_redexes tyvarP tyS) (ERR "vmatch_term" "lconst ty")
    val () = assert (check_redexes tmvarP tmS) (ERR "vmatch_term" "lconst tm")
  in
    sub
  end;

fun vunifyl (tmvarP, tyvarP) =
  let
    val varname = fst o dest_var
    fun occurs v = List.exists (equal (varname v) o varname) o free_vars
    val pure_unify_type = vunify_type tyvarP
    fun unify_type sub tyL = refine_subst sub ([], pure_unify_type tyL)
    fun unify_var_type sub v tm =
      let val s = pure_unify_type [type_of v, type_of tm]
      in refine_subst sub ([inst s v |-> inst s tm], s)
      end
    fun unify sub [] = sub
      | unify sub ((tm, tm') :: work) =
      unify' sub work (pinst sub tm) (pinst sub tm')
    and unify' sub work tm tm' =
      if aconv tm tm' then unify sub work
      else if tmvarP tm then
        if tmvarP tm' andalso varname tm = varname tm' then
          unify (unify_type sub [type_of tm, type_of tm']) work
        else if occurs tm tm' then raise ERR "unify_term" "occurs"
        else unify (unify_var_type sub tm tm') work
      else if tmvarP tm' then unify' sub work tm' tm
      else
        case (dest_term tm, dest_term tm') of (VAR (n, ty), VAR (n', ty'))
          => if n <> n' then raise ERR "unify_term" "different variables"
             else unify (unify_type sub [ty, ty']) work
        | (CONST {Thy, Name, Ty}, CONST {Thy = Thy', Name = Name', Ty = Ty'})
          => if Thy <> Thy' orelse Name <> Name' then
               raise ERR "unify_term" "different constants"
             else unify (unify_type sub [Ty, Ty']) work
        | (COMB (a, b), COMB (a', b')) => unify' sub ((b, b') :: work) a a'
        | (LAMB _, LAMB _) => raise ERR "unify_term" "can't deal with lambda"
        | _ => raise ERR "unify_term" "different structure"
  in
    unify
  end;

fun vunify varP = vunifyl varP ([], []) o chain;

local
  val uniq = ref 0;
  fun new_num () = let val n = !uniq val () = uniq := (n + 1) in n end;
  fun new_name () = "XXfrozenXX" ^ int_to_string (new_num ())
  fun correspond tmvarP = map (fn n => (n, new_name ())) o vfree_names tmvarP;
  fun revc c = map (fn (a, b) => (b, a)) c;
  fun csub c tm =
    let
      fun g v (_, y) = v |-> mk_var (y, type_of v)
      fun f v = Option.map (g v) (assoc1 (fst (dest_var v)) c)
      val tmS = List.mapPartial f (free_vars tm)
    in
      subst tmS tm
    end;
in
  fun vmatch_uty (varP as (tmvarP, _)) tm tm' =
    let
      val c = correspond tmvarP tm'
      val gtm' = csub c tm'
      val (tmS, tyS) = vunify varP [tm, gtm']
      val sub = (residue_map (csub (revc c)) tmS, tyS)
    in
      sub
    end;
end;

end
