(*****************************************************************************)
(* FILE          : instance.sml                                              *)
(* DESCRIPTION   : Conversional for increasing the power of a conversion by  *)
(*                 allowing it to work on a substitution instance of a term  *)
(*                 that is acceptable to it.                                 *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 30th January 1992                                         *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 16th February 1993                                        *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 16th February 1993                                        *)
(*****************************************************************************)

structure Instance :> Instance =
struct

open HolKernel boolLib;

(* ----------------------------------------------------------------------
    INSTANCE_T_CONV : (term -> term list) -> conv -> conv

    Generalizes a conversion that is used to prove formulae true by
    replacing any syntactically unacceptable subterms with variables,
    attempting to prove this generalised formula, and if successful
    re-instantiating. The first argument is a function for obtaining a
    list of syntactically unacceptable subterms of a term. This
    function should include in its result list any variables in the
    term that do not appear in other subterms returned. The second
    argument is the conversion to be generalised.

    If the detector reckons a boolean sub-term can't be handled, then
    the conversion is actually handed the result of doing a case-split
    on the sub-term being T or F.

   ---------------------------------------------------------------------- *)

val boolrwt =
    Rewrite.PURE_REWRITE_CONV [AND_CLAUSES, IMP_CLAUSES,
                               OR_CLAUSES, NOT_CLAUSES, FORALL_SIMP]

fun BOOL_FORALL_ELIM t = let
  fun forall_and t = TRY_CONV (FORALL_AND_CONV THENC BINOP_CONV forall_and) t
  fun elimbvars t = let
    val (v,body) = dest_forall t
    val k =
        if type_of v = bool then
          EVERY_CONJ_CONV (HO_REWR_CONV FORALL_BOOL) THENC boolrwt
        else
          ALL_CONV
  in
    (TRY_CONV (RAND_CONV (ABS_CONV elimbvars)) THENC forall_and THENC
     k) t
  end
  val (vs, _) = strip_forall t
  val bvs = filter (fn v => type_of v = bool) vs
  val c = length bvs
in
  if 4 < c then
    raise mk_HOL_ERR "Instance" "BOOL_FORALL_ELIM"
          "Too many (>4) non-presburger boolean sub-terms"
  else if 0 < c then
    elimbvars
  else ALL_CONV
end t


fun INSTANCE_T_CONV detector conv tm =
 let val (univs,tm') = strip_forall tm
     val insts = Lib.op_mk_set aconv (detector tm')
     val vars = map (genvar o type_of) insts
     val s = map2 (curry op |->) insts vars
     val tm'' = list_mk_forall (vars, subst s tm')
 in
    EQT_INTRO
      (GENL univs
            (SPECL insts
                   (EQT_ELIM
                      ((BOOL_FORALL_ELIM THENC
                        EVERY_CONJ_CONV conv) tm''))))
 end;

end
