(* ========================================================================= *)
(* FILE          : arm_rulesLib.sml                                          *)
(* DESCRIPTION   : Tools for symbolic evaluation of the ARM Instruction Set  *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2006                                                      *)
(* ========================================================================= *)

structure arm_rulesLib :> arm_rulesLib =
struct

(* interactive use:
  app load ["arm_rulesTheory"];
*)

open HolKernel boolLib Parse bossLib;
open Q wordsTheory arm_rulesTheory;

(* ------------------------------------------------------------------------- *)

val wrd_ss = std_ss ++ rewrites [dimindex_4,word_ls_n2w,n2w_11];

val REG_WRITE_WRITE_PC = (GEN_ALL o GSYM o SIMP_RULE std_ss [] o
  INST [`m1` |-> `usr`,`m2` |-> `m`] o DISCH `~(n = 15w)` o
  SPEC_ALL) lemmasTheory.REG_WRITE_WRITE_PC;

val REG_WRITE_WRITE_PC2 = (GEN_ALL o SIMP_RULE std_ss [] o
  INST [`n` |-> `15w`] o SPEC_ALL) lemmasTheory.REG_WRITE_WRITE_PC;

val REG_WRITEL_PC = GEN_ALL
 ((SIMP_CONV std_ss [REG_WRITEL_def,lemmasTheory.TO_WRITE_READ6] THENC
   REWRITE_CONV [REG_WRITE_WRITEL]) ``REG_WRITEL r m [(15w,d)]``);

val REG_WRITEL_WRITEL_PC = (GEN_ALL o ONCE_REWRITE_RULE [REG_WRITEL_PC] o
  INST [`l1` |-> `[(15w,d)]`] o SPEC_ALL) REG_WRITEL_WRITEL;

val SORT_REG_WRITEL_CONV =
  SIMP_CONV wrd_ss [INC_PC,REG_READ_WRITEL_PC2] THENC
  SIMP_CONV wrd_ss [REG_WRITEL_def,REG_WRITE_WRITE_THM,
    REG_WRITE_WRITE_PC,REG_WRITE_WRITE_PC2] THENC
  REWRITE_CONV [listTheory.APPEND,REG_WRITE_WRITEL,
    REG_WRITEL_WRITEL,REG_WRITEL_WRITEL_PC];

val REG_READ_WRITEL_CONV = SIMP_CONV std_ss
    [CONJUNCT1 REG_WRITEL_def,REG_READ_WRITEL,REG_READ_WRITEL_PC,
     REG_READ_WRITEL_PC2,dimindex_4,n2w_11];

val REG_WRITEL_CONV = SORT_REG_WRITEL_CONV THENC REG_READ_WRITEL_CONV;

(* ------------------------------------------------------------------------- *)

fun mk_abbrev v  = mk_comb(``Abbrev``,mk_eq(v,genvar (type_of v)));

val dest_abbrev = dest_eq o snd o dest_comb;

fun is_abbrev_match m t =
let val v = fst (dest_abbrev m)
    val rrl = match_term m t
in
  null (snd rrl) andalso
  not (isSome (List.find (fn x => term_eq (#redex x) v) (fst rrl)))
end;

fun total_is_abbrev_match m t =
  case total (is_abbrev_match m) t of
    SOME b => b
  | _ => false;
    
fun get_abbrev_match m t = find_term (total_is_abbrev_match m) t;

fun UNABBREV_RULE q thm =
let val t = concl thm
    val m = mk_abbrev (parse_in_context (free_vars t) q)
    val mt = get_abbrev_match m t
    val (l,r) = dest_abbrev mt
in
  SIMP_RULE bool_ss [SPEC `T` markerTheory.Abbrev_def] (Thm.INST [l |-> r] thm)
end;

fun UNABBREVL_RULE l t =
   GEN_ALL (foldl (fn (x,t) => UNABBREV_RULE x t) (SPEC_ALL t) l);

(* ------------------------------------------------------------------------- *)

end
