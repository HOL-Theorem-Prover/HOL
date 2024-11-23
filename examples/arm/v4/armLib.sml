structure armLib :> armLib =
struct

(* interactive use:
 app load ["fcpLib", "armTheory"];
*)

open HolKernel boolLib bossLib Parse;
open Q pairTheory armTheory;

(* ------------------------------------------------------------------------- *)

local
  val ICLASS_CONV = (REWRITE_CONV [iclass_EQ_iclass,iclass2num_thm]
                       THENC numLib.REDUCE_CONV);
  fun conv_rec t = {name = "ICLASS_CONV",trace = 3,conv = K (K ICLASS_CONV),
                    key = SOME([t],mk_eq(t,``x:iclass``))};
in
  val ICLASS_ss = simpLib.SSFRAG
    {name = SOME"ICLASS",
     convs = map conv_rec [``swp``,``mrs``,``msr``,``data_proc``,
             ``mla_mul``, ``ldr_str``,``ldrh_strh``, ``ldm_stm``,
             ``br``,``swi_ex``, ``cdp_und``, ``mcr``,``mrc``,``ldc_stc``,
             ``unexec``],
   rewrs = [], congs = [], filter = NONE, ac = [], dprocs = []};
end;

local open fcpTheory in
  val fcp_ss = std_ss ++ fcpLib.FCP_ss;
end;

val std_ss = std_ss ++ boolSimps.LET_ss;

local
  fun rstrip_comb l =
     if is_comb l then
       List.concat (map rstrip_comb (snd (boolSyntax.strip_comb l)))
     else
       [l];
in
  fun combCases M =
   let val vlist = rstrip_comb M
       val X = variant vlist (mk_var("x",type_of M))
       val tm = list_mk_exists(vlist, mk_eq(X,M))
   in
     GEN_ALL (METIS_PROVE (map (fn (a,(b,_,_)) => b) (find "nchotomy")) tm)
   end
end;

fun tupleCases M =
 let val vlist = pairSyntax.strip_pair M
     val X = variant vlist (mk_var("x",type_of M))
     val tm = list_mk_exists(vlist, mk_eq(X,M))
 in
   GEN_ALL (METIS_PROVE [pairTheory.ABS_PAIR_THM] tm)
 end;

val PBETA_ss = simpLib.SSFRAG
 {name = SOME "PBETA",
  convs = [{name="PBETA",trace = 3,conv=K (K PairRules.PBETA_CONV),
  key = SOME([],``(\(x:'a,y:'b). s1) s2:'c``)}], rewrs = [], congs = [],
  filter = NONE, ac = [], dprocs = []};

fun RES_MP1_TAC s t =
 let val a = (fst o dest_imp o concl o INST s o SPEC_ALL) t
 in
   Tactical.SUBGOAL_THEN a (fn th => STRIP_ASSUME_TAC (MATCH_MP t th))
 end;

fun RES_MP_TAC s t = RES_MP1_TAC s t THEN1 METIS_TAC [];

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
  PURE_REWRITE_RULE [METIS_PROVE [] ``Abbrev (x = x)``,
    AND_CLAUSES,OR_CLAUSES,IMP_CLAUSES] (Thm.INST [l |-> r] thm)
end;

end
