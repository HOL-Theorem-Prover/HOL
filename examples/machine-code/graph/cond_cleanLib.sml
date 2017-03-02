structure cond_cleanLib =
struct

open HolKernel boolLib bossLib Parse;
open listTheory wordsTheory pred_setTheory arithmeticTheory wordsLib pairTheory;
open set_sepTheory progTheory helperLib addressTheory combinTheory;

open backgroundLib syntaxLib file_readerLib derive_specsLib graph_specsLib;
open GraphLangTheory writerLib;

fun find_inst_for loc insts = let
  val pat = ``IMPL_INST code locs (Inst ^loc assert next)``
  in first (can (match_term pat) o concl) insts end

fun dest_IMPL_INST_IF_ASM_ASM th = let
  val (_,_,i) = dest_IMPL_INST (concl th)
  val (_,_,next) = dest_Inst i
  val (guard,next1,next2) = dest_IF next
  in (guard,dest_ASM next1, dest_ASM next2) end

fun negate tm = if is_neg tm then dest_neg tm else mk_neg tm;
fun negate_guard tm = combinSyntax.mk_o(``$~:bool->bool``,tm)

fun reduce_inst_under_assum assum th =
  if can (dest_IMPL_INST_IF_ASM_ASM) th then let
    val (guard,asm1,asm2) = dest_IMPL_INST_IF_ASM_ASM th
    in let
         val th1 = MATCH_MP IMPL_INST_IF_SIMP2 th |> SPEC assum
         val h = th1 |> concl |> dest_imp |> fst
         val lemma = MATCH_MP EQ_T (QCONV (SIMP_CONV std_ss []) h)
       in MP th1 lemma end
       handle HOL_ERR _ =>
       let
         val th1 = MATCH_MP IMPL_INST_IF_SIMP1 th |> SPEC assum
         val h = th1 |> concl |> dest_imp |> fst
         val lemma = MATCH_MP EQ_T (QCONV (SIMP_CONV std_ss []) h)
       in MP th1 lemma end
    end
  else MATCH_MP IMPL_INST_SET_ASSUM th |> SPEC assum

val pc_string = ``"pc"``

fun inst_only_updates_pc th = let
  val (_,_,i) = dest_IMPL_INST (concl th)
  val (_,_,next) = dest_Inst i
  val (_,update,_) = dest_ASM next
  in listSyntax.is_nil update end
  handle HOL_ERR _ => false;

val optimisations_count = ref 0;

fun report_optimisation branch loc old_dest new_dest = let
  val _ = write_line (branch ^ "-branch at `" ^
                      int_to_hex loc ^ "` can target `" ^
                      int_to_hex new_dest ^ "` instead of `" ^
                      int_to_hex old_dest ^ "`.")
  in optimisations_count := 1 + (!optimisations_count) end

val solve_conv =
  QCONV (EVAL THENC
         SIMP_CONV std_ss [apply_update_def,var_bool_def,var_acc_def] THENC
         EVAL THENC SIMP_CONV std_ss [apply_update_def])

fun append_nop_to_if th thms = let
  val th = th |> RW [I_LEMMA]
  val (guard,_,(s2,u2,j2)) = dest_IMPL_INST_IF_ASM_ASM th
  val th = let (* simplify else-branch *)
    val w = dest_Jump j2
    val th1 = find_inst_for w thms |> RW [I_LEMMA]
    val assum = negate_guard guard
    val th1 = reduce_inst_under_assum assum th1
    val res = MATCH_MP IMPL_INST_IF_COMPOSE2 (CONJ th th1)
    val h = res |> concl |> dest_imp |> fst
    val lemma = solve_conv h |> MATCH_MP EQ_T
    val th = MP res lemma
    val _ = let
              val (guard,_,(s2,u2,j2)) = dest_IMPL_INST_IF_ASM_ASM th
              val new_dest = dest_Jump j2 |> rand |> numSyntax.int_of_term
              val old_dest = w |> rand |> numSyntax.int_of_term
              val loc = th |> concl |> rand |> dest_Inst |> #1 |> rand
                           |> numSyntax.int_of_term
              val _ = report_optimisation "Else" loc old_dest new_dest
            in () end handle HOL_ERR _ => ()
    in th end handle HOL_ERR _ => th
  val (guard,(s1,u1,j1),_) = dest_IMPL_INST_IF_ASM_ASM th
  val th = let (* simplify then-branch *)
    val w = dest_Jump j1
    val th1 = find_inst_for w thms |> RW [I_LEMMA]
    val assum = guard
    val th1 = reduce_inst_under_assum assum th1
    val res = MATCH_MP IMPL_INST_IF_COMPOSE1 (CONJ th th1)
    val h = res |> concl |> dest_imp |> fst
    val lemma = solve_conv h |> MATCH_MP EQ_T
    val th = MP res lemma
    val _ = let
              val (guard,(s1,u1,j1),_) = dest_IMPL_INST_IF_ASM_ASM th
              val new_dest = dest_Jump j1 |> rand |> numSyntax.int_of_term
              val old_dest = w |> rand |> numSyntax.int_of_term
              val loc = th |> concl |> rand |> dest_Inst |> #1 |> rand
                           |> numSyntax.int_of_term
              val _ = report_optimisation "Then" loc old_dest new_dest
            in () end handle HOL_ERR _ => ()
    in th end handle HOL_ERR _ => th
  val th = PURE_REWRITE_RULE [combinTheory.UPDATE_EQ] th
  in th end handle HOL_ERR _ => th

fun list_append_nop_to_if thms = let
  fun aux [] result = result
    | aux (th::rest) result = let
      val th = append_nop_to_if th result
      in aux rest (th::result) end
  in aux (rev thms) [] end

fun clean_conds thms = let
  val _ = write_subsection "Optimising inst theorems"
  val _ = (optimisations_count := 0)
  val thms = list_append_nop_to_if thms
  val _ = (if (!optimisations_count) <> 0 then () else
             write_line "Nothing was optimised.")
  in thms end

(*
val th = first (can (find_term (fn tm => tm = ``Inst 0xF0013DECw``)) o concl) thms
*)

end
