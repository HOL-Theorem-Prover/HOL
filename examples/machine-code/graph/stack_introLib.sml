structure stack_introLib :> stack_introLib =
struct

open HolKernel boolLib bossLib Parse;
open helperLib backgroundLib file_readerLib writerLib;

open GraphLangTheory

fun STACK_MEMORY_INTRO_RULE th = let
  val (_,p,_,_) = th |> concl |> dest_spec
  val ps = list_dest dest_star p
  val pat = case !arch_name of ARM   => ``arm_MEMORY d m``
                             | ARM8  => ``arm8_MEMORY d m``
                             | M0    => ``m0_MEMORY d m``
                             | RISCV => ``riscv_MEMORY d m``
  val x = first (can (match_term pat)) ps
  val d = x |> rator |> rand
  val m = x |> rand
  val th = th |> RW1 [GSYM arm_STACK_MEMORY_def,
                      GSYM arm8_STACK_MEMORY_def,
                      GSYM m0_STACK_MEMORY_def,
                      GSYM riscv_STACK_MEMORY_def]
  val th = th |> INST [m |-> mk_var("stack" ,type_of m),
                       d |-> mk_var("dom_stack" ,type_of d)]
  in th end handle HOL_ERR _ => th;

(*
  val () = arm_progLib.arm_config "vfpv3" "array"
  val (f,_,_,_) = arm_decompLib.l3_arm_tools
  val ((th,_,_),_) = f "e59d900c"  (* ldr r9, [sp, #12] *)
  val ((th,_,_),_) = f "e58d2010"  (* str r2, [sp, #16] *)
  val ((th,_,_),_) = f "e92d0030"  (* push {r4, r5} *)
  val ((th,_,_),_) = f "e92d0010"  (* push {r4} *)
  val ((th,_,_),_) = f "e24dd014"  (* sub sp, sp, #20 *)
  val ((th,_,_),_) = f "e1370006"  (* teq r7, r6 *)
*)

val STACK_INTRO_RULE_input = ref ([]:int list,TRUTH);

(*
  val (stack_accesses,th) = !STACK_INTRO_RULE_input
*)

local
  fun get_pc_pat () = let
    val (_,_,_,pc) = get_tools ()
    in ``^pc w`` end
  fun dest_sp q = let
    val sp_pat = case !arch_name of
                    ARM   => ``arm_REG (R_mode mode 13w) r13``
                  | ARM8  => ``arm8_SP_EL0 sp``
                  | M0    => ``m0_REG RName_SP_main r13``
                  | RISCV => ``riscv_REG 2w r2``
    val sp = sp_pat |> rand
    val tm = find_term (can (match_term sp_pat)) q |> rand
    in let val (x,y) = wordsSyntax.dest_word_add tm
           val _ = aconv x sp orelse fail()
       in y |> wordsSyntax.dest_n2w |> fst |> numSyntax.int_of_term end
       handle HOL_ERR _ =>
       let val (x,y) = wordsSyntax.dest_word_sub tm
           val _ = aconv x sp orelse fail()
       in 0-(y |> wordsSyntax.dest_n2w |> fst |> numSyntax.int_of_term) end
       handle HOL_ERR _ =>
       if aconv tm sp then 0 else failwith "unexpected value assigned to sp" end
  fun get_pc_num th = let
    val pc_pat = get_pc_pat ()
    val (_,p,_,_) = dest_spec (concl th)
    in find_term (can (match_term pc_pat)) p
       |> rand |> wordsSyntax.dest_n2w |> fst |> numSyntax.int_of_term end
in
  fun STACK_INTRO_RULE stack_accesses th = let
    val (_,p,_,q) = dest_spec (concl th)
    val (n,must_intro) = (dest_sp q,true)
      handle HOL_ERR _ => (0,mem (get_pc_num th) stack_accesses)
    in if n <> 0 orelse must_intro then STACK_MEMORY_INTRO_RULE th else th end
  handle HOL_ERR e =>
    (STACK_INTRO_RULE_input := (stack_accesses,th);
     report_error "STACK_INTRO_RULE" (HOL_ERR e))
end

end
