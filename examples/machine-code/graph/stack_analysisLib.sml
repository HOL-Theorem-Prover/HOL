structure stack_analysisLib :> stack_analysisLib =
struct

open HolKernel boolLib bossLib Parse;
open wordsTheory set_sepTheory progTheory helperLib addressTheory combinTheory;
open backgroundLib file_readerLib writerLib;
open GraphLangTheory

fun arch_max_return_words () = let
  val max = (case !arch_name of
                RISCV => 2
              | ARM   => 1
              | ARM8  => 2
              | M0    => 1)
  in max end

fun stack_offset_in_fst_arg sec_name = let
  val (_,ret_word_count,_) = section_io sec_name
  in arch_max_return_words () < ret_word_count end

local
  val bool_arb = mk_arb(``:bool``)
  val mem_type = ``:word32->word8``
  val write32_pat = ``WRITE32 a w m``
  fun dest_write32 tm =
    if can (match_term write32_pat) tm then
      let val (xyz,q) = dest_comb tm
          val (xy,z) = dest_comb xyz
          val (x,y) = dest_comb xy
      in (y,z,q) end
    else failwith "dest_write32"
  fun list_dest_write32 tm =
    let val (a,w,m) = dest_write32 tm
        val ls = list_dest_write32 m
    in (``READ32 ^a ^m``,w)::ls end handle HOL_ERR _ => []
in
  fun get_updates pre post = let
    val ps = list_dest dest_star pre
    val qs = list_dest dest_star post
    fun find_same q [] = failwith "not found"
      | find_same q (y::ys) =
          (if aconv (rator y) q then rand y else find_same q ys)
          handle HOL_ERR _ => find_same q ys
    fun dest_write (x,y) =
      if type_of x <> mem_type then [(x,y)] else list_dest_write32 y
    in map (fn tm => (rand tm,find_same (rator tm) qs)) ps
       |> filter (fn (x,y) => is_var x andalso not (aconv x y))
       |> map (fn (x,y) => if type_of x = ``:bool`` then (x,bool_arb) else (x,y))
       |> map dest_write |> Lib.flatten
    end
end

fun get_assum_pre_post th = let
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [word_arith_lemma1]
              |> SIMP_RULE std_ss [word_arith_lemma3,word_arith_lemma4]
              |> PURE_REWRITE_RULE [SPEC_MOVE_COND]
              |> UNDISCH_ALL
  val (_,pre,_,post) = dest_spec (concl th)
  in (hyp th, pre, post) end

fun get_pc_pat () = let
  val (_,_,_,pc) = get_tools ()
  in ``^pc w`` end

local
  fun get_pc_val tm = let
    val pc_pat = get_pc_pat ()
    in find_term (can (match_term pc_pat)) tm |> rand end
  val dmem32_type = ``:word32 set``
  val dmem64_type = ``:word64 set``
  fun dest_dmem_test tm = let
    val (x,y) = pred_setSyntax.dest_in tm
    val (v,ty) = dest_var y
    val _ = (ty = dmem32_type) orelse (ty = dmem64_type) orelse fail()
    in x end
  fun get_mem_access [] = NONE
    | get_mem_access (tm::tms) =
        SOME (dest_dmem_test (find_term (can dest_dmem_test) tm))
        handle HOL_ERR _ => get_mem_access tms
  fun summary (i:int,(th,l:int,j:int option),NONE) = let
      val (assum,pre,post) = get_assum_pre_post th
      val pc = get_pc_val pre
      fun all_posts post =
        if is_cond post then let
          val (_,p1,p2) = dest_cond post
          in all_posts p1 @ all_posts p2 end
        else [post]
      in map (fn post => (pc,T,get_updates pre post,
                          get_mem_access assum,get_pc_val post))
           (all_posts post) end
    | summary (i,(th1,l1,j1),SOME (th2,l:int,j:int option)) = let
      val (assum1,pre1,post1) = get_assum_pre_post th1
      val (assum2,pre2,post2) = get_assum_pre_post th2
      val assum2 = list_mk_conj assum2
      val u1 = get_updates pre1 post1
      val u2 = get_updates pre2 post2
      val assum1' = mk_neg assum2 |> QCONV (REWRITE_CONV []) |> concl |> rand
      val pc = get_pc_val pre1
      val res1 = (pc,assum1',u1,get_mem_access assum1,get_pc_val post1)
      val res2 = (pc,assum2,u2,NONE,get_pc_val post2)
      in [res1,res2] end handle HOL_ERR _ =>
        summary (i,(th1,l1,j1),NONE) @ summary (i,(th2,l,j),NONE)
  fun dest_call_tag tm = let
    val (xy,z) = dest_comb tm
    val (x,y) = dest_comb xy
    val _ = (aconv x ``CALL_TAG``) orelse fail()
    in (stringSyntax.fromHOLstring y,
        if aconv z T then true else
        if aconv z F then false else fail()) end
  fun has_call_tag th =
    can (find_term (can dest_call_tag)) (concl (DISCH_ALL th))
  fun call_update () = let
    fun mk_arb_pair tm = (tm,mk_arb(type_of tm))
    val wty = wsize()
    val regs = (case !arch_name of
                  RISCV => ["r3"]
                | ARM   => ["r0","r1","r2","r3","r14"]
                | ARM8  => ["r0","r1","r2","r3","r14"] (* check! *)
                | M0    => ["r0","r1","r2","r3","r14"])
    in map mk_arb_pair
         (map (fn s => mk_var(s,wty)) regs @
         [``n:bool``, ``z:bool``, ``c:bool``, ``v:bool``]) end
  val write8_pat = WRITE8_def |> SPEC_ALL |> concl |> dest_eq |> fst
  fun remove_write8 (name,tm) = let
    val xs = find_terms (can (match_term write8_pat)) tm
    in (name,subst (map (fn t => t |-> mk_arb(type_of t)) xs) tm) end
  fun tidy_up_summary (p1,assum1,u1,addr,q1) = let
    val u1 = map remove_write8 u1
    in (p1,assum1,u1,addr,q1) end
in
(*
val (i,(th1,i1,i2),thi2) = el 3 (rev thms)
val tm = u1 |> hd |> snd
*)
  fun approx_summary (i,(th1,i1,i2),thi2) =
    if not (has_call_tag th1)
    then map tidy_up_summary (summary (i,(th1,i1,i2),thi2))
    else let
      val res = map tidy_up_summary (summary (i,(th1,i1,i2),thi2))
      val (p1,assum1,u1,addr,q1) = hd res
      val linkreg = (case !arch_name of
                       RISCV => mk_var("r1", ``:word64``)
                     | M0    => mk_var("r14",``:word32``)
                     | ARM   => mk_var("r14",``:word32``)
                     | ARM8  => mk_var("r30",``:word64``))
      val dest = first (fn (x,_) => aconv x linkreg) u1 |> snd handle HOL_ERR _ => T
      in (p1,assum1,call_update(),addr,dest) :: tl res end
end

fun find_stack_accesses_for all_summaries sec_name = let
  val sp_var = (case !arch_name of
                  ARM   => ``r13:word32``
                | ARM8  => ``sp:word64``
                | M0    => ``r13:word32``
                | RISCV => ``r2:word64``)
  val (init_pc,_,_,_,_) = hd all_summaries
  val state = (init_pc,(sp_var,sp_var)::
              (if stack_offset_in_fst_arg sec_name then
                 (case !arch_name of
                    RISCV => [(``r10:word64``,``^sp_var + offset``)]
                  | _ => [(``r0:word32``,``^sp_var + offset``)])
               else []),T)
  val (pc,s,t) = state
  val us = filter (fn (p,_,_,_,_) => aconv p pc) all_summaries
  val (pc1,assum,u,addr,pc2) = hd us
  val stack_accesses = ref ([]:int list);
  fun add_stack_access pc = let
    val n = pc |> wordsSyntax.dest_n2w |> fst |> numSyntax.int_of_term
    val a = !stack_accesses
    in if mem n a then () else (stack_accesses := n::a) end
  fun can_exec_step t (pc1,assum,u,addr,pc2) =
    if aconv assum T then true else let
      val test = mk_imp(t,mk_neg assum)
      val vs = free_vars test
      val test = list_mk_forall(vs,test)
      fun can_prove_by_cases goal =
        ([],goal) |> (REPEAT Cases THEN REWRITE_TAC [])
                  |> (fn (x,_) => length x = 0)
      in not (can_prove_by_cases test) end
  fun is_sp_add_or_sub a =
    if aconv a sp_var then true else let
      val (w1,w2) = wordsSyntax.dest_word_add a
      in (aconv w1 sp_var andalso wordsSyntax.is_n2w w2) orelse
         (aconv w2 sp_var andalso wordsSyntax.is_n2w w1) end
    handle HOL_ERR _ => let
      val (w1,w2) = wordsSyntax.dest_word_sub a
      in (aconv w1 sp_var andalso wordsSyntax.is_n2w w2) orelse
         (aconv w2 sp_var andalso wordsSyntax.is_n2w w1) end
    handle HOL_ERR _ => false
  val stack_read32_pat = ``READ32 (a:word32) m``
  val stack_read64_pat = ``READ64 (a:word64) m``
  fun is_simple_or_stack_read32 (x,y) =
    if is_var x then true else
    if can (match_term stack_read32_pat) x then
      (x |> rator |> rand |> is_sp_add_or_sub)
    else false
  fun is_simple_or_stack_read64 (x,y) =
    if is_var x then true else
    if can (match_term stack_read64_pat) x then
      (x |> rator |> rand |> is_sp_add_or_sub)
    else false
  val is_simple_or_stack_read = (if !arch_name = RISCV
                                 then is_simple_or_stack_read64
                                 else is_simple_or_stack_read32)
  val word_simp_tm = rand o concl o QCONV (SIMP_CONV std_ss [word_arith_lemma1] THENC
        SIMP_CONV std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0])
  fun exec_step s t (pc1,assum,u,addr,pc2) = let
    val s_simple = filter (fn (x,_) => is_var x) s
    val s_read_word = filter (fn (x,_) => not (is_var x)) s
    val i_simple = word_simp_tm o subst (map (fn (x,y) => x |-> y) s_simple)
    val i = word_simp_tm o subst (map (fn (x,y) => x |-> y) s_read_word) o i_simple
    fun i_read_word_only tm = if is_comb tm then i_simple tm else tm
    val new_u_part = map (fn (x,y) => (i_read_word_only x,i y)) u
    val u_domain = map fst new_u_part
    val new_u = new_u_part @ filter (fn (x,y) => not (term_mem x u_domain)) s
    val new_t = if aconv assum T then t else assum
    val new_t = if null (term_intersect u_domain (free_vars new_t)) then new_t else T
    in (pc2,filter is_simple_or_stack_read new_u,new_t) end
  fun register_state (pc,s,t) = let
    val _ = print ("\nRegister state:\n  pc = " ^ term_to_string pc ^ "\n")
    val _ = print ("  assumes " ^ term_to_string t ^ "\n")
    val s = filter (fn (x,y) => not (is_arb y)) s
    val _ = map (fn (x,y) => print ("  " ^ term_to_string x ^ " is " ^
                                           term_to_string y ^ "\n")) s
    in () end
  val read_word_pat = (if !arch_name = RISCV then ``READ64 a (m:word64->word8)``
                                             else ``READ32 a (m:word32->word8)``)
  fun remove_read_word tm = let
    val xs = find_terms (can (match_term read_word_pat)) tm
    val ss = map (fn x => x |-> (mk_arb(type_of x))) xs
    in subst ss tm end
  fun found_stack_access pc s = let
    val _ = add_stack_access pc
(*  val _ = print ("Stack found access at pc = " ^ term_to_string pc ^ "\n") *)
(*  val _ =  print "\n" *)
    in () end
  fun check_for_stack_accesses (pc,s,t) NONE = ()
    | check_for_stack_accesses (pc,s,t) (SOME a) = let
    val i = remove_read_word o word_simp_tm o subst (map (fn (x,y) => x |-> y) s)
    fun contains_sp tm = term_mem sp_var (free_vars tm)
    in if contains_sp (i a)
       then found_stack_access pc (filter (fn (x,y) => contains_sp y)
                                     (map (fn (x,y) => (x,i y)) s))
       else () end
  fun get_pc (pc,s,t) = pc
  fun term_term_mem (t1,t2) [] = false
    | term_term_mem (t1,t2) ((x,y)::xs) =
        (aconv t1 x andalso aconv t2 y) orelse term_term_mem (t1,t2) xs
  val seen_nodes = ref ([]:(term * term) list)
  fun has_visited (pc,s,t) = let
    val seen = !seen_nodes
    in if term_term_mem (t,pc) seen then true else
         (seen_nodes := ((t,pc)::seen); false) end
  fun print_state (pc,s,t) = let
    val _ = print ("Looking at pc = " ^ term_to_string pc ^ "\n")
    val _ = map (fn (x,y) => print ("  " ^ term_to_string x ^ " is " ^
                                             term_to_string y ^ "\n")) s
    val _ = print ("  assuming: " ^ term_to_string t ^ "\n\n")
    in () end
  fun exec_steps state =
    if has_visited state then () else let
   (* val _ = register_state state *)
      val (pc,s,t) = state
   (* val _ = print_state state *)
      val us = filter (fn (p,_,_,_,_) => aconv p pc) all_summaries
      val us = filter (can_exec_step t) us
      val addresses = map (fn (_,_,_,a,_) => a) us
      val _ = map (check_for_stack_accesses state) addresses
   (* val (pc1,assum,u,addr,pc2) = hd us *)
      val states = map (exec_step s t) us
   (*
      val state = hd states handle Empty => state
   *)
      val _ = map exec_steps states
      in () end
  val _ = exec_steps state
  val xs = !stack_accesses
  in xs end;

fun find_stack_accesses sec_name thms = let
  val _ = write_subsection "\nStack analysis"
  val all_summaries = map approx_summary thms |> flatten
  val all_simple_summaries = all_summaries
    |> map (fn (x,a,u,z,y) => (x,a,filter (is_var o fst) u,z,y))
  val all_stack_accesses = find_stack_accesses_for all_summaries sec_name
  val simple_stack_accesses = find_stack_accesses_for all_simple_summaries sec_name
  fun annotation loc =
    if mem loc simple_stack_accesses then "stack access" else
    if mem loc all_stack_accesses then "indirect stack access" else fail()
  val _ = if stack_offset_in_fst_arg sec_name then let
            val r = (case !arch_name of RISCV => "a0" | _ => "r0")
            in write_line ("Section `" ^ sec_name ^ "` expects pointer "^
                           "to stack in "^r^".") end
          else ()
  val l = all_stack_accesses |> all_distinct |> length |> int_to_string
  val _ = (if l = "0" then
             write_line ("No stack accesses found. Code for `" ^ sec_name ^ "`:")
           else
             write_line (l ^ " stack accesses found. " ^
                         "Annotated code for `" ^ sec_name ^ "`:"))
  val _ = show_annotated_code annotation sec_name
  in all_stack_accesses end

end
