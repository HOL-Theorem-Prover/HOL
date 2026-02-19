(* MergeTrace: merge per-theory proof traces into a single self-contained trace.

   Given per-theory .pftrace files and a set of desired theorem exports,
   produces a merged trace that can be replayed from scratch in a bare
   kernel session.

   ORACLE DISK_THM entries are resolved by (theory, name) against ancestor
   exports and replaced with direct step references.
*)

structure MergeTrace :> MergeTrace =
struct

open HolKernel

val ERR = mk_HOL_ERR "MergeTrace"
fun its i = Int.toString i
fun int_of s = valOf (Int.fromString s)
val escape = TraceExport.escape_string
val tokenize = ReplayTrace.tokenize
val unescape = ReplayTrace.unescape

(* -----------------------------------------------------------------------
   Infer theory dependencies from ORACLE DISK_THM entries
   ----------------------------------------------------------------------- *)

fun disk_thm_deps step_lines =
  let
    val deps = ref (Redblackset.empty String.compare)
    fun check_line l =
      case tokenize l of
        (_ :: _ :: "ORACLE" :: "DISK_THM" :: thy :: _) =>
          deps := Redblackset.add(!deps, unescape thy)
      | _ => ()
  in
    List.app check_line step_lines;
    Redblackset.listItems (!deps)
  end

(* -----------------------------------------------------------------------
   Topological sort
   ----------------------------------------------------------------------- *)

fun toposort trace_map root_theories =
  let
    val visited = ref (Redblackset.empty String.compare)
    val order = ref ([] : string list)
    fun get_deps thy =
      case Redblackmap.peek(trace_map, thy) of
        NONE => []
      | SOME path =>
        let val {step_lines, ...} = ReplayTrace.read_trace_file path
        in disk_thm_deps step_lines end
        handle _ => []
    fun visit thy =
      if Redblackset.member(!visited, thy) then ()
      else
        (visited := Redblackset.add(!visited, thy);
         List.app visit (get_deps thy);
         if isSome (Redblackmap.peek(trace_map, thy))
         then order := thy :: !order
         else ())
  in
    List.app visit root_theories;
    rev (!order)
  end

(* -----------------------------------------------------------------------
   Per-rule operand remapping
   ----------------------------------------------------------------------- *)

fun remap_step_operands (rtm : string -> string)
                        (rty : string -> string)
                        (rule : string) (ops : string list) =
  case rule of
    (* No operands *)
      "MP" => []  | "SYM" => []  | "TRANS" => []
    | "MK_COMB" => [] | "EQ_MP" => [] | "EQ_IMP_RULE1" => []
    | "EQ_IMP_RULE2" => [] | "CONJ" => [] | "CONJUNCT1" => []
    | "CONJUNCT2" => [] | "DISJ_CASES" => []
    | "NOT_INTRO" => [] | "NOT_ELIM" => [] | "Beta" => []
    | "Mk_comb" => [] | "Mk_abs" => []
    (* Single term_id *)
    | "REFL" => [rtm (hd ops)]
    | "ASSUME" => [rtm (hd ops)]
    | "BETA_CONV" => [rtm (hd ops)]
    | "ABS" => [rtm (hd ops)]
    | "AP_TERM" => [rtm (hd ops)]
    | "AP_THM" => [rtm (hd ops)]
    | "DISCH" => [rtm (hd ops)]
    | "SPEC" => [rtm (hd ops)]
    | "Specialize" => [rtm (hd ops)]
    | "GEN" => [rtm (hd ops)]
    | "CHOOSE" => [rtm (hd ops)]
    | "DISJ1" => [rtm (hd ops)]
    | "DISJ2" => [rtm (hd ops)]
    | "CCONTR" => [rtm (hd ops)]
    | "AXIOM" => [rtm (hd ops)]
    | "COMPUTE" => [rtm (hd ops)]
    (* Two term_ids *)
    | "ALPHA" => [rtm (List.nth(ops,0)), rtm (List.nth(ops,1))]
    | "EXISTS" => [rtm (List.nth(ops,0)), rtm (List.nth(ops,1))]
    (* INST: n (var_id term_id){n} *)
    | "INST" =>
        let val n = int_of (hd ops)
        in its n :: List.concat (List.tabulate(n, fn i =>
             [rtm (List.nth(ops, 1+2*i)), rtm (List.nth(ops, 2+2*i))]))
        end
    (* INST_TYPE: n (tyvar_id type_id){n} *)
    | "INST_TYPE" =>
        let val n = int_of (hd ops)
        in its n :: List.concat (List.tabulate(n, fn i =>
             [rty (List.nth(ops, 1+2*i)), rty (List.nth(ops, 2+2*i))]))
        end
    (* SUBST: n var_id{n} template_id *)
    | "SUBST" =>
        let val n = int_of (hd ops)
        in its n ::
           List.tabulate(n, fn i => rtm (List.nth(ops, 1+i))) @
           [rtm (List.nth(ops, 1+n))]
        end
    (* GENL: n var_id* *)
    | "GENL" =>
        let val n = int_of (hd ops)
        in its n :: List.tabulate(n, fn i => rtm (List.nth(ops, 1+i)))
        end
    (* GEN_ABS: opt_cst_id n var_id* *)
    | "GEN_ABS" =>
        let val opt_s = hd ops
            val opt = if opt_s = "~" then "~" else rtm opt_s
            val n = int_of (List.nth(ops, 1))
        in opt :: its n ::
           List.tabulate(n, fn i => rtm (List.nth(ops, 2+i)))
        end
    (* DEF_TYOP: thy tyop concl_id *)
    | "DEF_TYOP" =>
        [List.nth(ops,0), List.nth(ops,1), rtm (List.nth(ops,2))]
    (* DEF_SPEC: thyname n cname* concl_id *)
    | "DEF_SPEC" =>
        let val n = int_of (List.nth(ops, 1))
        in List.take(ops, 2 + n) @ [rtm (List.last ops)]
        end
    (* ORACLE: tag + rule-specific *)
    | "ORACLE" =>
        let val tag = hd ops
        in if tag = "DISK_THM" then ops  (* unresolved, pass through *)
           else
             let val nhyps = int_of (List.nth(ops,2))
             in tag :: rtm (List.nth(ops,1)) :: List.nth(ops,2) ::
                List.tabulate(nhyps, fn i => rtm (List.nth(ops, 3+i)))
             end
        end
    (* COMPUTE_INIT: n_cval (name term_id){n_cval}
       cval_type_id num_type_id n_char (name){n_char} *)
    | "COMPUTE_INIT" =>
        let val n_cval = int_of (hd ops)
            val bi = 1 + 2 * n_cval
        in its n_cval ::
           List.concat (List.tabulate(n_cval, fn i =>
             [List.nth(ops, 1+2*i), rtm (List.nth(ops, 2+2*i))])) @
           [rty (List.nth(ops, bi)), rty (List.nth(ops, bi+1))] @
           List.drop(ops, bi+2)
        end
    | _ => ops  (* unknown rule, pass through *)

(* -----------------------------------------------------------------------
   Main merge function
   ----------------------------------------------------------------------- *)

fun merge {trace_dir, root_theories, desired_exports, output_path} =
  let
    val all_traces = ReplayTrace.find_traces trace_dir
    val trace_map =
      List.foldl (fn ((thy, path), m) =>
        Redblackmap.insert(m, thy, path))
        (Redblackmap.mkDict String.compare) all_traces

    val replay_order = toposort trace_map root_theories
    val _ = print ("Merge: " ^ its (length replay_order) ^
                   " theories in dependency order\n")

    (* Global ID counters *)
    val global_type_id = ref 0
    val global_term_id = ref 0
    val global_step_id = ref 0

    (* Accumulators *)
    val all_type_lines = ref ([] : string list)
    val all_term_lines = ref ([] : string list)
    val all_step_lines = ref ([] : string list)

    (* Ancestor export map: (thy, name) -> global step ID *)
    fun thyname_cmp ((t1,n1) : string*string, (t2,n2)) =
      case String.compare(t1,t2) of EQUAL => String.compare(n1,n2)
                                  | ord => ord
    val export_map = ref (Redblackmap.mkDict thyname_cmp
                          : (string*string, int) Redblackmap.dict)

    fun process_theory thy =
      let
        val path = valOf (Redblackmap.peek(trace_map, thy))
        val _ = print ("  " ^ thy ^ " ... ")
        val {header, type_lines, term_lines, step_lines, export_lines} =
          ReplayTrace.read_trace_file path
        val ReplayTrace.Header {n_types, n_terms, n_steps, ...} = header

        val ty_base = !global_type_id
        val tm_base = !global_term_id

        fun rtm s = its (int_of s + tm_base)
        fun rty s = its (int_of s + ty_base)

        (* Remap type lines *)
        val remapped_type_lines =
          List.map (fn line =>
            case tokenize line of
              (_ :: id_s :: "V" :: rest) =>
                "Y " ^ its (int_of id_s + ty_base) ^
                " V " ^ String.concatWith " " rest
            | (_ :: id_s :: "O" :: thy_s :: name_s :: arg_ids) =>
                "Y " ^ its (int_of id_s + ty_base) ^
                " O " ^ thy_s ^ " " ^ name_s ^
                (if null arg_ids then ""
                 else " " ^ String.concatWith " "
                   (map (fn s => its (int_of s + ty_base)) arg_ids))
            | _ => line) type_lines

        (* Remap term lines *)
        val remapped_term_lines =
          List.map (fn line =>
            case tokenize line of
              (_ :: id_s :: "V" :: name_s :: ty_s :: _) =>
                "M " ^ its (int_of id_s + tm_base) ^
                " V " ^ name_s ^ " " ^ rty ty_s
            | (_ :: id_s :: "C" :: thy_s :: name_s :: ty_s :: _) =>
                "M " ^ its (int_of id_s + tm_base) ^
                " C " ^ thy_s ^ " " ^ name_s ^ " " ^ rty ty_s
            | (_ :: id_s :: "A" :: f_s :: x_s :: _) =>
                "M " ^ its (int_of id_s + tm_base) ^
                " A " ^ rtm f_s ^ " " ^ rtm x_s
            | (_ :: id_s :: "L" :: v_s :: b_s :: _) =>
                "M " ^ its (int_of id_s + tm_base) ^
                " L " ^ rtm v_s ^ " " ^ rtm b_s
            | _ => line) term_lines

        (* Assign global step IDs *)
        val step_remap = Array.array(n_steps, ~1)
        val n_local_steps = ref 0
        val _ = List.app (fn line =>
          let
            val toks = tokenize line
            val local_id = int_of (List.nth(toks, 1))
          in
            case toks of
              (_ :: _ :: "ORACLE" :: "DISK_THM" :: t :: n :: _) =>
                let val key = (unescape t, unescape n)
                in case Redblackmap.peek(!export_map, key) of
                     SOME gid => Array.update(step_remap, local_id, gid)
                   | NONE =>
                     let val gid = !global_step_id
                     in global_step_id := gid + 1;
                        n_local_steps := !n_local_steps + 1;
                        Array.update(step_remap, local_id, gid)
                     end
                end
            | _ =>
                let val gid = !global_step_id
                in global_step_id := gid + 1;
                   n_local_steps := !n_local_steps + 1;
                   Array.update(step_remap, local_id, gid)
                end
          end) step_lines

        fun remap_sid i = Array.sub(step_remap, i)
        fun rsid s = its (remap_sid (int_of s))

        (* Remap and collect steps *)
        val remapped_step_lines =
          List.mapPartial (fn line =>
            let
              val toks = tokenize line
              val local_id = int_of (List.nth(toks, 1))
              val resolved = case toks of
                (_ :: _ :: "ORACLE" :: "DISK_THM" :: t :: n :: _) =>
                  isSome (Redblackmap.peek(!export_map,
                    (unescape t, unescape n)))
              | _ => false
            in
              if resolved then NONE
              else
                let
                  val (_ :: _ :: rule :: rest) = toks
                  val gid = remap_sid local_id
                  (* Split operands from parents at | *)
                  fun split acc [] = (rev acc, [])
                    | split acc ("|" :: r) = (rev acc, r)
                    | split acc (t :: r) = split (t :: acc) r
                  val (ops, pars) = split [] rest
                  val remapped_ops =
                    remap_step_operands rtm rty rule ops
                  val remapped_pars = map rsid pars
                  val ops_str = String.concatWith " " remapped_ops
                  val par_str = String.concatWith " " remapped_pars
                in
                  SOME ("P " ^ its gid ^ " " ^ rule ^
                        (if ops_str = "" then "" else " " ^ ops_str) ^
                        (if par_str = "" then "" else " | " ^ par_str))
                end
            end) step_lines

        (* Register exports *)
        val exports = ReplayTrace.parse_exports export_lines
        val _ = List.app (fn (name, local_step_id) =>
          export_map := Redblackmap.insert(!export_map, (thy, name),
                          remap_sid local_step_id)) exports

        val _ = global_type_id := !global_type_id + n_types
        val _ = global_term_id := !global_term_id + n_terms
      in
        all_type_lines := !all_type_lines @ remapped_type_lines;
        all_term_lines := !all_term_lines @ remapped_term_lines;
        all_step_lines := !all_step_lines @ remapped_step_lines;
        print ("done (" ^ its (!n_local_steps) ^ " steps)\n")
      end

    val _ = List.app process_theory replay_order

    (* Collect desired exports *)
    val export_lines =
      List.mapPartial (fn (thy, name) =>
        case Redblackmap.peek(!export_map, (thy, name)) of
          SOME gid => SOME ("E " ^ escape name ^ " " ^ its gid)
        | NONE =>
          (print ("WARNING: export " ^ thy ^ "." ^ name ^
                  " not found\n"); NONE)) desired_exports

    val n_types = !global_type_id
    val n_terms = !global_term_id
    val n_steps = !global_step_id
    val _ = print ("Writing: " ^ its n_types ^ " types, " ^
                   its n_terms ^ " terms, " ^ its n_steps ^ " steps, " ^
                   its (length export_lines) ^ " exports\n")

    (* Write output *)
    val ostrm = TextIO.openOut output_path
  in
    TextIO.output(ostrm, "HOL4_PROOF_TRACE 1\n");
    TextIO.output(ostrm, "THEORY merged\n");
    TextIO.output(ostrm, "COUNTS " ^ its n_types ^ " " ^
      its n_terms ^ " " ^ its n_steps ^ "\n\n");
    List.app (fn l => TextIO.output(ostrm, l ^ "\n")) (!all_type_lines);
    TextIO.output(ostrm, "\n");
    List.app (fn l => TextIO.output(ostrm, l ^ "\n")) (!all_term_lines);
    TextIO.output(ostrm, "\n");
    List.app (fn l => TextIO.output(ostrm, l ^ "\n")) (!all_step_lines);
    TextIO.output(ostrm, "\n");
    List.app (fn l => TextIO.output(ostrm, l ^ "\n")) export_lines;
    TextIO.closeOut ostrm;
    print ("Merged trace written to " ^ output_path ^ "\n")
  end

end (* structure *)
