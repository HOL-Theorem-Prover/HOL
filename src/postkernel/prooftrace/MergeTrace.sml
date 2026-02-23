(* MergeTrace: merge per-theory traces into a single self-contained trace.

   Two-pass algorithm:
   Pass 1: determine live entries per theory via backward reachability
   Pass 2: write merged trace with global type/term dedup and ID remapping
*)

structure MergeTrace :> MergeTrace =
struct

open HolKernel

val ERR = mk_HOL_ERR "MergeTrace"
fun its i = Int.toString i
fun int_of s = valOf (Int.fromString s)
val esc = TraceRecord.escape_string
val tokenize = ReplayTrace.tokenize
val unescape = ReplayTrace.unescape

(* ------- Per-rule argument parsing ------- *)

(* Extract parent (theorem) IDs from a P entry's args, given the rule.
   Returns list of (position, thm_id) for parent args. *)
fun extract_parent_ids rule args =
  let
    fun ai n = int_of (List.nth(args, n))
    val nargs = length args
  in case rule of
    (* No parents *)
      "REFL" => [] | "ASSUME" => [] | "BETA_CONV" => []
    | "ALPHA" => [] | "AXIOM" => [] | "DISK_THM" => []
    (* Single parent at position 0 *)
    | "ABS" => [ai 0] | "AP_TERM" => [ai 0] | "AP_THM" => [ai 0]
    | "SYM" => [ai 0] | "DISCH" => [ai 0] | "SPEC" => [ai 0]
    | "Specialize" => [ai 0] | "GEN" => [ai 0]
    | "EQ_IMP_RULE1" => [ai 0] | "EQ_IMP_RULE2" => [ai 0]
    | "CONJUNCT1" => [ai 0] | "CONJUNCT2" => [ai 0]
    | "DISJ1" => [ai 0] | "DISJ2" => [ai 0]
    | "NOT_INTRO" => [ai 0] | "NOT_ELIM" => [ai 0]
    | "CCONTR" => [ai 0] | "Beta" => [ai 0]
    (* Two parents *)
    | "MK_COMB" => [ai 0, ai 1] | "TRANS" => [ai 0, ai 1]
    | "EQ_MP" => [ai 0, ai 1] | "MP" => [ai 0, ai 1]
    | "CONJ" => [ai 0, ai 1] | "Mk_abs" => [ai 0, ai 1]
    (* Three parents *)
    | "Mk_comb" => [ai 0, ai 1, ai 2]
    | "DISJ_CASES" => [ai 0, ai 1, ai 2]
    (* CHOOSE: p p t *)
    | "CHOOSE" => [ai 0, ai 1]
    (* EXISTS: p t t — parent at 0 *)
    | "EXISTS" => [ai 0]
    (* DEF_TYOP: p s s — parent at 0 *)
    | "DEF_TYOP" => [ai 0]
    (* DEF_SPEC: p s s* — parent at 0 *)
    | "DEF_SPEC" => [ai 0]
    (* GENL: p t* — parent at 0 *)
    | "GENL" => [ai 0]
    (* GEN_ABS: p t t* — parent at 0 *)
    | "GEN_ABS" => [ai 0]
    (* INST_TYPE: p (y y)* — parent at 0 *)
    | "INST_TYPE" => [ai 0]
    (* INST: p (t t)* — parent at 0 *)
    | "INST" => [ai 0]
    (* SUBST: p t (t p)* — parent at 0, then every other from pos 2 *)
    | "SUBST" =>
        ai 0 :: List.tabulate((nargs - 2) div 2, fn i => ai (3 + 2*i))
    (* COMPUTE: t p* — parents from pos 1 *)
    | "COMPUTE" =>
        List.tabulate(nargs - 1, fn i => ai (1 + i))
    (* ORACLE: s t t* — no parents *)
    | "ORACLE" => []
    | _ => []
  end

(* Extract term IDs referenced by a P entry *)
fun extract_term_ids rule args =
  let
    fun ai n = int_of (List.nth(args, n))
    val nargs = length args
  in case rule of
      "REFL" => [ai 0] | "ASSUME" => [ai 0] | "BETA_CONV" => [ai 0]
    | "ALPHA" => [ai 0, ai 1] | "AXIOM" => [ai 0]
    | "ABS" => [ai 1] | "AP_TERM" => [ai 1] | "AP_THM" => [ai 1]
    | "DISCH" => [ai 1] | "SPEC" => [ai 1] | "Specialize" => [ai 1]
    | "GEN" => [ai 1] | "CCONTR" => [ai 1]
    | "DISJ1" => [ai 1] | "DISJ2" => [ai 1]
    | "EXISTS" => [ai 1, ai 2]
    | "CHOOSE" => [ai 2]
    | "GENL" => List.tabulate(nargs - 1, fn i => ai (1 + i))
    | "GEN_ABS" =>
        (if List.nth(args, 1) = "~" then []
         else [ai 1]) @
        List.tabulate(nargs - 2, fn i => ai (2 + i))
    | "INST" =>
        List.tabulate(nargs - 1, fn i => ai (1 + i))
    | "SUBST" =>
        ai 1 :: List.tabulate((nargs - 2) div 2, fn i => ai (2 + 2*i))
    | "COMPUTE" => [ai 0]
    | "ORACLE" =>
        ai 1 :: List.tabulate(nargs - 2, fn i => ai (2 + i))
    | _ => []
  end

(* Extract type IDs referenced by a P entry *)
fun extract_type_ids rule args =
  let
    fun ai n = int_of (List.nth(args, n))
    val nargs = length args
  in case rule of
      "INST_TYPE" =>
        List.tabulate(nargs - 1, fn i => ai (1 + i))
    | _ => []
  end

(* ------- Pass 1: Reachability ------- *)

(* Per-theory trace data needed for reachability *)
type theory_data = {
  thy_name : string,
  path : string,
  (* Dependency lists per entry (P entries only need parent P ids;
     but we also need term/type deps for liveness) *)
  p_parents : int list Array.array,   (* P id -> parent P ids *)
  p_term_deps : int list Array.array,  (* P id -> term ids used *)
  p_type_deps : int list Array.array,  (* P id -> type ids used *)
  t_deps : int list Array.array,       (* T id -> sub T/Y ids *)
  y_deps : int list Array.array,       (* Y id -> sub Y ids *)
  t_type_deps : int list Array.array,  (* T id -> Y ids *)
  exports : (string * int) list,       (* name -> P id *)
  disk_thms : (int * string * string) list, (* P id, thy, name *)
  n_types : int,
  n_terms : int,
  n_thms : int,
  has_compute_init : bool
}

fun read_theory_data path : theory_data =
  let
    val (instrm, proc) = ReplayTrace.open_trace path
    val ty_count = ref 0
    val tm_count = ref 0
    val thm_count = ref 0
    val thy_name = ref ""
    val exports_rev = ref ([] : (string * int) list)
    val disk_thms_rev = ref ([] : (int * string * string) list)
    val has_ci = ref false

    (* Accumulate deps in lists, convert to arrays later *)
    val p_parents_rev = ref ([] : (int * int list) list)
    val p_term_deps_rev = ref ([] : (int * int list) list)
    val p_type_deps_rev = ref ([] : (int * int list) list)
    val t_deps_rev = ref ([] : (int * int list) list)
    val y_deps_rev = ref ([] : (int * int list) list)
    val t_type_deps_rev = ref ([] : (int * int list) list)

    fun process_line line =
      let val toks = tokenize line in
      case toks of
        [] => ()
      | ("Y" :: id_s :: "V" :: _) =>
          let val id = int_of id_s
          in ty_count := Int.max(!ty_count, id + 1);
             y_deps_rev := (id, []) :: !y_deps_rev
          end
      | ("Y" :: id_s :: "O" :: _ :: _ :: arg_ids) =>
          let val id = int_of id_s
              val deps = List.mapPartial Int.fromString arg_ids
          in ty_count := Int.max(!ty_count, id + 1);
             y_deps_rev := (id, deps) :: !y_deps_rev
          end
      | ("T" :: id_s :: "V" :: _ :: ty_s :: _) =>
          let val id = int_of id_s
          in tm_count := Int.max(!tm_count, id + 1);
             t_deps_rev := (id, []) :: !t_deps_rev;
             t_type_deps_rev := (id, [int_of ty_s]) :: !t_type_deps_rev
          end
      | ("T" :: id_s :: "C" :: _ :: _ :: ty_s :: _) =>
          let val id = int_of id_s
          in tm_count := Int.max(!tm_count, id + 1);
             t_deps_rev := (id, []) :: !t_deps_rev;
             t_type_deps_rev := (id, [int_of ty_s]) :: !t_type_deps_rev
          end
      | ("T" :: id_s :: "A" :: f_s :: x_s :: _) =>
          let val id = int_of id_s
          in tm_count := Int.max(!tm_count, id + 1);
             t_deps_rev := (id, [int_of f_s, int_of x_s]) :: !t_deps_rev;
             t_type_deps_rev := (id, []) :: !t_type_deps_rev
          end
      | ("T" :: id_s :: "L" :: v_s :: b_s :: _) =>
          let val id = int_of id_s
          in tm_count := Int.max(!tm_count, id + 1);
             t_deps_rev := (id, [int_of v_s, int_of b_s]) :: !t_deps_rev;
             t_type_deps_rev := (id, []) :: !t_type_deps_rev
          end
      | ("P" :: id_s :: rule :: args) =>
          let val id = int_of id_s
              val parents = extract_parent_ids rule args
              val term_deps = extract_term_ids rule args
              val type_deps = extract_type_ids rule args
          in thm_count := Int.max(!thm_count, id + 1);
             p_parents_rev := (id, parents) :: !p_parents_rev;
             p_term_deps_rev := (id, term_deps) :: !p_term_deps_rev;
             p_type_deps_rev := (id, type_deps) :: !p_type_deps_rev;
             (case rule of
                "DISK_THM" =>
                  disk_thms_rev := (id, unescape (List.nth(args, 0)),
                                    unescape (List.nth(args, 1)))
                                   :: !disk_thms_rev
              | _ => ())
          end
      | ("C" :: _) => has_ci := true
      | ("N" :: name :: _) => thy_name := unescape name
      | ("E" :: name :: id_s :: _) =>
          exports_rev := (unescape name, int_of id_s) :: !exports_rev
      | _ => ()
      end

    fun read_all () =
      case TextIO.inputLine instrm of
        NONE => ()
      | SOME line =>
          (process_line (String.substring(line, 0, size line - 1)
                         handle Subscript => line);
           read_all ())
    val _ = read_all ()
    val _ = ReplayTrace.close_trace (instrm, proc)

    val ny = !ty_count
    val nt = !tm_count
    val np = !thm_count

    fun to_array n items =
      let val arr = Array.array(n, [] : int list)
      in List.app (fn (id, deps) =>
           if id < n then Array.update(arr, id, deps) else ())
           items;
         arr
      end
  in
    { thy_name = !thy_name, path = path,
      p_parents = to_array np (!p_parents_rev),
      p_term_deps = to_array np (!p_term_deps_rev),
      p_type_deps = to_array np (!p_type_deps_rev),
      t_deps = to_array nt (!t_deps_rev),
      y_deps = to_array ny (!y_deps_rev),
      t_type_deps = to_array nt (!t_type_deps_rev),
      exports = rev (!exports_rev),
      disk_thms = rev (!disk_thms_rev),
      n_types = ny, n_terms = nt, n_thms = np,
      has_compute_init = !has_ci }
  end

fun mark_live (data : theory_data) (needed_thm_ids : int list) =
  let
    val live_p = Array.array(#n_thms data, false)
    val live_t = Array.array(#n_terms data, false)
    val live_y = Array.array(#n_types data, false)

    fun mark_thm id =
      if id < 0 orelse id >= #n_thms data orelse
         Array.sub(live_p, id) then ()
      else (Array.update(live_p, id, true);
            List.app mark_thm (Array.sub(#p_parents data, id));
            List.app mark_term (Array.sub(#p_term_deps data, id));
            List.app mark_type (Array.sub(#p_type_deps data, id)))
    and mark_term id =
      if id < 0 orelse id >= #n_terms data orelse
         Array.sub(live_t, id) then ()
      else (Array.update(live_t, id, true);
            List.app mark_term (Array.sub(#t_deps data, id));
            List.app mark_type (Array.sub(#t_type_deps data, id)))
    and mark_type id =
      if id < 0 orelse id >= #n_types data orelse
         Array.sub(live_y, id) then ()
      else (Array.update(live_y, id, true);
            List.app mark_type (Array.sub(#y_deps data, id)))
  in
    List.app mark_thm needed_thm_ids;
    (live_y, live_t, live_p)
  end

(* ------- Pass 2: Remap and write ------- *)

(* Dedup map key types *)
datatype ty_desc = TyV of string | TyO of string * string * int list
datatype tm_desc = TmV of string * int | TmC of string * string * int
                 | TmA of int * int | TmL of int * int

fun ty_desc_compare (TyV a, TyV b) = String.compare(a, b)
  | ty_desc_compare (TyV _, _) = LESS
  | ty_desc_compare (_, TyV _) = GREATER
  | ty_desc_compare (TyO(t1,n1,a1), TyO(t2,n2,a2)) =
      (case String.compare(t1,t2) of EQUAL =>
        (case String.compare(n1,n2) of EQUAL =>
          List.collate Int.compare (a1,a2)
        | ord => ord)
      | ord => ord)

fun tm_desc_compare (TmV(n1,t1), TmV(n2,t2)) =
      (case String.compare(n1,n2) of EQUAL => Int.compare(t1,t2)
       | ord => ord)
  | tm_desc_compare (TmV _, _) = LESS
  | tm_desc_compare (_, TmV _) = GREATER
  | tm_desc_compare (TmC(t1,n1,y1), TmC(t2,n2,y2)) =
      (case String.compare(t1,t2) of EQUAL =>
        (case String.compare(n1,n2) of EQUAL => Int.compare(y1,y2)
         | ord => ord)
      | ord => ord)
  | tm_desc_compare (TmC _, _) = LESS
  | tm_desc_compare (_, TmC _) = GREATER
  | tm_desc_compare (TmA(f1,x1), TmA(f2,x2)) =
      (case Int.compare(f1,f2) of EQUAL => Int.compare(x1,x2)
       | ord => ord)
  | tm_desc_compare (TmA _, _) = LESS
  | tm_desc_compare (_, TmA _) = GREATER
  | tm_desc_compare (TmL(v1,b1), TmL(v2,b2)) =
      (case Int.compare(v1,v2) of EQUAL => Int.compare(b1,b2)
       | ord => ord)

(* ------- Remap a P line's args ------- *)

fun remap_args (ry : int -> int) (rt : int -> int) (rp : int -> int)
               rule args =
  case rule of
    "REFL" => [its (rt (int_of (hd args)))]
  | "ASSUME" => [its (rt (int_of (hd args)))]
  | "BETA_CONV" => [its (rt (int_of (hd args)))]
  | "ALPHA" => map (its o rt o int_of) args
  | "ABS" => [its (rp (int_of (List.nth(args,0)))),
              its (rt (int_of (List.nth(args,1))))]
  | "MK_COMB" => map (its o rp o int_of) args
  | "AP_TERM" => [its (rp (int_of (List.nth(args,0)))),
                  its (rt (int_of (List.nth(args,1))))]
  | "AP_THM" => [its (rp (int_of (List.nth(args,0)))),
                 its (rt (int_of (List.nth(args,1))))]
  | "SYM" => [its (rp (int_of (hd args)))]
  | "TRANS" => map (its o rp o int_of) args
  | "EQ_MP" => map (its o rp o int_of) args
  | "EQ_IMP_RULE1" => [its (rp (int_of (hd args)))]
  | "EQ_IMP_RULE2" => [its (rp (int_of (hd args)))]
  | "MP" => map (its o rp o int_of) args
  | "DISCH" => [its (rp (int_of (List.nth(args,0)))),
                its (rt (int_of (List.nth(args,1))))]
  | "INST_TYPE" =>
      its (rp (int_of (hd args))) ::
      map (its o ry o int_of) (tl args)
  | "INST" =>
      its (rp (int_of (hd args))) ::
      map (its o rt o int_of) (tl args)
  | "SUBST" =>
      let val orig = its (rp (int_of (List.nth(args,0))))
          val tmpl = its (rt (int_of (List.nth(args,1))))
          val rest = List.drop(args, 2)
          fun pairs [] = []
            | pairs (v::r::t) =
                its (rt (int_of v)) :: its (rp (int_of r)) :: pairs t
            | pairs _ = []
      in orig :: tmpl :: pairs rest end
  | "SPEC" => [its (rp (int_of (List.nth(args,0)))),
               its (rt (int_of (List.nth(args,1))))]
  | "Specialize" => [its (rp (int_of (List.nth(args,0)))),
                     its (rt (int_of (List.nth(args,1))))]
  | "GEN" => [its (rp (int_of (List.nth(args,0)))),
              its (rt (int_of (List.nth(args,1))))]
  | "GENL" =>
      its (rp (int_of (hd args))) ::
      map (its o rt o int_of) (tl args)
  | "GEN_ABS" =>
      its (rp (int_of (List.nth(args,0)))) ::
      (if List.nth(args,1) = "~" then "~"
       else its (rt (int_of (List.nth(args,1))))) ::
      map (its o rt o int_of) (List.drop(args, 2))
  | "EXISTS" => [its (rp (int_of (List.nth(args,0)))),
                 its (rt (int_of (List.nth(args,1)))),
                 its (rt (int_of (List.nth(args,2))))]
  | "CHOOSE" => [its (rp (int_of (List.nth(args,0)))),
                 its (rp (int_of (List.nth(args,1)))),
                 its (rt (int_of (List.nth(args,2))))]
  | "CONJ" => map (its o rp o int_of) args
  | "CONJUNCT1" => [its (rp (int_of (hd args)))]
  | "CONJUNCT2" => [its (rp (int_of (hd args)))]
  | "DISJ1" => [its (rp (int_of (List.nth(args,0)))),
                its (rt (int_of (List.nth(args,1))))]
  | "DISJ2" => [its (rp (int_of (List.nth(args,0)))),
                its (rt (int_of (List.nth(args,1))))]
  | "DISJ_CASES" => map (its o rp o int_of) args
  | "NOT_INTRO" => [its (rp (int_of (hd args)))]
  | "NOT_ELIM" => [its (rp (int_of (hd args)))]
  | "CCONTR" => [its (rp (int_of (List.nth(args,0)))),
                 its (rt (int_of (List.nth(args,1))))]
  | "Beta" => [its (rp (int_of (hd args)))]
  | "Mk_comb" => map (its o rp o int_of) args
  | "Mk_abs" => map (its o rp o int_of) args
  | "DEF_TYOP" => [its (rp (int_of (List.nth(args,0)))),
                   List.nth(args,1), List.nth(args,2)]
  | "DEF_SPEC" =>
      its (rp (int_of (hd args))) :: tl args
  | "COMPUTE" =>
      its (rt (int_of (hd args))) ::
      map (its o rp o int_of) (tl args)
  | "AXIOM" => [its (rt (int_of (hd args)))]
  | "ORACLE" =>
      List.nth(args,0) ::
      its (rt (int_of (List.nth(args,1)))) ::
      map (its o rt o int_of) (List.drop(args, 2))
  | _ => args

(* ------- Main merge ------- *)

fun thyname_cmp ((t1,n1) : string*string, (t2,n2)) =
  case String.compare(t1,t2) of EQUAL => String.compare(n1,n2)
                               | ord => ord

fun merge {trace_paths : (string * string) list,
           desired_exports : (string * string) list,
           output_path : string} =
  let
    (* Build path map: theory name -> file path *)
    val path_map = List.foldl (fn ((thy, path), m) =>
      Redblackmap.insert(m, thy, path))
      (Redblackmap.mkDict String.compare) trace_paths

    (* --- Pass 1: reachability --- *)
    val _ = print "Pass 1: determining live entries...\n"

    (* needed_ancestor_exports: (thy, name) set *)
    val needed = ref (Redblackset.empty thyname_cmp)
    val _ = List.app (fn e => needed := Redblackset.add(!needed, e))
                     desired_exports

    (* Processed theories and their data *)
    val processed : (string, theory_data * (bool Array.array *
                     bool Array.array * bool Array.array)) Redblackmap.dict ref =
      ref (Redblackmap.mkDict String.compare)
    val topo_order = ref ([] : string list)

    fun process_theory thy =
      if isSome (Redblackmap.peek(!processed, thy)) then ()
      else
        case Redblackmap.peek(path_map, thy) of
          NONE => print ("WARNING: no trace for theory " ^ thy ^ "\n")
        | SOME path =>
          let
            val _ = print ("  " ^ thy ^ "...")
            val data = read_theory_data path

            (* Which thm IDs are needed from this theory? *)
            val needed_ids =
              List.mapPartial (fn (name, id) =>
                if Redblackset.member(!needed, (thy, name))
                then SOME id else NONE)
                (#exports data)

            val (live_y, live_t, live_p) = mark_live data needed_ids

            (* Discover ancestor dependencies *)
            val _ = List.app (fn (id, anc_thy, anc_name) =>
              if Array.sub(live_p, id) then
                needed := Redblackset.add(!needed, (anc_thy, anc_name))
              else ()) (#disk_thms data)

            val _ = processed :=
              Redblackmap.insert(!processed, thy,
                                (data, (live_y, live_t, live_p)))
            (* Process ancestors before adding self to topo order *)
            val ancestor_thys = Redblackset.foldl
              (fn ((t, _), s) => Redblackset.add(s, t))
              (Redblackset.empty String.compare)
              (!needed)
            val _ = Redblackset.app (fn t =>
              if t <> thy then process_theory t else ()) ancestor_thys

            val _ = topo_order := thy :: !topo_order
            val n_live = Array.foldl (fn (true,n) => n+1 | (_,n) => n)
                                     0 live_p
            val _ = print (" " ^ its n_live ^ " live thms\n")
          in () end

    (* Kick off from desired exports *)
    val desired_thys = Redblackset.listItems (
      List.foldl (fn ((t,_),s) => Redblackset.add(s,t))
        (Redblackset.empty String.compare) desired_exports)
    val _ = List.app process_theory desired_thys
    val topo = rev (!topo_order)
    val _ = print ("Pass 1 done: " ^ its (length topo) ^ " theories\n")

    (* --- Pass 2: write merged trace --- *)
    val _ = print "Pass 2: writing merged trace...\n"

    val global_ty_map = ref (Redblackmap.mkDict ty_desc_compare)
    val global_tm_map = ref (Redblackmap.mkDict tm_desc_compare)
    val global_ty_id = ref 0
    val global_tm_id = ref 0
    val global_thm_id = ref 0

    val ancestor_exports : (string * string, int) Redblackmap.dict ref =
      ref (Redblackmap.mkDict thyname_cmp)

    val ostrm = TextIO.openOut output_path
    val _ = TextIO.output(ostrm, "V 1\n")

    fun write_theory thy =
      case Redblackmap.peek(!processed, thy) of
        NONE => ()
      | SOME (data, (live_y, live_t, live_p)) =>
        let
          val (instrm, proc) = ReplayTrace.open_trace (#path data)

          (* Local -> global remap arrays *)
          val y_remap = Array.array(#n_types data, ~1)
          val t_remap = Array.array(#n_terms data, ~1)
          val p_remap = Array.array(#n_thms data, ~1)

          fun ry i = Array.sub(y_remap, i)
          fun rt i = Array.sub(t_remap, i)
          fun rp i = Array.sub(p_remap, i)

          fun process_line line =
            let val toks = tokenize line in
            case toks of
              [] => ()
            | ("Y" :: id_s :: rest) =>
                let val id = int_of id_s
                in if Array.sub(live_y, id) then
                  let val desc = case rest of
                        ["V", name] => TyV (unescape name)
                      | ("O" :: thy_s :: name_s :: arg_ids) =>
                          TyO (unescape thy_s, unescape name_s,
                               map (ry o int_of) arg_ids)
                      | _ => raise ERR "write_theory" "bad Y"
                  in case Redblackmap.peek(!global_ty_map, desc) of
                       SOME gid => Array.update(y_remap, id, gid)
                     | NONE =>
                       let val gid = !global_ty_id
                       in global_ty_id := gid + 1;
                          global_ty_map :=
                            Redblackmap.insert(!global_ty_map, desc, gid);
                          Array.update(y_remap, id, gid);
                          (* Write remapped Y line *)
                          TextIO.output(ostrm, case desc of
                            TyV name =>
                              "Y " ^ its gid ^ " V " ^ esc name ^ "\n"
                          | TyO (t,n,args) =>
                              "Y " ^ its gid ^ " O " ^ esc t ^ " " ^
                              esc n ^
                              (if null args then ""
                               else " " ^ String.concatWith " "
                                            (map its args)) ^ "\n")
                       end
                  end
                else ()
                end
            | ("T" :: id_s :: rest) =>
                let val id = int_of id_s
                in if Array.sub(live_t, id) then
                  let val desc = case rest of
                        ["V", name, ty_s] =>
                          TmV (unescape name, ry (int_of ty_s))
                      | ["C", thy_s, name_s, ty_s] =>
                          TmC (unescape thy_s, unescape name_s,
                               ry (int_of ty_s))
                      | ["A", f_s, x_s] =>
                          TmA (rt (int_of f_s), rt (int_of x_s))
                      | ["L", v_s, b_s] =>
                          TmL (rt (int_of v_s), rt (int_of b_s))
                      | _ => raise ERR "write_theory" "bad T"
                  in case Redblackmap.peek(!global_tm_map, desc) of
                       SOME gid => Array.update(t_remap, id, gid)
                     | NONE =>
                       let val gid = !global_tm_id
                       in global_tm_id := gid + 1;
                          global_tm_map :=
                            Redblackmap.insert(!global_tm_map, desc, gid);
                          Array.update(t_remap, id, gid);
                          TextIO.output(ostrm, case desc of
                            TmV (name, tyid) =>
                              "T " ^ its gid ^ " V " ^ esc name ^
                              " " ^ its tyid ^ "\n"
                          | TmC (t,n,tyid) =>
                              "T " ^ its gid ^ " C " ^ esc t ^ " " ^
                              esc n ^ " " ^ its tyid ^ "\n"
                          | TmA (f,x) =>
                              "T " ^ its gid ^ " A " ^ its f ^
                              " " ^ its x ^ "\n"
                          | TmL (v,b) =>
                              "T " ^ its gid ^ " L " ^ its v ^
                              " " ^ its b ^ "\n")
                       end
                  end
                else ()
                end
            | ("P" :: id_s :: "DISK_THM" :: _) =>
                let val id = int_of id_s
                in if Array.sub(live_p, id) then
                  (* Find in disk_thms list *)
                  case List.find (fn (i,_,_) => i = id) (#disk_thms data) of
                    SOME (_, anc_thy, anc_name) =>
                      (case Redblackmap.peek(!ancestor_exports,
                                             (anc_thy, anc_name)) of
                         SOME gid => Array.update(p_remap, id, gid)
                       | NONE =>
                         print ("WARNING: unresolved " ^ anc_thy ^ "." ^
                                anc_name ^ "\n"))
                  | NONE => ()
                else ()
                end
            | ("P" :: id_s :: rule :: args) =>
                let val id = int_of id_s
                in if Array.sub(live_p, id) then
                  let val gid = !global_thm_id
                      val remapped = remap_args ry rt rp rule args
                  in global_thm_id := gid + 1;
                     Array.update(p_remap, id, gid);
                     TextIO.output(ostrm, "P " ^ its gid ^ " " ^
                       rule ^ " " ^
                       String.concatWith " " remapped ^ "\n")
                  end
                else ()
                end
            | ("C" :: args) =>
                (* Remap C entry *)
                let
                  fun ai n = int_of (List.nth(args, n))
                  val cy = its (ry (ai 0))
                  val ny = its (ry (ai 1))
                  val rest = List.drop(args, 2)
                  val cvals = List.tabulate(29, fn i =>
                    List.nth(rest, 2*i) ^ " " ^
                    its (rt (int_of (List.nth(rest, 2*i + 1)))))
                  val rest2 = List.drop(rest, 58)
                  val char_pairs =
                    let fun go [] = []
                          | go (n::p::r) =
                              (n ^ " " ^ its (rp (int_of p))) :: go r
                          | go _ = []
                    in go rest2 end
                in TextIO.output(ostrm, "C " ^ cy ^ " " ^ ny ^ " " ^
                     String.concatWith " " cvals ^ " " ^
                     String.concatWith " " char_pairs ^ "\n")
                end
            | _ => ()  (* skip V, N, E, blank lines *)
            end

          fun read_all () =
            case TextIO.inputLine instrm of
              NONE => ()
            | SOME line =>
                (process_line (String.substring(line, 0, size line - 1)
                               handle Subscript => line);
                 read_all ())
        in
          read_all ();
          ReplayTrace.close_trace (instrm, proc);
          (* Register exports *)
          List.app (fn (name, local_id) =>
            let val gid = Array.sub(p_remap, local_id)
            in if gid >= 0 then
                 ancestor_exports :=
                   Redblackmap.insert(!ancestor_exports,
                                     (thy, name), gid)
               else ()
            end) (#exports data)
        end

    val _ = List.app write_theory topo

    (* Write exports *)
    val _ = List.app (fn (thy, name) =>
      case Redblackmap.peek(!ancestor_exports, (thy, name)) of
        SOME gid =>
          TextIO.output(ostrm, "E " ^ esc name ^ " " ^
                        its gid ^ "\n")
      | NONE =>
          print ("WARNING: desired export " ^ thy ^ "." ^ name ^
                 " not found\n")) desired_exports

    val _ = TextIO.closeOut ostrm
  in
    print ("Merged trace: " ^ its (!global_ty_id) ^ " types, " ^
           its (!global_tm_id) ^ " terms, " ^
           its (!global_thm_id) ^ " thms -> " ^
           output_path ^ "\n")
  end

end
