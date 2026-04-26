structure PFTReplay :> PFTReplay = struct

open Feedback Lib Type Term Thm

infix |->

(* ========================================================================= *)
(* trDB: theorem database keyed by "Thy$name" / "Thy#n"                      *)
(* ========================================================================= *)

type trDB = (string, thm) Redblackmap.dict

val empty_trDB = Redblackmap.mkDict String.compare

fun lookup (db: trDB) key = Redblackmap.peek(db, key)

fun size (db: trDB) = Redblackmap.numItems db

fun listItems (db: trDB) = Redblackmap.listItems db

(* ========================================================================= *)
(* Filename parsing                                                          *)
(* ========================================================================= *)

val known_extensions = [
  (".pft.jsonl", false),
  (".pft.bin",   true),
  (".pft",       true)
]

fun parse_filename file = let
  val base = OS.Path.file file
  fun try [] = raise Fail ("PFTReplay: unrecognised extension: " ^ file)
    | try ((ext, binary) :: rest) =
        if String.isSuffix ext base
        then (Substring.string
                (Substring.trimr (String.size ext) (Substring.full base)),
              binary)
        else try rest
in try known_extensions end

(* ========================================================================= *)
(* Name parsing: "thy$name" -> ("thy","name")                                *)
(* ========================================================================= *)

fun split_qualified s = let
  fun find i =
    if i >= String.size s then
      raise Fail ("PFTReplay: unqualified name: " ^ s)
    else if String.sub(s, i) = #"$" then
      (String.substring(s, 0, i), String.extract(s, i+1, NONE))
    else find (i + 1)
in find 0 end

(* ========================================================================= *)
(* Replay                                                                    *)
(* ========================================================================= *)

fun replay (db: trDB) file = let
  val db_ref = ref db
  val (thyname, binary) = parse_filename file
  val {n_ty, n_tm, n_th, n_ci} =
    PFTReader.read_limits {file = file, binary = binary}

  val tys : hol_type option array = Array.array(n_ty, NONE)
  val tms : term option array     = Array.array(n_tm, NONE)
  val ths : thm option array      = Array.array(n_th, NONE)
  val cis : (thm list -> term -> thm) option array =
    Array.array(n_ci, NONE)

  fun get msg arr i = case Array.sub(arr, i) of
      SOME x => x
    | NONE => raise Fail ("PFTReplay: dead " ^ msg ^ " " ^ Int.toString i)
  val get_ty = get "ty" tys
  val get_tm = get "tm" tms
  val get_th = get "th" ths
  val get_ci = get "ci" cis

  fun set_ty (i, v) = Array.update(tys, i, SOME v)
  fun set_tm (i, v) = Array.update(tms, i, SOME v)
  fun set_th (i, v) = Array.update(ths, i, SOME v)
  fun set_ci (i, v) = Array.update(cis, i, SOME v)

  fun del_ns ("ty", i) = Array.update(tys, i, NONE)
    | del_ns ("tm", i) = Array.update(tms, i, NONE)
    | del_ns ("th", i) = Array.update(ths, i, NONE)
    | del_ns ("ci", i) = Array.update(cis, i, NONE)
    | del_ns (ns, _) = raise Fail ("PFTReplay: unknown ns " ^ ns)

  fun del_range_ns (ns, lo, hi) = let
    fun loop i = if i > hi then ()
                 else (del_ns (ns, i); loop (i + 1))
  in loop lo end

  (* Extract common theory prefix from qualified names ["thy$c1","thy$c2",...] *)
  fun thy_of_names names = case names of
      [] => raise Fail "PFTReplay: empty names list"
    | (n :: rest) => let val (t, _) = split_qualified n in
        List.app (fn n' =>
          if #1 (split_qualified n') = t then ()
          else raise Fail ("PFTReplay: inconsistent theory prefix: "
                           ^ n ^ " vs " ^ n')) rest;
        t end

  (* ---- Format handler -------------------------------------------------- *)

  val format_handler : PFTReader.format_handler = {
    tyvar = fn (id, name) =>
      set_ty (id, mk_vartype name),

    tyop = fn (id, name, args) => let
      val (Thy, Tyop) = split_qualified name
      val Args = List.map get_ty args
    in set_ty (id, mk_thy_type {Thy=Thy, Tyop=Tyop, Args=Args}) end,

    var = fn (id, name, ty) =>
      set_tm (id, mk_var(name, get_ty ty)),

    const = fn (id, name, ty) => let
      val (Thy, Name) = split_qualified name
    in set_tm (id, mk_thy_const {Thy=Thy, Name=Name, Ty=get_ty ty}) end,

    comb = fn (id, f, x) =>
      set_tm (id, mk_comb(get_tm f, get_tm x)),

    abs = fn (id, v, b) =>
      set_tm (id, mk_abs(get_tm v, get_tm b)),

    new_const = fn (name, ty) => let
      val (Thy, Name) = split_qualified name
    in ignore (
         Term.prim_mk_const {Thy=Thy, Name=Name}
         handle HOL_ERR _ =>
           Term.prim_new_const {Thy=Thy, Name=Name} (get_ty ty))
    end,

    new_type = fn (name, arity) => let
      val (Thy, Tyop) = split_qualified name
    in case Type.op_arity {Thy=Thy, Tyop=Tyop} of
         SOME n => if n = arity then ()
                   else raise Fail ("PFTReplay: new_type arity mismatch: " ^
                                    name)
       | NONE => Type.prim_new_type {Thy=Thy, Tyop=Tyop} arity
    end,

    axiom = fn (id, tm, nameOpt) => let
      val c = get_tm tm
      val ax_name = case nameOpt of
          SOME n => n
        | NONE => (print "WARNING: PFTReplay: axiom without name\n";
                   "UNNAMED_AXIOM")
    in set_th (id, mk_axiom_thm(Nonce.mk ax_name, c)) end,

    save = fn (name, th) =>
      db_ref := Redblackmap.insert(!db_ref, name, get_th th),

    load = fn (id, name) =>
      (case Redblackmap.peek(!db_ref, name) of
         SOME th => set_th (id, th)
       | NONE => raise Fail ("PFTReplay: load: not found: " ^ name)),

    del = del_ns,

    del_range = del_range_ns
  }

  (* ---- Bool constant registration --------------------------------------- *)

  fun register_bool_def name thm =
    case name of
      "T"               => register_T thm
    | "!"               => register_forall thm
    | "?"               => register_exists thm
    | "F"               => register_F thm
    | "~"               => register_neg thm
    | "/\\"             => register_conj thm
    | "\\/"             => register_disj thm
    | "TYPE_DEFINITION" => register_type_definition thm
    | _                 => ()

  (* ---- HOL4 ruleset handler -------------------------------------------- *)

  val hol4_handler : PFTReader.HOL4.handler = {
    refl = fn (id, tm) =>
      set_th (id, REFL (get_tm tm)),

    alpha = fn (id, a, b) =>
      set_th (id, ALPHA (get_tm a) (get_tm b)),

    beta_conv = fn (id, tm) =>
      set_th (id, BETA_CONV (get_tm tm)),

    sym = fn (id, a) =>
      set_th (id, SYM (get_th a)),

    trans = fn (id, a, b) =>
      set_th (id, TRANS (get_th a) (get_th b)),

    eq_mp = fn (id, a, b) =>
      set_th (id, EQ_MP (get_th a) (get_th b)),

    mk_comb = fn (id, a, b) =>
      set_th (id, MK_COMB (get_th a, get_th b)),

    abs_thm = fn (id, v, th) =>
      set_th (id, ABS (get_tm v) (get_th th)),

    ap_term = fn (id, tm, th) =>
      set_th (id, AP_TERM (get_tm tm) (get_th th)),

    ap_thm = fn (id, th, tm) =>
      set_th (id, AP_THM (get_th th) (get_tm tm)),

    beta_thm = fn (id, th) =>
      set_th (id, Beta (get_th th)),

    mk_comb_thm = fn (id, th1, th2, th3) => let
      val (_, _, mkc) = Mk_comb (get_th th1)
    in set_th (id, mkc (get_th th2) (get_th th3)) end,

    mk_abs_thm = fn (id, th1, th3) => let
      val (_, _, mka) = Mk_abs (get_th th1)
    in set_th (id, mka (get_th th3)) end,

    assume = fn (id, tm) =>
      set_th (id, ASSUME (get_tm tm)),

    mp = fn (id, a, b) =>
      set_th (id, MP (get_th a) (get_th b)),

    disch = fn (id, tm, th) =>
      set_th (id, DISCH (get_tm tm) (get_th th)),

    not_intro = fn (id, th) =>
      set_th (id, NOT_INTRO (get_th th)),

    not_elim = fn (id, th) =>
      set_th (id, NOT_ELIM (get_th th)),

    ccontr = fn (id, tm, th) =>
      set_th (id, CCONTR (get_tm tm) (get_th th)),

    deductAntisym = fn _ =>
      raise Fail "PFTReplay: deductAntisym not implemented",

    conj = fn (id, a, b) =>
      set_th (id, CONJ (get_th a) (get_th b)),

    conjunct1 = fn (id, th) =>
      set_th (id, CONJUNCT1 (get_th th)),

    conjunct2 = fn (id, th) =>
      set_th (id, CONJUNCT2 (get_th th)),

    disj1 = fn (id, th, tm) =>
      set_th (id, DISJ1 (get_th th) (get_tm tm)),

    disj2 = fn (id, tm, th) =>
      set_th (id, DISJ2 (get_tm tm) (get_th th)),

    disj_cases = fn (id, th0, th1, th2) =>
      set_th (id, DISJ_CASES (get_th th0) (get_th th1) (get_th th2)),

    gen = fn (id, tm, th) =>
      set_th (id, GEN (get_tm tm) (get_th th)),

    spec = fn (id, tm, th) =>
      set_th (id, SPEC (get_tm tm) (get_th th)),

    specialize = fn (id, tm, th) =>
      set_th (id, Specialize (get_tm tm) (get_th th)),

    genl = fn (id, th, tms) =>
      set_th (id, GENL (List.map get_tm tms) (get_th th)),

    exists = fn (id, p, w, th) =>
      set_th (id, EXISTS (get_tm p, get_tm w) (get_th th)),

    choose = fn (id, v, th1, th2) =>
      set_th (id, CHOOSE (get_tm v, get_th th1) (get_th th2)),

    absl = fn (id, th, tms) => let
      fun fold_abs (tm_id, acc) = ABS (get_tm tm_id) acc
    in set_th (id, List.foldr fold_abs (get_th th) tms) end,

    gen_abs = fn (id, th, c, tms) =>
      set_th (id, GEN_ABS (SOME (get_tm c))
                           (List.map get_tm tms) (get_th th)),

    inst = fn (id, th, pairs) => let
      val s = List.map (fn (a, b) => get_tm a |-> get_tm b) pairs
    in set_th (id, INST s (get_th th)) end,

    inst_type = fn (id, th, pairs) => let
      val s = List.map (fn (a, b) => get_ty a |-> get_ty b) pairs
    in set_th (id, INST_TYPE s (get_th th)) end,

    subst = fn (id, template, th, pairs) => let
      val s = List.map (fn (a, b) => get_tm a |-> get_th b) pairs
    in set_th (id, SUBST s (get_tm template) (get_th th)) end,

    eq_imp_rule1 = fn (id, th) =>
      set_th (id, #1 (EQ_IMP_RULE (get_th th))),

    eq_imp_rule2 = fn (id, th) =>
      set_th (id, #2 (EQ_IMP_RULE (get_th th))),

    def_tyop = fn (id, th, name) => let
      val (Thy, Tyop) = split_qualified name
    in set_th (id, prim_type_definition ({Thy=Thy, Tyop=Tyop},
                                         get_th th)) end,

    def_spec = fn (id, th, names) => let
      val thy = thy_of_names names
      val cnames = List.map (#2 o split_qualified) names
    in set_th (id, prim_specification thy cnames (get_th th)) end,

    def_spec_gen = fn (id, th, names) => let
      val thy = thy_of_names names
      val thm = #2 (gen_prim_specification thy (get_th th))
      val () = if thy = "bool" then
                 List.app (fn n => register_bool_def (#2 (split_qualified n)) thm)
                   names
               else ()
    in set_th (id, thm) end,

    compute_init = fn (id, ty1, ty2, eqns, terms) => let
      val num_type = get_ty ty1
      val cval_type = get_ty ty2
      val char_eqns = List.map (fn (s, t) => (s, get_th t)) eqns
      val cval_terms = List.map (fn (s, t) => (s, get_tm t)) terms
    in set_ci (id, compute {num_type = num_type, char_eqns = char_eqns,
                            cval_type = cval_type,
                            cval_terms = cval_terms}) end,

    compute = fn (id, ci, tm, ths) => let
      val f = get_ci ci
      val t = get_tm tm
      val thms = List.map get_th ths
    in set_th (id, f thms t) end
  }

  val _ = PFTReader.read {
    file = file,
    binary = binary,
    format_handler = format_handler,
    ruleset_handler = PFTReader.HOL4.make_handler hol4_handler
  }
in !db_ref end

end
