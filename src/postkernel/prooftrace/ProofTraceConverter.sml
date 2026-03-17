structure ProofTraceConverter :> ProofTraceConverter = struct

open ProofTraceParser
fun convert (root, objs) file = let
  val out = TextIO.openOut file
  fun write s = (TextIO.output (out, s); TextIO.flushOut out)
  val _ = write "V 1\n"
  val {theory, types, constants, all_thms, ...} = shRoot objs root
  datatype cache = Empty | Typ of int | Term of int | Thm of int | Compute1 of int | Compute2 of int
  val cache = Array.array (heapSize objs, Empty)

  val tyN = ref 0
  val tmN = ref 0
  val thN = ref 0
  val c1N = ref 0
  val c2N = ref 0

  fun visitType w = case ptr w of p =>
    case Array.sub (cache, p) of Typ n => n | _ => let
    fun start () = let
      val n = !tyN before tyN := !tyN + 1
      val _ = Array.update (cache, p, Typ n)
      in write "Y "; write (Int.toString n); n end
    in
      case shType objs w of
        Tyapp (id, args) => let
        val (thy, name) = ident objs id
        val buf = ref []
        fun write' s = buf := s :: !buf
        val _ = appList objs (fn ty => app write' [" ", Int.toString (visitType ty)]) args
        val n = start ()
        val _ = app write (" O " :: mlquote thy :: " " :: mlquote name :: rev (!buf))
        in write "\n"; n end
      | Tyv v => let
        val n = start ()
        in app write [" V ", mlquote v, "\n"]; n end
    end

  fun visitTerm w = case ptr w of p =>
    case Array.sub (cache, p) of Term n => n | _ => let
    fun start () = let
      val n = !tmN before tmN := !tmN + 1
      val _ = Array.update (cache, p, Term n)
      in write "T "; write (Int.toString n); n end
    in
      case shTerm objs w of
        Abs (v, body) => let
        val v = visitTerm v; val body = visitTerm body; val n = start ()
        in app write [" l ", Int.toString v, " ", Int.toString body, "\n"]; n end
      | Bv v => let val n = start () in app write [" v ", Int.toString v, "\n"]; n end
      | Clos (subs, e) => let
        val buf = ref []
        fun write' s = buf := s :: !buf
        fun go w =
          case shSubs objs w of
            Cons (s, e) => (app write' [" C ", Int.toString (visitTerm e)]; go s)
          | Id => write' " I "
          | Lift (n, s) => (app write' [" L ", Int.toString n]; go s)
          | Shift (n, s) => (app write' [" S ", Int.toString n]; go s)
        val _ = go subs; val e = visitTerm e; val n = start ()
        in app write (" S " :: rev (!buf)); app write [Int.toString e, "\n"]; n end
      | Comb (f, x) => let
        val f = visitTerm f; val x = visitTerm x; val n = start ()
        in app write [" A ", Int.toString f, " ", Int.toString x, "\n"]; n end
      | Const (c, ty) => let
        val (thy, name) = ident objs c; val ty = visitType ty; val n = start ()
        in app write [" C ", mlquote thy, " ", mlquote name, " ", Int.toString ty, "\n"]; n end
      | Fv (v, ty) => let
        val ty = visitType ty; val n = start ()
        in app write [" V ", mlquote v, " ", Int.toString ty, "\n"]; n end
    end

  val visitThm = let
    fun hol_type write w = app write [" ", Int.toString (visitType w)]
    fun term write w = app write [" ", Int.toString (visitTerm w)]
    fun string write w = app write [" ", mlquote (str objs w)]
    fun tup2 (p, q) write = ignore o tuple2 objs (p write, q write)
    fun list p write w = (write " ["; appList objs (p write) w; write " ]")
    fun opt p write w = case option objs I w of
        NONE => write "~"
      | SOME w => p write w
    fun subst w = list (tup2 w)
    fun thm write w = app write [" ", Int.toString (visitThm w)]
    and visitCompute1 w = case ptr w of p =>
      case Array.sub (cache, p) of Compute1 n => n | _ => let
      val {num_type, char_eqns, cval_type, cval_terms} = shComputeArgs objs w
      val buf = ref []
      fun write' s = buf := s :: !buf
      val _ = list (tup2 (string, term)) write' cval_terms
      val _ = hol_type write' cval_type
      val _ = hol_type write' num_type
      val _ = list (tup2 (string, thm)) write' char_eqns
      val n = !c1N before c1N := !c1N + 1
      val _ = Array.update (cache, p, Compute1 n)
      in app write ("M " :: Int.toString n :: rev (!buf)); write "\n"; n end
    and visitCompute2 w = case ptr w of p =>
      case Array.sub (cache, p) of Compute2 n => n | _ => let
      val buf = ref []
      fun write' s = buf := s :: !buf
      val (x, _) = tuple2 objs (visitCompute1, appList objs (thm write')) w
      val n = !c2N before c2N := !c2N + 1
      val _ = Array.update (cache, p, Compute2 n)
      val _ = app write ("M2 " :: Int.toString n :: " " :: Int.toString x :: rev (!buf))
      in write "\n"; n end
    and compute_prep write w = app write [" ", Int.toString (visitCompute2 w)]
    and visitThm w = case ptr w of p =>
      case Array.sub (cache, p) of Thm n => n | _ => let
      val (hyps, concl, proof) = shThm objs w
      val _ = (appSet objs visitTerm hyps; visitTerm concl)
      val buf = ref []
      fun %f = f (fn s => buf := s :: !buf)
      val rule = case shProof objs proof of
        ABS_prf (a, b) => (%term a; %thm b; "ABS")
      | ALPHA_prf (a, b) => (%term a; %term b; "ALPHA")
      | AP_TERM_prf (a, b) => (%term a; %thm b; "AP_TERM")
      | AP_THM_prf (a, b) => (%thm a; %term b; "AP_THM")
      | ASSUME_prf a => (%term a; "ASSUME")
      | Axiom_prf => "Axiom"
      | BETA_CONV_prf a => (%term a; "BETA_CONV")
      | Beta_prf a => (%thm a; "Beta")
      | CCONTR_prf (a, b) => (%term a; %thm b; "CCONTR")
      | CHOOSE_prf (a, b, c) => (%term a; %thm b; %thm c; "CHOOSE")
      | CONJUNCT1_prf a => (%thm a; "CONJUNCT1")
      | CONJUNCT2_prf a => (%thm a; "CONJUNCT2")
      | CONJ_prf (a, b) => (%thm a; %thm b; "CONJ")
      | DISCH_prf (a, b) => (%term a; %thm b; "DISCH")
      | DISJ1_prf (a, b) => (%thm a; %term b; "DISJ1")
      | DISJ2_prf (a, b) => (%term a; %thm b; "DISJ2")
      | DISJ_CASES_prf (a, b, c) => (%thm a; %thm b; %thm c; "DISJ_CASES")
      | Def_const_list_prf (a, b) => (%thm a; %(list term) b; "Def_const_list")
      | Def_const_prf (a, b) => (%term a; %term b; "Def_const")
      | Def_spec_prf (a, b) => (%thm a; %(list term) b; "Def_spec")
      | Def_tyop_prf (a, b, c) => (%(list hol_type) a; %thm b; %hol_type c; "Def_tyop")
      | Disk_prf _ => "Disk"
      | EQ_IMP_RULE1_prf a => (%thm a; "EQ_IMP_RULE1")
      | EQ_IMP_RULE2_prf a => (%thm a; "EQ_IMP_RULE2")
      | EQ_MP_prf (a, b) => (%thm a; %thm b; "EQ_MP")
      | EXISTS_prf (a, b, c) => (%term a; %term b; %thm c; "EXISTS")
      | GENL_prf (a, b) => (%(list term) a; %thm b; "GENL")
      | GEN_ABS_prf (a, b, c) => (%(opt term) a; %(list term) b; %thm c; "GEN_ABS")
      | GEN_prf (a, b) => (%term a; %thm b; "GEN")
      | INST_TYPE_prf (a, b) => (%(subst (hol_type, hol_type)) a; %thm b; "INST_TYPE")
      | INST_prf (a, b) => (%(subst (term, term)) a; %thm b; "INST")
      | MK_COMB_prf (a, b) => (%thm a; %thm b; "MK_COMB")
      | MP_prf (a, b) => (%thm a; %thm b; "MP")
      | Mk_abs_prf (a, b, c) => (%thm a; %term b; %thm c; "Mk_abs")
      | Mk_comb_prf (a, b, c) => (%thm a; %thm b; %thm c; "Mk_comb")
      | NOT_ELIM_prf a => (%thm a; "NOT_ELIM")
      | NOT_INTRO_prf a => (%thm a; "NOT_INTRO")
      | REFL_prf a => (%term a; "REFL")
      | SPEC_prf (a, b) => (%term a; %thm b; "SPEC")
      | SUBST_prf (a, b, c) => (%(subst (term, thm)) a; %term b; %thm c; "SUBST")
      | SYM_prf a => (%thm a; "SYM")
      | Specialize_prf (a, b) => (%term a; %thm b; "Specialize")
      | TRANS_prf (a, b) => (%thm a; %thm b; "TRANS")
      | compute_prf (a, b) => (%compute_prep a; %term b; "compute")
      | deductAntisym_prf (a, b) => (%thm a; %thm b; "deductAntisym")
      | deleted_prf => "deleted"
      | save_dep_prf a => (%thm a; "save_dep")
      val n = !thN before thN := !thN + 1
      val _ = Array.update (cache, p, Thm n)
      val _ = app write ("P " :: Int.toString n :: " " :: rule :: rev (!buf))
      in write "\n"; n end
    in visitThm end

  val _ = appList objs ((fn (name, arity) =>
    app write ["O ", mlquote theory, " ", mlquote name, " ", Int.toString arity, "\n"]
  ) o tuple2 objs (str objs, int)) types

  val _ = appList objs ((fn (name, ty) =>
    app write ["C ", mlquote theory, " ", mlquote name, " ", Int.toString ty, "\n"]
  ) o tuple2 objs (str objs, visitType)) constants

  val _ = appList objs (tuple3 objs (K(), visitThm, K())) all_thms

  val _ = app write ["N ", mlquote theory, "\n"]

  val _ = appList objs ((fn (name, (thm, {private})) => (
    write "E ";
    if private then () else (write (mlquote name); write " ");
    write (Int.toString thm); write "\n"
  )) o tuple3 objs (str objs, visitThm, shThmInfo objs)) all_thms

  in TextIO.closeOut out end

end
