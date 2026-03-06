structure ProofTraceConverter :> ProofTraceConverter = struct

open ProofTraceParser
fun convert (root, objs) file = let
  val out = TextIO.openOut file
  fun write s = (TextIO.output (out, s); TextIO.flushOut out)
  val _ = write "V 1\n"
  val {theory, types, constants, all_thms, ...} = shRoot objs root
  datatype cache = Empty | Typ of int | Term of int | Thm of int
  val cache = Array.array (DArray.size objs, Empty)

  val tyN = ref 0
  val tmN = ref 0
  val thN = ref 0

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

  local
    val visitThm = ref ((fn _ => raise Fail "missing"): Word64.word -> int)
    fun ThyName (write, w) = let
      val (Thy, Name) = tuple2 objs (str objs, str objs) w
      in app write [" ", mlquote Thy, " ", mlquote Name] end
    val ThyTyop = ThyName
    fun hol_type (write, w) = app write [" ", Int.toString (visitType w)]
    fun term (write, w) = app write [" ", Int.toString (visitTerm w)]
    fun thm (write, w) = app write [" ", Int.toString (!visitThm w)]
    fun string (write, w) = app write [" ", mlquote (str objs w)]
    fun tup2 (p, q) (write, w) = let
      val (x, y) = tuple2 objs (I, I) w
      in p (write, x); q (write, y) end
    fun list p (write, w) =
      (write " ["; appList objs (fn w => p (write, w)) w; write " ]")
    fun opt p (write, w) = case option objs I w of
        NONE => write "~"
      | SOME w => p (write, w)
    val subst = list o tup2
    val rules = Array.fromList [
      ("ABS", [term, thm]),
      ("ALPHA", [term, term]),
      ("AP_TERM", [term, thm]),
      ("AP_THM", [thm, term]),
      ("ASSUME", [term]),
      ("Axiom", []),
      ("BETA_CONV", [term]),
      ("Beta", [thm]),
      ("CCONTR", [term, thm]),
      ("CHOOSE", [term, thm, thm]),
      ("CONJUNCT1", [thm]),
      ("CONJUNCT2", [thm]),
      ("CONJ", [thm, thm]),
      ("DISCH", [term, thm]),
      ("DISJ1", [thm, term]),
      ("DISJ2", [term, thm]),
      ("DISJ_CASES", [thm, thm, thm]),
      ("Def_const_list", [string, list (tup2 (string, hol_type)), thm]),
      ("Def_const", [ThyName, term]),
      ("Def_spec", [list term, thm]),
      ("Def_tyop", [ThyTyop, list hol_type, thm, hol_type]),
      ("EQ_IMP_RULE1", [thm]),
      ("EQ_IMP_RULE2", [thm]),
      ("EQ_MP", [thm, thm]),
      ("EXISTS", [term, term, thm]),
      ("GENL", [list term, thm]),
      ("GEN_ABS", [opt term, list term, thm]),
      ("GEN", [term, thm]),
      ("INST_TYPE", [subst (hol_type, hol_type), thm]),
      ("INST", [subst (term, term), thm]),
      ("MK_COMB", [thm, thm]),
      ("MP", [thm, thm]),
      ("Mk_abs", [thm, term, thm]),
      ("Mk_comb", [thm, thm, thm]),
      ("NOT_ELIM", [thm]),
      ("NOT_INTRO", [thm]),
      ("REFL", [term]),
      ("SPEC", [term, thm]),
      ("SUBST", [subst (term, thm), term, thm]),
      ("SYM", [thm]),
      ("Specialize", [term, thm]),
      ("TRANS", [thm, thm]),
      ("compute", []),
      ("deductAntisym", [thm, thm]),
      ("deleted", [])]
  in
    val _ = visitThm := (fn w => case ptr w of p =>
      case Array.sub (cache, p) of Thm n => n | _ => let
      val (hyps, concl, proof) = shThm objs w
      val (i, ps) = shVariant objs proof
      val _ = (appSet objs visitTerm hyps; visitTerm concl)
      val (rule, args) = Array.sub (rules, i)
      val buf = ref []
      fun write' s = buf := s :: !buf
      fun go (p :: ps, g :: gs) = (g (write', p); go (ps, gs))
        | go _ = ()
      val _ = go (ps, args)
      val n = !thN before thN := !thN + 1
      val _ = Array.update (cache, p, Thm n)
      val _ = app write ("P " :: Int.toString n :: " " :: rule :: rev (!buf))
      in write "\n"; n end)
    val visitThm = fn x => !visitThm x
  end

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
