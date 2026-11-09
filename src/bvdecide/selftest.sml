open HolKernel Parse boolLib testutils bvDecideLib

(* The certificate checker on a small CNF, without CaDiCaL: an accepted
   certificate, and the mutations it must reject. *)
local
  fun cnum n = cvSyntax.mk_cv_num (numSyntax.term_of_int n)
  fun clist f xs =
    List.foldr (fn (x, a) => cvSyntax.mk_cv_pair (f x, a)) (cnum 0) xs
  fun cint i =
    if i < 0 then cvSyntax.mk_cv_pair (cnum (~i), cnum 0) else cnum i
  fun csteps ss =
    clist (fn (n, c, hs) =>
             cvSyntax.mk_cv_pair
               (cnum n, cvSyntax.mk_cv_pair (clist cint c, clist cnum hs)))
          ss
  val check_tm = prim_mk_const {Thy = "lratCheck", Name = "cv_check_unsat"}
  val canon_tm = prim_mk_const {Thy = "lratCheck", Name = "cv_canon_steps"}
  val eqs = cv_transLib.cv_eqs_for check_tm @
            List.map (fn n => DB.fetch "lratCheck" n)
              ["cv_canon_steps_def", "cv_canon_ints_def", "cv_canon_nums_def",
               "cv_canon_int_def"]
  fun accepts cnf c =
    let val th = cv_computeLib.cv_compute eqs
                   (list_mk_comb (check_tm, [mk_comb (canon_tm, c),
                                             clist (clist cint) cnf]))
    in aconv (rhs (concl th)) (cnum 1) end
  (* all four clauses over x1, x2: derive [x2], then the empty clause *)
  val cnf = [[1, 2], [~1, 2], [1, ~2], [~1, ~2]]
  val good = [(5, [2], [1, 2]), (6, [], [5, 3, 4])]
  fun check (name, cnf, c, want) =
    (tprint ("check_unsat_cv: " ^ name);
     if accepts cnf c = want then OK ()
     else die (if want then "rejected" else "accepted"))
in
val _ = List.app check [
  ("certificate accepted", cnf, csteps good, true),
  ("dropped hint rejected", cnf,
   csteps [(5, [2], [1, 2]), (6, [], [5, 3])], false),
  ("literal 0 rejected", cnf,
   csteps [(5, [0], [1, 2]), (6, [], [5, 3, 4])], false),
  ("no certificate rejected", cnf, csteps [], false),
  ("wrong CNF rejected", List.take (cnf, 3), csteps good, false)]
end

(* proved, with no hypothesis and no tag beyond DISK_THM *)
fun proves (name, q) =
  let val g = Term q
  in
    tprint ("BV_DECIDE_PROVE: " ^ name);
    case Lib.total BV_DECIDE_PROVE g of
        NONE => die "not proved"
      | SOME th =>
          if not (null (hyp th)) orelse not (aconv (concl th) g) then
            die "wrong theorem"
          else
            case Tag.dest_tag (Thm.tag th) of
                (["DISK_THM"], []) => OK ()
              | (os, ds) => die ("tags " ^ String.concatWith "," (os @ ds))
  end

fun refuses (name, q, msg) =
  let val _ = tprint ("BV_DECIDE_PROVE fails: " ^ name)
      val m = (BV_DECIDE_PROVE (Term q); "proved")
              handle e => General.exnMessage e
  in if String.isSubstring msg m then OK () else die m end

val have_cadical =
  Option.isSome (OS.Process.getEnv "HOL_CADICAL") orelse
  List.exists
    (fn d => OS.FileSys.access (OS.Path.concat (d, "cadical"),
                                [OS.FileSys.A_EXEC]))
    (String.fields (fn c => c = #":")
                   (Option.getOpt (OS.Process.getEnv "PATH", "")))

val _ =
  if not have_cadical then
    print "Skipping BV_DECIDE_PROVE tests: no CaDiCaL (set HOL_CADICAL)\n"
  else
    (List.app proves [
       ("transitivity of <+",
        `!(a:256 word) b c. a <+ b /\ b <+ c ==> a <+ c`),
       ("low bit of a sum",
        `!(a:256 word) b. (a + b) && 1w = (a ?? b) && 1w`),
       ("mask split", `!(x:256 word) m. x = x && m || x && ~m`),
       ("or is zero",
        `!(v1:256 word) v2. v1 || v2 = 0w ==> v1 = 0w /\ v2 = 0w`),
       ("bit of a shift", `!a:16 word. a ' 3 = (a >>> 3) ' 0`),
       ("arithmetic shift", `!a:8 word. word_msb a ==> a >> 7 = -1w`),
       ("abstracted atom",
        `!(f:num -> 8 word) n. f n && 1w = 0w ==> (f n + 1w) && 1w = 1w`),
       ("atom with a variable named i",
        `!(f:num -> 8 word) i. f i && 1w = 0w ==> (f i + 1w) && 1w = 1w`)];
     refuses ("false goal", `!(a:8 word) b. a + b = a`, "goal is false"))
