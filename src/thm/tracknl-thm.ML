(* ===================================================================== *)
(* FILE          : Thm.sml                                               *)
(* DESCRIPTION   : The abstract data type of theorems.                   *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon, University of Cambridge              *)
(*                     Konrad Slind, University of Calgary               *)
(*                                   University of Cambridge             *)
(*                     Bruno Barras, University of Cambridge and INRIA   *)
(* DATE          : September 10, 1991, Konrad Slind                      *)
(* Modified      : September 23, 1997, Ken Larsen                        *)
(*               : 1999, Bruno Barras                                    *)
(*               : July 2000, Konrad Slind                               *)
(*               : May 2023, Oskar Abrahamsson                           *)
(* ===================================================================== *)

structure Thm =
struct

open Feedback Lib Term Tag Dep Compute

type 'a set = 'a HOLset.set;
type depdisk = (string * int) * ((string * int list) list);
datatype thm = THM of Tag.tag * term HOLset.set * term * int

val --> = Type.-->;
infixr 3 -->;
infix 5 |-> ;

val kernelid = "tracknl"

(*---------------------------------------------------------------------------
     Trace infrastructure: stream proof steps to temp files on disk.
     Types/terms are interned via ordered maps (Redblackmap).
     Each thm gets a unique int trace ID.
 ---------------------------------------------------------------------------*)

val trace_counter = ref 0
val steps_strm : TextIO.outstream option ref = ref NONE
val parents_strm : TextIO.outstream option ref = ref NONE

(* Number of lines written to the current temp file.
   file_base_id = trace_counter - lines_written at any point. *)
val lines_written : int ref = ref 0

(* Cache external parent thm statements: trace_id -> (hyps, concl).
   Populated by record_step when parent thms have ID < file_base_id.
   Used by ProofTrace to write TRUST entries with thm statements. *)
val ext_thm_cache : (int, term list * term) Redblackmap.dict ref =
  ref (Redblackmap.mkDict Int.compare)

val ty_map = ref (Redblackmap.mkDict Type.compare)
val tm_map = ref (Redblackmap.mkDict Term.compare)
val ty_counter = ref 0
val tm_counter = ref 0
val ty_list : hol_type list ref = ref [] (* accumulated in reverse *)
val tm_list : term list ref = ref []     (* accumulated in reverse *)

(* Per-process temp file paths to avoid races in parallel builds.
   Paths include PID and are computed lazily (after heap restore). *)
val trace_steps_path_ref : string option ref = ref NONE
val trace_parents_path_ref : string option ref = ref NONE

fun trace_paths () =
  case (!trace_steps_path_ref, !trace_parents_path_ref) of
    (SOME s, SOME p) => (s, p)
  | _ =>
    let val pid = SysWord.toString (Posix.Process.pidToWord
                    (Posix.ProcEnv.getpid ()))
        val s = ".tracknl_" ^ pid ^ "_steps.log"
        val p = ".tracknl_" ^ pid ^ "_parents.tbl"
    in trace_steps_path_ref := SOME s;
       trace_parents_path_ref := SOME p;
       (s, p)
    end

fun trace_steps_path () = #1 (trace_paths ())
fun trace_parents_path () = #2 (trace_paths ())

fun open_trace_streams () =
  let val s = TextIO.openAppend (trace_steps_path ())
      val p = TextIO.openAppend (trace_parents_path ())
  in steps_strm := SOME s;
     parents_strm := SOME p;
     (s, p)
  end

fun get_steps_strm () = case !steps_strm of
    SOME s => s
  | NONE => #1 (open_trace_streams ())

fun get_parents_strm () = case !parents_strm of
    SOME s => s
  | NONE => #2 (open_trace_streams ())

val its = Int.toString

fun intern_type ty =
  case Redblackmap.peek (!ty_map, ty) of
    SOME id => id
  | NONE =>
    let val _ = if not (Type.is_vartype ty) then
                  let val {Args,...} = Type.dest_thy_type ty
                  in List.app (ignore o intern_type) Args end
                else ()
        val id = !ty_counter
    in ty_counter := id + 1;
       ty_map := Redblackmap.insert (!ty_map, ty, id);
       ty_list := ty :: !ty_list;
       id
    end

fun intern_term tm =
  case Redblackmap.peek (!tm_map, tm) of
    SOME id => id
  | NONE =>
    let val _ = case dest_term tm of
            VAR _ => ignore (intern_type (type_of tm))
          | CONST _ => ignore (intern_type (type_of tm))
          | COMB (f, x) => (ignore (intern_term f); ignore (intern_term x))
          | LAMB (v, b) => (ignore (intern_term v); ignore (intern_term b))
        val id = !tm_counter
    in tm_counter := id + 1;
       tm_map := Redblackmap.insert (!tm_map, tm, id);
       tm_list := tm :: !tm_list;
       id
    end

(* Cache external parent thm statements (hyps, concl) for TRUST entries.
   A parent is external if its trace_id < file_base_id. *)
fun cache_ext_parents parent_thms =
  let
    (* base = trace_counter - lines_written: first ID in current temp file *)
    val base = !trace_counter - !lines_written
    fun get_id (THM(_, _, _, id)) = id
  in
    if !lines_written = 0 then ()  (* no file yet *)
    else List.app (fn thm =>
      let val id = get_id thm
          val THM(_, hyps, c, _) = thm
      in if id < base then
        (case Redblackmap.peek(!ext_thm_cache, id) of
           SOME _ => ()
         | NONE =>
           let val hyp_list = HOLset.listItems hyps
           in ignore (intern_term c);
              List.app (ignore o intern_term) hyp_list;
              ext_thm_cache :=
                Redblackmap.insert(!ext_thm_cache, id, (hyp_list, c))
           end)
        else ()
      end) parent_thms
  end

(* Cleanup handler ref: populated after trace_close_files is defined.
   Re-registered after heap restore since atExit handlers don't
   survive PolyML.SaveState.loadState. *)
val trace_cleanup_fn : (unit -> unit) ref = ref (fn () => ())
fun trace_cleanup () = (!trace_cleanup_fn) ()

(* Ensure both streams are open before writing to either.
   This avoids partial writes when one stream is stale after heap restore. *)
fun record_step line parent_thms =
  let
    fun get_id (THM(_, _, _, id)) = id
    val parent_ids = map get_id parent_thms
    val sf = get_steps_strm ()
    val pf = get_parents_strm ()
    fun write (s, p) =
      (TextIO.output(s, line);
       TextIO.output(s, "\n");
       TextIO.output(p, String.concatWith " " (map its parent_ids));
       TextIO.output(p, "\n"))
  in
    write (sf, pf)
    handle IO.Io _ =>
      (* Stale streams after heap restore — reopen both atomically.
         Also reset path refs and lines counter for the new file.
         Re-register atExit since loadState doesn't preserve it. *)
      (steps_strm := NONE; parents_strm := NONE;
       trace_steps_path_ref := NONE; trace_parents_path_ref := NONE;
       lines_written := 0;
       (* atExit handlers don't survive loadState; always re-register
          when we detect heap restore via IO.Io *)
       (OS.Process.atExit trace_cleanup handle _ => ());
       write (open_trace_streams ()));
    lines_written := !lines_written + 1;
    cache_ext_parents parent_thms
  end

fun trace_id (THM(_,_,_,id)) = id

val iT = intern_term
val iY = intern_type

(* Format a theorem statement as term IDs: "<concl> <n_hyps> <hyp1> ..." *)
fun fmt_thm_stmt (THM(_, hyps, c, _)) =
  let
    val c_id = iT c
    val hyp_list = HOLset.listItems hyps
    val hyp_ids = map iT hyp_list
  in
    its c_id ^ " " ^ its (length hyp_ids) ^
    (if null hyp_ids then ""
     else " " ^ String.concatWith " " (map its hyp_ids))
  end

(*---------------------------------------------------------------------------
       Exception handling
 ---------------------------------------------------------------------------*)

val thm_err = mk_HOL_ERR "Thm"
fun ERR f m = raise thm_err f m
fun Assert b s1 s2 = if b then () else ERR s1 s2


(*---------------------------------------------------------------------------*
 * Miscellaneous syntax routines.                                            *
 *---------------------------------------------------------------------------*)

val bool      = Type.bool
val alpha     = Type.alpha
fun dom ty    = fst (Type.dom_rng ty)
fun rng ty    = snd (Type.dom_rng ty);
val empty_tag = Tag.empty_tag


(*---------------------------------------------------------------------------
    The following are here because I didn't want to Thm to be dependent
    on some derived syntax (now in boolSyntax).
 ---------------------------------------------------------------------------*)
structure Susp = Portable.HOLSusp

val F = Susp.delay (fn () => mk_thy_const{Name="F", Thy="bool", Ty=bool});

val mk_neg = Susp.delay (fn () =>
  let val notc = mk_thy_const{Name="~",Thy="bool",Ty=bool --> bool}
  in fn M => mk_comb(notc,M)
  end);

val mk_forall = Susp.delay (fn () =>
 let val forallc = prim_mk_const{Name="!", Thy="bool"}
 in fn v => fn tm =>
      mk_comb(inst[alpha |-> type_of v] forallc, mk_abs(v,tm))
 end);

val mk_conj = Susp.delay (fn () =>
 let val conjc = prim_mk_const{Name="/\\", Thy="bool"}
 in fn (M,N) => list_mk_comb(conjc,[M,N])
 end);

val mk_disj = Susp.delay (fn () =>
 let val disjc = prim_mk_const{Name="\\/", Thy="bool"}
 in fn (M,N) => list_mk_comb(disjc,[M,N])
 end);


local val DEST_IMP_ERR = thm_err "dest_imp" ""
in
fun dest_imp M =
 let val (Rator,conseq) = with_exn dest_comb M DEST_IMP_ERR
 in if is_comb Rator
    then let val (Rator,ant) = dest_comb Rator
         in if Rator=Term.imp then (ant,conseq) else raise DEST_IMP_ERR
         end
    else case with_exn dest_thy_const Rator DEST_IMP_ERR
          of {Name="~", Thy="bool",...} => (conseq,Susp.force F)
           | otherwise => raise DEST_IMP_ERR
 end
end;

local val err = thm_err "dest_exists" ""
in
fun dest_exists tm =
 let val (Rator,Rand) = with_exn dest_comb tm err
 in case with_exn dest_thy_const Rator err
     of {Name="?", Thy="bool",...} => with_exn dest_abs Rand err
      | otherwise => raise err
 end
end;


(*---------------------------------------------------------------------------*
 * The type of theorems and some basic operations on it.                     *
 *---------------------------------------------------------------------------*)

(* datatype thm = datatype KernelTypes.thm *)

fun single_hyp tm = HOLset.singleton Term.compare tm
val empty_hyp = Term.empty_tmset
fun list_hyp tml = HOLset.addList(empty_hyp,tml)

fun tag  (THM(tg,_,_,_))  = tg
fun concl(THM(_,_,c,_))   = c
fun hypset  (THM(_,asl,_,_)) = asl
fun hyplist (THM(_,asl,_,_)) = HOLset.listItems asl
val hyp = hyplist   (* backwards compatibility *)

fun dest_thm(t as THM(_,asl,w,_)) = (hyplist t,w) (* Compatible with old code. *)
fun sdest_thm(THM(_,asl,w,_)) = (asl,w)
fun make_thm R (x,y,z) =
  let val id = !trace_counter
  in trace_counter := id + 1; Count.inc_count R; THM(x,y,z,id) end;

fun thm_frees (t as THM(_,asl,c,_)) = free_varsl (c::hyplist t);

fun add_hyp h asl = HOLset.add(asl,h)
fun union_hyp asl1 asl2 = HOLset.union(asl1, asl2)

fun tag_hyp_union thm_list =
  (itlist (Tag.merge o tag) (tl thm_list) (tag (hd thm_list)),
   itlist (union_hyp o hypset) thm_list empty_hyp);

fun var_occursl v l = isSome (HOLset.find (var_occurs v) l);

fun hypset_all P s = not (isSome (HOLset.find (not o P) s))
fun hypset_exists P s = isSome (HOLset.find P s)
fun hypset_map f s = HOLset.foldl(fn(i,s0) => HOLset.add(s0,f i)) empty_hyp s

fun hyp_tyvars th =
   HOLset.foldl (fn (h,tys) =>
                        List.foldl (fn (tyv,tys) => HOLset.add(tys,tyv))
                                   tys
                                   (Term.type_vars_in_term h))
                    (HOLset.empty Type.compare)
                    (hypset th)

fun hyp_frees th =
  HOLset.foldl (fn (h,tms) => Term.FVL[h] tms) empty_tmset (hypset th);

fun is_bool tm = (type_of tm = bool);


(*---------------------------------------------------------------------------
 *                THE PRIMITIVE RULES OF INFERENCE
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------*
 *                                                                           *
 *       ---------  ASSUME M                           [M is boolean]        *
 *         M |- M                                                            *
 *---------------------------------------------------------------------------*)

fun ASSUME tm =
   (Assert (is_bool tm) "ASSUME" "not a proposition";
    let val thm = make_thm Count.Assume (empty_tag,single_hyp tm,tm)
    in record_step ("ASSUME " ^ its (iT tm)) []; thm end);


(*---------------------------------------------------------------------------*
 *                                                                           *
 *         ---------  REFL M                                                 *
 *         |- M = M                                                          *
 *---------------------------------------------------------------------------*)

val mk_eq_nocheck = Term.prim_mk_eq;

fun refl_nocheck ty tm =
  let val thm = make_thm Count.Refl (empty_tag, empty_hyp, mk_eq_nocheck ty tm tm)
  in record_step ("REFL " ^ its (iT tm)) []; thm end;

fun REFL tm = refl_nocheck (type_of tm) tm;


(*---------------------------------------------------------------------------*
 *                                                                           *
 *         ------------------------  BETA_CONV "(\v.M) N"                    *
 *         |- (\v.M) N = M [v|->N]                                           *
 *---------------------------------------------------------------------------*)

fun BETA_CONV tm =
   let val thm = make_thm Count.Beta
      (empty_tag, empty_hyp, mk_eq_nocheck (type_of tm) tm (beta_conv tm))
   in record_step ("BETA_CONV " ^ its (iT tm)) []; thm end
   handle HOL_ERR _ => ERR "BETA_CONV" "not a beta-redex"


(*---------------------------------------------------------------------------
 * ltheta is a substitution mapping from the template to the concl of
 * the given theorem. It checks that the template is an OK abstraction of
 * the given theorem. rtheta maps the template to another theorem, in which
 * the lhs in the first theorem have been replaced by the rhs in the second
 * theorem. The replacements provide the lhs and rhs.
 *---------------------------------------------------------------------------*)

fun SUBST replacements template (th as THM(O,asl,c,_)) =
 let val fvs = Term.FVL [template] Term.empty_varset
     val (ltheta, rtheta, hyps, oracles) =
         itlist (fn {redex, residue = THM(ocls,h,c',_)} =>
                 fn (tuple as (ltheta,rtheta,hyps,Ocls)) =>
                    if HOLset.member(fvs,redex)
                     then let val (lhs,rhs,_) = Term.dest_eq_ty c'
                          in ((redex |-> lhs)::ltheta,
                              (redex |-> rhs)::rtheta,
                              union_hyp h hyps,
                             Tag.merge ocls Ocls)
                          end
                     else tuple)
                replacements ([],[],asl,O)
 in
   if aconv (subst ltheta template) c
    then let val result = make_thm Count.Subst (oracles,hyps,subst rtheta template)
             val n = length replacements
             val var_ids = String.concatWith " " (map (its o iT o #redex) replacements)
             val tmpl_id = its (iT template)
             val parent_thms = map #residue replacements @ [th]
         in record_step ("SUBST " ^ its n ^ " " ^ var_ids ^ " " ^ tmpl_id) parent_thms;
            result end
      else th
 end;

(*---------------------------------------------------------------------------*
 *        A |- t1 = t2                                                       *
 *   ------------------------  ABS x            [Where x is not free in A]   *
 *    A |- (\x.t1) = (\x.t2)                                                 *
 *---------------------------------------------------------------------------*)

fun ABS v (th as THM(ocl,asl,c,_)) =
 let val (lhs,rhs,ty) = Term.dest_eq_ty c handle HOL_ERR _
                      => ERR "ABS" "not an equality"
     val vty = snd(dest_var v) handle HOL_ERR _
                      => ERR "ABS" "first argument is not a variable"
 in if var_occursl v asl
     then ERR "ABS" "The variable is free in the assumptions"
     else let val result = make_thm Count.Abs
            (ocl, asl, mk_eq_nocheck (vty --> ty)
                                     (mk_abs(v,lhs))
                                     (mk_abs(v,rhs)))
          in record_step ("ABS " ^ its (iT v)) [th]; result end
 end;

(*---------------------------------------------------------------------------*
 *   A |- t1 = t2                                                            *
 *  ------------------------------------  GEN_ABS f [v1,...,vn]              *
 *   A |- (Q v1...vn.t1) = (Q v1...vn.t2)    (where no vi is free in A)      *
 *---------------------------------------------------------------------------*)

fun GEN_ABS opt vlist (th as THM(ocl,asl,c,_)) =
 let open HOLset
     val vset = addList(Term.empty_varset,vlist)
     val hset = hyp_frees th
 in if isEmpty (intersection(vset,hset))
    then let val (lhs,rhs,ty) = with_exn Term.dest_eq_ty c
                                  (thm_err "GEN_ABS" "not an equality")
             val lhs' = list_mk_binder opt (vlist,lhs)
             val rhs' = list_mk_binder opt (vlist,rhs)
         in let val result = make_thm Count.GenAbs
               (ocl,asl,mk_eq_nocheck (Term.type_of lhs') lhs' rhs')
                val opt_id = case opt of SOME t => its (iT t) | NONE => "~"
                val v_ids = String.concatWith " " (map (its o iT) vlist)
            in record_step ("GEN_ABS " ^ opt_id ^ " " ^ its (length vlist) ^ " " ^ v_ids) [th]; result end
         end
    else ERR "GEN_ABS" "variable(s) free in the assumptions"
 end

(*---------------------------------------------------------------------------
 *         A |- M
 *  --------------------  INST_TYPE theta
 *  theta(A) |- theta(M)
 *
 *---------------------------------------------------------------------------*)

fun INST_TYPE [] th = th
  | INST_TYPE theta (th as THM(ocl,asl,c,_)) =
     let val result = make_thm Count.InstType(ocl, hypset_map (inst theta) asl, inst theta c)
         val n = length theta
         val pairs = String.concatWith " "
           (List.concat (map (fn {redex,residue} =>
              [its (iY redex), its (iY residue)]) theta))
     in record_step ("INST_TYPE " ^ its n ^ " " ^ pairs) [th]; result end

(*---------------------------------------------------------------------------
 *          A |- M
 *  ---------------------- DISCH tm
 *     A - tm |- tm ==> M
 *
 * The term tm need not occur in A. All terms in A that are
 * alpha-convertible to tm are removed.
 *---------------------------------------------------------------------------*)

fun DISCH w (th as THM(ocl,asl,c,_)) =
  (Assert (is_bool w) "DISCH" "not a proposition";
   let val result = make_thm Count.Disch
      (ocl,
       HOLset.delete(asl, w) handle HOLset.NotFound => asl,
       Term.prim_mk_imp w c)
   in record_step ("DISCH " ^ its (iT w)) [th]; result end);


(*---------------------------------------------------------------------------
 *          A |- M ==> N ,  B |- M'
 *  ----------------------------------  MP
 *              A u B |- N
 *
 * M and M' must be alpha-convertible
 *---------------------------------------------------------------------------*)

fun MP (th1 as THM(o1,asl1,c1,_)) (th2 as THM(o2,asl2,c2,_)) =
 let val (ant,conseq) = dest_imp c1
 in Assert (aconv ant c2) "MP"
      "antecedent of first thm not alpha-convertible to concl. of second";
    let val result = make_thm Count.Mp (Tag.merge o1 o2, union_hyp asl1 asl2, conseq)
    in record_step "MP" [th1, th2]; result end
 end;


(*---------------------------------------------------------------------------*
 * Derived Rules -- these are here for efficiency purposes, and so that all  *
 * invocations of mk_thm are in Thm. The following derived rules do not use  *
 * any axioms of boolTheory:                                                 *
 *                                                                           *
 *   ALPHA, SYM, TRANS, MK_COMB, AP_TERM, AP_THM, EQ_MP, EQ_IMP_RULE,        *
 *   Beta, Mk_comb, Mk_abs                                                   *
 *                                                                           *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * Equivalence of alpha-convertible terms
 *
 *     t1, t2 alpha-convertable
 *     -------------------------
 *            |- t1 = t2
 *
 * fun ALPHA t1 t2 = TRANS (REFL t1) (REFL t2)
 *---------------------------------------------------------------------------*)

fun ALPHA t1 t2 =
   if aconv t1 t2 then
     let val thm = make_thm Count.Alpha (empty_tag, empty_hyp,
                           mk_eq_nocheck (type_of t1) t1 t2)
     in record_step ("ALPHA " ^ its (iT t1) ^ " " ^ its (iT t2)) []; thm end
   else ERR "ALPHA" "Terms not alpha-convertible";

(*---------------------------------------------------------------------------*
 *  Symmetry of =
 *
 *       A |- t1 = t2
 *     ----------------
 *       A |- t2 = t1
 *
 * fun SYM th =
 *   let val (t1,t2) = dest_eq(concl th)
 *       val v = genvar(type_of t1)
 *   in
 *   SUBST [(th,v)] (mk_eq(v,t1)) (REFL t1)
 *   end
 *   handle _ =>  ERR "SYM" "";
 *---------------------------------------------------------------------------*)

fun SYM th =
 let val (lhs,rhs,ty) = Term.dest_eq_ty (concl th)
     val result = make_thm Count.Sym (tag th, hypset th, mk_eq_nocheck ty rhs lhs)
 in record_step "SYM" [th]; result end
 handle HOL_ERR _ => ERR "SYM" "";

(*---------------------------------------------------------------------------
 * Transitivity of =
 *
 *   A1 |- t1 = t2  ,  A2 |- t2 = t3
 *  ---------------------------------
 *        A1 u A2 |- t1=t3
 *
 * fun TRANS th1 th2 =
 *   let val (t1,t2) = dest_eq(concl th1)
 *       and (t2',t3) = dest_eq(concl th2)
 *       val v = genvar(type_of t1)
 *   in
 *   SUBST [(th2,v)] (mk_eq(t1,v)) th1
 *   end
 *   handle _ =>  ERR{function = "TRANS",message = ""};
 *
 *---------------------------------------------------------------------------*)

fun TRANS th1 th2 =
   let val (lhs1,rhs1,ty) = Term.dest_eq_ty (concl th1)
       and (lhs2,rhs2,_)  = Term.dest_eq_ty (concl th2)
       val   _  = Assert (aconv rhs1 lhs2) "" ""
       val hyps = union_hyp (hypset th1) (hypset th2)
       val ocls = Tag.merge (tag th1) (tag th2)
       val result = make_thm Count.Trans (ocls, hyps, mk_eq_nocheck ty lhs1 rhs2)
   in
     record_step "TRANS" [th1, th2]; result
   end
   handle HOL_ERR _ => ERR "TRANS" "";


(*---------------------------------------------------------------------------
 *     A1 |- f = g    A2 |- x = y
 *     ---------------------------
 *       A1 u A2 |- f x = g y
 *
 * fun MK_COMB (funth,argth) =
 *   let val f = lhs (concl funth)
 *       and x = lhs (concl argth)
 *   in
 *   SUBS_OCCS [([2], funth), ([2], argth)] (REFL (Comb(f,x))))
 *   ? failwith `MK_COMB`;
 *---------------------------------------------------------------------------*)

fun MK_COMB (funth,argth) =
   let val (f,g,ty) = Term.dest_eq_ty (concl funth)
       val (x,y,_)  = Term.dest_eq_ty (concl argth)
       val result = make_thm Count.MkComb
         (Tag.merge (tag funth) (tag argth),
          union_hyp (hypset funth) (hypset argth),
          mk_eq_nocheck (rng ty) (mk_comb(f,x)) (mk_comb(g,y)))
   in
     record_step "MK_COMB" [funth, argth]; result
   end
   handle HOL_ERR _ => ERR "MK_COMB" "";

(*---------------------------------------------------------------------------
 * Application of a term to a theorem
 *
 *    A |- t1 = t2
 * ------------------
 *  A |- t t1 = t t2
 *
 * fun AP_TERM tm th =
 *   let val (t1,_) = dest_eq(concl th)
 *       val th1 = REFL (--`^tm ^t1`--)
 *       (* th1 = |- t t1 = t t1 *)
 *       and v  = genvar(type_of t1)
 *   in
 *   SUBST [(th,v)] (--`^tm ^t1 = ^tm ^v`--) th1
 *   end
 *   handle _ =>  ERR{function = "AP_TERM",message = ""};
 *---------------------------------------------------------------------------*)

fun AP_TERM f th =
 let val (lhs,rhs,_) = Term.dest_eq_ty (concl th)
     val result = make_thm Count.ApTerm
       (tag th, hypset th,
        mk_eq_nocheck (rng (type_of f)) (mk_comb(f,lhs)) (mk_comb(f,rhs)))
 in record_step ("AP_TERM " ^ its (iT f)) [th]; result end
 handle HOL_ERR _ => ERR "AP_TERM" "";


(*---------------------------------------------------------------------------
 * Application of a theorem to a term
 *
 *    A |- t1 = t2
 *   ----------------
 *   A |- t1 t = t2 t
 *
 * fun AP_THM th tm =
 *   let val (t1,_) = dest_eq(concl th)
 *       val th1 = REFL (--`^t1 ^tm`--)
 *       (* th1 = |- t1 t = t1 t *)
 *       and v   = genvar(type_of t1)
 *   in
 *   SUBST [(th,v)] (--`^t1 ^tm = ^v ^tm`--) th1
 *   end
 *   handle _ =>  ERR{function = "AP_THM",message = ""};
 *---------------------------------------------------------------------------*)

fun AP_THM th tm =
 let val (lhs,rhs,ty) = Term.dest_eq_ty (concl th)
     val result = make_thm Count.ApThm
       (tag th, hypset th,
        mk_eq_nocheck (rng ty) (mk_comb(lhs,tm)) (mk_comb(rhs,tm)))
 in record_step ("AP_THM " ^ its (iT tm)) [th]; result end
 handle HOL_ERR _ => ERR "AP_THM" "";

(*---------------------------------------------------------------------------
 *  Modus Ponens for =
 *
 *
 *   A1 |- t1 = t2  ,  A2 |- t1
 *  ----------------------------
 *        A1 u A2 |- t2
 *
 * fun EQ_MP th1 th2 =
 *   let val (t1,t2) = dest_eq(concl th1)
 *       val v = genvar(type_of t1)
 *   in  SUBST [(th1,v)] v th2
 *   end handle _ =>  ERR{function = "EQ_MP",message = ""};
 *---------------------------------------------------------------------------*)

fun EQ_MP th1 th2 =
   let val (lhs,rhs,_) = Term.dest_eq_ty (concl th1)
       val _ = Assert (aconv lhs (concl th2)) "" ""
       val result = make_thm Count.EqMp (Tag.merge (tag th1) (tag th2),
                         union_hyp (hypset th1) (hypset th2), rhs)
   in record_step "EQ_MP" [th1, th2]; result end
   handle HOL_ERR _ => ERR "EQ_MP" "";

(*---------------------------------------------------------------------------
 *              A |- t1 = t2
 *    ------------------------------------
 *     A |- t1 ==> t2      A |- t2 ==> t1
 *
 * fun EQ_IMP_RULE th =
 *   let val (t1,t2) = dest_eq(concl th)
 *   in
 *   (DISCH t1 (EQ_MP th (ASSUME t1)),
 *    DISCH t2 (EQ_MP (SYM th)(ASSUME t2)))
 *   end
 *   handle _ =>  ERR{function = "EQ_IMP_RULE",message = ""};
 *---------------------------------------------------------------------------*)

fun EQ_IMP_RULE th =
 let val (lhs,rhs,ty) = Term.dest_eq_ty (concl th)
     and A = hypset th
     and O = tag th
 in if ty = Type.bool
    then let val thm1 = make_thm Count.EqImpRule(O,A, Term.prim_mk_imp lhs rhs)
             val thm2 = make_thm Count.EqImpRule(O,A, Term.prim_mk_imp rhs lhs)
             val _ = record_step "EQ_IMP_RULE1" [th]
             val _ = record_step "EQ_IMP_RULE2" [th]
         in (thm1, thm2) end
    else ERR "" ""
 end
 handle HOL_ERR _ => ERR "EQ_IMP_RULE" "";

(*---------------------------------------------------------------------------
 * Specialization
 *
 *    A |- !(\x.u)
 *  --------------------   (where t is free for x in u)
 *    A |- u[t/x]
 *
 * fun SPEC t th =
 *   let val {Rator=F,Rand=body} = dest_comb(concl th)
 *   in
 *   if (not(#Name(dest_const F)="!"))
 *   then ERR{function = "SPEC",message = ""}
 *   else let val {Bvar=x,Body=u} = dest_abs body
 *        and v1 = genvar(type_of F)
 *        and v2 = genvar(type_of body)
 *        val th1 = SUBST[{var = v1,
 *                         thm = INST_TYPE[{redex   = (==`:'a`==),
 *                                          residue = type_of x}] FORALL_DEF}]
 *                       (--`^v1 ^body`--) th
 *        (* th1 = |- (\P. P = (\x. T))(\x. t1 x) *)
 *        val th2 = BETA_CONV(concl th1)
 *        (* th2 = |- (\P. P = (\x. T))(\x. t1 x) = ((\x. t1 x) = (\x. T)) *)
 *        val th3 = EQ_MP th2 th1
 *        (* th3 = |- (\x. t1 x) = (\x. T) *)
 *        val th4 = SUBST [{var= v2, thm=th3}] (--`^body ^t = ^v2 ^t`--)
 *                        (REFL (--`^body ^t`--))
 *        (* th4 = |- (\x. t1 x)t = (\x. T)t *)
 *        val {lhs=ls,rhs=rs} = dest_eq(concl th4)
 *        val th5 = TRANS(TRANS(SYM(BETA_CONV ls))th4)(BETA_CONV rs)
 *        (* th5 = |- t1 t = T *)
 *        in
 *        EQT_ELIM th5
 *        end
 *   end
 *   handle _ => ERR{function = "SPEC",message = ""};
 *
 *
 * pre-dB manner:
 * fun SPEC t th =
 *   let val {Bvar,Body} = dest_forall(concl th)
 *   in
 *   make_thm Count.(hypset th, subst[{redex = Bvar, residue = t}] Body)
 *   end
 *   handle _ => ERR{function = "SPEC",message = ""};
 *---------------------------------------------------------------------------*)

fun SPEC t th =
 let val (Rator,Rand) = dest_comb(concl th)
     val {Thy,Name,...} = dest_thy_const Rator
 in
   Assert (Name="!" andalso Thy="bool")
          "SPEC" "Theorem not universally quantified";
   let val result = make_thm Count.Spec
       (tag th, hypset th, beta_conv(mk_comb(Rand, t)))
   in record_step ("SPEC " ^ its (iT t)) [th]; result end
       handle HOL_ERR _ =>
              raise thm_err "SPEC"
                    "Term argument's type not equal to bound variable's"
 end;


(*---------------------------------------------------------------------------
 * Generalization
 *
 *         A |- t
 *   -------------------   (where x not free in A)
 *       A |- !(\x.t)
 *
 * fun GEN x th =
 *   let val th1 = ABS x (EQT_INTRO th)
 *     (* th1 = |- (\x. t1 x) = (\x. T)  --ABS does not behave this way --KLS*)
 *      val abs = `\^x. ^(concl th)`
 *      and v1 = genvar `:(^(type_of x) -> bool) -> bool`
 *      and v2 = genvar `:bool`
 *      val th2 = SUBST [(INST_TYPE[(type_of x, `:'a`)]FORALL_DEF,v1)]
 *                      `($! ^abs) = (^v1 ^abs)`
 *                      (REFL `$! ^abs`)
 *      (* th2 = |- (!x. t1 x) = (\P. P = (\x. T))(\x. t1 x) *)
 *      val th3 = TRANS th2 (BETA_CONV(snd(dest_eq(concl th2))))
 *      (* th3 = |- (!x. t1 x) = ((\x. t1 x) = (\x. T)) *)
 *      in
 *      SUBST [(SYM th3, v2)] v2 th1
 *      end
 *      handle _ => ERR{function = "GEN",message = ""};
 *---------------------------------------------------------------------------*)


fun GEN x th =
  let val (asl,c) = sdest_thm th
  in if var_occursl x asl
     then ERR  "GEN" "variable occurs free in hypotheses"
     else let val result = make_thm Count.Gen(tag th, asl, Susp.force mk_forall x c)
          in record_step ("GEN " ^ its (iT x)) [th]; result end
          handle HOL_ERR _ => ERR "GEN" ""
  end;

fun GENL vs th = let
  val (asl,c) = sdest_thm th
in
  if exists (fn v => var_occursl v asl) vs then
    ERR "GENL" "variable occurs free in hypotheses"
  else let
    val result = make_thm
      Count.Gen(tag th, asl,
                list_mk_binder (SOME (prim_mk_const {Thy="bool", Name="!"}))
                               (vs,c))
    val v_ids = String.concatWith " " (map (its o iT) vs)
  in record_step ("GENL " ^ its (length vs) ^ " " ^ v_ids) [th]; result end
    handle HOL_ERR _ => ERR "GENL" ""
end



(*---------------------------------------------------------------------------
 * Existential introduction
 *
 *    A |- t[t']
 *  --------------  EXISTS ("?x.t[x]", "t'")  ( |- t[t'] )
 *   A |- ?x.t[x]
 *
 *
 *
 * fun EXISTS (fm,tm) th =
 *   let val (x,t) = dest_exists fm
 *       val th1 = BETA_CONV `(\(^x). ^t) ^tm`
 *       (* th1 = |- (\x. t x)t' = t t' *)
 *       val th2 = EQ_MP (SYM th1) th
 *       (* th2 = |- (\x. t x)t' *)
 *       val th3 = SELECT_INTRO th2
 *       (* th3 = |- (\x. t x)(@x. t x) *)
 *       val th4 = AP_THM(INST_TYPE[(type_of x, `:'a`)]EXISTS_DEF) `\(^x).^t`
 *       (* th4 = |- (?x. t x) = (\P. P($@ P))(\x. t x) *)
 *       val th5 = TRANS th4 (BETA_CONV(snd(dest_eq(concl th4))))
 *       (* th5 = |- (?x. t x) = (\x. t x)(@x. t x) *)
 *   in
 *   EQ_MP (SYM th5) th3
 *   end
 *   handle _ => ERR{function = "EXISTS",message = ""};
 *
 *---------------------------------------------------------------------------*)

local
  val mesg1 = "First argument not of form `?x. P`"
  val mesg2 = "(2nd argument)/(bound var) in body of 1st argument is not theorem's conclusion"
  val err = thm_err "EXISTS" mesg1
in
fun EXISTS (w,t) th =
 let val (ex,Rand) = with_exn dest_comb w err
     val {Name,Thy,...}  = with_exn dest_thy_const ex err
     val _ = Assert ("?"=Name andalso Thy="bool") "EXISTS" mesg1
     val _ = Assert (aconv (beta_conv(mk_comb(Rand,t))) (concl th))
                    "EXISTS" mesg2
   in let val result = make_thm Count.Exists (tag th, hypset th, w)
      in record_step ("EXISTS " ^ its (iT w) ^ " " ^ its (iT t)) [th]; result end
   end
end;

(*---------------------------------------------------------------------------
 * Existential elimination
 *
 *   A1 |- ?x.t[x]   ,   A2, "t[v]" |- t'
 *   ------------------------------------     (variable v occurs nowhere)
 *            A1 u A2 |- t'
 *
 * fun CHOOSE (v,th1) th2 =
 *   let val (x,body) = dest_exists(concl th1)
 *       and t'     = concl th2
 *       and v1     = genvar `:bool`
 *       val th3 = AP_THM(INST_TYPE[(type_of v, `:'a`)]EXISTS_DEF)`\(^x).^body`
 *       (* th3 = |- (?x. t x) = (\P. P($@ P))(\x. t x) *)
 *       val th4 = EQ_MP th3 th1
 *       (* th4 = |- (\P. P($@ P))(\x. t x) *)
 *       val th5 = EQ_MP (BETA_CONV(concl th4)) th4
 *       (* th5 = |- (\x. t x)(@x. t x) *)
 *       val th6 = BETA_CONV `(\(^x).^body)^v`
 *       (* th6 = |- (\x. t x)v = t v *)
 *       val Pa = snd(dest_eq(concl th6))
 *       val th7 = UNDISCH(SUBST [(SYM th6,v1)] `^v1 ==> ^t'` (DISCH Pa th2))
 *       (* th7 = |- t' *)
 *   in
 *   SELECT_ELIM th5 (v,th7)
 *   end
 *   handle _ => ERR{function = "CHOOSE",message = ""};
 *---------------------------------------------------------------------------*)

fun disch(w,wl) = HOLset.delete(wl,w) handle HOLset.NotFound => wl

fun CHOOSE (v,xth) bth =
  let val (x_asl, x_c) = sdest_thm xth
      val (b_asl, b_c) = sdest_thm bth
      val (Bvar,Body)  = dest_exists x_c
      val A2_hyps = disch (subst [Bvar |-> v] Body, b_asl)
      val newhyps = union_hyp x_asl A2_hyps
      val occursv = var_occurs v
      val _ = Assert (not(occursv x_c) andalso
                      not(occursv b_c) andalso
                      not(hypset_exists occursv A2_hyps)) "" ""
    (* Need not check for occurrence of v in A1: one can imagine
       implementing a derived rule on top of a more restrictive one that
       instantiated the occurrence of v in A1 to something else, applied
       the restrictive rule, and then instantiated it back again.

       Credit for pointing out this optimisation to Jim Grundy and
       Tom Melham. *)
  in let val result = make_thm Count.Choose
           (Tag.merge (tag xth) (tag bth), newhyps, b_c)
     in record_step ("CHOOSE " ^ its (iT v)) [xth, bth]; result end
  end
  handle HOL_ERR _ => ERR "CHOOSE" "";


(*---------------------------------------------------------------------------
 * Conjunction introduction rule
 *
 *   A1 |- t1  ,  A2 |- t2
 *  -----------------------
 *    A1 u A2 |- t1 /\ t2
 *
 * fun CONJ th1 th2 = MP (MP (SPEC (concl th2)
 *                             (SPEC (concl th1) AND_INTRO_THM))
 *                          th1)
 *                      th2;
 *---------------------------------------------------------------------------*)

fun CONJ th1 th2 =
   let val result = make_thm Count.Conj
        (Tag.merge (tag th1) (tag th2),
         union_hyp (hypset th1) (hypset th2),
         Susp.force mk_conj(concl th1, concl th2))
   in record_step "CONJ" [th1, th2]; result end
   handle HOL_ERR _ => ERR "CONJ" "";


(*---------------------------------------------------------------------------
 * Left conjunct extraction
 *
 *   A |- t1 /\ t2
 *   -------------
 *      A |- t1
 *
 * fun CONJUNCT1 th =
 *   let val (t1,t2) = dest_conj(concl th)
 *   in
 *   MP (SPEC t2 (SPEC t1 AND1_THM)) th
 *   end
 *   handle _ => ERR{function = "CONJUNCT1",message = ""};
 *
 *---------------------------------------------------------------------------*)

fun conj1 tm =
  let val (c,M) = dest_comb (rator tm)
      val {Name,Thy,...} = dest_thy_const c
  in
    if Name="/\\" andalso Thy="bool" then M else ERR "" ""
  end


fun CONJUNCT1 th =
  let val result = make_thm Count.Conjunct1 (tag th, hypset th, conj1 (concl th))
  in record_step "CONJUNCT1" [th]; result end
  handle HOL_ERR _ => ERR "CONJUNCT1" "";


(*---------------------------------------------------------------------------
 *  Right conjunct extraction
 *
 *   A |- t1 /\ t2
 *   -------------
 *      A |- t2
 *
 * fun CONJUNCT2 th =
 *   let val (t1,t2) = dest_conj(concl th)
 *   in
 *   MP (SPEC t2 (SPEC t1 AND2_THM)) th
 *   end
 *   handle _ => ERR{function = "CONJUNCT2",message = ""};
 *---------------------------------------------------------------------------*)

fun conj2 tm =
  let val (Rator,M) = dest_comb tm
      val {Name,Thy,...} = dest_thy_const (rator Rator)
  in
     if Name="/\\" andalso Thy="bool" then M else ERR "" ""
  end

fun CONJUNCT2 th =
 let val result = make_thm Count.Conjunct2 (tag th, hypset th, conj2 (concl th))
 in record_step "CONJUNCT2" [th]; result end
  handle HOL_ERR _ => ERR "CONJUNCT2" "";


(*---------------------------------------------------------------------------
 * Left disjunction introduction
 *
 *      A |- t1
 *  ---------------
 *   A |- t1 \/ t2
 *
 * fun DISJ1 th t2 = MP (SPEC t2 (SPEC (concl th) OR_INTRO_THM1)) th
 *           handle _ => ERR{function = "DISJ1",message = ""};
 *---------------------------------------------------------------------------*)

fun DISJ1 th w =
 let val result = make_thm Count.Disj1
   (tag th, hypset th, Susp.force mk_disj (concl th, w))
 in record_step ("DISJ1 " ^ its (iT w)) [th]; result end
 handle HOL_ERR _ => ERR "DISJ1" "";


(*---------------------------------------------------------------------------
 * Right disjunction introduction
 *
 *      A |- t2
 *  ---------------
 *   A |- t1 \/ t2
 *
 * fun DISJ2 t1 th = MP (SPEC (concl th) (SPEC t1 OR_INTRO_THM2)) th
 *          handle _ => ERR{function = "DISJ2",message = ""};
 *---------------------------------------------------------------------------*)

fun DISJ2 w th =
 let val result = make_thm Count.Disj2
   (tag th, hypset th, Susp.force mk_disj(w,concl th))
 in record_step ("DISJ2 " ^ its (iT w)) [th]; result end
 handle HOL_ERR _ => ERR "DISJ2" "";


(*---------------------------------------------------------------------------
 * Disjunction elimination
 *
 *   A |- t1 \/ t2   ,   A1,t1 |- t   ,   A2,t2 |- t
 *   -----------------------------------------------
 *               A u A1 u A2 |- t
 *
 * fun DISJ_CASES th1 th2 th3 =
 *   let val (t1,t2) = dest_disj(concl th1)
 *       and t = concl th2
 *       val th4 = SPEC t2 (SPEC t1 (SPEC t OR_ELIM_THM))
 *   in
 *   MP (MP (MP th4 th1) (DISCH t1 th2)) (DISCH t2 th3)
 *   end
 *   handle _ => ERR{function = "DISJ_CASES",message = ""};
 *---------------------------------------------------------------------------*)

fun dest_disj tm =
  let val (Rator,N) = dest_comb tm
      val (c,M)     = dest_comb Rator
      val {Name,Thy,...}   = dest_thy_const c
  in
    if Name="\\/" andalso Thy="bool" then (M,N) else ERR "" ""
  end


fun DISJ_CASES dth ath bth =
  let val _ = Assert (aconv (concl ath) (concl bth)) "" ""
      val (disj1,disj2) = dest_disj (concl dth)
      val result = make_thm Count.DisjCases
       (itlist Tag.merge [tag dth, tag ath, tag bth] empty_tag,
        union_hyp (hypset dth) (union_hyp (disch(disj1, hypset ath))
                                       (disch(disj2, hypset bth))),
        concl ath)
  in
   record_step "DISJ_CASES" [dth, ath, bth]; result
  end
  handle HOL_ERR _ => ERR "DISJ_CASES" "";


(*---------------------------------------------------------------------------
 * NOT introduction
 *
 *     A |- t ==> F
 *     ------------
 *       A |- ~t
 *
 * fun NOT_INTRO th =
 *   let val (t,_) = dest_imp(concl th)
 *   in MP (SPEC t IMP_F) th
 *   end
 *   handle _ => ERR{function = "NOT_INTRO",message = ""};
 *---------------------------------------------------------------------------*)

fun NOT_INTRO th =
  let val (ant,c) = dest_imp(concl th)
  in Assert (c = Susp.force F) "" "";
     let val result = make_thm Count.NotIntro (tag th, hypset th, Susp.force mk_neg ant)
     in record_step "NOT_INTRO" [th]; result end
  end
  handle HOL_ERR _ => ERR "NOT_INTRO" "";


(*---------------------------------------------------------------------------
 * Negation elimination
 *
 *       A |- ~ t
 *     --------------
 *      A |- t ==> F
 *
 * fun NOT_ELIM th =
 *   let val (_,t) = dest_comb(concl th)
 *   in MP (SPEC t F_IMP) th
 *   end
 *   handle _ => ERR{function = "NOT_ELIM",message = ""};
 *---------------------------------------------------------------------------*)

local fun dest M =
        let val (Rator,Rand)  = dest_comb M
        in (dest_thy_const Rator, Rand)
        end
in
fun NOT_ELIM th =
  case with_exn dest (concl th) (thm_err "NOT_ELIM" "")
   of ({Name="~", Thy="bool",...},Rand)
       => let val result = make_thm Count.NotElim
             (tag th, hypset th, Term.prim_mk_imp Rand (Susp.force F))
          in record_step "NOT_ELIM" [th]; result end
    | otherwise => ERR "NOT_ELIM" ""
end;


(*---------------------------------------------------------------------------*
 * Classical contradiction rule                                              *
 *                                                                           *
 *   A,"~t" |- F                                                             *
 *   --------------                                                          *
 *       A |- t                                                              *
 *                                                                           *
 * fun CCONTR t th =                                                         *
 * let val th1 = RIGHT_BETA(AP_THM NOT_DEF t)                                *
 *     and v   = genvar (--`:bool`--)                                        *
 *     val th2 = EQT_ELIM (ASSUME (--`^t = T`--))                            *
 *     val th3 = SUBST [(th1,v)] (--`^v ==> F`--) (DISCH (--`~ ^t`--) th)    *
 *     val th4 = SUBST[(ASSUME(--`^t = F`--),v)] (--`(^v ==>F)==>F`--)th3    *
 *     val th5 = MP th4 (EQT_ELIM (CONJUNCT2 IMP_CLAUSE4))                   *
 *     val th6 = EQ_MP (SYM(ASSUME (--`^t = F`--))) th5                      *
 * in                                                                        *
 * DISJ_CASES (SPEC t BOOL_CASES_AX) th2 th6                                 *
 * end handle _ => ERR{function = "CCONTR",message = ""}                     *
 *---------------------------------------------------------------------------*)

fun CCONTR w fth =
  (Assert (concl fth = Susp.force F) "CCONTR" "";
   let val result = make_thm Count.Ccontr
       (tag fth, disch(Susp.force mk_neg w, hypset fth), w)
   in record_step ("CCONTR " ^ its (iT w)) [fth]; result end
     handle HOL_ERR _ => ERR "CCONTR" "");


(*---------------------------------------------------------------------------*
 * Instantiate free variables in a theorem                                   *
 *---------------------------------------------------------------------------*)

fun INST [] th = th
  | INST theta th =
      if List.all (is_var o #redex) theta then
        let
          val substf = subst theta
          val result = make_thm Count.Inst
            (tag th, hypset_map substf (hypset th), substf (concl th))
          val n = length theta
          val pairs = String.concatWith " "
            (List.concat (map (fn {redex,residue} =>
               [its (iT redex), its (iT residue)]) theta))
        in record_step ("INST " ^ its n ^ " " ^ pairs) [th]; result end
      else
        raise ERR "INST" "can only instantiate variables"

(*---------------------------------------------------------------------------*
 * Now some derived rules optimized for computations, avoiding most          *
 * of useless type-checking, using pointer equality and delayed              *
 * substitutions. See computeLib for further details.                        *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*
 *    A |- t = (\x.m) n                                                      *
 *  --------------------- Beta                                               *
 *     A |- t = m{x\n}                                                       *
 *                                                                           *
 * Other implementation (less efficient not using explicit subst.):          *
 *   val Beta = Drule.RIGHT_BETA                                             *
 *---------------------------------------------------------------------------*)

fun Beta th =
   let val (lhs, rhs, ty) = Term.dest_eq_ty (concl th)
       val result = make_thm Count.Beta
        (tag th, hypset th, mk_eq_nocheck ty lhs (Term.lazy_beta_conv rhs))
   in record_step "Beta" [th]; result end
   handle HOL_ERR _ => ERR "Beta" "";


(* --------------------------------------------------------------------------
    This rule behaves like a tactic: given a goal (reducing the rhs of thm),
    it returns two subgoals (reducing the rhs of th1 and th2), together
    with a validation (mkthm), that builds the normal form of t from the
    normal forms of u and v.
    NB:
     1. we do not have to typecheck the rator u,
     2. there used to just be a pointer equality check in the Assert lines,
        but this may cause unintended failures as gc-movement of values may
        make things that are "morally" pointer-equal not compare equal.

        The aconv test uses a pointer equality test as a fast-path option, so
        this should still be quick most of the time.

                        |- u = u    (th1)        |- v = v    (th2)
          (thm)             ...                     ...
       A |- t = u v    A' |- u = u' (th1')     A'' |- v = v' (th2')
     ----------------------------------------------------------------
                   A u A' u A'' |- t = u' v'

    Could be implemented outside Thm as:
      fun Mk_comb th =
        let val {Rator,Rand} = dest_comb(rhs (concl th))
            fun mka th1 th2 = TRANS th (MK_COMB(th1,th2)) in
        (REFL Rator, REFL Rand, mka)
        end
  --------------------------------------------------------------------------- *)

fun Mk_comb thm =
   let val (lhs, rhs, ty) = Term.dest_eq_ty (concl thm)
       val (Rator,Rand) = dest_comb rhs
       fun mkthm th1' th2' =
         let val (lhs1, rhs1, _) = Term.dest_eq_ty (concl th1')
             val _ = Assert (aconv lhs1 Rator) "" ""
             val (lhs2, rhs2, _) = Term.dest_eq_ty (concl th2')
             val _ = Assert (aconv lhs2 Rand) "" ""
             val (ocls,hyps) = tag_hyp_union [thm, th1', th2']
             val result = make_thm Count.MkComb
               (ocls, hyps,mk_eq_nocheck ty lhs (mk_comb(rhs1,rhs2)))
         in record_step "Mk_comb" [thm, th1', th2']; result end
         handle HOL_ERR _ => ERR "Mk_comb" "";
       val aty = type_of Rand    (* typing! *)
       val th1 = refl_nocheck (aty --> ty) Rator
       val th2 = refl_nocheck aty Rand
   in (th1,th2,mkthm)
   end
   handle HOL_ERR _ => ERR "Mk_comb" "";

(* --------------------------------------------------------------------------
                         |- u = u    (th1)
          (thm)              ...
       A |- t = \x.u    A' |- u = u' (th1')
     ---------------------------------------- x not in FV(A')
               A u A' |- t = \x.u'

    Could be implemented outside Thm as:
      fun Mk_abs th =
        let val {Bvar,Body} = dest_abs(rhs (concl th)) in
        (Bvar, REFL Body, (fn th1 => TRANS th (ABS Bvar th1)))
        end

    See comment accompanying Mk_comb for discussion of use of aconv in first
    Assert.
   -------------------------------------------------------------------------- *)

fun Mk_abs thm =
   let val (lhs, rhs, ty) = Term.dest_eq_ty (concl thm)
       val (Bvar,Body) = dest_abs rhs
       fun mkthm th1' =
         let val (lhs1, rhs1, _) = Term.dest_eq_ty (concl th1')
             val _ = Assert (aconv lhs1 Body) "" ""
             val _ = Assert (not (var_occursl Bvar (hypset th1'))) "" ""
             val (ocls,hyps) = tag_hyp_union [thm, th1']
             val result = make_thm Count.Abs
               (ocls, hyps, mk_eq_nocheck ty lhs (mk_abs(Bvar, rhs1)))
         in record_step ("Mk_abs " ^ its (iT Bvar)) [thm, th1']; result end
         handle HOL_ERR _ => ERR "Mk_abs" ""
       val th1 = refl_nocheck (rng ty) Body
   in (Bvar,th1,mkthm)
   end
   handle HOL_ERR _ => ERR "Mk_abs" "";

(*---------------------------------------------------------------------------*
 * Same as SPEC, but without propagating the substitution.  Spec = SPEC.     *
 *---------------------------------------------------------------------------*)

fun Specialize t th =
   let val (Rator,Rand) = dest_comb(concl th)
       val {Name,Thy,...} = dest_thy_const Rator
   in
     Assert (Thy="bool" andalso Name="!") "" "";
     let val result = make_thm Count.Spec
        (tag th, hypset th, Term.lazy_beta_conv(mk_comb(Rand,t)))
     in record_step ("Specialize " ^ its (iT t)) [th]; result end
   end
   handle HOL_ERR _ => ERR "Specialize" "";

(*---------------------------------------------------------------------------*
 * Construct a theorem directly and attach the given tag to it.              *
 *---------------------------------------------------------------------------*)

fun mk_oracle_thm tg (asl,c) =
  (Assert (Lib.all is_bool (c::asl)) "mk_oracle_thm"  "not a proposition"
   ; Assert (tg <> "DISK_THM") "mk_oracle_thm"  "invalid user tag"
   ; let val result = make_thm Count.Oracle (Tag.read tg,list_hyp asl,c)
     in record_step ("ORACLE " ^ tg ^ " " ^ fmt_thm_stmt result) [];
        result end);


val mk_thm = mk_oracle_thm "MK_THM"

fun add_tag (tag1, THM(tag2, h, c, id)) = THM(Tag.merge tag1 tag2, h, c, id)

(*---------------------------------------------------------------------------*
 *    The following two are only used internally
 *---------------------------------------------------------------------------*)

fun mk_axiom_thm (r,c) =
   (Assert (type_of c = bool) "mk_axiom_thm"  "Not a proposition!";
    let val result = make_thm Count.Axiom (Tag.ax_tag r, empty_hyp, c)
    in record_step ("AXIOM " ^ its (iT c)) []; result end)

fun mk_defn_thm (witness_tag, c) =
   (Assert (type_of c = bool) "mk_defn_thm"  "Not a proposition!";
    make_thm Count.Definition (witness_tag,empty_hyp,c))

(* ----------------------------------------------------------------------
    Primitive Definition Principles
   ---------------------------------------------------------------------- *)

val ERR = mk_HOL_ERR "Thm"
val TYDEF_ERR = ERR "prim_type_definition"
val DEF_ERR   = ERR "new_definition"
val SPEC_ERR  = ERR "new_specification"

val TYDEF_FORM_ERR = TYDEF_ERR "expected a theorem of the form \"?x. P x\""
val DEF_FORM_ERR   = DEF_ERR   "expected a term of the form \"v = M\""

(* some simple term manipulation functions *)
fun mk_exists (absrec as (Bvar,_)) =
  mk_comb(mk_thy_const{Name="?",Thy="bool", Ty= (type_of Bvar-->bool)-->bool},
          mk_abs absrec)

fun dest_eq M =
  let val (Rator,r) = dest_comb M
      val (eq,l) = dest_comb Rator
  in case dest_thy_const eq
      of {Name="=",Thy="min",...} => (l,r)
       | _ => raise ERR "dest_eq" "not an equality"
  end;

fun mk_eq (lhs,rhs) =
 let val ty = type_of lhs
     val eq = mk_thy_const{Name="=",Thy="min",Ty=ty-->ty-->bool}
 in list_mk_comb(eq,[lhs,rhs])
 end;

fun nstrip_exists 0 t = ([],t)
  | nstrip_exists n t =
     let val (Bvar, Body) = dest_exists t
         val (l,t'') = nstrip_exists (n-1) Body
     in (Bvar::l, t'')
     end;

(* standard checks *)
fun check_null_hyp th f =
  if null(hyp th) then ()
  else raise f "theorem must have no assumptions";

fun check_free_vars tm f =
  case free_vars tm
   of [] => ()
    | V  => raise f (String.concat
            ("Free variables in rhs of definition: "
             :: commafy (map (Lib.quote o fst o dest_var) V)));

fun check_vars tm vars f =
 case Lib.set_diff (free_vars tm) vars
  of [] => ()
   | extras =>
      raise f (String.concat
         ("Unbound variable(s) in definition: "
           :: commafy (map (Lib.quote o fst o dest_var) extras)));

fun check_tyvars body_tyvars ty f =
 case Lib.set_diff body_tyvars (Type.type_vars ty)
  of [] => ()
   | extras =>
      raise f (String.concat
         ("Unbound type variable(s) in definition: "
           :: commafy (map (Lib.quote o Type.dest_vartype) extras)));

fun okConstName cnm =
    CharVector.all (fn c => Char.isGraph c) cnm

fun prim_type_definition (name as {Thy, Tyop}, thm) = let
  val (bv,Body) = with_exn dest_exists (concl thm) TYDEF_FORM_ERR
  val (P,v)     = with_exn dest_comb Body TYDEF_FORM_ERR
  val _         = assert_exn (equal bv) v TYDEF_FORM_ERR
  val Pty       = type_of P
  val (dom,rng) = with_exn Type.dom_rng Pty TYDEF_FORM_ERR
  val tyvars    = Listsort.sort Type.compare (type_vars_in_term P)
  val checked   = check_null_hyp thm TYDEF_ERR
  val checked   =
      assert_exn null (free_vars P)
                 (TYDEF_ERR "subset predicate must be a closed term")
  val checked   = assert_exn okConstName Tyop
                             (TYDEF_ERR ("Type operator name: \"" ^ Tyop ^
                                         "\" invalid"))
  val checked   = assert_exn (op=) (rng,bool)
                             (TYDEF_ERR "subset predicate has the wrong type")
  val   _       = Type.prim_new_type name (List.length tyvars)
  val newty     = Type.mk_thy_type{Tyop=Tyop,Thy=Thy,Args=tyvars}
  val repty     = newty --> dom
  val rep       = mk_primed_var("rep", repty)
  val TYDEF     = mk_thy_const{Name="TYPE_DEFINITION", Thy="bool",
                               Ty = Pty --> (repty-->bool)}
in
  let val result = mk_defn_thm(tag thm, mk_exists(rep, list_mk_comb(TYDEF,[P,rep])))
  in record_step ("DEF_TYOP " ^ Thy ^ " " ^ Tyop ^ " " ^
                  its (iT (concl result))) [thm]; result end
end

(* subsumed by gen_prim_specification
fun prim_constant_definition Thy M = let
  val (lhs, rhs) = with_exn dest_eq M DEF_FORM_ERR
  val {Name, Thy, Ty} =
      if is_const lhs then let
          val r as {Name, Ty, ...} = dest_thy_const lhs
        in
          {Name = Name, Thy = Thy, Ty = Ty}
        end
      else if is_var lhs then let
          val (n, ty) = dest_var lhs
        in
          {Name = n, Ty = ty, Thy = Thy}
        end
      else raise DEF_FORM_ERR
  val checked = check_free_vars rhs DEF_ERR
  val checked = check_tyvars (type_vars_in_term rhs) Ty DEF_ERR
  val new_lhs = Term.prim_new_const {Name = Name, Thy = Thy} Ty
in
  mk_defn_thm(empty_tag, mk_eq(new_lhs, rhs))
end
*)

fun bind thy s ty =
    Term.prim_new_const {Name = s, Thy = thy} ty

fun prim_specification thyname cnames th = let
  val con       = concl th
  val checked   = check_null_hyp th SPEC_ERR
  val checked   = check_free_vars con SPEC_ERR
  val checked   =
      assert_exn (op=) (length(mk_set cnames),length cnames)
                 (SPEC_ERR "duplicate constant names in specification")
  val checked   =
      case List.find (not o okConstName) cnames of
          NONE => ()
        | SOME n => raise SPEC_ERR ("Constant name: \""^n^"\" invalid")
  val (V,body)  =
      with_exn (nstrip_exists (length cnames)) con
               (SPEC_ERR "too few existentially quantified variables")
  fun vOK V v   = check_tyvars V (type_of v) SPEC_ERR
  val checked   = List.app (vOK (type_vars_in_term body)) V
  fun addc v s  = v |-> bind thyname s (snd(dest_var v))
in
  let val result = mk_defn_thm (tag th, subst (map2 addc V cnames) body)
  in record_step ("DEF_SPEC " ^ its (iT (concl result))) [th]; result end
end

fun gen_prim_specification thyname th = let
  val hyps        = hypset th
  val stys        =
    let
      fun foldthis (tm,stys) =
        let
          val (l,r)   =
              with_exn dest_eq tm (SPEC_ERR "non-equational hypothesis")
          val (s,ty)  =
              with_exn dest_var l (SPEC_ERR "lhs of hyp not a variable")
          val checked = check_free_vars r SPEC_ERR
          val checked = check_tyvars (type_vars_in_term r) ty SPEC_ERR
        in
          (s,ty)::stys
        end
    in
      HOLset.foldl foldthis [] hyps
    end
  val cnames      = List.map fst stys
  val checked     =
      assert_exn (op=) (length(mk_set cnames),length cnames)
                 (SPEC_ERR "duplicate constant names in specification")
  val checked   =
      case List.find (not o okConstName) cnames of
          NONE => ()
        | SOME n => raise SPEC_ERR ("Constant name: \""^n^"\" invalid")
  val body        = concl th
  val checked     = check_vars body (List.map mk_var stys) SPEC_ERR
  fun addc (s,ty) = (mk_var (s,ty)) |-> bind thyname s ty
in
  let val result = mk_defn_thm (tag th, subst (List.map addc stys) body)
  in record_step ("DEF_SPEC " ^ its (iT (concl result))) [th]; (cnames, result) end
end







(* ----------------------------------------------------------------------
    Creating a theorem from disk
   ---------------------------------------------------------------------- *)

fun disk_thm ((d,ocl), termlist) = let
  val c = hd termlist
  val asl = tl termlist
  val result = make_thm Count.Disk (Tag.read_disk_tag (d,ocl),list_hyp asl,c)
in record_step ("DISK_THM " ^ fmt_thm_stmt result) []; result end

(* ----------------------------------------------------------------------
    Saving dependencies of a theorem
   ---------------------------------------------------------------------- *)

(* This reference is automatically reset to 0 each time you create
   a theory. *)
val thm_order = ref 0

fun save_dep thy (th as (THM(t,h,c,sid))) =
  let
    val did = (thy,!thm_order)
    val dl  = (transfer_thydepl o dep_of o tag) th
    val dep = DEP_SAVED(did,dl)
  in
    thm_order := (!thm_order) + 1;
    THM(Tag.set_dep dep t,h,c,sid)
  end

(* ----------------------------------------------------------------------
    Computing with first-order lisp-style values
   ---------------------------------------------------------------------- *)

local
  infix ##;
  fun dest_code_eqn th =
    case total ((List.null ## I) o dest_thm) th of
      SOME (true,tm) => tm
    | _ => raise ERR "compute" "code equation with hypotheses";
  fun safe_mk_eq l r =
    let
      val tyl = type_of l
    in
      if tyl = type_of r then
        Term.prim_mk_eq tyl l r
      else
        raise ERR "compute" "types of lhs and rhs disagree"
    end;
  val merge_tags = foldr (uncurry Tag.merge)
in
  fun compute {cval_terms, cval_type, num_type, char_eqns} =
    let
      val tag0 = merge_tags empty_tag (List.map (tag o snd) char_eqns)
      val char_thms = List.map snd char_eqns
      val char_eqns = List.map (I ## dest_thm) char_eqns
      val _ = List.all (List.null o fst o snd) char_eqns orelse
              raise ERR "compute" "Characteristic equation with hypotheses"
      val tc0 = Compute.term_compute
                 { cval_terms = cval_terms,
                   cval_type = cval_type,
                   num_type = num_type,
                   char_eqns = List.map (I ## snd) char_eqns }
    in
      fn code_eqs =>
        let
          val tag1 = merge_tags tag0 (List.map tag code_eqs)
          val code_thms = code_eqs
          val eqs = List.map dest_code_eqn code_eqs
          val tc1 = tc0 eqs
        in
          fn tm =>
            let
              val tm' = tc1 tm
              val eqn = safe_mk_eq tm tm'
              val result = make_thm Count.Compute (tag1, empty_hyp, eqn)
            in
              record_step ("COMPUTE " ^ its (iT tm) ^ " " ^ its (iT eqn))
                          (char_thms @ code_thms);
              result
            end
        end
    end;
end (*local *)

(*---------------------------------------------------------------------------
     Trace accessors for ProofTrace module
 ---------------------------------------------------------------------------*)

fun trace_get_types () = rev (!ty_list)
fun trace_get_terms () = rev (!tm_list)

fun trace_lookup_type ty =
  case Redblackmap.peek (!ty_map, ty) of SOME id => id | NONE => ~1
fun trace_lookup_term tm =
  case Redblackmap.peek (!tm_map, tm) of SOME id => id | NONE => ~1

fun trace_close_files () =
  ((case !steps_strm of
      SOME s => ((TextIO.flushOut s; TextIO.closeOut s) handle _ => ())
    | NONE => ());
   (case !parents_strm of
      SOME s => ((TextIO.flushOut s; TextIO.closeOut s) handle _ => ())
    | NONE => ());
   steps_strm := NONE;
   parents_strm := NONE)

(* Set the actual cleanup implementation now that trace_close_files exists *)
val _ = trace_cleanup_fn := (fn () =>
  ((trace_close_files () handle _ => ());
   (case !trace_steps_path_ref of
      SOME s => (OS.FileSys.remove s handle _ => ())
    | NONE => ());
   (case !trace_parents_path_ref of
      SOME p => (OS.FileSys.remove p handle _ => ())
    | NONE => ())))

fun trace_step_count () = !trace_counter

fun trace_reset () =
  (trace_close_files ();
   (OS.FileSys.remove (trace_steps_path ()) handle OS.SysErr _ => ());
   (OS.FileSys.remove (trace_parents_path ()) handle OS.SysErr _ => ());
   trace_steps_path_ref := NONE;
   trace_parents_path_ref := NONE;
   trace_counter := 0;
   ty_map := Redblackmap.mkDict Type.compare;
   tm_map := Redblackmap.mkDict Term.compare;
   ty_counter := 0;
   tm_counter := 0;
   ty_list := [];
   tm_list := [];
   lines_written := 0;
   ext_thm_cache := Redblackmap.mkDict Int.compare)

fun trace_get_ext_cache () = !ext_thm_cache

(* Cache an external ancestor thm's statement for TRUST entries.
   Used by ProofTrace for re-exported ancestor thms that were never
   parents of local steps and thus missed by cache_ext_parents. *)
fun trace_cache_ext_thm (THM(_, hyps, c, id)) =
  case Redblackmap.peek(!ext_thm_cache, id) of
    SOME _ => ()
  | NONE =>
    let val hyp_list = HOLset.listItems hyps
    in ignore (intern_term c);
       List.app (ignore o intern_term) hyp_list;
       ext_thm_cache :=
         Redblackmap.insert(!ext_thm_cache, id, (hyp_list, c))
    end

(* ===================================================================== *)
(* trace_export: write .pftrace at theory export time.                   *)
(* Reads temp files, backward-reachability minimizes, writes .pftrace.   *)
(* Called directly from Theory.export_theory so it works even when       *)
(* ProofTrace.sml is not loaded (e.g., Initial build phase).             *)
(* ===================================================================== *)

local
  fun count_lines path =
    let val instrm = TextIO.openIn path
        fun count n = case TextIO.inputLine instrm of
                        NONE => n | SOME _ => count (n + 1)
    in count 0 before TextIO.closeIn instrm end

  fun read_parents path n =
    let val arr = Array.array (n, [] : int list)
        val instrm = TextIO.openIn path
        fun rd i = case TextIO.inputLine instrm of
            NONE => ()
          | SOME line =>
            let val ids = List.mapPartial Int.fromString
                            (String.tokens Char.isSpace line)
            in if i < n then Array.update(arr, i, ids) else ();
               rd (i + 1) end
    in rd 0; TextIO.closeIn instrm; arr end

  fun mark_live parents base roots =
    let val n = Array.length parents
        val live = Array.array (n, false)
        fun mark gid =
          let val fp = gid - base in
            if fp < 0 orelse fp >= n then ()
            else if Array.sub(live, fp) then ()
            else (Array.update(live, fp, true);
                  List.app mark (Array.sub(parents, fp)))
          end
    in List.app mark roots; live end

  (* FNV-1a 64-bit hash for step deduplication *)
  val fnv_offset = 0wxCBF29CE484222325 : Word64.word
  val fnv_prime  = 0wx00000100000001B3 : Word64.word
  fun fnv1a_byte (h, b) =
    Word64.*(Word64.xorb(h, Word64.fromInt b), fnv_prime)
  fun fnv1a_string s =
    CharVector.foldl (fn (c,h) => fnv1a_byte(h, Char.ord c)) fnv_offset s
  fun fnv1a_word64 (h, w) =
    let fun byte n =
          Word64.toInt(Word64.andb(Word64.>>(w, Word.fromInt(n*8)), 0wxFF))
    in fnv1a_byte(fnv1a_byte(fnv1a_byte(fnv1a_byte(
       fnv1a_byte(fnv1a_byte(fnv1a_byte(fnv1a_byte(h,
       byte 0), byte 1), byte 2), byte 3),
       byte 4), byte 5), byte 6), byte 7) end

  fun build_renumber live =
    let val n = Array.length live
        val remap = Array.array (n, ~1)
        val next = ref 0
    in Array.appi (fn (i, true) =>
         (Array.update(remap, i, !next); next := !next + 1)
       | _ => ()) live;
       (remap, !next)
    end

  fun escape_string s =
    if CharVector.all (fn c => Char.isPrint c andalso c <> #" ") s
    then s
    else "\"" ^ String.translate
       (fn #"\"" => "\\\"" | #"\\" => "\\\\" | #"\n" => "\\n" | c => str c) s
         ^ "\""

  (* Detect retired/old constant names: oldN->original_name<-old *)
  fun decode_old_name name =
    if String.isPrefix "old" name andalso String.isSuffix "<-old" name then
      let val inner = String.substring(name, 3, size name - 3)
          val arrow_pos = Lib.index (fn c => c = #">") (String.explode inner)
          val orig = String.substring(inner, arrow_pos + 1,
                       size inner - arrow_pos - 1 - 5)
      in SOME orig end handle _ => NONE
    else NONE

  fun build_type_map (types : hol_type list) =
    #1 (List.foldl (fn (ty, (m, i)) =>
      case Redblackmap.peek(m, ty) of
        SOME _ => (m, i + 1)
      | NONE => (Redblackmap.insert(m, ty, i), i + 1))
      (Redblackmap.mkDict Type.compare, 0) types)

  fun build_term_map (terms : term list) =
    #1 (List.foldl (fn (tm, (m, i)) =>
      case Redblackmap.peek(m, tm) of
        SOME _ => (m, i + 1)
      | NONE => (Redblackmap.insert(m, tm, i), i + 1))
      (Redblackmap.mkDict Term.compare, 0) terms)

  fun write_type_entry ty_lookup ostrm idx ty =
    if Type.is_vartype ty then
      TextIO.output(ostrm,
        "Y " ^ its idx ^ " V " ^ escape_string (Type.dest_vartype ty) ^ "\n")
    else
      let val {Thy, Tyop, Args} = Type.dest_thy_type ty
          val arg_ids = map ty_lookup Args
          val out_tyop = case decode_old_name Tyop of
                           SOME orig => orig | NONE => Tyop
      in TextIO.output(ostrm,
           "Y " ^ its idx ^ " O " ^ escape_string Thy ^ " " ^
           escape_string out_tyop ^
           (if null arg_ids then ""
            else " " ^ String.concatWith " " (map its arg_ids)) ^ "\n")
      end

  fun write_term_entry ty_lookup tm_lookup ostrm idx tm =
    case Term.dest_term tm of
        Term.VAR (name, ty) =>
          TextIO.output(ostrm,
            "M " ^ its idx ^ " V " ^ escape_string name ^ " " ^
            its (ty_lookup ty) ^ "\n")
      | Term.CONST {Name, Thy, Ty} =>
          let val out_name = case decode_old_name Name of
                               SOME orig => orig | NONE => Name
          in TextIO.output(ostrm,
               "M " ^ its idx ^ " C " ^ escape_string Thy ^ " " ^
               escape_string out_name ^ " " ^ its (ty_lookup Ty) ^ "\n")
          end
      | Term.COMB (f, x) =>
          TextIO.output(ostrm,
            "M " ^ its idx ^ " A " ^
            its (tm_lookup f) ^ " " ^ its (tm_lookup x) ^ "\n")
      | Term.LAMB (v, b) =>
          TextIO.output(ostrm,
            "M " ^ its idx ^ " L " ^
            its (tm_lookup v) ^ " " ^ its (tm_lookup b) ^ "\n")

  (* --- Compression: prefer zstd, fallback to gzip --- *)
  val (compress_ext, compress_cmd) =
    let val p : (TextIO.instream, TextIO.outstream) Unix.proc =
          Unix.execute("/bin/sh",
            ["-c", "echo x | zstd -c > /dev/null 2>/dev/null"])
        val st = Unix.reap p
    in if OS.Process.isSuccess st
       then (".zst", fn path => "zstd -c -q > " ^ path)
       else (".gz", fn path => "gzip > " ^ path)
    end
    handle _ =>
      (".gz", fn path => "gzip > " ^ path)

in
fun trace_export thyname thy_parents all_thms =
  let
    val () = trace_close_files ()
    val n_file_lines = count_lines (trace_steps_path ())
    val _ = if n_file_lines = 0 then raise ERR "trace_export" "no steps"
            else ()
    val total_steps = !trace_counter
    val base = total_steps - n_file_lines
    val root_ids = map (fn (_, THM(_, _, _, id)) => id) all_thms
    val parents = read_parents (trace_parents_path ()) n_file_lines
    val live = mark_live parents base root_ids
    val (remap, n_live) = build_renumber live

    (* Collect external IDs *)
    val ext_set = ref (Redblackset.empty Int.compare)
    val _ = Array.appi (fn (i, _) =>
      if Array.sub(live, i) then
        List.app (fn pid =>
          if pid < base then ext_set := Redblackset.add(!ext_set, pid)
          else ())
          (Array.sub(parents, i))
      else ()) live
    val _ = List.app (fn (_, th as THM(_, _, _, tid)) =>
      let val fp = tid - base in
        if fp < 0 orelse fp >= n_file_lines
        then (ext_set := Redblackset.add(!ext_set, tid);
              trace_cache_ext_thm th)
        else ()
      end) all_thms
    val ext_ids = Redblackset.listItems (!ext_set)
    val n_ext = length ext_ids

    val types = rev (!ty_list)
    val terms = rev (!tm_list)
    val ty_map_local = build_type_map types
    val tm_map_local = build_term_map terms
    fun ty_lookup ty = case Redblackmap.peek(ty_map_local, ty) of
                         SOME id => id | NONE => ~1
    fun tm_lookup tm = case Redblackmap.peek(tm_map_local, tm) of
                         SOME id => id | NONE => ~1
    val n_types = length types
    val n_terms = length terms
    val objdir = ".hol/objs"
    val _ = (OS.FileSys.mkDir ".hol" handle OS.SysErr _ => ())
    val _ = (OS.FileSys.mkDir objdir handle OS.SysErr _ => ())
    val outname = objdir ^ "/" ^ thyname ^ "Theory.pftrace" ^ compress_ext

    fun open_compress path =
      let val p : (TextIO.instream, TextIO.outstream) Unix.proc =
            Unix.execute("/bin/sh", ["-c", compress_cmd path])
      in (Unix.textOutstreamOf p, p) end
    fun close_compress (ostrm, p) =
      (TextIO.closeOut ostrm; ignore (Unix.reap p))

    (* --- Parameterized trace writer --- *)
    fun write_body ostrm
        {step_count, step_offset,
         type_live_fn  : int -> bool,
         term_live_fn  : int -> bool,
         step_include  : int -> bool,   (* dense_id → include? *)
         step_outid    : int -> int,    (* dense_id → output id *)
         renumber      : int -> string, (* dense_id → output id string *)
         export_outid  : int -> int} =  (* dense_id → output id *)
      let
        val ext_rm =
          #1 (List.foldl (fn (eid, (m, next)) =>
                (Redblackmap.insert(m, eid, next), next + 1))
              (Redblackmap.mkDict Int.compare, step_offset) ext_ids)
        fun ren gid =
          let val fp = gid - base in
            if fp >= 0 andalso fp < n_file_lines then
              let val did = Array.sub(remap, fp) in
                if did >= 0 then renumber did else "?" ^ its gid
              end
            else case Redblackmap.peek(ext_rm, gid) of
                   SOME did => its did
                 | NONE => "?" ^ its gid
          end
      in
        TextIO.output(ostrm, "HOL4_PROOF_TRACE 1\n");
        TextIO.output(ostrm, "THEORY " ^ escape_string thyname ^ "\n");
        TextIO.output(ostrm, "PARENTS " ^
          String.concatWith " " (map escape_string thy_parents) ^ "\n");
        (* Best-effort ancestor digests: look for parent trace file in
           .hol/objs/ (try .zst then .gz), compute SHA-256 and record. *)
        List.app (fn par =>
          let val base = objdir ^ "/" ^ par ^ "Theory.pftrace"
              val p = if OS.FileSys.access(base ^ ".zst", [])
                      then SOME (base ^ ".zst")
                      else if OS.FileSys.access(base ^ ".gz", [])
                      then SOME (base ^ ".gz")
                      else NONE
          in
            case p of NONE => ()
            | SOME pf =>
              let
                val proc : (TextIO.instream, TextIO.outstream) Unix.proc =
                  Unix.execute("/usr/bin/sha256sum", [pf])
                val line = TextIO.inputAll (Unix.textInstreamOf proc)
                val hash = hd (String.tokens Char.isSpace line)
                val _ = Unix.reap proc
              in
                TextIO.output(ostrm, "ANCESTOR " ^
                  escape_string par ^ " sha256:" ^ hash ^ "\n")
              end handle _ => ()
          end) thy_parents;
        TextIO.output(ostrm, "COUNTS " ^ its n_types ^ " " ^
          its n_terms ^ " " ^ its (step_count + n_ext) ^ "\n");
        TextIO.output(ostrm, "\n");

        (* Types *)
        ignore (List.foldl (fn (ty, i) =>
          (if type_live_fn i
           then write_type_entry ty_lookup ostrm i ty else ();
           i+1)) 0 types);
        TextIO.output(ostrm, "\n");

        (* Terms *)
        ignore (List.foldl (fn (tm, i) =>
          (if term_live_fn i
           then write_term_entry ty_lookup tm_lookup ostrm i tm else ();
           i+1)) 0 terms);
        TextIO.output(ostrm, "\n");

        (* Steps *)
        let val instrm = TextIO.openIn (trace_steps_path ())
            fun process fp =
              case TextIO.inputLine instrm of
                NONE => ()
              | SOME line =>
                (if fp < n_file_lines andalso Array.sub(live, fp) then
                   let val did = Array.sub(remap, fp) in
                     if step_include did then
                       let val sl = String.substring(line, 0, size line - 1)
                           val pids = Array.sub(parents, fp)
                           val rs = String.concatWith " " (map ren pids)
                       in TextIO.output(ostrm,
                            "P " ^ its (step_outid did) ^ " " ^ sl ^
                            (if null pids then "" else " | " ^ rs) ^
                            "\n")
                       end
                     else ()
                   end
                 else ();
                 process (fp + 1))
        in process 0; TextIO.closeIn instrm end;

        (* Trust entries *)
        let val ecache = !ext_thm_cache in
          List.app (fn eid =>
            let val did = valOf (Redblackmap.peek(ext_rm, eid))
                val stmt = case Redblackmap.peek(ecache, eid) of
                    SOME (hyps, c) =>
                      let val c_id = tm_lookup c
                          val h_ids = map tm_lookup hyps
                      in " " ^ its c_id ^ " " ^ its (length h_ids) ^
                         (if null h_ids then ""
                          else " " ^ String.concatWith " "
                                       (map its h_ids))
                      end
                  | NONE => ""
            in TextIO.output(ostrm,
                 "P " ^ its did ^ " TRUST " ^ its eid ^ stmt ^ "\n")
            end) ext_ids
        end;
        TextIO.output(ostrm, "\n");

        (* Exports *)
        List.app (fn (name, THM(_, _, _, tid)) =>
          let val fp = tid - base
              val oid =
                if fp >= 0 andalso fp < n_file_lines then
                  let val did = Array.sub(remap, fp) in
                    if did >= 0 then export_outid did else ~1
                  end
                else (case Redblackmap.peek(ext_rm, tid) of
                        SOME d => d | NONE => ~1)
          in TextIO.output(ostrm,
               "E " ^ escape_string name ^ " " ^ its oid ^ "\n")
          end) all_thms
      end

    (* === Phase 1: Write raw trace (always valid) via gzip pipe === *)
    val (os1, p1) = open_compress outname
    val _ = (write_body os1
               {step_count = n_live, step_offset = n_live,
                type_live_fn = fn _ => true,
                term_live_fn = fn _ => true,
                step_include = fn _ => true,
                step_outid = fn did => did,
                renumber = fn did => its did,
                export_outid = fn did => did};
             close_compress (os1, p1))
            handle e => (close_compress (os1, p1) handle _ => (); raise e)

    (* === Phase 2: Try optimized export (pruning + dedup) === *)
    val (n_final, n_deduped, n_live_types, n_live_terms) =
    (let
       (* Step dedup: hash-cons with equality verification.
          Hash is used for bucketing only; dedup requires exact match
          of step line + canonical parent IDs. *)
       val hash_arr = Array.array(n_live, fnv_offset)
       val dedup_to = Array.tabulate(n_live, fn i => i)
       (* Map hash → list of (dense_id, step_line, canonical_parents) *)
       val cmap = ref (Redblackmap.mkDict Word64.compare
                       : (Word64.word, (int * string * int list) list)
                         Redblackmap.dict)
       fun phash gid =
         let val fp = gid - base in
           if fp >= 0 andalso fp < n_file_lines then
             let val did = Array.sub(remap, fp) in
               if did >= 0 then Array.sub(hash_arr, did) else fnv_offset
             end
           else fnv1a_string (its gid)
         end

       fun find_equal _ _ [] = NONE
         | find_equal sl cpids ((did, csl, ccpids) :: rest) =
             if sl = csl andalso cpids = ccpids then SOME did
             else find_equal sl cpids rest

       (* Scan: int refs for pruning + step hashes for dedup *)
       val int_refs = let
         val refs = ref (Redblackset.empty Int.compare)
         val instrm = TextIO.openIn (trace_steps_path ())
         fun scan fp =
           case TextIO.inputLine instrm of
             NONE => ()
           | SOME line =>
             (if fp < n_file_lines andalso Array.sub(live, fp) then
                let val did = Array.sub(remap, fp)
                    val sl = String.substring(line, 0, size line - 1)
                    val toks = String.tokens Char.isSpace sl
                    fun collect [] = ()
                      | collect (t :: rest) =
                        (case Int.fromString t of
                           SOME n => refs := Redblackset.add(!refs, n)
                         | NONE => ();
                         collect rest)
                    val _ = collect
                              (case toks of _ :: rest => rest | _ => [])
                    val pids = Array.sub(parents, fp)
                    (* Canonical parent IDs for equality check *)
                    val cpids = map (fn gid =>
                      let val pfp = gid - base in
                        if pfp >= 0 andalso pfp < n_file_lines then
                          let val pdid = Array.sub(remap, pfp) in
                            if pdid >= 0
                            then Array.sub(dedup_to, pdid)
                            else gid
                          end
                        else gid
                      end) pids
                    val h = List.foldl (fn (gid, h) =>
                              fnv1a_word64(h, phash gid))
                              (fnv1a_string sl) pids
                    val bucket = case Redblackmap.peek(!cmap, h) of
                                   SOME bs => bs | NONE => []
                in
                  Array.update(hash_arr, did, h);
                  case find_equal sl cpids bucket of
                    SOME canon => Array.update(dedup_to, did, canon)
                  | NONE => cmap :=
                      Redblackmap.insert(!cmap, h,
                        (did, sl, cpids) :: bucket)
                end
              else ();
              scan (fp + 1))
       in scan 0; TextIO.closeIn instrm; !refs end

       (* Output renumbering *)
       val output_id = Array.array(n_live, ~1)
       val n_unique = let val next = ref 0 in
         Array.appi (fn (i, _) =>
           if Array.sub(dedup_to, i) = i
           then (Array.update(output_id, i, !next); next := !next + 1)
           else ()) output_id;
         !next end
       val _ = Array.appi (fn (i, _) =>
         if Array.sub(dedup_to, i) <> i then
           Array.update(output_id, i,
             Array.sub(output_id, Array.sub(dedup_to, i)))
         else ()) output_id

       fun opt_outid did =
         Array.sub(output_id, Array.sub(dedup_to, did))

       (* Term/type pruning *)
       val all_refs = let
         val refs = ref int_refs
         val ecache = !ext_thm_cache
       in
         List.app (fn eid =>
           case Redblackmap.peek(ecache, eid) of
             SOME (hyps, c) =>
               (refs := Redblackset.add(!refs, tm_lookup c);
                List.app (fn h =>
                  refs := Redblackset.add(!refs, tm_lookup h)) hyps)
           | NONE => ()) ext_ids;
         !refs
       end

       val ty_arr = Array.fromList types
       val tm_arr = Array.fromList terms
       val live_ty = Array.array(n_types, false)
       val live_tm = Array.array(n_terms, false)
       fun mark_term i =
         if i < 0 orelse i >= n_terms orelse Array.sub(live_tm, i) then ()
         else (Array.update(live_tm, i, true);
               case Term.dest_term (Array.sub(tm_arr, i)) of
                 Term.COMB(f, x) =>
                   (mark_term (tm_lookup f); mark_term (tm_lookup x))
               | Term.LAMB(v, b) =>
                   (mark_term (tm_lookup v); mark_term (tm_lookup b))
               | Term.VAR(_, ty) => mark_type (ty_lookup ty)
               | Term.CONST{Ty,...} => mark_type (ty_lookup Ty))
       and mark_type i =
         if i < 0 orelse i >= n_types orelse Array.sub(live_ty, i) then ()
         else (Array.update(live_ty, i, true);
               let val ty = Array.sub(ty_arr, i) in
                 if Type.is_vartype ty then ()
                 else let val {Args,...} = Type.dest_thy_type ty
                      in List.app (fn a => mark_type (ty_lookup a)) Args
                      end
               end)
       val _ = Redblackset.app (fn i =>
         (if i >= 0 andalso i < n_terms then mark_term i else ();
          if i >= 0 andalso i < n_types then mark_type i else ())) all_refs

       val nlt = Array.foldl (fn (b,n) => if b then n+1 else n) 0 live_ty
       val nlm = Array.foldl (fn (b,n) => if b then n+1 else n) 0 live_tm

       (* Write optimized trace to temp .gz, then rename over raw *)
       val tmpgz = outname ^ ".tmp"
       val (os2, p2) = open_compress tmpgz
       val _ = (write_body os2
                  {step_count = n_unique, step_offset = n_unique,
                   type_live_fn = fn i => Array.sub(live_ty, i),
                   term_live_fn = fn i => Array.sub(live_tm, i),
                   step_include = fn did =>
                     Array.sub(dedup_to, did) = did,
                   step_outid = fn did => Array.sub(output_id, did),
                   renumber = fn did => its (opt_outid did),
                   export_outid = opt_outid};
                close_compress (os2, p2))
               handle e =>
                 (close_compress (os2, p2) handle _ => (); raise e)
       val _ = OS.FileSys.rename {old = tmpgz, new = outname}
     in
       (n_unique, n_live - n_unique, nlt, nlm)
     end)
    handle e =>
      (Feedback.HOL_WARNING "Thm" "trace_export"
         ("optimized export failed (" ^ General.exnMessage e ^
          "); keeping raw trace");
       (OS.FileSys.remove (outname ^ ".tmp") handle _ => ());
       (n_live, 0, n_types, n_terms))
  in
    trace_reset ();
    Feedback.HOL_MESG ("Proof trace: " ^ outname ^ " (" ^
      its n_final ^ " steps" ^
      (if n_deduped > 0 then " [" ^ its n_deduped ^ " deduped]" else "") ^
      " + " ^ its n_ext ^ " trust, " ^
      its n_live_terms ^ "/" ^ its n_terms ^ " terms, " ^
      its n_live_types ^ "/" ^ its n_types ^ " types)")
  end
  handle IO.Io e =>
    (trace_reset ();
     Feedback.HOL_WARNING "Thm" "trace_export"
       ("I/O error: " ^ #function e ^ " " ^ #name e))
  | HOL_ERR _ => trace_reset ()
end (* local trace_export *)

(* Register cleanup for the initial heap build process.
   For processes that restore this heap via loadState, the handler
   is re-registered in the IO.Io path of record_step. *)
val _ = OS.Process.atExit trace_cleanup

end (* Thm *)
