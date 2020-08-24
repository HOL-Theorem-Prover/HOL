(*---------------------------------------------------------------------------
 * The functions in this module (except [from_term] and [inst_dterm]) are
 * called only to build the database of rewrite rules. Therefore,
 * optimisation is not so important.
 *
 * [from_term] is the first step of normalisation, and it is not called
 * later on (except with external conv).
 *---------------------------------------------------------------------------*)

structure clauses :> clauses =
struct

open HolKernel boolSyntax Drule Conv compute_rules

val CL_ERR = mk_HOL_ERR "clauses"
infix ##

(*---------------------------------------------------------------------------
 * Checking that a given thm is a reduction rule we can handle:
 *         (c p1...pn) = rhs
 * with p1...pn  either a const applied to patterns or a free variable.
 *---------------------------------------------------------------------------*)

(* Raised by `check_arg_form`. *)
exception Not_suitable;

datatype pattern =
    Pvar of int
  | Papp of { Head : term, Args : pattern list};

(*
   `check_arg_form : term -> term list * term * pattern list`

   Check that the given term is acceptable as the left hand side of an equation
   accepted by computeLib. `check_arg_form t` gives `(l, c, patl)` where `l` is
   a list of the free variables of `t`, `c` head constant of `t` and `patl` is
   the list of arguments of `t` as a `pattern` with free variables numbered
   according to their position in `l`. If `t` is not of the required form, then
   raise an exception.
*)
fun check_arg_form trm =
  let
    fun chk t stk free =
      if is_comb t then
        let
          val (Rator,Rand) = dest_comb t
          val (free',pat1) = chk Rand [] free
        in
          chk Rator (pat1::stk) free'
        end
      else if (is_var t) then
        if null stk then
          let
            val newi = length free
          in
            (free, Pvar (newi - index (aconv t) free - 1))
            handle HOL_ERR _ => (t::free, Pvar newi)
          end
        else
          raise CL_ERR "check_arg_form"
                       (Lib.quote (fst(dest_var t))^
                       " occurs as a variable on lhs")
      else if is_const t then
        (free, Papp{Head=t, Args=rev stk})
      else
        raise Not_suitable
  in case chk trm [] [] of
       (fv,Papp{Head,Args}) => (rev fv,Head,Args)
     | _ => raise CL_ERR "check_arg_form" "ill-formed lhs"
  end;

(*
   Useful information about a term.
   - `CLOS` denotes a delayed substitution (closure).
   - `CST` denotes an applied constant. Its first argument is the head constant;
     the second is the list of its arguments (we keep both the term and its
     abstract representation); the last one is the set of rewrites that still
     have a chance to be used, ie. those with a lhs wider than the number of
     applied args.
   - `NEUTR` is a slight improvement of `CST` with an empty list of rewrites, so
     that arguments of a variable are immediatly strongly reduced.

  `fterm`s can be built from HOL4 terms with `from_term` followed by
  `equations.mk_clos`.

   Presumably means “focused term” based on [Barras2000] (reference given in
   computeLib.sml).
*)
datatype 'a fterm
    = (* order of Args: outermost ahead *)
      CST of { Head : term,
               Args : (term * 'a fterm) list,
               Rws  : 'a,
               Skip : int option }
    | NEUTR
    | CLOS of { Env : 'a fterm list, Term : 'a dterm }

(*
   Shadow terms with all information needed by `computeLib`. Only instantiated
   with `'a = db`.
   - They are real de Bruijn terms, so that abstraction destruction is in
     constant time.
   - Application is n-ary (slight optimization)
   - We forget the names of variables
   - Constants are tagged with the set of rewrites that apply to it. It's a
     reference since dterm is used to represent rhs of rewrites, and fixpoints
     equations add rewrites for a constant that appear in the rhs.

   These shadow terms can be built from HOL4 terms with `from_term`.

   Presumably means “de-Bruijin term” based on [Barras2000] (reference given in
   computeLib.sml).
*)
and 'a dterm
    = Bv of int
    | Fv
    | Cst of term * ('a * int option) ref
    | App of 'a dterm * 'a dterm list  (* order: outermost ahead *)
    | Abs of 'a dterm;

(* Make a combination of shadow terms. Left-nested applications are composed so
as to preserve the following invariant: the first arg of App never is an App. *)
fun appl(App(a,l1),arg) = App(a,arg::l1)
  | appl(t,arg) = App(t,[arg]);

(*---------------------------------------------------------------------------
 * Type variable instantiation in dterm. Make it tail-recursive ?
 *---------------------------------------------------------------------------*)
fun inst_type_dterm ([],v) = v
  | inst_type_dterm (tysub,v) =
      let fun tyi_dt (Cst(c,dbsk)) = Cst(Term.inst tysub c, dbsk)
            | tyi_dt (App(h,l))  = App(tyi_dt h, map tyi_dt l)
            | tyi_dt (Abs v)     = Abs(tyi_dt v)
            | tyi_dt v           = v
      in tyi_dt v end;

datatype action =
    Rewrite of rewrite list
  | Conv of (term -> Thm.thm * db fterm)

(*
   Database of actions for a single constant. There is a linked list through the
   argument of `NeedArg` and `Tail` of `Try`. The linked-to `db` is for the same
   constant with arity greater by 1. The `db` that appears as a value in the
   `Redblackmap.dict` in the `compset` is the `db` for arity 0 for that
   constant.

   TO-DO: Which type instance of the constant is `Hcst`?
*)
and db =
    EndDb
  | Try of { Hcst : term, Rws : action, Tail : db }
  | NeedArg of db

(* An equation used as a rewrite in the compset. *)
and rewrite =
    RW of { cst: term,           (* constant which the rule applies to *)
            ants: db dterm list, (* Antecedents of the `thm` *)
            lhs: pattern list,   (* patterns = constant args in lhs of thm *)
            npv: int,            (* number of distinct pat vars in lhs *)
            rhs: db dterm,
            thm: Thm.thm };      (* thm we use for rewriting *)

(*
   The key of an individual rewrite used in the compset map.

   `key_of rw --> ((const_name, theory_name), arg_count, head_const)`
 *)
fun key_of (RW{cst, lhs, ...}) =
  let val {Name,Thy,...} = dest_thy_const cst in
  ((Name,Thy), length lhs, cst)
  end;

fun is_skip (_, CST {Skip=SOME n,Args,...}) = (n <= List.length Args)
  | is_skip _ = false;

fun partition_skip (SOME n) Args =
  let val len = List.length Args in
     if n <= len
     then Lib.split_after (len - n) Args
     else ([], Args)
  end
   | partition_skip NONE Args = ([], Args);

(*
   Compsets are databases of actions where each action is (1) an equation used
   for rewriting or (2) a conversion with an associated pattern; the conversion
   is used where the pattern matches. Currently implemented as a map from
   constants to per-constant databases of actions.

   TO-DO: We should try to factorize the rules (cf. discrimination nets). Rules
   are packed according to their head constant, and then sorted according to the
   width of their lhs.
*)
datatype compset
   = Compset of (string * string, (db * int option) ref) Redblackmap.dict ref;

fun lex_string_comp ((s1, s2), (s3, s4)) =
  case String.compare (s1, s3) of
    EQUAL => String.compare (s2, s4)
  | x => x

fun empty_rws () = Compset (ref (Redblackmap.mkDict lex_string_comp));

(*
   Look up the per-constant database of `cst` in the given compset. If it does
   not exist, create an empty database for this constant. The constant is given
   as a pair `(const_name, theory_name)`.
*)
fun assoc_clause (Compset rws) cst =
  case Redblackmap.peek (!rws, cst)
   of SOME rl => rl
    | NONE => let val mt = ref (EndDb, NONE)
              in rws := Redblackmap.insert (!rws,cst,mt)
               ; mt
              end;

fun add_in_db (n,cst,act,EndDb) =
      funpow n NeedArg (Try{Hcst=cst, Rws=act, Tail=EndDb})
  | add_in_db (0,cst,act as Rewrite nrws,Try{Hcst,Rws as Rewrite rws,Tail}) =
      if aconv cst Hcst then
        Try{ Hcst=Hcst, Rws=Rewrite(nrws@rws), Tail=Tail }
      else
        Try { Hcst=Hcst, Rws=Rws, Tail=add_in_db(0,cst,act,Tail) }
  | add_in_db (n,cst,act,Try{Hcst,Rws,Tail}) =
      Try { Hcst=Hcst, Rws=Rws, Tail=add_in_db(n,cst,act,Tail) }
  | add_in_db (0,cst,act,db) = Try{ Hcst=cst, Rws=act, Tail=db }
  | add_in_db (n,cst,act,NeedArg tail) =
      NeedArg(add_in_db(n-1,cst,act,tail));

fun add_in_db_upd compset (name,arity,hcst) action =
  let val rl = assoc_clause compset name
    val (db, sk) = !rl
  in rl := (add_in_db (arity,hcst,action,db), sk)
  end;

fun set_skip (compset as Compset htbl) p sk =
  let val rl = assoc_clause compset p
    val (db,_) = !rl
  in rl := (db,sk)
  end;

fun scrub_const (Compset htbl) c =
  let val {Thy,Name,Ty} = dest_thy_const c
  in htbl := #1 (Redblackmap.remove (!htbl,(Name,Thy)))
  end;

(*
   `from_term(compset,env,t)` converts the HOL term `t` into a shadow term with
   the given compset. `env` is the environments of variables free in `t` when
   `t` is a subterm encounterd descending on a term. Modifies `compset` to add
   an empty entry for any constant that does not exist in the compset.

   Combinations nested in the left in the HOL term are translated into a single
   combination in the shadow term.
*)
fun from_term (rws,env,t) =
  let
    (* `c`: explicit representation of continuation. *)
    fun down (env,t,c) =
      case dest_term t of
        VAR _ => up((Bv (index (aconv t) env) handle HOL_ERR _ => Fv), c)
      | CONST{Name,Thy,...} => up(Cst (t,assoc_clause rws (Name,Thy)),c)
      (* Descend immediately into operator. Descend into operand in the
      continuation. If this is a left-nested combination, it is composed in a
      single `App` when ascending back from the operand. *)
      | COMB(Rator,Rand) => down(env,Rator,Zrator{Rand=(env,Rand),Ctx=c})
      | LAMB(Bvar,Body) => down(Bvar :: env, Body, Zabs{Bvar=(), Ctx=c})
    (* `dt`: shadow term. *)
    and up (dt, Ztop) = dt
      | up (dt, Zrator{Rand=(env,arg), Ctx=c}) =
          down (env,arg,Zrand{Rator=dt, Ctx=c})
      | up (dt, Zrand{Rator=dr, Ctx=c}) = up (appl(dr,dt), c)
      | up (dt, Zabs{Ctx=c,...}) = up(Abs dt, c)
  in
    down (env,t,Ztop)
  end;

(*---------------------------------------------------------------------------
 * Note: if the list of free variables of the lhs was empty, we could
 * evaluate (weak reduction) the rhs now. This implies that the
 * theorems must be added in dependencies order.
 *---------------------------------------------------------------------------*)
fun mk_rewrite compset thm =
  let
    val (ants, conseq) = strip_imp_only (concl thm)
    val (lhs,rhs) = dest_eq conseq
    val (fv,cst,pats) = check_arg_form lhs
    val gen_thm = foldr (uncurry GEN) thm fv
    val env = rev fv
    val rhsc = from_term (compset, env, rhs)
    val ants_in_db = List.map (fn t => from_term (compset, env, t)) ants
  in
    RW{ cst=cst,
        ants=ants_in_db,
        lhs=pats,
        rhs=rhsc,
        npv=length fv,
        thm=gen_thm }
  end;

fun unsuitable t = let
  val (l, r) = dest_eq t
in
  can (match_term l) r
end

val eqt_intro_conv =
  REWR_CONV (SYM (List.nth (BODY_CONJUNCTS boolTheory.EQ_CLAUSES, 1)))
val eqf_intro_conv =
  REWR_CONV (SYM (List.nth (BODY_CONJUNCTS boolTheory.EQ_CLAUSES, 3)))

fun enter_thm compset thm0 = let
  val t = concl thm0
  val (ants, conseq) = strip_imp_only t
  fun add thm =
    let
      val rw_option =
        SOME (mk_rewrite compset thm)
        handle Not_suitable => NONE
        handle HOL_ERR hol_err =>
          raise (wrap_exn "clauses"
                          ("enter_thm: computeLib cannot use thm\n"
                           ^Parse.thm_to_string thm0)
                          (HOL_ERR hol_err))
    in
      case rw_option of
        SOME rw => add_in_db_upd compset (key_of rw) (Rewrite [rw])
      | NONE => ()
    end
in
  if is_eq conseq then
    if unsuitable conseq then
      ()
    else
      add thm0
  else if is_neg conseq then
    add (CONV_RULE (funpow (length ants) RAND_CONV eqf_intro_conv) thm0)
  else
    add (CONV_RULE (funpow (length ants) RAND_CONV eqt_intro_conv) thm0);
  if not (List.null ants) then
    add (EQT_INTRO thm0)
  else
    ()
end

(* Like `BODY_CONJUNCTS` but descends into the consequent of implications. *)
fun split_conjuncts thm =
  let
    fun recurse [] acc =
        List.rev acc
      | recurse ((thm, ants)::rest) acc =
        (* `ants` is the list of antecedents to be discharged from `thm` before
        putting it in `acc`. *)
        let
          val t = concl (thm)
        in
          if is_conj t then
            recurse ((CONJUNCT1 thm, ants)::(CONJUNCT2 thm, ants)::rest) acc
          else if is_imp_only t then
            let
              val (ant, conseq) = dest_imp_only t
            in
              recurse ((MP thm (ASSUME ant), ant::ants)::rest) acc
            end
          else if is_forall t then
            recurse ((SPEC_ALL thm, ants)::rest) acc
          else
            recurse rest (List.foldl (uncurry DISCH) thm ants::acc)
        end
  in
    recurse [(thm, [])] []
  end

fun add_thms lthm compset =
  List.app (List.app (enter_thm compset) o split_conjuncts) lthm;

fun add_thmset setname compset = let
  open ThmSetData
  val data = all_data {settype = setname}
in
  app (fn (s, deltas) => add_thms (added_thms deltas) compset) data
end

fun add_extern (cst,arity,fconv) compset =
  let val {Name,Thy,...} = dest_thy_const cst in
  add_in_db_upd compset ((Name,Thy),arity,cst) (Conv fconv)
  end;

fun new_rws () =
  let val compset = empty_rws()
  in add_thms [boolTheory.REFL_CLAUSE] compset
   ; compset
  end;

fun from_list lthm =
  let val compset = new_rws()
  in add_thms lthm compset
   ; compset
  end;

fun scrub_thms lthm compset =
 let val tmlist = map (concl o hd o BODY_CONJUNCTS) lthm
     val clist = map (fst o strip_comb o lhs o snd o strip_forall) tmlist
 in List.app (scrub_const compset) clist
 end
 handle e => raise wrap_exn "clauses" "del_list" e;

(*---------------------------------------------------------------------------*)
(* Support for analysis of compsets                                          *)
(*---------------------------------------------------------------------------*)

fun rws_of (Compset rrbmap) =
 let val rbmap = !rrbmap
     val thinglist = Redblackmap.listItems rbmap
     fun db_of_entry (ss, r) = let val (db,opt) = !r in db end
     val dblist = List.map db_of_entry thinglist
     fun get_actions db =
      case db
       of EndDb => []
        | NeedArg db' => get_actions db'
        | Try{Hcst,Rws,Tail} => (Hcst,Rws)::get_actions Tail
     val actionlist = List.concat (List.map get_actions dblist)
     fun dest (RW{thm, ...}) = thm
     fun dest_action (Hcst,Rewrite rws) = (Hcst,map dest rws)
       | dest_action (Hcst,Conv _) = (Hcst,[])
     val rwlist = List.map dest_action actionlist
 in
   rwlist
 end;

datatype transform
  = Conversion of (term -> thm * db fterm)
  | RRules of thm list;

(*---------------------------------------------------------------------------*)
(* Compute the "attachments" for each element of the compset. Fortunately,   *)
(* it seems that the insertion of an attachment into a compset also makes    *)
(* insertions for the constants mentioned in the rhs of the rewrite.         *)
(* Otherwise, one would have to do a transitive closure sort of construction *)
(* to make all the dependencies explicit.                                    *)
(*---------------------------------------------------------------------------*)
fun deplist (Compset rrbmap) =
 let val rbmap = !rrbmap
     val thinglist = Redblackmap.listItems rbmap
     fun db_of_entry (ss, r) = let val (db,opt) = !r in (ss,db) end
     val dblist = List.map db_of_entry thinglist
     fun get_actions db =
      case db
       of EndDb => []
        | NeedArg db' => get_actions db'
        | Try{Hcst,Rws,Tail} => Rws::get_actions Tail
     val actionlist = List.map (I##get_actions) dblist
     fun dest (RW{thm, ...}) = thm
     fun dest_action (Rewrite rws) = RRules (map dest rws)
       | dest_action (Conv ecnv) = Conversion ecnv
     val rwlist = List.map (I##(map dest_action)) actionlist
 in
   rwlist
 end;

fun mkCSET () =
 let val tyinfol = TypeBasePure.listItems (TypeBase.theTypeBase())
     val init_set = HOLset.empty
                      (inv_img_cmp (fn {Thy,Name,Ty} => (Thy,Name))
                              (pair_compare(String.compare,String.compare)))
     fun insert_const c cset = HOLset.add(cset,dest_thy_const c)
     fun insert_tycs tyinfo cset =
        itlist insert_const (TypeBasePure.constructors_of tyinfo) cset
 in
     itlist insert_tycs tyinfol init_set
 end;

(*---------------------------------------------------------------------------*)
(* Compute the attachments for each constant, then delete the constructors.  *)
(*---------------------------------------------------------------------------*)
fun no_transform compset =
 let val CSET = mkCSET()
     fun inCSET t = HOLset.member(CSET, dest_thy_const t)
     fun interesting (ss,_::_) = false
       | interesting ((Name,Thy),[]) =
          let val c = prim_mk_const{Name=Name,Thy=Thy}
          in not(inCSET c)
          end
 in
    map fst (filter interesting (deplist compset))
 end;

end
