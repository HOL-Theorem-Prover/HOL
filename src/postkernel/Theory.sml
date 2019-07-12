(* ========================================================================= *)
(* FILE          : Theory.sml                                                *)
(* DESCRIPTION   : Management of logical theories.                           *)
(*                                                                           *)
(* AUTHOR        : Konrad Slind, University of Calgary                       *)
(*                 (also T.U. Munich and Cambridge)                          *)
(* DATE          : September 11, 1991                                        *)
(* REVISION      : August 7, 1997                                            *)
(*               : March 9, 1998                                             *)
(*               : August 2000                                               *)
(*                                                                           *)
(* ========================================================================= *)

(* ----------------------------------------------------------------------
    Updated November/December 2002 - by Michael Norrish
   ---------------------------------------------------------------------- *)

(*---------------------------------------------------------------------------

     Notes on the design.

  We provide a single current theory segment, which can be thought of as
  a scratchpad for building the segment that eventually gets exported.
  The following are the important components of a segment:

      - the types and terms declared in the current segment (stored in
        the "symbol tables" maintained in modules Term and Type).

      - the unique id for the theory, along with its parents, which
        should be already-loaded theory segments.

      - the theory graph, used to enforce a prohibition on circular
        dependencies among segments.

      - the axioms, definitions, and theorems stored in the segment so far.

  The parents of the segment are held in the theory graph.

  When a segment is exported, we dump everything in it to a text file
  representing an ML structure.

  Elements in the current segment can be deleted or overwritten, which
  makes consistency maintenance an issue.  Before a theory is exported,
  everything that is about to be exported gets checked for up-to-date-ness.

 ---------------------------------------------------------------------------*)


structure Theory :> Theory =
struct

open Feedback Lib Type Term Thm ;

open TheoryPP


val debug = ref false
fun DPRINT f = if !debug then print ("Theory.DEBUG: " ^ f ()) else ()
val _ = register_btrace("Theory.debug", debug)

structure PP = HOLPP
type num = Arbnum.num

val ERR  = mk_HOL_ERR "Theory";
val WARN = HOL_WARNING "Theory";

type thy_addon = {sig_ps    : (unit -> PP.pretty) option,
                  struct_ps : (unit -> PP.pretty) option}

local
  val hooks =
    (* hooks are stored in the order they are registered, with later
       hooks earlier in the list.
       The set component is the list of the disabled hooks.
     *)
      ref (HOLset.empty String.compare,
           [] : (string * (TheoryDelta.t -> unit)) list)
in
fun call_hooks td = let
  val (disabled, hooks) = !hooks
  val hooks_rev = List.rev hooks
  fun protect nm (f:TheoryDelta.t -> unit) td = let
    fun error_pfx() =
        "Hook "^nm^" failed on event " ^ TheoryDelta.toString td
  in
    f td
    handle e as HOL_ERR {origin_function,origin_structure,message} =>
           Feedback.HOL_WARNING
               "Theory"
               "callhooks"
               (error_pfx() ^ " with problem " ^
                Feedback.exn_to_string e)
         | Match =>
           Feedback.HOL_WARNING
               "Theory"
               "callhooks"
               (error_pfx() ^ " with a Match exception")
  end
  fun recurse l =
      case l of
        [] => ()
      | (nm, f) :: rest => let
        in
          if HOLset.member(disabled,nm) then ()
          else protect nm f td;
          recurse rest
        end
in
  recurse hooks_rev
end

fun register_hook (nm, f) = let
  val (disabled, hooks0) = !hooks
  val hooks0 = List.filter (fn (nm',f) => nm' <> nm) hooks0
in
  hooks := (disabled, (nm,f) :: hooks0)
end

fun delete_hook nm = let
  val (disabled, hookfns) = !hooks
  val (deleting, remaining) = Lib.partition (fn (nm', _) => nm' = nm) hookfns
in
  case deleting of
    [] => HOL_WARNING "Theory" "delete_hook" ("No hook with name: "^nm)
  | _ => ();
  hooks := (HOLset.delete(disabled,nm), remaining)
end

fun get_hooks () = #2 (!hooks)

fun hook_modify act f x =
  let
    val (disabled0, fns) = !hooks
    fun finish() = hooks := (disabled0, fns)
    val _ = hooks := (act disabled0, fns)
    val result = f x handle e => (finish(); raise e)
  in
    finish();
    result
  end

fun disable_hook nm f x =
  hook_modify (fn s => HOLset.add(s,nm)) f x

fun safedel_fromset nm s =
  HOLset.delete(s, nm) handle HOLset.NotFound => s
fun enable_hook nm f x =
  hook_modify (safedel_fromset nm) f x


end (* local block enclosing declaration of hooks variable *)

(* This reference is set in course of loading the parsing library *)

val pp_thm = ref (fn _:thm => PP.add_string "<thm>")

(*---------------------------------------------------------------------------*
 * Unique identifiers, for securely linking a theory to its parents when     *
 * loading from disk.                                                        *
 *---------------------------------------------------------------------------*)
local
  open Arbnum
in
abstype thyid = UID of {name:string, sec: num, usec : num}
with
  fun thyid_eq x (y:thyid) = (x=y);
  fun new_thyid s =
      let val {sec,usec} = Portable.dest_time (Portable.timestamp())
      in
        UID{name=s, sec = sec, usec = usec}
      end

  fun dest_thyid (UID{name, sec, usec}) = (name,sec,usec)

  val thyid_name = #1 o dest_thyid;

  fun make_thyid(s,i1,i2) = UID{name=s, sec=i1,usec=i2}

  fun thyid_to_string (UID{name,sec,usec}) =
     String.concat["(",Lib.quote name,",",toString sec, ",",
                   toString usec, ")"]

  val min_thyid =
      UID{name="min", sec = fromInt 0, usec = fromInt 0}  (* Ur-theory *)

end;
end (* local *)

fun thyid_assoc x [] = raise ERR "thyid_assoc" "not found"
  | thyid_assoc x ((a,b)::t) = if thyid_eq x a then b else thyid_assoc x t;

fun thyname_assoc x [] = raise ERR "thyname_assoc" "not found"
  | thyname_assoc x ((a,b)::t) = if x = thyid_name a then b
                                 else thyname_assoc x t;


(*---------------------------------------------------------------------------
    The theory graph is quite basic: just a list of pairs (thyid,parents).
    The "min" theory is already installed; it has no parents.
 ---------------------------------------------------------------------------*)

structure Graph = struct type graph = (thyid * thyid list) list
local val theGraph = ref [(min_thyid,[])]
in
   fun add p = theGraph := (p :: !theGraph)
   fun add_parent (n,newp) =
     let fun same (node,_) = thyid_eq node n
         fun addp(node,parents) = (node, op_union thyid_eq [newp] parents)
         fun ins (a::rst) = if same a then addp a::rst else a::ins rst
           | ins [] = raise ERR "Graph.add_parent.ins" "not found"
     in theGraph := ins (!theGraph)
     end
   fun isin n = Lib.can (thyid_assoc n) (!theGraph);
   fun parents_of n = thyid_assoc n (!theGraph);
   fun ancestryl L =
    let fun Anc P Q = rev_itlist
           (fn nde => fn A => if op_mem thyid_eq nde A then A
             else Anc (parents_of nde handle HOL_ERR _ => []) (nde::A)) P Q
    in Anc L []
    end;
   fun fringe () =
     let val all_parents = List.map #2 (!theGraph)
         fun is_parent y = Lib.exists (Lib.op_mem thyid_eq y) all_parents
     in List.filter (not o is_parent) (List.map #1 (!theGraph))
     end;
   fun first P = Lib.first P (!theGraph)
end
end; (* structure Graph *)


(*---------------------------------------------------------------------------*
 * A type for distinguishing the different kinds of theorems that may be     *
 * stored in a theory.                                                       *
 *---------------------------------------------------------------------------*)

open ThmKind_dtype
type thmkind = ThmKind_dtype.t

fun is_axiom (Axiom _) = true  | is_axiom _   = false;
fun is_theorem (Thm _) = true  | is_theorem _ = false;
fun is_defn (Defn _)   = true  | is_defn _    = false;

fun drop_thmkind (Axiom(_,th)) = th
  | drop_thmkind (Thm th)      = th
  | drop_thmkind (Defn th)     = th;

fun drop_pthmkind (s,th) = (s,drop_thmkind th);

fun drop_Axkind (Axiom rth) = rth
  | drop_Axkind    _        = raise ERR "drop_Axkind" "";


(*---------------------------------------------------------------------------*
 * The type of HOL theory segments. Lacks fields for the type and term       *
 * signatures, which are held locally in the Type and Term structures.       *
 * Also lacks a field for the theory graph, which is held in Graph.          *
 *---------------------------------------------------------------------------*)

datatype thydata = Loaded of UniversalType.t
                 | Pending of (string * (string -> term)) list
type ThyDataMap = (string,thydata)Binarymap.dict
                  (* map from string identifying the "type" of the data,
                     e.g., "simp", "mono", "cong", "grammar_update",
                     "LaTeX map", to the data itself. *)
val empty_datamap : ThyDataMap = Binarymap.mkDict String.compare

type segment = {thid    : thyid,                               (* unique id  *)
                facts   : (string * thmkind) list,  (* stored ax,def,and thm *)
                thydata : ThyDataMap,                   (* extra theory data *)
                adjoin  : thy_addon list,              (*  extras for export *)
                mldeps  : string HOLset.set}
local
  open FunctionalRecordUpdate
  fun seg_mkUp z = makeUpdate5 z
in
  fun update_seg z = let
    fun from adjoin facts mldeps thid thydata =
      {adjoin=adjoin, facts=facts, mldeps=mldeps, thid=thid, thydata=thydata}
    (* fields in reverse order to above *)
    fun from' thydata thid mldeps facts adjoin =
      {adjoin=adjoin, facts=facts, mldeps=mldeps, thid=thid, thydata=thydata}
    fun to f {adjoin, facts, mldeps, thid, thydata} =
      f adjoin facts mldeps thid thydata
  in
    seg_mkUp (from, from', to)
  end z
  val U = U
  val $$ = $$
end (* local *)



(*---------------------------------------------------------------------------*
 *                 CREATE THE INITIAL THEORY SEGMENT.                        *
 *                                                                           *
 * The timestamp for a segment is its creation date. "con_wrt_disk" is       *
 * set to false because when a segment is created no corresponding file      *
 * gets created (the file is only created on export).                        *
 *---------------------------------------------------------------------------*)

fun fresh_segment s :segment = {thid=new_thyid s,  facts=[],  adjoin=[],
                               thydata = empty_datamap,
                               mldeps = HOLset.empty String.compare};


local val CT = ref (fresh_segment "scratch")
in
  fun theCT() = !CT
  fun makeCT seg = CT := seg
end;

val CTname = thyid_name o #thid o theCT;
val current_theory = CTname;


(*---------------------------------------------------------------------------*
 *                  READING FROM THE SEGMENT                                 *
 *---------------------------------------------------------------------------*)

fun thy_types thyname               = Type.thy_types thyname
fun thy_constants thyname           = Term.thy_consts thyname
fun thy_parents thyname             = snd (Graph.first
                                           (equal thyname o thyid_name o fst))
fun thy_axioms (th:segment)         = filter (is_axiom o #2)   (#facts th)
fun thy_theorems (th:segment)       = filter (is_theorem o #2) (#facts th)
fun thy_defns (th:segment)          = filter (is_defn o #2)    (#facts th)
fun thy_addons (th:segment)         = #adjoin th

fun stamp thyname =
  let val (_,sec,usec) = dest_thyid (fst (Graph.first
                          (equal thyname o thyid_name o fst)))
  in
    Portable.mk_time {sec = sec, usec = usec}
  end;

local fun norm_name "-" = CTname()
        | norm_name s = s
      fun grab_item style name alist =
        case Lib.assoc1 name alist
         of SOME (_,th) => th
          | NONE => raise ERR style
                      ("couldn't find "^style^" named "^Lib.quote name)
in
 val types            = thy_types o norm_name
 val constants        = thy_constants o norm_name
 fun get_parents s    = if norm_name s = CTname()
                         then Graph.fringe() else thy_parents s
 val parents          = map thyid_name o get_parents
 val ancestry         = map thyid_name o Graph.ancestryl o get_parents
 fun current_axioms() = map drop_pthmkind (thy_axioms (theCT()))
 fun current_theorems() = map drop_pthmkind (thy_theorems (theCT()))
 fun current_definitions() = map drop_pthmkind (thy_defns (theCT()))
 fun current_ML_deps() = HOLset.listItems (#mldeps (theCT()))
end;

(*---------------------------------------------------------------------------*
 * Is a segment empty?                                                       *
 *---------------------------------------------------------------------------*)

fun empty_segment ({thid,facts, ...}:segment) =
  let val thyname = thyid_name thid
  in null (thy_types thyname) andalso
     null (thy_constants thyname) andalso
     null facts
  end;

(*---------------------------------------------------------------------------*
 *              ADDING TO THE SEGMENT                                        *
 *---------------------------------------------------------------------------*)

fun add_type {name,theory,arity} thy =
    (Type.prim_new_type {Thy = theory, Tyop = name} arity; thy)

fun add_term {name,theory,htype} thy =
    (Term.prim_new_const {Thy = theory, Name = name} htype; thy)

local fun pluck1 x L =
        let fun get [] A = NONE
              | get ((p as (x',_))::rst) A =
                if x=x' then SOME (p,rst@A) else get rst (p::A)
        in get L []
        end
      fun overwrite (p as (s,f)) l =
       case pluck1 s l of
         NONE => p::l
       | SOME ((_,f'),l') => p::l'
in
fun add_fact th (seg : segment) =
    update_seg seg (U #facts (overwrite th (#facts seg))) $$
end;

fun new_addon a (s as {adjoin, ...} : segment) =
  update_seg s (U #adjoin (a::adjoin)) $$

fun add_ML_dep s (seg as {mldeps, ...} : segment) =
  update_seg seg (U #mldeps (HOLset.add(mldeps, s))) $$

local fun plucky x L =
       let fun get [] A = NONE
             | get ((p as (x',_))::rst) A =
                if x=x' then SOME (rev A, p, rst) else get rst (p::A)
       in get L []
       end
in
fun set_MLbind (s1,s2) (seg as {facts, ...} : segment) =
    case plucky s1 facts of
      NONE => (WARN "set_MLbind" (Lib.quote s1^" not found in current theory");
               seg)
    | SOME (X,(_,b),Y) =>
      update_seg seg (U #facts (X@((s2,b)::Y))) $$
end;

(*---------------------------------------------------------------------------
            Deleting from the segment
 ---------------------------------------------------------------------------*)

fun del_type (name,thyname) thy =
    (Type.prim_delete_type {Thy = thyname, Tyop = name}; thy)

(*---------------------------------------------------------------------------
        Remove a constant from the signature.
 ---------------------------------------------------------------------------*)

fun del_const (name,thyname) thy =
    (Term.prim_delete_const {Thy = thyname, Name = name} ; thy)

fun del_binding name (s as {facts,...} : segment) =
  update_seg s (U #facts (filter (fn (s, _) => not(s=name)) facts)) $$;

(*---------------------------------------------------------------------------
   Clean out the segment. Note: this clears out the segment, and the
   signatures, but does not alter the theory graph. The segment will
   still be there, with its parents.
 ---------------------------------------------------------------------------*)

fun zap_segment s (thy : segment) =
    (Type.del_segment s; Term.del_segment s;
     {adjoin=[], facts=[],thid= #thid thy, thydata = empty_datamap,
      mldeps = HOLset.empty String.compare})

(*---------------------------------------------------------------------------
       Wrappers for functions that alter the segment.
 ---------------------------------------------------------------------------*)

local
  fun inCT f arg = makeCT(f arg (theCT()))
  open TheoryDelta
  fun add_factCT p = (inCT add_fact p;
                      call_hooks (TheoryDelta.NewBinding p))
in
  val add_typeCT        = inCT add_type
  val add_termCT        = inCT add_term
  fun add_axiomCT(r,ax) = add_factCT (Nonce.dest r, Axiom(r,ax))
  fun add_defnCT(s,def) = add_factCT (s,  Defn def)
  fun add_thmCT(s,th)   = add_factCT (s,  Thm th)
  val add_ML_dependency = inCT add_ML_dep

  fun delete_type n     = (inCT del_type  (n,CTname());
                           call_hooks
                               (DelTypeOp{Name = n, Thy = CTname()}))
  fun delete_const n    = (inCT del_const (n,CTname());
                           call_hooks
                               (DelConstant{Name = n, Thy = CTname()}))

  fun delete_binding s  = (inCT del_binding s; call_hooks (DelBinding s))

  fun set_MLname s1 s2  = inCT set_MLbind (s1,s2)
  val adjoin_to_theory  = inCT new_addon
  val zapCT             = inCT zap_segment

end;

local
  structure PP = HOLPP
  fun pp_lines l =
    PP.block PP.CONSISTENT 0
       (List.concat (map (fn s => [PP.add_string s, PP.NL]) l))
  val is_empty =
    fn [] => true
     | [s] => s = "none" orelse List.all Char.isSpace (String.explode s)
     | _ => false
  fun pp l = if is_empty l then NONE else SOME (fn _ => pp_lines l)
  val qpp = pp o Portable.quote_to_string_list
in
  fun quote_adjoin_to_theory q1 q2 =
    adjoin_to_theory {sig_ps = qpp q1, struct_ps = qpp q2}
end

(*---------------------------------------------------------------------------*
 *            INSTALLING CONSTANTS IN THE CURRENT SEGMENT                    *
 *---------------------------------------------------------------------------*)

fun new_type (Name,Arity) =
 (if Lexis.allowed_type_constant Name orelse
     not (!Globals.checking_type_names)
  then ()
  else WARN "new_type" (Lib.quote Name^" is not a standard type name")
  ; add_typeCT {name=Name, arity=Arity, theory = CTname()}
  ; call_hooks (TheoryDelta.NewTypeOp {Name = Name, Thy = CTname()}));

fun new_constant (Name,Ty) =
  (if Lexis.allowed_term_constant Name orelse
      not (!Globals.checking_const_names)
   then ()
   else WARN "new_constant" (Lib.quote Name^" is not a standard constant name")
   ; add_termCT {name=Name, theory=CTname(), htype=Ty}
   ; call_hooks (TheoryDelta.NewConstant {Name = Name, Thy = CTname()}))

(*---------------------------------------------------------------------------
     Install constants in the current theory, as part of loading a
     previously built theory from disk.
 ---------------------------------------------------------------------------*)

fun install_type(s,a,thy)   = add_typeCT {name=s, arity=a, theory=thy};
fun install_const(s,ty,thy) = add_termCT {name=s, htype=ty, theory=thy}


(*---------------------------------------------------------------------------
 * Is an object wellformed (current) wrt the symtab, i.e., have none of its
 * constants been re-declared after it was built? A constant is
 * up-to-date if either 1) it was not declared in the current theory (hence
 * it was declared in an ancestor theory and is thus frozen); or 2) it was
 * declared in the current theory and its witness is up-to-date.
 *
 * When a new entry is made in the theory, it is checked to see if it is
 * uptodate (or if its witnesses are). The "overwritten" bit of a segment
 * tells whether any element of the theory has been overwritten. If
 * overwritten is false, then the theory is uptodate. If we want to add
 * something to an uptodate theory, then no processing need be done.
 * Otherwise, we have to examine the item, and recursively any item it
 * depends on, to see if any constant or type constant occurring in it,
 * or any theorem it depends on, is outofdate. If so, then the item
 * will not be added to the theory.
 *
 * To clean up a theory with outofdate elements, use "scrub".
 *
 * To tell if an object is uptodate, we can't just look at it; we have
 * to recursively examine its witness(es). We can't just accept a witness
 * that seems to be uptodate, since its constants may be flagged as uptodate,
 * but some may depend on outofdate witnesses. The solution taken
 * here is to first set all constants in the segment signature to be
 * outofdate. Then a bottom-up pass is made. The "utd" flag in each
 * signature entry is used to cut off repeated recursive traversal, as in
 * dynamic programming. It holds the value "true" when the witness is
 * uptodate.
 *---------------------------------------------------------------------------*)

fun uptodate_thm thm =
    Lib.all uptodate_term (Thm.concl thm::Thm.hyp thm)
    andalso
    uptodate_axioms (Tag.axioms_of (Thm.tag thm))
and uptodate_axioms [] = true
  | uptodate_axioms rlist = let
      val axs = map (drop_Axkind o snd) (thy_axioms(theCT()))
    in
      (* tempting to call uptodate_thm here, but this would put us into a loop
         because axioms have themselves as tags, also unnecessary because
         axioms never have hypotheses (check type of new_axiom) *)
      Lib.all (uptodate_term o Thm.concl o Lib.C Lib.assoc axs) rlist
    end handle HOL_ERR _ => false

fun scrub_ax (s as {facts,...} : segment) =
   let fun check (_, Thm _ ) = true
         | check (_, Defn _) = true
         | check (_, Axiom(_,th)) = uptodate_term (Thm.concl th)
   in
      update_seg s (U #facts (List.filter check facts)) $$
   end

fun scrub_thms (s as {facts,...}: segment) =
   let fun check (_, Axiom _) = true
         | check (_, Thm th ) = uptodate_thm th
         | check (_, Defn th) = uptodate_thm th
   in
     update_seg s (U #facts (List.filter check facts)) $$
   end

fun scrub () = makeCT (scrub_thms (scrub_ax (theCT())))

fun scrubCT() = (scrub(); theCT());


(*---------------------------------------------------------------------------*
 *   WRITING AXIOMS, DEFINITIONS, AND THEOREMS INTO THE CURRENT SEGMENT      *
 *---------------------------------------------------------------------------*)

local
  fun check_name tempok (fname,s) =
    if Lexis.ok_sml_identifier s andalso
       not (Lib.mem s ["ref", "true", "false", "::", "nil", "="]) orelse
       tempok andalso is_temp_binding s
      then ()
    else raise ERR fname ("Can't use name " ^ Lib.mlquote s ^
                          " as a theory-binding")
  fun DATED_ERR f bindname = ERR f (Lib.quote bindname^" is out-of-date!")
  val save_thm_reporting = ref 1
  val _ = Feedback.register_trace ("Theory.save_thm_reporting",
                                   save_thm_reporting, 2)
  fun mesg_str th =
    let
      val tags = Lib.set_diff (fst (Tag.dest_tag (Thm.tag th))) ["DISK_THM"]
    in
      if List.null tags
        then "theorem"
      else if Lib.null_intersection tags ["fast_proof", "cheat"]
        then "ORACLE thm"
      else "CHEAT"
    end
  fun save_mesg s name =
    if !save_thm_reporting = 0 orelse
       !Globals.interactive andalso !save_thm_reporting < 2
      then ()
    else let
           val s = if !Globals.interactive then s
                   else StringCvt.padRight #"_" 13 (s ^ " ")
         in
           with_flag (MESG_to_string, Lib.I) HOL_MESG
             ("Saved " ^ s ^ " " ^ Lib.quote name ^ "\n")
         end
in
  fun save_thm (name, th) =
    let
      val th' = save_dep (CTname ()) th
    in
      check_name true ("save_thm", name)
      ; if uptodate_thm th' then add_thmCT (name, th')
        else raise DATED_ERR "save_thm" name
      ; save_mesg (mesg_str th') name
      ; th'
    end

  fun new_axiom (name,tm) =
    let
      val rname  = Nonce.mk name
      val axiom  = Thm.mk_axiom_thm (rname, tm)
      val axiom' = save_dep (CTname()) axiom
    in
      check_name false ("new_axiom",name)
      ; if uptodate_term tm then add_axiomCT (rname, axiom')
        else raise DATED_ERR "new_axiom" name
      ; axiom'
    end

  fun store_definition (name, def) =
    let
      val def' = save_dep (CTname ()) def
    in
      check_name true ("store_definition", name)
      ; uptodate_thm def' orelse raise DATED_ERR "store_definition" name
      ; add_defnCT (name, def')
      ; def'
    end
end;

(*---------------------------------------------------------------------------*
 * Adding a new theory into the current theory graph.                        *
 *---------------------------------------------------------------------------*)

fun set_diff a b = filter (fn x => not (Lib.op_mem thyid_eq x b)) a;
fun node_set_eq S1 S2 = null(set_diff S1 S2) andalso null(set_diff S2 S1);

fun link_parents thy plist =
 let val node = make_thyid thy
     val parents = map make_thyid plist
 in
 if Lib.all Graph.isin parents
 then if Graph.isin node
      then if node_set_eq parents (Graph.parents_of node) then ()
           else (HOL_MESG
                  "link_parents: the theory has two unequal sets of parents";
                 raise ERR "link_parents" "")
      else Graph.add (node,parents)
 else let val baddies = Lib.filter (not o Graph.isin) parents
          val names = map thyid_to_string baddies
    in HOL_MESG (String.concat
        ["link_parents: the following parents of ",
         Lib.quote (thyid_name node),
         "\n  should already be in the theory graph (but aren't): ",
         String.concat (commafy names)]);
       raise ERR "link_parents" ""
    end
 end;

fun incorporate_types thy tys =
  let fun itype (s,a) = (install_type(s,a,thy);())
  in List.app itype tys
  end;

fun incorporate_consts thy tyvector consts =
  let fun iconst(s,i) = (install_const(s,Vector.sub(tyvector,i),thy);())
  in List.app iconst consts
  end;

(* ----------------------------------------------------------------------
    Theory data functions

    In addition to the data in the current segment, we want to track the data
    associated with all previous segments.  We do this with another reference
    variable (yuck).
   ---------------------------------------------------------------------- *)

structure LoadableThyData =
struct

  type t = UniversalType.t
  type DataOps = {merge : t * t -> t, pp : t -> string,
                  read : (string -> term) -> string -> t option,
                  write : (term -> string) -> t -> string,
                  terms : t -> term list}
  val allthydata = ref (Binarymap.mkDict String.compare :
                        (string, ThyDataMap) Binarymap.dict)
  val dataops = ref (Binarymap.mkDict String.compare :
                     (string, DataOps) Binarymap.dict)

  fun segment_data {thy,thydataty} = let
    val {thydata,thid,...} = theCT()
    fun check_map m =
        case Binarymap.peek(m, thydataty) of
          NONE => NONE
        | SOME (Loaded value) => SOME value
        | SOME (Pending _) => raise ERR "segment_data"
                                        "Can't interpret pending loads"
  in
    if thyid_name thid = thy then
      (DPRINT
         (fn _ => "segment_data for " ^ thydataty ^
                  " coming from current_theory\n");
       check_map thydata)
    else
      case Binarymap.peek(!allthydata, thy) of
        NONE => NONE
      | SOME dmap => check_map dmap
  end

  fun segment_data_string (arg as {thy,thydataty}) =
      case Binarymap.peek (!dataops, thydataty) of
          SOME {pp,...} => Option.map pp (segment_data arg)
        | NONE => raise Fail ("No pp-fn for "^thydataty)

  fun write_data_update {thydataty,data} =
      case Binarymap.peek(!dataops, thydataty) of
        NONE => raise ERR "write_data_update"
                          ("No operations defined for "^thydataty)
      | SOME {merge,read,write,terms,pp} => let
          val (s as {thydata,...}) = theCT()
          open Binarymap
          fun updatemap inmap = let
            val newdata =
                case peek(inmap, thydataty) of
                  NONE => Loaded data
                | SOME (Loaded t) => Loaded (merge(t, data))
                | SOME (Pending ds) =>
                    raise Fail "write_data_update invariant failure"
            val _ = DPRINT
                      (fn () =>
                          let
                            val newdata_s =
                                case newdata of
                                    Loaded t => pp t
                                  | Pending ds => "Pending[" ^
                                                  String.concatWith
                                                    ", "
                                                    (List.map fst ds) ^ "]"
                          in
                            "write_data_update/" ^ thydataty ^ ": writing " ^
                            newdata_s ^ "\n"
                          end)
          in
            insert(inmap,thydataty,newdata)
          end
        in
          makeCT (update_seg s (U #thydata (updatemap thydata)) $$)
        end

  fun set_theory_data {thydataty,data} =
      case Binarymap.peek(!dataops, thydataty) of
        NONE => raise ERR "set_theory_data"
                          ("No operations defined for "^thydataty)
      | SOME{read,write,pp,...} => let
          val (s as {thydata,...}) = theCT()
          open Binarymap
        in
          DPRINT (fn _ => "Updating "^thydataty^" in segment with value " ^
                          pp data ^ "\n");
          makeCT
            (update_seg s
                        (U #thydata (insert(thydata, thydataty, Loaded data)))
                        $$)
        end

  fun temp_encoded_update {thy, thydataty, data, read = tmread} = let
    val (s as {thydata, thid, ...}) = theCT()
    open Binarymap
    fun updatemap inmap = let
      val baddecode = ERR "temp_encoded_update"
                          ("Bad decode for "^thydataty^" ("^data^")")
      val newdata =
        case (peek(inmap, thydataty), peek(!dataops,thydataty)) of
          (NONE, NONE) => Pending [(data,tmread)]
        | (NONE, SOME {read,...}) =>
            Loaded (valOf (read tmread data) handle Option => raise baddecode)
        | (SOME (Loaded t), NONE) =>
             raise Fail "temp_encoded_update invariant failure 1"
        | (SOME (Loaded t), SOME {merge,read,...}) =>
             Loaded (merge(t, valOf (read tmread data)
                              handle Option => raise baddecode))
        | (SOME (Pending ds), NONE) => Pending ((data,tmread)::ds)
        | (SOME (Pending _), SOME _) =>
             raise Fail "temp_encoded_update invariant failure 2"
    in
      insert(inmap, thydataty, newdata)
    end
  in
    if thy = thyid_name thid then
      makeCT (update_seg s (U #thydata (updatemap thydata)) $$)
    else let
      val newsubmap =
          case peek (!allthydata, thy) of
              NONE => updatemap empty_datamap
            | SOME dm => updatemap dm
    in
      allthydata := insert(!allthydata, thy, newsubmap)
    end
  end

fun update_pending (m,r) thydataty = let
  open Binarymap
  fun update1 inmap =
      case peek(inmap, thydataty) of
        NONE => inmap
      | SOME (Loaded t) =>
          raise ERR "LoadableThyData.new"
                    ("Theory data name " ^ Lib.quote thydataty ^
                     " already in use.")
      | SOME (Pending []) => raise Fail "update_pending invariant failure 2"
      | SOME (Pending (ds as (_ :: _))) => let
          fun foldthis ((d,tmrd),acc) = m(acc, valOf (r tmrd d))
          val ds' = List.rev ds
          val (d1,tmrd1) = hd ds'
        in
          insert(inmap,thydataty,
                 Loaded (List.foldl foldthis (valOf (r tmrd1 d1)) (tl ds')))
        end
  fun foldthis (k,v,acc) = insert(acc,k,update1 v)
  val _ = allthydata := Binarymap.foldl foldthis
                                        (Binarymap.mkDict String.compare)
                                        (!allthydata)
  val (seg as {thydata,...}) = theCT()
in
  makeCT (update_seg seg (U #thydata (update1 thydata)) $$)
end

fun 'a new {thydataty, merge, read, write, terms, pp} = let
  val (mk : 'a -> t, dest) = UniversalType.embed ()
  fun vdest t = valOf (dest t)
  fun merge' (t1, t2) = mk(merge(vdest t1, vdest t2))
  fun read' tmread s = Option.map mk (read tmread s)
  fun write' tmwrite t = write tmwrite (vdest t)
  fun terms' t = terms (vdest t)
  fun pp' t = pp (vdest t)
in
  update_pending (merge',read') thydataty;
  dataops := Binarymap.insert(!dataops, thydataty,
                              {merge=merge', read=read', write=write',
                               terms=terms', pp=pp'});
  (mk,dest)
end


end (* struct *)



(*---------------------------------------------------------------------------*
 *         PRINTING THEORIES OUT AS ML STRUCTURES AND SIGNATURES.            *
 *---------------------------------------------------------------------------*)

fun theory_out p ostrm =
 let
 in
   PP.prettyPrint ((fn s => TextIO.output(ostrm,s)), 75) p
     handle e => (Portable.close_out ostrm; raise e);
   TextIO.closeOut ostrm
 end;

fun unkind facts =
  List.foldl (fn ((s,Axiom (_,th)),(A,D,T)) => ((s,th)::A,D,T)
               | ((s,Defn th),(A,D,T))     => (A,(s,th)::D,T)
               | ((s,Thm th),(A,D,T))     => (A,D,(s,th)::T)) ([],[],[]) facts;

(* automatically reverses the list, which is what is needed. *)

fun unadjzip [] A = A
  | unadjzip ({sig_ps,struct_ps}::t) (l1,l2) =
       unadjzip t (sig_ps::l1, struct_ps::l2)


(*---------------------------------------------------------------------------
    We always export the theory, except if it is the initial theory (named
    "scratch") and the initial theory is empty. If the initial theory is
    *not* empty, i.e., the user made some definitions, or stored some
    theorems or whatnot, then the initial theory will be exported.
 ----------------------------------------------------------------------------*)

fun total_cpu {usr,sys} = Time.+(usr,sys)
val new_theory_time = ref (total_cpu (Timer.checkCPUTimer Globals.hol_clock))

val report_times = ref true
val _ = Feedback.register_btrace ("report_thy_times", report_times)

local
  val mesg = Lib.with_flag(Feedback.MESG_to_string, Lib.I) HOL_MESG
  fun maybe_log_time_to_disk thyname timestr = let
    open FileSys
    fun concatl pl = List.foldl (fn (p2,p1) => Path.concat(p1,p2))
                                (hd pl) (tl pl)
    val filename_opt = let
      val build = Systeml.build_log_file
      val currentdir = Systeml.make_log_file
    in
      List.find (fn s => access(s, [A_WRITE])) [build, currentdir]
    end
  in
    case filename_opt of
      SOME s => let
        val fs = TextIO.openAppend s
      in
        TextIO.output(fs, thyname ^ " " ^ timestr ^ "\n");
        TextIO.closeOut fs
      end
    | NONE => ()
  end
in
fun export_theory () = let
  val _ = call_hooks (TheoryDelta.ExportTheory (current_theory()))
  val {thid,facts,adjoin,thydata,mldeps,...} = scrubCT()
  val concat = String.concat
  val thyname = thyid_name thid
  val name = thyname^"Theory"
  val (A,D,T) = unkind facts
  val (sig_ps, struct_ps) = unadjzip adjoin ([],[])
  val sigthry = {name = thyname,
                 parents = map thyid_name (Graph.fringe()),
                 axioms = A,
                 definitions = D,
                 theorems = T,
                 sig_ps = sig_ps}
  fun mungethydata dmap = let
    fun foldthis (k,v,acc as (tmlist,dict)) =
        case v of
          Loaded t =>
          let
            val {write,terms,...} = Binarymap.find(!LoadableThyData.dataops, k)
              handle NotFound => raise ERR "export_theory"
                                       ("Couldn't find thydata ops for "^k)

          in
            (terms t @ tmlist,
             Binarymap.insert(dict,k,(fn wrtm => write wrtm t)))
          end
        | _ => acc
  in
    Binarymap.foldl foldthis ([], Binarymap.mkDict String.compare) dmap
  end
  val structthry =
      {theory = dest_thyid thid,
       parents = map dest_thyid (Graph.fringe()),
       types = thy_types thyname,
       constants = Lib.mapfilter Term.dest_const (thy_constants thyname),
       axioms = A,
       definitions = D,
       theorems = T,
       struct_ps = struct_ps,
       thydata = mungethydata thydata,
       mldeps = HOLset.listItems mldeps}
  fun filtP s = not (Lexis.ok_sml_identifier s) andalso
                not (is_temp_binding s)
 in
   case filter filtP (map fst (A@D@T)) of
     [] =>
     (let val ostrm1 = Portable.open_out(concat["./",name,".sig"])
          val ostrm2 = Portable.open_out(concat["./",name,".sml"])
          val ostrm3 = Portable.open_out(concat["./",name,".dat"])
          val time_now = total_cpu (Timer.checkCPUTimer Globals.hol_clock)
          val time_since = Time.-(time_now, !new_theory_time)
          val tstr = Lib.time_to_string time_since
      in
        mesg ("Exporting theory "^Lib.quote thyname^" ... ");
        theory_out (TheoryPP.pp_sig (!pp_thm) sigthry) ostrm1;
        theory_out (TheoryPP.pp_struct structthry) ostrm2;
        theory_out (TheoryPP.pp_thydata structthry) ostrm3;
        mesg "done.\n";
        if !report_times then
          (mesg ("Theory "^Lib.quote thyname^" took "^ tstr ^ " to build\n");
           maybe_log_time_to_disk thyname (Time.toString time_since))
        else ()
      end
        handle e => (Lib.say "\nFailure while writing theory!\n"; raise e))

   | badnames =>
     (HOL_MESG
        (String.concat
           ["\nThe following ML binding names in the theory to be exported:\n",
            String.concat (Lib.commafy (map Lib.quote badnames)),
            "\n are not acceptable ML identifiers.\n",
            "   Use `set_MLname <bad> <good>' to change each name."]);
        raise ERR "export_theory" "bad binding names")
end
end;


(* ----------------------------------------------------------------------
    "on load" stuff
   ---------------------------------------------------------------------- *)

fun load_complete thyname =
    call_hooks (TheoryDelta.TheoryLoaded thyname)


(* ----------------------------------------------------------------------
     Allocate a new theory segment over an existing one. After
     that, initialize any registered packages. A package registers
     with a call to "register_hook".
    ---------------------------------------------------------------------- *)

fun new_theory str =
    if not(Lexis.ok_identifier str) then
      raise ERR "new_theory"
                ("proposed theory name "^Lib.quote str^" is not an identifier")
    else let
        val thy as {thid, ...} = theCT()
        val thyname = thyid_name thid
        val tdelta = TheoryDelta.NewTheory{oldseg=thyname,newseg=str}
        fun mk_thy () = (HOL_MESG ("Created theory "^Lib.quote str);
                         makeCT(fresh_segment str);
                         call_hooks tdelta)
        val _ =
            new_theory_time := total_cpu (Timer.checkCPUTimer Globals.hol_clock)
      in
        if str=thyname then
          (HOL_MESG("Restarting theory "^Lib.quote str);
           zapCT str;
           call_hooks tdelta)
        else if mem str (ancestry thyname) then
          raise ERR"new_theory" ("theory: "^Lib.quote str^" already exists.")
        else if thyname="scratch" andalso empty_segment thy then
          mk_thy()
        else
          (export_theory ();
           Graph.add (thid, Graph.fringe()); mk_thy ())
      end


(* ----------------------------------------------------------------------
    Function f tries to extend current theory. If that fails then
    revert to previous state.

    We do not (yet) track changes to the state used by adjoin_to_theory or
    any hooks, though the hooks should see the changes adding and
    removing things from the "signature".
   ---------------------------------------------------------------------- *)

fun try_theory_extension f x =
  let open Term
      val tnames1 = map fst (types"-")
      val cnames1 = map (fst o dest_const) (constants"-")
      fun revert _ =
        let val tnames2 = map fst (types"-")
            val cnames2 = map (fst o dest_const) (constants"-")
            val new_tnames = Lib.set_diff tnames2 tnames1
            val new_cnames = Lib.set_diff cnames2 cnames1
        in map delete_type new_tnames;
           map delete_const new_cnames;
           scrub()
        end
  in
    f x handle e => (revert(); raise e)
  end;

structure Definition =
struct
(* ----------------------------------------------------------------------
   DESCRIPTION   : Principles of type definition, constant specification
                   and constant definition. Almost the same as in hol88,
                   except that parsing status is not dealt with by the
                   functions in this module (at this stage, the parser
                   hasn't been compiled yet). A further difference is
                   the principle of constant definition is not derived
                   from constant specification, as in hol88. The
                   principle of definition has also been changed to be
                   simpler than that of hol88.

   AUTHOR        : (c) Mike Gordon, University of Cambridge
   TRANSLATOR    : Konrad Slind, University of Calgary
   DATE          : September 11, 1991  -- translated
   DATE          : October 1, 2000     -- union of previous 3 modules
   ---------------------------------------------------------------------- *)

val ERR       = mk_HOL_ERR "Definition";
val TYDEF_ERR = ERR "new_type_definition"
val DEF_ERR   = ERR "new_definition"
val SPEC_ERR  = ERR "new_specification";

val TYDEF_FORM_ERR = TYDEF_ERR "expected a theorem of the form \"?x. P x\"";
val DEF_FORM_ERR   = DEF_ERR   "expected a term of the form \"v = M\"";

(*---------------------------------------------------------------------------
      Misc. utilities. There are some local definitions of syntax
      operations, since we delay defining all the basic formula
      operations until after boolTheory is built.
 ---------------------------------------------------------------------------*)

fun mk_exists (absrec as (Bvar,_)) =
  mk_comb(mk_thy_const{Name="?",Thy="bool", Ty= (type_of Bvar-->bool)-->bool},
          mk_abs absrec)

fun dest_exists M =
 let val (Rator,Rand) = with_exn dest_comb M (TYDEF_ERR"dest_exists")
 in case total dest_thy_const Rator
     of SOME{Name="?",Thy="bool",...} => dest_abs Rand
      | otherwise => raise TYDEF_ERR"dest_exists"
 end

fun nstrip_exists 0 t = ([],t)
  | nstrip_exists n t =
     let val (Bvar, Body) = dest_exists t
         val (l,t'') = nstrip_exists (n-1) Body
     in (Bvar::l, t'')
     end;

fun mk_eq (lhs,rhs) =
 let val ty = type_of lhs
     val eq = mk_thy_const{Name="=",Thy="min",Ty=ty-->ty-->bool}
 in list_mk_comb(eq,[lhs,rhs])
 end;

fun dest_eq M =
  let val (Rator,r) = dest_comb M
      val (eq,l) = dest_comb Rator
  in case dest_thy_const eq
      of {Name="=",Thy="min",...} => (l,r)
       | _ => raise ERR "dest_eq" "not an equality"
  end;

fun check_null_hyp th f =
  if null(Thm.hyp th) then ()
  else raise f "theorem must have no assumptions";

fun check_free_vars tm f =
  case free_vars tm
   of [] => ()
    | V  => raise f (String.concat
            ("Free variables in rhs of definition: "
             :: commafy (map (Lib.quote o fst o dest_var) V)));

fun check_tyvars body_tyvars ty f =
 case Lib.set_diff body_tyvars (type_vars ty)
  of [] => ()
   | extras =>
      raise f (String.concat
         ("Unbound type variable(s) in definition: "
           :: commafy (map (Lib.quote o dest_vartype) extras)));

val new_definition_hook = ref
    ((fn tm => ([], tm)),
     (fn (V,th) =>
       if null V then th
       else raise ERR "new_definition" "bare post-processing phase"));

fun okChar c = Char.isGraph c andalso c <> #"(" andalso c <> #")"

fun check_name princ_name name =
  if CharVector.all okChar name then true
  else raise ERR
             princ_name
             ("Entity name >"^name^"< includes non-printable/bad character")

(*---------------------------------------------------------------------------*)
(*                DEFINITION PRINCIPLES                                      *)
(*---------------------------------------------------------------------------*)

fun new_type_definition (name,thm) = let
  val Thy = current_theory()
  val _ = is_temp_binding name orelse check_name "new_type_definition" name
  val tydef = Thm.prim_type_definition({Thy = Thy, Tyop = name}, thm)
 in
   store_definition (name^"_TY_DEF", tydef) before
   call_hooks (TheoryDelta.NewTypeOp{Name = name, Thy = Thy})
 end
 handle e => raise (wrap_exn "Theory.Definition" "new_type_definition" e);

fun gen_new_specification(name, th) = let
  val thy = current_theory()
  val (cnames,def) = Thm.gen_prim_specification thy th
 in
  store_definition (name, def) before
  List.app (fn s => call_hooks (TheoryDelta.NewConstant{Name=s, Thy=thy}))
           cnames
 end
 handle e => raise (wrap_exn "Definition" "gen_new_specification" e);

fun new_definition(name,M) =
 let val (dest,post) = !new_definition_hook
     val (V,eq)      = dest M
     val (nm, _)     = eq |> dest_eq |> #1 |> dest_var
                          handle HOL_ERR _ =>
                                 raise ERR "Definition.new_definition"
                                       "Definition not an equality"
     val _           = is_temp_binding name orelse
                       check_name "new_definition" nm
     val Thy         = current_theory()
     val (cn,def_th) = Thm.gen_prim_specification Thy (Thm.ASSUME eq)
     val Name        = case cn of [Name] => Name | _ => raise Match
 in
   store_definition (name, post(V,def_th)) before
   call_hooks (TheoryDelta.NewConstant{Name=Name, Thy=Thy})
 end
 handle e => raise (wrap_exn "Definition" "new_definition" e);

fun new_specification (name, cnames, th) = let
  val thy   = current_theory()
  val _     = is_temp_binding name orelse
              List.all (check_name "new_specification") cnames
  val def   = Thm.prim_specification thy cnames th
  val final = store_definition (name, def)
 in
  List.app (fn s => call_hooks (TheoryDelta.NewConstant{Name=s, Thy = thy}))
           cnames
  ; final
 end
 handle e => raise (wrap_exn "Definition" "new_specification" e);

end (* Definition struct *)

end (* Theory *)
