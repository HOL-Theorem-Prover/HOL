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

(*---------------------------------------------------------------------------

     Notes on the design.

  We provide a single current theory segment, which can be thought of as
  a scratchpad for building the segment that eventually gets exported.
  The following are the important components of a segment:

      - mini-signatures for the types and terms declared in the current
        segment

      - the unique id for the theory, along with its parents, which
        should be already-loaded theory segments.

      - the theory graph, used to enforce a prohibition on circular
        dependencies among segments.

      - the axioms, definitions, and theorems stored in the segment so far.

      - the status of the segment: is it consistent with disk (obscure),
        have items been deleted from the segment?

  The mini-signatures are held in Type.TypeSig and Term.TermSig,
  along with all the types and terms declared in ancestor theories.

  The parents of the segment are held in the theory graph.

  When a segment is exported, we dump everything in it to a text file
  representing an ML structure.

  Elements in the current segment can be deleted or overwritten, which
  makes consistency maintenance an issue.

 ---------------------------------------------------------------------------*)


structure Theory : RawTheory =
struct

open Feedback Lib KernelTypes ;

type ppstream = Portable.ppstream
type pp_type  = ppstream -> hol_type -> unit
type pp_thm   = ppstream -> thm -> unit
type num      = Arbnum.num

infix ##;

val ERR  = mk_HOL_ERR "Theory";
val WARN = HOL_WARNING "Theory";

type thy_addon = {sig_ps    : (ppstream -> unit) option,
                  struct_ps : (ppstream -> unit) option}


(* This reference is set in course of loading the parsing library *)

val pp_thm = ref (fn _:ppstream => fn _:thm => ())

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
   fun add (p:(thyid*thyid list)) = theGraph := (p :: !theGraph)
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

datatype thmkind = Thm of thm | Axiom of string ref * thm | Defn of thm

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

type segment = {thid  : thyid,                                 (* unique id  *)
                facts : (string * thmkind) list,    (* stored ax,def,and thm *)
                con_wrt_disk : bool,                (* consistency with disk *)
                adjoin       : thy_addon list}         (*  extras for export *)


(*---------------------------------------------------------------------------*
 *                 CREATE THE INITIAL THEORY SEGMENT.                        *
 *                                                                           *
 * The timestamp for a segment is its creation date. "con_wrt_disk" is       *
 * set to false because when a segment is created no corresponding file      *
 * gets created (the file is only created on export).                        *
 *---------------------------------------------------------------------------*)

fun fresh_segment s :segment =
   {thid=new_thyid s,  facts=[], con_wrt_disk=false, adjoin=[]};


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
fun thy_con_wrt_disk n (th:segment) = #con_wrt_disk th;


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

fun add_type {name,theory,arity} thy = let
  open Type KernelSig
in
  insert(typesig, {Name=name,Thy=theory}, arity);
  thy
end

fun add_term {name,theory,htype} thy = let
  open Term KernelSig
in
  insert(termsig, {Name=name,Thy=theory},
         (if Type.polymorphic htype then POLY else GRND) htype);
  thy
end

local fun pluck1 x L =
        let fun get [] A = NONE
              | get ((p as (x',_))::rst) A =
                if x=x' then SOME (p,rst@A) else get rst (p::A)
        in get L []
        end
      fun overwrite (p as (s,f)) l =
       case pluck1 s l
        of NONE => (p::l, false)
         | SOME ((_,f'),l') =>
            (case f'
              of Thm _ => (p::l', false)
               |  _    => (p::l', true))
in
fun add_fact (th as (s,_)) {thid, con_wrt_disk,facts,adjoin}
  = let val (X,b) = overwrite th facts
    in {facts=X, thid=thid, con_wrt_disk=con_wrt_disk, adjoin=adjoin}
    end
end;

fun new_addon a {thid, con_wrt_disk, facts, adjoin} =
    {adjoin = a::adjoin, facts=facts, thid=thid, con_wrt_disk=con_wrt_disk};

local fun plucky x L =
       let fun get [] A = NONE
             | get ((p as (x',_))::rst) A =
                if x=x' then SOME (rev A, p, rst) else get rst (p::A)
       in get L []
       end
in
fun set_MLbind (s1,s2) (rcd as {thid, con_wrt_disk,facts, adjoin})
 = case plucky s1 facts
   of NONE => (WARN "set_MLbind"
               (Lib.quote s1^" not found in current theory"); rcd)
    | SOME (X,(_,b),Y) =>
        {facts=X@((s2,b)::Y), adjoin=adjoin,thid=thid,
         con_wrt_disk=con_wrt_disk}
end;

(*---------------------------------------------------------------------------
            Deleting from the segment
 ---------------------------------------------------------------------------*)

fun del_type (name,thyname) thy = let
  open Type KernelSig
  val knm = {Name = name, Thy = thyname}
in
  retire_name(typesig, knm) handle KernelSig.NotFound =>
               WARN "del_type" (name_toString knm^" not found");
  thy
end

(*---------------------------------------------------------------------------
        Remove a constant from the signature.
 ---------------------------------------------------------------------------*)

fun del_const (name,thyname) thy = let
  open Term KernelSig
  val knm = {Name=name, Thy=thyname}
in
  retire_name(termsig,knm) handle KernelSig.NotFound =>
                  WARN "del_const" (name_toString knm^" not found");
  thy
end

fun del_binding name {thid,facts,con_wrt_disk,adjoin} =
  {facts = filter (fn (s, _) => not(s=name)) facts,
   thid=thid, adjoin=adjoin, con_wrt_disk=con_wrt_disk};

(*---------------------------------------------------------------------------
   Clean out the segment. Note: this clears out the segment, and the
   signatures, but does not alter the theory graph. The segment will
   still be there, with its parents.
 ---------------------------------------------------------------------------*)

fun zap_segment s {thid, con_wrt_disk, facts, adjoin} =
 let val _ = KernelSig.del_segment(Type.typesig, s)
     val _ = KernelSig.del_segment(Term.termsig, s)
 in {adjoin=[], facts=[], con_wrt_disk=con_wrt_disk, thid=thid}
 end;

fun set_consistency b {thid, con_wrt_disk, facts, adjoin} =
{con_wrt_disk=b, thid=thid,facts=facts, adjoin=adjoin}
;

(*---------------------------------------------------------------------------
       Wrappers for functions that alter the segment. Each time the
       segment is altered, the con_wrt_disk flag is set. This is a
       bit stewpid and I'd like to get rid of it.
 ---------------------------------------------------------------------------*)

local fun inCT f arg = makeCT(set_consistency false (f arg (theCT())))
in
  val add_typeCT        = inCT add_type
  val add_termCT        = inCT add_term
  fun add_axiomCT(r,ax) = inCT add_fact (!r, Axiom(r,ax))
  fun add_defnCT(s,def) = inCT add_fact (s,  Defn def)
  fun add_thmCT(s,th)   = inCT add_fact (s,  Thm th)

  fun delete_type n     = inCT del_type  (n,CTname())
  fun delete_const n    = inCT del_const (n,CTname())
  val delete_binding    = inCT del_binding

  fun set_MLname s1 s2  = inCT set_MLbind (s1,s2)
  val adjoin_to_theory  = inCT new_addon
  val zapCT             = inCT zap_segment

  fun set_ct_consistency b = makeCT(set_consistency b (theCT()))
end;


(*---------------------------------------------------------------------------*
 *            INSTALLING CONSTANTS IN THE CURRENT SEGMENT                    *
 *---------------------------------------------------------------------------*)

fun new_type (Name,Arity) =
 (if not (Lexis.allowed_type_constant Name) andalso
     !Globals.checking_type_names
   then WARN "new_type" (Lib.quote Name^" is not a standard type name")
   else ()
  ; add_typeCT {name=Name, arity=Arity, theory = CTname()};());

fun new_constant (Name,Ty) =
  (if not (Lexis.allowed_term_constant Name) andalso
     !Globals.checking_const_names
   then WARN "new_constant" (Lib.quote Name^" is not a standard constant name")
   else ()
   ; add_termCT {name=Name, theory=CTname(), htype=Ty}; ())

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

fun up2date_id id = KernelSig.uptodate_id id

fun uptodate_type ty =
    if Type.is_vartype ty then true
    else let val ((id,_),args) = Type.break_type ty
         in up2date_id id
            andalso Lib.all uptodate_type args
         end

fun uptodate_term tm =
    let open Term
    in if is_const tm
       then let val (id,ty) = break_const tm
            in up2date_id id andalso uptodate_type ty
            end
       else case (is_var tm, is_comb tm, is_abs tm)
             of (true,_,_) => uptodate_type (type_of tm)
              | (_,true,_) => uptodate_term (rator tm) andalso
                              uptodate_term (rand tm)
              | (_,_,true) => uptodate_term (bvar tm) andalso
                              uptodate_term (body tm)
              | otherwise  => raise ERR "uptodate_term" "unexpected case"
    end

fun uptodate_thm thm =
    Lib.all uptodate_term (Thm.concl thm::Thm.hyp thm)
    andalso
    up2date_axioms (Tag.axioms_of (Thm.tag thm))

and up2date_axioms [] = true
  | up2date_axioms rlist =
    let val axs = map (drop_Axkind o snd) (thy_axioms(theCT()))
    in Lib.all (uptodate_term o Thm.concl o Lib.C Lib.assoc axs) rlist
    end handle HOL_ERR _ => false

fun scrub_sig () =
    let
      open Type Term KernelSig
      fun appthis tab (knm,(kid,v)) =
          if not (uptodate_id kid) then retire_name(tab,knm)
          else ()
    in
      KernelSig.app (appthis typesig) typesig;
      KernelSig.app (appthis termsig) termsig
    end

fun scrub_ax {thid,con_wrt_disk,facts,adjoin} =
    let fun check (_, Thm _ ) = true
          | check (_, Defn _) = true
          | check (_, Axiom(_,th)) = uptodate_term (Thm.concl th)
    in
      {thid=thid, con_wrt_disk=con_wrt_disk, adjoin=adjoin,
       facts=Lib.gather check facts}
    end

fun scrub_thms {thid,con_wrt_disk,facts,adjoin} =
    let fun check (_, Axiom _) = true
          | check (_, Thm th ) = uptodate_thm th
          | check (_, Defn th) = uptodate_thm th
    in {thid=thid, con_wrt_disk=con_wrt_disk,adjoin=adjoin,
        facts=Lib.gather check facts}
    end

fun scrub () = let
  val  _  = scrub_sig ()
  val {thid,con_wrt_disk,facts,adjoin} =
      scrub_thms (scrub_ax (theCT()))
in
  makeCT {thid=thid, con_wrt_disk=con_wrt_disk, facts=facts, adjoin=adjoin}
end

fun scrubCT() = (scrub(); theCT());


(*---------------------------------------------------------------------------*
 *   WRITING AXIOMS, DEFINITIONS, AND THEOREMS INTO THE CURRENT SEGMENT      *
 *---------------------------------------------------------------------------*)

local fun check_name (fname,s) = ()
      fun DATED_ERR f bindname = ERR f (Lib.quote bindname^" is out-of-date!")
      val save_thm_reporting = ref 1
      val _ = Feedback.register_trace ("Theory.save_thm_reporting",
                                       save_thm_reporting, 2)
      val mesg = with_flag(MESG_to_string, Lib.I) HOL_MESG
in
fun save_thm (name,th) =
      (check_name ("save_thm",name)
       ; if uptodate_thm th then add_thmCT(name,th)
         else raise DATED_ERR "save_thm" name
       ; if !save_thm_reporting = 0 then ()
         else if not (!Globals.interactive) orelse !save_thm_reporting > 1
         then
           mesg ("Saved theorem " ^ name ^ "\n")
         else ()
       ; th)

fun new_axiom (name,tm) =
   let val rname = ref name
       val axiom = Thm.mk_axiom_thm (rname,tm)
       val  _ = check_name ("new_axiom",name)
   in if uptodate_term tm then add_axiomCT(rname,axiom)
      else raise DATED_ERR "new_axiom" name
      ; axiom
   end

fun store_type_definition(name, s, witness, def) =
  let val ()  = check_name ("store_type_definition",name)
  in
    if uptodate_thm def then ()
    else raise DATED_ERR "store_type_definition" name
    (* ; Type.TypeSig.add_witness (s,CTname(),witness) *)
    ; add_defnCT(name,def)
    ; def
  end

fun store_definition (name, slist, witness, def) =
  let val ()  = check_name ("store_definition",name)
  in
    if uptodate_thm def then () else raise DATED_ERR "store_definition" name
    (* ; map (fn s => Term.TermSig.add_witness (s,CTname(),witness)) slist *)
    ; add_defnCT(name,def)
    ; def
  end


end;

(*---------------------------------------------------------------------------*
 * Adding a new theory into the current theory graph.                        *
 *---------------------------------------------------------------------------*)

fun set_diff a b = gather (fn x => not (Lib.op_mem thyid_eq x b)) a;
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

fun incorporate_consts thy consts =
  let fun iconst(s,ty) = (install_const(s,ty,thy);())
  in List.app iconst consts
  end;


(*---------------------------------------------------------------------------*
 *         PRINTING THEORIES OUT AS ML STRUCTURES AND SIGNATURES.            *
 *---------------------------------------------------------------------------*)

fun theory_out f width {name,style} ostrm =
 let val ppstrm = Portable.mk_ppstream
                    {consumer = Portable.outputc ostrm,
                     linewidth=width, flush = fn () => Portable.flush_out ostrm}
 in f ppstrm handle e => (Portable.close_out ostrm; raise e);
    Portable.flush_ppstream ppstrm;
    Portable.close_out ostrm
 end;

fun unkind facts =
  List.foldl (fn ((s,Axiom (_,th)),(A,D,T)) => ((s,th)::A,D,T)
               | ((s,Defn th),(A,D,T))     => (A,(s,th)::D,T)
               | ((s,Thm th),(A,D,T))     => (A,D,(s,th)::T)) ([],[],[]) facts;

val utd_types  = Lib.gather uptodate_type;
val utd_consts = Lib.gather uptodate_term;
val utd_thms   = Lib.gather uptodate_thm;

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
val new_theory_time = ref (Timer.checkCPUTimer Globals.hol_clock)

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
fun export_theory () =
 let val {thid,con_wrt_disk,facts,adjoin} = scrubCT()
 in
 if con_wrt_disk
 then HOL_MESG ("\nTheory "^Lib.quote(thyid_name thid)^" already \
                 \consistent with disk, hence not exported.\n")
 else
 let val concat = String.concat
     val thyname = thyid_name thid
     val name = CTname()^"Theory"
     val (A,D,T) = unkind facts
     val (sig_ps, struct_ps) = unadjzip adjoin ([],[])
     val sigthry = {name = thyname,
                    parents = map thyid_name (Graph.fringe()),
                    axioms = A,
                    definitions = D,
                    theorems = T,
                    sig_ps = sig_ps}
     val structthry
     = {theory = dest_thyid thid,
        parents = map dest_thyid (Graph.fringe()),
        types = thy_types thyname,
        constants = Lib.mapfilter Term.dest_const (thy_constants thyname),
        axioms = A,
        definitions = D,
        theorems = T,
        struct_ps = struct_ps}
 in
   case filter (not o Lexis.ok_sml_identifier) (map fst (A@D@T))
    of [] =>
       (let val ostrm1 = Portable.open_out(concat["./",name,".sig"])
            val ostrm2 = Portable.open_out(concat["./",name,".sml"])
            val time_now = #usr (Timer.checkCPUTimer Globals.hol_clock)
            val time_since = Time.-(time_now, #usr (!new_theory_time))
            val tstr = Time.toString time_since
        in
          mesg ("Exporting theory "^Lib.quote thyname^" ... ");
          theory_out (TheoryPP.pp_struct structthry) 75
                     {name=name, style="structure"} ostrm2;
          theory_out (TheoryPP.pp_sig (!pp_thm) sigthry) 85
                     {name=name, style="signature"} ostrm1;
          set_ct_consistency true;
          mesg "done.\n";
          if !report_times then
            (mesg ("Theory "^Lib.quote thyname^" took "^ tstr ^"s to build\n");
             maybe_log_time_to_disk thyname tstr)
          else ()

        end
        handle e => (Lib.say "\nFailure while writing theory!\n"; raise e))

     | badnames => (HOL_MESG
          (String.concat
           ["\nThe following ML binding names in the theory to be exported:\n",
            String.concat (Lib.commafy (map Lib.quote badnames)),
            "\n are not acceptable ML identifiers.\n",
            "   Use `set_MLname <bad> <good>' to change each name."]);
          raise ERR "export_theory" "bad binding names")
 end
end end;

(*---------------------------------------------------------------------------*
 *    Allocate a new theory segment over an existing one. After              *
 *    that, initialize any registered packages. A package registers          *
 *    with a call to "after_new_theory".                                     *
 *---------------------------------------------------------------------------*)

local val initializers = ref [] : (string * string -> unit) list ref
in
fun after_new_theory f = (initializers := f :: !initializers)
fun initialize oldname =
  let val ct = current_theory()
      fun rev_app [] = ()
        | rev_app (f::rst) =
            (rev_app rst;
             f (oldname, ct) handle e =>
                let val errstr =
                   case e
                    of HOL_ERR r => !ERR_to_string r
                     | otherwise => General.exnMessage e
                in
                  WARN "new_theory.initialize"
                        ("an initializer failed with message: "
                         ^errstr^"\n ... continuing anyway. \n")
                end)
  in rev_app (!initializers)
  end
end;


fun new_theory str =
  if not(Lexis.ok_identifier str)
  then raise ERR "new_theory"
         ("proposed theory name "^Lib.quote str^" is not an identifier")
  else
  let val thy as {thid, facts, con_wrt_disk,adjoin} = theCT()
      val thyname = thyid_name thid
      fun mk_thy () = (HOL_MESG ("Created theory "^Lib.quote str);
                        makeCT(fresh_segment str); initialize thyname)
      val _ = new_theory_time := Timer.checkCPUTimer Globals.hol_clock
  in
   if str=thyname
      then (HOL_MESG("Restarting theory "^Lib.quote str);
            zapCT str; initialize thyname)
   else
   if mem str (ancestry thyname)
      then raise ERR"new_theory" ("theory: "^Lib.quote str^" already exists.")
   else
   if thyname="scratch" andalso empty_segment thy
      then mk_thy()
   else
    (if con_wrt_disk then () else export_theory ();
     Graph.add (thid, Graph.fringe()); mk_thy ()
    )
  end;


(*---------------------------------------------------------------------------*)
(* Function f tries to extend current theory. If that fails, or if predicate *)
(* is_ok (expected to be total) returns false, then revert to previous state *)
(* and return FAIL. Otherwise return PASS y, where y is what (if anything)   *)
(* f(x) returned.                                                            *)
(*                                                                           *)
(* We do not (yet) track changes to the state used by adjoin_to_theory or    *)
(* after_new_theory.                                                         *)
(*---------------------------------------------------------------------------*)

(* Overly complex definition commented out
fun attempt_theory_extension is_ok f x =
  let infix ?>
      open Term
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
    case (verdict f revert x ?> verdict (assert is_ok) revert)
     of PASS y => PASS y
      | FAIL((),e) => FAIL (wrap_exn "Theory" "attempt_theory_extension" e)
  end;
*)

fun try_theory_extension f x =
  let infix ?>
      open Term
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

end (* Theory *)
