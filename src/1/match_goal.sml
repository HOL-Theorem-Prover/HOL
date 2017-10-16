structure match_goal :> match_goal =
struct

open HolKernel boolLib Streams

fun Redblackmap_contains (m,v) =
  let
    exception found
    val _ = Redblackmap.app (fn (_,v') => if v = v' then raise found else ()) m
  in false end
  handle found => true

val ERR = Feedback.mk_HOL_ERR"match_goal";

datatype name =
    Assumption of string option
  | Conclusion
  | Anything

type pattern = term quotation
type matcher = name * pattern * bool

               (* (name, assumption number) *)
type named_thms = (string, int) Redblackmap.dict
val (empty_named_thms:named_thms) = Redblackmap.mkDict String.compare;

(* If you want to be able to treat certain type variables as constants (e.g.,
   if they are in the goal) then you need to keep track of the avoid_tys/tyIds
   thing that raw_match uses. But we are not doing that. *)
type named_tms =
  ((term,term) subst) * ((hol_type,hol_type) subst)

val empty_named_tms : named_tms = ([],[])

type data = named_thms * named_tms

fun is_underscore v =
  case total dest_var v of NONE
    => raise(ERR"umatch""unexpected non-variable binding") (* should not happen *)
  | SOME (s,_) => String.isPrefix "_" s

val is_uvar = String.isSuffix "_" o #1 o dest_var

fun umatch avoid_tms ((tmS,tyS):named_tms) pat ob : named_tms =
  let
    val ((tmS',tmIds'),(tyS',_)) = raw_match [] avoid_tms pat ob (tmS,tyS)
                                   handle HOL_ERR _ => raise end_of_stream
    val tmS'' = List.filter (not o is_underscore o #redex) tmS'
    val _ = assert_exn (List.all (is_uvar o #redex)) tmS'' end_of_stream
    val _ = assert_exn (curry HOLset.isSubset tmIds') avoid_tms end_of_stream
  in
    (tmS'', tyS')
  end

fun umatch_subterms avoid_tms (ntms:named_tms) pat ob : unit -> named_tms stream =
  stream_append
    (fn () => Stream(umatch avoid_tms ntms pat ob,empty_stream))
    (fn () =>
      (case dest_term ob of
         COMB(t1,t2) =>
           stream_append
             (umatch_subterms avoid_tms ntms pat t1)
             (umatch_subterms avoid_tms ntms pat t2)
       | LAMB(v,b) =>
           umatch_subterms (HOLset.add(avoid_tms,v)) ntms pat b
       | _ => empty_stream)
      ())

fun preprocess_matcher fvs =
  fn (nm,q,b):matcher => (nm, Parse.parse_in_context fvs q, b)

type mg_tactic = (string -> thm) * (string -> term) -> tactic

fun match_single fvs ((asl,w):goal)
  ((nm,pat,whole):name * term * bool) ((nths,ntms):data) : unit -> data stream =
  let
    fun add_nth NONE _ = SOME nths
      | add_nth (SOME l) i =
        (case Redblackmap.peek(nths,l) of
           NONE =>
             if Redblackmap_contains(nths,i)
             then NONE
             else SOME (Redblackmap.insert(nths,l,i))
         | SOME j => if i = j then SOME nths else NONE)

    fun protect f NONE = K empty_stream
      | protect f (SOME x) = f x

    fun umatch_sing nths w =
      (fn() => Stream ((nths, umatch fvs ntms pat w),empty_stream))
    fun umatch_many nths w =
      stream_map (fn ntms => (nths,ntms)) (umatch_subterms fvs ntms pat w)
  in
    case nm of
      Conclusion =>
        if whole then
          umatch_sing nths w
        else
          umatch_many nths w
    | Assumption l =>
        if whole then
          stream_append_list (Lib.mapi (protect umatch_sing o add_nth l) asl)
        else
          stream_append_list (Lib.mapi (protect umatch_many o add_nth l) asl)
    | Anything =>
        if whole then
          stream_append_list (List.map (umatch_sing nths) (w::asl))
        else
          stream_append_list (List.map (umatch_many nths) (w::asl))
(*
          (el 2 (List.map (umatch_many nths) (w::asl))) ()

          val avoid_tms = fvs
          val ob = el 2 (w::asl)
          umatch_subterms fvs ntms pat (el 2 (w::asl))
          val
          el 2 (w::asl)
          pat
*)
  end

val tr1 = Substring.string o Substring.trimr 1 o Substring.full

fun match_tac (ms:matcher list,mtac:mg_tactic) (g as (asl,w):goal) : goal list * validation =
  let
    fun try_tactic ((thms,tms):data) : (unit -> (goal list * validation) stream) =
      let
        fun lookup_assum s =
          let
            val i = Redblackmap.find(thms,s)
            val tm = List.nth(#1 g,i)
          in ASSUME tm end
        val s =
          case tms of (tmS,tyS) =>
            #1 (norm_subst ((tmS,empty_tmset),(tyS,[])))
            |> List.map (fn {redex,residue} => (tr1(#1(dest_var redex)),residue))
        val tac = mtac (lookup_assum,Lib.C assoc s)
        val r = tac g
      in
        (fn()=>Stream (r,empty_stream))
      end
      handle HOL_ERR _ => empty_stream

    fun search [] d = try_tactic d
      | search (m::ms) d = stream_flat (stream_map (search ms) (m d))

    val fvs = FVL (w::asl) empty_tmset

    val matches = map (match_single fvs g o preprocess_matcher (HOLset.listItems fvs)) ms
  in
    (case search matches (empty_named_thms,empty_named_tms) () of
       Stream (x,_) => x)
    handle end_of_stream => raise ERR "match_tac" "no match"
  end

val first_match_tac = FIRST o List.map match_tac

fun match1_tac (x,t) = match_tac ([x],t)

fun kill_asm th = first_x_assum((K ALL_TAC) o assert (aconv (concl th) o concl))

fun drule_thm th = mp_tac o Lib.C MATCH_MP th

structure mg = struct
  type pattern = pattern
  type matcher = matcher

  fun a nm p = (Assumption (SOME nm),p,true)

  fun ua p = (Assumption NONE,p,true)
  val au = ua

  fun ab nm p = (Assumption (SOME nm),p,false)
  val ba = ab

  fun uab p = (Assumption NONE,p,false)
  val uba = uab
  val aub = uab
  val abu = uab
  val bau = uab
  val bua = uab

  fun c p = (Conclusion,p,true)

  fun cb p = (Conclusion,p,false)
  val bc = cb

  fun ac p = (Anything,p,true)
  val ca = ac

  fun acb p = (Anything,p,false)
  val abc = acb
  val bca = acb
  val cba = acb
  val cab = acb
  val bac = acb
end

end
