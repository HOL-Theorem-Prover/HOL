structure term_pp_utils :> term_pp_utils =
struct

type term = Term.term
open smpp term_pp_types term_pp_utils_dtype

fun bv2term (Simple t) = t
  | bv2term (Restricted {Bvar,...}) = Bvar

fun PP_ERR fname str = Feedback.mk_HOL_ERR "term_pp_utils" fname str

infix >> >-

fun getbvs x =
  (fupdate (fn x => x) >-
   (fn (i:printing_info) => return (#current_bvars i)))
  x

val dflt_pinfo = {seen_frees = Term.empty_tmset,
                  current_bvars = Term.empty_tmset,
                  last_string = " ", in_gspec = false}

fun setbvs bvs = let
  fun set {seen_frees,current_bvars,last_string,in_gspec} =
      {seen_frees=seen_frees, current_bvars=bvs,last_string=last_string,
       in_gspec=in_gspec}
in
  fupdate set >> return ()
end

fun addbvs bvlist =
    getbvs >- (fn old => setbvs (HOLset.addList(old,bvlist)))

fun getfvs x =
    (fupdate (fn x => x) >-
     (fn (i:printing_info) => return (#seen_frees i)))
    x

fun spotfv v = let
  fun set {seen_frees,current_bvars,last_string,in_gspec} =
      {seen_frees = HOLset.add(seen_frees, v),
       current_bvars = current_bvars, last_string=last_string,
       in_gspec = in_gspec}
in
  fupdate set >> return ()
end

fun record_bvars newbvs p =
    getbvs >-
    (fn old => setbvs (HOLset.addList(old,newbvs)) >>
               p >- (fn pres => setbvs old >> return pres))

fun get_gspec x =
    (fupdate (fn x => x) >-
     (fn (i : printing_info) => return (#in_gspec i))) x

fun set_gspec p = let
  fun set b {in_gspec,current_bvars,seen_frees,last_string} =
      {in_gspec = b, current_bvars = current_bvars, seen_frees = seen_frees,
       last_string = last_string}
in
  get_gspec >-
  (fn old => fupdate (set true) >> p >-
   (fn pval => fupdate (set old) >> return pval))
end

fun decdepth n = if n < 0 then n else n - 1

fun mk_pair (t1,t2) = let
  open HolKernel
  val fsty = Term.type_of t1
  val sndty = Term.type_of t2
  val commaty = fsty --> sndty -->
                mk_thy_type{Tyop="prod",Thy="pair",Args=[fsty,sndty]}
  val c = mk_thy_const{Name=",", Thy="pair", Ty = commaty}
in
  list_mk_comb(c,[t1,t2])
end;

  (* This code will print paired abstractions "properly" only if
        1. the term has a constant in the right place, and
        2. that constant maps to the name "UNCURRY" in the overloading map.
     These conditions are checked in the call to grammar_name.

     We might vary this.  In particular, in 2., we could check to see
     name "UNCURRY" maps to a term (looking at the overload map in the
     reverse direction).

     Another option again might be to look to see if the term is a
     constant whose real name is UNCURRY, and if this term also maps
     to the name UNCURRY.  This last used to be the actual
     implementation, but it's hard to do this in the changed world
     (since r6355) of "syntactic patterns" because of the way
     overloading resolution can create fake constants (concealing true
     names) before this code gets a chance to run.

     The particular choice made above means that the printer does the
     'right thing'
       (prints `(\(x,y). x /\ y)` as `pair$UNCURRY (\x y. x /\ y)`)
     if given a paired abstraction to print wrt an "earlier" grammar,
     such boolTheory.bool_grammars. *)

fun pp_dest_abs G tm =
  let
    open HolKernel
    fun recurse tm =
      case dest_term tm of
          LAMB p => p
        | COMB(Rator,Rand) =>
          let
            val _ =
                term_grammar.grammar_name G Rator = SOME "UNCURRY" orelse
                raise PP_ERR "pp_dest_abs" "term not an abstraction"
            val (v1, body0) = recurse Rand
            val (v2, body) = recurse body0
          in
            (mk_pair(v1, v2), body)
          end
        | _ => raise PP_ERR "pp_dest_abs" "term not an abstraction"
  in
    recurse tm
  end

fun pp_is_abs G tm = Portable.can (pp_dest_abs G) tm


fun has_name G s tm = (term_grammar.grammar_name G tm = SOME s)

fun dest_vstruct G {binder=bnder,restrictor=res} t =
  let
    open HolKernel
    val my_is_abs = pp_is_abs G
    val my_dest_abs = pp_dest_abs G
  in
    case bnder of
      NONE =>
      let
      in
        case (Lib.total (pp_dest_abs G) t, res) of
            (SOME (bv, body), _) => (Simple bv, body)
          | (NONE, NONE) =>
            raise PP_ERR "dest_vstruct" "term not an abstraction"
          | (NONE, SOME s) =>
            let
            in
              case dest_term t of
                  COMB (Rator, Rand) =>
                  let
                  in
                    case dest_term Rator of
                        COMB(rator1, rand1) =>
                        if has_name G s rator1 andalso my_is_abs Rand then
                          let
                            val (bv, body) = my_dest_abs Rand
                          in
                            (Restricted{Bvar = bv, Restrictor = rand1}, body)
                          end
                        else
                          raise PP_ERR "dest_vstruct" "term not an abstraction"
                      | _ => raise PP_ERR "dest_vstruct"
                                   "term not an abstraction"
                  end
                | _ => raise PP_ERR "dest_vstruct" "term not an abstraction"
            end
      end
    | SOME s =>
      let
      in
        case (dest_term t) of
            COMB(Rator,Rand) =>
            let
            in
              if has_name G s Rator andalso my_is_abs Rand then
                let
                  val (bv, body) = my_dest_abs Rand
                in
                  (Simple bv, body)
                end
              else
                case res of
                  NONE => raise PP_ERR "dest_vstruct" "term not an abstraction"
                | SOME s => let
                  in
                    case (dest_term Rator) of
                      COMB(rator1, rand1) =>
                      if has_name G s rator1 andalso my_is_abs Rand then let
                          val (bv, body) = my_dest_abs Rand
                        in
                            (Restricted{Bvar = bv, Restrictor = rand1}, body)
                        end
                      else
                        raise PP_ERR "dest_vstruct" "term not an abstraction"
                    | _ =>
                      raise PP_ERR "dest_vstruct" "term not an abstraction"
                  end
            end
          | _ => raise PP_ERR "dest_vstruct" "term not an abstraction"
      end
  end

fun strip_vstructs G bres tm =
  let
    fun strip acc t = let
      val (bvar, body) = dest_vstruct G bres t
    in
      strip (bvar::acc) body
    end handle Feedback.HOL_ERR _ => (List.rev acc, t)
  in
    strip [] tm
  end

end (* struct *)
