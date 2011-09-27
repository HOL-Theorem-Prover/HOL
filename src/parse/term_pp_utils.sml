structure term_pp_utils :> term_pp_utils =
struct

type term = Term.term
open smpp term_pp_types

infix >> >-

fun getbvs x =
  (fupdate (fn x => x) >-
   (fn (i:printing_info) => return (#current_bvars i)))
  x

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

end (* struct *)
