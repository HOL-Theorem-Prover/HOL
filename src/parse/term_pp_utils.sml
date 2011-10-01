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
  fun set {seen_frees,current_bvars,last_string} =
      {seen_frees=seen_frees, current_bvars=bvs,last_string=last_string}
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
  fun set {seen_frees,current_bvars,last_string} =
      {seen_frees = HOLset.add(seen_frees, v),
       current_bvars = current_bvars, last_string=last_string}
in
  fupdate set >> return ()
end

fun record_bvars newbvs p =
    getbvs >-
    (fn old => setbvs (HOLset.addList(old,newbvs)) >>
               p >- (fn pres => setbvs old >> return pres))


end (* struct *)
