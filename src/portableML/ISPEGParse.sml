structure ISPEGParse :> ISPEGParse =
struct

open ISPEG_dtype

val lpTOP = lpxGE 0

fun evalrel lrEQ p c = p = c
  | evalrel lrGE p c = p <= c
  | evalrel lrGT p c = p < c
  | evalrel lrOK p c = true

fun sloc [] = EOF
  | sloc ((_,l)::t) = l

fun loccol hl =
    case hl of
        POSN (r,c) => c
      | _ => 0

fun optmax f NONE NONE = NONE
  | optmax f NONE (SOME x) = SOME x
  | optmax f (SOME x) NONE = SOME x
  | optmax f (SOME x) (SOME y) = SOME (f x y)

fun MAXerr (e1 as (fl1, _)) (e2 as (fl2, _)) = if locsle fl1 fl2 then e2 else e1

fun conjpred lpBOT p = lpBOT
  | conjpred p lpBOT = lpBOT
  | conjpred (lpIval(m1, sz1)) (lpIval(m2, sz2)) =
    if m1 + sz1 < m2 orelse m2 + sz2 < m1 then lpBOT
    else let val l = Int.max(m1, m2)
         in
           lpIval (l, Int.min (m1 + sz1, m2 + sz2) - l)
         end
  | conjpred (lpIval(m, sz)) (lpxGE n) =
    if m + sz < n then lpBOT
    else let val l = Int.max(m, n)
         in lpIval (l, m + sz - l)
         end
  | conjpred (lpxGE n) (lpIval(m, sz)) =
    if m + sz < n then lpBOT
    else let val l = Int.max(m, n)
         in lpIval (l, m + sz - l)
         end
  | conjpred (lpxGE m) (lpxGE n) = lpxGE (Int.max(m, n))

fun rel_at_col lrOK c = lpTOP
  | rel_at_col lrGE c = lpIval(0, c)
  | rel_at_col lrGT c = if c = 0 then lpBOT else lpIval(0,c - 1)
  | rel_at_col lrEQ c = lpIval(c, 0)

fun poplist_aux acc (SOME h::t) = poplist_aux (h::acc) t
  | poplist_aux acc (NONE::t) = (acc,t)
  | poplist_aux acc [] = (acc,[])

fun poplistval f l =
    let val (values,rest) = poplist_aux [] l in SOME (f values)::rest end

fun comppred r lpBOT = lpBOT
  | comppred lrOK (lpIval _) = lpTOP
  | comppred lrOK (lpxGE _) = lpTOP
  | comppred lrEQ (p as (lpIval _)) = p
  | comppred lrEQ (p as (lpxGE _)) = p
  | comppred lrGE (lpIval(m, sz)) = lpIval(0, m + sz)
  | comppred lrGE (lpxGE _) = lpTOP
  | comppred lrGT (lpIval(m, sz)) =
    if m = 0 andalso sz = 0 then lpBOT else lpIval (0, m + sz - 1)
  | comppred lrGT (lpxGE _) = lpTOP

fun ispeg_exec (G:('a,'b,'c,'e)ispeg) (empty v) i p r eo errs k fk =
     if p = lpBOT then
       let
         val err = (sloc i,#iFAIL G)
       in
         applykont G fk i lpBOT r (optmax MAXerr eo (SOME err)) (err::errs)
       end
      else applykont G k i p (SOME v::r) eo errs
  | ispeg_exec G (tok(P, f, R)) [] p r eo errs k fk =
    let
        val err = (EOF,#tokEOF G)
      in
        applykont G fk [] p r (optmax MAXerr eo (SOME err)) (err::errs)
    end
  | ispeg_exec G (tok(P, f, R)) ((tk,Locs(l1, l2))::xs) p r eo errs k fk =
    if P tk then
      let val p' = conjpred p (rel_at_col R (loccol l1))
      in
        if p' = lpBOT then
          let val err = (Locs(l1, l2),#iFAIL G)
          in
            applykont G fk ((tk,Locs(l1, l2))::xs) p r
                      (optmax MAXerr eo (SOME err)) (err::errs)
          end
        else applykont G k xs p' (SOME (f (tk,Locs(l1, l2)))::r) eo errs
      end
    else
      let val err = (Locs(l1, l2),#tokFALSE G)
      in
        applykont G fk ((tk,Locs(l1, l2))::xs) p r
                  (optmax MAXerr eo (SOME err)) (err::errs)
      end
  | ispeg_exec G (any f) [] p r eo errs k fk =
    let val err = (EOF,#anyEOF G)
    in
      applykont G fk [] p r (optmax MAXerr eo (SOME err)) (err::errs)
    end
  | ispeg_exec G (any f) (x::xs) p r eo errs k fk =
    if p = lpBOT then
      let val err = (#2 x,#iFAIL G)
      in
        applykont G fk (x::xs) lpBOT r (optmax MAXerr eo (SOME err))
                  (err::errs)
      end
    else applykont G k xs p (SOME (f x)::r) eo errs
  | ispeg_exec G (seq(e1, e2, sf)) i p r eo errs k fk =
    ispeg_exec G e1 i p r eo errs
       (restoreEO(eo,
                  ksym(e2,
                       appf2(sf, k),
                       returnTo(i, r, setlps(p, fk)))))
       (setlps(p, cmpEO(eo, returnTo(i, r, fk))))
  | ispeg_exec G (choice(e1, e2, c1, c2)) i p r eo errs k fk =
    ispeg_exec G e1 i p r eo errs (appf1 (c1, k))
               (returnTo(i, r,
                         setlps(p, ksym(e2,
                                        dropErr (appf1 (c2, k)),
                                        cmpErrs fk))))
  | ispeg_exec G (not(e, v)) i p r eo errs k fk =
    if p = lpBOT then
      let val err = (sloc i,#iFAIL G)
      in
        applykont G fk i lpBOT r (optmax MAXerr eo (SOME err)) (err::errs)
      end
    else
      ispeg_exec G e i p r eo errs
                 (restoreEO(
                     eo,
                     returnTo(i, r,
                              setlps(p, addErr (sloc i, #notFAIL G, fk)))
                   )
                 )
                 (restoreEO(eo, returnTo(i, SOME v::r, dropErr k)))
  | ispeg_exec G (rpt(e, lf)) i p r eo errs k fk =
    if p = lpBOT then
      let val err = (sloc i,#iFAIL G)
      in
        applykont G fk i lpBOT r (optmax MAXerr eo (SOME err)) (err::errs)
      end
    else
      ispeg_exec G e i p (NONE::r) eo errs
                 (restoreEO(eo, listsym(e, lf, k)))
                 (setlps (p, poplist(lf, k)))
  | ispeg_exec G (error err) i p r eo errs k fk =
    let val err = (sloc i,err)
    in
      applykont G fk i p r (optmax MAXerr eo (SOME err)) (err::errs)
    end
and applykont G (ksym(e, k, fk)) i p r eo errs =
    ispeg_exec G e i p r eo errs k fk
  | applykont G (appf1(f, k)) i p (SOME v::r) eo errs =
    applykont G k i p (SOME (f v)::r) eo errs
  | applykont G (appf2(f, k)) i p (SOME v1::SOME v2::r) eo errs =
    applykont G k i p (SOME (f v2 v1)::r) eo errs
  | applykont G (returnTo(i', r', k)) i p r eo errs =
    applykont G k i' p r' eo errs
  | applykont G (addErr(l, e, k)) i p r eo errs =
    applykont G k i p r (optmax MAXerr eo (SOME (l,e))) ((l,e)::errs)
  | applykont G (dropErr k) i p r eo [] = raise Fail "Looped"
  | applykont G (dropErr k) i p r eo (e::errs) = applykont G k i p r eo errs
  | applykont G (cmpErrs k) i p r eo ((l1,er1)::(l2,er2)::errs) =
    applykont G k i p r eo
              ((if locsle l2 l1 then (l1,er1) else (l2,er2))::errs)
  | applykont G done i p [] eo errs = raise Fail "Looped"
  | applykont G done i p (NONE::rs) eo errs = raise Fail "Looped"
  | applykont G done i p (SOME rv::rs) eo errs = Success(i, rv, eo, p)
  | applykont G failed i p r eo [] = raise Fail "Looped"
  | applykont G failed i p r eo ((l,e)::errs) = Failure(l, e)
  | applykont G (poplist(f, k)) i p r eo [] = raise Fail "Looped"
  | applykont G (poplist(f, k)) i p r eo (le::errs) =
    applykont G k i p (poplistval f r) eo errs
  | applykont G (listsym(e, f, k)) i p r eo errs =
     ispeg_exec G e i p r eo errs
                (restoreEO(eo, listsym(e, f, k)))
                (setlps(p, poplist(f, k)))
  | applykont G (restoreEO(eo0, k)) i p r eo errs =
    applykont G k i p r eo0 errs
  | applykont G (cmpEO(eo0, k)) i p r eo ((l,err)::errs) =
    applykont G k i p r (optmax MAXerr eo0 (SOME (l,err))) ((l,err)::errs)
  | applykont G (lpcomp(p0, R, k, fk)) i p r eo errs =
     let val p'' = conjpred p0 (comppred R p)
     in
       if p'' = lpBOT then applykont G fk i p r eo errs
       else applykont G k i p'' r eo errs
     end
  | applykont G (setlps(ps, k)) i p r eo errs = applykont G k i ps r eo errs
  | applykont G (genIFAIL k) i p r eo errs =
    let val err = (sloc i,#iFAIL G)
    in
      applykont G k i p r (optmax MAXerr eo (SOME err)) (err::errs)
    end

end
