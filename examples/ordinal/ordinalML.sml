structure ordinalML :> ordinalML =
struct
  nonfix ord_mult ord_sub ord_add ord_less is_ord oless rank tail finp
         coeff expt Plus End * / div mod + - ^ @ <> > < >= <= := o
         before;
  
  open numML
  
  datatype osyntax = End of num | Plus of osyntax * num * osyntax
  fun expt (End(v0)) = End(ZERO)
    | expt (Plus(e,k,t)) = e
    
  fun coeff (End(x)) = x
    | coeff (Plus(e,k,t)) = k
    
  fun finp (End(v0)) = true
    | finp (Plus(v1,v2,v3)) = false
    
  fun tail (End(n)) = raise (Fail "tail: (End n)")
    | tail (Plus(e,k,t)) = t
    
  fun rank (End(v0)) = ZERO
    | rank (Plus(e,k,t)) = + ONE (rank e)
    
  fun oless (End(m)) (End(n)) = < m n
    | oless (End(m)) (Plus(e,k,t)) = true
    | oless (Plus(e,k,t)) (End(m)) = false
    | oless (Plus(e1,k1,t1)) (Plus(e2,k2,t2)) =
        (if oless e1 e2 then
           true
         else
           if (e1 = e2) andalso < k1 k2 then
           true
         else
           if (e1 = e2) andalso ((k1 = k2) andalso oless t1 t2) then
           true
         else false)
    
  fun is_ord (End(k)) = true
    | is_ord (Plus(e,k,t)) =
        is_ord e andalso
        (not (e = End(ZERO)) andalso
         (< ZERO k andalso (is_ord t andalso oless (expt t) e)))
    
  fun ord_less x y = is_ord x andalso (is_ord y andalso oless x y)
    
  fun ord_add (End(m)) (End(n)) = End(+ m n)
    | ord_add (End(m)) (Plus(p,k,t)) = Plus(p,k,t)
    | ord_add (Plus(e,k,t)) (End(m)) = Plus(e,k,ord_add t (End(m)))
    | ord_add (Plus(e1,k1,t1)) (Plus(e2,k2,t2)) =
        (if oless e1 e2 then
           Plus(e2,k2,t2)
         else
           if e1 = e2 then
           Plus(e2,+ k1 k2,t2)
         else Plus(e1,k1,ord_add t1 (Plus(e2,k2,t2))))
    
  fun ord_sub (End(m)) (End(n)) = End(- m n)
    | ord_sub (End(m)) (Plus(p,k,t)) = End(ZERO)
    | ord_sub (Plus(e,k,t)) (End(m)) = Plus(e,k,t)
    | ord_sub (Plus(e1,k1,t1)) (Plus(e2,k2,t2)) =
        (if oless e1 e2 then
           End(ZERO)
         else
           if e1 = e2 then
           (if < k1 k2 then
              End(ZERO)
            else if > k1 k2 then Plus(e1,- k1 k2,t1) else ord_sub t1 t2)
         else Plus(e1,k1,t1))
    
  fun ord_mult x y =
        if (x = End(ZERO)) orelse (y = End(ZERO)) then End(ZERO)
        else
          case (x,y)
           of (End(m),End(n)) => End( *  m n)
            | (End(m),Plus(e,k,t)) =>
                 Plus(ord_add (End(ZERO)) e,k,ord_mult (End(m)) t)
            | (Plus(e',k',t'),End(n')) => Plus(e', *  k' n',t')
            | (Plus(e',k',t'),Plus(e2,k2,t2)) =>
                 Plus(ord_add e' e2,k2,ord_mult (Plus(e',k',t')) t2)
    
end
