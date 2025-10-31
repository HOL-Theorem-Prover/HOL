
  datatype e =
      Var of string
    | Num of int
    | Add of e * e
    | Assign of string * e;

  datatype t =
      Dec of string * t
    | Exp of e
    | Break
    | Seq of t * t
    | If of e * t * t
    | For of e * e * t;

  datatype r =
      Rval of int
    | Rbreak
    | Rtimeout
    | Rfail;

  fun lookup y [] = NONE
    | lookup y ((x,v)::xs) = if y = x then SOME v else lookup y xs

  fun run_e s (Var x) =
       (case lookup x s of
          NONE => (Rfail,s)
        | SOME v => (Rval v,s))
    | run_e s (Num i) = (Rval i,s)
    | run_e s (Add (e1, e2)) =
       (case run_e s e1 of
          (Rval n1, s1) =>
             (case run_e s1 e2 of
                (Rval n2, s2) => (Rval (n1+n2), s2)
              | r => r)
        | r => r)
    | run_e s (Assign (x, e)) =
       (case run_e s e of
          (Rval n1, s1) => (Rval n1, (x,n1)::s1)
        | r => r)

  fun run_t s (Exp e) = run_e s e
    | run_t s (Dec (x, t)) = run_t ((x,0)::s) t
    | run_t s Break = (Rbreak, s)
    | run_t s (Seq (t1, t2)) =
       (case run_t s t1 of
          (Rval _, s1) => run_t s1 t2
        | r => r)
    | run_t s (If (e, t1, t2)) =
       (case run_e s e of
          (Rval n1, s1) =>
            if n1 = 0 then
              run_t s1 t2
            else
              run_t s1 t1
        | r => r)
    | run_t s (For (e1, e2, t)) =
       (case run_e s e1 of
          (Rval n1, s1) =>
            if n1 = 0 then (Rval 0, s1) else
             (case run_t s1 t of
                (Rval _, s2) =>
                  (case run_e s2 e2 of
                     (Rval _, s3) => run_t s3 (For (e1, e2, t))
                   | r => r)
              | (Rbreak, s2) =>
                  (Rval 0, s2)
              | r => r)
        | r => r)
