structure PEGParse :> PEGParse =
struct

  datatype ('tok,'nt,'value)pegsym =
           empty of 'value
         | any of 'tok -> 'value
         | tok of ('tok -> bool) * ('tok -> 'value)
         | nt of 'nt * ('value -> 'value)
         | seq of ('tok,'nt,'value)pegsym * ('tok,'nt,'value)pegsym * ('value -> 'value -> 'value)
         | choice of ('tok,'nt,'value)pegsym * ('tok,'nt,'value)pegsym * ('value -> 'value) * ('value -> 'value)
         | rpt of ('tok,'nt,'value)pegsym * ('value list -> 'value)
         | not of ('tok,'nt,'value)pegsym * 'value

  datatype ('tok,'nt,'value) grammar = PEG of { start : ('tok,'nt,'value)pegsym, rules : 'nt -> ('tok,'nt,'value)pegsym option }

  datatype ('source,'tok,'nt,'value)kont =
           ksym of ('tok,'nt,'value)pegsym * ('source,'tok,'nt,'value)kont * ('source,'tok,'nt,'value)kont
         | appf1 of ('value -> 'value) * ('source,'tok,'nt,'value)kont
         | appf2 of ('value -> 'value -> 'value) * ('source,'tok,'nt,'value)kont
         | returnTo of 'source * 'value option list * ('source,'tok,'nt,'value)kont
         | poplist of ('value list -> 'value) * ('source,'tok,'nt,'value)kont
         | listsym of ('tok,'nt,'value)pegsym * ('value list -> 'value) * ('source,'tok,'nt,'value)kont
         | kdone
         | kfailed

fun poplistval f acc stk =
  case stk of
      [] => raise Fail "Invariant failure in poplist"
    | SOME h :: t => poplistval f (h::acc) t
    | NONE::rest => SOME(f acc)::rest


fun pegexec G get e inp stk k fk = let
  fun pe e inp stk k fk =
      case e of
          empty v => applykont k inp (SOME v::stk)
        | tok(P,f) =>
          let
          in
            case get inp of
                NONE => applykont fk inp stk
              | SOME(inp',t) => if P t then applykont k inp' (SOME (f t)::stk)
                                else applykont fk inp stk
          end
        | any f =>
          let
          in
            case get inp of
                NONE => applykont fk inp stk
              | SOME(inp',t) => applykont k inp' (SOME (f t)::stk)
          end
        | seq(e1,e2,f) => pe e1 inp stk (ksym(e2,appf2(f,k),returnTo(inp,stk,fk))) fk
        | choice(e1,e2,f1,f2) => pe e1 inp stk (appf1(f1,k)) (returnTo(inp,stk,ksym(e2,appf1(f2,k),fk)))
        | not(e,v) => pe e inp stk (returnTo(inp,stk,fk)) (returnTo(inp,SOME v::stk,k))
        | rpt(e,f) => pe e inp (NONE::stk) (listsym(e,f,k)) (poplist(f,k))
        | nt(nm,f) => pe (G nm) inp stk (appf1(f,k)) fk
  and applykont k0 inp stk =
      case k0 of
          ksym(e,k,fk) => pe e inp stk k fk
        | appf1(f,k) =>
          let
          in
            case stk of
                SOME v::rest => applykont k inp (SOME (f v)::rest)
              | _ => raise Fail "Invariant failure in appf1"
          end
        | appf2(f,k) =>
          let
          in
            case stk of
                SOME v1::SOME v2::rest => applykont k inp (SOME (f v2 v1)::rest)
              | _ => raise Fail "Invariant failure in appf2"
          end
        | returnTo(inp,stk,k) => applykont k inp stk
        | poplist(f,k) => applykont k inp (poplistval f [] stk)
        | listsym(e,f,k) => pe e inp stk (listsym(e,f,k)) (poplist(f,k))
        | kdone => SOME(inp,valOf (hd stk))
        | kfailed => NONE
in
  pe e inp stk k fk
end

end (* struct *)
