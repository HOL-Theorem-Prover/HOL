








open Lib;;

  type hol_type = Tyvar of string
                | Tyapp of string *  hol_type list

  type term = Var of string * hol_type
            | Const of int * hol_type
            | Comb of term * term
            | Abs of term * term

  type thm = Sequent of (term list * term)









  let the_type_constants = ref ["bool",0; "fun",2]





  let types() = !the_type_constants





  let get_type_arity s = assoc s (!the_type_constants)





  let new_type(name,arity) =
    if Lib.can get_type_arity name then
      failwith ("new_type: type "^name^" has already been declared")
    else the_type_constants := (name,arity)::(!the_type_constants)





  let mk_type(tyop,args) =
    let arity = try get_type_arity tyop with Failure _ ->
      failwith ("mk_type: type "^tyop^" has not been defined") in
    if arity = length args then
      Tyapp(tyop,args)
    else failwith ("mk_type: wrong number of arguments to "^tyop)

  let mk_vartype v = Tyvar(v)





  let dest_type =
    function
        (Tyapp (s,ty)) -> s,ty
      | (Tyvar _) -> failwith "dest_type: type variable not a constructor"

  let dest_vartype =
    function
        (Tyapp(_,_)) -> failwith "dest_vartype: type constructor not a variable"
      | (Tyvar s) -> s





  let is_type = Lib.can dest_type

  let is_vartype = Lib.can dest_vartype





  let rec tyvars =
      function
          (Tyapp(_,args)) -> Lib.itlist (Lib.o Lib.union tyvars) args []
        | (Tyvar v as tv) -> [tv]








  let rec type_subst i ty =
    match ty with
      Tyapp(tycon,args) ->
          let args' = Lib.qmap (type_subst i) args in
          if args' == args then ty else Tyapp(tycon,args')
      | _ -> rev_assocd ty i ty

  let bool_ty = Tyapp("bool",[])

  let aty = Tyvar "A"






  let the_term_constants = Hashtbl.create 1000;;
  let hash_name_const = Hashtbl.create 1000;;
  let hash_const_name = Hashtbl.create 1000;;

  Hashtbl.add hash_name_const "=" 0;;
  Hashtbl.add hash_const_name 0 "=";;
  Hashtbl.add the_term_constants 0 (Tyapp("fun",[aty;Tyapp("fun",[aty;bool_ty])]));;
  let next_const_no = ref 0;;

  let constants() =
    let i = ref 0 and ret = ref [] in
    try while true do
      ret := (Hashtbl.find hash_const_name !i, Hashtbl.find the_term_constants !i) :: !ret;
      incr i
    done; failwith "constants" with Not_found -> List.rev !ret
  ;;

  let get_const_type s = try Hashtbl.find the_term_constants (Hashtbl.find hash_name_const s) with Not_found -> failwith "find";;


  let new_constant(name,ty) =
    if Hashtbl.mem hash_name_const name then
      failwith ("new_constant: constant "^name^" has already been declared")
    else begin
      incr next_const_no;
      let no = !next_const_no in
      Hashtbl.add hash_name_const name no;
      Hashtbl.add hash_const_name no name;
      Hashtbl.add the_term_constants no ty
    end


  let set_term_constants l =
    Hashtbl.clear the_term_constants;
    Hashtbl.clear hash_name_const;
    Hashtbl.clear hash_const_name;
    next_const_no := -1;
    List.iter new_constant l
  ;;



  let rec type_of tm =
    match tm with
      Var(_,ty) -> ty
    | Const(_,ty) -> ty
    | Comb(s,_) -> hd(tl(snd(dest_type(type_of s))))
    | Abs(Var(_,ty),t) -> Tyapp("fun",[ty;type_of t])





  let is_var = function (Var(_,_)) -> true | _ -> false

  let is_const = function (Const(_,_)) -> true | _ -> false

  let is_abs = function (Abs(_,_)) -> true | _ -> false

  let is_comb = function (Comb(_,_)) -> true | _ -> false





  let mk_var(v,ty) = Var(v,ty)

  let mk_const(name,theta) =
    let no = try Hashtbl.find hash_name_const name with Not_found ->
      failwith "mk_const: not a constant name" in
    let uty = Hashtbl.find the_term_constants no in
    Const(no,type_subst theta uty)

  let mk_abs(bvar,bod) =
    match bvar with
      Var(_,_) -> Abs(bvar,bod)
    | _ -> failwith "mk_abs: not a variable"

  let mk_comb(f,a) =
    match type_of f with
      Tyapp("fun",[ty;_]) when Pervasives.compare ty (type_of a) = 0
        -> Comb(f,a)
    | _ -> failwith "mk_comb: types do not agree"





  let dest_var =
    function (Var(s,ty)) -> s,ty | _ -> failwith "dest_var: not a variable"

  let dest_const =
    function (Const(s,ty)) ->
      (try
        Hashtbl.find hash_const_name s,ty
      with Not_found -> failwith ("No const: " ^ string_of_int s))
    | _ -> failwith "dest_const: not a constant"

  let dest_comb =
    function (Comb(f,x)) -> f,x | _ -> failwith "dest_comb: not a combination"

  let dest_abs =
    function (Abs(v,b)) -> v,b | _ -> failwith "dest_abs: not an abstraction"





  let rec frees tm =
    match tm with
      Var(_,_) -> [tm]
    | Const(_,_) -> []
    | Abs(bv,bod) -> subtract (frees bod) [bv]
    | Comb(s,t) -> union (frees s) (frees t)

  let freesl tml = itlist (o union frees) tml []





  let rec freesin acc tm =
    match tm with
      Var(_,_) -> mem tm acc
    | Const(_,_) -> true
    | Abs(bv,bod) -> freesin (bv::acc) bod
    | Comb(s,t) -> freesin acc s && freesin acc t





  let rec vfree_in v tm =
    match tm with
      Abs(bv,bod) -> v <> bv && vfree_in v bod
    | Comb(s,t) -> vfree_in v s || vfree_in v t
    | _ -> Pervasives.compare tm v = 0





  let rec type_vars_in_term tm =
    match tm with
      Var(_,ty)        -> tyvars ty
    | Const(_,ty)      -> tyvars ty
    | Comb(s,t)        -> union (type_vars_in_term s) (type_vars_in_term t)
    | Abs(Var(_,ty),t) -> union (tyvars ty) (type_vars_in_term t)





  let rec variant avoid v =
    if not(exists (vfree_in v) avoid) then v else
    match v with
      Var(s,ty) -> variant avoid (Var(s^"'",ty))
    | _ -> failwith "variant: not a variable"





  let vsubst =
    let rec vsubst ilist tm =
      match tm with
        Var(_,_) -> rev_assocd tm ilist tm
      | Const(_,_) -> tm
      | Comb(s,t) -> let s' = vsubst ilist s and t' = vsubst ilist t in
                     if s' == s && t' == t then tm else Comb(s',t')
      | Abs(v,s) -> let ilist' = filter (fun (t,x) -> x <> v) ilist in
                    if ilist' = [] then tm else
                    let s' = vsubst ilist' s in
                    if s' == s then tm else
                    if exists (fun (t,x) -> vfree_in v t && vfree_in x s) ilist'
                    then let v' = variant [s'] v in
                         Abs(v',vsubst ((v',v)::ilist') s)
                    else Abs(v,s') in
    fun theta ->
      if theta = [] then (fun tm -> tm) else
      if forall (fun (t,x) -> type_of t = snd(dest_var x)) theta
      then vsubst theta else failwith "vsubst: Bad substitution list"





  exception Clash of term

  let inst =
    let rec inst env tyin tm =
      match tm with
        Var(n,ty)   -> let ty' = type_subst tyin ty in
                       let tm' = if ty' == ty then tm else Var(n,ty') in
                       if Pervasives.compare (rev_assocd tm' env tm) tm = 0
                       then tm'
                       else raise (Clash tm')
      | Const(c,ty) -> let ty' = type_subst tyin ty in
                       if ty' == ty then tm else Const(c,ty')
      | Comb(f,x)   -> let f' = inst env tyin f and x' = inst env tyin x in
                       if f' == f && x' == x then tm else Comb(f',x')
      | Abs(y,t)    -> let y' = inst [] tyin y in
                       let env' = (y,y')::env in
                       try let t' = inst env' tyin t in
                           if y' == y && t' == t then tm else Abs(y',t')
                       with (Clash(w') as ex) ->
                       if w' <> y' then raise ex else
                       let ifrees = map (inst [] tyin) (frees t) in
                       let y'' = variant ifrees y' in
                       let z = Var(fst(dest_var y''),snd(dest_var y)) in
                       inst env tyin (Abs(z,vsubst[z,y] t)) in
    fun tyin -> if tyin = [] then fun tm -> tm else inst [] tyin





  let rator tm =
    match tm with
      Comb(l,r) -> l
    | _ -> failwith "rator: Not a combination"

  let rand tm =
    match tm with
      Comb(l,r) -> r
    | _ -> failwith "rand: Not a combination"





  let safe_mk_eq l r =
    let ty = type_of l in
    Comb(Comb(Const(0,Tyapp("fun",[ty;Tyapp("fun",[ty;bool_ty])])),l),r)

  let dest_eq tm =
    match tm with
      Comb(Comb(Const(0,_),l),r) -> l,r
    | _ -> failwith "dest_eq"





  let rec ordav env x1 x2 =
    match env with
      [] -> Pervasives.compare x1 x2
    | (t1,t2)::oenv -> if Pervasives.compare x1 t1 = 0
                       then if Pervasives.compare x2 t2 = 0
                            then 0 else -1
                       else if Pervasives.compare x2 t2 = 0 then 1
                       else ordav oenv x1 x2

  let rec orda env tm1 tm2 =
    if tm1 == tm2 && forall (fun (x,y) -> x = y) env then 0 else
    match (tm1,tm2) with
      Var(x1,ty1),Var(x2,ty2) -> ordav env tm1 tm2
    | Const(x1,ty1),Const(x2,ty2) -> Pervasives.compare tm1 tm2
    | Comb(s1,t1),Comb(s2,t2) ->
          let c = orda env s1 s2 in if c <> 0 then c else orda env t1 t2
    | Abs(Var(_,ty1) as x1,t1),Abs(Var(_,ty2) as x2,t2) ->
          let c = Pervasives.compare ty1 ty2 in
          if c <> 0 then c else orda ((x1,x2)::env) t1 t2
    | Const(_,_),_ -> -1
    | _,Const(_,_) -> 1
    | Var(_,_),_ -> -1
    | _,Var(_,_) -> 1
    | Comb(_,_),_ -> -1
    | _,Comb(_,_) -> 1

  let alphaorder = orda []

  let rec term_union l1 l2 =
    match (l1,l2) with
      ([],l2) -> l2
    | (l1,[]) -> l1
    | (h1::t1,h2::t2) -> let c = alphaorder h1 h2 in
                         if c = 0 then h1::(term_union t1 t2)
                         else if c < 0 then h1::(term_union t1 l2)
                         else h2::(term_union l1 t2)

  let rec term_remove t l =
    match l with
      s::ss -> let c = alphaorder t s in
               if c > 0 then
                 let ss' = term_remove t ss in
                 if ss' == ss then l else s::ss'
               else if c = 0 then ss else l
    | [] -> l

  let rec term_image f l =
    match l with
      h::t -> let h' = f h and t' = term_image f t in
              if h' == h && t' == t then l else term_union [h'] t'
    | [] -> l





  let dest_thm (Sequent(asl,c)) = (asl,c)

  let hyp (Sequent(asl,c)) = asl

  let concl (Sequent(asl,c)) = c





  let rEFL tm =
    Sequent([],safe_mk_eq tm tm)

  let tRANS (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    match (c1,c2) with
      Comb((Comb(Const(0,_),_) as eql),m1),Comb(Comb(Const(0,_),m2),r)
        when alphaorder m1 m2 = 0 -> Sequent(term_union asl1 asl2,Comb(eql,r))
    | _ -> failwith "TRANS"





  let mK_COMB(Sequent(asl1,c1),Sequent(asl2,c2)) =
     match (c1,c2) with
       Comb(Comb(Const(0,_),l1),r1),Comb(Comb(Const(0,_),l2),r2) ->
        (match type_of l1 with
           Tyapp("fun",[ty;_]) when Pervasives.compare ty (type_of l2) = 0
             -> Sequent(term_union asl1 asl2,
                        safe_mk_eq (Comb(l1,l2)) (Comb(r1,r2)))
         | _ -> failwith "MK_COMB: types do not agree")
     | _ -> failwith "MK_COMB: not both equations"

  let aBS v (Sequent(asl,c)) =
    match (v,c) with
      Var(_,_),Comb(Comb(Const(0,_),l),r) when not(exists (vfree_in v) asl)
         -> Sequent(asl,safe_mk_eq (Abs(v,l)) (Abs(v,r)))
    | _ -> failwith "ABS";;





  let bETA tm =
    match tm with
      Comb(Abs(v,bod),arg) when Pervasives.compare arg v = 0
        -> Sequent([],safe_mk_eq tm bod)
    | _ -> failwith "BETA: not a trivial beta-redex"





  let aSSUME tm =
    if Pervasives.compare (type_of tm) bool_ty = 0 then Sequent([tm],tm)
    else failwith "ASSUME: not a proposition"

  let eQ_MP (Sequent(asl1,eq)) (Sequent(asl2,c)) =
    match eq with
      Comb(Comb(Const(0,_),l),r) when alphaorder l c = 0
        -> Sequent(term_union asl1 asl2,r)
    | _ -> failwith "EQ_MP"

  let dEDUCT_ANTISYM_RULE (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    let asl1' = term_remove c2 asl1 and asl2' = term_remove c1 asl2 in
    Sequent(term_union asl1' asl2',safe_mk_eq c1 c2)





  let iNST_TYPE theta (Sequent(asl,c)) =
    let inst_fn = inst theta in
    Sequent(term_image inst_fn asl,inst_fn c)

  let iNST theta (Sequent(asl,c)) =
    let inst_fun = vsubst theta in
    Sequent(term_image inst_fun asl,inst_fun c)





  let the_axioms = ref ([]:thm list)

  let axioms() = !the_axioms

  let new_axiom tm =
    if Pervasives.compare (type_of tm) bool_ty = 0 then
      let th = Sequent([],tm) in
       (the_axioms := th::(!the_axioms); th)
    else failwith "new_axiom: Not a proposition"





  let the_definitions = ref ([]:thm list)

  let definitions() = !the_definitions

  let new_basic_definition tm =
    match tm with
      Comb(Comb(Const(0,_),Var(cname,ty)),r) ->
        if not(freesin [] r) then failwith "new_definition: term not closed"
        else if not (subset (type_vars_in_term r) (tyvars ty))
        then failwith "new_definition: Type variables not reflected in constant"
        else let c = new_constant(cname,ty); Const(Hashtbl.find hash_name_const cname,ty) in
             let dth = Sequent([],safe_mk_eq c r) in
             the_definitions := dth::(!the_definitions); dth
    | _ -> failwith "new_basic_definition"














  let new_basic_type_definition tyname (absname,repname) (Sequent(asl,c)) =
    if exists (Hashtbl.mem hash_name_const) [absname; repname] then
      failwith "new_basic_type_definition: Constant(s) already in use" else
    if not (asl = []) then
      failwith "new_basic_type_definition: Assumptions in theorem" else
    let p,x = try dest_comb c
              with Failure _ ->
                failwith "new_basic_type_definition: Not a combination" in
    if not(freesin [] p) then
      failwith "new_basic_type_definition: Predicate is not closed" else
    let tyvars = sort (<=) (type_vars_in_term p) in
    let _ = try new_type(tyname,length tyvars)
            with Failure _ ->
                failwith "new_basic_type_definition: Type already defined" in
    let aty = Tyapp(tyname,tyvars)
    and rty = type_of x in
    let absty = Tyapp("fun",[rty;aty]) and repty = Tyapp("fun",[aty;rty]) in
    let abs = (new_constant(absname,absty); Const(Hashtbl.find hash_name_const absname,absty))
    and rep = (new_constant(repname,repty); Const(Hashtbl.find hash_name_const repname,repty)) in
    let a = Var("a",aty) and r = Var("r",rty) in
    Sequent([],safe_mk_eq (Comb(abs,mk_comb(rep,a))) a),
    Sequent([],safe_mk_eq (Comb(p,r))
                          (safe_mk_eq (mk_comb(rep,mk_comb(abs,r))) r))





let mk_fun_ty ty1 ty2 = mk_type("fun",[ty1; ty2]);;
let bty = mk_vartype "B";;

let is_eq tm =
  match tm with
    Comb(Comb(Const(0,_),_),_) -> true
  | _ -> false;;

let mk_eq =
  let eq = mk_const("=",[]) in
  fun (l,r) ->
    try let ty = type_of l in
        let eq_tm = inst [ty,aty] eq in
        mk_comb(mk_comb(eq_tm,l),r)
    with Failure _ -> failwith "mk_eq";;





let aconv s t = alphaorder s t = 0;;






let equals_thm th th' = dest_thm th = dest_thm th';;
