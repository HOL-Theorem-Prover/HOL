structure isaload :> isaload =
struct

fun nthy_cmp ({Name = n1, Theory = t1},
              {Name = n2, Theory = t2}) =
    pair_compare (String.compare, String.compare) ((n1,t1),(n2,t2))

val defdb = ref (Binarymap.mkDict nthy_cmp)

fun declare_const (name, ty) = let
  val thy = current_theory()
  val nthy =  {Name = name, Theory = thy}
in
  new_constant(name, ty);
  defdb := Binarymap.insert(!defdb, nthy, [] : thm list)
end

fun freshen_tyvars pfx ty = let
  val tyvars = type_vars ty
  val newtyvars = map (fn s => mk_vartype (pfx ^ dest_vartype s)) tyvars
in
  Type.type_subst (ListPair.map (op |->) (tyvars, newtyvars)) ty
end

fun unify (ty01, ty02) = let
  val ty1 = trace ("Vartype Format Complaint", 0) (freshen_tyvars "a") ty01
  val ty2 = trace ("Vartype Format Complaint", 0) (freshen_tyvars "b") ty02
  fun env_subst (v,ty) env =
      map (fn {redex, residue} => {redex = redex,
                                   residue = type_subst [v |-> ty] residue})
          env

  fun raw_unify env problist =
      case problist of
        [] => env
      | (ty1,ty2) :: rest =>
        if is_vartype ty1 then
          if mem ty1 (type_vars ty2) then raise Fail "Occurs check"
          else let
              val new_env = ({redex = ty1, residue = ty2} ::
                             env_subst(ty1,ty2) env)
              val new_probs =
                  map (fn (ty11, ty21) =>
                          (type_subst [ty1 |-> ty2] ty11,
                           type_subst [ty1 |-> ty2] ty21))
                      rest
            in
              raw_unify new_env new_probs
            end
        else if is_vartype ty2 then
          if mem ty2 (type_vars ty1) then raise Fail "occurs check"
          else let
              val new_env = ({redex = ty2, residue = ty1} ::
                             env_subst(ty2,ty1) env)
              val new_probs =
                  map (fn (ty11, ty21) =>
                          (type_subst [ty2 |-> ty1] ty11,
                           type_subst [ty2 |-> ty1] ty21))
                      rest
            in
              raw_unify new_env new_probs
            end
        else let
            val {Thy = thy1, Tyop = op1, Args = args1} = dest_thy_type ty1
            val {Thy = thy2, Tyop = op2, Args = args2} = dest_thy_type ty2
          in
            if op1 = op2 andalso thy1 = thy2 then
              raw_unify env (ListPair.zip(args1, args2) @ rest)
            else raise Fail (op1 ^ " and " ^ op2 ^ " don't unify")
          end
in
  raw_unify [] [(ty1,ty2)]
end

fun vlist [] = ""
  | vlist [x] = #1 (dest_var x)
  | vlist (h::t) = #1 (dest_var h) ^ ", " ^ vlist t


(* checks:
    * non-overlapping-ness
    * type variables on right all occur on left
    * no free (term) variables on RHS
    * termination (TODO)
*)



fun define_const t = let
  val c = lhs t
  val r = rhs t
  val fs = free_vars r
  val ltyvs = type_vars (type_of c)
  val rtyvs = type_vars_in_term r
  val _ = case List.find (fn ty => not (mem ty ltyvs)) rtyvs of
            NONE => ()
          | SOME ty =>
            raise mk_HOL_ERR "isaload" "define_const"
                             ("Type variable "^dest_vartype ty^
                              " occurs on RHS of def'n and not on left")
  val _ = null fs orelse
          raise mk_HOL_ERR "isaload" "define_const"
                ("Definition has free variable(s) " ^ vlist fs ^ " on RHS")
  val {Name,Thy,...} = dest_thy_const c
  val nthy = {Name = Name, Theory = Thy}
  val info = Binarymap.peek (!defdb, nthy)
in
  case info of
    NONE => raise mk_HOL_ERR "isaload" "define_const"
                             "Attempting to define a non-declared const"
  | SOME thlist => let
      val base_tag = "ISALOAD_" ^ Name ^ "$" ^ Thy ^ "_"
      fun check_for_overlap th = let
        val c' = lhs (concl th)
      in
        if not (aconv c c') andalso can unify (type_of c', type_of c) then
          raise mk_HOL_ERR "isaload" "define_const"
                           ("Definition overlaps with that for "^Name^
                            " at type "^type_to_string (type_of c'))
        else ()
      end
      val _ = app check_for_overlap thlist

    in
      case List.find (fn th => aconv (lhs (concl th)) c) thlist of
        NONE => let
          val defth =
              mk_oracle_thm (Tag.read (base_tag ^ Int.toString 0)) ([], t)
        in
          defdb := Binarymap.insert(!defdb, nthy, defth :: thlist);
          defth
        end
      | SOME th => let
          val (tags, _) = Tag.dest_tag (Thm.tag th)
          val isatag = valOf (List.find (String.isPrefix "ISALOAD") tags)
          val (_, nstr) = Substring.splitr Char.isDigit (Substring.all isatag)
          val n = valOf (Int.fromString (Substring.string nstr))
          val defth =
              mk_oracle_thm (Tag.read(base_tag ^ Int.toString (n + 1))) ([], t)
        in
          defdb := Binarymap.insert(!defdb, nthy, defth :: thlist);
          defth
        end
    end
end


end

ancestor:

  declare_const ("c", ``:'a -> bool``)


derived:

  val th = define_const (``c:(num -> bool) = \n. T``);

  val th = define_const (``c:(num -> bool) = \n. F``);



