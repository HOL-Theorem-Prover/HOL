structure listSyntax :> listSyntax =
struct
  open HolKernel boolSyntax
  fun ERR f msg = raise HOL_ERR {origin_function = f,
                                 origin_structure = "listSyntax",
                                 message = msg}

  local open listTheory in end;
  infixr -->

  fun mk_list_ty ty =
    mk_thy_type {Tyop = "list", Thy = "list",  Args = [ty]};
  val list_ty = mk_list_ty Type.alpha

  fun is_list_ty ty = let
    val {Tyop,Thy,...} = dest_thy_type ty
  in
    Tyop = "list" andalso Thy = "list"
  end handle HOL_ERR _ => false

  fun base_type t = let
    val ty = type_of t
  in
    if is_list_ty ty then hd (#Args (dest_type ty))
    else ERR "base_type" "Term not of list type"
  end

  val MAP_tm = prim_mk_const{Name = "MAP", Thy = "list"};
  val CONS_tm = prim_mk_const{Name = "CONS", Thy = "list"};
  val APPEND_tm = prim_mk_const{Name = "APPEND", Thy = "list"};
  val NIL_tm = prim_mk_const{Name = "NIL", Thy = "list"};
  val LIST_EQ_tm = mk_thy_const{Name = "=", Thy = "min",
                                Ty = list_ty --> list_ty --> bool}

  fun mk_CONS_tm ty = let
    val lty = mk_list_ty ty
  in
    mk_thy_const{Name = "CONS", Thy = "list", Ty = ty --> lty --> lty}
  end
  fun mk_NIL_tm ty = let
    val lty = mk_list_ty ty
  in
    mk_thy_const{Name = "NIL", Thy = "list", Ty = lty}
  end

  fun mk_cons (h,t) = let
    val ty = type_of h
    val bty = base_type t
      handle HOL_ERR _ => ERR "mk_cons" "tail not of list type"
    val _ = bty = ty orelse ERR "mk_cons" "element types not compatible"
  in
    list_mk_comb(mk_CONS_tm bty, [h,t])
  end

  fun mk_list0 tl cons acc =
    case tl of
      [] => acc
    | (h::rest) => mk_list0 rest cons (list_mk_comb(cons, [h, acc]))
  fun mk_list (tl,ty) = mk_list0 (List.rev tl) (mk_CONS_tm ty) (mk_NIL_tm ty)


  fun dest_cons t = let
    val (f, args) = strip_comb t
    val {Name,Thy,...} = dest_thy_const f
      handle HOL_ERR _ => ERR "dest_cons" "term not a cons"
  in
    if Name = "CONS" andalso Thy = "list" andalso length args = 2 then
      (hd args, hd (tl args))
    else
      ERR "dest_cons" "term not a cons"
  end

  val is_cons = can dest_cons
  fun is_nil t = let
    val {Name,Thy,...} = dest_thy_const t
  in
    Name = "NIL" andalso Thy = "list"
  end handle HOL_ERR _ => false

  fun dest_list0 acc tm =
    if is_nil tm then acc
    else let
      val (h,t) = dest_cons tm
    in
      dest_list0 (h::acc) t
    end

  fun dest_list tm =
    (List.rev (dest_list0 [] tm), base_type tm)
    handle HOL_ERR _ => ERR "dest_list" "not a list term"

end
