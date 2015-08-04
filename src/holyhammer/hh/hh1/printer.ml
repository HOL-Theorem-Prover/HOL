









open Lib;;
open Fusion;;
open Basics;;
open Num;;





let isspace,issep,isbra,issymb,isalpha,isnum,isalnum =
  let charcode s = Char.code(String.get s 0) in
  let spaces = " \t\n\r"
  and separators = ",;"
  and brackets = "()[]{}"
  and symbs = "\\!@#$%^&*-+|\\<=>/?~.:"
  and alphas = "'abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ"
  and nums = "0123456789" in
  let allchars = spaces^separators^brackets^symbs^alphas^nums in
  let csetsize = itlist (o max charcode) (explode allchars) 256 in
  let ctable = Array.make csetsize 0 in
  do_list (fun c -> Array.set ctable (charcode c) 1) (explode spaces);
  do_list (fun c -> Array.set ctable (charcode c) 2) (explode separators);
  do_list (fun c -> Array.set ctable (charcode c) 4) (explode brackets);
  do_list (fun c -> Array.set ctable (charcode c) 8) (explode symbs);
  do_list (fun c -> Array.set ctable (charcode c) 16) (explode alphas);
  do_list (fun c -> Array.set ctable (charcode c) 32) (explode nums);
  let isspace c = Array.get ctable (charcode c) = 1
  and issep c  = Array.get ctable (charcode c) = 2
  and isbra c  = Array.get ctable (charcode c) = 4
  and issymb c = Array.get ctable (charcode c) = 8
  and isalpha c = Array.get ctable (charcode c) = 16
  and isnum c = Array.get ctable (charcode c) = 32
  and isalnum c = Array.get ctable (charcode c) >= 16 in
  isspace,issep,isbra,issymb,isalpha,isnum,isalnum;;





let reserve_words,unreserve_words,is_reserved_word,reserved_words =
  let reswords = ref ["(";  ")"; "[";   "]";  "{";   "}";
                      ":";  ";";  ".";  "|";
                      "let"; "in"; "and"; "if"; "then"; "else";
                      "match"; "with"; "function"; "->"; "when"] in
  (fun ns  -> reswords := union (!reswords) ns),
  (fun ns  -> reswords := subtract (!reswords) ns),
  (fun n  -> mem n (!reswords)),
  (fun () -> !reswords);;














let unparse_as_binder,parse_as_binder,parses_as_binder,binders =
  let binder_list = ref ([]:string list) in
  (fun n  -> binder_list := subtract (!binder_list) [n]),
  (fun n  -> binder_list := union (!binder_list) [n]),
  (fun n  -> mem n (!binder_list)),
  (fun () -> !binder_list);;

let unparse_as_prefix,parse_as_prefix,is_prefix,prefixes =
  let prefix_list = ref ([]:string list) in
  (fun n  -> prefix_list := subtract (!prefix_list) [n]),
  (fun n  -> prefix_list := union (!prefix_list) [n]),
  (fun n  -> mem n (!prefix_list)),
  (fun () -> !prefix_list);;

let unparse_as_infix,parse_as_infix,get_infix_status,infixes =
  let cmp (s,(x,a)) (t,(y,b)) =
     x < y or x = y & a > b or x = y & a = b & s < t in
  let infix_list = ref ([]:(string * (int * string)) list) in
  (fun n     -> infix_list := filter (o ((<>) n) fst) (!infix_list)),
  (fun (n,d) -> infix_list := sort cmp
     ((n,d)::(filter (o ((<>) n) fst) (!infix_list)))),
  (fun n     -> assoc n (!infix_list)),
  (fun ()    -> !infix_list);;





let the_interface = ref ([] :(string * (string * hol_type)) list);;

let the_overload_skeletons = ref ([] : (string * hol_type) list);;





include Format;;

set_max_boxes 100;;





let reverse_interface_mapping = ref true;;





let unspaced_binops = ref [","; ".."; "$"];;





let prebroken_binops = ref ["==>"];;





let print_unambiguous_comprehensions = ref false;;





let typify_universal_set = ref true;;





let print_all_thm = ref true;;





let name_of tm =
  match tm with
    Var(x,ty) -> x
  | Const(x,ty) -> Hashtbl.find hash_const_name x
  | _ -> "";;





let pp_print_type,pp_print_qtype =
  let soc sep flag ss =
    if ss = [] then "" else
    let s = end_itlist (fun s1 s2 -> s1^sep^s2) ss in
    if flag then "("^s^")" else s in
  let rec sot pr ty =
    try dest_vartype ty with Failure _ ->
    match dest_type ty with
      con,[] -> con
    | "fun",[ty1;ty2] -> soc "->" (pr > 0) [sot 1 ty1; sot 0 ty2]
    | "sum",[ty1;ty2] -> soc "+" (pr > 2) [sot 3 ty1; sot 2 ty2]
    | "prod",[ty1;ty2] -> soc "#" (pr > 4) [sot 5 ty1; sot 4 ty2]
    | "cart",[ty1;ty2] -> soc "^" (pr > 6) [sot 6 ty1; sot 7 ty2]
    | con,args -> (soc "," true (map (sot 0) args))^con in
  (fun fmt ty -> pp_print_string fmt (sot 0 ty)),
  (fun fmt ty -> pp_print_string fmt ("`:" ^ sot 0 ty ^ "`"));;





let install_user_printer,delete_user_printer,try_user_printer =
  let user_printers = ref ([]:(string*(term->unit))list) in
  (fun pr -> user_printers := pr::(!user_printers)),
  (fun s -> user_printers := snd(remove (fun (s',_) -> s = s')
                                        (!user_printers))),
  (fun tm -> tryfind (fun (_,pr) -> pr tm) (!user_printers));;





let pp_print_term =
  let reverse_interface (s0,ty0) =
    if not(!reverse_interface_mapping) then s0 else
    try fst(find (fun (s,(s',ty)) -> s' = s0 & can (type_match ty ty0) [])
                 (!the_interface))
    with Failure _ -> s0 in
  let dEST_BINARY c tm =
    try let il,r = dest_comb tm in
        let i,l = dest_comb il in
        if i = c or
           (is_const i & is_const c &
            reverse_interface(dest_const i) = reverse_interface(dest_const c))
        then l,r else fail()
    with Failure _ -> failwith "DEST_BINARY"
  and aRIGHT s =
    match snd(get_infix_status s) with
    "right" -> true | _ -> false in
  let rec powerof10 n =
    if abs_num n </ Int 1 then false
    else if n =/ Int 1 then true
    else powerof10 (n // Int 10) in
  let bool_of_term t =
    match t with
      Const(1,_) -> true
    | Const(7,_) -> false
    | _ -> failwith "bool_of_term" in
  let code_of_term t =
    let f,tms = strip_comb t in
    if not(is_const f & fst(dest_const f) = "ASCII")
       or not(length tms = 8) then failwith "code_of_term"
    else
       itlist (fun b f -> if b then 1 + 2 * f else 2 * f)
              (map bool_of_term (rev tms)) 0 in
  let rec dest_clause tm =
    let pbod = snd(strip_exists(body(body tm))) in
    let s,args = strip_comb pbod in
    if name_of s = "_UNGUARDED_PATTERN" & length args = 2 then
      [rand(rator(hd args));rand(rator(hd(tl args)))]
    else if name_of s = "_GUARDED_PATTERN" & length args = 3 then
      [rand(rator(hd args)); hd(tl args); rand(rator(hd(tl(tl args))))]
    else failwith "dest_clause" in
  let rec dest_clauses tm =
    let s,args = strip_comb tm in
    if name_of s = "_SEQPATTERN" & length args = 2 then
      dest_clause (hd args)::dest_clauses(hd(tl args))
    else [dest_clause tm] in
  fun fmt ->
    let rec print_term prec tm =
      try try_user_printer tm with Failure _ ->
      try pp_print_string fmt (string_of_num(dest_numeral tm)) with Failure _ ->
      try (let tms = dest_list tm in
           try if fst(dest_type(hd(snd(dest_type(type_of tm))))) <> "char"
               then fail() else
               let ccs = map (o (String.make 1) (o Char.chr code_of_term)) tms in
               let s = "\"" ^ String.escaped (implode ccs) ^ "\"" in
               pp_print_string fmt s
           with Failure _ ->
               pp_print_string fmt "[";
               print_term_sequence "; " 0 tms;
               pp_print_string fmt "]")
      with Failure _ ->
      if is_gabs tm then print_binder prec tm else
      let hop,args = strip_comb tm in
      let s0 = name_of hop
      and ty0 = type_of hop in
      let s = reverse_interface (s0,ty0) in
      try if s = "EMPTY" & is_const tm & args = [] then
          pp_print_string fmt "{}" else fail()
      with Failure _ ->
      try if s = "UNIV" & !typify_universal_set & is_const tm & args = [] then
            let ty = fst(dest_fun_ty(type_of tm)) in
            (pp_print_string fmt "(:";
             pp_print_type fmt ty;
             pp_print_string fmt ")")
          else fail()
      with Failure _ ->
      try if s <> "INSERT" then fail() else
          let mems,oth = splitlist (dest_binary "INSERT") tm in
          if is_const oth & fst(dest_const oth) = "EMPTY" then
            (pp_print_string fmt "{";
             print_term_sequence ", " 14 mems;
             pp_print_string fmt "}")
          else fail()
      with Failure _ ->
      try if not (s = "GSPEC") then fail() else
          let evs,bod = strip_exists(body(rand tm)) in
          let bod1,fabs = dest_comb bod in
          let bod2,babs = dest_comb bod1 in
          let c = rator bod2 in
          if fst(dest_const c) <> "SETSPEC" then fail() else
          pp_print_string fmt "{";
          print_term 0 fabs;
          pp_print_string fmt " | ";
          (let fvs = frees fabs and bvs = frees babs in
           if not(!print_unambiguous_comprehensions) &
              set_eq evs
               (if (length fvs <= 1 or bvs = []) then fvs
                else intersect fvs bvs)
           then ()
           else (print_term_sequence "," 14 evs;
                 pp_print_string fmt " | "));
          print_term 0 babs;
          pp_print_string fmt "}"
      with Failure _ ->
      try let eqs,bod = dest_let tm in
          (if prec = 0 then pp_open_hvbox fmt 0
           else (pp_open_hvbox fmt 1; pp_print_string fmt "(");
           pp_print_string fmt "let ";
           print_term 0 (mk_eq(hd eqs));
           do_list (fun (v,t) -> pp_print_break fmt 1 0;
                                 pp_print_string fmt "and ";
                                 print_term 0 (mk_eq(v,t)))
                   (tl eqs);
           pp_print_string fmt " in";
           pp_print_break fmt 1 0;
           print_term 0 bod;
           if prec = 0 then () else pp_print_string fmt ")";
           pp_close_box fmt ())
      with Failure _ -> try
        if s <> "DECIMAL" then fail() else
        let n_num = dest_numeral (hd args)
        and n_den = dest_numeral (hd(tl args)) in
        if not(powerof10 n_den) then fail() else
        let s_num = string_of_num(quo_num n_num n_den) in
        let s_den = implode(tl(explode(string_of_num
                        (n_den +/ (mod_num n_num n_den))))) in
        pp_print_string fmt("#"^s_num^(if n_den = Int 1 then "" else ".")^s_den)
      with Failure _ -> try
        if s <> "_MATCH" or length args <> 2 then failwith "" else
        let cls = dest_clauses(hd(tl args)) in
        (if prec = 0 then () else pp_print_string fmt "(";
         pp_open_hvbox fmt 0;
         pp_print_string fmt "match ";
         print_term 0 (hd args);
         pp_print_string fmt " with";
         pp_print_break fmt 1 2;
         print_clauses cls;
         pp_close_box fmt ();
         if prec = 0 then () else pp_print_string fmt ")")
      with Failure _ -> try
        if s <> "_FUNCTION" or length args <> 1 then failwith "" else
        let cls = dest_clauses(hd args) in
        (if prec = 0 then () else pp_print_string fmt "(";
         pp_open_hvbox fmt 0;
         pp_print_string fmt "function";
         pp_print_break fmt 1 2;
         print_clauses cls;
         pp_close_box fmt ();
         if prec = 0 then () else pp_print_string fmt ")")
      with Failure _ ->
      if s = "COND" & length args = 3 then
        (if prec = 0 then () else pp_print_string fmt "(";
         pp_open_hvbox fmt (-1);
         pp_print_string fmt "if ";
         print_term 0 (hd args);
         pp_print_break fmt 0 0;
         pp_print_string fmt " then ";
         print_term 0 (hd(tl args));
         pp_print_break fmt 0 0;
         pp_print_string fmt " else ";
         print_term 0 (hd(tl(tl args)));
         pp_close_box fmt ();
         if prec = 0 then () else pp_print_string fmt ")")
      else if is_prefix s & length args = 1 then
        (if prec = 1000 then pp_print_string fmt "(" else ();
         pp_print_string fmt s;
         (if isalnum s or
           s = "--" &
           length args = 1 &
           (try let l,r = dest_comb(hd args) in
                let s0 = name_of l and ty0 = type_of l in
                reverse_interface (s0,ty0) = "--" or
                mem (fst(dest_const l)) ["real_of_num"; "int_of_num"]
            with Failure _ -> false) or
           s = "~" & length args = 1 & is_neg(hd args)
          then pp_print_string fmt " " else ());
         print_term 999 (hd args);
         if prec = 1000 then pp_print_string fmt ")" else ())
      else if parses_as_binder s & length args = 1 & is_gabs (hd args) then
        print_binder prec tm
      else if can get_infix_status s & length args = 2 then
        let bargs =
          if aRIGHT s then
            let tms,tmt = splitlist (dEST_BINARY hop) tm in tms@[tmt]
          else
            let tmt,tms = rev_splitlist (dEST_BINARY hop) tm in tmt::tms in
        let newprec = fst(get_infix_status s) in
        (if newprec <= prec then
          (pp_open_hvbox fmt 1; pp_print_string fmt "(")
         else pp_open_hvbox fmt 0;
         print_term newprec (hd bargs);
         do_list (fun x -> if mem s (!unspaced_binops) then ()
                           else if mem s (!prebroken_binops)
                           then pp_print_break fmt 1 0
                           else pp_print_string fmt " ";
                           pp_print_string fmt s;
                           if mem s (!unspaced_binops)
                           then pp_print_break fmt 0 0
                           else if mem s (!prebroken_binops)
                           then pp_print_string fmt " "
                           else pp_print_break fmt 1 0;
                           print_term newprec x) (tl bargs);
         if newprec <= prec then pp_print_string fmt ")" else ();
         pp_close_box fmt ())
      else if (is_const hop or is_var hop) & args = [] then
        let s' = if parses_as_binder s or can get_infix_status s or is_prefix s
                 then "("^s^")" else s in
        pp_print_string fmt s'
      else
        let l,r = dest_comb tm in
        (pp_open_hvbox fmt 0;
         if prec = 1000 then pp_print_string fmt "(" else ();
         print_term 999 l;
         (if try mem (fst(dest_const l)) ["real_of_num"; "int_of_num"]
             with Failure _ -> false
          then () else pp_print_space fmt ());
         print_term 1000 r;
         if prec = 1000 then pp_print_string fmt ")" else ();
         pp_close_box fmt ())

    and print_term_sequence sep prec tms =
      if tms = [] then () else
      (print_term prec (hd tms);
       let ttms = tl tms in
       if ttms = [] then ()
       else (pp_print_string fmt sep; print_term_sequence sep prec ttms))

    and print_binder prec tm =
      let absf = is_gabs tm in
      let s = if absf then "\\" else name_of(rator tm) in
      let rec collectvs tm =
        if absf then
          if is_abs tm then
            let v,t = dest_abs tm in
            let vs,bod = collectvs t in (false,v)::vs,bod
          else if is_gabs tm then
            let v,t = dest_gabs tm in
            let vs,bod = collectvs t in (true,v)::vs,bod
          else [],tm
        else if is_comb tm & name_of(rator tm) = s then
          if is_abs(rand tm) then
            let v,t = dest_abs(rand tm) in
            let vs,bod = collectvs t in (false,v)::vs,bod
          else if is_gabs(rand tm) then
            let v,t = dest_gabs(rand tm) in
            let vs,bod = collectvs t in (true,v)::vs,bod
          else [],tm
        else [],tm in
      let vs,bod = collectvs tm in
      ((if prec = 0 then pp_open_hvbox fmt 4
        else (pp_open_hvbox fmt 5; pp_print_string fmt "("));
       pp_print_string fmt s;
       (if isalnum s then pp_print_string fmt " " else ());
       do_list (fun (b,x) ->
         (if b then pp_print_string fmt "(" else ());
         print_term 0 x;
         (if b then pp_print_string fmt ")" else ());
         pp_print_string fmt " ") (butlast vs);
       (if fst(last vs) then pp_print_string fmt "(" else ());
       print_term 0 (snd(last vs));
       (if fst(last vs) then pp_print_string fmt ")" else ());
       pp_print_string fmt ".";
       (if length vs = 1 then pp_print_string fmt " "
        else pp_print_space fmt ());
       print_term 0 bod;
       (if prec = 0 then () else pp_print_string fmt ")");
       pp_close_box fmt ())
  and print_clauses cls =
    match cls with
      [c] -> print_clause c
    | c::cs -> (print_clause c;
                pp_print_break fmt 1 0;
                pp_print_string fmt "| ";
                print_clauses cs)
  and print_clause cl =
    match cl with
     [p;g;r] -> (print_term 1 p;
                 pp_print_string fmt " when ";
                 print_term 1 g;
                 pp_print_string fmt " -> ";
                 print_term 1 r)
   | [p;r] -> (print_term 1 p;
               pp_print_string fmt " -> ";
               print_term 1 r)
  in print_term 0;;





let pp_print_qterm fmt tm =
  pp_print_string fmt "`";
  pp_print_term fmt tm;
  pp_print_string fmt "`";;





let pp_print_thm fmt th =
  let asl,tm = dest_thm th in
  (if not (asl = []) then
    (if !print_all_thm then
      (pp_print_term fmt (hd asl);
       do_list (fun x -> pp_print_string fmt ",";
                         pp_print_space fmt ();
                         pp_print_term fmt x)
               (tl asl))
     else pp_print_string fmt "...";
     pp_print_space fmt ())
   else ();
   pp_open_hbox fmt();
   pp_print_string fmt "|- ";
   pp_print_term fmt tm;
   pp_close_box fmt ());;





let print_type = pp_print_type std_formatter;;
let print_qtype = pp_print_qtype std_formatter;;
let print_term = pp_print_term std_formatter;;
let print_qterm = pp_print_qterm std_formatter;;
let print_thm = pp_print_thm std_formatter;;









let print_to_string printer =
  let sbuff = ref "" in
  let output s m n = sbuff := (!sbuff)^(String.sub s m n) and flush() = () in
  let fmt = make_formatter output flush in
  ignore(pp_set_max_boxes fmt 100);
  fun i -> ignore(printer fmt i);
           ignore(pp_print_flush fmt ());
           let s = !sbuff in sbuff := ""; s;;

let string_of_type = print_to_string pp_print_type;;
let string_of_term = print_to_string pp_print_term;;
let string_of_thm = print_to_string pp_print_thm;;
