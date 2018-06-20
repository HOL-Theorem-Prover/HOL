%{
 open Fusion;;
 open Bool;;
 let ind_ty = Tyapp ("$i", []);;
 let is_uppercase c = 'A' <= c.[0] && c.[0] <= 'Z';;
 let domkconst name args rty =
   if name = "$true" then Fusion.mk_const ("T", []) else
   if name = "$false" then Fusion.mk_const ("F", []) else
   let needty = List.fold_left (fun sofar _ -> mk_fun_ty ind_ty sofar) rty args in
   (try
     ignore (get_const_type name)
    with Failure _ -> new_constant (name, needty));
   List.fold_left (fun sofar arg -> mk_comb (sofar, arg)) (mk_const (name, [])) args
 ;;
 let mk_indv s = mk_var (s, ind_ty);;
 let quant q tm vars = List.fold_right (fun var tm -> (if q = "!" then mk_forall else mk_exists) (mk_indv var, tm)) vars tm;;
 let mk_eq (a,b) = try mk_eq (a,b) with Failure _ -> mk_var ("fof_parse_error:eq", bool_ty);;
 let mk_imp (a,b) = try mk_imp (a,b) with Failure _ -> mk_var ("fof_parse_error:imp", bool_ty);;
 let mk_conj (a,b) = try mk_conj (a,b) with Failure _ -> mk_var ("fof_parse_error:conj", bool_ty);;
 let mk_disj (a,b) = try Basics.mk_binary "\\/" (a,b) with Failure _ -> mk_var ("fof_parse_error:disj", bool_ty);;
 let pnot = Hl_parser.parse_term "~";;
 let mk_neg a = try Fusion.mk_comb (pnot, a) with Failure _ -> mk_var ("fof_parse_error:neg", bool_ty);;
 let domkconst a b c = try domkconst a b c with Failure _ -> mk_var ("fof_parse_error:const", c);;
 let quant a b c = try quant a b c with Failure _ ->  mk_var ("fof_parse_error:quant", bool_ty);;
%}

%token <string> Word
%token <string list> All
%token <string list> Exists
%token Eof Openp Closep Dot Comma Eq Neq Tilde Eqvt Neqvt Impl And Or
%right Impl
%nonassoc Eqvt
%nonassoc Eq Neq
%right Or
%left And
%nonassoc Tilde
%nonassoc All Exists

%start hhtop
%type <(string * string * string * term)> hhtop

%%

hhtop :
  Word Openp Word Comma Word Comma formula Closep Dot { ($1, $3, $5, $7) }
| Eof { raise End_of_file };

formula :
  Word { domkconst $1 [] bool_ty }
| Word Openp ts { domkconst $1 $3 bool_ty }
| fterm Eq fterm { mk_eq ($1, $3) }
| fterm Neq fterm { mk_neg (mk_eq ($1, $3)) }
| All formula { quant "!" $2 $1 }
| Exists formula { quant "?" $2 $1 }
| formula Eqvt formula { mk_eq ($1, $3) }
| formula Neqvt formula { mk_neg (mk_eq ($1, $3)) }
| formula Impl formula { mk_imp ($1, $3) }
| Tilde formula { mk_neg $2 }
| formula And formula { mk_conj ($1, $3) }
| formula Or formula { mk_disj ($1, $3) }
| Openp formula Closep { $2 }

fterm :
  Word { if is_uppercase $1 then mk_var ($1, ind_ty) else domkconst $1 [] ind_ty }
| Word Openp ts { domkconst $1 $3 ind_ty }

ts :
  fterm Comma ts { $1 :: $3 }
| fterm Closep   { [$1] };
