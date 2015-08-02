%{
 type hhterm = 
   Id of string (* may be a constant or variable *)
 | Comb of hhterm * hhterm
 | Abs of string * hhterm * hhterm;; (* name of introduced id, type and subterm *)

 let mk_uni s t = Comb (Id s, t);;
 let mk_neg t = mk_uni "~" t;;
 let mk_bin s t1 t2 = Comb (mk_uni s t1, t2);;
 let mk_lam l t = List.fold_right (fun (n, t) sf -> Abs (n, t, sf)) l t;;
 let mk_qua s l t = List.fold_right (fun (n, t) sf -> mk_uni s (Abs (n, t, sf))) l t;;
 let mk_app t1 tl = List.fold_left (fun sf e -> Comb (sf, e)) t1 tl;;

%}
%token TokEof TokParO TokParC TokDot TokComma TokQUni TokQExi TokLam TokSqrC TokEq TokNEq
%token TokAnd TokOr TokTilde TokEqvt TokNEqvt TokColon TokImpl TokFun TokAt
%token <string> TokWord
%token <string> TokUnknown


%right TokFun
%right TokImpl
%nonassoc TokEqvt TokNEqvt
%nonassoc TokEq TokNEq
%right TokOr
%right TokAnd
%nonassoc TokTilde
%left TokApp TokAt TokComma
%nonassoc TokLam TokQUni TokQExi

%start hhtop
%type <(string * string * string * hhterm)> hhtop
%%



hhtop :
  TokWord TokParO TokWord TokComma TokWord TokComma term TokParC TokDot { ($1, $3, $5, $7) }
| TokEof { raise End_of_file };

term:
| TokWord TokColon term { mk_bin ":"  (Id $1) $3 }
| term TokImpl  term { mk_bin "=>"  $1 $3 }
| TokImpl TokAt term TokAt term { mk_bin "=>" $3 $5 }
| term TokEq    term { mk_bin "="   $1 $3 }
| term TokEqvt  term { mk_bin "="   $1 $3 }
| term TokAnd   term { mk_bin "&"   $1 $3 }
| TokAnd TokAt term TokAt term { mk_bin "&" $3 $5 }
| term TokOr    term { mk_bin "|"   $1 $3 }
| TokOr TokAt term TokAt term { mk_bin "|" $3 $5 }
| term TokFun   term { mk_bin ">"   $1 $3 }
| TokTilde term       { mk_neg $2 }
| TokTilde TokAt term { mk_neg $3 }
| term TokNEq   term { mk_neg (mk_bin "=" $1 $3) }
| term TokNEqvt term { mk_neg (mk_bin "=" $1 $3) }
| TokLam  vars term  { mk_lam $2 $3 }
| TokQUni vars term  { mk_qua "!" $2 $3 }
| TokQExi vars term  { mk_qua "?" $2 $3 }
| term TokAt term    { mk_app $1 [$3] }
| termapp %prec TokApp { $1 }

termapp:
| termapp simpleterm %prec TokApp { mk_app $1 [$2] }
| simpleterm { $1 }

simpleterm:
| TokParO term TokParC {$2}
| TokWord              { Id $1 }

vars :
  TokWord TokColon term TokComma vars { ($1, $3) :: $5 }
| TokWord TokColon term TokSqrC  { [($1, $3)] };



