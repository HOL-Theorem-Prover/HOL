/* -*- caml -*- */

%{

open Holparsesupp
open Holdoc_init
open Holdocmodel

let delim_wrap d s = (delim_info d).sopen ^ s ^ (delim_info d).sclose

let add_to_list r xs = (r := !r @ xs)

let extractstrs ds =
  let rec go strs whites = function
      [] -> (List.rev strs, List.rev whites)
    | (MosmlStr s::ds) -> go (s::strs) whites ds
    | (d::ds) -> go strs (d::whites) ds
  in
  go [] [] ds

%}

/* content */
%token < string * bool > Ident    /* MH..D */  /* flag: alphanumeric? */
%token < string  >       Str      /* MH..D */
%token                   Dot      /* M.... */
%token < string  >       Int      /* M.... */
%token < string  >       Real     /* M.... */
%token < string  >       Word     /* M.... */
%token < string  >       Char     /* M.... */
%token < int  >          Indent   /* MH..D */
%token < string  >       White    /* MH..D */
%token < string  >       Sep      /* MH..D */
%token < string  >       Content  /* ..TX. */

/* delimiters */
%token < Holparsesupp.delim >  ToMosml
%token < Holparsesupp.delim >  ToHol
%token < Holparsesupp.delim >  ToText
%token < Holparsesupp.delim >  ToTex
%token < Holparsesupp.delim >  ToDir
%token                         From

/* directives */
%token TYPE_LIST       
%token CON_LIST        
%token FIELD_LIST      
%token LIB_LIST        
%token AUX_LIST        
%token AUX_INFIX_LIST  
%token VAR_PREFIX_LIST 
%token VAR_PREFIX_ALIST
%token HOL_OP_LIST     
%token HOL_SYM_ALIST   
%token HOL_ID_ALIST    
%token HOL_CURRIED_ALIST
%token SMART_PREFIX    
%token NO_SMART_PREFIX 
%token INDENT          
%token NOINDENT        
%token RULES           
%token NORULES         
%token COMMENTS        
%token NOCOMMENTS      
%token ECHO            
%token NOECHO          
%token RCSID           
%token HOLDELIM        
%token NEWMODE         
%token MODE            
%token SPECIAL         
%token VARS

/* low precedence (loosest) */

%nonassoc below_mosmlintertok
%nonassoc Indent
%nonassoc Str
%nonassoc White ToHol ToText ToTex ToDir

/* high precedence (tightest) */

%start tex_main
%type < Holdocmodel.texdoc > tex_main

%start mosml_main
%type < Holdocmodel.mosmldoc > mosml_main

%%

tex_main :
  tex_parse From         { $1 }

mosml_main :
  mosml_parse From       { $1 }

tex_parse :
  tex_parse_rev          { List.rev $1 }

tex_parse_rev :
  /* empty */                { [] }
| tex_parse_rev tex_content  { $2 :: $1 }

tex_content :
  Content                 { TexContent $1 }
| ToHol hol_parse From    { TexHol ((match $1 with
                                      DelimHolTex     -> TexHolLR
                                    | DelimHolTexMath -> TexHolMath
                                    | _ -> raise (NeverHappen "tex_content")),
                                    $2) }
| ToDir directive From    { TexDir $2 }

mosml_parse :
  mosml_parse_rev             { List.rev $1 }

mosml_parse_rev :
  /* empty */                     { [] }
| mosml_parse_rev mosml_token_rev { $2 @ $1 }

/* note horrible hackery to allow whitespace between Ident and
   backtick.  This whitespace (incl. comments or TeX or directives)
   appears *before* the MosmlHol in the output stream. */
/* note worse hackery: if there's an indent (i.e., newline) in between,
   it just appears as inline MosmlContent... sorry! */
mosml_token_rev :
  Str                     { [MosmlStr $1] }
| Dot                     { [MosmlContent "."] }
| Int                     { [MosmlContent $1] }
| Real                    { [MosmlContent $1] }
| Word                    { [MosmlContent $1] }
| Char                    { [MosmlContent ("#\"" ^ $1 ^ "\"")] }
| Sep                     { [MosmlContent $1] }
| Ident opt_mosml_interstuff_rev mosml_to_hol_rev
                          { $3 ($1,$2) }
| ToHol hol_parse From    { [MosmlHol(None,
                                      (match $1 with
                                         DelimHolMosml  -> MosmlHolBT
                                       | DelimHolMosmlD -> MosmlHolBTBT
                                       | _ -> raise (NeverHappen "mosml_token_rev")),
                                      $2)] }
| mosmlwhitetok           { [$1] }

mosml_to_hol_rev :
  /* empty */ %prec below_mosmlintertok
                          { fun (x,y) -> y @ [MosmlContent (fst x)] }
| ToHol hol_parse From    { fun (x,y) -> let (strs,whites) = extractstrs y in
                                         MosmlHol(Some (fst x,
                                                        List.rev strs),
                                                  (match $1 with
                                                     DelimHolMosml  -> MosmlHolBT
                                                   | DelimHolMosmlD -> MosmlHolBTBT
                                                   | _ -> raise (NeverHappen "mosml_to_hol_rev")),
                                                  $2) :: whites }

opt_mosml_interstuff_rev :
  /* empty */                             { [] }
| opt_mosml_interstuff_rev mosmlwhitetok  { $2 :: $1 }
| opt_mosml_interstuff_rev Str            { MosmlStr $2 :: $1 }

mosmlwhitetok :
  White                    { MosmlContent $1 }
| Indent                   { MosmlIndent $1 }
| ToTex tex_parse From     { MosmlTex $2 }
| ToText text_parse From   { MosmlText $2 }
| ToDir directive From     { MosmlDir $2 }


hol_parse :
  hol_parse_rev            { List.rev $1 }
                                                 
hol_parse_rev :
  /* empty */              { [] }
| hol_parse_rev hol_token  { $2 :: $1 }

hol_token :
  Ident                   { HolIdent(snd $1, fst $1) }
| Str                     { HolStr $1 }
| White                   { HolWhite $1 }
| Indent                  { HolIndent $1 }
| Sep                     { HolSep $1 }
| ToText text_parse From  { HolText $2 }
| ToTex tex_parse From    { HolTex $2 }
| ToDir directive From    { HolDir $2 }

text_parse :
  text_parse_rev          { List.rev $1 }

text_parse_rev :
  /* empty */             { [] }
| text_parse_rev text_chunk   { $2 :: $1 }

text_chunk :
  Content                 { TextContent $1 }
| ToText text_parse From  { TextText $2 }
| ToDir directive From    { TextDir $2 }

directive :
  opt_whitestuff directive0 { $2 }

directive0 :
/* category lists: */
  TYPE_LIST         ident_list      { DirThunk (fun () -> add_to_list (!curmodals.tYPE_LIST        ) $2) }
| CON_LIST          ident_list      { DirThunk (fun () -> add_to_list (!curmodals.cON_LIST         ) $2) }
| FIELD_LIST        ident_list      { DirThunk (fun () -> add_to_list (!curmodals.fIELD_LIST       ) $2) }
| LIB_LIST          ident_list      { DirThunk (fun () -> add_to_list (!curmodals.lIB_LIST         ) $2) }
| AUX_LIST          ident_list      { DirThunk (fun () -> add_to_list (!curmodals.aUX_LIST         ) $2) }
| AUX_INFIX_LIST    ident_list      { DirThunk (fun () -> add_to_list (!curmodals.aUX_INFIX_LIST   ) $2) }
| VAR_PREFIX_LIST   ident_list      { DirThunk (fun () -> add_to_list (!curmodals.vAR_PREFIX_LIST  ) $2) }
| VAR_PREFIX_ALIST  ident_alist     { DirThunk (fun () -> add_to_list (!curmodals.vAR_PREFIX_ALIST ) $2) }
| HOL_OP_LIST       ident_list      { DirThunk (fun () -> add_to_list (!curmodals.hOL_OP_LIST      ) $2) }
| HOL_SYM_ALIST     ident_alist     { DirThunk (fun () -> add_to_list (!curmodals.hOL_SYM_ALIST    ) $2) }
| HOL_ID_ALIST      ident_alist     { DirThunk (fun () -> add_to_list (!curmodals.hOL_ID_ALIST     ) $2) }
| HOL_CURRIED_ALIST curryspec_alist { DirThunk (fun () -> add_to_list (!curmodals.hOL_CURRIED_ALIST) $2) }
/* other modals: */
| SMART_PREFIX      opt_whitestuff { DirThunk (fun () -> !curmodals.sMART_PREFIX := true ) }
| NO_SMART_PREFIX   opt_whitestuff { DirThunk (fun () -> !curmodals.sMART_PREFIX := false) }
| INDENT            opt_whitestuff { DirThunk (fun () -> !curmodals.iNDENT       := true ) }
| NOINDENT          opt_whitestuff { DirThunk (fun () -> !curmodals.iNDENT       := false) }
| RULES             opt_whitestuff { DirThunk (fun () -> !curmodals.rULES        := true ) }
| NORULES           opt_whitestuff { DirThunk (fun () -> !curmodals.rULES        := false) }
| COMMENTS          opt_whitestuff { DirThunk (fun () -> !curmodals.cOMMENTS     := true ) }
| NOCOMMENTS        opt_whitestuff { DirThunk (fun () -> !curmodals.cOMMENTS     := false) }
/* other non-modals: */
| ECHO dirstuff /* used as comment in existing files sadly */
                                              { DirThunk (fun () -> eCHO  := true ) }
| NOECHO opt_whitestuff                       { DirThunk (fun () -> eCHO  := false) }
| RCSID opt_whitestuff Str opt_whitestuff     { DirThunk (fun () -> rCSID := Some $3) }
| HOLDELIM opt_whitestuff Str opt_whitestuff Str opt_whitestuff
                               { DirThunk (fun () -> hOLDELIMOPEN := $3; hOLDELIMCLOSE := $5) }
| NEWMODE opt_whitestuff Ident opt_whitestuff { DirThunk (fun () -> new_mode    (fst $3)) }
| MODE    opt_whitestuff Ident opt_whitestuff { DirThunk (fun () -> change_mode (fst $3)) }
| SPECIAL string_list          { (* must happen immediately, since it affects lexing *)
                                 add_to_list Holdoc_init.nonagg_specials $2;
                                 DirThunk (fun () -> ()) }
/* special handling: */
| VARS ident_list_b  { DirVARS $2 }  /* ignore for now */
/* unrecognised things: */
| Ident dirstuff     { if fst $1 = "C" then
                         DirThunk (fun () -> ())  (* ignore comment *)
                       else
                         raise Parse_error  (* unrecognised directive *) }
                         

ident_list :
  ident_list_b       { List.map snd $1 }

ident_list_b :
  ident_list_rev     { List.rev $1 }

ident_list_rev :
  opt_whitestuff
    { [] }
| ident_list_rev Ident opt_whitestuff
    { (snd $2, fst $2) :: $1 }

ident_alist :
  ident_alist_rev { List.rev $1 }

ident_alist_rev :
  opt_whitestuff
    { [] }
| ident_alist_rev Ident opt_whitestuff_nonl Str opt_whitestuff
    { (fst $2,$4) :: $1 }

/* curried list: note that each entry is terminated by newline,
   including the last one (ugh).  So the closing delimiter *must*
   be on a new line */

curryspec_alist :
  curryspec_alist_rev { List.rev $1 }

curryspec_alist_rev :
  opt_whitestuff { [] }
| curryspec_alist_rev curryspec_one Indent opt_whitestuff { $2 :: $1 }  

curryspec_one :
    Ident opt_whitestuff_nonl Str opt_whitestuff_nonl Ident opt_whitestuff_nonl Ident opt_whitestuff_nonl opt_ident
    { (fst $1,{ cy_cmd = $3;
                cy_arity = int_of_string (fst $5);
                cy_commas = bool_of_string (fst $7);
                cy_multiline = match $9 with None -> false
                                           | Some (b,_) -> bool_of_string b }) }
      /* default for cy_multiline is false */

opt_ident :
  /* empty */                 { None }
| Ident opt_whitestuff_nonl   { Some $1 }

string_list :
  string_list_rev { List.rev $1 }

string_list_rev :
  opt_whitestuff                  { [] }
| string_list_rev Str opt_whitestuff { $2 :: $1 }

opt_whitestuff :
  /* empty */              { () }
| opt_whitestuff whitetok  { () }

whitetok :
  White                    { () }
| Indent                   { () }
| ToText text_parse From   { () }

opt_whitestuff_nonl :
  /* empty */                        { () }
| opt_whitestuff_nonl whitetok_nonl  { () }

whitetok_nonl :
  White                    { () }
| ToText text_parse From   { () }

dirstuff :
  /* empty */           { () }
| dirstuff dirstufftok  { () }

dirstufftok :
  Ident   { () }
| Str     { () }
| White   { () }
| Sep     { () }
| Indent  { () }

%%

