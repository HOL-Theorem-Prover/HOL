/* -*- caml -*- */

%{

open Holparsesupp
open Holdoc_init

let delim_wrap d s = (delim_info d).sopen ^ s ^ (delim_info d).sclose

let add_to_list r xs = (r := !r @ xs)

let print_string s = (Pervasives.print_string s; flush stdout)

%}

/* content */
%token < string * bool > Ident    /* MH..D */  /* flag: alphanumeric? */
%token < string  >       Str      /* MH..D */
%token                   Dot      /* M.... */
%token < string  >       Int      /* M.... */
%token < string  >       Real     /* M.... */
%token < string  >       Word     /* M.... */
%token < string  >       Char     /* M.... */
%token < int  >          Indent   /* MH... */
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


%start main
%type < unit > main

%start tex_main
%type < unit > tex_main

%start mosml_main
%type < unit > mosml_main

%%

main :
  From { () }

tex_main :
  tex_render From         { print_string $1 }

mosml_main :
  mosml_render From       { print_string $1 }

tex_render :
  /* empty */             { "" }
| tex_render tex_content  { $1 ^ $2 }

tex_content :
  Content                 { $1 }
| ToHol hol_render From   { delim_wrap $1 $2 }
| ToDir directive From    { "" }

mosml_render :
  mosml_line0             { $1 }
| mosml_render mosml_line { $1 ^ $2 }

mosml_line :
  Indent mosml_line0      { make_indent $1 ^ $2 }

mosml_line0 :
  /* empty */             { "" }
| mosml_line0 mosml_token { $1 ^ $2 }

mosml_token :
  Ident                   { fst $1 }
| Str                     { "\"" ^ $1 ^ "\"" }
| Dot                     { "." }
| Int                     { $1 }
| Real                    { $1 }
| Word                    { $1 }
| Char                    { "#\"" ^ $1 ^ "#" }
| White                   { $1 }
| Sep                     { $1 }
| ToHol hol_render From   { delim_wrap $1 $2 }
| ToText text_render From { delim_wrap $1 $2 }
| ToTex tex_render From   { delim_wrap $1 $2 }
| ToDir directive From    { "" }

hol_render :
  hol_line0               { $1 }
| hol_render hol_line     { $1 ^ $2 }

hol_line :
  Indent hol_line0        { make_indent $1 ^ $2 }

hol_line0 :
  /* empty */             { "" }
| hol_line0 hol_token     { $1 ^ $2 }

hol_token :
  Ident                   { fst $1 }
| Str                     { "\"" ^ $1 ^ "\"" }
| White                   { $1 }
| Sep                     { $1 }
| ToText text_render From { delim_wrap $1 $2 }
| ToTex tex_render From   { delim_wrap $1 $2 }
| ToDir directive From    { "" }

text_render :
  /* empty */             { "" }
| text_render text_chunk  { $1 ^ $2 }

text_chunk :
  Content                 { $1 }
| ToText text_render From { delim_wrap $1 $2 }
| ToDir directive From    { "" }

directive :
  opt_whitestuff directive0 { $2 }

directive0 :
/* category lists: */
  TYPE_LIST         ident_list      { add_to_list (!curmodals.tYPE_LIST        ) $2 }
| CON_LIST          ident_list      { add_to_list (!curmodals.cON_LIST         ) $2 }
| FIELD_LIST        ident_list      { add_to_list (!curmodals.fIELD_LIST       ) $2 }
| LIB_LIST          ident_list      { add_to_list (!curmodals.lIB_LIST         ) $2 }
| AUX_LIST          ident_list      { add_to_list (!curmodals.aUX_LIST         ) $2 }
| AUX_INFIX_LIST    ident_list      { add_to_list (!curmodals.aUX_INFIX_LIST   ) $2 }
| VAR_PREFIX_LIST   ident_list      { add_to_list (!curmodals.vAR_PREFIX_LIST  ) $2 }
| VAR_PREFIX_ALIST  ident_alist     { add_to_list (!curmodals.vAR_PREFIX_ALIST ) $2 }
| HOL_OP_LIST       ident_list      { add_to_list (!curmodals.hOL_OP_LIST      ) $2 }
| HOL_SYM_ALIST     ident_alist     { add_to_list (!curmodals.hOL_SYM_ALIST    ) $2 }
| HOL_ID_ALIST      ident_alist     { add_to_list (!curmodals.hOL_ID_ALIST     ) $2 }
| HOL_CURRIED_ALIST curryspec_alist { add_to_list (!curmodals.hOL_CURRIED_ALIST) $2 }
/* other modals: */
| SMART_PREFIX      { !curmodals.sMART_PREFIX := true  }
| NO_SMART_PREFIX   { !curmodals.sMART_PREFIX := false }
| INDENT            { !curmodals.iNDENT       := true  }
| NOINDENT          { !curmodals.iNDENT       := false }
| RULES             { !curmodals.rULES        := true  }
| NORULES           { !curmodals.rULES        := false }
| COMMENTS          { !curmodals.cOMMENTS     := true  }
| NOCOMMENTS        { !curmodals.cOMMENTS     := false }
/* other non-modals: */
| ECHO                         { eCHO  := true  }
| NOECHO                       { eCHO  := false }
| RCSID opt_whitestuff Str     { rCSID := Some $3 }
| HOLDELIM opt_whitestuff Str opt_whitestuff Str
                               { hOLDELIMOPEN := $3; hOLDELIMCLOSE := $5 }
| NEWMODE opt_whitestuff Ident { new_mode    (fst $3) }
| MODE    opt_whitestuff Ident { change_mode (fst $3) }
| SPECIAL string_list          { add_to_list Holdoc_init.nonagg_specials $2 }
/* special handling: */
| VARS ident_list   { () }  /* ignore for now */

ident_list :
  ident_list0 { List.rev $1 }

ident_list0 :
  opt_whitestuff
    { [] }
| ident_list0 Ident opt_whitestuff
    { fst $2 :: $1 }

ident_alist :
  ident_alist0 { List.rev $1 }

ident_alist0 :
  opt_whitestuff
    { [] }
| ident_alist0 Ident opt_whitestuff_nonl Str opt_whitestuff
    { (fst $2,$4) :: $1 }

/* curried list: note that each entry is terminated by newline,
   including the last one (ugh).  So the closing delimiter *must*
   be on a new line */

curryspec_alist :
  curryspec_alist0 { List.rev $1 }

curryspec_alist0 :
  opt_whitestuff { [] }
| curryspec_alist0 curryspec_one Indent opt_whitestuff_nonl { $2 :: $1 }  

curryspec_one :
    Ident opt_whitestuff_nonl Str opt_whitestuff_nonl Ident opt_whitestuff_nonl Ident opt_whitestuff_nonl opt_ident
    { (fst $1,($3,int_of_string (fst $5),bool_of_string (fst $7),
               match $9 with None -> false | Some (b,_) -> bool_of_string b)) }
      /* default final parameter is =false */

opt_ident :
  /* empty */                 { None }
| Ident opt_whitestuff_nonl   { Some $1 }

string_list :
  string_list0 { List.rev $1 }

string_list0 :
  opt_whitestuff                  { [] }
| string_list0 Str opt_whitestuff { $2 :: $1 }

opt_whitestuff :
  /* empty */              { () }
| opt_whitestuff whitetok  { $1 }

whitetok :
  White                    { () }
| Indent                   { () }
| ToText text_render From  { () }

opt_whitestuff_nonl :
  /* empty */                        { () }
| opt_whitestuff_nonl whitetok_nonl  { $1 }

whitetok_nonl :
  White                    { () }
| ToText text_render From  { () }

%%

