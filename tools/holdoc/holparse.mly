/* -*- caml -*- */

%{

open Holparsesupp
open Holdoc_init
open Holdocmodel

let delim_wrap d s = (delim_info d).sopen ^ s ^ (delim_info d).sclose

let add_to_list r xs = (r := xs @ !r)

let add_to_class_list r tbl (cls,_) xs =
  if List.mem_assoc cls !r then
    List.iter (fun x -> Hashtbl.add tbl x cls) xs
  else
    raise Parse_error  (* unknown class *)

let new_class r (cls,_) cmd =
  if List.mem_assoc cls !r then
    raise Parse_error  (* class already defined *)
  else
    r := (cls, { cl_cmd = cmd; cl_dosub = false; cl_highpri = true }) :: !r

let extractstrs ds =
  let rec go strs whites = function
      [] -> (List.rev strs, List.rev whites)
    | (MosmlStr s::ds) -> go (s::strs) whites ds
    | (d::ds) -> go strs (d::whites) ds
  in
  go [] [] ds

(* apply location of LHS symbol to value x *)
let loc : 'a -> 'a located
   = fun x ->
   (x,(symbol_start_pos (), symbol_end_pos ()))

(* apply location of RHS item n to value x *)
let loc_n : int -> 'a -> 'a located
   = fun n x ->
   (x,(rhs_start_pos n, rhs_end_pos n))

let delimmode_of_delim : Holparsesupp.delim -> texholdelimmode
    = function
      | DelimHolTex     -> TexHolLR
      | DelimHolTexMath -> TexHolMath
      | _ -> raise (NeverHappen "tex_content")

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
%token < Holparsesupp.delim >  From

/* directives */
%token CLASS
%token CLASS_LIST
%token TYPE_LIST       
%token CON_LIST        
%token FIELD_LIST      
%token LIB_LIST        
%token AUX_LIST        
%token AUX_INFIX_LIST  
%token VAR_PREFIX_LIST 
%token VAR_PREFIX_ALIST
%token AUTO_BINDERS
%token NOAUTO_BINDERS
%token HOL_OP_LIST     
%token HOL_SYM_ALIST   
%token HOL_SYM_BOL_ALIST   
%token HOL_IOPEN_LIST   
%token HOL_ICLOSE_LIST   
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
%token HOLDELIMUNBAL
%token NOHOLDELIMUNBAL
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
  Content                 { loc (TexContent $1) }
| ToHol hol_parse From    { loc (TexHol ((delimmode_of_delim $1, delimmode_of_delim $3),
                                         $2)) }
| ToDir directive From    { loc (TexDir $2) }

mosml_parse :
  mosml_parse_rev             { List.rev $1 }

mosml_parse_rev :
  /* empty */                 { [] }
| mosml_parse_rev mosml_token { $2 :: $1 }

mosml_token :
  Str                      { loc (MosmlStr $1) }
| Dot                      { loc (MosmlContent ".") }
| Int                      { loc (MosmlContent $1) }
| Real                     { loc (MosmlContent $1) }
| Word                     { loc (MosmlContent $1) }
| Char                     { loc (MosmlContent ("#\"" ^ $1 ^ "\"")) }
| Sep                      { loc (MosmlContent $1) }
| Ident                    { loc (MosmlIdent(snd $1, fst $1)) }
| White                    { loc (MosmlWhite $1) }
| Indent                   { loc (MosmlIndent $1) }
| ToHol hol_parse From     { loc (MosmlHol((match $1 with
                                              DelimHolMosml  -> MosmlHolBT
                                            | DelimHolMosmlD -> MosmlHolBTBT
                                            | _ -> raise (NeverHappen "mosml_token_rev")),
                                           $2)) }
| ToTex tex_parse From     { loc (MosmlTex $2) }
| ToText text_parse From   { loc (MosmlText $2) }
| ToDir directive From     { loc (MosmlDir $2) }

hol_parse :
  hol_parse_rev            { List.rev $1 }
                                                 
hol_parse_rev :
  /* empty */              { [] }
| hol_parse_rev hol_token  { $2 :: $1 }

hol_token :
  Ident                   { loc (HolIdent(snd $1, fst $1)) }
| Str                     { loc (HolStr $1) }
| White                   { loc (HolWhite $1) }
| Indent                  { loc (HolIndent $1) }
| Sep                     { loc (HolSep $1) }
| ToText text_parse From  { loc (HolText $2) }
| ToTex tex_parse From    { loc (HolTex $2) }
| ToDir directive From    { loc (HolDir $2) }

text_parse :
  text_parse_rev          { List.rev $1 }

text_parse_rev :
  /* empty */             { [] }
| text_parse_rev text_chunk   { $2 :: $1 }

text_chunk :
  Content                 { loc (TextContent $1) }
| ToText text_parse From  { loc (TextText $2) }
| ToDir directive From    { loc (TextDir $2) }

directive :
  opt_whitestuff directive0 { $2 }

directive0 :
/* category lists: */
| CLASS_LIST        opt_whitestuff Ident ident_list { loc (DirThunk (fun () -> add_to_class_list (!curmodals.cLASSES) (!curmodals.cLASS_IDS_LIST) $3 $4)) }
| TYPE_LIST         ident_list      { loc (DirThunk (fun () -> add_to_class_list (!curmodals.cLASSES) (!curmodals.cLASS_IDS_LIST) ("TYPE"     ,true) $2)) }
| CON_LIST          ident_list      { loc (DirThunk (fun () -> add_to_class_list (!curmodals.cLASSES) (!curmodals.cLASS_IDS_LIST) ("CON"      ,true) $2)) }
| FIELD_LIST        ident_list      { loc (DirThunk (fun () -> add_to_class_list (!curmodals.cLASSES) (!curmodals.cLASS_IDS_LIST) ("FIELD"    ,true) $2)) }
| LIB_LIST          ident_list      { loc (DirThunk (fun () -> add_to_class_list (!curmodals.cLASSES) (!curmodals.cLASS_IDS_LIST) ("LIB"      ,true) $2)) }
| AUX_LIST          ident_list      { loc (DirThunk (fun () -> add_to_class_list (!curmodals.cLASSES) (!curmodals.cLASS_IDS_LIST) ("AUX"      ,true) $2)) }
| AUX_INFIX_LIST    ident_list      { loc (DirThunk (fun () -> add_to_class_list (!curmodals.cLASSES) (!curmodals.cLASS_IDS_LIST) ("AUX_INFIX",true) $2)) }
| HOL_OP_LIST       ident_list      { loc (DirThunk (fun () -> add_to_class_list (!curmodals.cLASSES) (!curmodals.cLASS_IDS_LIST) ("HOL_OP"   ,true) $2)) }
| VAR_PREFIX_LIST   ident_list      { loc (DirThunk (fun () -> add_to_list (!curmodals.vAR_PREFIX_LIST  ) $2)) }
| VAR_PREFIX_ALIST  ident_alist     { loc (DirThunk (fun () -> add_to_list (!curmodals.vAR_PREFIX_ALIST ) $2)) }
| HOL_SYM_ALIST     ident_alist     { loc (DirThunk (fun () -> add_to_list (!curmodals.hOL_SYM_ALIST    ) $2)) }
| HOL_SYM_BOL_ALIST ident_alist     { loc (DirThunk (fun () -> add_to_list (!curmodals.hOL_SYM_BOL_ALIST) $2)) }
| HOL_IOPEN_LIST    ident_list      { loc (DirThunk (fun () -> add_to_list (!curmodals.hOL_IOPEN_LIST   ) $2)) }
| HOL_ICLOSE_LIST   ident_list      { loc (DirThunk (fun () -> add_to_list (!curmodals.hOL_ICLOSE_LIST  ) $2)) }
| HOL_ID_ALIST      ident_alist     { loc (DirThunk (fun () -> add_to_list (!curmodals.hOL_ID_ALIST     ) $2)) }
| HOL_CURRIED_ALIST curryspec_alist { loc (DirThunk (fun () -> add_to_list (!curmodals.hOL_CURRIED_ALIST) $2)) }
/* other modals: */
| CLASS             opt_whitestuff Ident opt_whitestuff Str opt_whitestuff { loc (DirThunk (fun () -> new_class (!curmodals.cLASSES) $3 $5)) }
| AUTO_BINDERS      opt_whitestuff { loc (DirThunk (fun () -> !curmodals.aUTO_BINDERS := true )) }
| NOAUTO_BINDERS    opt_whitestuff { loc (DirThunk (fun () -> !curmodals.aUTO_BINDERS := false)) }
| SMART_PREFIX      opt_whitestuff { loc (DirThunk (fun () -> !curmodals.sMART_PREFIX := true )) }
| NO_SMART_PREFIX   opt_whitestuff { loc (DirThunk (fun () -> !curmodals.sMART_PREFIX := false)) }
| INDENT            opt_whitestuff { loc (DirThunk (fun () -> !curmodals.iNDENT       := true )) }
| NOINDENT          opt_whitestuff { loc (DirThunk (fun () -> !curmodals.iNDENT       := false)) }
| RULES             opt_whitestuff { loc (DirThunk (fun () -> !curmodals.rULES        := true )) }
| NORULES           opt_whitestuff { loc (DirThunk (fun () -> !curmodals.rULES        := false)) }
| COMMENTS          opt_whitestuff { loc (DirThunk (fun () -> !curmodals.cOMMENTS     := true )) }
| NOCOMMENTS        opt_whitestuff { loc (DirThunk (fun () -> !curmodals.cOMMENTS     := false)) }
/* other non-modals: */
| ECHO dirstuff /* used as comment in existing files sadly */
                                              { loc (DirThunk (fun () -> eCHO  := true )) }
| NOECHO opt_whitestuff                       { loc (DirThunk (fun () -> eCHO  := false)) }
| RCSID opt_whitestuff Str opt_whitestuff     { loc (DirRCSID $3) }
| HOLDELIM opt_whitestuff Str opt_whitestuff Str opt_whitestuff
                               { loc (DirThunk (fun () -> hOLDELIMOPEN := $3; hOLDELIMCLOSE := $5)) }
| NEWMODE opt_whitestuff Ident opt_whitestuff { loc (DirThunk (fun () -> new_mode    (fst $3))) }
| MODE    opt_whitestuff Ident opt_whitestuff { loc (DirThunk (fun () -> change_mode (fst $3))) }
| SPECIAL string_list            { (* must happen immediately, since it affects lexing *)
                                   add_to_list Holdoc_init.nonagg_specials $2;
                                   loc (DirThunk (fun () -> ())) }
| HOLDELIMUNBAL opt_whitestuff   { (* must happen immediately, since it affects lexing *)
                                   hOLDELIMUNBAL := true;
                                   loc (DirThunk (fun () -> ())) }
| NOHOLDELIMUNBAL opt_whitestuff { (* must happen immediately, since it affects lexing *)
                                   hOLDELIMUNBAL := false;
                                   loc (DirThunk (fun () -> ())) }
/* special handling: */
| VARS ident_list_b  { loc (DirVARS $2) }  /* ignore for now */
/* unrecognised things: */
| Ident dirstuff     { if fst $1 = "C" then
                         loc (DirThunk (fun () -> ()))  (* ignore comment *)
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

