(* File: pat.sml *)

(*---------------------------------------------------------------------------

     A type describing the SML pattern language.

 ---------------------------------------------------------------------------*)

load "mutualLib"; open mutualLib;

val tydef = 
 define_type []
        `pat = ATPATpat of atpat
             | CONpat   of 'c => atpat
             | EXCONpat of 'e => atpat ;

       atpat = WILDCARDatpat
             | SCONatpat  of 'sc
             | VARatpat   of 'v
             | CONatpat   of 'c
             | EXCONatpat of 'e
             | RECORD1atpat
             | RECORD2atpat of patrow
             | PARatpat     of pat ;

      patrow = DOTDOTDOT
             | PATROW1 of 'l => pat
             | PATROW2 of 'l => pat => patrow`;


val varcon = define_mutual_functions
{name = "varcon", rec_axiom = #New_Ty_Existence_Thm tydef,
 fixities = NONE,
 def = Term
   `(varcon_pat (ATPATpat ap)       = varcon_atpat ap) /\
    (varcon_pat (CONpat c ap)       = 1 + varcon_atpat ap) /\
    (varcon_pat (EXCONpat e a)      = 1 + varcon_atpat a) /\
    (varcon_atpat (WILDCARDatpat:('sc,'v,'c,'e,'l)atpat) = 0) /\
    (varcon_atpat (SCONatpat sc)    = 0) /\
    (varcon_atpat (VARatpat v)      = 1) /\
    (varcon_atpat (CONatpat c)      = 1) /\
    (varcon_atpat (EXCONatpat e)    = 1) /\
    (varcon_atpat RECORD1atpat      = 0) /\
    (varcon_atpat (RECORD2atpat pr) = varcon_patrow pr) /\
    (varcon_atpat (PARatpat p)      = varcon_pat p) /\
    (varcon_patrow DOTDOTDOT        = 0) /\
    (varcon_patrow (PATROW1 l p)    = varcon_pat p) /\
    (varcon_patrow (PATROW2 l p pr) = varcon_pat p + varcon_patrow pr)`};


(* The End. *)
