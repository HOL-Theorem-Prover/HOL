structure HolMlyValue = 
struct
datatype svalue = VOID 
                | ntVOID of unit 
                | string_ of  (string)
                | aq of  (Term.term)
                | qualified_binder of  string*string
                | binder of  (string)
                | type_var_ident of  (string)
                | qualified_type_ident of  string*string
                | type_ident of  (string) 
                | qualified_ident of  string*string
                | symbolic_ident of  (string) 
                | ident of  (string)
                | CARGS of  (Type.hol_type list)
                | CLAUSE of ({ constructor:string,args:Type.hol_type list } )
                | CLAUSES of {constructor:string,
                              args:Parse_support.arg list} list
                | TYID of  (string)
                | TYSPEC of { ty_name:string,
                              clauses: {constructor:string,
                                        args:Parse_support.arg list} list } 
                | BASIC of  (Type.hol_type) 
                | TYPE_LIST of  (Type.hol_type list)
                | TYPE_ARG of  (Type.hol_type list) 
                | TYPE of  (Type.hol_type)
                | LIST of  (Parse_support.preterm_in_env list) 
                | COMMA of  (unit)
                | BINDL of  ( ( Parse_support.binder_in_env list 
                                * Parse_support.preterm_in_env )  list)
                | VSTRUCT of  (Parse_support.binder_in_env list) 
                | BV of  (Parse_support.binder_in_env)
                | BVL of  (Parse_support.binder_in_env list) 
                | SUFFIX of  (Parse_support.preterm_in_env)
                | AEXP of  (Parse_support.preterm_in_env) 
                | APP of  (Parse_support.preterm_in_env list)
                | PTRM of  (Parse_support.preterm_in_env) 
                | START of  (Parse_support.parse)
end
