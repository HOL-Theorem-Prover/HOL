val _ = print ("\nMLSYSTEM = mosml"^
               (List.nth([], 1) handle Option => "2.01" | Subscript => "2.10")^
               "\n")
