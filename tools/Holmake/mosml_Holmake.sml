val die_with = Holmake.die_with

val _ = Holmake.main()
        handle Interrupt => die_with "Holmake interrupted"
             | e => die_with ("Holmake failed with exception: " ^
                              exnMessage e)
