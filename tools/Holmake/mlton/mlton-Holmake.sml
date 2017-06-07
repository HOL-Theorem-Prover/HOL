Holmake.main()
  handle e => Holmake.die_with ("Holmake failed with exception: "^
                                exnMessage e)
;
