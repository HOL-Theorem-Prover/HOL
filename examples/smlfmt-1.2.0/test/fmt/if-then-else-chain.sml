val () =
  if theWorldIsFlat () then
    print "what's west of westeros?\n"
  else if theWorldIsRound () then
    print "east is west and west is east"
  else if theMoonIsFlat () then
    print "ah, yes, that explains it"
  else if theMoonIsRound () then
    print "what's on the other side?"
  else
    print "huh?"