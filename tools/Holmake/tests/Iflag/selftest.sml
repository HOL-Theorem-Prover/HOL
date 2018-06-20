open testutils

val _ = tprint "Testing Holmake -I includethis"

val res = OS.Process.system (Systeml.HOLDIR ^ "/bin/Holmake -q -I includethis BTheory.uo 2> /dev/null");

val _ = if OS.Process.isSuccess res then OK()
        else die "\b\b\bFAILED"
