if String.isPrefix "Fail: " (General.exnMessage (General.Fail "")) then
  use "mosmlsysinfo.sml"
else
  use "polysysinfo.sml";
