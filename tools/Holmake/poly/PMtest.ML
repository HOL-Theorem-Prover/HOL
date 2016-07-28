use "../../../tools-poly/poly/Binarymap.sig";
use "../../../tools-poly/poly/Binarymap.sml";
use "../FunctionalRecordUpdate.sml";
use "ProcessMultiplexor.sig";
use "ProcessMultiplexor.sml";

open ProcessMultiplexor;

shell_commands text_monitor
               (["for i in 1 2 3 4 5 6 7 ; do echo A$i ; sleep 2 ; done",
                 "for i in 1 2 3 4 5 6 7 ; do echo B$i ; sleep 4 ; done"],
                2);
