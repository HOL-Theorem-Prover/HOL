use "../../../tools/Holmake/Systeml.sig";
use "../../../tools-poly/Holmake/Systeml.sml";

val origdir = OS.FileSys.getDir();
OS.FileSys.chDir "../../../tools-poly";
val _ = use "poly/poly-init.ML";
OS.FileSys.chDir origdir;

structure BasicIO = SML90;
exception Interrupt = SML90.Interrupt;

use "../../../tools/Holmake/hmcore.ML";

fun useB s = (use (s ^ ".sig"); use (s ^ ".sml"));

use "../poly/PrettyImpl.sml";
use "../quotation_dtype.sml";
useB "../Uref";
useB "../HOLPP";
useB "../UTF8";
useB "../OldPP";
useB "../poly/Arbnumcore";
useB "../Arbnum";
useB "../poly/Exn";
useB "../HOLquotation";
useB "../poly/MD5";
useB "../poly/Susp";
use  "../poly/Thread_Attributes.sml";
use  "../poly/Thread_Data.sml";
use  "../poly/ConcIsaLib.sml";
use  "../poly/Multithreading.sml";
use  "../poly/Unsynchronized.sml";
use  "../poly/Synchronized.sml";
use  "../poly/MLSYSPortable.sml";
useB "../Portable";
use  "../Table.sml";
useB "../AList";
use  "../Graph.sml";

(* mlyacc cruft *)
fun MLYuse s = use ("../../../tools/mlyacc/mlyacclib/MLY_" ^ s ^ ".sml");
MLYuse "base-sig";
MLYuse "join";
MLYuse "lrtable";
MLYuse "stream";
MLYuse "parser2";

use  "../HOLsexp_dtype.sml";

use  "../HOLsexp.grm-sig.sml";
use  "../HOLsexp.grm.sml";
use  "../HOLsexp.lex.sml";
useB "../HOLsexp_parser";
useB "../HOLsexp";
use  "RawTheory_dtype.sml";
useB "RawTheoryReader";

useB "../poly/SHA1_ML";
useB "../SHA1";

use "theorystats.sml";
use "theorytool.ML";
