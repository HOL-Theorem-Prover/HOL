open HolKernel Parse boolLib bossLib;


open EmitML;
open basis_emitTheory;

open regexExecutableTheory;
open regexMarkedTheory;
open regexCachedMarkedTheory;


val _ = new_theory "emit_regex";




(* prepare empty directory *)
(* ============================================================================================== *)

val emitDir = OS.Path.concat(OS.FileSys.getDir(), "../emit");

val _ = ignore (OS.Process.system ("rm -rf " ^ emitDir));

val _ = if (not (OS.FileSys.access(emitDir, []))) then (OS.FileSys.mkDir emitDir) else ();






(* emit the regexEMCML library *)
(* ============================================================================================== *)

(* regexExecutableTheory *)

val defsE = map DEFN [split_def, parts_def, accept_def];

val datatypeDefE = DATATYPE regexDatatypes.Reg_datatype_quot;



(* regexMarkedTheory *)

val defsM = map DEFN [MARK_REG_def, empty_def, final_def, shift_def, acceptM_def];

val datatypeDefM = DATATYPE regexDatatypes.MReg_datatype_quot;



(* regexCachedMarkedTheory *)

val defsCM = map DEFN [cempty_def, cfinal_def, cmEps_def, cmSym_def, cmAlt_def,
                       cmSeq_def, cmRep_def, CACHE_REG_def, cshift_def, acceptCM_def];

val datatypeDefCMReg   = DATATYPE regexDatatypes.CMReg_datatype_quot;



(* bundle everything and emit as SML library *)

val name = "regexEMC";

val contents =
  (OPEN ["list"])::
  (datatypeDefE)::
  (datatypeDefM)::
  (datatypeDefCMReg)::
  (defsE @ defsM @ defsCM);

val _ = emitML emitDir (name, contents);
(*val _ = eSML name contents;*)





(* copy dependencies *)
(* ============================================================================================== *)

fun copyDep name =
        ignore (List.map (fn suffix => ignore (OS.Process.system ("cp " ^ (OS.Path.concat(!Globals.emitMLDir, name ^ suffix)) ^ " " ^ emitDir))) ["ML.sml", "ML.sig"]);



copyDep "combin";
copyDep "pair";
copyDep "num";
copyDep "list";
copyDep "rich_list";



val _ = export_theory ();


