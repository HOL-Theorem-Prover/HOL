(** a few MLton-specific directives *)
val extra = _prim "Exn_extra": exn -> 'a;
val keepHistory = _command_line_const "Exn.keepHistory": bool = false;
val getOpArgsResPtr = _import "GC_getCallFromCOpArgsResPtr" runtime private: GCState.t -> Pointer.t;
val foo =
  case _build_const "MLton_Codegen_codegen": Int32.int; of
    0 => true
  | _ => false
