signature Type =
sig

  include FinalType where type hol_type = KernelTypes.hol_type

  val to_kt          : hol_type -> KernelTypes.hol_type
end
