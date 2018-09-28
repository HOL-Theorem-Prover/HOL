structure KNametab = Table(
  type key = KernelSig.kernelname
  val ord = KernelSig.name_compare
  val pp = HOLPP.add_string o KernelSig.name_toString
);
