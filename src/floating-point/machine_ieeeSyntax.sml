structure machine_ieeeSyntax :> machine_ieeeSyntax =
struct

structure fp16Syntax =
   fpSyntax (val thy = "machine_ieee"
             val fp = "fp16"
             val ty = ``:word16``)

structure fp32Syntax =
   fpSyntax (val thy = "machine_ieee"
             val fp = "fp32"
             val ty = ``:word32``)

structure fp64Syntax =
   fpSyntax (val thy = "machine_ieee"
             val fp = "fp64"
             val ty = ``:word64``)

end
