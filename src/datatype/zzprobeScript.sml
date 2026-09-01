Theory zzprobe[bare]
Ancestors arithmetic
Libs HolKernel Parse boolLib BasicProvers

val _ = print ("ZZ parseSpec: " ^
               ((let val s = bnfFixLib.parseSpec
                                `zexpr = ZVar 'a | ZLit num | ZOp zexpr num zexpr`
                 in String.concatWith "," (#tynames s) end)
                handle e => "FAILED " ^ General.exnMessage e) ^ "\n")
