val libc_name =
    if Systeml.OS = "macosx" then "/usr/lib/libSystem.B.dylib"
    else
      let val a = case Mosml.run "uname" ["-m"] "" of
                      Mosml.Success s => s
                    | _ => raise Fail "No uname output"
      in
        "/lib/" ^ a ^ "-linux-gnu/libc.so.6" (* Ubuntu *)
      end

val libc = Foreign.loadLibrary libc_name

val ioctlsym = Foreign.getSymbol libc "ioctl"

val winsz_conv =
    Foreign.cStar (
      Foreign.cStruct4 (
        Foreign.cUshort, Foreign.cUshort, Foreign.cUshort, Foreign.cUshort
      )
    )

local
val wszref = ref (0,0,0,0)

val ioctl = Foreign.buildCall3 (
      ioctlsym,
      (Foreign.cInt, Foreign.cInt, winsz_conv),
      Foreign.cVoid
    )
in
fun getxy() =
    (ioctl(1, CDefines.TIOCGWINSZ, wszref);
     (#2 (!wszref), #1 (!wszref)));
end
