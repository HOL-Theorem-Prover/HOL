signature extra_stringLib =
sig

   include Abbrev

   val safe_list_ss             : simpLib.simpset
   val safe_string_ss           : simpLib.simpset
   val arith_string_ss          : simpLib.simpset
   val string_ss                : simpLib.simpset

   val test_eq                  : term -> term -> thm
   val toString_CONV_helper     : term -> conv
   val toString_CONV            : conv
   val toStringCAT_CONV         : conv
   val REPEAT_STRING_CONV       : (thm list) -> conv
   val REPEAT_STRINGCAT_CONV    : (thm list) -> conv

end
