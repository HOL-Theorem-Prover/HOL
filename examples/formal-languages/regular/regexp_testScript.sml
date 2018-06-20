open HolKernel regexpLib ;

val _ = new_theory "regexp_test";

(*---------------------------------------------------------------------------*)
(* Create the deduction-based matcher                                        *)
(*---------------------------------------------------------------------------*)

fun matcher q =
  #matchfn(regexpLib.matcher regexpLib.HOL (Regexp_Type.fromQuote q));

val test = matcher `foobar`;
 not (test "fo2b") 
 andalso (test "foobar")
 andalso not(test "foobar1");

val test = matcher `\d*`;
  test"" 
andalso test"1" 
andalso test"11434123412341234235456337467456745675256245"
andalso not(test "a")
andalso not(test "_[");

val test = matcher `.*1`;
test"asdfasdfasd1" 
andalso not(test"")
andalso test"1";

val test = matcher `[0-9]`;
 not(test "")
 andalso test "1"
 andalso test "9"
 andalso test "0"
 andalso not (test "10");

val test = matcher `[0-9]*`;
 test ""
 andalso test "1"
 andalso test "9"
 andalso test "0"
 andalso test "10"
 andalso not(test " a")
 andalso test "1024563735355365673463";

val test = matcher `(.*1)(12)*`;
test "adfasd11212"
andalso test "111212"
andalso not (test"");

val test = matcher `b*|b*(a|ab*a)b*`;
test ""
andalso test "bbbb"
andalso test "bbbbabb"
andalso not (test "apha")
andalso test "a"
andalso test "baa";

val test = matcher `b*ab*ab*`;
test"bbbaa" 
andalso test"aa"
andalso test"bababb";

val test = matcher `[]*|.|..|...`;
test""
andalso test"a"
andalso test"abb"
andalso test"123"
andalso not (test"1234");

val test = matcher `.|(ab)*|(ba)*`;
test""
andalso test"a"
andalso test"7"
andalso not (test"abba")
andalso not (test"abb")
andalso test"ababababab"
andalso not (test"babababab")
andalso test"bababababa";

(* Beware the juxtaposition of * and ) in the quotation for some SML lexers. *)

val test = matcher `~((.*aa.*)|(.*bb.*))`;
             (true  = test ("")) 
   andalso   (true  = test ("a"))
   andalso   (true  = test ("b"))
   andalso   (false = test ("aa")) 
   andalso   (true  = test ("ab")) 
   andalso   (true  = test ("ba")) 
   andalso   (false = test ("bb")) 
   andalso   (true  = test ("ababababababababababababababababababababababababababab"))
   andalso   (false = test ("abababababababababababbababababababababababababababab"));

val test = matcher `(.*00.*)&~(.*01)`;
             (true  = test ("00"))
    andalso  (false = test ("001"))
    andalso  (true  = test ("0111010101010111111000000"))
    andalso  (true  = test ("011101010101011111100000010101000111111111111111111111"))
    andalso  (true  = test ("0011010101010111111000000101010001111111111111111111110"))
    andalso  (false = test ("0011010101010111111000000101010001111111111111111111101"))
   ;

(*---------------------------------------------------------------------------*)
(* All strings with at least three consecutive ones and not ending in 01 or  *)
(*   consisting of all ones.                                                 *)
(*---------------------------------------------------------------------------*)

val test = matcher `(.*111.*)&~((.*01)|1*)`;
            (true  = test "01110")
    andalso (false = test "1")
    andalso (false = test "11")
    andalso (false = test "111")
    andalso (false = test "1111111111111111111111111111111111")
    andalso (false = test "11111111111111111111111111111111111111111111111111111111")
    andalso (false = test "1111111111111111111111111111111111111111111111111111111111111111")
    andalso (true  = test "0111010101010111111000000")
    andalso (true  = test "01101010101011111100000010101000111111111111111111111")
    andalso (true  = test "10001101010101011000000101010001111111111111111111110")
    andalso (false = test "0011010101010111111000000101010001111111111111111111101")
   ;
 
(*---------------------------------------------------------------------------*)
(* Date strings                                                              *)
(*---------------------------------------------------------------------------*)

val date_matcher = time matcher 
   `(201\d|202[0-5])-([1-9]|1[0-2])-([1-9]|[1-2]\d|3[0-1]) (1?\d|2[0-3]):(\d|[1-5]\d):(\d|[1-5]\d)`;

  date_matcher "2016-5-21 20:23:24"
  andalso 
  date_matcher "2010-12-1 0:0:0"
  andalso 
  date_matcher "2019-1-22 11:11:11"
  andalso 
  date_matcher "2016-5-21 20:23:24"
  andalso 
  not (date_matcher "20162107-501-2100 20000:23000:")
  andalso 
  not (date_matcher "foo-bar-baz")
; 

(*---------------------------------------------------------------------------*)
(* UTF-8                                                                     *)
(*   Binary    Hex          Comments                                         *)
(*   0xxxxxxx  0x00..0x7F   Only byte of a 1-byte character encoding         *)
(*   10xxxxxx  0x80..0xBF   Continuation bytes (1-3 continuation bytes)      *)
(*   110xxxxx  0xC0..0xDF   First byte of a 2-byte character encoding        *)
(*   1110xxxx  0xE0..0xEF   First byte of a 3-byte character encoding        *)
(*   11110xxx  0xF0..0xF4   First byte of a 4-byte character encoding        *)
(*                                                                           *)
(* Since a 4-byte character has 5 header bits in the first byte and 3        *)
(* "payload" bits, it seems as though the Hex range should be 0xF0..0xF7,    *)
(* but there is a requirement to be compatible with UTF-16, which has        *)
(* U+10FFFF as its highest codepoint, so the Hex range is actually           *)
(* restricted to 0xF0..0xF4.                                                 *)
(*                                                                           *)
(* There are further requirements, e.g., characters need to be "minimally"   *)
(* (or canonically) encoded. This is also known as the "overlong" encoding   *)
(* issue. I am not yet sure whether this can be handled nicely with a regex. *)
(*---------------------------------------------------------------------------*)

val utf8_matcher =
 time matcher
  `([\000-\127]|[\192-\223][\128-\191]|[\224-\239][\128-\191][\128-\191]|[\240-\244][\128-\191][\128-\191][\128-\191])*`;

(*---------------------------------------------------------------------------*)
(* CANBUS GPS message format. Taken from                                     *)
(*                                                                           *)
(* http://www.caemax.de/Downloads/QIC/QIC_GPS_DE.pdf                         *)
(*                                                                           *)
(* NB: The regexp for message 1801 is wrong, since it needs data packing to  *)
(* handle bytes 4 and 5 properly.                                            *)
(*---------------------------------------------------------------------------*)
(*
 * CAN ID Name Position (Format) Range of Values Units (Result)
 * Identifier 1800 
 * Time Day Byte 0 (unsigned char) 1 ... 31 
 * Time Month Byte 1 ( unsigned char) 1 ... 12 
 * Time Year Byte 2 ( unsigned char) 0 ... 99 
 * Time Hour Byte 3 ( unsigned char) 0 … 23 
 * Time Minute Byte 4 ( unsigned char) 0 … 59 
 * Time Second Byte 5 ( unsigned char) 0 … 59 
 * Altitude Byte 6, 7 (LSB, MSB) 0 … 17999 "m" (1 m)
 *
 * Identifier 1801 
 * Latitude Degrees Byte 0 (Bit 0 ...7) -90 ... +90 "Deg" (1°)
 * Latitude Minutes Byte 1 (Bit 8 ... 13) 0 ... 59 "Min" (1’)
 * Latitude Seconds Byte 2, 3 (Bit 16 ... 28) 0 ... 5999 "Sec" (0.01“)
 * Longitude Degrees Byte 4 (Bit 32 ... 40) -180 ... +180 "Deg" (1°)
 * Longitude Minutes Byte 5 (Bit 41 ... 46) 0 ... 59 "Min" (1’)
 * Longitude Seconds Byte 6, 7 (Bit 48 ... 60) 0 ... 5999 "Sec" (0.01“)
 * 
 * Identifier 1802 
 * Speed Byte 0, 1 (LSB, MSB) 0 ... 9999 "km/h" (0.1 km/h)
 * Heading Byte 2, 3 (LSB, MSB) 0 ... 3599 "Deg" (0.1°)
 * 
 * Identifier 1803 
 * Number of Active Satellites Byte 0 (Bit 0 ... 3) 0 ... 12 
 *                             Byte 0 (Bit 4 ... 7) 0 
 * Number of Visible Satellites Byte 1 (unsigned char) 0 ... 16 
 * PDOP (vertical accuracy) Byte 2, 3 (LSB, MSB) 0 ... 999 "m" (0.1 m)
 * HDOP (horizontal accuracy) Byte 4, 5 (LSB,MSB) 0 ... 999 "m" (0.1 m)
 * VDOP (positional accuracy) Byte 6, 7 (LSB, MSB) 0 ... 999 "m" (0.1 m)
 *)
 
val test_1800 = matcher `\i{1,31}\i{1,12}\i{0,99}\i{0,23}\i{0,59}\i{0,59}\i{0,17999}`;
val test_1801 = matcher `\i{~90,90}\i{0,59}\i{0,5999}\i{~180,180}\i{0,59}\i{0,5999}`;
val test_1801_packed = matcher `\i{~90,90}\i{0,59}\i{0,5999}\p{(~180,180)(0,59).{1}}\i{0,5999}`;
val test_1802 = matcher `\i{0,9999}\i{0,3599}.{4}`;
val test_1802_alt = matcher `\i{0,9999}\i{0,3599}\k{0}{4}`;
val test_1803 = matcher `\i{0,12}\i{0,16}\i{0,999}\i{0,999}\i{0,999}`;

val test_18xx = matcher `\i{1,31}\i{1,12}\i{0,99}\i{0,23}\i{0,59}\i{0,59}\i{0,17999}\i{~90,90}\i{0,59}\i{0,5999}\i{~180,180}\i{0,59}\i{0,5999}\i{0,9999}\i{0,3599}\i{0,12}\i{0,16}\i{0,999}\i{0,999}\i{0,999}`;

(*---------------------------------------------------------------------------*)
(* Time-stamped data in JSON format                                          *)
(*---------------------------------------------------------------------------*)
(* Expensive, so commented out

val time_matcher = time matcher
  `\[\{"time":\d{13}(:\d{3})?,\w{1,20}:\{(\w{1,25}:\w{1,30},?)+\}\}\]`;

time_matcher "[{\"time\":1234567890123:000,foo:{ted:teddy,sam:sammy}}]"
  andalso 
not (time_matcher "[{\"time\":1234567890123:000,foo:{ted:teddy,   sam:sammy}}]")
  andalso
time_matcher "[{\"time\":1234567890123,foo:{ted:teddy,sam:sammy}}]"
  andalso
time_matcher "[{\"time\":1234567890123,foo:{ted:teddy}}]";
*)

(*---------------------------------------------------------------------------*)
(* Timing tests for search-only                                              *)
(*---------------------------------------------------------------------------*)
(*

val dom =
 let open regexpSyntax Regexp_Type regexpLib
     val regexpEval = Count.apply (computeLib.CBV_CONV (regexp_compset()))
 in fn quote => ignore
                (regexpEval ``dom_Brz_alt empty 
                                [normalize ^(mk_regexp(fromQuote quote))]``)
end;

val _ = 
 List.app dom
  [`1`,
   `.*1`,
   `[0-9]`,
   `[0-9]*`,
   `(.*1)(12)*`,
   `b*|b*(a|ab*a)b*`, 
   `b*ab*ab*`,
   `[]*|.|..|...`, 
   `.?|..|...`, 
   `.|(ab)*|(ba)*`,
   `~(.*(aa|bb).* )`,  (* note the additional spaces to save the SML lexer *)
   `(.*00.* )&~(.*01)`,
   `(.*111.* )&~(.*01|11* )`
  ];

print "\nDONE.\n";

dom `\w{1,2}`;
dom `\w{1,3}`;
dom `\w{1,4}`;
dom `\w{1,5}`;
dom `\w{1,6}`;
dom `\w{1,10}`;
dom `\w{1,15}`;
dom `\w{1,20}`;

*)

val _ = export_theory();
