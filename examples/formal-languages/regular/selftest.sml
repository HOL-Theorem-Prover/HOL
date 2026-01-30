open HolKernel regexpLib testutils

val testlevel =
    case OS.Process.getEnv "TESTLEVEL" of
        NONE => 0
      | SOME s => (case Int.fromString s of
                           NONE => 0
                         | SOME i => i)

fun exitIfLevelLE n =
    if testlevel <= n then OS.Process.exit OS.Process.success
    else print ("\nTest-level > " ^ Int.toString n ^ "\n")


(*---------------------------------------------------------------------------*)
(* Matchers                                                                  *)
(*---------------------------------------------------------------------------*)

fun matcher q = #matchfn(regexpLib.gen_dfa regexpLib.HOL (Regexp_Type.fromQuote q));

fun boolcheck pfx0 f (s, result) = let
  val pfx = if size pfx0 <= 20 then pfx0 else "r.e."
in
  tprint ("⟨" ^ pfx ^ "⟩ on \"" ^ s ^ "\" = " ^ Bool.toString result);
  require_msg
    (check_result (fn b => b = result))
    Bool.toString
    f s
end

fun kill_locncomment s =
    let open Substring
        val ss = full s
        val (_, ss') = position "*)" ss
    in
      string (slice(ss',2,NONE))
    end

fun tests (q as [QUOTE s0]) checks =
    let
      val s = kill_locncomment s0
      fun k (Res test) = List.app (boolcheck s test) checks
        | k (Exn _) = raise Fail "Can't happen"
      val _ = print "\n"
      val _ = tprint ("(HOL-)Compiling r.e. ⟨" ^ s ^ "⟩")
    in
      require_msgk
        (check_result (fn _ => true))
        (fn m => PP.add_string "<a matcher>")
        (quietly matcher) k q
    end

val _ = tests `foobar` [
      ("fo2b", false),
      ("foobar", true),
      ("foobar1", false)
    ];

val _ = tests `\d*` [
      ("", true),
      ("1", true),
      ("11434123412341234235456337467456745675256245", true),
      ("a", false),
      ("_[", false)
    ];

val _ = tests `.*1` [
          ("asdfasdfasd1", true),
          ("", false),
          ("1", true)
        ];

val _ = tests `[0-9]` [
      ("", false),
      ("1", true),
      ("9", true),
      ("0", true),
      ("10", false)
    ];

val _ = tests `[0-9]*` [
      ("", true),
      ("1", true),
      ("9", true),
      ("0", true),
      ("10", true),
      (" a",false),
      ("1024563735355365673463", true)
    ];

val _ = tests `(.*1)(12)*` [
      ("adfasd11212", true),
      ("111212", true),
      ("", false)
    ];

val _ = tests `b*|b*(a|ab*a)b*` [
      ("", true),
      ("bbbb", true),
      ("bbbbabb", true),
      ("apha", false),
      ("a", true),
      ("baa", true)
    ];

val _ = tests `b*ab*ab*` [
      ("bbbaa", true),
      ("aa", true),
      ("bababb", true)
    ];

val _ = exitIfLevelLE 1

val _ = tests `[]*|.|..|...` [
      ("", true),
      ("a", true),
      ("abb", true),
      ("123",true),
      ("1234", false)
    ];

val _ = tests `.|(ab)*|(ba)*` [
      ("", true),
      ("a", true),
      ("7", true),
      ("abba", false),
      ("abb",false),
      ("ababababab", true),
      ("babababab", false),
      ("bababababa", true)
    ];

(* Beware the juxtaposition of * and ) in the quotation for some SML lexers. *)
val _ = tests `~((.*aa.*)|(.*bb.*))` [
      ("", true),
      ("a", true),
      ("b", true),
      ("aa", false),
      ("ab", true),
      ("ba", true),
      ("bb", false),
      ("ababababababababababababababababababababababababababab", true),
      ("abababababababababababbababababababababababababababab", false)
    ];

val _ = tests `(.*00.*)&~(.*01)` [
      ("00", true),
      ("001", false),
      ("0111010101010111111000000", true),
      ("011101010101011111100000010101000111111111111111111111", true),
      ("0011010101010111111000000101010001111111111111111111110", true),
      ("0011010101010111111000000101010001111111111111111111101", false)
    ];

(*---------------------------------------------------------------------------*)
(* All strings with at least three consecutive ones and not ending in 01 or  *)
(*   consisting of all ones.                                                 *)
(*---------------------------------------------------------------------------*)

val _ = tests `(.*111.*)&~((.*01)|1*)` [
  ("01110", true),
  ("1", false),
  ("11",false),
  ("111",false),
  ("1111111111111111111111111111111111",false),
  ("11111111111111111111111111111111111111111111111111111111",false),
  ("1111111111111111111111111111111111111111111111111111111111111111",false),
  ("0111010101010111111000000",true),
  ("01101010101011111100000010101000111111111111111111111",true),
  ("10001101010101011000000101010001111111111111111111110",true),
  ("0011010101010111111000000101010001111111111111111111101",false)
  ] ;

val _ = exitIfLevelLE 2

(*---------------------------------------------------------------------------*)
(* Date strings                                                              *)
(*---------------------------------------------------------------------------*)

val _ = tests
   `(201\d|202[0-5])-([1-9]|1[0-2])-([1-9]|[1-2]\d|3[0-1]) (1?\d|2[0-3]):(\d|[1-5]\d):(\d|[1-5]\d)` [
  ("2016-5-21 20:23:24", true),
  ("2010-12-1 0:0:0", true),
  ("2019-1-22 11:11:11", true),
  ("2016-5-21 20:23:24", true),
  ("20162107-501-2100 20000:23000:", false),
  ("foo-bar-baz", false)
];

val _ = exitIfLevelLE 3

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

(* message formats via intervals *)

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
val test_1802 = matcher `\i{0,9999}\i{0,3599}.{4}`;
val test_1802_alt = matcher `\i{0,9999}\i{0,3599}\k{0}{4}`;
val test_1803 = matcher `\i{0,12}\i{0,16}\i{0,999}\i{0,999}\i{0,999}`;

val test_18xx = matcher `\i{1,31}\i{1,12}\i{0,99}\i{0,23}\i{0,59}\i{0,59}\i{0,17999}\i{~90,90}\i{0,59}\i{0,5999}\i{~180,180}\i{0,59}\i{0,5999}\i{0,9999}\i{0,3599}\i{0,12}\i{0,16}\i{0,999}\i{0,999}\i{0,999}`;


matcher `\i{1,31}`;
matcher `\i{1,31}\i{1,12}\i{0,99}\i{0,23}\i{0,59}\i{0,59}`;
matcher `\i{~90,90}`;
matcher `\i{~180,180}`;
matcher `\i{0,17999}`;
matcher `\i{1,31}\i{1,12}\i{0,99}\i{0,23}\i{0,59}\i{0,59}\i{0,17999}`;
matcher `.{8}\i{0,1}\i{~90,90}\i{0,360}`;
matcher `.{8}(t|f)\i{~90,90}\i{0,360}`;

(* gps *)
matcher `\i{~90,90}\i{~180,180}\{0,17999}`;
matcher `(\i{~90,90}\i{~180,180}\{0,17999}){4}`;  (* slow *)
matcher `.{8}(t|f)(\i{~90,90}\i{~180,180}\{0,17999}){4}`; (* slow *)
