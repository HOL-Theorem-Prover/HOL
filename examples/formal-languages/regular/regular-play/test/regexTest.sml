structure regexTest :> regexTest =
struct

  open regexEMCML;
  open regexType;




(* test cases from the paper *)
  val aObS = Rep (Alt (Sym #"a", Sym #"b"));
  val aObSc = Seq (aObS, Sym #"c");
  val regExp = Seq (Rep (Seq (aObSc, aObSc)), aObS);

  val baseTests = [
    (1, true,  Eps, ""),

    (2, true,  regExp, "acc"),
    (3, false, regExp, "accc")
  ];




(* more test cases *)
(* /opt/hol_bir/examples/PSL/regexp/test *)
(* /opt/hol_bir/src/tfl/examples/regexp.{naive/deriv} - in the end *)
(* /opt/hol_bir/examples/formal-languages/regular/test.{ml/hol} *)

  val Any = (*Alt (Sym #"0", Sym #"1", Sym #"2"Sym #"3")*)
       let
         fun toRegAlt 0 = Sym (chr 0)
           | toRegAlt i = Alt (Sym (chr i), toRegAlt (i - 1))
       in
         toRegAlt 255
       end;

  val r0  = Seq (Sym #"1", Sym #"2");
  val r1  = Rep r0;
  val r2  = Seq (Rep Any,  Sym #"1");
  val r3  = Seq (r2, r1);

  val onetwoTests = [
    (11, true,  r0, "12"),

    (12, true,  r1, "12"),
    (13, true,  r1, "1212"),
    (14, true,  r1, "1212121212"),
    (15, false, r1, "12123"),

    (16, false, r2, ""),
    (17, true,  r2, "1"),
    (18, true,  r2, "0001"),
    (19, false, r2, "0002"),

    (19, true,  r3, "00011212"),
    (19, false, r3, "00011213")
  ];


(* randomly genrated long strings, accepts sequences with a 12 sequence repetition in the end and a 1 right before - can be arbitrary before *)

(* polyml I/O - http://www.cs.cornell.edu/courses/cs312/2006fa/recitations/rec09.html *)

  fun readFile fileName maxSize =
         let
           val infile = BinIO.openIn fileName;
           fun readMax 0 l = l
             | readMax i l = 
                   let
                     val co = BinIO.input1 infile;
                   in 
                     if (co = NONE) then [] else readMax (i - 1) ((valOf co)::l)
                   end;
         in
           implode (map (fn x => chr ((Word8.toIntX x) + 128)) (readMax maxSize []))
         end;
    
  

(* performance test case collection *)
  val r4  = Seq (r1, r2);

  fun getPerformanceTests file size =
    let
      val longString = readFile file size;
    in
      [
        (101, true,  r3, longString ^ "112121212"),
        (102, false, r3, longString ^ "112121213"),
        (103, true,  r4, "12121212" ^ longString ^ "1"),
        (104, false, r4, "12121212" ^ longString ^ "3")
      ]
    end;



(* performance test case collection using big regular expressions *)
  fun genRegex reg 0 = Eps
    | genRegex reg i = Seq (reg, genRegex reg (i-1));

  fun getPerformanceTestsRegexSize file size regexLength =
    let
      val longString = readFile file size;
      val regex = Seq (Rep (Any), Seq (Sym #"1", Seq (genRegex (Sym #"2") regexLength, Sym #"1")));
    in
      [
        (201, true,  regex, longString ^ "1" ^ (implode (List.tabulate (regexLength, Lib.K #"2"))) ^ "1"),
        (202, false, regex, longString ^ "1" ^ (implode (List.tabulate (regexLength, Lib.K #"1"))) ^ "1")
      ]
    end;
(*
genRegex (Sym #"2") 0

get
*)


(* test case collection *)
  fun getTests () = baseTests @ onetwoTests;

end

