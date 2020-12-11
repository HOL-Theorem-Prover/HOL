(**
  Structure LassieLib

  Implements the main communication interface between HOL4 and SEMPRE
**)
structure LassieLib =
struct

  open Abbrev Tactical Manager proofManagerLib;
  open LassieUtilsLib LassieParserLib;

  exception LassieException of string;

  type sempre_response =
    { formula: string,
      result: SempreParse,
      descr: string};

  type ambiguity_warning =
    { set : string list,
      span: string };

  datatype AmbiguityWarning =
    Warning of ambiguity_warning;

  datatype GoalPart =
    All | Sub of int;

  val map = List.map
  fun mem x l = List.exists (fn x' => x = x') l
  val LASSIEPROMPT = "|>";
  val LASSIESEP = ref ".";

  val knownJargon :(string * (unit->unit)) list ref= ref [];

  val sempreResponse :sempre_response list ref = ref [];

  val ambiguityWarning : AmbiguityWarning option ref = ref NONE;

  val lastUtterance = ref "";

  (* val HOLDIR =
    let val lDir = getOSVar "HOLDIR" in
    if (endsWith lDir #"/") then lDir else (lDir ^ "/") end; *)

  val LASSIEDIR = Globals.HOLDIR ^ ("/examples/lassie");

  val historyPath = LASSIEDIR ^ "sempre/interactive/last-sempre-output.sml";

  (**************************************)
  (*           Communication            *)
  (**************************************)
  val logging = ref false;

  (* wait for the SEMPRE prompt; signifies end of execution
     returns the complete string read from SEMPRE *)
  fun waitSempre instream :string =
    let
      val s = TextIO.input(instream);
      val _ = if !logging then print s else ()
    in
      if String.isSuffix "\n> " s orelse s = "> " then s
      (* else if s = "" then raise LassieException "Reached EOS? Empty string was read."  *)
      else s ^ (waitSempre instream)
    end;

  (* run SEMPRE as a subprocess through the run script
   returns in- and outstream of its shell *)
  fun launchSempre () =
    let
      val currDir = OS.FileSys.getDir();
      (* SEMPRE's run script is dependent on being at the top of its directory *)
      val _ = OS.FileSys.chDir (LASSIEDIR ^ "/sempre")
      val instream' =
        Unix.textInstreamOf
          (Unix.executeInEnv("interactive/run",["-n","@mode=lassie"],
          Posix.ProcEnv.environ()))
      val execCommand = TextIO.input(instream')
      val (instr,outstr) =
        case String.tokens Char.isSpace execCommand of
          [] => raise Fail "Run script returned no arguments"
          | cmd::args => Unix.streamsOf(Unix.execute(cmd,args))
      val _ = waitSempre(instr);
      val _ = OS.FileSys.chDir currDir;
    in
      (ref instr, ref outstr)
    end;

  (* Start SEMPRE when the Lib file is loaded
    TODO: Box into a function? *)
  val (instream, outstream) = launchSempre();

  (* send a string to sempre *)
  fun writeSempre (cmd : string) =
    let
      (* not needed anymore as we do not load from the socket file
      val _ = if OS.FileSys.access (socketPath, []) then OS.FileSys.remove socketPath else () *)
      val _ = lastUtterance := cmd
      val _ = if !logging then (print "Writing "; print cmd; print "\n") else ()
      val _ = TextIO.output(!outstream, cmd ^ "\n")
    in
      ()
    end;

  (* Splits the response of SEMPRE into separate components based on matching
    pairs of { and } *)
  fun prepareResponse s =
  List.foldl
    (fn (xs, ys) =>
      ys @ (LassieUtilsLib.string_split xs #"}")) [] (LassieUtilsLib.string_split s #"{");

  (* Extracts text starting with descr from list xs *)
  fun getPart descr xs =
    case xs of
    [] => NONE
    | x::[] => NONE
    | x::y::xs =>
       if (String.isSuffix descr x) then
         SOME(y,xs)
       else getPart descr (y::xs);

  (* Removes a trailing quotation mark " from s *)
  fun strip_quotmark s =
    let val xs = explode s in
      if hd xs = #"\"" then implode (tl xs) else s end;

  (* read SEMPRE's response from stdin *)
  (* returns a derivation (i.e. the first candidate) of type sempre_response *)
  (* TODO: Ambiguities ? *)
  fun readSempre () :sempre_response=
  let
    val response = waitSempre (!instream) |> prepareResponse;
    val (theFormula,theResponse) =
      case getPart "Top formula " response of
      NONE => raise LassieException "Could not extract formula"
      | SOME (formula,remainder) =>
      case getPart "Top value " remainder of
      NONE => raise LassieException "Could not extract value"
      | SOME (response,remainder) =>
        (String.map (fn c => if (c = #"\n") then #" " else c) formula, response)
    val cleanedResponse =
      LassieUtilsLib.get_suffix_after_match "(string " theResponse
      |> explode |> List.rev |> implode
      |> LassieUtilsLib.get_suffix_after_match ")" (* TODO: This may be too fragile...*)
      |> explode |> List.rev |> implode
      |> strip_quotmark |> explode |> List.rev |> implode
      |> strip_quotmark |> explode |> List.rev |> implode
      |> String.map (fn c => if (c = #"$") then #" " else c)
    val _ = if !logging then (print "\n"; print cleanedResponse; print "\n") else ();
    val res = LassieParserLib.parse cleanedResponse;
  in
    { formula= theFormula, result = fst res, descr = snd res}
  end;

  (* send a NL query to sempre and return at least a derivation *)
  fun sempre utt = (writeSempre utt; readSempre ());

  (*************************************)
  (*          Main interface           *)
  (*************************************)
  fun find_matching_goal tq gl =
    let val (id,found) =
      foldl (fn (g,(id, found)) =>
        if found then (id,found) else
          let val _ = rename1 tq g in (id,true) end handle Feedback.HOL_ERR e => (id+1,false))
        (1, false)
        gl
    in
      if found then id else raise (LassieException "No matching subgoal found")
    end;

  (* parse and apply most likely tactic *)
  fun nltac (utt:'a frag list) g : goal list * validation=
    let
      (* preprocess the input string *)
      val uttStr =
        case utt of
        [QUOTE s] => LassieUtilsLib.preprocess s
        | _ => raise LassieException "Illegal input to nltac";
      val _ =
        if (not (String.isSuffix (! LASSIESEP) uttStr)) then
          raise LassieException "Tactics must end with LASSIESEP"
        else ();
      val theStrings = LassieUtilsLib.string_split uttStr #" ";
      val (gls1,vld1) = ALL_TAC g;
      val (str, pos, gls, vld) =
        (List.foldl
             (fn (str, (strAcc, goalpos, gl, vld)) =>
                if not (String.isSuffix (! LASSIESEP) str) then
                  (strAcc ^ " " ^ str, goalpos, gl, vld)
                else
                let
                  val theString = strAcc ^ " " ^ (removeTrailing (! LASSIESEP) str);
                  val t = sempre theString;
                in
                  case #result t of
                  HOLTactic t =>
                    (case goalpos of
                    All =>
                      let val (gls, vld2) = ALLGOALS t gl in
                        ("", goalpos, gls, vld o vld2) end
                    | Sub i =>
                      let val (gls, vld2) = NTH_GOAL t i gl in
                        ("", goalpos, gls, vld o vld2) end)
                  | Subgoal n => if n = ~1 then ("", All, gl, vld) else ("", Sub n, gl, vld)
                  | Termgoal t =>
                    let val id = find_matching_goal t gl in
                      ("", Sub id, gl, vld) end
                  | Command c => raise LassieException "Command found during tactic"
                end
                (* The Lassie separator was a HOL4 level token *)
                handle LassieException diag =>
                  (strAcc ^ " " ^ str, goalpos, gl, vld))
             ("", All, gls1, vld1) theStrings)
    in
      if (str = "") then (gls, vld)
      else raise LassieException ("Could not parse string "^str^"\n")
    end;

  (* define an utterance in terms of a list of utterances*)
  local
    fun define ndum niens : string =
      let
        fun extract s = case hd s of QUOTE s => LassieUtilsLib.preprocess s | _ => raise LassieException "Illegal Quote"
        (* for each utterance of the definition, get its logical form *)
        fun getFormula u = [u, (u |> sempre |> #formula |> escape |> escape)]
        (* formatting *)
        fun quot s = "\"" ^ s ^ "\""
        fun quot' s = "\\\"" ^ s ^ "\\\""
        fun list2string l = "[" ^ (String.concatWith "," l) ^ "]"
        fun stripAllSpaces s = explode s |> stripSpaces |> explode |> List.rev
          |> stripSpaces |> explode |> List.rev |> implode;
        val definiens =
          niens |> (map extract)
                |> (map getFormula)
                |> map (map stripAllSpaces)
                |> (map (map quot'))
                |> (map list2string)
                |> list2string
        val theDef = "(:def " ^ (quot (extract ndum)) ^ " " ^ (quot definiens) ^ ")"
        val _ = if (!logging) then (print "Defining:\n"; print theDef; print "\n\n") else ()
        val _ = writeSempre ("(:def " ^ (quot (extract ndum)) ^ " " ^ (quot definiens) ^ ")")
        val res = waitSempre(!instream)
        val _ = (if (!logging) then print res else ())
      in
        res
      end;
  in
    fun def cmd def = define cmd [def];
  end;

  fun addRule lhs rhs sem anchoring : unit =
    let
      fun paren str =
        let
          val clist = String.explode str
        in
          if (hd clist = #"(" andalso last clist = #")") then str
          else "(" ^ str ^ ")"
        end
    in
      (writeSempre ("(rule " ^ lhs ^ " " ^  paren rhs ^ " " ^ paren sem ^ " " ^ paren anchoring ^ ")");
      waitSempre (!instream); ())
    end;

  fun addIDRule (cat:string) (str:string) (anchoring:string) : unit =
    addRule cat str ("ConstantFn ( string \"" ^ str ^ "\")") anchoring;

  (** Adding a custom SML tactic to the grammar **)
  fun addCustomTactic tac str : unit =
    (addIDRule "$tactic" str "anchored 1";
    LassieParserLib.addCustomTactic tac str);

  (** Adding a custom SML thm tactic to the grammar **)
  fun addCustomThmTactic thmtac str: unit =
    (addIDRule "$thm->tactic" str "anchored 1";
    LassieParserLib.addCustomThmTactic thmtac str)

  (** Adding a custom SML thmlist tactic to the grammar **)
  (**
  fun addCustomThmlistTactic tac : unit =
    addIDRule "$thmlist->tactic" tac "anchored 1";

  fun addCustomTermTactic tac : unit =
    addIDRule "$term->tactic" tac "anchored 1";
  **)

  fun printGrammar () : unit =
    let
      val prev = !logging;
      val _ = logging := true;
      val _ = writeSempre ("(grammar)");
      val _ = waitSempre (!instream);
      val _ = logging := prev;
    in
      () end;

  (** Jargon Management **)

  fun registerJargon (name:string) (loader:unit->unit) =
    knownJargon := (name, loader):: !knownJargon;

  fun knownJargons () = !knownJargon;

  fun loadJargon (n:string) =
    case List.find (fn (s,f) => s = n) (!knownJargon) of
    SOME (s,f) =>  f()
    | NONE => raise LassieException ("Jargon " ^ n ^ " not found. Did you 'open' the correct library?");

  (** Interactive mode **)
  local
    fun printHelp () =
      (
      map (fn x => print (x ^"\n"))
        [ "",
          "=======================================",
          "======= Lassie Interactive Mode =======",
          "=======================================",
          " ",
          "Send natural language commands with the same keybinding as the one",
          "used to send code to you running HOL4 session.",
          "The commands will be send to Lassie and evaluated.",
          "HOL4 keybindings still work as before.",
          "Sending \"exit\" quits the session and clears the goal state,",
          "\"pause\" quits the session and keeps the goal state.",
          ""
        ]; ());
  fun getAll instream =
    case TextIO.canInput (instream,1) of
    NONE => ""
    | SOME _ =>
      (case TextIO.input1 instream of
      NONE => ""
      | SOME c => implode [c] ^ (getAll instream))
  fun proofLoop () =
    let
      (* Set up prompt; wait for input *)
      val _ = print ("\n"^LASSIEPROMPT);
      val theText =
        case (TextIO.inputLine (TextIO.stdIn)) of
        NONE => raise LassieException "Error getting input"
        | SOME s => LassieUtilsLib.preprocess (s ^ (getAll (TextIO.stdIn)))
      val theTrueText =
        LassieUtilsLib.preprocess theText
        |> LassieUtilsLib.removeTrailing ((!LASSIESEP)^"; ")
    in
      (* Handle exit keyword separately TODO: Make command? *)
      if (theTrueText = "exit")
      then (print " Exiting\n") (* ProofRecorderLib.reset()) *)
      (* Handle pause keyword separately TODO: Make command? *)
      else if (theTrueText = "pause")
      then (print "Pausing proof.\nReturn with LassieLib.nlexplain().\n")
      (* help keyword *)
      else if (theTrueText = "help")
      then (printHelp(); proofLoop())
      (* Proof step or command was given, parse with SEMPRE *)
      else
        let
          (* Remove semicolons and line-breaks from string *)
         val theString = String.translate
                            (fn x => if ((x = #"\n") orelse (x = #";")) then "" else implode [x])
                            theTrueText;
          (* Get a tactic from SEMPRE *)
          val res = theString |> sempre
          val theTactic = #descr res;
          val theResult = #result res;
          val _ = case theResult of
                  Command c => (c (); ())
                  | Subgoal _ => (print "Subgoals are not supported in verbose prove mode."; ())
                  | Termgoal _ => (print "Subgoals are not supported in verbose prove mode."; ())
                  | HOLTactic t => (et (theTactic, t); ());
          (* first print the current goal *)
          val _  = print "\n";
          val t = proofManagerLib.pp_proof (proofManagerLib.p());
          val _ = PolyML.prettyPrint (print, 80) t;
          (*
          val done =
            (let val _ = proofManagerLib.top_goal(); in false end
            handle HOL_ERR _=> true); *)
        in
          (*
          if (done)
          then (print ("Finished proof;\nPrinting proofscript\n\n" ^
                      ProofRecorderLib.pp_finished (hd(! ProofRecorderLib.finished)));
                ProofRecorderLib.reset())
          else *)
          (proofLoop())
        end
    end
  in
    fun nlexplain () =
    let
      val (asms,gl) = proofManagerLib.initial_goal();
      val _ = proofManagerLib.drop();
      val _ = proofManagerLib.gt (‘^gl’);
    in
      proofLoop()
    end;
  end;

end
