(*
  A reinforcement learning environment for tactic-based proof in HOL.
  Authors: Fei Wang, Ramana Kumar
*)
open HolKernel RL_Lib RL_Goal_manager RL_Actions

datatype node = Node of {
  goal_state : RL_Goal_manager.goal_state
  , partial_action : RL_Actions.action option
  , parent : node option
(* , current page *)}

fun extract_success (Node{goal_state = RL_Goal_manager.SUCCESS th,...}) = SOME th
  | extract_success _ = NONE

fun next_actions (Node{goal_state=RL_Goal_manager.ERROR msg,...}, _): action list = [Back]
  | next_actions (Node{goal_state=RL_Goal_manager.SUCCESS thm,...}, _): action list = die("next actions: invariant failure (SUCCESS)")
  | next_actions (Node{partial_action, goal_state, ...}, excl): action list =
    case partial_action of
      NONE => top_level_actions
    | SOME (Tactic t) => List.map Tactic (tactic_actions goal_state t excl) @ [Back]
    | SOME _ => die("next_actions: invariant failure (partial non-tactic)")

fun take_action (node as Node{partial_action, goal_state, parent}) action =
  case action of
    Back => (case parent of NONE => node | SOME parent_node => parent_node)
  | Rotate =>
      (case rotate_goal_state goal_state of
        NONE => node
      | SOME new_goal_state =>
          Node
            {partial_action = partial_action,
             goal_state = new_goal_state,
             parent = SOME node})
  | Tactic t =>
    (case get_complete_tactic t of
      NONE => Node
                {partial_action = SOME action, (* assumes action continues partial_action *)
                 goal_state = goal_state,
                 parent = SOME node}
    | SOME tactic => Node
                     {partial_action = NONE,
                      goal_state = apply_tactic tactic goal_state,
                      parent = SOME node})

type observation = {
    obs_goals : observed_goal_state
  , obs_partial_action : action option
  , obs_actions : action list
  }

fun observation (node as Node{partial_action, goal_state, ...}, excl):observation =
  { obs_goals = get_observed_goal_state goal_state
  , obs_partial_action = partial_action
  , obs_actions = (next_actions (node, excl))
  } handle e => (* most likely term construction type error *)
  { obs_goals = get_observed_goal_state (RL_Goal_manager.ERROR (exnMessage e))
  , obs_partial_action = partial_action
  , obs_actions = [Back]
  }

fun partial_action_to_string (NONE) = "{?}"
  | partial_action_to_string (SOME a) = action_to_string(a)

fun str_of_numbered_action i a =
  String.concat[Int.toString i, ": ", action_to_string a]

fun observation_to_string {obs_goals, obs_partial_action, obs_actions} =
  "Current STATE:\n\n" ^ observed_goal_state_to_string(obs_goals) ^ "\n\n" ^
  "Current partial action: \n\n" ^ partial_action_to_string (obs_partial_action) ^ "\n\n" ^
  "Choose from: \n\n" ^
    (String.concatWith "\n"
      (Lib.mapi str_of_numbered_action obs_actions))

exception EndInteraction
fun get_number() =
  let
    val () = TextIO.print("Give me a number: ")
  in
    case TextIO.inputLine(TextIO.stdIn) of
      NONE => raise EndInteraction
    | SOME line =>
        (case Int.fromString line of
          NONE => 0
        | SOME n => n)
  end

fun from_node_to_observation(node, excl) =
  let
    val obs:observation = observation(node, excl)
    val obs_print:string = observation_to_string(obs)
    val () = TextIO.print(obs_print)
    val () = TextIO.print("\n")
  in
    from_observation_to_action(node, obs, excl)
  end
and from_observation_to_action(node, obs, excl) =
  let
    val choice = get_number()  (*get human choice from stdin*)
    val action = List.nth(#obs_actions obs, choice)
  in
    from_action_to_node(node, action, excl)
  end
  handle Subscript => (TextIO.print("Your choice is out of range\n");
                       from_observation_to_action(node, obs, excl))
and from_action_to_node(node, action, excl) =
  let
    val () = TextIO.print("You picked: " ^ action_to_string(action) ^ "\n")
    val new_node = take_action node action
  in
    case extract_success new_node of
      NONE => from_node_to_observation(new_node, excl)
    | SOME th => th
  end

fun initial_node g =
  Node { goal_state = initial_goal_state g,
         partial_action = NONE , parent = NONE}

fun run gtm excl = from_node_to_observation (initial_node ([],gtm), excl)

local open RL_Socket in

fun node2observation(node, sock, excl) =
  let
    val obs:observation = observation(node, excl)
    val obs_print:string = observation_to_string(obs) ^ "\n"
    val sending = sendStr(sock, obs_print)
  in
    observation2action(node, obs, sock, excl)
  end
and observation2action(node, obs, sock, excl) =
  let
    val choice = case Int.fromString(receive(sock)) of
                      NONE => raise Subscript
                    | SOME n => n
    val action = List.nth(#obs_actions obs, choice)
  in
    action2node(node, action, sock, excl)
  end
  handle Subscript => (TextIO.print("Your choice is out of range\n");
                       node2observation(node, sock, excl))
and action2node(node, action, sock, excl) =
  let
    val new_node = take_action node action
  in
    case extract_success new_node of
      NONE => node2observation(new_node, sock, excl)
    | SOME th => th
  end

fun sock_run port gtm excl =
  let
    val node = initial_node([], gtm)
    val sa = INetSock.any port;
    val sock: Socket.active INetSock.stream_sock =
      let
        val sock = INetSock.TCP.socket()
        val () = Socket.connect(sock, sa)
      in
        sock
      end
  in
    node2observation(node, sock, excl)
    before Socket.close sock
  end

end

val arguments_help = String.concat[
  "  --goal=s      : parse string s as the initial goal term (default='?x. x > 0')\n",
  "  --goal_name=s : parse string s as the initial goal term name (default='DEFAULT')\n",
  "  --socket=n    : communicate over socket (default) on port n (default=8012)\n",
  "  --interactive : communicate over stdin/out\n",
  "  --help        : print this message and exit\n"
]

fun usage name =
  (TextIO.output(TextIO.stdOut, String.concat[name," : Reinforcement Learning environment for HOL4\n\n"]);
   TextIO.output(TextIO.stdOut, String.concat["Arguments: \n"]);
   TextIO.output(TextIO.stdOut, arguments_help);
   OS.Process.exit OS.Process.success)

val all_goals =
  let val () = tacticToe.load_sigobj()
      val alls = DB.listDB()
      val phil = fn (_,(_, c)) => case c of Thm => true | _ => false
      val mapper = fn ((s1,s2),(th,_)) => (s1 ^ "." ^ s2, th)
      val all_g = List.map mapper (List.filter phil alls)
  in all_g
  end

val all_goals_length = List.length(all_goals)

fun random_goal_string() =
  let val randInt = Random.range(0, all_goals_length-1)(Random.newgen())
      val () = TextIO.print("pick random goal " ^ Int.toString(randInt) ^ " of "
      ^ Int.toString(all_goals_length) ^ " goals.\n")
      val randpick = List.nth (all_goals, randInt)
  in  ((#1 randpick), (Parse.thm_to_string (#2 randpick)))
  end

fun main() =
let
  val args = CommandLine.arguments()
  val (goal_name, goal_string) =
    (String.extract(Lib.first (String.isPrefix"--goal=") args, String.size("--goal="), NONE)
    ,String.extract(Lib.first (String.isPrefix"--goal_name=") args, String.size("--goal_name="), NONE))
      handle HOL_ERR _ => random_goal_string() (* ("DEFAULT", "?x. x > 0") *)
  val interactive = Lib.mem "--interactive" args
  val port_string =
    String.extract(Lib.first (String.isPrefix"--socket=") args, String.size("--socket="), NONE)
      handle HOL_ERR _ => "8012"
  val goal = Parse.Term[QUOTE goal_string]
    handle HOL_ERR _ => die ("Unable to parse goal term: "^goal_string)
  val port = Option.valOf(Int.fromString port_string)
    handle Option => die ("Unable to parse port: "^port_string)
in
  (
  if not (Lib.null_intersection ["--help","-h","-?"] args) then
     usage (CommandLine.name())
    else
      let
        (* [goal_name] is the list of goal names to exclude from DB.matchDB when proving *)
        val th = (if interactive then run else sock_run port) goal [goal_name]
      in
        TextIO.print("You proved: " ^ boolLib.thm_to_string th ^ "\n")
      end
      handle EndInteraction =>
        TextIO.print "Got end of stream. Bye!\n"
  ) handle e => die("unexpected exception: "^(exnMessage e))
end
