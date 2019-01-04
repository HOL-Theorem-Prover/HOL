signature RL_Socket = sig
  val sendStr : ('a, Socket.active Socket.stream) Socket.sock * string -> int
  val receive : ('a, Socket.active Socket.stream) Socket.sock -> string
end
