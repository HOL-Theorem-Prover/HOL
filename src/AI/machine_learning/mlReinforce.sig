signature mlReinforce =
sig

  include Abbrev

  type dhex = mlTreeNeuralNetwork.dhex
  type dhtnn = mlTreeNeuralNetwork.dhtnn
  type schedule = mlTreeNeuralNetwork.schedule
  type dhtnn_param = mlTreeNeuralNetwork.dhtnn_param
  type 'a ex = 'a psBigSteps.ex

  type 'a train_descr =
    {term_of_board : 'a -> term, schedule : schedule, dhtnn_param : dhtnn_param}

  type 'a guider_descr =
    {guidername : string, dhtnn : dhtnn, train_descr : 'a train_descr}
  
  type 'a rl_param =
    {
    expname : string, 
    parallel_dir : string,
    ntarget_compete : int, ntarget_explore : int,
    ex_window : int, ex_uniq : bool,
    ngen : int,
    level_start : int, level_threshold : real,
    level_targetl : int -> int -> 'a list,
    ncore_search : int, 
    par_search : (dhtnn, 'a, bool * 'a ex list) smlParallel.extspec,
    ncore_train : int
    }


  (* training *)
  val rl_train : 'a rl_param -> 'a train_descr -> 'a ex list -> dhtnn
  val rl_compete : 'a rl_param -> dhtnn -> dhtnn -> dhtnn

end
