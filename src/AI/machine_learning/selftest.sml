local open mlFeature mlMatrix mlNearestNeighbor mlNeuralNetwork
  mlTacticData mlThmData mlTreeNeuralNetwork mlReinforce in end

open aiLib psTermGen mlTreeNeuralNetwork;

(* operators *)
val vx = mk_var ("x",alpha);
val vy = mk_var ("y",alpha);
val vz = mk_var ("z",alpha);
val vf = mk_var  ("f", rpt_fun_type 3 alpha);
val vg = mk_var  ("g", rpt_fun_type 2 alpha);
val vhead = mk_var ("head_", rpt_fun_type 2 alpha);
val varl = [vx,vy,vz,vf,vg];

(* examples *)
val terml = gen_term varl (8,alpha);
fun test tm = can (find_term (fn x => term_eq x vx)) tm;
val (pos,neg) = partition test terml;
val (pos',neg') = (map_assoc (fn x => 1.0) pos, map_assoc (fn x => 0.0) neg);
val ex = map (fn (a,b) => [(mk_comb (vhead,a),[b])]) (pos' @ neg');
val (trainex,testex) = part_pct 0.9 ex;

(* TNN *)
val nlayer = 1;
val dim = 16;
val randtnn = random_tnn_std (nlayer,dim) (vhead :: varl);

(* training *)
val trainparam =
  {ncore = 1, verbose = true, learning_rate = 0.02, batch_size = 16, nepoch = 2};
val schedule = [trainparam];
val tnn = train_tnn schedule randtnn (trainex,testex);

val trainparam =
  {ncore = 2, verbose = true, learning_rate = 0.02, batch_size = 16, nepoch = 2};
val schedule = [trainparam];
val tnn = train_tnn schedule randtnn (trainex,testex);
