signature mlNearestNeighbor =
sig

  include Abbrev

  type fea = mlFeature.fea
  type thmid = mlThmData.thmid
  type stac = mlTacticData.stac
  type call = mlTacticData.call
  type symweight = mlFeature.symweight
  type 'a afea = ('a * fea) list
  
  val inter_time : real ref
  val dfind_time : real ref
  val sum_time : real ref

  (* nearest neighbor predictors *)
  val termknn: symweight * term afea -> int -> fea -> term list
  val thmknn:  symweight * thmid afea -> int -> fea -> thmid list
  val thmknn_wdep: symweight * thmid afea -> int -> fea -> thmid list
  val tacknn: symweight * stac afea -> int -> fea -> stac list
  val callknn: symweight * call afea -> int -> fea -> call list
  val add_calldep:
    (goal, call list) Redblackmap.dict -> int -> call list -> call list

  (* for comparison with tree neural networks *)
  type 'a knnpred = (symweight * term afea) * (term, 'a) Redblackmap.dict
  val train_knn: (term * 'a) list -> 'a knnpred
  val infer_knn : 'a knnpred -> term -> 'a
  val knn_accuracy: (real list) knnpred -> (term * real list) list -> real

end
