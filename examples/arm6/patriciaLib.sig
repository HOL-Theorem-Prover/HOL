signature patriciaLib =
sig
  type 'a pnode;
  type 'a ptree;

  val empty : 'a ptree;
  val member : word -> 'a ptree -> {data : 'a, key : word} option
  val add : {data : 'a, key : word} -> 'a ptree -> 'a ptree
  val update : {data : 'a, key : word} -> 'a ptree -> 'a ptree
  val remove : word -> 'a ptree -> 'a ptree
  val keys : 'a ptree -> word list
end
