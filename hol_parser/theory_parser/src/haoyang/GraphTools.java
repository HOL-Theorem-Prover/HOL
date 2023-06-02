package haoyang;
import java.util.Set;
import java.util.List;

import java.util.HashSet;
import java.util.ArrayList;
import java.util.Collections;

//states using for DFS deep first search.

//PASSED means: visiting its(children) but not end recursive function
enum VertexState {
	UNVISITED,VISITED,PASSED;
}

//Vertex
class Vertex{


    private String nodename;        
    private VertexState state;
    private String timestamp;
    private String report;


    //initial node with unvisited before build
    public Vertex(String itsname,String stamp)   
    {
        nodename = itsname;
        timestamp = stamp;
        state = VertexState.UNVISITED;
    }

    public VertexState getState(){
         return state;
    }
    public void setState(VertexState state){
         this.state=state;
    }
    public String toString(){
       return nodename;
    }
    public boolean nameEquals(String s){
        return s.equals(nodename);
    }
    public void setReport(String s){
        report=s;
    }
    public String getreporString(){
        return report;
    }

    //check timestamp
    //if false, an error stamp!
    public boolean checkTimeStamp(String s){
        return timestamp.equals(s);
    }
    public void updateStamp(String s){
        timestamp=s;
    }
} 


class Edge{

    private String start;        
    private String end; 
    
    public Edge(String startT, String endT)   
    {
        start = startT;
        end = endT;
    }

    public String getStART(){
         return start;
    }
    public String getEND(){
        return end;
    }
    public boolean Edquals(String startT, String endT){
        if(start.equals(startT)&&end.equals(endT)){
            return true;
        }
        else{
            return false;
        }
    }
    public String toString(){
        return "";
     }
} 

//DAG: Directed Acyclic Graphs
//it has vertex and edge, the relation x->y is stored in adjacent matrix 
class myGraph
    {
    //1.if build graph not under the main files: HOL, may have more theorm than the number of .dat file
    //if use map, the key can only have one value,not proper for edges
    private ArrayList<Vertex> vertexList; // vertex
    private ArrayList<Edge> edgeList;  
    private ArrayList<String> stampError;    

    public myGraph()             
    {
        //init vertex and edge 
        vertexList = new ArrayList<Vertex>();                                        
        edgeList = new ArrayList<Edge>();
        stampError = new ArrayList<String>(); 
    }

    public void addVertex(Vertex v)//function: add a new nodes v
    {
        vertexList.add(v);
    }

    //if find an incompatible theory, record it 
    public void findErrorStamp(String v,Vertex vt)
    {   
        //care, incompatible theory can appear more than one times so check exist.
        //it only returns the theory name of which has error stamp
        if(!stampError.contains(v)){
            stampError.add(v);
        }
    }

    public void findErrorStamp(String v,Vertex vt,String stamp)
    {   
        //care, incompatible theory can appear more than one times so check exist.
        //it only returns the theory name of which has error stamp
        if(!stampError.contains(v)){
            stampError.add(v);
            //if found in its theory.dat, update the stamp
            vt.updateStamp(stamp);
            }
    }
    public ArrayList<Vertex> vertexs()//
    {
        return vertexList;
    }

    public ArrayList<String> errors()//
    {
        return stampError;
    }

    public ArrayList<Edge> edges()//
    {
        return edgeList;
    }

    public boolean hasEdges(Edge e)//
    {
        return edgeList.contains(e);
    }

    public void addEdge(String start, String end)//function: add a new edge start to end
    {
        Edge e=new Edge(start, end);
        edgeList.add(e);
    }

    //delete the edge from edgelist
    private void deleteEdge(String start, String end)//function: add a new edge start to end
    {
        if(!edgeList.isEmpty()){
            for(Edge e:edgeList){
                if(e.Edquals(start, end)){
                    edgeList.remove(e);
                    break;
                }
            }
        }
    }

    //return vertex of input string
    public Vertex getVex(String name){
        for(Vertex v: vertexList){
            if(v.nameEquals(name)){
                return v;
            }
        }
        return null;
    }

    //check count v in graph
    public void printEdges()
    {   
        int count=edgeList.size();
        System.out.println("current vertexs are "+count);
    }

    public void printVexs(){
        int count=vertexList.size();
        System.out.println("current edges are "+count); 
    }

    //check for topo influence
    public void printNames(List<Vertex> vList,int count)
    {   
        System.out.println(" ");
        System.out.println("theories order are: ");
        if (vList==null){
            vList= vertexList;
        }
        for(int i=0;i<count;i++){
            System.out.println(vList.get(i).toString());
        }
    }

    //function: return children of v in Hashset
    public Set<Vertex> getChild(Vertex v){
        Set<Vertex> vSet = new HashSet<Vertex>();
        Vertex item=getVex(v.toString());
        if(item==null) return null;


        for(Edge e:edgeList){
            //cgetChild: input vertex name=edge start
            if(v.nameEquals(e.getStART())){
                //vSet add the child vex
                vSet.add(getVex(e.getEND()));
            }
        }     
        return vSet;
    }


    // //function: return parents of v in Hashset
    // private Set<Vertex> getParent(Vertex v){
    //     Set<Vertex> vSet = new HashSet<Vertex>();
    //     Vertex item=getVex(v.toString());
    //     if(item==null) return null;
    //     for(Edge e:edgeList){
    //         //cgetParent: input vertex name=edge end
    //         if(v.nameEquals(e.getEND())){
    //             //vSet add the parent vex
    //             vSet.add(getVex(e.getStART()));
    //         }
    //     }     
    //     return vSet;
    // }

    //reset state
    private void allUnVisted(){
		for(Vertex v:vertexList){
			if(v.getState() != VertexState.UNVISITED){
				v.setState(VertexState.UNVISITED);
			}
		}
	}

    //check whether v in graph
    private boolean ExistVertex(Vertex v){
        return vertexList.contains(v);
	}

    //the dfs travel
    //vList is the stack stored the degree-out 0 vertexs
    private void dfsVisit(Vertex v,List<Vertex> vList){
        Set<Vertex> children = null;
		if(!ExistVertex(v)){
			throw new IllegalStateException("error can't found vertex v as the dfs firstpoint");
		}
		v.setState(VertexState.PASSED);
		
		children = getChild(v);
		VertexState state = null;

        //for each children of v
		for(Vertex node : children){
			state = node.getState();
			if(state == VertexState.UNVISITED){
            
                //unvisited, deep in
				dfsVisit(node, vList);
			}
            //already passed
            else if(state == VertexState.PASSED){
                // 
				// throw new IllegalStateException("error found a circle when dfs");
                System.out.println("one circle occurs");
                //only keep first road, delete other roads which cause a circle!
                deleteEdge(v.toString(),node.toString());
			}
		}
		v.setState(VertexState.VISITED);//end visit
		vList.add(v);       
	}


    //Topological Sorting, the initial of DAG
    //the property of Transitive Closure
    //alorithm: do dfs, push out-degree 0 point in list
    //out-degree 0: can't move forward in graph
    //if visited: means two branch to a single leave, has circle
    //then do reverse, is the graph in topo_order
	public List<Vertex> topoSort(){
		List<Vertex> vList = new ArrayList<Vertex>();
		allUnVisted();

        //for all points(unvisited) do deepth first search

        for(Vertex v: vertexList){

			if(v.getState()== VertexState.UNVISITED){
				try{
					dfsVisit(v, vList);
				}catch (IllegalStateException e) {
					throw new IllegalStateException("error in toposort, circle in graph");
				}
			}

        }

		Collections.reverse(vList);
		return vList;
    }

}

//wtd:
//1.create graph Graph theGraph = new Graph();
//2.create new vex Vertex v1=new Vertex("c0");
//3.add vex theGraph.addVertex(v1);
//4.build edge (index i, index j);
//List<Vertex> vl=theGraph.topoSort();  