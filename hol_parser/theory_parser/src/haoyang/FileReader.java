package haoyang;

import java.io.IOException;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;

import javax.swing.JOptionPane;

import animator.InfiniteProgressPanel;

//fileReader: get current dir then open all .dat files under the dir
public class FileReader {
	

	//store the current paths
	public static ArrayList<Path> currentFiles=new ArrayList<Path>();
	public static String MainFolder="";
	public static String LastThy="";
	public static HashMap<String, String> external=new HashMap<String, String>();
	public static myGraph current_g;
	//store current status: theory graph or theorem graph?
	//false: theory, true: theorem
	public static boolean status=false;
	public FileReader(String args){
		//init with HOL path
		MainFolder=MainFolder+args;
		System.out.println("current HOL path is "+MainFolder);
	}


	//load the path and store it as svgs, return the svg path
	//this is for load one dir
    public static String loadir(String args) throws IOException, InterruptedException {
		

		status=false;

		//load the path -param and return the myGraph
		String path = args;
		String cpath = System.getProperty("java.class.path");
		if (test.testmode==true)cpath="/home/haoyang/hol_parser/theory_parser/bin";
		

		cpath=(cpath.split(":"))[cpath.split(":").length-1];
		System.out.println("current path is "+path);
		System.out.println("current workpath is "+cpath);
		long etime = System.currentTimeMillis();
		System.out.println("myGraph process start, please wait");
		myGraph g=loadg(args,path);
		current_g=g;
		long stime = System.currentTimeMillis();
		System.out.printf("myGraph: Process:%d ms.\n", (stime - etime));
		if(HolParser_commands.sign==false){
			String spath=gtoSvg(g, path, cpath,0);
			return spath;
		}

		else{
			if(HolParser_commands.commandindex==1){
				System.out.println("\n");
				System.out.println("**************************************************************\n");
				System.out.println("There are "+g.errors().size()+" incompatible theorys\n");
				System.out.println("**************************************************************\n");
				System.out.println("The result of theorys' stamp incompatible check:\n");
				System.out.println(g.errors());
			}
			else if(HolParser_commands.commandindex==2){
				System.out.println("\n");
				System.out.println("**************************************************************\n");
				System.out.println("Theorems that not with tag “DISK_THM” are:");
				System.out.println("**************************************************************\n");
				TheoremParser.tag_check(FileReader.loadCurrentTheory());
			}
			else if(HolParser_commands.commandindex==3){
				System.out.println("\n");
				System.out.println("please input the theory name");
				Scanner Theoryscanner = new Scanner(System.in);
				String thyname = Theoryscanner.nextLine();
				System.out.println("**************************************************************\n");
				System.out.println("theorems from the theory that are not used in the current dependency:");
				System.out.println("**************************************************************\n");
				TheoremParser.unused_check(FileReader.loadCurrentTheory(),thyname);
			}
			return null;
		}
	}

	//load current theory graph's files
	public static ArrayList<Theory> loadCurrentTheory() throws IOException, InterruptedException {

		ArrayList<Theory> theories=new ArrayList<Theory>();
        // Theory t= new Theory();
        TheoremParser hol_theorem = new TheoremParser();
		//for each file's path
		long etime = System.currentTimeMillis();
		for(int i=0;i< currentFiles.size();i++){
			Theory t=new Theory();
			hol_theorem.Process(Files.readString(currentFiles.get(i)),t);
			theories.add(t);
		}
		long stime = System.currentTimeMillis();
		System.out.printf("loadCurrentTheory: Process:%d ms.\n", (stime - etime));
		return theories;
	}
	
	public static String loadir_multi(ArrayList<String> paths) throws IOException, InterruptedException {
		
		status=false;

		String cpath = System.getProperty("java.class.path");
		if (test.testmode==true)cpath="/home/haoyang/hol_parser/theory_parser/bin";
		cpath=(cpath.split(":"))[cpath.split(":").length-1];
		System.out.println("current path is "+paths);
		System.out.println("current workpath is "+cpath);
		long etime = System.currentTimeMillis();
		System.out.println("myGraph process start, please wait");
		myGraph g=loadgs(paths);
		current_g=g;
		//use the first dirname_multi to represent multisvg
		String path=paths.get(0);
		long stime = System.currentTimeMillis();
		System.out.printf("myGraph_multi: Process:%d ms.\n", (stime - etime));
		if(HolParser_commands.sign==false){
			String spath=gtoSvg(g, path, cpath,1);
			return spath;
		}

		else{
			if(HolParser_commands.commandindex==1){
				System.out.println("\n");
				System.out.println("**************************************************************\n");
				System.out.println("There are "+g.errors().size()+" incompatible theorys\n");
				System.out.println("**************************************************************\n");
				System.out.println("The result of theorys' stamp incompatible check:\n");
				System.out.println(g.errors());
			}
			else if(HolParser_commands.commandindex==2){
				System.out.println("\n");
				System.out.println("**************************************************************\n");
				System.out.println("Theorems that not with tag “DISK_THM” are:");
				System.out.println("**************************************************************\n");
				TheoremParser.tag_check(FileReader.loadCurrentTheory());
			}
			else if(HolParser_commands.commandindex==3){
				System.out.println("\n");
				System.out.println("please input the theory name");
				Scanner Theoryscanner = new Scanner(System.in);
				String thyname = Theoryscanner.nextLine();
				System.out.println("**************************************************************\n");
				System.out.println("theorems from the theory that are not used in the current dependency:");
				System.out.println("**************************************************************\n");
				TheoremParser.unused_check(FileReader.loadCurrentTheory(),thyname);
			}
			return null;
		}
	}


	private static String gtoSvg(myGraph g,String path,String cpath,int flag) throws InterruptedException, IOException{
		List<Vertex> DAG=g.topoSort();

		//method use dot and graphviz
		//Name the DAG as the fileNameDag

		GraphUtil graphUtil = new GraphUtil();
		String DagName=(path.split("/"))[path.split("/").length-1];
		long stime = System.currentTimeMillis();
		if(flag==1)DagName+="_multi";
		graphUtil.setSourcePath(cpath+"/"+DagName+"DAG.txt"); 
		graphUtil.setTargetPath(cpath+"/"+DagName+"DAG.svg");
				//write link a->b /n/r
		graphUtil.setSpine();
		if(status==true)graphUtil.setInverse();
		graphUtil.DAGToNode(DAG);
		graphUtil.GraphToEdge(g);

		GraphUtil.saveCodeToFile(graphUtil.getSourcePath(),graphUtil.getCode());
		//this process may cost lot of time and cause FileNotFind error!
		GraphUtil.genAndOpenGraph(graphUtil.getSourcePath(),graphUtil.getTargetPath());


		ThreadControl Rdialog=new ThreadControl();
		//start the diag thread
		Rdialog.start();
		// do{
		// 	Thread.sleep(100);
		// }while(GraphUtil.dotprogram.isAlive()==true);

		//wait for generation finish
		GraphUtil.dotprogram.waitFor();
		long etime = System.currentTimeMillis();
		System.out.printf("svg:Process:%d ms.\n", (etime - stime));

		System.out.println(graphUtil.getTargetPath());
		// if(Rdialog.isAlive())Rdialog.clueDiag.dispose();
		
		//do a stampcheck and show:
		if(status==false){
			// messageBox m=new messageBox("There are "+g.errors().size()+" incompatible theorys\r\n"+g.errors(), "The result of theorys' stamp incompatible check");
			JOptionPane.showMessageDialog(null, "There are "+g.errors().size()+" incompatible theorys\r\n"+g.errors(), "The result of theorys' stamp incompatible check", JOptionPane.INFORMATION_MESSAGE);
			//record thy's svg
			LastThy=graphUtil.getTargetPath();
		}
		
		return graphUtil.getTargetPath();
	}

	//load multigraph
	private static myGraph loadgs(ArrayList<String> paths) throws IOException {
		myGraph g = new myGraph();
		currentFiles.clear();
		for(String dirname:paths){

			
			// for each dir, do a standard dirload, but they will load into the same graph
			// check is dir then travel all .dat files
			if(Files.isDirectory(Paths.get(dirname))){

				//get paths and files
				Path dir=Paths.get(dirname);
				FileVistor filterFilesVisitor= new FileVistor();
				Files.walkFileTree(dir, filterFilesVisitor);
				List<Path> files = filterFilesVisitor.getFilenameList();
				//record all files
				currentFiles.addAll(files);
				//filter the inf
				System.out.println("task start");
				TheoryParser hol_theory = new TheoryParser();
				//for each file 
				for(int i=0;i< files.size();i++){
					hol_theory.Process(Files.readString(files.get(i)),g);
				}
			}
		}
		return g;
	}

	//care String can't edit in method so use string buffer
	private static myGraph loadg(String args,String path) throws IOException{
		currentFiles.clear();
		// check is dir then travel all .dat files
		if(Files.isDirectory(Paths.get(path))){

			//get paths and files
			Path dir=Paths.get(path);
			FileVistor filterFilesVisitor= new FileVistor();
			Files.walkFileTree(dir, filterFilesVisitor);
			List<Path> files = filterFilesVisitor.getFilenameList();

			//record current files'path
			
			currentFiles= new ArrayList<Path>(files);
			
			//filter the inf
			System.out.println("task start");
			TheoryParser hol_theory = new TheoryParser();
			myGraph g = new myGraph();


			//for each file, add the theory relation_data
			for(int i=0;i< files.size();i++){
				hol_theory.Process(Files.readString(files.get(i)),g);
			}
			return g;

		}
		return null;
	}


	//
	private static myGraph loadthorems(String thyname) throws IOException, InterruptedException{
		
		//1. status to theorem graph mode
		//2. do not clear the currentfiles
		ArrayList<Theory> theories =loadCurrentTheory();
		myGraph g = new myGraph();
		TheoryParser hol_theory = new TheoryParser();
		// //add the root: theory
		// Vertex v=new Vertex(thyname,"theorey");
        // g.addVertex(v);
		

		long etime = System.currentTimeMillis();
		

		for(Theory y:theories){
			if(y.getName().equals(thyname)){
				external.clear();
				hol_theory.Initial();
				//add the theory->its theorems
				for(Theorem t:y.getTheorems()){
					//theory->theorems
					// Edge n=new Edge(thyname, t.getName());
					// g.addEdge(thyname, t.getName());
					//use external to store external theorems
					//for each theorem,do the theorem graph generation
					hol_theory.theorem_graph(theories,t,y,g,external);
				}
				System.out.println("inner:"+hol_theory.innertheorems);
				System.out.println("external:"+hol_theory.externaltheorems);
			}
			
		}
		long stime = System.currentTimeMillis();

		System.out.printf("myGraph_theorems: Process:%d ms.\n", (stime - etime));

		return g;
	}


	//match .dat, return the FileNameList
	private static class FileVistor extends SimpleFileVisitor<Path> {

		private List<Path> FileNameList = new LinkedList<>();

		@Override
		public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
			if (file.toString().endsWith(".dat")) 
			{
				FileNameList.add(file.normalize());
			}
			return FileVisitResult.CONTINUE;
		}
		
		//return list
		public List<Path> getFilenameList() {
			return FileNameList;
		}

	}


	public static String loadthem(String theoremname) throws IOException, InterruptedException {
		
		//set the status to true: a theorem graph!
		status=true;

		String cpath = System.getProperty("java.class.path");
		if (test.testmode==true)cpath="/home/haoyang/hol_parser/theory_parser/bin";
		
		cpath=(cpath.split(":"))[cpath.split(":").length-1];
		System.out.println("current workpath is "+cpath);

		myGraph g=loadthorems(theoremname);
		String spath=gtoSvg(g, theoremname, cpath,0);

		return spath;
	}
}

