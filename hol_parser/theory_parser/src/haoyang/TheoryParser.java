package haoyang;
import java.io.File;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

import javax.naming.InitialContext; 

//TheoryParser: read theory structure in .dat files then add it into the graph
//Theory inf: in first nested bracket after (theory


public class TheoryParser {

    //set enum:
    public enum States { STARTING, TOKEN, BETWEEN };
    //the bracket stack
    int theoryStack;
    int theorySign;
    int innertheorems;
    int externaltheorems;

    public void Initial(){
        innertheorems=0;
        externaltheorems=0;
    }
    //extract parent nodes inf and store it
    //extract the theory inf from one file under the dir

    public void Process(String dat_content,myGraph g)
    {
        States state = States.STARTING;
        theoryStack=0;
        theorySign=0;

        //create new empty ArrayList string for storing inf
        ArrayList<String> theoryName = new ArrayList<String>();

        //temp to store the current input
        StringBuffer Stemp = new StringBuffer("");
        String cString;


        //extract the theory names in .dat
        for (int i = 0; i < dat_content.length() ; i++)
        {
            //travel every char in the string 
            char cTemp = dat_content.charAt(i);
            switch (cTemp)
            {

                //check bracket: stack check
                //TOKEN: has cTemp
                //Between: last input is a bracket (recored cTemp last step)
                case '(':
                {
                    if (state == States.STARTING)  state = States.BETWEEN;
                    else if (state == States.BETWEEN)  {theoryStack=theoryStack+1;} 
                    else if (state == States.TOKEN )
                    {

                        state = States.BETWEEN;
                        
                        cString=Stemp.toString().trim();
                        if(cString.equals("theory")||theoryStack>0){
                            //after read theory, start record theory till stack return 0
                            theorySign=1;
                            theoryStack=theoryStack+1;
                            theoryName.add(cString);
                        }
                        //free the temp
                        Stemp.delete(0,Stemp.length());

                    }
                    break;
                }

                case ')':
                {
                    if (state == States.STARTING) 
                    {  /* this is an error */ }
                    else if (state == States.TOKEN) 
                    {
                        cString=Stemp.toString().trim();
                        theoryName.add(cString);
                        theoryStack=theoryStack-1;
                        Stemp.delete(0,Stemp.length());
                        state = States.BETWEEN;
                    } 
                    else if (state == States.BETWEEN) {theoryStack=theoryStack-1;}
                    break;
                }

                default:
                {   
                    //some space between the bracket units and don't want it recorded
                    //they are not in the lowest nested bracket, I still want to use those space for split
                    if(!Character.isWhitespace(cTemp)||state != States.BETWEEN){
                        state = States.TOKEN;
                        //record the char
                        Stemp.append(cTemp);
                    }
                }
            }
            //end of bracket 1
            if(theorySign==1&&theoryStack==0)break;
        }

        // PrintArrayList(theoryName);
        graph_input(theoryName,g);
    }

    // regex extract the theory itself and its parents
    //its for theorys
    public static void graph_input(ArrayList<String> theList,myGraph g)
    {   

        //start from 1, 0 is "theory"
        String itName=  theList.get(1).split("\\s+")[0].replace("\"", "");
        //e.g. theoryname, string,string,  all strings except theory name are the timestamp
        String stamp="";
        //[1,2,3,4,5].copyOfRange(1,4)=234
        //do a slice, from the second to the end.
        String[] itstamps = Arrays.copyOfRange((theList.get(1).split("\\s+")),1,(theList.get(1).split("\\s+")).length);
        //also record the stamp
        for(String s:itstamps){
            s=s.replace("\"", "");
            stamp+=s;
        }

        // add itself 

        //create if not find, create new vex, add vex into the graph
        //each time check whether its in the currentFiles,if not, search and add it.
        if(g.getVex(itName)==null){
            Vertex v=new Vertex(itName,stamp);

            StringBuffer s=new StringBuffer("");
            //please set the HOL main folder
            File dir = new File(FileReader.MainFolder);
            String filename=itName+"Theory.dat";
            TheoremParser.searchFile(dir,filename,s);
            String report=v.toString()+"-"+itName+":"+s.toString()+"\n";
            v.setReport(report);
            g.addVertex(v);
        }
        //else already exist, check the stamp 
        else{
            Vertex v=g.getVex(itName);
            //if not consistant -> report
            if(!v.checkTimeStamp(stamp)){
                String report=v.getreporString(); 
                g.findErrorStamp(report,v,stamp);
            }
        }

        // ArrayList<String> otherName = new ArrayList<String>();
        // add Parents
        for (int i = 2; i < theList.size(); i++)
        {
            String otherName=theList.get(i).split("\\s+")[0].replace("\"", "");
            String stampo="";
            //[1,2,3,4,5].copyOfRange(1,4)=234
            //do a slice, from the second to the end.
            String[] ostamps = Arrays.copyOfRange((theList.get(i).split("\\s+")),1,(theList.get(i).split("\\s+")).length);
            for(String s:ostamps){
                s=s.replace("\"", "");
                stampo+=s;
            }


            //for the parents
            //create if not find
            if(g.getVex(otherName)==null){


                //check whether its in the currentFile?
                String filename=otherName+"Theory.dat";
                int index=-1;
                for(int k=0;k<FileReader.currentFiles.size();k++){
                    String result=FileReader.currentFiles.get(k).getFileName().toString();
                    if(result.equals(filename)){
                        index=k;
                        break;
                    }
                }
                //so not in currentFiles
                if(index==-1 && !otherName.equals("min")){
                    //not in currentFile, do search and add it into the currentFile.
                    StringBuffer s=new StringBuffer("");
                    //please set the HOL main folder
                    File dir = new File(FileReader.MainFolder);
                    TheoremParser.searchFile(dir,filename,s);

                    System.out.println("searched file is "+filename+" its location is "+s.toString());
                    //actually find it!
                    if(!s.isEmpty())FileReader.currentFiles.add(Paths.get(s.toString()));
                }


                Vertex z=new Vertex(otherName,stampo);
                //parent-child(found inconsistant):file link
                StringBuffer s=new StringBuffer("");
                //please set the HOL main folder
                File dir = new File(FileReader.MainFolder);
                String childfile=itName+"Theory.dat";
                TheoremParser.searchFile(dir,childfile,s);

                String report=otherName+"-"+itName+":"+s.toString()+"\n";
                z.setReport(report);
                g.addVertex(z);   
            }
            //else already exist, check the stamp 
            else{
                Vertex v=g.getVex(otherName);
                if(!v.checkTimeStamp(stampo)){
                    //parent-child(found inconsistant):file link
                    StringBuffer s=new StringBuffer("");
                    //please set the HOL main folder
                    File dir = new File(FileReader.MainFolder);
                    String filename=itName+"Theory.dat";
                    TheoremParser.searchFile(dir,filename,s);
                    String report=v.toString()+"-"+itName+":"+s.toString()+"\n";
                    g.findErrorStamp(report,v);
                }
            }

            //add the edge, (parent,itName)
            Edge n=new Edge(otherName, itName);
            //check whether it exists
            if(!g.hasEdges(n))g.addEdge(otherName, itName);

        }

    }

    public void  theorem_graph(ArrayList<Theory> theories,Theorem t,Theory thy,myGraph g,HashMap<String, String> externals)
    {   

        //this is the method to manually build the theorem graph for a theory!
        
        //new root: if not found it in graph,add the theorem
        if(g.getVex(t.getName())==null){
        Vertex v=new Vertex(t.getName(),"theorem");
        innertheorems+=1;
        g.addVertex(v);
        String external_theorems="";
        
        //what todo: find the theorem and build edge based on the record!
        for(Dependency_record r:t.getRecords()){
            //other theorems in this theory, keep record
            if(r.getName().equals(thy.getName())){
                for(int index:r.getIndexs()){
                    //check the name of the theorem in theory
                    for(Theorem x:thy.getTheorems()){
                        if(x.getName().equals(thy.checkHashtable(index))){
                                Edge n=new Edge(t.getName(), x.getName());
                                //check whether it exists
                                if(!g.hasEdges(n))g.addEdge(t.getName(), x.getName());
                                theorem_graph(theories,x,thy,g,externals);
                            }
                    }
                }
            }
            //its a record to other theorys'theorems
            //only show name:ammount
            else{
                //contains external in hashmap, create first then update.
                if(!externals.containsKey(t.getName())){
                    external_theorems+=String.valueOf(r.getIndexs().size())+" FROM "+r.getName()+"\n";
                    externals.put(t.getName(), external_theorems);
                    externaltheorems+=r.getIndexs().size();
                }
                else{
                    external_theorems+=String.valueOf(r.getIndexs().size())+" FROM "+r.getName()+"\n";
                    externals.replace(t.getName(), external_theorems);
                    externaltheorems+=r.getIndexs().size();
                }
                
            }
        }

        }

    }

    //print theory inf
    public static void PrintArrayList(ArrayList<String> theList)
    {   
        int count=theList.size()-1;
        System.out.println("The " 
                + count + " theories in the .dat file:");
        for (int i = 1; i < theList.size(); i++)
        {
            
            System.out.println(i + ":" + theList.get(i));
        }
    }
}