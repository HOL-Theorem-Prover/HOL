package haoyang;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

//a theorem, belong to a theory, has a tag, depend to other theorem.

public class Theory{
    private String name="";
    private ArrayList<String> table=new ArrayList<String>();
    private ArrayList<String> id_table=new ArrayList<String>();
    private ArrayList<String> term_table=new ArrayList<String>();
    // //dependency table: index:theorem
    private ArrayList<Theorem> theorems=new  ArrayList<Theorem>();
    private HashMap<Integer, String> theoremsTable = new HashMap<Integer, String>();

    //record the theory name
    public void initName(String s){
        this.name= s.split("\\s+")[0].replace("\"", "");      
    }

    //load term table
    public void initTable(String s){

        String[] tmp=s.split("\\s+");
         //remove the start label string-table
        tmp=Arrays.copyOfRange(tmp,1,tmp.length);
        for(String r:tmp){
            r=r.replace("\"", "");
            //remove @ cus dot name doesnt support it!
            r=r.replace("@", "");
            r=r.replace("'", "2");
            table.add(r);
        }

    }

    //print for test
    public void printTheory(){
        System.out.println("this .dat is for theory: "+name);
        System.out.println("the term table is: ");
        for(int i=0;i<table.size();i++){
            System.out.println("the index "+i+" is "+table.get(i));
        }
        System.out.println("it has: "+theorems.size()+" theorems");
        for(Theorem e: theorems){
            e.printTheorem();
        }
    }
    public String getName(){
        return name;
    }
    public void addTheorem(Theorem e){

        //update the inf
        int index= e.getRecords().get(0).getIndexs().get(0);
        e.setPos(index);
        theoremsTable.put(index, e.getName());
        e.removeFirstRecord();
        theorems.add(e);
    }
    public ArrayList<String> getable(){
        return table;
    }
    //given a index, return the term
    public String checktable(String s){
        int index=Integer.valueOf(s).intValue();
        return table.get(index);
    }

    public String checkHashtable(int index){
        return theoremsTable.get(index);
    }


    public ArrayList<Theorem> tagfilter(String tag){
        ArrayList<Theorem> result=new ArrayList<Theorem>();
        for(Theorem t:theorems){
            //get all theorems which not tag
            //also not empty
            if(!t.getTag().isEmpty()&&!t.getTag().equals(tag))result.add(t);
        }
        return result;
    }

    public ArrayList<Theorem> getTheorems(){
        return theorems;
    }
}