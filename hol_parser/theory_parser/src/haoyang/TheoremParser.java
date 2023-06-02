package haoyang;
import java.io.BufferedReader;

import java.io.File;
import java.io.FileFilter;
import java.io.FileReader;
import java.io.IOException;

import java.util.ArrayList;
import java.util.Arrays;


//a theorem, belong to a theory, has a tag, depend to other theorem.


//String thyname_index,
//int dep theorem_index
class Dependency_record{
    private String thyname="";
    //the index stored in one theory
    private ArrayList<Integer> theorem_index=new ArrayList<Integer>();


    //create a record
    //the record will load to theorem
    public Dependency_record(Theory t, String s){
        //(x x1 x2 x3...) x is the theory's index in the string table
        String thyname_index= s.split("\\s+")[0];
        //check the table and get the name of theory
        thyname=t.checktable(thyname_index);
        //get name from 
        
        //do a slice to get x1...xn
        String[] others=Arrays.copyOfRange((s.split("\\s+")),1,(s.split("\\s+")).length);
        for(String o:others){
            int index=Integer.valueOf(o).intValue();
            theorem_index.add(index);
        }

        //two kinds of record, self and others
        //stored in different places
        //add record (thyname, indexs) to theorem
    }

    public void printRecord(){
        System.out.println("record: this theorem depend on "+thyname+" index: "+theorem_index);
    }
    public String getName(){
        return thyname;
    }
    public ArrayList<Integer> getIndexs(){
        return theorem_index;
    }
}

class Theorem {
    private String name="";
    private String tag="";
    private int pos=-1;

    private ArrayList<Dependency_record> records=new ArrayList<Dependency_record>();

    public Theorem(){
    }

    public void setName(Theory t, String s){
        //if name is empty,
        //avoid layer2 another case: (name()(xxx))
        if(name.equals("")){
            String term=t.checktable(s);
            name=term;
        }
    }

    public void setTag(String s){
        //add the tag!
        tag=s.replace("\"", "");
    }

    public void removeFirstRecord(){
        records.remove(0);
    }
    public ArrayList<Dependency_record> getRecords(){
        return records;
    }

    public void addRecord(Dependency_record r){
        records.add(r);
    }

    public String getName(){
        return name;
    }

    public void setPos(int p){
        pos=p;
    }

    public void printTheorem(){
        System.out.println("this theorem name is "+name+" tag is "+tag+" pos is "+pos);
        for(Dependency_record r:records)r.printRecord();
    }

    public String getTag(){
        return tag;
    }
    // public void set_thy(Theory t){
    //     theory=t;
    // }
}

//theoremParser
public class TheoremParser {

    //set enum:
    public enum States { STARTING, TOKEN, BETWEEN };
    //the bracket stack

    //input: one .dat
    public void Process(String dat_content,Theory t)
    {
        States state = States.STARTING;
        // Stack=0;
        // Sign=0;

        //flags:
        //1.table one .dat only have one table
        int tableSign=0;
        //same as 1
        int TnameSign=0;
        //export (nil) (nil), i use the double nil as a sign of theorems.
        //the sign for theorem data start
        int nilcount=0;

        //layers inf for each theorem,1 is start of whole theorems, 2 is start of one theorem
        int layer=-1;
        //
        int tagflag=0;
        
        // ArrayList<Theorem> theorems = new ArrayList<Theorem>();
        
        Theorem theorem=new Theorem();

        String table="";
        String theoryName="";


        //temp to store the current input
        StringBuffer Stemp = new StringBuffer("");
        String cString;


        //(theorem_name (((theoryname, identity_number)...)) tag )(logic structure string))
        
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
                    else if (state == States.BETWEEN)  
                    {
                        if(layer>=0)layer+=1;
                    } 
                    else if (state == States.TOKEN )
                    {

                        state = States.BETWEEN;
                        
                        cString=Stemp.toString().trim();
                        //record its theory name 
                        if(cString.equals("theory")){
                            //after read theory, start record theory till stack return 0
                            TnameSign=1;
                        }
                        //read tables,the after is the string table
                        if(cString.equals("tables")){
                            //string tables for .dat
                            tableSign=1;
                            //it will record the next table
                            //it is the left bracket of table
                        }


                        //   layer 2(theorem_name (dep_info)(logicstructure)) 
                        if(nilcount==2){
                            if(layer==2){
                                //check name in string table
                                theorem.setName(t,cString);
                            }
                            layer+=1;
                        }

                        //after theorem 
                        if(cString.equals("incorporate")){
                            nilcount=-1;
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


                        //.dat name
                        if(TnameSign==1){
                            //record the theoryname
                            TnameSign=0;
                            theoryName=cString;
                            t.initName(theoryName);
                        }

                        //right bracket of table
                        if(tableSign==1){
                            //record the table
                            tableSign=2;
                            table=cString;
                            t.initTable(table);
                        }

                        //it's the start of theorem
                        if(nilcount==2){
                            //load the theorems of this .dat
                            if(layer==5){
                                Dependency_record record=new Dependency_record(t,cString);
                                theorem.addRecord(record);
                            }
                            //3->2 layer, can be tag or logic only record tag
                            if(layer==3){
                                //add tag
                                if(tagflag==0){
                                    theorem.setTag(cString);
                                    tagflag=1;
                                }
                            }
                            layer-=1;
                        }

                        //export (nil) (nil) （: 
                        if(cString.equals("nil")){
                            //term tables for .dat
                            nilcount+=1;
                            if(nilcount==2)layer=0;
                        }
                        
                        
                        Stemp.delete(0,Stemp.length());
                        state = States.BETWEEN;
                    } 
                    else if (state == States.BETWEEN) {
                        //this case, no tag
                        if(layer==3&&tagflag==0){
                            tagflag=1;
                        }
                        //end of a theorem inf
                        if(layer==2){
                            tagflag=0;
                            //add theorem to theory
                            t.addTheorem(theorem);
                            theorem=new Theorem();
                        }
                        if(layer>0)layer-=1;
                    }
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
            if(nilcount==-1)break;
        }

    }

    public static String sig_parser(String dat_content,String theoremName)
    {
        States state = States.STARTING;
        //temp to store the current input
        StringBuffer Stemp = new StringBuffer("");
        String cString;
        String sig="";
        int level=0;


    
        for (int i = 0; i < dat_content.length() ; i++)
        {
            //travel every char in the string 
            char cTemp = dat_content.charAt(i);
            switch (cTemp)
            {

                case '[':
                {
                    if (state == States.STARTING)  state = States.BETWEEN;
                    else if (state == States.BETWEEN)  {} 
                    else if (state == States.TOKEN )
                    {

                        state = States.BETWEEN;
                        cString=Stemp.toString().trim();
                        if(level==1){
                            sig+=cString;
                            level=2;
                            
                            
                        }
                    
                        // //free the temp
                        Stemp.delete(0,Stemp.length());

                    }
                    break;
                }

                case ']':
                {
                    if (state == States.STARTING) 
                    {  /* this is an error */ }
                    else if (state == States.TOKEN) 
                    {
                        cString=Stemp.toString().trim();
                        if(cString.equals(theoremName)){
                            //start record the statement
                            sig+="["+cString+"]";
                            level=1;
                        }
                        Stemp.delete(0,Stemp.length());

                        state = States.BETWEEN;
                    } 
                    else if (state == States.BETWEEN) {}
                    break;
                }

                default:
                {   
                    state = States.TOKEN;
                    //record the char
                    Stemp.append(cTemp);

                }
            }
            if(level==2)break;
        }
        return sig;
    }

    public static String sml_parser(String path,String theoremName) throws IOException{
        
        String line="";
        StringBuffer strbuf = new StringBuffer();
        boolean start=true;

        //theoremname->QED
        BufferedReader in = new BufferedReader(new FileReader(path));

        //read until theoremName appear
        while((line = in.readLine())!= null){
            if(line.contains(theoremName))break;
        }
        strbuf.append(line + "\r\n");

        //record until QED
        while (start) {
            if((line = in.readLine())!=null){
                if (!line.trim().equals("")) {
                    strbuf.append(line + "\r\n");
                    if(line.trim().equals("QED"))break;
                }
            }
            else break;
        }

        return strbuf.toString();
    }

    //tag check for current loaded dirs
    public static void tag_check(ArrayList<Theory> in) throws IOException, InterruptedException{
        ArrayList<Theory> current=in;
        ArrayList<Theorem> no_DISK_THMs=new ArrayList<Theorem>();
        for(Theory t:current){
            if(!t.tagfilter("DISK_THM").isEmpty())System.out.println("abnormal tags in\s"+t.getName());
            no_DISK_THMs.addAll(t.tagfilter("DISK_THM"));
        }
        String dialog="";

        for(Theorem t:no_DISK_THMs){
            dialog=dialog+t.getName()+", ";
        }
        if(HolParser_commands.sign==false){
            messageBox m=new messageBox(dialog,"Theorems that not with tag “DISK_THM” are:");
        }
        else{
            System.out.println(dialog);
        }
        
        // too large dialog cause stuck!!!!
        // JOptionPane.showMessageDialog(null,dialog, "The result of tag check", JOptionPane.PLAIN_MESSAGE);
    }

    //unused check
    public static void unused_check(ArrayList<Theory> in,String thyanme) throws IOException, InterruptedException{
        // first part, given a theory name, load that theory!

        Theory target=new Theory();
        for(Theory thy:in){
            if(thy.getName().equals(thyanme))
            {
                target=thy;
                break;
            }
        }

        System.out.println("theorems in "+target.getName()+" are "+target.getTheorems().size());
        //need to get whole depend theorems
        ArrayList<String> wholeDeps=new ArrayList<String>();
        ArrayList<Theory> current=in;
        //for all theory y in current->all theorems->for all records of this theorem(record: depend on the number i theorem of theory x)
        //then collect the name of dependency: depend on which theorem

        long etime = System.currentTimeMillis();
        
        for(Theory y:current){
            for(Theorem t:y.getTheorems()){
                for(Dependency_record r:t.getRecords()){
                    //record thyname-->found the this theory's dep table
                    for(Theory x:current){
                        //find that theory
                        if(r.getName().equals(x.getName())){
                            //convert all index into theorem name!
                            for(int i:r.getIndexs()){
                                wholeDeps.add(x.checkHashtable(i));
                            }
                        }
                    }
                }
            }
        }

        long stime = System.currentTimeMillis();
        System.out.printf("unused: Process:%d ms.\n", (stime - etime));
        String dialog="";
        int count=0;
        //for the target theory's theorems:
        for(Theorem e:target.getTheorems()){
            //then check whether it is in the list.
            //if not
            if(!wholeDeps.contains(e.getName()))
            {
                dialog=dialog+e.getName()+", ";
                count++;
            }
        }
        System.out.println(count+" unused");
        if(HolParser_commands.sign==false){
            messageBox m=new messageBox(dialog,target.getName()+"'s "+"theorems that are not used in the graph:");
        }
        else{
            System.out.println(dialog);
        }
    }

    //search for target theory in main files
    public static void searchFile(File dir,String name,StringBuffer s){
        File[] files=dir.listFiles(new FileFilter() {
            @Override
            public boolean accept(File pathname){
                // System.out.println(pathname.getName());
                if(pathname.getName().equals(name)){
                    
                    return true;
                }
                else if(pathname.isDirectory()){
                    return true;
                }
                else{
                    return false;
                }
            }
        });
        
        for(File file:files){
            if(file.isDirectory()){
                //get the absoluate path
                searchFile(file,name,s);
            }
            else{
                
                if(s.isEmpty())s.append(file.getAbsolutePath());
            }
        }
        
    }
}
