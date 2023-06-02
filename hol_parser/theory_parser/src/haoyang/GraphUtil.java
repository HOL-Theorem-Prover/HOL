package haoyang;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;

public class GraphUtil {

    private String code = "digraph G {" + "\r\n";
    private String sourcePath;
    private String targetPath;
    public static Process dotprogram;
    
    public void setTargetPath(String targetPath) {
        this.targetPath = targetPath;
    }

    //draw edge from A to B
    public void link(String dotA, String dotB){
        String linkCode = dotA + " -> " + dotB + "\r\n";
        this.code += linkCode;
    }

    public void setSpine(){
        this.code += "splines=ortho"+ "\r\n";
    }
    public void setInverse(){
        this.code += "rankdir=\"BT\""+ "\r\n";
    }

    //draw node label
    public void node(String dot,String label){
        String nodeCode = dot + "[" + label + "]" + "\r\n";
        this.code += nodeCode;
    }

    public void DAGToNode(List<Vertex> DAG){
        for(Vertex v:DAG){
            node(v.toString(),"shape=box style=filled BORDER=5");
        }
    }

    public void GraphToEdge(myGraph g){
        for(Edge e:g.edges()){
            link(e.getStART(), e.getEND());
        }
    }
    //open a file
    public static void openFile(String filePath) throws IOException {

        File file = new File(filePath);
        System.out.println("already generate the visualization: "+file.toString());

        //my linux dont have a terminal
        // Desktop.getDesktop().open(file);
    }

    //generate jpg
    public static void genGraph(String sourcePath,String targetPath) throws IOException, InterruptedException {
        Runtime run = Runtime.getRuntime();
        // dotprogram=run.exec("dot "+"-Tsvg "+sourcePath+" -o "+targetPath);
        Process newdot=run.exec("dot "+"-Tsvg "+sourcePath+" -o "+targetPath);
        dotprogram=newdot;
    }

    //generate and open
    public static void genAndOpenGraph(String sourcePath,String targetPath) throws InterruptedException, IOException {
        genGraph(sourcePath,targetPath);
        // openFile(targetPath);
    }

    //save dot strings to file
    public static void saveCodeToFile(String filePath, String content) {
        FileWriter fwriter = null;
        try {
            fwriter = new FileWriter(filePath, false);
            fwriter.write(content);
        } catch (IOException ex) {
            ex.printStackTrace();
        } finally {
            try {
                fwriter.flush();
                fwriter.close();
            } catch (IOException ex) {
                ex.printStackTrace();
            }
        }
    }

    public String getCode() {
        return code + "\n}";
    }

    public void setCode(String code) {
        this.code = code;
    }

    public String getSourcePath() {
        return sourcePath;
    }

    public void setSourcePath(String sourcePath) {
        this.sourcePath = sourcePath;
    }

    public String getTargetPath() {
        return targetPath;
    }

}

