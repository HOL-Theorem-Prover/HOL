package haoyang;
import java.io.IOException;
import net.claribole.zgrviewer.FrameDesign;

public class test {
    public static String location;

    //testmode for debug
    public static boolean testmode=false;
    public static void main(String[] args) throws IOException, InterruptedException{


        //init with current working path:
        //init the location
        location="/home/haoyang/HOL/";
  
        FileReader f=new FileReader(location);
        //load dir to svg
        String svgpath = FileReader.loadir(location);
        FrameDesign fm=new FrameDesign();
        fm.display(svgpath);
    }
}