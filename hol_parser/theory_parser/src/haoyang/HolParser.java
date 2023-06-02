package haoyang;
import java.io.IOException;
import net.claribole.zgrviewer.FrameDesign;

public class HolParser {
    public static String location;
    public static void main(String[] args) throws IOException, InterruptedException{


        //init with current working path:
        //init the location
        location=System.getProperties().getProperty("user.dir");
        //load dir to svg
        FileReader f=new FileReader(location);
        String svgpath = FileReader.loadir(location);

        FrameDesign fm=new FrameDesign();
        fm.display(svgpath);
    }
}
