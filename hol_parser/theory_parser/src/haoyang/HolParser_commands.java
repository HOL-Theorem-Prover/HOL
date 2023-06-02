package haoyang;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Scanner;


public class HolParser_commands {
    public static String location;
    public static boolean sign=false;
    public static int commandindex=0;
    public static void main(String[] args) throws IOException, InterruptedException{

        sign=true;
        //init with current working path:
        //init the location
        location=System.getProperties().getProperty("user.dir");
        //load dir to svg
        FileReader f=new FileReader(location);
        
        System.out.println("multi_folders_merge? (Y/N)");
        Scanner scanner = new Scanner(System.in);
        String input = scanner.nextLine();
        System.out.println("please input your command's index:");
        System.out.println("1.incompatible timestamp check \n2.abnormal tag check \n3.unused theorems check");
        Scanner Commandscanner = new Scanner(System.in);
        String command = Commandscanner.nextLine();
        switch(command){
            case "1":{
                commandindex=1;
                break;
            }
            case "2":{
                commandindex=2;
                break;
            }
            case "3":{
                commandindex=3;
                break;
            }
            default: System.out.println("wrong command");
        }
        System.out.println("please input the target folder (split by space in multi-mode)");
        //if multi folders
        if(input.contains("Y") || input.contains("y")){
            Scanner Filescanner = new Scanner(System.in);
            String file = Filescanner.nextLine();
            String[] files=file.split("\\s+");
            ArrayList<String> paths = new ArrayList<String>(Arrays.asList(files));
            FileReader.loadir_multi(paths);
        }
        if(input.contains("N") || input.contains("n")){
            Scanner Filescanner = new Scanner(System.in);
            String file = Filescanner.nextLine();
            FileReader.loadir(file);
        }
    }
}
