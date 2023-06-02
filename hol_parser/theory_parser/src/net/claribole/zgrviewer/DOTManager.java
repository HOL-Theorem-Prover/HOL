/*   FILE: DOTManager.java
 *   DATE OF CREATION:   Thu Jan 09 14:14:35 2003
 *   Copyright (c) Emmanuel Pietriga, 2002. All Rights Reserved
 *   Copyright (c) INRIA, 2004-2011. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: DOTManager.java 5322 2015-02-05 15:44:14Z epietrig $
 */

package net.claribole.zgrviewer;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.IOException;
import java.net.MalformedURLException;
import java.util.StringTokenizer;
import javax.swing.JOptionPane;

import org.w3c.dom.Document;

import fr.inria.zvtm.svg.SVGReader;

class DOTManager {

    static final short DOT_PROGRAM = 0;
    static final short NEATO_PROGRAM = 1;
    static final short CIRCO_PROGRAM = 2;
    static final short TWOPI_PROGRAM = 3;
    static final short SVG_FILE = 4;
    short lastProgramUsed = DOT_PROGRAM;

    ConfigManager cfgMngr;
    GraphicsManager grMngr;

    File dotF;
    File svgF;

    DOTManager(GraphicsManager gm, ConfigManager cm){
    this.grMngr = gm;
    this.cfgMngr = cm;
    }

    void load(File f, short prg, boolean parser){
        // prg is the program to use DOTManager.*_PROGRAM
        grMngr.gp.setMessage("Resetting...");
        grMngr.gp.setProgress(10);
        grMngr.gp.setVisible(true);
        try {
            svgF=Utils.createTempFile(ConfigManager.m_TmpDir.toString(),"zgrv",(parser?".dot":".svg"));
            dotF=f;
            callGraphViz(prg, parser);
            grMngr.gp.setMessage("Deleting Temp File...");
            grMngr.gp.setProgress(100);
            grMngr.gp.setVisible(false);
        }
        catch (Exception ex){
            grMngr.gp.setVisible(false);
            javax.swing.JOptionPane.showMessageDialog(grMngr.mainView.getFrame(),Messages.loadError+f.toString());
        }
    }

    private void callGraphViz(short prg, boolean parser) throws Exception {
        // prg is the program to use DOTManager.*_PROGRAM
        try {
            grMngr.gp.setMessage("Preparing " + (parser ? "Augmented DOT" : "SVG")
                + " Temp File");
            grMngr.gp.setProgress(10);
            // if (parser) {
            //     if (!generateDOTFile(dotF.getAbsolutePath(), svgF.getAbsolutePath(), prg)) {
            //         deleteTempFiles();
            //         return;
            //     }
            //     displayDOT();
            //     if (ConfigManager.DELETE_TEMP_FILES) {
            //         deleteTempFiles();
            //     }
            // } else {
                if (!generateSVGFile(dotF.getAbsolutePath(), svgF.getAbsolutePath(), prg)) {
                    deleteTempFiles();
                    return;
                }
                displaySVG(dotF.getAbsoluteFile().getParentFile());
                if (ConfigManager.DELETE_TEMP_FILES) {
                    deleteTempFiles();
                }
            // }
        } catch (Exception e) {
            System.err.println("Exception generating graph: " + e.getMessage()
                + "\n");
            e.printStackTrace();
            throw new Exception();
        }
    }

    void deleteTempFiles(){
    if (svgF!=null){svgF.delete();}
    }

    protected String getProgram(short prg){
    // prg is the program to use DOTManager.*_PROGRAM
    switch (prg){
    case DOT_PROGRAM:{return ConfigManager.m_DotPath.toString();}
    case NEATO_PROGRAM:{return ConfigManager.m_NeatoPath.toString();}
    case TWOPI_PROGRAM:{return ConfigManager.m_TwopiPath.toString();}
    case CIRCO_PROGRAM:{return ConfigManager.m_CircoPath.toString();}
    default:{return ConfigManager.m_DotPath.toString();}
    }
    }

    private boolean generateDOTFile(String dotFilePath, String tmpFilePath, short prg){
        String[] cmdArray = new String[(cfgMngr.FORCE_SILENT) ? 7 : 6];
        cmdArray[0] = getProgram(prg);
        cmdArray[1] = "-Tdot";
        if (cfgMngr.FORCE_SILENT){
            cmdArray[2] = "-q";
            cmdArray[3] = checkOptions(ConfigManager.CMD_LINE_OPTS);
            cmdArray[4] = "-o";
            cmdArray[5] = tmpFilePath;
            cmdArray[6] = dotFilePath;
        }
        else {
            cmdArray[2] = checkOptions(ConfigManager.CMD_LINE_OPTS);
            cmdArray[3] = "-o";
            cmdArray[4] = tmpFilePath;
            cmdArray[5] = dotFilePath;
        }
        Runtime rt=Runtime.getRuntime();
        grMngr.gp.setMessage("Computing Graph Layout (GraphViz)...");
        grMngr.gp.setProgress(40);
        try {
            try {
                File execDir = (new File(dotFilePath)).getParentFile();
                Process p = rt.exec(cmdArray, null, execDir);
                executeProcess(p);
            }
            catch (IOException ex){
                Process p = rt.exec(cmdArray);
                executeProcess(p);
            }
        }
        catch (Exception e) {System.err.println("Error: generating OutputFile.\n");return false;}
        return true;
    }

    /**
        * Invokes the GraphViz program to create a graph image from the
        * the given DOT data file
        *@param dotFilePath the name of the DOT data file
        *@param svgFilePath the name of the output data file
        *@param prg program to use (dot or neato)
        *@return true if success; false if any failure occurs
        */
    private boolean generateSVGFile(String dotFilePath, String svgFilePath, short prg){
        String[] cmdArray = new String[(cfgMngr.FORCE_SILENT) ? 7 : 6];
        cmdArray[0] = getProgram(prg);
        cmdArray[1] = "-Tsvg";
        if (cfgMngr.FORCE_SILENT){
            cmdArray[2] = "-q";
            cmdArray[3] = checkOptions(ConfigManager.CMD_LINE_OPTS);
            cmdArray[4] = "-o";
            cmdArray[5] = svgFilePath;
            cmdArray[6] = dotFilePath;
        }
        else {
            cmdArray[2] = checkOptions(ConfigManager.CMD_LINE_OPTS);
            cmdArray[3] = "-o";
            cmdArray[4] = svgFilePath;
            cmdArray[5] = dotFilePath;
        }
        Runtime rt=Runtime.getRuntime();
        grMngr.gp.setMessage("Computing Graph Layout (GraphViz)...");
        grMngr.gp.setProgress(40);
        try {
            try {
                File execDir = (new File(dotFilePath)).getParentFile();
                final Process p = rt.exec(cmdArray, null, execDir);
                executeProcess(p);
            }
            catch (IOException ex){
                Process p = rt.exec(cmdArray);
                p.waitFor();
            }
        }
        catch (Exception e) {System.err.println("Error: generating OutputFile.\n");return false;}
        return true;
    }

    protected void executeProcess(Process p) throws InterruptedException, IOException {
        Thread consumer = new ProcessOutputConsumer(p);
        consumer.start();
        p.waitFor();
        p.destroy();
        consumer.interrupt();
    }

    /*load a file using a program other than dot/neato for computing the layout (e.g. twopi)*/
    void loadCustom(String srcFile, String cmdLineExpr){
        grMngr.gp.setMessage("Resetting SVG...");
        grMngr.gp.setProgress(10);
        grMngr.gp.setVisible(true);
        try {
            svgF = Utils.createTempFile(ConfigManager.m_TmpDir.toString(), "zgrv", ".svg");
            if (!generateSVGFileFOP(srcFile, svgF.getAbsolutePath(), cmdLineExpr)){
                deleteTempFiles();
                return;
            }
            displaySVG((new File(srcFile)).getParentFile());
            if (ConfigManager.DELETE_TEMP_FILES) {
                deleteTempFiles();
            }
            grMngr.gp.setMessage("Deleting Temp File...");
            grMngr.gp.setProgress(100);
            grMngr.gp.setVisible(false);
        }
        catch (Exception ex){
            grMngr.gp.setVisible(false);
            javax.swing.JOptionPane.showMessageDialog(grMngr.mainView.getFrame(),Messages.loadError+srcFile);
        }
    }


    /**
     * Invokes a program to create an SVG image from a source file using a program other than dot/neato for computing the layout (e.g. twopi)
     *@return true if success; false if any failure occurs
     */
    private boolean generateSVGFileFOP(String srcFilePath, String svgFilePath, String commandLine){
    StringTokenizer st = new StringTokenizer(commandLine, " ");
    int nbTokens = st.countTokens();
    String[] cmdArray = new String[nbTokens];
    for (int i=0;i<nbTokens;i++){
        cmdArray[i] = st.nextToken();
        if (cmdArray[i].equals("%s")){cmdArray[i] = srcFilePath;}
        else if (cmdArray[i].equals("%t")){cmdArray[i] = svgFilePath;}
    }
    Runtime rt=Runtime.getRuntime();
    grMngr.gp.setMessage("Computing layout...");
    grMngr.gp.setProgress(40);
    try {
        try {
        File execDir = (new File(srcFilePath)).getParentFile();
        Process p = rt.exec(cmdArray, null, execDir);
        p.waitFor();
        }
        catch (IOException ex){
        Process p = rt.exec(cmdArray);
        p.waitFor();
        }
    }
    catch (Exception e){
        JOptionPane.showMessageDialog(grMngr.mainView.getFrame(), Messages.customCallExprError2 + Utils.join(cmdArray, " "),
                      "Command line call error", JOptionPane.ERROR_MESSAGE);
        System.err.println("Error generating output SVG file.\n");
        return false;
    }
        return true;
    }

    void displaySVG(File sourceDotFileParentDir){
        grMngr.gp.setMessage("Parsing SVG...");
        grMngr.gp.setProgress(60);
        Document svgDoc=Utils.parse(svgF,false);
        grMngr.gp.setMessage("Displaying...");
        grMngr.gp.setProgress(80);
        try {
            // going through URI and then URL as advised in JDK 1.6
            SVGReader.load(svgDoc, grMngr.mSpace, true, svgF.toURI().toURL().toString(), sourceDotFileParentDir.toURI().toURL().toString());
            grMngr.seekBoundingBox();
            grMngr.buildLogicalStructure();
        }
        catch (MalformedURLException ex){
            JOptionPane.showMessageDialog(grMngr.mainView.getFrame(), svgF.getAbsolutePath(),
                Messages.SVG_PARSING_ERROR, JOptionPane.ERROR_MESSAGE);
            System.err.println("Error loading SVG file.\n");
        }
    }

    /*checks that the command line options do not contain a -Txxx */
    static String checkOptions(String options){
    int i = options.indexOf("-T");
    if (i!=-1){
        String res=options.substring(0,i);
        while (i<options.length() && options.charAt(i)!=' '){i++;}
        res+=options.substring(i);
        return res;
    }
    else return options;
    }

}

/**
 * A simple thread that will consume the stdout and stderr streams of a process, to prevent deadlocks.
 *
 * @author David J. Hamilton <hamilton37@llnl.gov>
 */

class ProcessOutputConsumer extends Thread {

    // Wrapping the inpustreams in readers because on my system
    // FileInputStream#skip would not actually consume any of the available
    // input
    private BufferedReader pout, perr;

    private long waitTime = 200;


    /**
     * @param p The process whose stdout and stderr streams are to be consumed.
     * @throws IOException
     */
    public ProcessOutputConsumer(Process p) throws IOException {
        p.getOutputStream().close();

        pout = new BufferedReader( new InputStreamReader( p.getInputStream()));
        perr = new BufferedReader( new InputStreamReader( p.getErrorStream()));

        setDaemon( true);
    }

    /**
     * @param p The process whose stdout and stderr streams are to be consumed.
     * @param waitTime How long to wait (in ms) between checks for output to consume.
     * @throws IOException
     */
    public ProcessOutputConsumer(Process p, long waitTime) throws IOException {
        this(p);
        this.waitTime = waitTime;
    }


    @Override
    public void run() {
        try {
            while (true) {
                while( pout.ready())
                    pout.readLine();
                while( perr.ready())
                    perr.readLine();

                if( waitTime > 0)
                    sleep( waitTime);
            }
        }
        catch (IOException e) { /* do nothing */ }
        catch (InterruptedException e) { /* do nothing */}
    }
}
